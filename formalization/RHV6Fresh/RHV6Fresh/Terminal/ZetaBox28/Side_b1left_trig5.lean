/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b1left (b1), angles 5

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

lemma cs_b1left_v19p892_9 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.962396435411:ℝ):ℂ) + ((0.2716488562617:ℝ):ℂ) * I)‖ ≤ 0.00000015168 := by
  have hl := lg_9
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.707191282030396576 43.70719130192243636 0.2751059 0.00000005167 0.962396435411 0.2716488562617 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_10 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2473353336728):ℝ):ℂ) + (((-0.9689299421092):ℝ):ℂ) * I)‖ ≤ 0.00000013392 := by
  have hl := lg_10
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.803022654325045428 45.80302268416306532 (-1.8207255) 0.00000003391 (-0.2473353336728) (-0.9689299421092) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_11 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.839168941974):ℝ):ℂ) + ((0.5438708364665:ℝ):ℂ) * I)‖ ≤ 0.00000012341 := by
  have hl := lg_11
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.698932750992658436 47.69893278083069822 2.5665497 0.0000000234 (-0.839168941974) 0.5438708364665 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_12 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6706442203159:ℝ):ℂ) + ((0.7417791650868:ℝ):ℂ) * I)‖ ≤ 0.00000013449 := by
  have hl := lg_12
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.429763062070398288 49.42976309190841818 0.8357194 0.00000003448 0.6706442203159 0.7417791650868 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_13 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7272495177519:ℝ):ℂ) + (((-0.6863731776007):ℝ):ℂ) * I)‖ ≤ 0.00000015434 := by
  have hl := lg_13
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.0219726031123764 51.021972632950416184 (-0.7564902) 0.00000005433 0.7272495177519 (-0.6863731776007) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_14 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6129980090365):ℝ):ℂ) + (((-0.7900844517544):ℝ):ℂ) * I)‖ ≤ 0.00000015761 := by
  have hl := lg_14
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.496128385194214424 52.496128415032254208 (-2.2306459) 0.0000000576 (-0.6129980090365) (-0.7900844517544) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_15 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8954036217671):ℝ):ℂ) + ((0.4452553806695:ℝ):ℂ) * I)‖ ≤ 0.00000015005 := by
  have hl := lg_15
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.868534584812643716 53.8685346146506835 2.6801332 0.00000005004 (-0.8954036217671) 0.4452553806695 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_16 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.17357973468:ℝ):ℂ) + ((0.9848198189051:ℝ):ℂ) * I)‖ ≤ 0.00000012252 := by
  have hl := lg_16
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.1523348421104 55.1523348818944 1.3963329 0.00000002251 0.17357973468 0.9848198189051 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_17 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9819309028744:ℝ):ℂ) + ((0.1892398002013:ℝ):ℂ) * I)‖ ≤ 0.00000014535 := by
  have hl := lg_17
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.358279819282905128 56.35827985906692502 0.1903879 0.00000004534 0.9819309028744 0.1892398002013 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_18 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5844394923934:ℝ):ℂ) + (((-0.8114372925439):ℝ):ℂ) * I)‖ ≤ 0.00000015779 := by
  have hl := lg_18
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.495274992557996576 57.49527502239603636 (-0.9466072) 0.00000005778 0.5844394923934 (-0.8114372925439) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_19 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4361502113825):ℝ):ℂ) + (((-0.899873876222):ℝ):ℂ) * I)‖ ≤ 0.0000001233 := by
  have hl := lg_19
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.570780158066306876 58.570780187904366552 (-2.0221124) 0.00000002329 (-0.4361502113825) (-0.899873876222) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v19p892_20 : ‖exp (-((((((19892:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9950882627458):ℝ):ℂ) + (((-0.0989916605993):ℝ):ℂ) * I)‖ ≤ 0.00000014004 := by
  have hl := lg_20
  refine (ecis_approx ((((19892:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.591106364852645428 59.59110640463666532 (-3.0424386) 0.00000004003 (-0.9950882627458) (-0.0989916605993) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_2 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2244670804259:ℝ):ℂ) + (((-0.9744816723803):ℝ):ℂ) * I)‖ ≤ 0.00000015293 := by
  have hl := lg_2
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.9107707614407 13.9107707714752 (-1.3444002) 0.00000005292 0.2244670804259 (-0.9744816723803) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_3 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.998381548777):ℝ):ℂ) + ((0.0568707526159:ℝ):ℂ) * I)‖ ≤ 0.00000011267 := by
  have hl := lg_3
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.048050016063443316 22.048050026097963385 3.0846912 0.00000001266 (-0.998381548777) 0.0568707526159 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_4 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8992290158284):ℝ):ℂ) + (((-0.4374782017161):ℝ):ℂ) * I)‖ ≤ 0.00000011425 := by
  have hl := lg_4
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.8215415228814 27.8215415429504 (-2.6888003) 0.00000001424 (-0.8992290158284) (-0.4374782017161) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_5 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6341536465959:ℝ):ℂ) + (((-0.7732070566861):ℝ):ℂ) * I)‖ ≤ 0.00000013839 := by
  have hl := lg_5
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.299809454206260421 32.29980947427528049 (-0.8838829) 0.00000003838 0.6341536465959 (-0.7732070566861) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_6 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1686843836631):ℝ):ℂ) + ((0.9856701165742:ℝ):ℂ) * I)‖ ≤ 0.00000015451 := by
  have hl := lg_6
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.958820777504143316 35.958820797573163385 1.7402911 0.0000000545 (-0.1686843836631) 0.9856701165742 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_7 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2157281006306:ℝ):ℂ) + (((-0.9764534738523):ℝ):ℂ) * I)‖ ≤ 0.00000014796 := by
  have hl := lg_7
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.052470770957384118 39.052470791026424256 (-1.3533589) 0.00000004795 0.2157281006306 (-0.9764534738523) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_8 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6281618737445):ℝ):ℂ) + ((0.7780826822127:ℝ):ℂ) * I)‖ ≤ 0.00000016418 := by
  have hl := lg_8
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.7323122843221 41.7323123144256 2.2499849 0.00000006417 (-0.6281618737445) 0.7780826822127 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_9 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9935314357508:ℝ):ℂ) + (((-0.1135574135626):ℝ):ℂ) * I)‖ ≤ 0.00000011815 := by
  have hl := lg_9
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.096100032126886632 44.09610005219592677 (-0.1138029) 0.00000001814 0.9935314357508 (-0.1135574135626) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_10 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6111294881018):ℝ):ℂ) + (((-0.7915306366525):ℝ):ℂ) * I)‖ ≤ 0.00000013463 := by
  have hl := lg_10
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.210580215646960421 46.21058024575048049 (-2.2282831) 0.00000003462 (-0.6111294881018) (-0.7915306366525) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_11 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5407478280306):ℝ):ℂ) + ((0.8411847516877:ℝ):ℂ) * I)‖ ≤ 0.00000014331 := by
  have hl := lg_11
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.123360214139938777 48.123360244243478915 2.1421222 0.0000000433 (-0.5407478280306) 0.8411847516877 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_12 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9226533725006:ℝ):ℂ) + ((0.385630333627:ℝ):ℂ) * I)‖ ≤ 0.00000011851 := by
  have hl := lg_12
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.869591538944843316 49.869591569048363385 0.3958909 0.0000000185 0.9226533725006 0.385630333627 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_13 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3525644630121:ℝ):ℂ) + (((-0.9357875289942):ℝ):ℂ) * I)‖ ≤ 0.00000011821 := by
  have hl := lg_13
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.4759686392450373 51.475968669348577438 (-1.2104862) 0.0000000182 0.3525644630121 (-0.9357875289942) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_14 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9031121572511):ℝ):ℂ) + (((-0.4294047406646):ℝ):ℂ) * I)‖ ≤ 0.00000012505 := by
  have hl := lg_14
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.963241532398084118 52.963241562501624256 (-2.6977591) 0.00000002504 (-0.9031121572511) (-0.4294047406646) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_15 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5891544325783):ℝ):ℂ) + ((0.8080204542968:ℝ):ℂ) * I)‖ ≤ 0.00000013577 := by
  have hl := lg_15
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.347859470269703737 54.347859500373243875 2.2008083 0.00000003576 (-0.5891544325783) 0.8080204542968 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_16 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6172256515862:ℝ):ℂ) + ((0.7867861812615:ℝ):ℂ) * I)‖ ≤ 0.0000001213 := by
  have hl := lg_16
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.6430830457628 55.6430830859008 0.9055847 0.00000002129 0.6172256515862 0.7867861812615 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_17 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9520002454266:ℝ):ℂ) + (((-0.3060972602093):ℝ):ℂ) * I)‖ ≤ 0.00000015653 := by
  have hl := lg_17
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.859758580996813946 56.859758621134834015 (-0.3110908) 0.00000005652 0.9520002454266 (-0.3060972602093) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_18 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1123555817815:ℝ):ℂ) + (((-0.9936680649203):ℝ):ℂ) * I)‖ ≤ 0.00000015907 := by
  have hl := lg_18
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.006870793567586632 58.00687082367112677 (-1.458203) 0.00000005906 0.1123555817815 (-0.9936680649203) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_19 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8262861167979):ℝ):ℂ) + (((-0.5632506130724):ℝ):ℂ) * I)‖ ≤ 0.00000012274 := by
  have hl := lg_19
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.091945857240735607 59.091945887344295814 (-2.5432781) 0.00000002273 (-0.8262861167979) (-0.5632506130724) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p069_20 : ‖exp (-((((((20069:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9085105892568):ℝ):ℂ) + ((0.4178618301323:ℝ):ℂ) * I)‖ ≤ 0.00000014544 := by
  have hl := lg_20
  refine (ecis_approx ((((20069:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.121350977087660421 60.12135101722568049 2.7105021 0.00000004543 (-0.9085105892568) 0.4178618301323 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_2 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1344919403932:ℝ):ℂ) + (((-0.9909146875333):ℝ):ℂ) * I)‖ ≤ 0.00000012513 := by
  have hl := lg_2
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.0022661892403 14.0022661993408 (-1.4358956) 0.00000002512 0.1344919403932 (-0.9909146875333) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_3 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9796836766127):ℝ):ℂ) + ((0.2005489801923:ℝ):ℂ) * I)‖ ≤ 0.00000011953 := by
  have hl := lg_3
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.193066838133320964 22.193066848233841165 2.9396744 0.00000001952 (-0.9796836766127) 0.2005489801923 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_4 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9638238358453):ℝ):ℂ) + (((-0.2665400780554):ℝ):ℂ) * I)‖ ≤ 0.00000015025 := by
  have hl := lg_4
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.0045323784806 28.0045323986816 (-2.8717912) 0.00000005024 (-0.9638238358453) (-0.2665400780554) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_5 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4568649467751:ℝ):ℂ) + (((-0.8895360703244):ℝ):ℂ) * I)‖ ≤ 0.0000001429 := by
  have hl := lg_5
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.512255258578936009 32.51225527877995621 (-1.0963287) 0.00000004289 0.4568649467751 (-0.8895360703244) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_6 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0669673715436:ℝ):ℂ) + ((0.9977551659342:ℝ):ℂ) * I)‖ ≤ 0.00000011572 := by
  have hl := lg_6
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.195333027373620964 36.195333047574641165 1.5037788 0.00000001571 0.0669673715436 0.9977551659342 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_7 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0394125624816):ℝ):ℂ) + (((-0.9992230231126):ℝ):ℂ) * I)‖ ≤ 0.00000013253 := by
  have hl := lg_7
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.309330910564059822 39.309330930765100224 (-1.6102191) 0.00000003252 (-0.0394125624816) (-0.9992230231126) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_8 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3937451015009):ℝ):ℂ) + ((0.9192196663698:ℝ):ℂ) * I)‖ ≤ 0.00000014778 := by
  have hl := lg_8
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.0067985677209 42.0067985980224 1.9754986 0.00000004777 (-0.3937451015009) 0.9192196663698 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_9 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9195602157808:ℝ):ℂ) + (((-0.392949118275):ℝ):ℂ) * I)‖ ≤ 0.00000014623 := by
  have hl := lg_9
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.386133676266641928 44.38613369646768233 (-0.4038365) 0.00000004622 0.9195602157808 (-0.392949118275) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_10 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.820009703973):ℝ):ℂ) + (((-0.5723496180941):ℝ):ℂ) * I)‖ ≤ 0.00000012788 := by
  have hl := lg_10
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.514521447819236009 46.51452147812075621 (-2.5322243) 0.00000002787 (-0.820009703973) (-0.5723496180941) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_11 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2520555223123):ℝ):ℂ) + ((0.9677127743657:ℝ):ℂ) * I)‖ ≤ 0.00000016293 := by
  have hl := lg_11
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.439882390046385133 48.439882420347925535 1.8256001 0.00000006292 (-0.2520555223123) 0.9677127743657 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_12 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9976968202285:ℝ):ℂ) + ((0.0678310762558:ℝ):ℂ) * I)‖ ≤ 0.00000014084 := by
  have hl := lg_12
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.197599216613920964 50.197599246915441165 0.0678832 0.00000004083 0.9976968202285 0.0678310762558 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_13 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0217351150977:ℝ):ℂ) + (((-0.9997637644821):ℝ):ℂ) * I)‖ ≤ 0.00000012721 := by
  have hl := lg_13
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.8145419543270217 51.814541984628562102 (-1.5490595) 0.0000000272 0.0217351150977 (-0.9997637644821) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_14 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9954454415066):ℝ):ℂ) + (((-0.0953329560005):ℝ):ℂ) * I)‖ ≤ 0.00000015765 := by
  have hl := lg_14
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.311597099804359822 53.311597130105900224 (-3.0461147) 0.00000005764 (-0.9954454415066) (-0.0953329560005) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_15 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2691875789427):ℝ):ℂ) + ((0.9630877672059:ℝ):ℂ) * I)‖ ≤ 0.00000016241 := by
  have hl := lg_15
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.705322096712256973 54.705322127013797375 1.8433457 0.0000000624 (-0.2691875789427) 0.9630877672059 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_16 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8579127257558:ℝ):ℂ) + ((0.5137954407993:ℝ):ℂ) * I)‖ ≤ 0.00000013276 := by
  have hl := lg_16
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.0090647569612 56.0090647973632 0.539603 0.00000003275 0.8579127257558 0.5137954407993 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_17 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7743715944381:ℝ):ℂ) + (((-0.6327310911655):ℝ):ℂ) * I)‖ ≤ 0.00000012236 := by
  have hl := lg_17
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.233742742274983234 57.233742782677003435 (-0.685075) 0.00000002235 0.7743715944381 (-0.6327310911655) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_18 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2657056150233):ℝ):ℂ) + (((-0.9640542132804):ℝ):ℂ) * I)‖ ≤ 0.00000013121 := by
  have hl := lg_18
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.388399865506941928 58.38839989580848233 (-1.8397321) 0.0000000312 (-0.2657056150233) (-0.9640542132804) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_19 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9781041166788):ℝ):ℂ) + (((-0.2081161613698):ℝ):ℂ) * I)‖ ≤ 0.00000016224 := by
  have hl := lg_19
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.480611802387767203 59.480611832689327806 (-2.9319441) 0.00000006223 (-0.9781041166788) (-0.2081161613698) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_20 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6774343339521):ℝ):ℂ) + ((0.7355832537263:ℝ):ℂ) * I)‖ ≤ 0.00000013475 := by
  have hl := lg_20
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.516787637059536009 60.51678767746155621 2.3150654 0.00000003474 (-0.6774343339521) 0.7355832537263 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_21 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2390050025513:ℝ):ℂ) + ((0.9710183359522:ℝ):ℂ) * I)‖ ≤ 0.00000012311 := by
  have hl := lg_21
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.502397748697380786 61.502397778998941389 1.3294553 0.0000000231 0.2390050025513 0.9710183359522 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_22 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9250213651507:ℝ):ℂ) + ((0.3799150879009:ℝ):ℂ) * I)‖ ≤ 0.00000014791 := by
  have hl := lg_22
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.442148579286685133 62.442148619688725535 0.3897045 0.0000000479 0.9250213651507 0.3799150879009 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_23 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8735898891683:ℝ):ℂ) + (((-0.4866628253144):ℝ):ℂ) * I)‖ ≤ 0.00000013683 := by
  have hl := lg_23
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.340118634980082566 63.340118675382143169 (-0.5082656) 0.00000003682 0.8735898891683 (-0.4866628253144) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_24 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2013969910097:ℝ):ℂ) + (((-0.9795096998051):ℝ):ℂ) * I)‖ ≤ 0.00000016596 := by
  have hl := lg_24
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.199865405854220964 64.199865446256241165 (-1.3680124) 0.00000006595 0.2013969910097 (-0.9795096998051) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_25 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5825489220952):ℝ):ℂ) + (((-0.8127956405856):ℝ):ℂ) * I)‖ ≤ 0.00000015465 := by
  have hl := lg_25
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.024510517157872018 65.02451055755991242 (-2.1926575) 0.00000005464 (-0.5825489220952) (-0.8127956405856) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_26 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9877574003199):ℝ):ℂ) + (((-0.1559978132195):ℝ):ℂ) * I)‖ ≤ 0.00000012824 := by
  have hl := lg_26
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.8168081435673217 65.816808183969362102 (-2.9849551) 0.00000002823 (-0.9877574003199) (-0.1559978132195) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_27 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8220725312327):ℝ):ℂ) + ((0.5693827827869:ℝ):ℂ) * I)‖ ≤ 0.00000016459 := by
  have hl := lg_27
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.579200514399962892 66.579200544701523495 2.5358378 0.00000006458 (-0.8220725312327) 0.5693827827869 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_28 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2283463059137):ℝ):ℂ) + ((0.973579973384:ℝ):ℂ) * I)‖ ≤ 0.00000015049 := by
  have hl := lg_28
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.313863289044659822 67.313863329446700224 1.8011751 0.00000005048 (-0.2283463059137) 0.973579973384 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_29 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4604490756266:ℝ):ℂ) + ((0.8876861206275:ℝ):ℂ) * I)‖ ≤ 0.00000013844 := by
  have hl := lg_29
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.022743040552125092 68.022743080954185695 1.0922953 0.00000003843 0.4604490756266 0.8876861206275 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p201_30 : ‖exp (-((((((20201:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.918134254087:ℝ):ℂ) + ((0.3962694682563:ℝ):ℂ) * I)‖ ≤ 0.00000014739 := by
  have hl := lg_30
  refine (ecis_approx ((((20201:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.707588285952556973 68.707588326354597375 0.4074501 0.00000004738 0.918134254087 0.3962694682563 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_2 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0433916986441:ℝ):ℂ) + (((-0.9990581366911):ℝ):ℂ) * I)‖ ≤ 0.00000011286 := by
  have hl := lg_2
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.0937616170399 14.0937616272064 (-1.527391) 0.00000001285 0.0433916986441 (-0.9990581366911) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_3 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9404192623627):ℝ):ℂ) + ((0.3400170742726:ℝ):ℂ) * I)‖ ≤ 0.00000014167 := by
  have hl := lg_3
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.338083660203198612 22.338083670369718945 2.7946576 0.00000004166 (-0.9404192623627) 0.3400170742726 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_4 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.996234320747):ℝ):ℂ) + (((-0.086701658957):ℝ):ℂ) * I)‖ ≤ 0.00000012571 := by
  have hl := lg_4
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.1875232340798 28.1875232544128 (-3.054782) 0.0000000257 (-0.996234320747) (-0.086701658957) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_5 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2590338982684:ℝ):ℂ) + (((-0.9658682309445):ℝ):ℂ) * I)‖ ≤ 0.0000001474 := by
  have hl := lg_5
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.724701062951611597 32.72470108328463193 (-1.3087745) 0.00000004739 0.2590338982684 (-0.9658682309445) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_6 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2988904355261:ℝ):ℂ) + ((0.954287434451:ℝ):ℂ) * I)‖ ≤ 0.00000015451 := by
  have hl := lg_6
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.431845277243098612 36.431845297576118945 1.2672666 0.0000000545 0.2988904355261 0.954287434451 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_7 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2919670663735):ℝ):ℂ) + (((-0.9564283727241):ℝ):ℂ) * I)‖ ≤ 0.00000012744 := by
  have hl := lg_7
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.566191050170735526 39.566191070503776192 (-1.8670792) 0.00000002743 (-0.2919670663735) (-0.9564283727241) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_8 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.129848290395):ℝ):ℂ) + ((0.991533873088:ℝ):ℂ) * I)‖ ≤ 0.00000013138 := by
  have hl := lg_8
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.2812848511197 42.2812848816192 1.7010123 0.00000003137 (-0.129848290395) 0.991533873088 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_9 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7687767189175:ℝ):ℂ) + (((-0.6395172839341):ℝ):ℂ) * I)‖ ≤ 0.00000012987 := by
  have hl := lg_9
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.676167320406397224 44.67616734073943789 (-0.6938702) 0.00000002986 0.7687767189175 (-0.6395172839341) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_10 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9537185941671):ℝ):ℂ) + (((-0.3007005868407):ℝ):ℂ) * I)‖ ≤ 0.00000016025 := by
  have hl := lg_10
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.818462679991511597 46.81846271049103193 (-2.8361655) 0.00000006024 (-0.9537185941671) (-0.3007005868407) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_11 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0616792516531:ℝ):ℂ) + ((0.9980960223923:ℝ):ℂ) * I)‖ ≤ 0.00000013903 := by
  have hl := lg_11
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.756404565952831489 48.756404596452372155 1.5090779 0.00000003902 0.0616792516531 0.9980960223923 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_12 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9663579641162:ℝ):ℂ) + (((-0.2572008654517):ℝ):ℂ) * I)‖ ≤ 0.00000016317 := by
  have hl := lg_12
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.525606894282998612 50.525606924782518945 (-0.2601245) 0.00000006316 0.9663579641162 (-0.2572008654517) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_13 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.311562059871):ℝ):ℂ) + (((-0.9502258062414):ℝ):ℂ) * I)‖ ≤ 0.00000014249 := by
  have hl := lg_13
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.1531152694090061 52.153115299908546766 (-1.8876328) 0.00000004248 (-0.311562059871) (-0.9502258062414) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_14 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9681964929932):ℝ):ℂ) + ((0.2501910284:ℝ):ℂ) * I)‖ ≤ 0.00000013311 := by
  have hl := lg_14
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.659952667210635526 53.659952697710176192 2.8887151 0.0000000331 (-0.9681964929932) 0.2501910284 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_15 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.084811322197:ℝ):ℂ) + ((0.9963970291139:ℝ):ℂ) * I)‖ ≤ 0.00000014148 := by
  have hl := lg_15
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.062784723154810209 55.062784753654350875 1.485883 0.00000004147 0.084811322197 0.9963970291139 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_16 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9849656458275:ℝ):ℂ) + ((0.172750330071:ℝ):ℂ) * I)‖ ≤ 0.00000014422 := by
  have hl := lg_16
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.3750464681596 56.3750465088256 0.1736213 0.00000004421 0.9849656458275 0.172750330071 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_17 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4896925774258:ℝ):ℂ) + (((-0.8718951654953):ℝ):ℂ) * I)‖ ≤ 0.00000016108 := by
  have hl := lg_17
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.607726903553152522 57.607726944219172855 (-1.0590592) 0.00000006107 0.4896925774258 (-0.8718951654953) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_18 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6055564183561):ℝ):ℂ) + (((-0.7958023775883):ℝ):ℂ) * I)‖ ≤ 0.00000012718 := by
  have hl := lg_18
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.769928937446297224 58.76992896794583789 (-2.2212612) 0.00000002717 (-0.6055564183561) (-0.7958023775883) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_19 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.984019140383):ℝ):ℂ) + ((0.178062716501:ℝ):ℂ) * I)‖ ≤ 0.00000012428 := by
  have hl := lg_19
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.869277747534798799 59.869277778034359798 2.9625753 0.00000002427 (-0.984019140383) 0.178062716501 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_20 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3418008311869):ℝ):ℂ) + ((0.9397724148951:ℝ):ℂ) * I)‖ ≤ 0.00000016592 := by
  have hl := lg_20
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.912224297031411597 60.91222433769743193 1.9196288 0.00000006591 (-0.3418008311869) 0.9397724148951 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_21 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5997735103637:ℝ):ℂ) + ((0.8001698171426:ℝ):ℂ) * I)‖ ≤ 0.00000016144 := by
  have hl := lg_21
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.904274710373934138 61.904274740873495137 0.9275783 0.00000006143 0.5997735103637 0.8001698171426 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_22 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9998323198705:ℝ):ℂ) + (((-0.0183120764076):ℝ):ℂ) * I)‖ ≤ 0.00000015188 := by
  have hl := lg_22
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.850166182992731489 62.850166223658772155 (-0.0183131) 0.00000005187 0.9998323198705 (-0.0183120764076) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_23 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6041075767549:ℝ):ℂ) + (((-0.7969027768225):ℝ):ℂ) * I)‖ ≤ 0.00000014023 := by
  have hl := lg_23
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.754003871345478878 63.754003912011539877 (-0.9221508) 0.00000004022 0.6041075767549 (-0.7969027768225) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_24 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2150267038324):ℝ):ℂ) + (((-0.9766081694508):ℝ):ℂ) * I)‖ ≤ 0.00000016049 := by
  have hl := lg_24
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.619368511322898612 64.619368551988918945 (-1.7875155) 0.00000006048 (-0.2150267038324) (-0.9766081694508) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_25 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8658029291122):ℝ):ℂ) + (((-0.5003851395236):ℝ):ℂ) * I)‖ ≤ 0.00000014591 := by
  have hl := lg_25
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.449402125903223194 65.44940216656926386 (-2.6175491) 0.0000000459 (-0.8658029291122) (-0.5003851395236) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_26 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.962850028401):ℝ):ℂ) + ((0.2700367059588:ℝ):ℂ) * I)‖ ≤ 0.00000014815 := by
  have hl := lg_26
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.2468768864489061 66.246876927114946766 2.8681615 0.00000004814 (-0.962850028401) 0.2700367059588 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_27 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5055256390828):ℝ):ℂ) + ((0.8628115832692:ℝ):ℂ) * I)‖ ≤ 0.00000013215 := by
  have hl := lg_27
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.014250980609595836 67.014251011109156835 2.1007874 0.00000003214 (-0.5055256390828) 0.8628115832692 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_28 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2079436923268:ℝ):ℂ) + ((0.9781407980559:ℝ):ℂ) * I)‖ ≤ 0.00000014596 := by
  have hl := lg_28
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.753714284250535526 67.753714324916576192 1.3613241 0.00000004595 0.2079436923268 0.9781407980559 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_29 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7974058587526:ℝ):ℂ) + ((0.6034433663792:ℝ):ℂ) * I)‖ ≤ 0.00000015168 := by
  have hl := lg_29
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.467226089973088436 68.467226130639149435 0.6478123 0.00000005167 0.7974058587526 0.6034433663792 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p333_30 : ‖exp (-((((((20333:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9991386666456:ℝ):ℂ) + (((-0.0414960819072):ℝ):ℂ) * I)‖ ≤ 0.0000001388 := by
  have hl := lg_30
  refine (ecis_approx ((((20333:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.156546340194710209 69.156546380860750875 (-0.041508) 0.00000003879 0.9991386666456 (-0.0414960819072) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_2 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0252136009517):ℝ):ℂ) + (((-0.9996820866289):ℝ):ℂ) * I)‖ ≤ 0.00000012648 := by
  have hl := lg_2
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.1623831878896 14.1623831981056 (-1.5960126) 0.00000002647 (-0.0252136009517) (-0.9996820866289) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_3 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8979541730994):ℝ):ℂ) + ((0.440088971572:ℝ):ℂ) * I)‖ ≤ 0.00000015198 := by
  have hl := lg_3
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.446846276755606848 22.44684628697162728 2.6858949 0.00000005197 (-0.8979541730994) 0.440088971572 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_4 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.998728548019):ℝ):ℂ) + ((0.0504111773304:ℝ):ℂ) * I)‖ ≤ 0.00000016013 := by
  have hl := lg_4
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.3247663757792 28.3247663962112 3.0911601 0.00000006012 (-0.998728548019) 0.0504111773304 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_5 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1025070537715:ℝ):ℂ) + (((-0.9947322775134):ℝ):ℂ) * I)‖ ≤ 0.00000011968 := by
  have hl := lg_5
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.884035416231118288 32.88403543666313872 (-1.4681089) 0.00000001967 0.1025070537715 (-0.9947322775134) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_6 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4625896310022:ℝ):ℂ) + ((0.8865725200395:ℝ):ℂ) * I)‖ ≤ 0.00000014201 := by
  have hl := lg_6
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.609229464645206848 36.60922948507722728 1.0898824 0.000000042 0.4625896310022 0.8865725200395 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_7 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4696797334545):ℝ):ℂ) + (((-0.8828368750664):ℝ):ℂ) * I)‖ ≤ 0.00000013225 := by
  have hl := lg_7
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.758836154875742304 39.758836175307783168 (-2.0597243) 0.00000003224 (-0.4696797334545) (-0.8828368750664) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_8 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0755765945663:ℝ):ℂ) + ((0.997139999375:ℝ):ℂ) * I)‖ ≤ 0.00000014407 := by
  have hl := lg_8
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.4871495636688 42.4871495943168 1.4951476 0.00000004406 0.0755765945663 0.997139999375 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_9 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6126434788033:ℝ):ℂ) + (((-0.7903593915934):ℝ):ℂ) * I)‖ ≤ 0.0000001237 := by
  have hl := lg_9
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.893692553511213696 44.89369257394325456 (-0.9113954) 0.00000002369 0.6126434788033 (-0.7903593915934) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_10 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9970006105295):ℝ):ℂ) + (((-0.077393682469):ℝ):ℂ) * I)‖ ≤ 0.00000014615 := by
  have hl := lg_10
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.046418604120718288 47.04641863476873872 (-3.0641215) 0.00000004614 (-0.9970006105295) (-0.077393682469) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_11 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2946699614226:ℝ):ℂ) + ((0.9555990863512:ℝ):ℂ) * I)‖ ≤ 0.00000015957 := by
  have hl := lg_11
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.993796197882666256 48.99379622853070712 1.2716862 0.00000005956 0.2946699614226 0.9555990863512 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_12 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8746271164207:ℝ):ℂ) + (((-0.4847962533082):ℝ):ℂ) * I)‖ ≤ 0.00000012576 := by
  have hl := lg_12
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.771612652534806848 50.77161268318282728 (-0.5061302) 0.00000002575 0.8746271164207 (-0.4847962533082) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_13 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5402771846974):ℝ):ℂ) + (((-0.8414871143917):ℝ):ℂ) * I)‖ ≤ 0.00000012895 := by
  have hl := lg_13
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.4070452557204944 52.407045286368535264 (-2.1415628) 0.00000002894 (-0.5402771846974) (-0.8414871143917) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_14 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8707138884937):ℝ):ℂ) + ((0.4917899188635:ℝ):ℂ) * I)‖ ≤ 0.00000012187 := by
  have hl := lg_14
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.921219342765342304 53.921219373413383168 2.6274484 0.00000002186 (-0.8707138884937) 0.4917899188635 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_15 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3457239745184:ℝ):ℂ) + ((0.9383362581949:ℝ):ℂ) * I)‖ ≤ 0.00000015903 := by
  have hl := lg_15
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.330881692986725136 55.330881723634766 1.2177861 0.00000005902 0.3457239745184 0.9383362581949 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_16 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9949174371399:ℝ):ℂ) + (((-0.1006940577935):ℝ):ℂ) * I)‖ ≤ 0.00000012782 := by
  have hl := lg_16
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.6495327515584 56.6495327924224 (-0.100865) 0.00000002781 0.9949174371399 (-0.1006940577935) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_17 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2291934808054:ℝ):ℂ) + (((-0.9733808855511):ℝ):ℂ) * I)‖ ≤ 0.00000014012 := by
  have hl := lg_17
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.888215024511779488 57.88821506537579992 (-1.3395473) 0.00000004011 0.2291934808054 (-0.9733808855511) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_18 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8055550739644):ℝ):ℂ) + (((-0.5925209049129):ℝ):ℂ) * I)‖ ≤ 0.00000012323 := by
  have hl := lg_18
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.056075741400813696 59.05607577204885456 (-2.507408) 0.00000002322 (-0.8055550739644) (-0.5925209049129) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_19 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8913341385219):ℝ):ℂ) + ((0.4533469459459:ℝ):ℂ) * I)‖ ≤ 0.00000016526 := by
  have hl := lg_19
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.160777206395072496 60.160777237043133792 2.6710759 0.00000006525 (-0.8913341385219) 0.4533469459459 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_20 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0522311953683):ℝ):ℂ) + ((0.9986350195292:ℝ):ℂ) * I)‖ ≤ 0.00000016109 := by
  have hl := lg_20
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.208801792010318288 61.20880183287433872 1.6230513 0.00000006108 (-0.0522311953683) 0.9986350195292 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_21 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8102776491609:ℝ):ℂ) + ((0.5860461852707:ℝ):ℂ) * I)‖ ≤ 0.00000014018 := by
  have hl := lg_21
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.205682431631349152 62.205682462279410448 0.6261706 0.00000004017 0.8102776491609 0.5860461852707 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_22 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9478656296717:ℝ):ℂ) + (((-0.3186702811483):ℝ):ℂ) * I)‖ ≤ 0.00000015486 := by
  have hl := lg_22
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.156179385772266256 63.15617942663630712 (-0.3243263) 0.00000005485 0.9478656296717 (-0.3186702811483) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_23 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3318194294893:ℝ):ℂ) + (((-0.9433429207947):ℝ):ℂ) * I)‖ ≤ 0.0000001677 := by
  have hl := lg_23
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.064417798619526112 64.064417839483587408 (-1.2325647) 0.00000006769 0.3318194294893 (-0.9433429207947) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_24 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5066946291919):ℝ):ℂ) + (((-0.8621256014883):ℝ):ℂ) * I)‖ ≤ 0.00000013139 := by
  have hl := lg_24
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.933995840424406848 64.93399588128842728 (-2.1021428) 0.00000003138 (-0.5066946291919) (-0.8621256014883) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_25 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9789846077246):ℝ):ℂ) + (((-0.203934149961):ℝ):ℂ) * I)‖ ≤ 0.00000013935 := by
  have hl := lg_25
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.768070832462236576 65.76807087332627744 (-2.9362178) 0.00000003934 (-0.9789846077246) (-0.203934149961) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_26 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.827597257009):ℝ):ℂ) + ((0.5613223495728:ℝ):ℂ) * I)‖ ≤ 0.00000013538 := by
  have hl := lg_26
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.5694284436100944 66.569428484474135264 2.5456099 0.00000003537 (-0.827597257009) 0.5613223495728 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_27 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2022973165667):ℝ):ℂ) + ((0.97932415252:ℝ):ℂ) * I)‖ ≤ 0.00000014872 := by
  have hl := lg_27
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.340538830266820544 67.34053886091488184 1.7744995 0.00000004871 (-0.2022973165667) 0.97932415252 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_28 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5135874048492:ℝ):ℂ) + ((0.8580372821622:ℝ):ℂ) * I)‖ ≤ 0.00000014834 := by
  have hl := lg_28
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.083602530654942304 68.083602571518983168 1.0314358 0.00000004833 0.5135874048492 0.8580372821622 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_29 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9509666341567:ℝ):ℂ) + ((0.3092934863858:ℝ):ℂ) * I)‖ ≤ 0.00000013894 := by
  have hl := lg_29
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.800588377038810944 68.80058841790287224 0.31445 0.00000003893 0.9509666341567 0.3092934863858 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p432_30 : ‖exp (-((((((20432:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9293210022191:ℝ):ℂ) + (((-0.3692729002168):ℝ):ℂ) * I)‖ ≤ 0.00000014278 := by
  have hl := lg_30
  refine (ecis_approx ((((20432:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.493264880876325136 69.493264921740366 (-0.3782265) 0.00000004277 0.9293210022191 (-0.3692729002168) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_2 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0937001186403):ℝ):ℂ) + (((-0.9956004659332):ℝ):ℂ) * I)‖ ≤ 0.00000015466 := by
  have hl := lg_2
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.2310047587393 14.2310047690048 (-1.6646341) 0.00000005465 (-0.0937001186403) (-0.9956004659332) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_3 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8448774126355):ℝ):ℂ) + ((0.5349599588264:ℝ):ℂ) * I)‖ ≤ 0.00000013543 := by
  have hl := lg_3
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.555608893308015084 22.555608903573535615 2.5771323 0.00000003542 (-0.8448774126355) 0.5349599588264 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_4 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9824405553949):ℝ):ℂ) + ((0.1865758686825:ℝ):ℂ) * I)‖ ≤ 0.00000011843 := by
  have hl := lg_4
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.4620095174786 28.4620095380096 2.953917 0.00000001842 (-0.9824405553949) 0.1865758686825 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_5 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0566165826734):ℝ):ℂ) + (((-0.9983959948668):ℝ):ℂ) * I)‖ ≤ 0.00000015416 := by
  have hl := lg_5
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.043369769510624979 33.04336979004164551 (-1.6274432) 0.00000005415 (-0.0566165826734) (-0.9983959948668) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_6 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6117714981043:ℝ):ℂ) + ((0.7910345340801:ℝ):ℂ) * I)‖ ≤ 0.00000012952 := by
  have hl := lg_6
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.786613652047315084 36.786613672578335615 0.9124982 0.00000002951 0.6117714981043 0.7910345340801 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_7 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6300154243289):ℝ):ℂ) + (((-0.7765826196182):ℝ):ℂ) * I)‖ ≤ 0.00000013705 := by
  have hl := lg_7
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.951481259580749082 39.951481280111790144 (-2.2523694) 0.00000003704 (-0.6300154243289) (-0.7765826196182) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_8 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2778098185698:ℝ):ℂ) + ((0.9606360937973:ℝ):ℂ) * I)‖ ≤ 0.00000015677 := by
  have hl := lg_8
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.6930142762179 42.6930143070144 1.2892829 0.00000005676 0.2778098185698 0.9606360937973 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_9 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4276357817062:ℝ):ℂ) + (((-0.9039511260043):ℝ):ℂ) * I)‖ ≤ 0.0000001569 := by
  have hl := lg_9
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.111217786616030168 45.11121780714707123 (-1.1289206) 0.00000005689 0.4276357817062 (-0.9039511260043) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_10 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.988698520924):ℝ):ℂ) + ((0.1499174250365:ℝ):ℂ) * I)‖ ≤ 0.0000001292 := by
  have hl := lg_10
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.274374528249924979 47.27437455904644551 2.9911079 0.00000002919 (-0.988698520924) 0.1499174250365 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_11 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5111323525021:ℝ):ℂ) + ((0.8595020175809:ℝ):ℂ) * I)‖ ≤ 0.00000012764 := by
  have hl := lg_11
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.231187829812501023 49.231187860609042085 1.0342946 0.00000002763 0.5111323525021 0.8595020175809 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_12 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7302312204264:ℝ):ℂ) + (((-0.6832000912723):ℝ):ℂ) * I)‖ ≤ 0.00000014667 := by
  have hl := lg_12
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.017618410786615084 51.017618441583135615 (-0.752136) 0.00000004666 0.7302312204264 (-0.6832000912723) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_13 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7343417881876):ℝ):ℂ) + (((-0.6787798892801):ℝ):ℂ) * I)‖ ≤ 0.00000011542 := by
  have hl := lg_13
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.6609752420319827 52.660975272828523762 (-2.3954928) 0.00000001541 (-0.7343417881876) (-0.6787798892801) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_14 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7141334229005):ℝ):ℂ) + ((0.700009610127:ℝ):ℂ) * I)‖ ≤ 0.00000014631 := by
  have hl := lg_14
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.182486018320049082 54.182486049116590144 2.3661817 0.0000000463 (-0.7141334229005) 0.700009610127 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_15 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5819359522279:ℝ):ℂ) + ((0.8132346202079:ℝ):ℂ) * I)‖ ≤ 0.00000012901 := by
  have hl := lg_15
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.598978662818640063 55.598978693615181125 0.9496891 0.000000029 0.5819359522279 0.8132346202079 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_16 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9303788929577:ℝ):ℂ) + (((-0.3665993938057):ℝ):ℂ) * I)‖ ≤ 0.00000012967 := by
  have hl := lg_16
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.9240190349572 56.9240190760192 (-0.3753513) 0.00000002966 0.9303788929577 (-0.3665993938057) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_17 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0492191790403):ℝ):ℂ) + (((-0.9987880017373):ℝ):ℂ) * I)‖ ≤ 0.00000012193 := by
  have hl := lg_17
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.168703145470406454 58.168703186532426985 (-1.6200354) 0.00000002192 (-0.0492191790403) (-0.9987880017373) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_18 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9400437197557):ℝ):ℂ) + (((-0.3410539616665):ℝ):ℂ) * I)‖ ≤ 0.00000011928 := by
  have hl := lg_18
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.342222545355330168 59.34222257615187123 (-2.7935548) 0.00000001927 (-0.9400437197557) (-0.3410539616665) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_19 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7234454980114):ℝ):ℂ) + ((0.6903814969849:ℝ):ℂ) * I)‖ ≤ 0.00000012427 := by
  have hl := lg_19
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.452276665255346193 60.452276696051907786 2.3795764 0.00000002426 (-0.7234454980114) 0.6903814969849 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_20 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2418990271329:ℝ):ℂ) + ((0.9703014277389:ℝ):ℂ) * I)‖ ≤ 0.00000015627 := by
  have hl := lg_20
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.505379286989224979 61.50537932805124551 1.3264738 0.00000005626 0.2418990271329 0.9703014277389 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_21 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9477264078905:ℝ):ℂ) + ((0.3190840888967:ℝ):ℂ) * I)‖ ≤ 0.00000011892 := by
  have hl := lg_21
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.507090152888764166 62.507090183685325759 0.3247629 0.00000001891 0.9477264078905 0.3190840888967 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_22 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8078274471039:ℝ):ℂ) + (((-0.5894190493236):ℝ):ℂ) * I)‖ ≤ 0.00000015783 := by
  have hl := lg_22
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.462192588551801023 63.462192629613842085 (-0.6303395) 0.00000005782 0.8078274471039 (-0.5894190493236) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_23 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0278140392927:ℝ):ℂ) + (((-0.9996131147689):ℝ):ℂ) * I)‖ ≤ 0.00000014592 := by
  have hl := lg_23
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.374831725893573346 64.374831766955634939 (-1.5429787) 0.00000004591 0.0278140392927 (-0.9996131147689) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_24 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7486170811796):ℝ):ℂ) + (((-0.6630026136695):ℝ):ℂ) * I)‖ ≤ 0.00000013881 := by
  have hl := lg_24
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.248623169525915084 65.248623210587935615 (-2.4167701) 0.0000000388 (-0.7486170811796) (-0.6630026136695) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_25 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9935891128126):ℝ):ℂ) + ((0.1130516450461:ℝ):ℂ) * I)‖ ≤ 0.00000013997 := by
  have hl := lg_25
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.086739539021249958 66.08673958008329102 3.0282988 0.00000003996 (-0.9935891128126) 0.1130516450461 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_26 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6069856556677):ℝ):ℂ) + ((0.7947127869872:ℝ):ℂ) * I)‖ ≤ 0.00000016287 := by
  have hl := lg_26
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.8919800007712827 66.891980041833323762 2.2230584 0.00000006286 (-0.6069856556677) 0.7947127869872 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_27 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1222778443781:ℝ):ℂ) + ((0.9924959086939:ℝ):ℂ) * I)‖ ≤ 0.00000013176 := by
  have hl := lg_27
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.666826679924045252 67.666826710720606845 1.4482117 0.00000003175 0.1222778443781 0.9924959086939 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_28 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7638442804662:ℝ):ℂ) + ((0.6454005850625:ℝ):ℂ) * I)‖ ≤ 0.00000013916 := by
  have hl := lg_28
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.413490777059349082 68.413490818121390144 0.7015476 0.00000003915 0.7638442804662 0.6454005850625 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_29 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9998211677848:ℝ):ℂ) + (((-0.0189111726104):ℝ):ℂ) * I)‖ ≤ 0.00000012621 := by
  have hl := lg_29
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.133950664104533452 69.133950705166595045 (-0.0189123) 0.0000000262 0.9998211677848 (-0.0189111726104) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p531_30 : ‖exp (-((((((20531:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7551292334698:ℝ):ℂ) + (((-0.6555759610902):ℝ):ℂ) * I)‖ ≤ 0.00000015743 := by
  have hl := lg_30
  refine (ecis_approx ((((20531:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.829983421557940063 69.829983462619981125 (-0.7149451) 0.00000005742 0.7551292334698 (-0.6555759610902) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_2 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1446217303848):ℝ):ℂ) + (((-0.9894870161351):ℝ):ℂ) * I)‖ ≤ 0.00000014604 := by
  have hl := lg_2
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.2822976500815 14.282297660384 (-1.715927) 0.00000004603 (-0.1446217303848) (-0.9894870161351) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_3 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7986440374643):ℝ):ℂ) + ((0.6018037066802:ℝ):ℂ) * I)‖ ≤ 0.00000012608 := by
  have hl := lg_3
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.63690620265021922 22.636906212952739825 2.495835 0.00000002607 (-0.7986440374643) 0.6018037066802 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_4 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9581690794423):ℝ):ℂ) + ((0.2862027515129:ℝ):ℂ) * I)‖ ≤ 0.00000013575 := by
  have hl := lg_4
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.564595300163 28.564595320768 2.8513312 0.00000003574 (-0.9581690794423) 0.2862027515129 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_5 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1748419794769):ℝ):ℂ) + (((-0.9845965073124):ℝ):ℂ) * I)‖ ≤ 0.00000015971 := by
  have hl := lg_5
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.162468174992276445 33.16246819559729705 (-1.7465416) 0.0000000597 (-0.1748419794769) (-0.9845965073124) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_6 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7109782367102:ℝ):ℂ) + ((0.7032140121787:ℝ):ℂ) * I)‖ ≤ 0.00000013027 := by
  have hl := lg_6
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.91920385273171922 36.919203873336739825 0.779908 0.00000003026 0.7109782367102 0.7032140121787 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_7 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7349347612623):ℝ):ℂ) + (((-0.6781378153871):ℝ):ℂ) * I)‖ ≤ 0.00000013252 := by
  have hl := lg_7
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.09547861057237031 40.09547863117741152 (-2.3963668) 0.00000003251 (-0.7349347612623) (-0.6781378153871) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_8 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4217659770019:ℝ):ℂ) + ((0.9067047262718:ℝ):ℂ) * I)‖ ≤ 0.00000013091 := by
  have hl := lg_8
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.8468929502445 42.846892981152 1.1354042 0.0000000309 0.4217659770019 0.9067047262718 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_9 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2756646040877:ℝ):ℂ) + (((-0.9612538822045):ℝ):ℂ) * I)‖ ≤ 0.00000014497 := by
  have hl := lg_9
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.27381240530043844 45.27381242590547965 (-1.2915153) 0.00000004496 0.2756646040877 (-0.9612538822045) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_10 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9489594766272):ℝ):ℂ) + ((0.315398020791:ℝ):ℂ) * I)‖ ≤ 0.00000013238 := by
  have hl := lg_10
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.444765825073776445 47.44476585598129705 2.8207166 0.00000003237 (-0.9489594766272) 0.315398020791 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_11 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6548211290731:ℝ):ℂ) + ((0.7557838903545:ℝ):ℂ) * I)‖ ≤ 0.00000015343 := by
  have hl := lg_11
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.408632079941872465 49.408632110849413675 0.8568504 0.00000005342 0.6548211290731 0.7557838903545 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_12 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5929981512361:ℝ):ℂ) + (((-0.8052038205514):ℝ):ℂ) * I)‖ ≤ 0.00000015464 := by
  have hl := lg_12
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.20150150281321922 51.201501533720739825 (-0.9360191) 0.00000005463 0.5929981512361 (-0.8052038205514) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_13 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8492180999834):ℝ):ℂ) + (((-0.5280422507597):ℝ):ℂ) * I)‖ ≤ 0.00000016303 := by
  have hl := lg_13
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.8507814944264285 52.85078152533396971 (-2.5852991) 0.00000006302 (-0.8492180999834) (-0.5280422507597) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_14 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5647210206729):ℝ):ℂ) + ((0.8252818723325:ℝ):ℂ) * I)‖ ≤ 0.00000012696 := by
  have hl := lg_14
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.37777626065387031 54.37777629156141152 2.1708915 0.00000002695 (-0.5647210206729) 0.8252818723325 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_15 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7321703321215:ℝ):ℂ) + ((0.6811215785461:ℝ):ℂ) * I)‖ ≤ 0.00000014395 := by
  have hl := lg_15
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.799374377642495665 55.799374408550036875 0.7492934 0.00000004394 0.7321703321215 0.6811215785461 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_16 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.836175973857:ℝ):ℂ) + (((-0.54846124817):ℝ):ℂ) * I)‖ ≤ 0.00000016431 := by
  have hl := lg_16
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.129190600326 57.129190641536 (-0.5805229) 0.0000000643 0.836175973857 (-0.54846124817) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_17 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2560143450101):ℝ):ℂ) + (((-0.9666729825271):ℝ):ℂ) * I)‖ ≤ 0.00000013178 := by
  have hl := lg_17
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.37836093285362257 58.378360974063643175 (-1.8296932) 0.00000003177 (-0.2560143450101) (-0.9666729825271) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_18 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9910153275161):ℝ):ℂ) + (((-0.1337483465689):ℝ):ℂ) * I)‖ ≤ 0.00000012169 := by
  have hl := lg_18
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.55611005538193844 59.55611008628947965 (-3.0074423) 0.00000002168 (-0.9910153275161) (-0.1337483465689) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_19 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5571016461322):ℝ):ℂ) + ((0.8304443123218:ℝ):ℂ) * I)‖ ≤ 0.00000012215 := by
  have hl := lg_19
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.670165149655954815 60.67016518056351663 2.1616879 0.00000002214 (-0.5571016461322) 0.8304443123218 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_20 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4493224081756:ℝ):ℂ) + ((0.8933696734898:ℝ):ℂ) * I)‖ ≤ 0.00000014458 := by
  have hl := lg_20
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.727063475155276445 61.72706351636529705 1.1047896 0.00000004457 0.4493224081756 0.8933696734898 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_21 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9950571159873:ℝ):ℂ) + ((0.0993042593397:ℝ):ℂ) * I)‖ ≤ 0.00000015859 := by
  have hl := lg_21
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.73238481322258953 62.732384844130151345 0.0994682 0.00000005858 0.9950571159873 0.0993042593397 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_22 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6531369060071:ℝ):ℂ) + (((-0.7572398444426):ℝ):ℂ) * I)‖ ≤ 0.00000014179 := by
  have hl := lg_22
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.690929730023372465 63.690929771233413675 (-0.8590767) 0.00000004178 0.6531369060071 (-0.7572398444426) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_23 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2027925349025):ℝ):ℂ) + (((-0.9792217255489):ℝ):ℂ) * I)‖ ≤ 0.00000016722 := by
  have hl := lg_23
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.60685829779538643 64.606858339005448245 (-1.7750052) 0.00000006721 (-0.2027925349025) (-0.9792217255489) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_24 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8824991444977):ℝ):ℂ) + (((-0.4703140013462):ℝ):ℂ) * I)‖ ≤ 0.00000012232 := by
  have hl := lg_24
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.48379915289471922 65.483799194104739825 (-2.6519461) 0.00000002231 (-0.8824991444977) (-0.4703140013462) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_25 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9388605274634):ℝ):ℂ) + ((0.344297705183:ℝ):ℂ) * I)‖ ≤ 0.00000012901 := by
  have hl := lg_25
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.32493634998455289 66.3249363911945941 2.790102 0.000000029 (-0.9388605274634) 0.344297705183 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_26 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3996755534603):ℝ):ℂ) + ((0.9166566707131:ℝ):ℂ) * I)‖ ≤ 0.00000013448 := by
  have hl := lg_26
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.1330791445079285 67.13307918571796971 1.9819592 0.00000003447 (-0.3996755534603) 0.9166566707131 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_27 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3583281636407:ℝ):ℂ) + ((0.9335956979024:ℝ):ℂ) * I)‖ ≤ 0.0000001599 := by
  have hl := lg_27
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.91071860795065766 67.910718638858219475 1.2043198 0.00000005989 0.3583281636407 0.9335956979024 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_28 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8982766724677:ℝ):ℂ) + ((0.4394303354348:ℝ):ℂ) * I)‖ ≤ 0.00000016826 := by
  have hl := lg_28
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.66007391073537031 68.66007395194541152 0.4549644 0.00000006825 0.8982766724677 0.4394303354348 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_29 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9642780123738:ℝ):ℂ) + (((-0.2648922702769):ℝ):ℂ) * I)‖ ≤ 0.00000012354 := by
  have hl := lg_29
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.38313055544658866 69.383130596656650475 (-0.2680922) 0.00000002353 0.9642780123738 (-0.2648922702769) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_30 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5680731357155:ℝ):ℂ) + (((-0.8229780753328):ℝ):ℂ) * I)‖ ≤ 0.00000015127 := by
  have hl := lg_30
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.081672027723995665 70.081672068934036875 (-0.9666337) 0.00000005126 0.5680731357155 (-0.8229780753328) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_31 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0714108401436):ℝ):ℂ) + (((-0.9974469870172):ℝ):ℂ) * I)‖ ≤ 0.000000152 := by
  have hl := lg_31
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.757306326991704615 70.75730636820176643 (-1.642268) 0.00000005199 (-0.0714108401436) (-0.9974469870172) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_32 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6636245001609):ℝ):ℂ) + (((-0.7480658545661):ℝ):ℂ) * I)‖ ≤ 0.00000012858 := by
  have hl := lg_32
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.4114882504075 71.41148830192 (-2.2964499) 0.00000002857 (-0.6636245001609) (-0.7480658545661) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_33 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9778025354013):ℝ):ℂ) + (((-0.2095285218097):ℝ):ℂ) * I)‖ ≤ 0.00000014484 := by
  have hl := lg_33
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.045538282592091685 72.0455383238021535 (-2.9304999) 0.00000004483 (-0.9778025354013) (-0.2095285218097) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_34 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9194851246141):ℝ):ℂ) + ((0.3931247963068:ℝ):ℂ) * I)‖ ≤ 0.00000014831 := by
  have hl := lg_34
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.66065858293512257 72.660658634447643175 2.7375651 0.0000000483 (-0.9194851246141) 0.3931247963068 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_35 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5391946700306):ℝ):ℂ) + ((0.8421811609164:ℝ):ℂ) * I)‖ ≤ 0.00000014063 := by
  have hl := lg_35
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.257946785564646755 73.25794682677470857 2.1402769 0.00000004062 (-0.5391946700306) 0.8421811609164 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_36 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.010980106151:ℝ):ℂ) + ((0.9999397168173:ℝ):ℂ) * I)‖ ≤ 0.00000016053 := by
  have hl := lg_36
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.83840770546343844 73.83840774667347965 1.559816 0.00000006052 0.010980106151 0.9999397168173 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_37 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5442847098738:ℝ):ℂ) + ((0.8389005629975:ℝ):ℂ) * I)‖ ≤ 0.00000012368 := by
  have hl := lg_37
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.40296356860952741 74.402963609819589225 0.9952601 0.00000002367 0.5442847098738 0.8389005629975 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_38 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9022828687349:ℝ):ℂ) + ((0.4311445520791:ℝ):ℂ) * I)‖ ≤ 0.00000015481 := by
  have hl := lg_38
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.952462799737454815 74.95246284094751663 0.4457609 0.0000000548 0.9022828687349 0.4311445520791 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_39 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9960007648454:ℝ):ℂ) + (((-0.0893447056478):ℝ):ℂ) * I)‖ ≤ 0.00000015215 := by
  have hl := lg_39
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.48768769707664772 75.487687738286709535 (-0.089464) 0.00000005214 0.9960007648454 (-0.0893447056478) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p605_40 : ‖exp (-((((((20605:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8189958509764:ℝ):ℂ) + (((-0.5737994389014):ℝ):ℂ) * I)‖ ≤ 0.00000016093 := by
  have hl := lg_40
  refine (ecis_approx ((((20605:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.009361125236776445 76.00936117674929705 (-0.6111375) 0.00000006092 0.8189958509764 (-0.5737994389014) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_2 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1822298243272):ℝ):ℂ) + (((-0.9832559641949):ℝ):ℂ) * I)‖ ≤ 0.00000014098 := by
  have hl := lg_2
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.320420744998 14.320420755328 (-1.7540501) 0.00000004097 (-0.1822298243272) (-0.9832559641949) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_3 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7608454633918):ℝ):ℂ) + ((0.6489331096496:ℝ):ℂ) * I)‖ ≤ 0.00000015022 := by
  have hl := lg_3
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.69732987851266824 22.6973298888426889 2.4354113 0.00000005021 (-0.7608454633918) 0.6489331096496 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_4 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9335845437874):ℝ):ℂ) + ((0.3583572232213:ℝ):ℂ) * I)‖ ≤ 0.00000014592 := by
  have hl := lg_4
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.640841489996 28.640841510656 2.775085 0.00000004591 (-0.9335845437874) 0.3583572232213 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_5 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2611992494448):ℝ):ℂ) + (((-0.9652849072104):ℝ):ℂ) * I)‖ ≤ 0.00000014492 := by
  have hl := lg_5
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.25098726014755794 33.2509872808075786 (-1.8350607) 0.00000004491 (-0.2611992494448) (-0.9652849072104) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_6 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7767160855823:ℝ):ℂ) + ((0.629850873142:ℝ):ℂ) * I)‖ ≤ 0.00000011958 := by
  have hl := lg_6
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.01775062351066824 37.0177506441706889 0.6813612 0.00000001957 0.7767160855823 0.629850873142 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_7 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.803168901166):ℝ):ℂ) + (((-0.5957513878702):ℝ):ℂ) * I)‖ ≤ 0.00000014634 := by
  have hl := lg_7
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.20250366874181852 40.20250368940185984 (-2.5033918) 0.00000004633 (-0.803168901166) (-0.5957513878702) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_8 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.52248382455:ℝ):ℂ) + ((0.8526491969642:ℝ):ℂ) * I)‖ ≤ 0.00000011574 := by
  have hl := lg_8
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.961262234994 42.961262265984 1.0210349 0.00000001573 0.52248382455 0.8526491969642 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_9 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1577717441845:ℝ):ℂ) + (((-0.9874756081731):ℝ):ℂ) * I)‖ ≤ 0.00000012744 := by
  have hl := lg_9
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.39465975702533648 45.3946597776853778 (-1.4123626) 0.00000002743 0.1577717441845 (-0.9874756081731) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_10 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9015238024077):ℝ):ℂ) + ((0.4327295154877:ℝ):ℂ) * I)‖ ≤ 0.00000015231 := by
  have hl := lg_10
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.57140800514555794 47.5714080361355786 2.6940744 0.0000000523 (-0.9015238024077) 0.4327295154877 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_11 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7485219018276:ℝ):ℂ) + ((0.6631100681519:ℝ):ℂ) * I)‖ ≤ 0.00000013755 := by
  have hl := lg_11
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.54051631990289178 49.5405163508929331 0.7249661 0.00000003754 0.7485219018276 0.6631100681519 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_12 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4777637917429:ℝ):ℂ) + (((-0.8784883376001):ℝ):ℂ) * I)‖ ≤ 0.00000014208 := by
  have hl := lg_12
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.33817136850866824 51.3381713994986889 (-1.0726889) 0.00000004207 0.4777637917429 (-0.8784883376001) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_13 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9150270504956):ℝ):ℂ) + (((-0.4033924847165):ℝ):ℂ) * I)‖ ≤ 0.00000014841 := by
  have hl := lg_13
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.991853709043922 52.99185374003396332 (-2.7263713) 0.0000000484 (-0.9150270504956) (-0.4033924847165) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_14 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4394146812848):ℝ):ℂ) + ((0.8982843301913:ℝ):ℂ) * I)‖ ≤ 0.00000015089 := by
  have hl := lg_14
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.52292441373981852 54.52292444472985984 2.0257433 0.00000005088 (-0.4394146812848) 0.8982843301913 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_15 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8251376005373:ℝ):ℂ) + ((0.5649318013527:ℝ):ℂ) * I)‖ ≤ 0.00000012597 := by
  have hl := lg_15
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.94831713866022618 55.9483171696502675 0.6003506 0.00000002596 0.8251376005373 0.5649318013527 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_16 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7431602727199:ℝ):ℂ) + (((-0.6691134500598):ℝ):ℂ) * I)‖ ≤ 0.00000015671 := by
  have hl := lg_16
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.281682979992 57.281683021312 (-0.7330152) 0.0000000567 0.7431602727199 (-0.6691134500598) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_17 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4029369523133):ℝ):ℂ) + (((-0.9152277380287):ℝ):ℂ) * I)‖ ≤ 0.00000014344 := by
  have hl := lg_17
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.53418766671952644 58.5341877080395471 (-1.9855199) 0.00000004343 (-0.4029369523133) (-0.9152277380287) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_18 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996919979748):ℝ):ℂ) + ((0.0248175050482:ℝ):ℂ) * I)‖ ≤ 0.00000016123 := by
  have hl := lg_18
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.71508050202333648 59.7150805330133778 3.1167726 0.00000006122 (-0.9996919979748) 0.0248175050482 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_19 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4159138608914):ℝ):ℂ) + ((0.9094040137996:ℝ):ℂ) * I)‖ ≤ 0.00000015268 := by
  have hl := lg_19
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.83210929346721798 60.83210932445727996 1.9997438 0.00000005267 (-0.4159138608914) 0.9094040137996 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_20 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5897684011951:ℝ):ℂ) + ((0.8075724320157:ℝ):ℂ) * I)‖ ≤ 0.00000012167 := by
  have hl := lg_20
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.89182875014355794 61.8918287914635786 0.9400243 0.00000002166 0.5897684011951 0.8075724320157 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_21 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.997690215542:ℝ):ℂ) + (((-0.0679281518352):ℝ):ℂ) * I)‖ ≤ 0.00000012456 := by
  have hl := lg_21
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.89983354725448676 62.89983357824454874 (-0.0679805) 0.00000002455 0.997690215542 (-0.0679281518352) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_22 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5156039147533:ℝ):ℂ) + (((-0.8568270555317):ℝ):ℂ) * I)‖ ≤ 0.00000013444 := by
  have hl := lg_22
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.86093706490089178 63.8609371062209331 (-1.029084) 0.00000003443 0.5156039147533 (-0.8568270555317) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_23 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3678176643504):ℝ):ℂ) + (((-0.9298979329954):ℝ):ℂ) * I)‖ ≤ 0.00000014915 := by
  have hl := lg_23
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.77931047961430156 64.77931052093436354 (-1.9474574) 0.00000004914 (-0.3678176643504) (-0.9298979329954) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_24 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9508417401548):ℝ):ℂ) + (((-0.3096772270828):ℝ):ℂ) * I)‖ ≤ 0.0000001583 := by
  have hl := lg_24
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.65859211350666824 65.6585921548266889 (-2.8267391) 0.00000005829 (-0.9508417401548) (-0.3096772270828) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_25 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8635498501109):ℝ):ℂ) + ((0.5042634790369:ℝ):ℂ) * I)‖ ≤ 0.0000001587 := by
  have hl := lg_25
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.50197452029511588 66.5019745616151572 2.6130638 0.00000005869 (-0.8635498501109) 0.5042634790369 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_26 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2298928409191):ℝ):ℂ) + ((0.9732159481292:ℝ):ℂ) * I)‖ ≤ 0.00000012495 := by
  have hl := lg_26
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.312274454041922 67.31227449536196332 1.8027639 0.00000002494 (-0.2298928409191) 0.9732159481292 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_27 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5207657013201:ℝ):ℂ) + ((0.8536996452667:ℝ):ℂ) * I)‖ ≤ 0.00000014345 := by
  have hl := lg_27
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.09198963553800472 68.0919896665280667 1.0230487 0.00000004344 0.5207657013201 0.8536996452667 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_28 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9633178853834:ℝ):ℂ) + ((0.2683629104412:ℝ):ℂ) * I)‖ ≤ 0.0000001211 := by
  have hl := lg_28
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.84334515873781852 68.84334520005785984 0.2716932 0.00000002109 0.9633178853834 0.2683629104412 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_29 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8990096623215:ℝ):ℂ) + (((-0.437928792217):ℝ):ℂ) * I)‖ ≤ 0.00000015295 := by
  have hl := lg_29
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.56833182603865672 69.5683318673587187 (-0.4532935) 0.00000005294 0.8990096623215 (-0.437928792217) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_30 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.405107883052:ℝ):ℂ) + (((-0.9142688899274):ℝ):ℂ) * I)‖ ≤ 0.00000014602 := by
  have hl := lg_30
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.26873788365822618 70.2687379249782675 (-1.1536995) 0.00000004601 0.405107883052 (-0.9142688899274) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_31 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2574100500297):ℝ):ℂ) + (((-0.9663022643782):ℝ):ℂ) * I)‖ ≤ 0.00000015581 := by
  have hl := lg_31
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.94617562318119958 70.94617566450126156 (-1.8311373) 0.0000000558 (-0.2574100500297) (-0.9663022643782) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_32 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7933358173083):ℝ):ℂ) + (((-0.6087842646858):ℝ):ℂ) * I)‖ ≤ 0.000000154 := by
  have hl := lg_32
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.60210372499 71.60210377664 (-2.4870654) 0.00000005399 (-0.7933358173083) (-0.6087842646858) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_33 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998235695102):ℝ):ℂ) + (((-0.0187837485504):ℝ):ℂ) * I)‖ ≤ 0.00000016078 := by
  have hl := lg_33
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.23784619841556002 72.237846239735622 (-3.1228078) 0.00000006077 (-0.9998235695102) (-0.0187837485504) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_34 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8264759416278):ℝ):ℂ) + ((0.5629720400248:ℝ):ℂ) * I)‖ ≤ 0.00000017445 := by
  have hl := lg_34
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.85460841171752644 72.8546084633675471 2.5436152 0.00000007444 (-0.8264759416278) 0.5629720400248 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_35 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3652826092509):ℝ):ℂ) + ((0.9308966727711:ℝ):ℂ) * I)‖ ≤ 0.00000015728 := by
  have hl := lg_35
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.45349092888937646 73.45349097020943844 1.9447327 0.00000005727 (-0.3652826092509) 0.9308966727711 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_36 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2065757552044:ℝ):ℂ) + ((0.9784306093749:ℝ):ℂ) * I)‖ ≤ 0.00000013915 := by
  have hl := lg_36
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.03550124702133648 74.0355012883413778 1.3627224 0.00000003914 0.2065757552044 0.9784306093749 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_37 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6990990741589:ℝ):ℂ) + ((0.7150248139122:ℝ):ℂ) * I)‖ ≤ 0.00000013242 := by
  have hl := lg_37
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.60156405374777172 74.6015640950678337 0.7966596 0.00000003241 0.6990990741589 0.7150248139122 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_38 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.969968854562:ℝ):ℂ) + ((0.2432291536386:ℝ):ℂ) * I)‖ ≤ 0.0000001477 := by
  have hl := lg_38
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.15253003846521798 75.15253007978527996 0.2456936 0.00000004769 0.969968854562 0.2432291536386 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_39 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9579689485472:ℝ):ℂ) + (((-0.2868719115204):ℝ):ℂ) * I)‖ ≤ 0.00000014274 := by
  have hl := lg_39
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.68918358755659024 75.68918362887665222 (-0.2909599) 0.00000004273 0.9579689485472 (-0.2868719115204) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_40 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6865770181557:ℝ):ℂ) + (((-0.7270570803867):ℝ):ℂ) * I)‖ ≤ 0.00000016065 := by
  have hl := lg_40
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.21224949514155794 76.2122495467915786 (-0.8140258) 0.00000006064 0.6865770181557 (-0.7270570803867) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_41 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2441287209867:ℝ):ℂ) + (((-0.969742835802):ℝ):ℂ) * I)‖ ≤ 0.00000013677 := by
  have hl := lg_41
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.7223988712586228 76.72239892290866412 (-1.3241752) 0.00000003676 0.2441287209867 (-0.969742835802) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_42 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2485996731399):ℝ):ℂ) + (((-0.9686063196746):ℝ):ℂ) * I)‖ ≤ 0.00000014743 := by
  have hl := lg_42
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.22025429225248676 77.22025433357254874 (-1.8220306) 0.00000004742 (-0.2485996731399) (-0.9686063196746) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_43 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6723466467779):ℝ):ℂ) + (((-0.7402364396238):ℝ):ℂ) * I)‖ ≤ 0.00000012393 := by
  have hl := lg_43
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.7063943687470948 77.70639441006717744 (-2.3081707) 0.00000002392 (-0.6723466467779) (-0.7402364396238) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_44 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9364387233853):ℝ):ℂ) + (((-0.3508311804451):ℝ):ℂ) * I)‖ ≤ 0.00000017541 := by
  have hl := lg_44
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.18135780989889178 78.1813578615489331 (-2.7831341) 0.0000000754 (-0.9364387233853) (-0.3508311804451) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_45 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9944051610041):ℝ):ℂ) + ((0.1056332111737:ℝ):ℂ) * I)‖ ≤ 0.00000016517 := by
  have hl := lg_45
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.64564701717289442 78.6456470584929564 3.035762 0.00000006516 (-0.9944051610041) 0.1056332111737 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_46 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.847300283411):ℝ):ℂ) + ((0.5311141399544:ℝ):ℂ) * I)‖ ≤ 0.00000016874 := by
  have hl := lg_46
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.09973122461230156 79.09973127626236354 2.5816777 0.00000006873 (-0.847300283411) 0.5311141399544 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_47 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5367353995958):ℝ):ℂ) + ((0.8437506212222:ℝ):ℂ) * I)‖ ≤ 0.00000016887 := by
  have hl := lg_47
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.54404942447739714 79.54404947612747978 2.1373595 0.00000006886 (-0.5367353995958) 0.8437506212222 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_48 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1312202502073):ℝ):ℂ) + ((0.991353239736:ℝ):ℂ) * I)‖ ≤ 0.00000013484 := by
  have hl := lg_48
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.97901285850466824 79.9790129101546889 1.7023961 0.00000003483 (-0.1312202502073) 0.991353239736 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_49 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2901606702026:ℝ):ℂ) + ((0.9569779440863:ℝ):ℂ) * I)‖ ≤ 0.00000015587 := by
  have hl := lg_49
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.40500733748363704 80.40500737880371968 1.2764016 0.00000005586 0.2901606702026 0.9569779440863 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p66_50 : ‖exp (-((((((20660:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6531846108211:ℝ):ℂ) + ((0.7571986953148:ℝ):ℂ) * I)‖ ≤ 0.00000012806 := by
  have hl := lg_50
  refine (ecis_approx ((((20660:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.82239526529311588 80.8223953169431572 0.8590137 0.00000002805 0.6531846108211 0.7571986953148 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_2 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2195731028477):ℝ):ℂ) + (((-0.9755960498612):ℝ):ℂ) * I)‖ ≤ 0.00000013593 := by
  have hl := lg_2
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.3585438399145 14.358543850272 (-1.7921732) 0.00000003592 (-0.2195731028477) (-0.9755960498612) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_3 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7202699390723):ℝ):ℂ) + ((0.6936938913105:ℝ):ℂ) * I)‖ ≤ 0.00000013603 := by
  have hl := lg_3
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.75775355437511726 22.757753564732637975 2.3749877 0.00000003602 (-0.7202699390723) 0.6936938913105 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_4 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9035752590569):ℝ):ℂ) + ((0.4284294003679:ℝ):ℂ) * I)‖ ≤ 0.00000015608 := by
  have hl := lg_4
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.717087679829 28.717087700544 2.6988388 0.00000005607 (-0.9035752590569) 0.4284294003679 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_5 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3455111945173):ℝ):ℂ) + (((-0.938414628222):ℝ):ℂ) * I)‖ ≤ 0.00000013013 := by
  have hl := lg_5
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.339506345302839435 33.33950636601786015 (-1.9235798) 0.00000003012 (-0.3455111945173) (-0.938414628222) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_6 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8349169806393:ℝ):ℂ) + ((0.5503759037605:ℝ):ℂ) * I)‖ ≤ 0.0000001488 := by
  have hl := lg_6
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.11629739428961726 37.116297415004637975 0.5828144 0.00000004879 0.8349169806393 0.5503759037605 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_7 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8622120916193):ℝ):ℂ) + (((-0.5065474400128):ℝ):ℂ) * I)‖ ≤ 0.00000011618 := by
  have hl := lg_7
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.30952872691126673 40.30952874762630816 (-2.6104169) 0.00000001617 (-0.8622120916193) (-0.5065474400128) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_8 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6163748540023:ℝ):ℂ) + ((0.7874528807197:ℝ):ℂ) * I)‖ ≤ 0.00000013053 := by
  have hl := lg_8
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.0756315197435 43.075631550816 0.9066656 0.00000003052 0.6163748540023 0.7874528807197 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_9 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0375774775191:ℝ):ℂ) + (((-0.9992937171739):ℝ):ℂ) * I)‖ ≤ 0.00000014152 := by
  have hl := lg_9
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.51550710875023452 45.51550712946527595 (-1.53321) 0.00000004151 0.0375774775191 (-0.9992937171739) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_10 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8396486354629):ℝ):ℂ) + ((0.5431299742213:ℝ):ℂ) * I)‖ ≤ 0.00000015887 := by
  have hl := lg_10
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.698050185217339435 47.69805021628986015 2.5674323 0.00000005886 (-0.8396486354629) 0.5431299742213 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_11 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8292220865991:ℝ):ℂ) + ((0.5589192527515:ℝ):ℂ) * I)‖ ≤ 0.00000013351 := by
  have hl := lg_11
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.672400559863911095 49.672400590936452525 0.5930819 0.0000000335 0.8292220865991 0.5589192527515 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_12 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3536192455887:ℝ):ℂ) + (((-0.9353894531955):ℝ):ℂ) * I)‖ ≤ 0.00000012325 := by
  have hl := lg_12
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.47484123420411726 51.474841265276637975 (-1.2093588) 0.00000002324 0.3536192455887 (-0.9353894531955) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_13 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9626558938769):ℝ):ℂ) + (((-0.270727962615):ℝ):ℂ) * I)‖ ≤ 0.00000013379 := by
  have hl := lg_13
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.1329259236614155 53.13292595473395693 (-2.8674435) 0.00000003378 (-0.9626558938769) (-0.270727962615) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_14 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3048670904762):ℝ):ℂ) + ((0.9523949060882:ℝ):ℂ) * I)‖ ≤ 0.0000001333 := by
  have hl := lg_14
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.66807256682576673 54.66807259789830816 1.8805952 0.00000003329 (-0.3048670904762) 0.9523949060882 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_15 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8998338657777:ℝ):ℂ) + ((0.436232752094:ℝ):ℂ) * I)‖ ≤ 0.00000016495 := by
  have hl := lg_15
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.097259899677956695 56.097259930750498125 0.4514078 0.00000006494 0.8998338657777 0.436232752094 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_16 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6328965806718:ℝ):ℂ) + (((-0.7742363451646):ℝ):ℂ) * I)‖ ≤ 0.00000013649 := by
  have hl := lg_16
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.434175359658 57.434175401088 (-0.8855076) 0.00000003648 0.6328965806718 (-0.7742363451646) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_17 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5400953267182):ℝ):ℂ) + (((-0.841603848642):ℝ):ℂ) * I)‖ ≤ 0.00000016405 := by
  have hl := lg_17
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.69001440058543031 58.690014442015451025 (-2.1413467) 0.00000006404 (-0.5400953267182) (-0.841603848642) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_18 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9831580050062):ℝ):ℂ) + ((0.1827575903934:ℝ):ℂ) * I)‖ ≤ 0.00000012315 := by
  have hl := lg_18
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.87405094866473452 59.87405097973727595 2.9578021 0.00000002314 (-0.9831580050062) 0.1827575903934 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_19 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2638420852697):ℝ):ℂ) + ((0.9645658889051:ℝ):ℂ) * I)‖ ≤ 0.00000013453 := by
  have hl := lg_19
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.994053437278481145 60.99405346835104329 1.8377996 0.00000003452 (-0.2638420852697) 0.9645658889051 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_20 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7142397836324:ℝ):ℂ) + ((0.6999010869235:ℝ):ℂ) * I)‖ ≤ 0.00000014668 := by
  have hl := lg_20
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.056594025131839435 62.05659406656186015 0.775259 0.00000004667 0.7142397836324 0.6999010869235 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_21 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9724143155516:ℝ):ℂ) + (((-0.2332603672086):ℝ):ℂ) * I)‖ ≤ 0.00000014058 := by
  have hl := lg_21
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.06728228128638399 63.067282312358946135 (-0.2354292) 0.00000004057 0.9724143155516 (-0.2332603672086) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_22 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3632045486717:ℝ):ℂ) + (((-0.9317094267121):ℝ):ℂ) * I)‖ ≤ 0.00000016943 := by
  have hl := lg_22
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.030944399778411095 64.030944441208452525 (-1.1990913) 0.00000006942 0.3632045486717 (-0.9317094267121) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_23 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5219310672021):ℝ):ℂ) + (((-0.8529876676026):ℝ):ℂ) * I)‖ ≤ 0.00000013108 := by
  have hl := lg_23
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.95176266143321669 64.951762702863278835 (-2.1199096) 0.00000003107 (-0.5219310672021) (-0.8529876676026) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_24 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9902075304216):ℝ):ℂ) + (((-0.1396031743457):ℝ):ℂ) * I)‖ ≤ 0.00000014377 := by
  have hl := lg_24
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.83338507411861726 65.833385115548637975 (-3.001532) 0.00000004376 (-0.9902075304216) (-0.1396031743457) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_25 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7612440242645):ℝ):ℂ) + ((0.6484655237442:ℝ):ℂ) * I)‖ ≤ 0.00000015308 := by
  have hl := lg_25
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.67901269060567887 66.6790127320357203 2.4360257 0.00000005307 (-0.7612440242645) 0.6484655237442 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_26 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0527477822523):ℝ):ℂ) + ((0.998607866716:ℝ):ℂ) * I)‖ ≤ 0.00000012605 := by
  have hl := lg_26
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.4914697635759155 67.49146980500595693 1.6235686 0.00000002604 (-0.0527477822523) 0.998607866716 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_27 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6661380198007:ℝ):ℂ) + ((0.7458284913947:ℝ):ℂ) * I)‖ ≤ 0.00000011587 := by
  have hl := lg_27
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.27326066312535178 68.273260694197913925 0.8417777 0.00000001586 0.6661380198007 0.7458284913947 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_28 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.996093321301:ℝ):ℂ) + ((0.088306824535:ℝ):ℂ) * I)‖ ≤ 0.00000016921 := by
  have hl := lg_28
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.02661640674026673 69.02661644817030816 0.088422 0.0000000692 0.996093321301 0.088306824535 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_29 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8029938070972:ℝ):ℂ) + (((-0.5959873704732):ℝ):ℂ) * I)‖ ≤ 0.0000001591 := by
  have hl := lg_29
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.75353309663072478 69.753533138060786925 (-0.6384947) 0.00000005909 0.8029938070972 (-0.5959873704732) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_30 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.228007635807:ℝ):ℂ) + (((-0.9736593439256):ℝ):ℂ) * I)‖ ≤ 0.0000001394 := by
  have hl := lg_30
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.455803739592456695 70.455803781022498125 (-1.3407654) 0.00000003939 0.228007635807 (-0.9736593439256) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_31 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4342542913439):ℝ):ℂ) + (((-0.9007903254616):ℝ):ℂ) * I)‖ ≤ 0.00000015962 := by
  have hl := lg_31
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.135044919370694545 71.13504496080075669 (-2.0200066) 0.00000005961 (-0.4342542913439) (-0.9007903254616) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_32 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8943089859701):ℝ):ℂ) + (((-0.4474499273696):ℝ):ℂ) * I)‖ ≤ 0.0000001724 := by
  have hl := lg_32
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.7927191995725 71.79271925136 (-2.6776808) 0.00000007239 (-0.8943089859701) (-0.4474499273696) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_33 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9849826130218):ℝ):ℂ) + ((0.1726535597227:ℝ):ℂ) * I)‖ ≤ 0.00000016953 := by
  have hl := lg_33
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.430154114239028355 72.4301541556690905 2.9680696 0.00000006952 (-0.9849826130218) 0.1726535597227 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_34 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.702474978454):ℝ):ℂ) + ((0.711708440741:ℝ):ℂ) * I)‖ ≤ 0.00000014567 := by
  have hl := lg_34
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.04855824049993031 73.048558292287451025 2.3496654 0.00000004566 (-0.702474978454) 0.711708440741 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_35 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.177447590864):ℝ):ℂ) + ((0.9841302517938:ℝ):ℂ) * I)‖ ≤ 0.0000001275 := by
  have hl := lg_35
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.649035072214106165 73.64903511364416831 1.7491886 0.00000002749 (-0.177447590864) 0.9841302517938 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_36 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3941726372161:ℝ):ℂ) + ((0.9190364149859:ℝ):ℂ) * I)‖ ≤ 0.00000014387 := by
  have hl := lg_36
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.23259478857923452 74.23259483000927595 1.1656289 0.00000004386 0.3941726372161 0.9190364149859 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_37 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8264299742408:ℝ):ℂ) + ((0.5630395169758:ℝ):ℂ) * I)‖ ≤ 0.00000014728 := by
  have hl := lg_37
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.80016453888601603 74.800164580316078175 0.5980591 0.00000004727 0.8264299742408 0.5630395169758 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_38 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9989592963723:ℝ):ℂ) + ((0.0456105710483:ℝ):ℂ) * I)‖ ≤ 0.00000013248 := by
  have hl := lg_38
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.352597277192981145 75.35259731862304329 0.0456264 0.00000003247 0.9989592963723 0.0456105710483 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_39 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8811744360627:ℝ):ℂ) + (((-0.4727912998666):ℝ):ℂ) * I)‖ ≤ 0.00000013333 := by
  have hl := lg_39
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.89067947803653276 75.890679519466594905 (-0.4924558) 0.00000003332 0.8811744360627 (-0.4727912998666) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_40 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5259928902272:ℝ):ℂ) + (((-0.8504889649081):ℝ):ℂ) * I)‖ ≤ 0.00000013069 := by
  have hl := lg_40
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.415137865046339435 76.41513791683386015 (-1.0169142) 0.00000003068 0.5259928902272 (-0.8504889649081) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_41 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0423619465565:ℝ):ℂ) + (((-0.999102329836):ℝ):ℂ) * I)‖ ≤ 0.00000015131 := by
  have hl := lg_41
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.9266453348558747 76.92664538664341613 (-1.5284217) 0.0000000513 0.0423619465565 (-0.999102329836) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_42 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4410840111037):ℝ):ℂ) + (((-0.897465818371):ℝ):ℂ) * I)‖ ≤ 0.00000016497 := by
  have hl := lg_42
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.42582612120088399 77.425826162630946135 (-2.0276025) 0.00000006496 (-0.4410840111037) (-0.897465818371) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_43 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8100517539918):ℝ):ℂ) + (((-0.5863583851209):ℝ):ℂ) * I)‖ ≤ 0.00000013034 := by
  have hl := lg_43
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.9132603750530527 77.91326041648313556 (-2.5150367) 0.00000003033 (-0.8100517539918) (-0.5863583851209) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_44 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9887220008456):ℝ):ℂ) + (((-0.1497624941381):ℝ):ℂ) * I)‖ ≤ 0.00000014648 := by
  have hl := lg_44
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.389488239692911095 78.389488291480452525 (-2.9912646) 0.00000004647 (-0.9887220008456) (-0.1497624941381) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_45 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9507352789332):ℝ):ℂ) + ((0.3100039180181:ℝ):ℂ) * I)‖ ≤ 0.0000001393 := by
  have hl := lg_45
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.855013454053073955 78.8550134954831361 2.8263955 0.00000003929 (-0.9507352789332) 0.3100039180181 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_46 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7175693701953):ℝ):ℂ) + ((0.6964870414665:ℝ):ℂ) * I)‖ ≤ 0.00000015982 := by
  have hl := lg_46
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.31030650134771669 79.310306553135278835 2.3711025 0.00000005981 (-0.7175693701953) 0.6964870414665 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_47 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3474075862086):ℝ):ℂ) + ((0.9377142256798:ℝ):ℂ) * I)‖ ≤ 0.00000015085 := by
  have hl := lg_47
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.755807542499965235 79.755807594287548095 1.9256014 0.00000005084 (-0.3474075862086) 0.9377142256798 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_48 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0812266414811:ℝ):ℂ) + ((0.9966956570155:ℝ):ℂ) * I)‖ ≤ 0.0000001725 := by
  have hl := lg_48
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.19192891403311726 80.191928965820637975 1.4894801 0.00000007249 0.0812266414811 0.9966956570155 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_49 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4868193882131:ℝ):ℂ) + ((0.8735026521195:ℝ):ℂ) * I)‖ ≤ 0.00000013953 := by
  have hl := lg_49
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.61905745382253346 80.61905749525261632 1.0623515 0.00000003952 0.4868193882131 0.8735026521195 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p715_50 : ‖exp (-((((((20715:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7997891759181:ℝ):ℂ) + ((0.6002809959379:ℝ):ℂ) * I)‖ ≤ 0.00000016283 := by
  have hl := lg_50
  refine (ecis_approx ((((20715:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.03755653052017887 81.0375565823077203 0.6438524 0.00000006282 0.7997891759181 0.6002809959379 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_2 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2472062700107):ℝ):ℂ) + (((-0.9689628785801):ℝ):ℂ) * I)‖ ≤ 0.00000014007 := by
  have hl := lg_2
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.3869628743068 14.3869628846848 (-1.8205923) 0.00000004006 (-0.2472062700107) (-0.9689628785801) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_3 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6883038330451):ℝ):ℂ) + ((0.7254225206:ℝ):ℂ) * I)‖ ≤ 0.00000013987 := by
  have hl := lg_3
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.802796658199851984 22.80279666857787274 2.3299446 0.00000003986 (-0.6883038330451) 0.7254225206 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_4 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8777781645765):ℝ):ℂ) + ((0.4790673164582:ℝ):ℂ) * I)‖ ≤ 0.00000013349 := by
  have hl := lg_4
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.7739257486136 28.7739257693696 2.6420008 0.00000003348 (-0.8777781645765) 0.4790673164582 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_5 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4066374778112):ℝ):ℂ) + (((-0.9135896024123):ℝ):ℂ) * I)‖ ≤ 0.00000013622 := by
  have hl := lg_5
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.405493299691322004 33.40549332044734276 (-1.9895668) 0.00000003621 (-0.4066374778112) (-0.9135896024123) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_6 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8730605169616:ℝ):ℂ) + ((0.4876118679059:ℝ):ℂ) * I)‖ ≤ 0.00000011059 := by
  have hl := lg_6
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.189759532506651984 37.18975955326267274 0.5093523 0.00000001058 0.8730605169616 0.4876118679059 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_7 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.899840124025):ℝ):ℂ) + (((-0.4362198426006):ℝ):ℂ) * I)‖ ≤ 0.00000012069 := by
  have hl := lg_7
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.389311043001219032 40.389311063757260544 (-2.6901992) 0.00000002068 (-0.899840124025) (-0.4362198426006) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_8 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6811907120072:ℝ):ℂ) + ((0.7321060127298:ℝ):ℂ) * I)‖ ≤ 0.00000012735 := by
  have hl := lg_8
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.1608886229204 43.1608886540544 0.8214085 0.00000002734 0.6811907120072 0.7321060127298 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_9 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0524757595158):ℝ):ℂ) + (((-0.9986221981625):ℝ):ℂ) * I)‖ ≤ 0.00000013387 := by
  have hl := lg_9
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.605593316399703968 45.60559333715574548 (-1.6232962) 0.00000003386 (-0.0524757595158) (-0.9986221981625) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_10 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7847111343878):ℝ):ℂ) + ((0.6198616261102:ℝ):ℂ) * I)‖ ≤ 0.00000014771 := by
  have hl := lg_10
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.792456173998122004 47.79245620513214276 2.4730263 0.0000000477 (-0.7847111343878) 0.6198616261102 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_11 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8800787985311:ℝ):ℂ) + ((0.4748276617638:ℝ):ℂ) * I)‖ ≤ 0.00000013973 := by
  have hl := lg_11
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.770714266016670948 49.77071429715071246 0.4947682 0.00000003972 0.8800787985311 0.4748276617638 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_12 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2566517652646:ℝ):ℂ) + (((-0.9665039427682):ℝ):ℂ) * I)‖ ≤ 0.00000015064 := by
  have hl := lg_12
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.576722406813451984 51.57672243794747274 (-1.31124) 0.00000005063 0.2566517652646 (-0.9665039427682) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_13 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9857557682902):ℝ):ℂ) + (((-0.1681831291074):ℝ):ℂ) * I)‖ ≤ 0.000000121 := by
  have hl := lg_13
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.2380888472853652 53.238088878419406712 (-2.9726064) 0.00000002099 (-0.9857557682902) (-0.1681831291074) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_14 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2002347067325):ℝ):ℂ) + ((0.9797479585173:ℝ):ℂ) * I)‖ ≤ 0.00000014732 := by
  have hl := lg_14
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.776273917308019032 54.776273948442060544 1.7723938 0.00000004731 (-0.2002347067325) 0.9797479585173 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_15 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9426286068269:ℝ):ℂ) + ((0.3338432410452:ℝ):ℂ) * I)‖ ≤ 0.00000012442 := by
  have hl := lg_15
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.208289957891173988 56.2082899890252155 0.3403778 0.00000002441 0.9426286068269 0.3338432410452 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_16 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5409889344397:ℝ):ℂ) + (((-0.8410297098282):ℝ):ℂ) * I)‖ ≤ 0.0000001674 := by
  have hl := lg_16
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.5478514972272 57.5478515387392 (-0.9991838) 0.00000006739 0.5409889344397 (-0.8410297098282) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v20p756_17 : ‖exp (-((((((20756:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6339979457236):ℝ):ℂ) + (((-0.7733347301157):ℝ):ℂ) * I)‖ ≤ 0.00000012456 := by
  have hl := lg_17
  refine (ecis_approx ((((20756:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.806176147649104104 58.80617618916112486 (-2.2575084) 0.00000002455 (-0.6339979457236) (-0.7733347301157) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
