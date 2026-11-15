/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
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
namespace H28

open Complex Set

lemma cs_b1left_v14p283_4 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5809618495392:ℝ):ℂ) + (((-0.8139307890601):ℝ):ℂ) * I)‖ ≤ 0.00000014521 := by
  have hl := lg_4
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.8004423524498 19.8004423667328 (-0.9508864) 0.0000000452 0.5809618495392 (-0.8139307890601) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_5 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5432834694216):ℝ):ℂ) + ((0.83954932663:ℝ):ℂ) * I)‖ ≤ 0.00000013286 := by
  have hl := lg_5
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.987601695870647147 22.98760171015366143 2.1451395 0.00000003285 (-0.5432834694216) 0.83954932663 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_6 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8965140289994:ℝ):ℂ) + (((-0.4430153448893):ℝ):ℂ) * I)‖ ≤ 0.00000013717 := by
  have hl := lg_6
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.591700491558706412 25.591700505841720695 (-0.4589593) 0.00000003716 0.8965140289994 (-0.4430153448893) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_7 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.886579307588):ℝ):ℂ) + (((-0.4625766220363):ℝ):ℂ) * I)‖ ≤ 0.00000013711 := by
  have hl := lg_7
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.793434651531432426 27.793434665814460992 (-2.6606934) 0.0000000371 (-0.886579307588) (-0.4625766220363) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_8 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1439646791728):ℝ):ℂ) + ((0.9895828268266:ℝ):ℂ) * I)‖ ≤ 0.00000011422 := by
  have hl := lg_8
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.7006635286747 29.7006635500992 1.715263 0.00000001421 (-0.1439646791728) 0.9895828268266 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_9 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9994566080044:ℝ):ℂ) + ((0.032961928286:ℝ):ℂ) * I)‖ ≤ 0.00000010907 := by
  have hl := lg_9
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.382958630667612824 31.38295864495064139 0.0329679 0.00000000906 0.9994566080044 0.032961928286 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_10 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0987388785505:ℝ):ℂ) + (((-0.995113377391):ℝ):ℂ) * I)‖ ≤ 0.00000015764 := by
  have hl := lg_10
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.887822872095547147 32.88782289352006143 (-1.4718963) 0.00000005763 0.0987388785505 (-0.995113377391) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_11 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9528261951514):ℝ):ℂ) + (((-0.3035164602162):ℝ):ℂ) * I)‖ ≤ 0.00000015578 := by
  have hl := lg_11
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.249138170240706839 34.249138191665235405 (-2.8332116) 0.00000005577 (-0.9528261951514) (-0.3035164602162) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_12 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5942991056205):ℝ):ℂ) + ((0.8042441004117:ℝ):ℂ) * I)‖ ≤ 0.00000014615 := by
  have hl := lg_12
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.491921667783606412 35.491921689208120695 2.2071902 0.00000004614 (-0.5942991056205) 0.8042441004117 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_13 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4854310407753:ℝ):ℂ) + ((0.8742749594102:ℝ):ℂ) * I)‖ ≤ 0.00000013985 := by
  have hl := lg_13
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.6351716614847211 36.635171682909249666 1.0639402 0.00000003984 0.4854310407753 0.8742749594102 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_14 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999851160689:ℝ):ℂ) + ((0.0054559729311:ℝ):ℂ) * I)‖ ≤ 0.00000011534 := by
  have hl := lg_14
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.693655827756332426 37.693655849180860992 0.005456 0.00000001533 0.9999851160689 0.0054559729311 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_15 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.557048125821:ℝ):ℂ) + (((-0.8304802138036):ℝ):ℂ) * I)‖ ≤ 0.00000013189 := by
  have hl := lg_15
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.679081011204453559 38.679081032628982125 (-0.9799692) 0.00000003188 0.557048125821 (-0.8304802138036) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_16 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3249667533326):ℝ):ℂ) + (((-0.9457254407208):ℝ):ℂ) * I)‖ ≤ 0.00000013819 := by
  have hl := lg_16
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.6008847048996 39.6008847334656 (-1.9017729) 0.00000003818 (-0.3249667533326) (-0.9457254407208) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_17 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9309032548203):ℝ):ℂ) + (((-0.3652658347063):ℝ):ℂ) * I)‖ ≤ 0.00000016381 := by
  have hl := lg_17
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.466786178303726822 40.466786206869741105 (-2.7676743) 0.0000000638 (-0.9309032548203) (-0.3652658347063) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_18 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9036945416017):ℝ):ℂ) + ((0.4281777380464:ℝ):ℂ) * I)‖ ≤ 0.00000014338 := by
  have hl := lg_18
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.283179806892512824 41.28317982831704139 2.6991173 0.00000004337 (-0.9036945416017) 0.4281777380464 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_19 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3486017644204):ℝ):ℂ) + ((0.9372709372645:ℝ):ℂ) * I)‖ ≤ 0.00000012198 := by
  have hl := lg_19
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.055421928295850649 42.055421949720393498 1.9268752 0.00000002197 (-0.3486017644204) 0.9372709372645 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_20 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3677080766632:ℝ):ℂ) + ((0.929941272531:ℝ):ℂ) * I)‖ ≤ 0.00000012664 := by
  have hl := lg_20
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.788044048320447147 42.78804407688646143 1.1942531 0.00000002663 0.3677080766632 0.929941272531 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_21 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.878834116524:ℝ):ℂ) + ((0.4771274417108:ℝ):ℂ) * I)‖ ≤ 0.00000013805 := by
  have hl := lg_21
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.484913966865238838 43.484913988289781687 0.4973832 0.00000003804 0.878834116524 0.4771274417108 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_22 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9860775369749:ℝ):ℂ) + (((-0.1662861722258):ℝ):ℂ) * I)‖ ≤ 0.00000012479 := by
  have hl := lg_22
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.149359346465606839 44.149359375031635405 (-0.1670622) 0.00000002478 0.9860775369749 (-0.1662861722258) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_23 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6952945386341:ℝ):ℂ) + (((-0.7187249157679):ℝ):ℂ) * I)‖ ≤ 0.00000014959 := by
  have hl := lg_23
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.784263871264814578 44.784263899830857427 (-0.8019667) 0.00000004958 0.6952945386341 (-0.7187249157679) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_24 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1602566191939:ℝ):ℂ) + (((-0.987075385168):ℝ):ℂ) * I)‖ ≤ 0.00000012233 := by
  have hl := lg_24
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.392142844008506412 45.392142872574520695 (-1.4098457) 0.00000002232 0.1602566191939 (-0.987075385168) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_25 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4096861371563):ℝ):ℂ) + (((-0.9122265447894):ℝ):ℂ) * I)‖ ≤ 0.00000015853 := by
  have hl := lg_25
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.975203391741294294 45.97520342030732286 (-1.9929063) 0.00000005852 (-0.4096861371563) (-0.9122265447894) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_26 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8317759765999):ℝ):ℂ) + (((-0.555111452492):ℝ):ℂ) * I)‖ ≤ 0.00000011603 := by
  have hl := lg_26
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.5353928377096211 46.535392866275649666 (-2.5530957) 0.00000001602 (-0.8317759765999) (-0.555111452492) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_27 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9987775059769):ℝ):ℂ) + (((-0.0494317001572):ℝ):ℂ) * I)‖ ≤ 0.00000011718 := by
  have hl := lg_27
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.074437946001419236 47.074437967425962085 (-3.0921408) 0.00000001717 (-0.9987775059769) (-0.0494317001572) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_28 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8915740607667):ℝ):ℂ) + ((0.452874920989:ℝ):ℂ) * I)‖ ≤ 0.00000015347 := by
  have hl := lg_28
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.593877003981232426 47.593877032547260992 2.6716054 0.00000005346 (-0.8915740607667) 0.452874920989 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_29 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5643121067528):ℝ):ℂ) + ((0.8255615338439:ℝ):ℂ) * I)‖ ≤ 0.00000013261 := by
  have hl := lg_29
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.095086324845601836 48.095086353411644685 2.1703961 0.0000000326 (-0.5643121067528) 0.8255615338439 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_30 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1151281169048):ℝ):ℂ) + ((0.9933506514305:ℝ):ℂ) * I)‖ ≤ 0.00000015857 := by
  have hl := lg_30
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.579302187429353559 48.579302215995382125 1.6861803 0.00000005856 (-0.1151281169048) 0.9933506514305 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_31 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3456703949545:ℝ):ℂ) + ((0.9383559975042:ℝ):ℂ) * I)‖ ≤ 0.00000013064 := by
  have hl := lg_31
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.047639226810119729 49.047639255376162578 1.2178432 0.00000003063 0.3456703949545 0.9383559975042 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_32 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.721813944799:ℝ):ℂ) + ((0.6920871542614:ℝ):ℂ) * I)‖ ≤ 0.00000015941 := by
  have hl := lg_32
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.5011058811245 49.501105916832 0.7643766 0.0000000594 0.721813944799 0.6920871542614 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_33 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9476938244653:ℝ):ℂ) + ((0.3191808500996:ℝ):ℂ) * I)‖ ≤ 0.00000015672 := by
  have hl := lg_33
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.940617485574513251 49.9406175141405561 0.324865 0.00000005671 0.9476938244653 0.3191808500996 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_34 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9948507725087:ℝ):ℂ) + (((-0.1013505818381):ℝ):ℂ) * I)‖ ≤ 0.00000013281 := by
  have hl := lg_34
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.367007354528626822 50.367007390236141105 (-0.1015249) 0.0000000328 0.9948507725087 (-0.1013505818381) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_35 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.870019773754:ℝ):ℂ) + (((-0.4930168285942):ℝ):ℂ) * I)‖ ≤ 0.00000011855 := by
  have hl := lg_35
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.781036347402079573 50.781036375968122422 (-0.5155539) 0.00000001854 0.870019773754 (-0.4930168285942) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_36 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6074748878192:ℝ):ℂ) + (((-0.7943388827629):ℝ):ℂ) * I)‖ ≤ 0.00000015426 := by
  have hl := lg_36
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.183400983117412824 51.18340101168344139 (-0.9179185) 0.00000005425 0.6074748878192 (-0.7943388827629) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_37 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2585667741202:ℝ):ℂ) + (((-0.9659933867895):ℝ):ℂ) * I)‖ ≤ 0.00000012601 := by
  have hl := lg_37
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.574740531446245086 51.574740560012287935 (-1.3092581) 0.000000026 0.2585667741202 (-0.9659933867895) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_38 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1190811273772):ℝ):ℂ) + (((-0.9928845275771):ℝ):ℂ) * I)‖ ≤ 0.00000015293 := by
  have hl := lg_38
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.955643104520750649 51.955643133086793498 (-1.6901607) 0.00000005292 (-0.1190811273772) (-0.9928845275771) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_39 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4709542362176):ℝ):ℂ) + (((-0.8821576431588):ℝ):ℂ) * I)‖ ≤ 0.00000014796 := by
  have hl := lg_39
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.326650976818527512 52.326651005384570361 (-2.0611685) 0.00000004795 (-0.4709542362176) (-0.8821576431588) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p283_40 : ‖exp (-((((((14283:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7525899608031):ℝ):ℂ) + (((-0.6584894462814):ℝ):ℂ) * I)‖ ≤ 0.00000013291 := by
  have hl := lg_40
  refine (ecis_approx ((((14283:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.688265224545347147 52.68826526025286143 (-2.4227828) 0.0000000329 (-0.7525899608031) (-0.6584894462814) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_2 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8757243580188):ℝ):ℂ) + ((0.4828114007353:ℝ):ℂ) * I)‖ ≤ 0.00000010376 := by
  have hl := lg_2
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.9286402106172 9.9286402177792 2.6377304 0.00000000375 (-0.8757243580188) 0.4828114007353 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_3 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9995922147888):ℝ):ℂ) + ((0.0285552712073:ℝ):ℂ) * I)‖ ≤ 0.0000001048 := by
  have hl := lg_3
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.736522419158541136 15.73652242632055546 3.1130335 0.00000000479 (-0.9995922147888) 0.0285552712073 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_4 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5337863086136:ℝ):ℂ) + (((-0.8456194041865):ℝ):ℂ) * I)‖ ≤ 0.00000011403 := by
  have hl := lg_4
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.8572804212344 19.8572804355584 (-1.0077245) 0.00000001402 0.5337863086136 (-0.8456194041865) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_5 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4867420345088):ℝ):ℂ) + ((0.8735457582958:ℝ):ℂ) * I)‖ ≤ 0.00000013588 := by
  have hl := lg_5
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.053588650259129716 23.05358866458314404 2.0791526 0.00000003587 (-0.4867420345088) 0.8735457582958 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_6 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8615804438841:ℝ):ℂ) + (((-0.5076210581886):ℝ):ℂ) * I)‖ ≤ 0.0000001154 := by
  have hl := lg_6
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.665162629775741136 25.66516264409975546 (-0.5324214) 0.00000001539 0.8615804438841 (-0.5076210581886) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_7 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9206254572813):ℝ):ℂ) + (((-0.3904468814855):ℝ):ℂ) * I)‖ ≤ 0.00000015324 := by
  have hl := lg_7
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.873216967621384728 27.873216981945413376 (-2.7404757) 0.00000005323 (-0.9206254572813) (-0.3904468814855) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_8 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0591749833762):ℝ):ℂ) + ((0.9982476252624:ℝ):ℂ) * I)‖ ≤ 0.00000011745 := by
  have hl := lg_8
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.7859206318516 29.7859206533376 1.6300059 0.00000001744 (-0.0591749833762) 0.9982476252624 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_9 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9983691933505:ℝ):ℂ) + (((-0.0570872469885):ℝ):ℂ) * I)‖ ≤ 0.00000011676 := by
  have hl := lg_9
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.473044838317082272 31.47304485264111092 (-0.0571183) 0.00000001675 0.9983691933505 (-0.0570872469885) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_10 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0044940116678:ℝ):ℂ) + (((-0.9999899018785):ℝ):ℂ) * I)‖ ≤ 0.00000014648 := by
  have hl := lg_10
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.982228860876329716 32.98222888236234404 (-1.5663023) 0.00000004647 0.0044940116678 (-0.9999899018785) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_11 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9780168927092):ℝ):ℂ) + (((-0.2085256753094):ℝ):ℂ) * I)‖ ≤ 0.00000015952 := by
  have hl := lg_11
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.347451876393466692 34.34745189787949534 (-2.9315254) 0.00000005951 (-0.9780168927092) (-0.2085256753094) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_12 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5094217469508):ℝ):ℂ) + ((0.8605169863093:ℝ):ℂ) * I)‖ ≤ 0.00000011882 := by
  have hl := lg_12
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.593802840392941136 35.59380286187895546 2.105309 0.00000001881 (-0.5094217469508) 0.8605169863093 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_13 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5745212644976:ℝ):ℂ) + ((0.8184896557929:ℝ):ℂ) * I)‖ ≤ 0.00000015798 := by
  have hl := lg_13
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.7403345851086708 36.740334606594699448 0.9587772 0.00000005797 0.5745212644976 0.8184896557929 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_14 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9947263434359:ℝ):ℂ) + (((-0.102564621945):ℝ):ℂ) * I)‖ ≤ 0.00000015666 := by
  have hl := lg_14
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.801857178238584728 37.801857199724613376 (-0.1027453) 0.00000005665 0.9947263434359 (-0.102564621945) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_15 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.461599218537:ℝ):ℂ) + (((-0.8870885871468):ℝ):ℂ) * I)‖ ≤ 0.00000014784 := by
  have hl := lg_15
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.790111069417670852 38.7901110909036995 (-1.0909992) 0.00000004783 0.461599218537 (-0.8870885871468) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_16 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4301443534735):ℝ):ℂ) + (((-0.9027601205032):ℝ):ℂ) * I)‖ ≤ 0.00000012805 := by
  have hl := lg_16
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.7145608424688 39.7145608711168 (-2.015449) 0.00000002804 (-0.4301443534735) (-0.9027601205032) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_17 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9669642920484):ℝ):ℂ) + (((-0.2549118625027):ℝ):ℂ) * I)‖ ≤ 0.00000011773 := by
  have hl := lg_17
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.582947925367400616 40.58294795401541494 (-2.8838361) 0.00000001772 (-0.9669642920484) (-0.2549118625027) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_18 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8467338472346):ℝ):ℂ) + ((0.5320167214248:ℝ):ℂ) * I)‖ ≤ 0.00000012018 := by
  have hl := lg_18
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.401685048934282272 41.40168507042031092 2.5806121 0.00000002017 (-0.8467338472346) 0.5320167214248 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_19 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2331900349879):ℝ):ℂ) + ((0.9724311839823:ℝ):ℂ) * I)‖ ≤ 0.00000012386 := by
  have hl := lg_19
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.176143926409701372 42.176143947895744344 1.8061532 0.00000002385 (-0.2331900349879) 0.9724311839823 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_20 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4788710098149:ℝ):ℂ) + ((0.8778852749414:ℝ):ℂ) * I)‖ ≤ 0.0000001499 := by
  have hl := lg_20
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.910869071493529716 42.91086910014154404 1.0714281 0.00000004989 0.4788710098149 0.8778852749414 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_21 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9313993568627:ℝ):ℂ) + ((0.3639989533442:ℝ):ℂ) * I)‖ ≤ 0.00000015802 := by
  have hl := lg_21
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.609739386779925864 43.609739408265968836 0.3725578 0.00000005801 0.9313993568627 0.3639989533442 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_22 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9571517891054:ℝ):ℂ) + (((-0.2895866927404):ℝ):ℂ) * I)‖ ≤ 0.00000016326 := by
  have hl := lg_22
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.276092087010666692 44.27609211565869534 (-0.293795) 0.00000006325 0.9571517891054 (-0.2895866927404) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_23 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5974154552471:ℝ):ℂ) + (((-0.8019319009941):ℝ):ℂ) * I)‖ ≤ 0.0000001162 := by
  have hl := lg_23
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.912819134075278584 44.912819162723321556 (-0.930522) 0.00000001619 0.5974154552471 (-0.8019319009941) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_24 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0306456279365:ℝ):ℂ) + (((-0.9995303124409):ℝ):ℂ) * I)‖ ≤ 0.00000012942 := by
  have hl := lg_24
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.522443051010141136 45.52244307965815546 (-1.5401459) 0.00000002941 0.0306456279365 (-0.9995303124409) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_25 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.526164462617):ℝ):ℂ) + (((-0.8503828304191):ℝ):ℂ) * I)‖ ≤ 0.00000014975 := by
  have hl := lg_25
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.107177300518259432 46.10717732916628808 (-2.1248802) 0.00000004974 (-0.526164462617) (-0.8503828304191) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_26 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8982983995888):ℝ):ℂ) + (((-0.4393859182789):ℝ):ℂ) * I)‖ ≤ 0.00000015455 := by
  have hl := lg_26
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.6689747957258708 46.668974824373899448 (-2.6866777) 0.00000005454 (-0.8982983995888) (-0.4393859182789) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_27 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9963319313917):ℝ):ℂ) + ((0.0855726707966:ℝ):ℂ) * I)‖ ≤ 0.00000012154 := by
  have hl := lg_27
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.209567257475623408 47.20956727896166638 3.0559152 0.00000002153 (-0.9963319313917) 0.0855726707966 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_28 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8215867197293):ℝ):ℂ) + ((0.5700835569511:ℝ):ℂ) * I)‖ ≤ 0.00000016008 := by
  have hl := lg_28
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.730497388855784728 47.730497417503813376 2.5349851 0.00000006007 (-0.8215867197293) 0.5700835569511 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_29 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4453281035988):ℝ):ℂ) + ((0.8953674553728:ℝ):ℂ) * I)‖ ≤ 0.00000012506 := by
  have hl := lg_29
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.233145453832416208 48.23314548248045918 2.032337 0.00000002505 (-0.4453281035988) 0.8953674553728 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_30 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0240628040547:ℝ):ℂ) + ((0.9997104488105:ℝ):ℂ) * I)‖ ≤ 0.00000015126 := by
  have hl := lg_30
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.718751280034870852 48.7187513086828995 1.5467312 0.00000005125 0.0240628040547 0.9997104488105 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_31 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4739283492334:ℝ):ℂ) + ((0.8805634104327:ℝ):ℂ) * I)‖ ≤ 0.0000001553 := by
  have hl := lg_31
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.188432702151379612 49.188432730799422584 1.0770497 0.00000005529 0.4739283492334 0.8805634104327 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_32 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8125507661665:ℝ):ℂ) + ((0.5828904291565:ℝ):ℂ) * I)‖ ≤ 0.00000013147 := by
  have hl := lg_32
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.643201053086 49.643201088896 0.6222814 0.00000003146 0.8125507661665 0.5828904291565 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_33 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9835725795809:ℝ):ℂ) + ((0.1805131039472:ℝ):ℂ) * I)‖ ≤ 0.0000001619 := by
  have hl := lg_33
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.083974295552007828 50.0839743242000508 0.1815081 0.00000006189 0.9835725795809 0.1805131039472 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_34 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9698685374674:ℝ):ℂ) + (((-0.2436288571389):ℝ):ℂ) * I)‖ ≤ 0.00000012147 := by
  have hl := lg_34
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.511588135984600616 50.51158817179461494 (-0.2461057) 0.00000002146 0.9698685374674 (-0.2436288571389) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_35 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7891802639335:ℝ):ℂ) + (((-0.6141616326488):ℝ):ℂ) * I)‖ ≤ 0.00000013957 := by
  have hl := lg_35
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.926805617880514444 50.926805646528557416 (-0.6613232) 0.00000003956 0.7891802639335 (-0.6141616326488) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_36 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.484641722567:ℝ):ℂ) + (((-0.8747127532781):ℝ):ℂ) * I)‖ ≤ 0.00000013078 := by
  have hl := lg_36
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.330325259551482272 51.33032528819951092 (-1.0648428) 0.00000003077 0.484641722567 (-0.8747127532781) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_37 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1132471547851:ℝ):ℂ) + (((-0.9935668482458):ℝ):ℂ) * I)‖ ≤ 0.00000013705 := by
  have hl := lg_37
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.722788165822027208 51.72278819447007018 (-1.4573057) 0.00000003704 0.1132471547851 (-0.9935668482458) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_38 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2652906614926):ℝ):ℂ) + (((-0.9641684836809):ℝ):ℂ) * I)‖ ≤ 0.00000012042 := by
  have hl := lg_38
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.104784137026901372 52.104784165674944344 (-1.8393017) 0.00000002041 (-0.2652906614926) (-0.9641684836809) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_39 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5976591719693):ℝ):ℂ) + (((-0.8017502816645):ℝ):ℂ) * I)‖ ≤ 0.00000015318 := by
  have hl := lg_39
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.476857004267211936 52.476857032915254908 (-2.2113746) 0.00000005317 (-0.5976591719693) (-0.8017502816645) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p324_40 : ‖exp (-((((((14324:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8432120231033):ℝ):ℂ) + (((-0.537581141805):ℝ):ℂ) * I)‖ ≤ 0.0000001605 := by
  have hl := lg_40
  refine (ecis_approx ((((14324:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.839509282110729716 52.83950931792074404 (-2.5740268) 0.00000006049 (-0.8432120231033) (-0.537581141805) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_2 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8616515766708):ℝ):ℂ) + ((0.5075003057527:ℝ):ℂ) * I)‖ ≤ 0.00000013785 := by
  have hl := lg_2
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.9570592450095 9.957059252192 2.6093114 0.00000003784 (-0.8616515766708) 0.5075003057527 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_3 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9972925764609):ℝ):ℂ) + ((0.0735358171974:ℝ):ℂ) * I)‖ ≤ 0.00000010864 := by
  have hl := lg_3
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.78156552298327586 15.781565530165790225 3.0679904 0.00000000863 (-0.9972925764609) 0.0735358171974 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_4 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4848867980522:ℝ):ℂ) + (((-0.8745769223314):ℝ):ℂ) * I)‖ ≤ 0.00000013153 := by
  have hl := lg_4
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.914118490019 19.914118504384 (-1.0645626) 0.00000003152 0.4848867980522 (-0.8745769223314) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_5 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4280818714379):ℝ):ℂ) + ((0.9037399578099:ℝ):ℂ) * I)‖ ≤ 0.00000012409 := by
  have hl := lg_5
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.119575604647612285 23.11957561901262665 2.0131656 0.00000002408 (-0.4280818714379) 0.9037399578099 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_6 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8219992753922:ℝ):ℂ) + (((-0.5694885347877):ℝ):ℂ) * I)‖ ≤ 0.00000015365 := by
  have hl := lg_6
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.73862476799277586 25.738624782357790225 (-0.6058835) 0.00000005364 0.8219992753922 (-0.5694885347877) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_7 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9488147668936):ℝ):ℂ) + (((-0.3158330855441):ℝ):ℂ) * I)‖ ≤ 0.00000014502 := by
  have hl := lg_7
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.95299928371133703 27.95299929807636576 (-2.8202581) 0.00000004501 (-0.9488147668936) (-0.3158330855441) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_8 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.026044581468:ℝ):ℂ) + ((0.9996607823537:ℝ):ℂ) * I)‖ ≤ 0.00000012069 := by
  have hl := lg_8
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.8711777350285 29.871177756576 1.5447488 0.00000002068 0.026044581468 0.9996607823537 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_9 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9891849681597:ℝ):ℂ) + (((-0.1466734426097):ℝ):ℂ) * I)‖ ≤ 0.00000012445 := by
  have hl := lg_9
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.56313104596655172 31.56313106033158045 (-0.1472045) 0.00000002444 0.9891849681597 (-0.1466734426097) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_10 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.089790878323):ℝ):ℂ) + (((-0.9959606408737):ℝ):ℂ) * I)‖ ≤ 0.00000013532 := by
  have hl := lg_10
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.076634849657112285 33.07663487120462665 (-1.6607083) 0.00000003531 (-0.089790878323) (-0.9959606408737) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_11 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9937620675346):ℝ):ℂ) + (((-0.1115210862306):ℝ):ℂ) * I)‖ ≤ 0.00000015337 := by
  have hl := lg_11
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.445765582546226545 34.445765604093755275 (-3.0298391) 0.00000005336 (-0.9937620675346) (-0.1115210862306) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_12 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4192612753417):ℝ):ℂ) + ((0.9078656194587:ℝ):ℂ) * I)‖ ≤ 0.00000013009 := by
  have hl := lg_12
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.69568401300227586 35.695684034549790225 2.0034278 0.00000003008 (-0.4192612753417) 0.9078656194587 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_13 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.657263488299:ℝ):ℂ) + ((0.7536608699866:ℝ):ℂ) * I)‖ ≤ 0.00000013436 := by
  have hl := lg_13
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.8454975087326205 36.84549753028014923 0.8536143 0.00000003435 0.657263488299 0.7536608699866 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_14 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9778331274908:ℝ):ℂ) + (((-0.2093857081596):ℝ):ℂ) * I)‖ ≤ 0.00000011437 := by
  have hl := lg_14
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.91005852872083703 37.91005855026836576 (-0.2109467) 0.00000001436 0.9778331274908 (-0.2093857081596) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_15 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3604656227527:ℝ):ℂ) + (((-0.9327724989586):ℝ):ℂ) * I)‖ ≤ 0.00000011546 := by
  have hl := lg_15
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.901141127630888145 38.901141149178416875 (-1.2020293) 0.00000001545 0.3604656227527 (-0.9327724989586) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_16 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5297695861492):ℝ):ℂ) + (((-0.8481416070349):ℝ):ℂ) * I)‖ ≤ 0.00000016305 := by
  have hl := lg_16
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.828236980038 39.828237008768 (-2.1291252) 0.00000006304 (-0.5297695861492) (-0.8481416070349) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_17 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9899921859565):ℝ):ℂ) + (((-0.1411221858474):ℝ):ℂ) * I)‖ ≤ 0.0000001581 := by
  have hl := lg_17
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.69910967243107441 40.699109701161088775 (-2.9999978) 0.00000005809 (-0.9899921859565) (-0.1411221858474) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_18 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7778959076306):ℝ):ℂ) + ((0.628393154681:ℝ):ℂ) * I)‖ ≤ 0.0000001593 := by
  have hl := lg_18
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.52019029097605172 41.52019031252358045 2.4621068 0.00000005929 (-0.7778959076306) 0.628393154681 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_19 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1143839656993):ℝ):ℂ) + ((0.9934366151851:ℝ):ℂ) * I)‖ ≤ 0.00000012575 := by
  have hl := lg_19
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.296865924523552095 42.29686594607109519 1.6854312 0.00000002574 (-0.1143839656993) 0.9934366151851 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_20 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5828188629456:ℝ):ℂ) + ((0.8126021000433:ℝ):ℂ) * I)‖ ≤ 0.00000015561 := by
  have hl := lg_20
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.033694094666612285 43.03369412339662665 0.948603 0.0000000556 0.5828188629456 0.8126021000433 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_21 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.969470967891:ℝ):ℂ) + ((0.2452061223064:ℝ):ℂ) * I)‖ ≤ 0.00000014358 := by
  have hl := lg_21
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.73456480669461289 43.734564828242155985 0.2477323 0.00000004357 0.969470967891 0.2452061223064 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_22 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9128736379985:ℝ):ℂ) + (((-0.408242233297):ℝ):ℂ) * I)‖ ≤ 0.00000012272 := by
  have hl := lg_22
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.402824827555726545 44.402824856285755275 (-0.4205277) 0.00000002271 0.9128736379985 (-0.408242233297) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_23 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4896767960431:ℝ):ℂ) + (((-0.8719040287881):ℝ):ℂ) * I)‖ ≤ 0.00000015339 := by
  have hl := lg_23
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.04137439688574259 45.041374425615785685 (-1.0590773) 0.00000005338 0.4896767960431 (-0.8719040287881) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_24 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0994849334116):ℝ):ℂ) + (((-0.9950390685916):ℝ):ℂ) * I)‖ ≤ 0.0000001365 := by
  have hl := lg_24
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.65274325801177586 45.652743286741790225 (-1.6704461) 0.00000003649 (-0.0994849334116) (-0.9950390685916) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_25 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6334918171359):ℝ):ℂ) + (((-0.7737493894064):ℝ):ℂ) * I)‖ ≤ 0.00000014098 := by
  have hl := lg_25
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.23915120929522457 46.2391512380252533 (-2.2568541) 0.00000004097 (-0.6334918171359) (-0.7737493894064) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_26 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9488152406422):ℝ):ℂ) + (((-0.3158316623216):ℝ):ℂ) * I)‖ ≤ 0.00000013223 := by
  have hl := lg_26
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.8025567537421205 46.80255678247214923 (-2.8202596) 0.00000003222 (-0.9488152406422) (-0.3158316623216) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_27 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9757210741159):ℝ):ℂ) + ((0.219016860599:ℝ):ℂ) * I)‖ ≤ 0.00000013308 := by
  have hl := lg_27
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.34469656894982758 47.344696590497370675 2.9207859 0.00000003307 (-0.9757210741159) 0.219016860599 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_28 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7362881451184):ℝ):ℂ) + ((0.6766681367757:ℝ):ℂ) * I)‖ ≤ 0.00000014504 := by
  have hl := lg_28
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.86711777373033703 47.86711780246036576 2.3983647 0.00000004503 (-0.7362881451184) 0.6766681367757 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_29 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3178694800526):ℝ):ℂ) + ((0.9481344807827:ℝ):ℂ) * I)‖ ≤ 0.00000015413 := by
  have hl := lg_29
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.37120458281923058 48.371204611549273675 1.8942779 0.00000005412 (-0.3178694800526) 0.9481344807827 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_30 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.162786556273:ℝ):ℂ) + ((0.9866613081989:ℝ):ℂ) * I)‖ ≤ 0.00000014395 := by
  have hl := lg_30
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.858200372640388145 48.858200401370416875 1.4072821 0.00000004394 0.162786556273 0.9866613081989 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_31 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5928071402094:ℝ):ℂ) + ((0.8053444570597:ℝ):ℂ) * I)‖ ≤ 0.0000001488 := by
  have hl := lg_31
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.329226177492639495 49.32922620622268259 0.9362563 0.00000004879 0.5928071402094 0.8053444570597 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_32 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.886908924121:ℝ):ℂ) + ((0.4619443259901:ℝ):ℂ) * I)‖ ≤ 0.0000001324 := by
  have hl := lg_32
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.7852962250475 49.78529626096 0.4801862 0.00000003239 0.886908924121 0.4619443259901 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_33 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9992723274225:ℝ):ℂ) + ((0.0381420456661:ℝ):ℂ) * I)‖ ≤ 0.00000015192 := by
  have hl := lg_33
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.227331105529502405 50.2273311342595455 0.0381513 0.00000005191 0.9992723274225 0.0381420456661 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_34 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9246478425842:ℝ):ℂ) + (((-0.3808232755549):ℝ):ℂ) * I)‖ ≤ 0.00000014001 := by
  have hl := lg_34
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.65616891744057441 50.656168953353088775 (-0.3906865) 0.00000004 0.9246478425842 (-0.3808232755549) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_35 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6916014528173:ℝ):ℂ) + (((-0.7222793299417):ℝ):ℂ) * I)‖ ≤ 0.00000015967 := by
  have hl := lg_35
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.072574888358949315 51.07257491708899241 (-0.8070924) 0.00000005966 0.6916014528173 (-0.7222793299417) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_36 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3513655238669:ℝ):ℂ) + (((-0.9362383610159):ℝ):ℂ) * I)‖ ≤ 0.00000012147 := by
  have hl := lg_36
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.47724953598555172 51.47724956471558045 (-1.2117671) 0.00000002146 0.3513655238669 (-0.9362383610159) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_37 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0345501956564):ℝ):ℂ) + (((-0.9994029637638):ℝ):ℂ) * I)‖ ≤ 0.00000015725 := by
  have hl := lg_37
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.87083580019780933 51.870835828927852425 (-1.6053534) 0.00000005724 (-0.0345501956564) (-0.9994029637638) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_38 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4056102550417):ℝ):ℂ) + (((-0.9140461262987):ℝ):ℂ) * I)‖ ≤ 0.00000014084 := by
  have hl := lg_38
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.253925169533052095 52.25392519826309519 (-1.9884427) 0.00000004083 (-0.4056102550417) (-0.9140461262987) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_39 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7109050609154):ℝ):ℂ) + (((-0.703287988195):ℝ):ℂ) * I)‖ ≤ 0.00000012574 := by
  have hl := lg_39
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.62706303171589636 52.627063060445939455 (-2.3615806) 0.00000002573 (-0.7109050609154) (-0.703287988195) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p365_40 : ‖exp (-((((((14365:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9145826035012):ℝ):ℂ) + (((-0.40439913605):ℝ):ℂ) * I)‖ ≤ 0.00000011817 := by
  have hl := lg_40
  refine (ecis_approx ((((14365:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.990753339676112285 52.99075337558862665 (-2.7252709) 0.00000001816 (-0.9145826035012) (-0.40439913605) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_2 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8468828850785):ℝ):ℂ) + ((0.531779445719:ℝ):ℂ) * I)‖ ≤ 0.00000013497 := by
  have hl := lg_2
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.9854782794018 9.9854782866048 2.5808923 0.00000003496 (-0.8468828850785) 0.531779445719 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_3 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9929698923829):ℝ):ℂ) + ((0.1183671929949:ℝ):ℂ) * I)‖ ≤ 0.00000011249 := by
  have hl := lg_3
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.826608626808010584 15.82660863401102499 3.0229473 0.00000001248 (-0.9929698923829) 0.1183671929949 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_4 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4344213386748:ℝ):ℂ) + (((-0.9007097759567):ℝ):ℂ) * I)‖ ≤ 0.00000015169 := by
  have hl := lg_4
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.9709565588036 19.9709565732096 (-1.1214006) 0.00000005168 0.4344213386748 (-0.9007097759567) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_5 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3675584875149):ℝ):ℂ) + ((0.9300004076629:ℝ):ℂ) * I)‖ ≤ 0.00000014474 := by
  have hl := lg_5
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.185562559036094854 23.18556257344210926 1.9471787 0.00000004473 (-0.3675584875149) 0.9300004076629 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_6 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7779839715545:ℝ):ℂ) + (((-0.6282841236291):ℝ):ℂ) * I)‖ ≤ 0.00000012252 := by
  have hl := lg_6
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.812086906209810584 25.81208692061582499 (-0.6793457) 0.00000002251 0.7779839715545 (-0.6282841236291) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_7 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9709678299223):ℝ):ℂ) + (((-0.2392101021699):ℝ):ℂ) * I)‖ ≤ 0.00000012893 := by
  have hl := lg_7
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.032781599801289332 28.032781614207318144 (-2.9000404) 0.00000002892 (-0.9709678299223) (-0.2392101021699) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_8 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1110749488035:ℝ):ℂ) + ((0.9938120324026:ℝ):ℂ) * I)‖ ≤ 0.00000012393 := by
  have hl := lg_8
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.9564348382054 29.9564348598144 1.4594917 0.00000002392 0.1110749488035 0.9938120324026 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_9 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9719784168329:ℝ):ℂ) + (((-0.2350701112668):ℝ):ℂ) * I)‖ ≤ 0.00000013214 := by
  have hl := lg_9
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.653217253616021168 31.65321726802204998 (-0.2372907) 0.00000003213 0.9719784168329 (-0.2350701112668) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_10 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1832761019372):ℝ):ℂ) + (((-0.9830614784732):ℝ):ℂ) * I)‖ ≤ 0.00000012416 := by
  have hl := lg_10
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.171040838437894854 33.17104086004690926 (-1.7551143) 0.00000002415 (-0.1832761019372) (-0.9830614784732) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_11 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999096862036):ℝ):ℂ) + (((-0.0134394486947):ℝ):ℂ) * I)‖ ≤ 0.00000014721 := by
  have hl := lg_11
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.544079288698986398 34.54407931030801521 (-3.1281528) 0.0000000472 (-0.9999096862036) (-0.0134394486947) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_12 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3247527273461):ℝ):ℂ) + ((0.9457989564803:ℝ):ℂ) * I)‖ ≤ 0.00000015748 := by
  have hl := lg_12
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.797565185611610584 35.79756520722062499 1.9015466 0.00000005747 (-0.3247527273461) 0.9457989564803 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_13 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7327435768817:ℝ):ℂ) + ((0.680504849754:ℝ):ℂ) * I)‖ ≤ 0.0000001109 := by
  have hl := lg_13
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.9506604323565702 36.950660453965599012 0.7484514 0.00000001089 0.7327435768817 0.680504849754 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_14 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9495030842328:ℝ):ℂ) + (((-0.3137576979652):ℝ):ℂ) * I)‖ ≤ 0.00000015775 := by
  have hl := lg_14
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.018259879203089332 38.018259900812118144 (-0.319148) 0.00000005774 0.9495030842328 (-0.3137576979652) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_15 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.254892884175:ℝ):ℂ) + (((-0.9669692950642):ℝ):ℂ) * I)‖ ≤ 0.00000015725 := by
  have hl := lg_15
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.012171185844105438 39.01217120745313425 (-1.3130594) 0.00000005724 0.254892884175 (-0.9669692950642) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_16 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6225562792643):ℝ):ℂ) + (((-0.7825750309936):ℝ):ℂ) * I)‖ ≤ 0.00000012549 := by
  have hl := lg_16
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.9419131176072 39.9419131464192 (-2.2428013) 0.00000002548 (-0.6225562792643) (-0.7825750309936) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_17 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996765970192):ℝ):ℂ) + (((-0.0254303115425):ℝ):ℂ) * I)‖ ≤ 0.0000001236 := by
  have hl := lg_17
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.815271419494748204 40.81527144830676261 (-3.1161596) 0.00000002359 (-0.9996765970192) (-0.0254303115425) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_18 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6981464324114):ℝ):ℂ) + ((0.7159549978091:ℝ):ℂ) * I)‖ ≤ 0.00000011725 := by
  have hl := lg_18
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.638695533017821168 41.63869555462684998 2.3436016 0.00000001724 (-0.6981464324114) 0.7159549978091 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_19 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0060870892038:ℝ):ℂ) + ((0.9999814735008:ℝ):ℂ) * I)‖ ≤ 0.00000012763 := by
  have hl := lg_19
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.417587922637402818 42.417587944246446036 1.5647092 0.00000002762 0.0060870892038 0.9999814735008 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_20 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6779852821471:ℝ):ℂ) + ((0.7350754772076:ℝ):ℂ) * I)‖ ≤ 0.00000013243 := by
  have hl := lg_20
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.156519117839694854 43.15651914665170926 0.825778 0.00000003242 0.6779852821471 0.7350754772076 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_21 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9924564502815:ℝ):ℂ) + ((0.1225976928602:ℝ):ℂ) * I)‖ ≤ 0.00000012366 := by
  have hl := lg_21
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.859390226609299916 43.859390248218343134 0.1229069 0.00000002365 0.9924564502815 0.1225976928602 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_22 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8539532749304:ℝ):ℂ) + (((-0.5203496941823):ℝ):ℂ) * I)‖ ≤ 0.00000014667 := by
  have hl := lg_22
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.529557568100786398 44.52955759691281521 (-0.5472604) 0.00000004666 0.8539532749304 (-0.5203496941823) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_23 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3738567421505:ℝ):ℂ) + (((-0.9274864615446):ℝ):ℂ) * I)‖ ≤ 0.00000013827 := by
  have hl := lg_23
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.169929659696206596 45.169929688508249814 (-1.1876325) 0.00000003826 0.3738567421505 (-0.9274864615446) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_24 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.227928813841):ℝ):ℂ) + (((-0.9736777987712):ℝ):ℂ) * I)‖ ≤ 0.00000014358 := by
  have hl := lg_24
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.783043465013410584 45.78304349382542499 (-1.8007463) 0.00000004357 (-0.227928813841) (-0.9736777987712) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_25 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7298015799646):ℝ):ℂ) + (((-0.6836590187015):ℝ):ℂ) * I)‖ ≤ 0.0000001322 := by
  have hl := lg_25
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.371125118072189708 46.37112514688421852 (-2.388828) 0.00000003219 (-0.7298015799646) (-0.6836590187015) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_26 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9824264847818):ℝ):ℂ) + (((-0.18664994417):ℝ):ℂ) * I)‖ ≤ 0.00000013851 := by
  have hl := lg_26
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.9361387117583702 46.936138740570399012 (-2.9538416) 0.0000000385 (-0.9824264847818) (-0.18664994417) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_27 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9373207148178):ℝ):ℂ) + ((0.3484679000995:ℝ):ℂ) * I)‖ ≤ 0.00000014461 := by
  have hl := lg_27
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.479825880424031752 47.47982590203307497 2.7856566 0.0000000446 (-0.9373207148178) 0.3484679000995 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_28 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6372680166547):ℝ):ℂ) + ((0.7706422483446:ℝ):ℂ) * I)‖ ≤ 0.00000013 := by
  have hl := lg_28
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.003738158604889332 48.003738187416918144 2.2617443 0.00000002999 (-0.6372680166547) 0.7706422483446 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_29 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1843616830424):ℝ):ℂ) + ((0.9828584688677:ℝ):ℂ) * I)‖ ≤ 0.00000014565 := by
  have hl := lg_29
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.509263711806044952 48.50926374061808817 1.7562187 0.00000004564 (-0.1843616830424) 0.9828584688677 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_30 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2983498792087:ℝ):ℂ) + ((0.9544565729126:ℝ):ℂ) * I)‖ ≤ 0.00000013664 := by
  have hl := lg_30
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.997649465245905438 48.99764949405793425 1.267833 0.00000003663 0.2983498792087 0.9544565729126 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_31 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6999543149816:ℝ):ℂ) + ((0.7141876202642:ℝ):ℂ) * I)‖ ≤ 0.00000012422 := by
  have hl := lg_31
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.470019652833899378 49.470019681645942596 0.7954628 0.00000002421 0.6999543149816 0.7141876202642 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_32 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9433895741696:ℝ):ℂ) + ((0.3316867669173:ℝ):ℂ) * I)‖ ≤ 0.00000016044 := by
  have hl := lg_32
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.927391397009 49.927391433024 0.338091 0.00000006043 0.9433895741696 0.3316867669173 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_33 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9944710038766:ℝ):ℂ) + (((-0.1050115348361):ℝ):ℂ) * I)‖ ≤ 0.00000014194 := by
  have hl := lg_33
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.370687915506996982 50.3706879443190402 (-0.1052055) 0.00000004193 0.9944710038766 (-0.1050115348361) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_34 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8601323180337:ℝ):ℂ) + (((-0.5100709710167):ℝ):ℂ) * I)‖ ≤ 0.00000015856 := by
  have hl := lg_34
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.800749698896548204 50.80074973491156261 (-0.5352673) 0.00000005855 0.8601323180337 (-0.5100709710167) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_35 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5793529596961:ℝ):ℂ) + (((-0.815076774354):ℝ):ℂ) * I)‖ ≤ 0.00000013023 := by
  have hl := lg_35
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.218344158837384186 51.218344187649427404 (-0.9528617) 0.00000003022 0.5793529596961 (-0.815076774354) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_36 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2105181199913:ℝ):ℂ) + (((-0.9775899555311):ℝ):ℂ) * I)‖ ≤ 0.00000014503 := by
  have hl := lg_36
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.624173812419621168 51.62417384123164998 (-1.3586914) 0.00000004502 0.2105181199913 (-0.9775899555311) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_37 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1815915545361):ℝ):ℂ) + (((-0.9833740424276):ℝ):ℂ) * I)‖ ≤ 0.00000012288 := by
  have hl := lg_37
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.018883434573591452 52.01888346338563467 (-1.753401) 0.00000002287 (-0.1815915545361) (-0.9833740424276) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_38 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5369246393568):ℝ):ℂ) + (((-0.8436302102483):ℝ):ℂ) * I)‖ ≤ 0.00000015541 := by
  have hl := lg_38
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.403066202039202818 52.403066230851246036 (-2.1375838) 0.0000000554 (-0.5369246393568) (-0.8436302102483) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_39 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8081417556142):ℝ):ℂ) + (((-0.5889880327989):ℝ):ℂ) * I)‖ ≤ 0.00000013055 := by
  have hl := lg_39
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.777269059164580784 52.777269087976624002 (-2.5117866) 0.00000003054 (-0.8081417556142) (-0.5889880327989) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p406_40 : ‖exp (-((((((14406:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9650721596812):ℝ):ℂ) + (((-0.2619842101292):ℝ):ℂ) * I)‖ ≤ 0.00000016021 := by
  have hl := lg_40
  refine (ecis_approx ((((14406:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.141997397241494854 53.14199743325650926 (-2.876515) 0.0000000602 (-0.9650721596812) (-0.2619842101292) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_2 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8314303141468):ℝ):ℂ) + ((0.5556290423065:ℝ):ℂ) * I)‖ ≤ 0.00000010667 := by
  have hl := lg_2
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.0138973137941 10.0138973210176 2.5524733 0.00000000666 (-0.8314303141468) 0.5556290423065 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_3 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9866329312847):ℝ):ℂ) + ((0.1629584564571:ℝ):ℂ) * I)‖ ≤ 0.00000011633 := by
  have hl := lg_3
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.871651730632745308 15.871651737856259755 2.9779042 0.00000001632 (-0.9866329312847) 0.1629584564571 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_4 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3825527412465:ℝ):ℂ) + (((-0.923933655716):ℝ):ℂ) * I)‖ ≤ 0.00000012051 := by
  have hl := lg_4
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.0277946275882 20.0277946420352 (-1.1782387) 0.0000000205 0.3825527412465 (-0.923933655716) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_5 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3054351397662):ℝ):ℂ) + ((0.9522128834427:ℝ):ℂ) * I)‖ ≤ 0.00000011531 := by
  have hl := lg_5
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.251549513424577423 23.25154952787159187 1.8811917 0.0000000153 (-0.3054351397662) 0.9522128834427 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_6 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7297720818574:ℝ):ℂ) + (((-0.6836905064):ℝ):ℂ) * I)‖ ≤ 0.00000013017 := by
  have hl := lg_6
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.885549044426845308 25.885549058873859755 (-0.7528078) 0.00000003016 0.7297720818574 (-0.6836905064) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_7 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9869437511696):ℝ):ℂ) + (((-0.1610653024423):ℝ):ℂ) * I)‖ ≤ 0.00000011284 := by
  have hl := lg_7
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.112563915891241634 28.112563930338270528 (-2.9798227) 0.00000001283 (-0.9869437511696) (-0.1610653024423) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_8 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1952984264749:ℝ):ℂ) + ((0.9807438629002:ℝ):ℂ) * I)‖ ≤ 0.00000012717 := by
  have hl := lg_8
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.0416919413823 30.0416919630528 1.3742346 0.00000002716 0.1952984264749 0.9807438629002 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_9 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9468890851284:ℝ):ℂ) + (((-0.3215603527561):ℝ):ℂ) * I)‖ ≤ 0.00000013983 := by
  have hl := lg_9
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.743303461265490616 31.74330347571251951 (-0.3273769) 0.00000003982 0.9468890851284 (-0.3215603527561) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_10 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2751290914191):ℝ):ℂ) + (((-0.9614072930103):ℝ):ℂ) * I)‖ ≤ 0.00000011301 := by
  have hl := lg_10
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.265446827218677423 33.26544684888919187 (-1.8495203) 0.000000013 (-0.2751290914191) (-0.9614072930103) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_11 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9964003758798):ℝ):ℂ) + ((0.0847719909117:ℝ):ℂ) * I)‖ ≤ 0.00000014824 := by
  have hl := lg_11
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.642392994851746251 34.642393016522275145 3.0567188 0.00000004823 (-0.9964003758798) 0.0847719909117 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_12 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2268763299559):ℝ):ℂ) + ((0.9739235754949:ℝ):ℂ) * I)‖ ≤ 0.00000013683 := by
  have hl := lg_12
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.899446358220945308 35.899446379891459755 1.7996655 0.00000003682 (-0.2268763299559) 0.9739235754949 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_13 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.800127547194:ℝ):ℂ) + ((0.5998298994059:ℝ):ℂ) * I)‖ ≤ 0.00000013459 := by
  have hl := lg_13
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.0558233559805199 37.055823377651048794 0.6432885 0.00000003458 0.800127547194 0.5998298994059 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_14 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9100675130804:ℝ):ℂ) + (((-0.4144600362346):ℝ):ℂ) * I)‖ ≤ 0.00000011341 := by
  have hl := lg_14
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.126461229685341634 38.126461251355870528 (-0.4273494) 0.0000000134 0.9100675130804 (-0.4144600362346) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_15 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1461812325383:ℝ):ℂ) + (((-0.9892578264808):ℝ):ℂ) * I)‖ ≤ 0.00000012267 := by
  have hl := lg_15
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.123201244057322731 39.123201265727851625 (-1.4240894) 0.00000002266 0.1461812325383 (-0.9892578264808) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_16 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7073068003262):ℝ):ℂ) + (((-0.7069067054339):ℝ):ℂ) * I)‖ ≤ 0.00000014101 := by
  have hl := lg_16
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.0555892551764 40.0555892840704 (-2.3564774) 0.000000041 (-0.7073068003262) (-0.7069067054339) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_17 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9958869780703):ℝ):ℂ) + ((0.0906042295774:ℝ):ℂ) * I)‖ ≤ 0.00000014521 := by
  have hl := lg_17
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.931433166558421998 40.931433195452436445 3.050864 0.0000000452 (-0.9958869780703) 0.0906042295774 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_18 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6086040186664):ℝ):ℂ) + ((0.7934741006803:ℝ):ℂ) * I)‖ ≤ 0.00000014649 := by
  have hl := lg_18
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.757200775059590616 41.75720079673011951 2.2250964 0.00000004648 (-0.6086040186664) 0.7934741006803 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_19 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1264695397653:ℝ):ℂ) + ((0.9919704912504:ℝ):ℂ) * I)‖ ≤ 0.00000012952 := by
  have hl := lg_19
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.538309920751253541 42.538309942421796882 1.4439872 0.00000002951 0.1264695397653 0.9919704912504 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_20 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7629364804295:ℝ):ℂ) + ((0.6464734540798:ℝ):ℂ) * I)‖ ≤ 0.00000011966 := by
  have hl := lg_20
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.279344141012777423 43.27934416990679187 0.702953 0.00000001965 0.7629364804295 0.6464734540798 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_21 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999981596794:ℝ):ℂ) + (((-0.0019184988231):ℝ):ℂ) * I)‖ ≤ 0.00000011795 := by
  have hl := lg_21
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.984215646523986942 43.984215668194530283 (-0.0019185) 0.00000001794 0.9999981596794 (-0.0019184988231) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_22 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7813357019643:ℝ):ℂ) + (((-0.6241109843897):ℝ):ℂ) * I)‖ ≤ 0.00000014163 := by
  have hl := lg_22
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.656290308645846251 44.656290337539875145 (-0.6739932) 0.00000004162 0.7813357019643 (-0.6241109843897) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_23 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2518665750638:ℝ):ℂ) + (((-0.9677619688568):ℝ):ℂ) * I)‖ ≤ 0.00000012777 := by
  have hl := lg_23
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.298484922506670602 45.298484951400713943 (-1.3161878) 0.00000002776 0.2518665750638 (-0.9677619688568) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_24 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.352508358557):ℝ):ℂ) + (((-0.9358086648162):ℝ):ℂ) * I)‖ ≤ 0.00000015067 := by
  have hl := lg_24
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.913343672015045308 45.913343700909059755 (-1.9310465) 0.00000005066 (-0.352508358557) (-0.9358086648162) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_25 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8134187466041):ℝ):ℂ) + (((-0.5816785560929):ℝ):ℂ) * I)‖ ≤ 0.00000012342 := by
  have hl := lg_25
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.503099026849154846 46.50309905574318374 (-2.5208019) 0.00000002341 (-0.8134187466041) (-0.5816785560929) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_26 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9985332098503):ℝ):ℂ) + (((-0.0541426658183):ℝ):ℂ) * I)‖ ≤ 0.00000014843 := by
  have hl := lg_26
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.0697206697746199 47.069720698668648794 (-3.0874235) 0.00000004842 (-0.9985332098503) (-0.0541426658183) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_27 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8818309749843):ℝ):ℂ) + ((0.4715656173433:ℝ):ℂ) * I)‖ ≤ 0.00000015615 := by
  have hl := lg_27
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.614955191898235924 47.614955213568779265 2.6505273 0.00000005614 (-0.8818309749843) 0.4715656173433 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_28 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5263716852863):ℝ):ℂ) + ((0.8502545788888:ℝ):ℂ) * I)‖ ≤ 0.00000011495 := by
  have hl := lg_28
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.140358543479441634 48.140358572373470528 2.1251239 0.00000001494 (-0.5263716852863) 0.8502545788888 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_29 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0473455670135):ℝ):ℂ) + ((0.9988785698391:ℝ):ℂ) * I)‖ ≤ 0.00000011666 := by
  have hl := lg_29
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.647322840792859324 48.647322869686902665 1.6181596 0.00000001665 (-0.0473455670135) 0.9988785698391 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_30 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4281208706627:ℝ):ℂ) + ((0.9037214837012:ℝ):ℂ) * I)‖ ≤ 0.00000012932 := by
  have hl := lg_30
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.137098557851422731 49.137098586745451625 1.1283839 0.00000002931 0.4281208706627 0.9037214837012 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_31 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7932493336949:ℝ):ℂ) + ((0.6088969490748:ℝ):ℂ) * I)‖ ≤ 0.00000012928 := by
  have hl := lg_31
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.610813128175159261 49.610813157069202602 0.6546693 0.00000002927 0.7932493336949 0.6088969490748 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_32 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9808542109796:ℝ):ℂ) + ((0.1947434640846:ℝ):ℂ) * I)‖ ≤ 0.00000014767 := by
  have hl := lg_32
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.0694865689705 50.069486605088 0.1959959 0.00000004766 0.9808542109796 0.1947434640846 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_33 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9692671128986:ℝ):ℂ) + (((-0.2460106986561):ℝ):ℂ) * I)‖ ≤ 0.00000013197 := by
  have hl := lg_33
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.514044725484491559 50.5140447543785349 (-0.2485623) 0.00000003196 0.9692671128986 (-0.2460106986561) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_34 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7776682863077:ℝ):ℂ) + (((-0.6286748257019):ℝ):ℂ) * I)‖ ≤ 0.00000015905 := by
  have hl := lg_34
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.945330480352521998 50.945330516470036445 (-0.679848) 0.00000005904 0.7776682863077 (-0.6286748257019) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_35 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4548157588644:ℝ):ℂ) + (((-0.8905855520323):ℝ):ℂ) * I)‖ ≤ 0.00000012814 := by
  have hl := lg_35
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.364113429315819057 51.364113458209862398 (-1.098631) 0.00000002813 0.4548157588644 (-0.8905855520323) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_36 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0651345829169:ℝ):ℂ) + (((-0.9978764884033):ℝ):ℂ) * I)‖ ≤ 0.00000016033 := by
  have hl := lg_36
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.771098088853690616 51.77109811774771951 (-1.5056156) 0.00000006032 0.0651345829169 (-0.9978764884033) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_37 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3246600374891):ℝ):ℂ) + (((-0.9458307777058):ℝ):ℂ) * I)‖ ≤ 0.00000014042 := by
  have hl := lg_37
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.166931068949373574 52.166931097843416915 (-1.9014486) 0.00000004041 (-0.3246600374891) (-0.9458307777058) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_38 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6563182178448):ℝ):ℂ) + (((-0.7544841926161):ℝ):ℂ) * I)‖ ≤ 0.00000012291 := by
  have hl := lg_38
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.552207234545353541 52.552207263439396882 (-2.2867248) 0.0000000229 (-0.6563182178448) (-0.7544841926161) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_39 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8871795387285):ℝ):ℂ) + (((-0.4614243881273):ℝ):ℂ) * I)‖ ≤ 0.00000015809 := by
  have hl := lg_39
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.927475086613265208 52.927475115507308549 (-2.6619926) 0.00000005808 (-0.8871795387285) (-0.4614243881273) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p447_40 : ‖exp (-((((((14447:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.99352794278):ℝ):ℂ) + (((-0.1135879679529):ℝ):ℂ) * I)‖ ≤ 0.0000001335 := by
  have hl := lg_40
  refine (ecis_approx ((((14447:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.293241454806877423 53.29324149092439187 (-3.027759) 0.00000003349 (-0.99352794278) (-0.1135879679529) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_2 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8096490281105):ℝ):ℂ) + ((0.5869143474363:ℝ):ℂ) * I)‖ ≤ 0.00000010566 := by
  have hl := lg_2
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.0520204087106 10.0520204159616 2.5143502 0.00000000565 (-0.8096490281105) 0.5869143474363 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_3 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9749918069067):ℝ):ℂ) + ((0.2222408067149:ℝ):ℂ) * I)‖ ≤ 0.00000011506 := by
  have hl := lg_3
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.932075406495194328 15.93207541374620883 2.9174805 0.00000001505 (-0.9749918069067) 0.2222408067149 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_4 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3110631043006:ℝ):ℂ) + (((-0.9503892597998):ℝ):ℂ) * I)‖ ≤ 0.0000001104 := by
  have hl := lg_4
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.1040408174212 20.1040408319232 (-1.2544849) 0.00000001039 0.3110631043006 (-0.9503892597998) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_5 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2200602881139):ℝ):ℂ) + ((0.9754862734012:ℝ):ℂ) * I)‖ ≤ 0.00000013015 := by
  have hl := lg_5
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.340068598579858918 23.34006861308187342 1.7926726 0.00000003014 (-0.2200602881139) 0.9754862734012 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_6 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6589648562444:ℝ):ℂ) + (((-0.7521737287587):ℝ):ℂ) * I)‖ ≤ 0.00000011353 := by
  have hl := lg_6
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.984095815205794328 25.98409582970780883 (-0.8513546) 0.00000001352 0.6589648562444 (-0.7521737287587) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_7 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9985018744477):ℝ):ℂ) + (((-0.0547175123838):ℝ):ℂ) * I)‖ ≤ 0.00000015467 := by
  have hl := lg_7
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.219588974060689844 28.219588988562718848 (-3.0868478) 0.00000005466 (-0.9985018744477) (-0.0547175123838) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_8 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3059451521725:ℝ):ℂ) + ((0.9520491394157:ℝ):ℂ) * I)‖ ≤ 0.000000112 := by
  have hl := lg_8
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.1560612261318 30.1560612478848 1.2598653 0.00000001199 0.3059451521725 0.9520491394157 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_9 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9012180506415:ℝ):ℂ) + (((-0.4333659252848):ℝ):ℂ) * I)‖ ≤ 0.00000012292 := by
  have hl := lg_9
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.864150812990388656 31.86415082749241766 (-0.4482243) 0.00000002291 0.9012180506415 (-0.4333659252848) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_10 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3943552846184):ℝ):ℂ) + (((-0.918958056437):ℝ):ℂ) * I)‖ ≤ 0.00000012862 := by
  have hl := lg_10
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.392089007290458918 33.39208902904347342 (-1.9761625) 0.00000002861 (-0.3943552846184) (-0.918958056437) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_11 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9765998082698):ℝ):ℂ) + ((0.2150646744194:ℝ):ℂ) * I)‖ ≤ 0.0000001135 := by
  have hl := lg_11
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.774277234812765566 34.77427725656579457 2.9248346 0.00000001349 (-0.9765998082698) 0.2150646744194 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_12 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0920687022293):ℝ):ℂ) + ((0.9957526570737:ℝ):ℂ) * I)‖ ≤ 0.00000011918 := by
  have hl := lg_12
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.036116223916394328 36.03611624566940883 1.6629956 0.00000001917 (-0.0920687022293) 0.9957526570737 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_13 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8765178566034:ℝ):ℂ) + ((0.4813693457786:ℝ):ℂ) * I)‖ ≤ 0.00000014929 := by
  have hl := lg_13
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.1968955705980134 37.196895592351042404 0.5022163 0.00000004928 0.8765178566034 0.4813693457786 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_14 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8405505656684:ℝ):ℂ) + (((-0.5417330953104):ℝ):ℂ) * I)‖ ≤ 0.00000016032 := by
  have hl := lg_14
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.271609382771289844 38.271609404524318848 (-0.5724976) 0.00000006031 0.8405505656684 (-0.5417330953104) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_15 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0022358713422):ℝ):ℂ) + (((-0.9999975004364):ℝ):ℂ) * I)‖ ≤ 0.00000013802 := by
  have hl := lg_15
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.272144005075053246 39.27214402682808225 (-1.5730322) 0.00000003801 (-0.0022358713422) (-0.9999975004364) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_16 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8064794902749):ℝ):ℂ) + (((-0.5912620668656):ℝ):ℂ) * I)‖ ≤ 0.00000012078 := by
  have hl := lg_16
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.2080816348424 40.2080816638464 (-2.5089698) 0.00000002077 (-0.8064794902749) (-0.5912620668656) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_17 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9697588663213):ℝ):ℂ) + ((0.2440650342036:ℝ):ℂ) * I)‖ ≤ 0.00000014985 := by
  have hl := lg_17
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.087259900424325868 41.08725992942834037 2.8950372 0.00000004984 (-0.9697588663213) 0.2440650342036 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_18 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4753216395751):ℝ):ℂ) + ((0.8798121043418:ℝ):ℂ) * I)‖ ≤ 0.00000012857 := by
  have hl := lg_18
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.916171221700988656 41.91617124345401766 2.0661259 0.00000002856 (-0.4753216395751) 0.8798121043418 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_19 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2847572903782:ℝ):ℂ) + ((0.9585996482247:ℝ):ℂ) * I)‖ ≤ 0.00000013607 := by
  have hl := lg_19
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.700254064562516706 42.700254086315560212 1.2820431 0.00000003606 0.2847572903782 0.9585996482247 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_20 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8586390409692:ℝ):ℂ) + ((0.5125807227388:ℝ):ℂ) * I)‖ ≤ 0.00000013427 := by
  have hl := lg_20
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.444109416001058918 43.44410944500507342 0.5381877 0.00000003426 0.8586390409692 0.5125807227388 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_21 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9856916281612:ℝ):ℂ) + (((-0.1685586371948):ℝ):ℂ) * I)‖ ≤ 0.00000015207 := by
  have hl := lg_21
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.151664380555884172 44.151664402308927678 (-0.1693672) 0.00000005206 0.9856916281612 (-0.1685586371948) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_22 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6644785479552:ℝ):ℂ) + (((-0.747307339257):ℝ):ℂ) * I)‖ ≤ 0.00000012229 := by
  have hl := lg_22
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.826297643523365566 44.82629767252739457 (-0.8440005) 0.00000002228 0.6644785479552 (-0.747307339257) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_23 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0820639367405:ℝ):ℂ) + (((-0.9966270668041):ℝ):ℂ) * I)‖ ≤ 0.00000014595 := by
  have hl := lg_23
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.470937104325585732 45.470937133329629238 (-1.48864) 0.00000004594 0.0820639367405 (-0.9966270668041) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_24 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5098781795073):ℝ):ℂ) + (((-0.8602466169975):ℝ):ℂ) * I)‖ ≤ 0.00000011765 := by
  have hl := lg_24
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.088136632626994328 46.08813666163100883 (-2.1058395) 0.00000001764 (-0.5098781795073) (-0.8602466169975) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_25 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9031469360724):ℝ):ℂ) + (((-0.4293315871713):ℝ):ℂ) * I)‖ ≤ 0.00000015311 := by
  have hl := lg_25
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.680137197159717836 46.68013722616374684 (-2.6978401) 0.0000000531 (-0.9031469360724) (-0.4293315871713) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_26 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9921944060059):ℝ):ℂ) + ((0.1247006826668:ℝ):ℂ) * I)‖ ≤ 0.00000015089 := by
  have hl := lg_26
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.2489159793086134 47.248916008312642404 3.0165665 0.00000005088 (-0.9921944060059) 0.1247006826668 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_27 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7823686228078):ℝ):ℂ) + ((0.6228156533059:ℝ):ℂ) * I)‖ ≤ 0.00000013797 := by
  have hl := lg_27
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.796226219485582984 47.79622624123862649 2.4692562 0.00000003796 (-0.7823686228078) 0.6228156533059 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_28 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3626001156405):ℝ):ℂ) + ((0.9319448246194:ℝ):ℂ) * I)‖ ≤ 0.00000016306 := by
  have hl := lg_28
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.323629791481889844 48.323629820485918848 1.9418527 0.00000006305 (-0.3626001156405) 0.9319448246194 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_29 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1374019697398:ℝ):ℂ) + ((0.9905153702551:ℝ):ℂ) * I)‖ ≤ 0.00000014607 := by
  have hl := lg_29
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.832524111384927384 48.83252414038897089 1.4329583 0.00000004606 0.1374019697398 0.9905153702551 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_30 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5887231514955:ℝ):ℂ) + ((0.8083347393829:ℝ):ℂ) * I)‖ ≤ 0.00000014367 := by
  have hl := lg_30
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.324164413785653246 49.32416444278968225 0.941318 0.00000004366 0.5887231514955 0.8083347393829 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_31 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8934625413809:ℝ):ℂ) + ((0.4491377151266:ℝ):ℂ) * I)‖ ≤ 0.00000013309 := by
  have hl := lg_31
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.799682424364654226 49.799682453368697732 0.4658 0.00000003308 0.8934625413809 0.4491377151266 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_32 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999855256828:ℝ):ℂ) + ((0.0053803740408:ℝ):ℂ) * I)‖ ≤ 0.00000012239 := by
  have hl := lg_32
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.260102043553 50.260102079808 0.0053804 0.00000002238 0.9999855256828 0.0053803740408 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_33 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9043806681836:ℝ):ℂ) + (((-0.4267266185931):ℝ):ℂ) * I)‖ ≤ 0.00000011614 := by
  have hl := lg_33
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.706352641307959894 50.7063526703120034 (-0.4408702) 0.00000001613 0.9043806681836 (-0.4267266185931) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_34 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6419190588507:ℝ):ℂ) + (((-0.7667724055312):ℝ):ℂ) * I)‖ ≤ 0.00000014832 := by
  have hl := lg_34
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.139280309134925868 51.13928034538994037 (-0.8737979) 0.00000004831 0.6419190588507 (-0.7667724055312) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_35 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2731068889274:ℝ):ℂ) + (((-0.9619836938433):ℝ):ℂ) * I)‖ ≤ 0.00000014422 := by
  have hl := lg_35
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.559657572640548762 51.559657601644592268 (-1.2941751) 0.00000004421 0.2731068889274 (-0.9619836938433) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_36 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1315306364697):ℝ):ℂ) + (((-0.9913121060843):ℝ):ℂ) * I)‖ ≤ 0.00000012704 := by
  have hl := lg_36
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.968191630411588656 51.96819165941561766 (-1.7027092) 0.00000002703 (-0.1315306364697) (-0.9913121060843) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_37 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.504888487571):ℝ):ℂ) + (((-0.863184577661):ℝ):ℂ) * I)‖ ≤ 0.00000012567 := by
  have hl := lg_37
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.365531554087617884 52.36553158309166139 (-2.1000491) 0.00000002566 (-0.504888487571) (-0.863184577661) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_38 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7931693460425):ℝ):ℂ) + (((-0.609001139943):ℝ):ℂ) * I)‖ ≤ 0.00000014486 := by
  have hl := lg_38
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.752274473273116706 52.752274502277160212 (-2.486792) 0.00000004485 (-0.7931693460425) (-0.609001139943) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_39 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9615776386436):ℝ):ℂ) + (((-0.2745331393877):ℝ):ℂ) * I)‖ ≤ 0.00000014868 := by
  have hl := lg_39
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.128970977093207728 53.128971006097251234 (-2.8634885) 0.00000004867 (-0.9615776386436) (-0.2745331393877) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p502_40 : ‖exp (-((((((14502:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9960372452099):ℝ):ℂ) + ((0.0889370882079:ℝ):ℂ) * I)‖ ≤ 0.00000013992 := by
  have hl := lg_40
  refine (ecis_approx ((((14502:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.496129824711658918 53.49612986096667342 3.0525379 0.00000003991 (-0.9960372452099) 0.0889370882079 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_2 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7866911643661):ℝ):ℂ) + ((0.6173467517238:ℝ):ℂ) * I)‖ ≤ 0.00000011075 := by
  have hl := lg_2
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.0901435036271 10.0901435109056 2.4762271 0.00000001074 (-0.7866911643661) 0.6173467517238 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_3 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9597920474173):ℝ):ℂ) + ((0.280711997396:ℝ):ℂ) * I)‖ ≤ 0.0000001392 := by
  have hl := lg_3
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.992499082357643348 15.992499089636157905 2.8570568 0.00000003919 (-0.9597920474173) 0.280711997396 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_4 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2377659831843:ℝ):ℂ) + (((-0.9713224682053):ℝ):ℂ) * I)‖ ≤ 0.0000001143 := by
  have hl := lg_4
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.1802870072542 20.1802870218112 (-1.3307311) 0.00000001429 0.2377659831843 (-0.9713224682053) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_5 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1329622508602):ℝ):ℂ) + ((0.9911211025125:ℝ):ℂ) * I)‖ ≤ 0.000000145 := by
  have hl := lg_5
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.428587683735140413 23.42858769829215497 1.7041535 0.00000004499 (-0.1329622508602) 0.9911211025125 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_6 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.581763289405:ℝ):ℂ) + (((-0.8133581468828):ℝ):ℂ) * I)‖ ≤ 0.00000014275 := by
  have hl := lg_6
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.082642585984743348 26.082642600541757905 (-0.9499014) 0.00000004274 0.581763289405 (-0.8133581468828) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_7 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9986337037403):ℝ):ℂ) + ((0.0522563411054:ℝ):ℂ) * I)‖ ≤ 0.0000001109 := by
  have hl := lg_7
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.326614032230138054 28.326614046787167168 3.0893125 0.00000001089 (-0.9986337037403) 0.0522563411054 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_8 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4125943724871:ℝ):ℂ) + ((0.9109148608909:ℝ):ℂ) * I)‖ ≤ 0.00000012503 := by
  have hl := lg_8
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.2704305108813 30.2704305327168 1.145496 0.00000002502 0.4125943724871 0.9109148608909 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_9 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.842401606656:ℝ):ℂ) + (((-0.5388501954193):ℝ):ℂ) * I)‖ ≤ 0.00000014339 := by
  have hl := lg_9
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.984998164715286696 31.98499817927231581 (-0.5690716) 0.00000004338 0.842401606656 (-0.5388501954193) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_10 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5072651590914):ℝ):ℂ) + (((-0.8617900314841):ℝ):ℂ) * I)‖ ≤ 0.00000014855 := by
  have hl := lg_10
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.518731187362240413 33.51873120919775497 (-2.1028047) 0.00000004854 (-0.5072651590914) (-0.8617900314841) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_11 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9398374150553):ℝ):ℂ) + ((0.341622061763:ℝ):ℂ) * I)‖ ≤ 0.00000015355 := by
  have hl := lg_11
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.906161474773784881 34.906161496609313995 2.7929504 0.00000005354 (-0.9398374150553) 0.341622061763 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_12 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.044455970454:ℝ):ℂ) + ((0.9990113446257:ℝ):ℂ) * I)‖ ≤ 0.00000015348 := by
  have hl := lg_12
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.172786089611843348 36.172786111447357905 1.5263257 0.00000005347 0.044455970454 0.9990113446257 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_13 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9354932096221:ℝ):ℂ) + ((0.3533446684909:ℝ):ℂ) * I)‖ ≤ 0.00000015788 := by
  have hl := lg_13
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.3379677852155069 37.337967807051036014 0.361144 0.00000005787 0.9354932096221 0.3533446684909 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_14 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7533560335135:ℝ):ℂ) + (((-0.6576128699842):ℝ):ℂ) * I)‖ ≤ 0.00000011463 := by
  have hl := lg_14
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.416757535857238054 38.416757557692767168 (-0.7176457) 0.00000001462 0.7533560335135 (-0.6576128699842) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_15 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.150603367515):ℝ):ℂ) + (((-0.9885942674791):ℝ):ℂ) * I)‖ ≤ 0.00000014487 := by
  have hl := lg_15
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.421086766092783761 39.421086787928312875 (-1.7219749) 0.00000004486 (-0.150603367515) (-0.9885942674791) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_16 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.886934674452):ℝ):ℂ) + (((-0.4618948832278):ℝ):ℂ) * I)‖ ≤ 0.00000012858 := by
  have hl := lg_16
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.3605740145084 40.3605740436224 (-2.6614622) 0.00000002857 (-0.886934674452) (-0.4618948832278) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_17 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9201307271821):ℝ):ℂ) + ((0.3916113440035:ℝ):ℂ) * I)‖ ≤ 0.00000011598 := by
  have hl := lg_17
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.243086634290229738 41.243086663404244295 2.7392105 0.00000001597 (-0.9201307271821) 0.3916113440035 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_18 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3300524829902):ℝ):ℂ) + ((0.9439625831938:ℝ):ℂ) * I)‖ ≤ 0.00000013994 := by
  have hl := lg_18
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.075141668342386696 42.07514169017791581 1.9071555 0.00000003993 (-0.3300524829902) 0.9439625831938 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_19 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4355934242124:ℝ):ℂ) + ((0.9001435267683:ℝ):ℂ) * I)‖ ≤ 0.0000001419 := by
  have hl := lg_19
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.862198208373779871 42.862198230209323542 1.1200989 0.00000004189 0.4355934242124 0.9001435267683 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_20 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9310842952809:ℝ):ℂ) + ((0.3648041050772:ℝ):ℂ) * I)‖ ≤ 0.00000015928 := by
  have hl := lg_20
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.608874690989340413 43.60887472010335497 0.3734224 0.00000005927 0.9310842952809 0.3648041050772 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_21 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9438117078841:ℝ):ℂ) + (((-0.330483675937):ℝ):ℂ) * I)‖ ≤ 0.00000013568 := by
  have hl := lg_21
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.319113114587781402 44.319113136423325073 (-0.336816) 0.00000003567 0.9438117078841 (-0.330483675937) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_22 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.528462526303:ℝ):ℂ) + (((-0.8489566292181):ℝ):ℂ) * I)‖ ≤ 0.00000015727 := by
  have hl := lg_22
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.996304978400884881 44.996305007514913995 (-1.0140078) 0.00000005726 0.528462526303 (-0.8489566292181) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_23 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.090173220987):ℝ):ℂ) + (((-0.9959260967644):ℝ):ℂ) * I)‖ ≤ 0.00000016413 := by
  have hl := lg_23
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.643389286144500862 45.643389315258544533 (-1.6610922) 0.00000006412 (-0.090173220987) (-0.9959260967644) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_24 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6517095222774):ℝ):ℂ) + (((-0.7584686536409):ℝ):ℂ) * I)‖ ≤ 0.00000015703 := by
  have hl := lg_24
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.262929593238943348 46.262929622352957905 (-2.2806325) 0.00000005702 (-0.6517095222774) (-0.7584686536409) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_25 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9646420513491):ℝ):ℂ) + (((-0.263563488593):ℝ):ℂ) * I)‖ ≤ 0.00000014634 := by
  have hl := lg_25
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.857175367470280826 46.85717539658430994 (-2.8748782) 0.00000004633 (-0.9646420513491) (-0.263563488593) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_26 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9540804555602):ℝ):ℂ) + ((0.2995504700437:ℝ):ℂ) * I)‖ ≤ 0.00000016053 := by
  have hl := lg_26
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.4281112888426069 47.428111317956636014 2.8373712 0.00000006052 (-0.9540804555602) 0.2995504700437 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_27 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6572686481532):ℝ):ℂ) + ((0.7536563700635:ℝ):ℂ) * I)‖ ≤ 0.00000011149 := by
  have hl := lg_27
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.977497247072930044 47.977497268908473715 2.2879852 0.00000001148 (-0.6572686481532) 0.7536563700635 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_28 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1866833660007):ℝ):ℂ) + ((0.9824201345951:ℝ):ℂ) * I)‖ ≤ 0.00000011797 := by
  have hl := lg_28
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.506901039484338054 48.506901068598367168 1.7585814 0.00000001796 (-0.1866833660007) 0.9824201345951 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_29 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3174500450834:ℝ):ℂ) + ((0.9482749964417:ℝ):ℂ) * I)‖ ≤ 0.00000015367 := by
  have hl := lg_29
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.017725381976995444 49.017725411091039115 1.2477571 0.00000005366 0.3174500450834 0.9482749964417 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p557_30 : ‖exp (-((((((14557:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7287837983749:ℝ):ℂ) + ((0.6847438756399:ℝ):ℂ) * I)‖ ≤ 0.00000014141 := by
  have hl := lg_30
  refine (ecis_approx ((((14557:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.511230269719883761 49.511230298833912875 0.7542522 0.0000000414 0.7287837983749 0.6847438756399 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_2 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.754004892216):ℝ):ℂ) + ((0.6568688015727:ℝ):ℂ) * I)‖ ≤ 0.0000001194 := by
  have hl := lg_2
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.1414363949693 10.1414364022848 2.4249342 0.00000001939 (-0.754004892216) 0.6568688015727 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_3 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9338260433488):ℝ):ℂ) + ((0.3577274389767:ℝ):ℂ) * I)‖ ≤ 0.00000012985 := by
  have hl := lg_3
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.073796391699847484 16.073796399015362115 2.7757595 0.00000002984 (-0.9338260433488) 0.3577274389767 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_4 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1370467621011:ℝ):ℂ) + (((-0.9905645789132):ℝ):ℂ) * I)‖ ≤ 0.00000013162 := by
  have hl := lg_4
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.2828727899386 20.2828728045696 (-1.4333169) 0.00000003161 0.1370467621011 (-0.9905645789132) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_5 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0142582900453):ℝ):ℂ) + ((0.9998983454155:ℝ):ℂ) * I)‖ ≤ 0.00000013952 := by
  have hl := lg_5
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.547686089216791879 23.54768610384780651 1.5850551 0.00000003951 (-0.0142582900453) 0.9998983454155 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_6 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4691294173567:ℝ):ℂ) + (((-0.8831294297953):ℝ):ℂ) * I)‖ ≤ 0.00000014206 := by
  have hl := lg_6
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.215232786669147484 26.215232801300162115 (-1.0824916) 0.00000004205 0.4691294173567 (-0.8831294297953) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_7 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.980799321744):ℝ):ℂ) + ((0.1950197173034:ℝ):ℂ) * I)‖ ≤ 0.00000015269 := by
  have hl := lg_7
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.470611383221759282 28.470611397852788544 2.9453151 0.00000005268 (-0.980799321744) 0.1950197173034 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_8 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5473370387631:ℝ):ℂ) + ((0.8369122809459:ℝ):ℂ) * I)‖ ≤ 0.00000015101 := by
  have hl := lg_8
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.4243091849079 30.4243092068544 0.9916173 0.000000051 0.5473370387631 0.8369122809459 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_9 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7440621634774:ℝ):ℂ) + (((-0.6681103927356):ℝ):ℂ) * I)‖ ≤ 0.00000015251 := by
  have hl := lg_9
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.147592783399694968 32.14759279803072423 (-0.7316663) 0.0000000525 0.7440621634774 (-0.6681103927356) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_10 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6460512019367):ℝ):ℂ) + (((-0.7632940746919):ℝ):ℂ) * I)‖ ≤ 0.00000015173 := by
  have hl := lg_10
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.689122484186091879 33.68912250613260651 (-2.273196) 0.00000005172 (-0.6460512019367) (-0.7632940746919) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_11 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8647788361188):ℝ):ℂ) + ((0.5021529294121:ℝ):ℂ) * I)‖ ≤ 0.00000011819 := by
  have hl := lg_11
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.083605724903156323 35.083605746849685585 2.6155061 0.00000001818 (-0.8647788361188) 0.5021529294121 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_12 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2263741970243:ℝ):ℂ) + ((0.9740404113391:ℝ):ℂ) * I)‖ ≤ 0.00000016052 := by
  have hl := lg_12
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.356669181638447484 36.356669203584962115 1.3424427 0.00000006051 0.2263741970243 0.9740404113391 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_13 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9853575528757:ℝ):ℂ) + ((0.1705007125813:ℝ):ℂ) * I)‖ ≤ 0.00000011649 := by
  have hl := lg_13
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.5277740376099527 37.527774059556481962 0.1713378 0.00000001648 0.9853575528757 0.1705007125813 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_14 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6114252036978:ℝ):ℂ) + (((-0.7913022306825):ℝ):ℂ) * I)‖ ≤ 0.00000015708 := by
  have hl := lg_14
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.612047778191059282 38.612047800137588544 (-0.9129359) 0.00000005707 0.6114252036978 (-0.7913022306825) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_15 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3443762112282):ℝ):ℂ) + (((-0.9388317341983):ℝ):ℂ) * I)‖ ≤ 0.0000001598 := by
  have hl := lg_15
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.621482480916639363 39.621482502863168625 (-1.9223706) 0.00000005979 (-0.3443762112282) (-0.9388317341983) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_16 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9624363699045):ℝ):ℂ) + (((-0.271507336261):ℝ):ℂ) * I)‖ ≤ 0.00000016322 := by
  have hl := lg_16
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.5657455798772 40.5657456091392 (-2.8666338) 0.00000006321 (-0.9624363699045) (-0.271507336261) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_17 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8184776901664):ℝ):ℂ) + ((0.5745383108575:ℝ):ℂ) * I)‖ ≤ 0.0000001286 := by
  have hl := lg_17
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.452744421673445854 41.452744450935460485 2.5295527 0.00000002859 (-0.8184776901664) 0.5745383108575 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_18 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1221657376226):ℝ):ℂ) + ((0.9925097140837:ℝ):ℂ) * I)‖ ≤ 0.00000015007 := by
  have hl := lg_18
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.289029178368994968 42.28902920031552423 1.693268 0.00000005006 (-0.1221657376226) 0.9925097140837 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_19 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.619876985328:ℝ):ℂ) + ((0.7846990015673:ℝ):ℂ) * I)‖ ≤ 0.0000001575 := by
  have hl := lg_19
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.080086692774388493 43.080086714720932386 0.9022104 0.00000005749 0.619876985328 0.7846990015673 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_20 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9885098158833:ℝ):ℂ) + ((0.1511566865952:ℝ):ℂ) * I)‖ ≤ 0.00000015818 := by
  have hl := lg_20
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 43.830558879155391879 43.83055890841740651 0.1517383 0.00000005817 0.9885098158833 0.1511566865952 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_21 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8461321031521:ℝ):ℂ) + (((-0.5329732301114):ℝ):ℂ) * I)‖ ≤ 0.00000014663 := by
  have hl := lg_21
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.544407774921606766 44.544407796868150659 (-0.5621106) 0.00000004662 0.8461321031521 (-0.5329732301114) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_22 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3221988869474:ℝ):ℂ) + (((-0.9466720008799):ℝ):ℂ) * I)‖ ≤ 0.0000001304 := by
  have hl := lg_22
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.225042119872456323 45.225042149134485585 (-1.242745) 0.00000003039 0.3221988869474 (-0.9466720008799) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_23 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3167701892409):ℝ):ℂ) + (((-0.9485023179763):ℝ):ℂ) * I)‖ ≤ 0.00000013707 := by
  have hl := lg_23
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.875415858046313946 45.875415887308357839 (-1.8931187) 0.00000003706 (-0.3167701892409) (-0.9485023179763) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_24 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8105040055113):ℝ):ℂ) + (((-0.58573309365):ℝ):ℂ) * I)‖ ≤ 0.00000015563 := by
  have hl := lg_24
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.498105576607747484 46.498105605869762115 (-2.5158084) 0.00000005562 (-0.8105040055113) (-0.58573309365) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_25 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9995933989718):ℝ):ℂ) + (((-0.0285137881057):ℝ):ℂ) * I)‖ ≤ 0.00000015745 := by
  have hl := lg_25
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 47.095372178433583758 47.09537220769561302 (-3.113075) 0.00000005744 (-0.9995933989718) (-0.0285137881057) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_26 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8549610141808):ℝ):ℂ) + ((0.5186922634413:ℝ):ℂ) * I)‖ ≤ 0.00000012487 := by
  have hl := lg_26
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.6692104325792527 47.669210461841281962 2.596272 0.00000002486 (-0.8549610141808) 0.5186922634413 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_27 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4558232953684):ℝ):ℂ) + ((0.8900702912663:ℝ):ℂ) * I)‖ ≤ 0.00000013962 := by
  have hl := lg_27
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.221389175099542452 48.221389197046086345 2.0440933 0.00000003961 (-0.4558232953684) 0.8900702912663 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_28 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0587641531498:ℝ):ℂ) + ((0.998271893977:ℝ):ℂ) * I)‖ ≤ 0.000000145 := by
  have hl := lg_28
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.753484173160359282 48.753484202422388544 1.5119983 0.00000004499 0.0587641531498 0.998271893977 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_29 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5414990034983:ℝ):ℂ) + ((0.8407013912266:ℝ):ℂ) * I)‖ ≤ 0.00000014516 := by
  have hl := lg_29
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.266905273319050652 49.266905302581094545 0.9985772 0.00000004515 0.5414990034983 0.8407013912266 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p631_30 : ‖exp (-((((((14631:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8763506241714:ℝ):ℂ) + ((0.4816737313934:ℝ):ℂ) * I)‖ ≤ 0.00000014773 := by
  have hl := lg_30
  refine (ecis_approx ((((14631:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.762918875885939363 49.762918905147968625 0.5025636 0.00000004772 0.8763506241714 0.4816737313934 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_2 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7193352970492):ℝ):ℂ) + ((0.694663033702:ℝ):ℂ) * I)‖ ≤ 0.00000012806 := by
  have hl := lg_2
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.1927292863115 10.192729293664 2.3736413 0.00000002805 (-0.7193352970492) 0.694663033702 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_3 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.90169154712):ℝ):ℂ) + ((0.4323798720269:ℝ):ℂ) * I)‖ ≤ 0.00000012051 := by
  have hl := lg_3
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.15509370104205162 16.155093708394566325 2.6944622 0.0000000205 (-0.90169154712) 0.4323798720269 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_4 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0348865463484:ℝ):ℂ) + (((-0.9993912791713):ℝ):ℂ) * I)‖ ≤ 0.00000014893 := by
  have hl := lg_4
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.385458572623 20.385458587328 (-1.5359027) 0.00000004892 0.0348865463484 (-0.9993912791713) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_5 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.104647677522:ℝ):ℂ) + ((0.994509358221:ℝ):ℂ) * I)‖ ≤ 0.00000013403 := by
  have hl := lg_5
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.666784494698443345 23.66678450940345805 1.4659567 0.00000003402 0.104647677522 0.994509358221 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_6 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3482602499883:ℝ):ℂ) + (((-0.9373978868539):ℝ):ℂ) * I)‖ ≤ 0.00000014138 := by
  have hl := lg_6
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.34782298735355162 26.347823002058566325 (-1.2150818) 0.00000004137 0.3482602499883 (-0.9373978868539) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_7 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9426629697311):ℝ):ℂ) + ((0.3337461989483:ℝ):ℂ) * I)‖ ≤ 0.00000011304 := by
  have hl := lg_7
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.61460873421338051 28.61460874891840992 2.8013178 0.00000001303 (-0.9426629697311) 0.3337461989483 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_8 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.669144979366:ℝ):ℂ) + ((0.7431318837119:ℝ):ℂ) * I)‖ ≤ 0.00000014511 := by
  have hl := lg_8
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.5781878589345 30.578187880992 0.8377387 0.0000000451 0.669144979366 0.7431318837119 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_9 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6260952980198:ℝ):ℂ) + (((-0.7797465471533):ℝ):ℂ) * I)‖ ≤ 0.00000013383 := by
  have hl := lg_9
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.31018740208410324 32.31018741678913265 (-0.8942609) 0.00000003382 0.6260952980198 (-0.7797465471533) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_10 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7661256514173):ℝ):ℂ) + (((-0.6426908169582):ℝ):ℂ) * I)‖ ≤ 0.0000001549 := by
  have hl := lg_10
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.859513781009943345 33.85951380306745805 (-2.4435873) 0.00000005489 (-0.7661256514173) (-0.6426908169582) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v14p705_11 : ‖exp (-((((((14705:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7625628507511):ℝ):ℂ) + ((0.6469141354285:ℝ):ℂ) * I)‖ ≤ 0.00000015403 := by
  have hl := lg_11
  refine (ecis_approx ((((14705:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.261049975032527765 35.261049997090057175 2.4380619 0.00000005402 (-0.7625628507511) 0.6469141354285 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
