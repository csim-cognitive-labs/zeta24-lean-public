/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b1left (b1), angles 15

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

lemma cs_b1left_v25p347_38 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4574157011621):ℝ):ℂ) + ((0.8892529878081:ℝ):ℂ) * I)‖ ≤ 0.00000014348 := by
  have hl := lg_38
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.201896364229326241 92.201896414923402282 2.0458832 0.00000004347 (-0.4574157011621) 0.8892529878081 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_39 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1822887737243:ℝ):ℂ) + ((0.9832450370961:ℝ):ℂ) * I)‖ ≤ 0.00000016111 := by
  have hl := lg_39
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.860297018092782808 92.860297068786858849 1.3874826 0.0000000611 0.1822887737243 0.9832450370961 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_40 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7345777919279:ℝ):ℂ) + ((0.6785244782661:ℝ):ℂ) * I)‖ ≤ 0.00000014617 := by
  have hl := lg_40
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.502027490481755523 93.50202755384928087 0.7457521 0.00000004616 0.7345777919279 0.6785244782661 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_41 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9928243813833:ℝ):ℂ) + ((0.1195815526362:ℝ):ℂ) * I)‖ ≤ 0.0000001659 := by
  have hl := lg_41
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.12791114180988926 94.127911205177439954 0.1198684 0.00000006589 0.9928243813833 0.1195815526362 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_42 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8818937578485:ℝ):ℂ) + (((-0.4714481942566):ℝ):ℂ) * I)‖ ≤ 0.00000013129 := by
  have hl := lg_42
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.738711788273174342 94.738711838967250383 (-0.4909322) 0.00000003128 0.8818937578485 (-0.4714481942566) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_43 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4648247131633:ℝ):ℂ) + (((-0.8854027253362):ℝ):ℂ) * I)‖ ≤ 0.00000014914 := by
  have hl := lg_43
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.33513930612936166 95.335139356823463048 (-1.0873597) 0.00000004913 0.4648247131633 (-0.8854027253362) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_44 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0991156675714):ℝ):ℂ) + (((-0.9950759189335):ℝ):ℂ) * I)‖ ≤ 0.00000017367 := by
  have hl := lg_44
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.917854617981955951 95.917854681349506645 (-1.670075) 0.00000007366 (-0.0991156675714) (-0.9950759189335) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_45 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6201219745508):ℝ):ℂ) + (((-0.7845054089459):ℝ):ℂ) * I)‖ ≤ 0.00000014487 := by
  have hl := lg_45
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.487474101852921339 96.48747415254699738 (-2.2396945) 0.00000004486 (-0.6201219745508) (-0.7845054089459) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_46 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.941143494354):ℝ):ℂ) + (((-0.3380072822488):ℝ):ℂ) * I)‖ ≤ 0.00000016384 := by
  have hl := lg_46
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 97.044573443864860002 97.044573507232436043 (-2.7967939) 0.00000006383 (-0.941143494354) (-0.3380072822488) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_47 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9800031615614):ℝ):ℂ) + ((0.1989819162771:ℝ):ℂ) * I)‖ ≤ 0.00000017611 := by
  have hl := lg_47
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.589691227600609163 97.589691290968210551 2.9412737 0.0000000761 (-0.9800031615614) 0.1989819162771 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_48 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7425279277805):ℝ):ℂ) + ((0.6698151061554:ℝ):ℂ) * I)‖ ≤ 0.00000013905 := by
  have hl := lg_48
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.123331990538132908 98.123332053905658255 2.4076329 0.00000003904 (-0.7425279277805) 0.6698151061554 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_49 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3090552340593):ℝ):ℂ) + ((0.9510440906176:ℝ):ℂ) * I)‖ ≤ 0.00000014503 := by
  have hl := lg_49
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.645969069854682868 98.645969120548784256 1.8849958 0.00000004502 (-0.3090552340593) 0.9510440906176 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_50 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1965897003003:ℝ):ℂ) + ((0.9804858437202:ℝ):ℂ) * I)‖ ≤ 0.00000013415 := by
  have hl := lg_50
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.158047085643011046 99.15804714901056174 1.3729178 0.00000003414 0.1965897003003 0.9804858437202 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_51 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6440767363795:ℝ):ℂ) + ((0.7649608863561:ℝ):ℂ) * I)‖ ≤ 0.00000013517 := by
  have hl := lg_51
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.659984279719285506 99.6599843430868362 0.8709806 0.00000003516 0.6440767363795 0.7649608863561 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_52 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9291126214874:ℝ):ℂ) + ((0.3697968855909:ℝ):ℂ) * I)‖ ≤ 0.00000015045 := by
  have hl := lg_52
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.1521745019392499 100.152174565306800594 0.3787904 0.00000005044 0.9291126214874 0.3697968855909 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_53 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9945943600969:ℝ):ℂ) + (((-0.1038366932422):ℝ):ℂ) * I)‖ ≤ 0.00000014837 := by
  have hl := lg_53
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.634989099861430718 100.634989163229006759 (-0.1040242) 0.00000004836 0.9945943600969 (-0.1038366932422) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_54 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8376587945874:ℝ):ℂ) + (((-0.5461938702059):ℝ):ℂ) * I)‖ ≤ 0.00000013774 := by
  have hl := lg_54
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.108778601909298724 101.108778652603374765 (-0.5778137) 0.00000003773 0.8376587945874 (-0.5461938702059) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_55 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5037091258245:ℝ):ℂ) + (((-0.8638733220566):ℝ):ℂ) * I)‖ ≤ 0.00000016165 := by
  have hl := lg_55
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.573874213143211474 101.573874276510787515 (-1.0429093) 0.00000006164 0.5037091258245 (-0.8638733220566) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_56 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0711118557862:ℝ):ℂ) + (((-0.9974683473507):ℝ):ℂ) * I)‖ ≤ 0.00000014277 := by
  have hl := lg_56
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.030589272119641434 102.030589335487192128 (-1.4996244) 0.00000004276 0.0711118557862 (-0.9974683473507) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_57 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3685597916291):ℝ):ℂ) + (((-0.9296040447371):ℝ):ℂ) * I)‖ ≤ 0.00000015544 := by
  have hl := lg_57
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.479220459446959149 102.479220510141060537 (-1.9482556) 0.00000005543 (-0.3685597916291) (-0.9296040447371) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_58 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7299766411046):ℝ):ℂ) + (((-0.6834720940992):ℝ):ℂ) * I)‖ ≤ 0.00000015951 := by
  have hl := lg_58
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.920048955375902124 102.920049018743478165 (-2.3890841) 0.0000000595 (-0.7299766411046) (-0.6834720940992) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_59 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9494817610069):ℝ):ℂ) + (((-0.313822219279):ℝ):ℂ) * I)‖ ≤ 0.00000015715 := by
  have hl := lg_59
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.353341557734079224 103.353341621101680612 (-2.8223767) 0.00000005714 (-0.9494817610069) (-0.313822219279) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p347_60 : ‖exp (-((((((25347:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9943029325116):ℝ):ℂ) + ((0.1065911719373:ℝ):ℂ) * I)‖ ≤ 0.00000013637 := by
  have hl := lg_60
  refine (ecis_approx ((((25347:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 103.779351585699388431 103.779351649066939125 3.0347986 0.00000003636 (-0.9943029325116) 0.1065911719373 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_2 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3226852444713:ℝ):ℂ) + ((0.9465063301428:ℝ):ℂ) * I)‖ ≤ 0.00000014757 := by
  have hl := lg_2
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.6073246739806 17.6073246866816 1.2422312 0.00000004756 0.3226852444713 0.9465063301428 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_3 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9332699414373):ℝ):ℂ) + (((-0.3591757456232):ℝ):ℂ) * I)‖ ≤ 0.00000013414 := by
  have hl := lg_3
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.906949350144181928 27.90694936284520733 (-2.7742081) 0.00000003413 (-0.9332699414373) (-0.3591757456232) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_4 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7917485270765):ℝ):ℂ) + ((0.6108471738708:ℝ):ℂ) * I)‖ ≤ 0.0000001303 := by
  have hl := lg_4
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.2146493479612 35.2146493733632 2.4844625 0.00000003029 (-0.7917485270765) 0.6108471738708 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_5 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9991081352991):ℝ):ℂ) + ((0.0422247959105:ℝ):ℂ) * I)‖ ≤ 0.0000001136 := by
  have hl := lg_5
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.882941838444737018 40.88294186384676242 3.0993553 0.00000001359 (-0.9991081352991) 0.0422247959105 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_6 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0388096777205:ℝ):ℂ) + (((-0.9992466206673):ℝ):ℂ) * I)‖ ≤ 0.00000012615 := by
  have hl := lg_6
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.514274024124781928 45.51427404952680733 (-1.5319769) 0.00000002614 0.0388096777205 (-0.9992466206673) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_7 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6708270485033:ℝ):ℂ) + ((0.7416138287521:ℝ):ℂ) * I)‖ ≤ 0.00000016108 := by
  have hl := lg_7
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.430009593096789644 49.430009618498840448 0.8354729 0.00000006107 0.6708270485033 0.7416138287521 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_8 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8336562798855):ℝ):ℂ) + (((-0.552283629074):ℝ):ℂ) * I)‖ ≤ 0.00000013551 := by
  have hl := lg_8
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.8219740219418 52.8219740600448 (-2.5564916) 0.0000000355 (-0.8336562798855) (-0.552283629074) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_9 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7419855721999:ℝ):ℂ) + ((0.6704158490424:ℝ):ℂ) * I)‖ ≤ 0.00000016109 := by
  have hl := lg_9
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.813898700288363856 55.81389872569041466 0.7347691 0.00000006108 0.7419855721999 0.6704158490424 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_10 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3623634831645):ℝ):ℂ) + (((-0.9320368587488):ℝ):ℂ) * I)‖ ≤ 0.00000015221 := by
  have hl := lg_10
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.490266512425337018 58.49026655052836242 (-1.9415988) 0.0000000522 (-0.3623634831645) (-0.9320368587488) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_11 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3426357779002):ℝ):ℂ) + ((0.9394683196896:ℝ):ℂ) * I)‖ ≤ 0.00000016614 := by
  have hl := lg_11
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.911335699814775266 60.91133573791782607 1.9205174 0.00000006613 (-0.3426357779002) 0.9394683196896 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_12 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9583165907495:ℝ):ℂ) + (((-0.2857084386122):ℝ):ℂ) * I)‖ ≤ 0.00000016443 := by
  have hl := lg_12
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.121598698105381928 63.12159873620840733 (-0.2897456) 0.00000006442 0.9583165907495 (-0.2857084386122) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_13 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6832425700042):ℝ):ℂ) + (((-0.7301914752398):ℝ):ℂ) * I)‖ ≤ 0.00000012475 := by
  have hl := lg_13
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.1548435584285434 65.154843596531594204 (-2.3229905) 0.00000002474 (-0.6832425700042) (-0.7301914752398) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_14 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.485476193291):ℝ):ℂ) + ((0.8742498874704:ℝ):ℂ) * I)‖ ≤ 0.00000012622 := by
  have hl := lg_14
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.037334267077389644 67.037334305180440448 2.0777041 0.00000002621 (-0.485476193291) 0.8742498874704 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_15 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9476037138949:ℝ):ℂ) + ((0.3194482765841:ℝ):ℂ) * I)‖ ≤ 0.00000014773 := by
  have hl := lg_15
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.789891188588918946 68.78989122669196975 0.3251472 0.00000004772 0.9476037138949 0.3194482765841 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_16 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2537314672294:ℝ):ℂ) + (((-0.9672746985927):ℝ):ℂ) * I)‖ ≤ 0.00000016777 := by
  have hl := lg_16
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.4292986959224 70.4292987467264 (-1.3142603) 0.00000006776 0.2537314672294 (-0.9672746985927) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_17 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9589995151207):ℝ):ℂ) + (((-0.2834077094372):ℝ):ℂ) * I)‖ ≤ 0.00000013969 := by
  have hl := lg_17
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.969285339303456468 71.96928539010748187 (-2.854247) 0.00000003968 (-0.9589995151207) (-0.2834077094372) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_18 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3951250491873):ℝ):ℂ) + ((0.9186273431058:ℝ):ℂ) * I)‖ ≤ 0.00000012623 := by
  have hl := lg_18
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.421223374268963856 73.42122341237201466 1.9770003 0.00000002622 (-0.3951250491873) 0.9186273431058 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_19 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.823306242564:ℝ):ℂ) + ((0.5675974197926:ℝ):ℂ) * I)‖ ≤ 0.00000015719 := by
  have hl := lg_19
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.794638928976489406 74.794638967079565612 0.6035847 0.00000005718 0.823306242564 0.5675974197926 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_20 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7652495019546:ℝ):ℂ) + (((-0.6437337957248):ℝ):ℂ) * I)‖ ≤ 0.00000015107 := by
  have hl := lg_20
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.097591186405937018 76.09759123720996242 (-0.6993675) 0.00000005106 0.7652495019546 (-0.6437337957248) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_21 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3596931136441):ℝ):ℂ) + (((-0.9330706639877):ℝ):ℂ) * I)‖ ≤ 0.00000014293 := by
  have hl := lg_21
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.336958943240971572 77.336958981344047778 (-1.9387353) 0.00000004292 (-0.3596931136441) (-0.9330706639877) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_22 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997762208481):ℝ):ℂ) + (((-0.0211543751953):ℝ):ℂ) * I)‖ ≤ 0.00000013846 := by
  have hl := lg_22
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.518660373795375266 78.51866042459942607 (-3.1204367) 0.00000003845 (-0.9997762208481) (-0.0211543751953) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_23 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4464450856118):ℝ):ℂ) + ((0.8948110334191:ℝ):ℂ) * I)‖ ≤ 0.00000014673 := by
  have hl := lg_23
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.647824046619675132 79.647824097423751338 2.0335849 0.00000004672 (-0.4464450856118) 0.8948110334191 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_24 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5796594690886:ℝ):ℂ) + ((0.8148588220642:ℝ):ℂ) * I)‖ ≤ 0.00000012957 := by
  have hl := lg_24
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.728923372085981928 80.72892342289000733 0.9524856 0.00000002956 0.5796594690886 0.8148588220642 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_25 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9964341337811:ℝ):ℂ) + (((-0.0843742676171):ℝ):ℂ) * I)‖ ≤ 0.00000013437 := by
  have hl := lg_25
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.765883676889474036 81.76588372769352484 (-0.0844747) 0.00000003436 0.9964341337811 (-0.0843742676171) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_26 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4706585578063:ℝ):ℂ) + (((-0.8823154322371):ℝ):ℂ) * I)‖ ≤ 0.00000016094 := by
  have hl := lg_26
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.7621682324091434 82.762168283213194204 (-1.0807593) 0.00000006093 0.4706585578063 (-0.8823154322371) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_27 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4516758082575):ℝ):ℂ) + (((-0.8921821362425):ℝ):ℂ) * I)‖ ≤ 0.00000014292 := by
  have hl := lg_27
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.720848050432545784 83.72084808853562199 (-2.0394391) 0.00000004291 (-0.4516758082575) (-0.8921821362425) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_28 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9841390553157):ℝ):ℂ) + (((-0.177398758308):ℝ):ℂ) * I)‖ ≤ 0.00000015229 := by
  have hl := lg_28
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.644658941057989644 84.644658991862040448 (-2.96325) 0.00000005228 (-0.9841390553157) (-0.177398758308) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_29 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7563721861097):ℝ):ℂ) + ((0.6541415107178:ℝ):ℂ) * I)‖ ≤ 0.00000015363 := by
  have hl := lg_29
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.536048646903870184 85.53604869770794639 2.4285456 0.00000005362 (-0.7563721861097) 0.6541415107178 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_30 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.00341792014:ℝ):ℂ) + ((0.9999941588938:ℝ):ℂ) * I)‖ ≤ 0.00000013796 := by
  have hl := lg_30
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.397215862569518946 86.39721591337356975 1.5673784 0.00000003795 0.00341792014 0.9999941588938 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_31 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.742198592884:ℝ):ℂ) + ((0.6701800121765:ℝ):ℂ) * I)‖ ≤ 0.00000015861 := by
  have hl := lg_31
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.230142941919110926 87.230142992723187132 0.7344513 0.0000000586 0.742198592884 0.6701800121765 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_32 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.997407025738:ℝ):ℂ) + (((-0.0719668326972):ℝ):ℂ) * I)‖ ≤ 0.00000013291 := by
  have hl := lg_32
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.036623369903 88.036623433408 (-0.0720291) 0.0000000329 0.997407025738 (-0.0719668326972) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_33 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6572058313193:ℝ):ℂ) + (((-0.7537111484381):ℝ):ℂ) * I)‖ ≤ 0.00000015057 := by
  have hl := lg_33
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.818285049958957194 88.8182851007630334 (-0.8536908) 0.00000005056 0.6572058313193 (-0.7537111484381) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_34 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0412077019919):ℝ):ℂ) + (((-0.9991506019096):ℝ):ℂ) * I)‖ ≤ 0.00000017629 := by
  have hl := lg_34
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.576610013284056468 89.57661007678908187 (-1.6120157) 0.00000007628 (-0.0412077019919) (-0.9991506019096) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_35 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7015433206341):ℝ):ℂ) + (((-0.7126268092415):ℝ):ℂ) * I)‖ ≤ 0.00000016899 := by
  have hl := lg_35
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.312951431541526662 90.312951482345602868 (-2.3483572) 0.00000006898 (-0.7015433206341) (-0.7126268092415) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_36 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9969876175897):ℝ):ℂ) + (((-0.0775608783825):ℝ):ℂ) * I)‖ ≤ 0.00000015228 := by
  have hl := lg_36
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 91.028548048249563856 91.02854809905361466 (-3.0639538) 0.00000005227 (-0.9969876175897) (-0.0775608783825) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_37 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8148361412114):ℝ):ℂ) + ((0.579691351428:ℝ):ℂ) * I)‖ ≤ 0.0000001337 := by
  have hl := lg_37
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.724536790576035684 91.72453684138011189 2.5232428 0.00000003369 (-0.8148361412114) 0.579691351428 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_38 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.271565870892):ℝ):ℂ) + ((0.9624198552426:ℝ):ℂ) * I)‖ ≤ 0.00000014608 := by
  have hl := lg_38
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.401963602957089406 92.401963653761165612 1.845816 0.00000004607 (-0.271565870892) 0.9624198552426 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_39 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.375382692355:ℝ):ℂ) + ((0.9268699122748:ℝ):ℂ) * I)‖ ≤ 0.0000001517 := by
  have hl := lg_39
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.061792908572725328 93.061792959376801534 1.1859867 0.00000005169 0.375382692355 0.9268699122748 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_40 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8562328352002:ℝ):ℂ) + ((0.5165901004907:ℝ):ℂ) * I)‖ ≤ 0.00000014732 := by
  have hl := lg_40
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.704915860386537018 93.70491592389156242 0.5428637 0.00000004731 0.8562328352002 0.5165901004907 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_41 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.996442288114:ℝ):ℂ) + (((-0.0842779120421):ℝ):ℂ) * I)‖ ≤ 0.00000016123 := by
  have hl := lg_41
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.33215760540714116 94.332157668912191964 (-0.084378) 0.00000006122 0.996442288114 (-0.0842779120421) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_42 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7670896937794:ℝ):ℂ) + (((-0.6415398675822):ℝ):ℂ) * I)‖ ≤ 0.00000016035 := by
  have hl := lg_42
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.944283617221571572 94.944283668025647778 (-0.696504) 0.00000006034 0.7670896937794 (-0.6415398675822) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_43 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2730582122029:ℝ):ℂ) + (((-0.9619975118204):ℝ):ℂ) * I)‖ ≤ 0.00000015556 := by
  have hl := lg_43
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.54200531243531956 95.542005363239421168 (-1.2942257) 0.00000005555 0.2730582122029 (-0.9619975118204) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_44 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3025902840386):ℝ):ℂ) + (((-0.9531207268776):ℝ):ℂ) * I)‖ ≤ 0.00000015993 := by
  have hl := lg_44
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.125985047775975266 96.12598511128102607 (-1.8782055) 0.00000005992 (-0.3025902840386) (-0.9531207268776) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_45 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7696320535084):ℝ):ℂ) + (((-0.6384876679885):ℝ):ℂ) * I)‖ ≤ 0.00000016898 := by
  have hl := lg_45
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.696840538733100874 96.69684058953717708 (-2.449061) 0.00000006897 (-0.7696320535084) (-0.6384876679885) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_46 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9910055344821):ℝ):ℂ) + (((-0.1338208885326):ℝ):ℂ) * I)‖ ≤ 0.00000017643 := by
  have hl := lg_46
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 97.255148720600275132 97.255148784105351338 (-3.0073691) 0.00000007642 (-0.9910055344821) (-0.1338208885326) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_47 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9162908720836):ℝ):ℂ) + ((0.4005134674375:ℝ):ℂ) * I)‖ ≤ 0.00000016927 := by
  have hl := lg_47
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.801449345623177258 97.801449409128278866 2.7295155 0.00000006926 (-0.9162908720836) 0.4005134674375 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_48 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5842214757629):ℝ):ℂ) + ((0.8115942750208:ℝ):ℂ) * I)‖ ≤ 0.00000016882 := by
  have hl := lg_48
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.336248046066581928 98.33624810957160733 2.1947168 0.00000006881 (-0.5842214757629) 0.8115942750208 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_49 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0999820424938):ℝ):ℂ) + ((0.99498924174:ℝ):ℂ) * I)‖ ≤ 0.00000012869 := by
  have hl := lg_49
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.860019186193579288 98.860019236997680896 1.6709457 0.00000002868 (-0.0999820424938) 0.99498924174 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p402_50 : ‖exp (-((((((25402:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4013953704595:ℝ):ℂ) + ((0.9159048840211:ℝ):ℂ) * I)‖ ≤ 0.00000016402 := by
  have hl := lg_50
  refine (ecis_approx ((((25402:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.373208350870074036 99.37320841437512484 1.1577565 0.00000006401 0.4013953704595 0.9159048840211 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_2 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3585257978189:ℝ):ℂ) + ((0.9335198189103:ℝ):ℂ) * I)‖ ≤ 0.00000015266 := by
  have hl := lg_2
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.6454477688971 17.6454477816256 1.2041081 0.00000005265 0.3585257978189 0.9335198189103 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_3 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9532562881731):ℝ):ℂ) + (((-0.3021629508166):ℝ):ℂ) * I)‖ ≤ 0.00000011003 := by
  have hl := lg_3
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.967373026006630948 27.967373038735156405 (-2.8346318) 0.00000001002 (-0.9532562881731) (-0.3021629508166) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_4 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7429185715295):ℝ):ℂ) + ((0.6693818013992:ℝ):ℂ) * I)‖ ≤ 0.00000012019 := by
  have hl := lg_4
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.2908955377942 35.2908955632512 2.4082163 0.00000002018 (-0.7429185715295) 0.6693818013992 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_5 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9914635476278):ℝ):ℂ) + ((0.1303841758097:ℝ):ℂ) * I)‖ ≤ 0.00000012667 := by
  have hl := lg_5
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 40.971460923600018513 40.97146094905704397 3.0108362 0.00000002666 (-0.9914635476278) 0.1303841758097 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_6 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0596918680406):ℝ):ℂ) + (((-0.9982168506339):ℝ):ℂ) * I)‖ ≤ 0.00000015537 := by
  have hl := lg_6
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.612820794903730948 45.612820820360756405 (-1.6305237) 0.00000005536 (-0.0596918680406) (-0.9982168506339) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_7 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7462086192932:ℝ):ℂ) + ((0.6657121724082:ℝ):ℂ) * I)‖ ≤ 0.0000001193 := by
  have hl := lg_7
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.537034651266237854 49.537034676723288768 0.7284478 0.00000001929 0.7462086192932 0.6657121724082 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_8 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8912366483283):ℝ):ℂ) + (((-0.4535385723063):ℝ):ℂ) * I)‖ ≤ 0.00000015076 := by
  have hl := lg_8
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.9363433066913 52.9363433448768 (-2.6708609) 0.00000005075 (-0.8912366483283) (-0.4535385723063) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_9 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.817395106311:ℝ):ℂ) + ((0.5760774602246:ℝ):ℂ) * I)‖ ≤ 0.00000011287 := by
  have hl := lg_9
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.934746052013261896 55.93474607747031281 0.6139217 0.00000001286 0.817395106311 0.5760774602246 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_10 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4771813776786):ℝ):ℂ) + (((-0.8788048320255):ℝ):ℂ) * I)‖ ≤ 0.00000016608 := by
  have hl := lg_10
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.616908692497118513 58.61690873068264397 (-2.0682409) 0.00000006607 (-0.4771813776786) (-0.8788048320255) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_11 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.216118026608):ℝ):ℂ) + ((0.9763672457503:ℝ):ℂ) * I)‖ ≤ 0.00000013204 := by
  have hl := lg_11
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.043219939775794581 61.043219977961345495 1.7886331 0.00000003203 (-0.216118026608) 0.9763672457503 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_12 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9104541803856:ℝ):ℂ) + (((-0.4136099435681):ℝ):ℂ) * I)‖ ≤ 0.00000013021 := by
  have hl := lg_12
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.258268563800830948 63.258268601986356405 (-0.4264155) 0.0000000302 0.9104541803856 (-0.4136099435681) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_13 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7791234930808):ℝ):ℂ) + (((-0.6268704670725):ℝ):ℂ) * I)‖ ≤ 0.00000013945 := by
  have hl := lg_13
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.2959157730460369 65.295915811231587814 (-2.4640627) 0.00000003944 (-0.7791234930808) (-0.6268704670725) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_14 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3539204660615):ℝ):ℂ) + ((0.935275522881:ℝ):ℂ) * I)‖ ≤ 0.00000015883 := by
  have hl := lg_14
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.182482420163337854 67.182482458348888768 1.9325559 0.00000005882 (-0.3539204660615) 0.935275522881 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_15 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9845161289028:ℝ):ℂ) + ((0.1752940156715:ℝ):ℂ) * I)‖ ≤ 0.00000012938 := by
  have hl := lg_15
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.938833949606649461 68.938833987792200375 0.1762044 0.00000002937 0.9845161289028 0.1752940156715 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_16 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1038560150032:ℝ):ℂ) + (((-0.994592342695):ℝ):ℂ) * I)‖ ≤ 0.00000014754 := by
  have hl := lg_16
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.5817910755884 70.5817911265024 (-1.4667527) 0.00000004753 0.1038560150032 (-0.994592342695) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_17 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9913638414824):ℝ):ℂ) + (((-0.1311401287891):ℝ):ℂ) * I)‖ ≤ 0.00000014512 := by
  have hl := lg_17
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.125112073169360338 72.125112124083385795 (-3.0100737) 0.00000004511 (-0.9913638414824) (-0.1311401287891) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_18 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2447224937238):ℝ):ℂ) + ((0.9695931626535:ℝ):ℂ) * I)‖ ≤ 0.00000016526 := by
  have hl := lg_18
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.580193820910361896 73.58019385909591281 1.8180298 0.00000006525 (-0.2447224937238) 0.9695931626535 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_19 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9040516496469:ℝ):ℂ) + ((0.4274232267563:ℝ):ℂ) * I)‖ ≤ 0.00000012483 := by
  have hl := lg_19
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.956583072787752571 74.956583110973328942 0.4416406 0.00000002482 0.9040516496469 0.4274232267563 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_20 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6492998935162:ℝ):ℂ) + (((-0.7605324768081):ℝ):ℂ) * I)‖ ≤ 0.00000012617 := by
  have hl := lg_20
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.262356461394218513 76.26235651230824397 (-0.8641328) 0.00000002616 0.6492998935162 (-0.7605324768081) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_21 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5101745042048):ℝ):ℂ) + (((-0.860070912921):ℝ):ℂ) * I)‖ ≤ 0.00000012932 := by
  have hl := lg_21
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.504407677272868802 77.504407715458445173 (-2.106184) 0.00000002931 (-0.5101745042048) (-0.860070912921) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_22 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9889420770148):ℝ):ℂ) + ((0.1483022855997:ℝ):ℂ) * I)‖ ≤ 0.00000016627 := by
  have hl := lg_22
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.688667708672894581 78.688667759586945495 2.9927413 0.00000006626 (-0.9889420770148) 0.1483022855997 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_23 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2862745364852):ℝ):ℂ) + ((0.958147634636:ℝ):ℂ) * I)‖ ≤ 0.00000016491 := by
  have hl := lg_23
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.820276228438590262 79.820276279352666633 1.8611327 0.0000000649 (-0.2862745364852) 0.958147634636 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_24 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7125343910195:ℝ):ℂ) + ((0.7016371865961:ℝ):ℂ) * I)‖ ≤ 0.00000016065 := by
  have hl := lg_24
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.903716332697930948 80.903716383611956405 0.7776926 0.00000006064 0.7125343910195 0.7016371865961 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_25 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9659999351474:ℝ):ℂ) + (((-0.2585423085209):ℝ):ℂ) * I)‖ ≤ 0.00000014615 := by
  have hl := lg_25
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.942921847200037026 81.94292189811408794 (-0.2615129) 0.00000004614 0.9659999351474 (-0.2585423085209) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_26 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3058601329646:ℝ):ℂ) + (((-0.9520764565217):ℝ):ℂ) * I)‖ ≤ 0.00000015141 := by
  have hl := lg_26
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.9413635419431369 82.941363592857187814 (-1.2599546) 0.0000000514 0.3058601329646 (-0.9520764565217) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_27 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6051177597309):ℝ):ℂ) + (((-0.7961359788665):ℝ):ℂ) * I)‖ ≤ 0.00000012289 := by
  have hl := lg_27
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.902119078019892844 83.902119116205469215 (-2.2207101) 0.00000002288 (-0.6051177597309) (-0.7961359788665) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_28 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999878543681):ℝ):ℂ) + ((0.0049285333367:ℝ):ℂ) * I)‖ ≤ 0.00000013948 := by
  have hl := lg_28
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 84.827930189060437854 84.827930239974488768 3.1366641 0.00000003947 (-0.9999878543681) 0.0049285333367 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_29 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6229812039288):ℝ):ℂ) + ((0.7822368052817:ℝ):ℂ) * I)‖ ≤ 0.00000016791 := by
  have hl := lg_29
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.721249917495938244 85.721249968410014615 2.2433444 0.0000000679 (-0.6229812039288) 0.7822368052817 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_30 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1893338946235:ℝ):ℂ) + ((0.9819127641225:ℝ):ℂ) * I)‖ ≤ 0.00000016892 := by
  have hl := lg_30
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.584281718503749461 86.584281769417800375 1.3803126 0.00000006891 0.1893338946235 0.9819127641225 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_31 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8548254266428:ℝ):ℂ) + ((0.5189156867593:ℝ):ℂ) * I)‖ ≤ 0.00000016242 := by
  have hl := lg_31
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.419012238108605891 87.419012289022682262 0.545582 0.00000006241 0.8548254266428 0.5189156867593 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_32 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9657067242796:ℝ):ℂ) + (((-0.2596353648508):ℝ):ℂ) * I)‖ ≤ 0.00000015604 := by
  have hl := lg_32
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.2272388444855 88.227238908128 (-0.2626446) 0.00000005603 0.9657067242796 (-0.2596353648508) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_33 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5010378760319:ℝ):ℂ) + (((-0.8654253559848):ℝ):ℂ) * I)‖ ≤ 0.00000013475 := by
  have hl := lg_33
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.010592965782425529 89.0105930166965019 (-1.0459987) 0.00000003474 0.5010378760319 (-0.8654253559848) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_34 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2330076027954):ℝ):ℂ) + (((-0.9724749133209):ℝ):ℂ) * I)‖ ≤ 0.00000015846 := by
  have hl := lg_34
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.770559842066460338 89.770559905708985795 (-1.8059656) 0.00000005845 (-0.2330076027954) (-0.9724749133209) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_35 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8266369741014):ℝ):ℂ) + (((-0.5627355622205):ℝ):ℂ) * I)‖ ≤ 0.00000012566 := by
  have hl := lg_35
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.508495574866256367 90.508495625780332738 (-2.5439013) 0.00000002565 (-0.8266369741014) (-0.5627355622205) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_36 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9928737726437):ℝ):ℂ) + ((0.1191707646785:ℝ):ℂ) * I)‖ ≤ 0.00000013304 := by
  have hl := lg_36
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.225641589807461896 91.22564164072151281 3.022138 0.00000003303 (-0.9928737726437) 0.1191707646785 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_37 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6844477676405):ℝ):ℂ) + ((0.729061899533:ℝ):ℂ) * I)‖ ≤ 0.00000013199 := by
  have hl := lg_37
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.923137275714279994 91.923137326628356365 2.3246423 0.00000003198 (-0.6844477676405) 0.729061899533 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_38 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0748822142805):ℝ):ℂ) + ((0.9971923856429:ℝ):ℂ) * I)‖ ≤ 0.00000016602 := by
  have hl := lg_38
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.602030841684852571 92.602030892598928942 1.6457487 0.00000006601 (-0.0748822142805) 0.9971923856429 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_39 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5532873449041:ℝ):ℂ) + ((0.8329904645126:ℝ):ℂ) * I)‖ ≤ 0.00000014229 := by
  have hl := lg_39
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.263288799052667848 93.263288849966744219 0.9844908 0.00000004228 0.5532873449041 0.8329904645126 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p457_40 : ‖exp (-((((((25457:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9427629023719:ℝ):ℂ) + ((0.3334638059988:ℝ):ℂ) * I)‖ ≤ 0.00000017742 := by
  have hl := lg_40
  refine (ecis_approx ((((25457:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.907804230291318513 93.90780429393384397 0.3399753 0.00000007741 0.9427629023719 0.3334638059988 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_2 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4059161211406:ℝ):ℂ) + ((0.9139103361918:ℝ):ℂ) * I)‖ ≤ 0.00000015148 := by
  have hl := lg_2
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.6967406602393 17.6967406730048 1.1528153 0.00000005147 0.4059161211406 0.9139103361918 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_3 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9746458493328):ℝ):ℂ) + (((-0.2237531409491):ℝ):ℂ) * I)‖ ≤ 0.00000011941 := by
  have hl := lg_3
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.048670335348835084 28.048670348114360615 (-2.9159291) 0.0000000194 (-0.9746458493328) (-0.2237531409491) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_4 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6704641309999):ℝ):ℂ) + ((0.7419419445099:ℝ):ℂ) * I)‖ ≤ 0.00000012261 := by
  have hl := lg_4
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.3934813204786 35.3934813460096 2.3056305 0.0000000226 (-0.6704641309999) 0.7419419445099 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_5 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9689483211975):ℝ):ℂ) + ((0.2472633223542:ℝ):ℂ) * I)‖ ≤ 0.00000012119 := by
  have hl := lg_5
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.090559329081669979 41.09055935461269551 2.8917378 0.00000002118 (-0.9689483211975) 0.2472633223542 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_6 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1911342524478):ℝ):ℂ) + (((-0.9815639039514):ℝ):ℂ) * I)‖ ≤ 0.00000015468 := by
  have hl := lg_6
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.745410995588135084 45.745411021119160615 (-1.7631139) 0.00000005467 (-0.1911342524478) (-0.9815639039514) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_7 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8340154487367:ℝ):ℂ) + ((0.5517410907922:ℝ):ℂ) * I)‖ ≤ 0.00000015519 := by
  have hl := lg_7
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.681032002257859082 49.681032027788910144 0.5844504 0.00000005518 0.8340154487367 0.5517410907922 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_8 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9502206090625):ℝ):ℂ) + (((-0.3115779098538):ℝ):ℂ) * I)‖ ≤ 0.00000016159 := by
  have hl := lg_8
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.0902219807179 53.0902220190144 (-2.8247395) 0.00000006158 (-0.9502206090625) (-0.3115779098538) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_9 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8998690668307:ℝ):ℂ) + ((0.4361601340806:ℝ):ℂ) * I)‖ ≤ 0.00000013163 := by
  have hl := lg_9
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.097340670697670168 56.09734069622872123 0.4513271 0.00000003162 0.8998690668307 0.4361601340806 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_10 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6192882447137):ℝ):ℂ) + (((-0.7851637217458):ℝ):ℂ) * I)‖ ≤ 0.00000016302 := by
  have hl := lg_10
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.787299989320969979 58.78730002761749551 (-2.2386322) 0.00000006301 (-0.6192882447137) (-0.7851637217458) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_11 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0403815902836):ℝ):ℂ) + ((0.9991843309249:ℝ):ℂ) * I)‖ ≤ 0.00000015642 := by
  have hl := lg_11
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.220664189905166023 61.220664228201717085 1.6111889 0.00000005641 (-0.0403815902836) 0.9991843309249 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_12 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8194769230837:ℝ):ℂ) + (((-0.573112181456):ℝ):ℂ) * I)‖ ≤ 0.00000012234 := by
  have hl := lg_12
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.442151655827435084 63.442151694123960615 (-0.6102986) 0.00000002233 0.8194769230837 (-0.573112181456) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_13 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.883401879194):ℝ):ℂ) + (((-0.4686161752833):ℝ):ℂ) * I)‖ ≤ 0.00000014637 := by
  have hl := lg_13
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.4857220254404827 65.485722063737033762 (-2.653869) 0.00000004636 (-0.883401879194) (-0.4686161752833) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_14 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1657015698543):ℝ):ℂ) + ((0.986175942592:ℝ):ℂ) * I)‖ ≤ 0.00000012183 := by
  have hl := lg_14
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.377772662497159082 67.377772700793710144 1.7372657 0.00000002182 (-0.1657015698543) 0.986175942592 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_15 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997074047719:ℝ):ℂ) + (((-0.0241889405343):ℝ):ℂ) * I)‖ ≤ 0.00000012377 := by
  have hl := lg_15
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.139229664430505063 69.139229702727056125 (-0.0241913) 0.00000002376 0.9997074047719 (-0.0241889405343) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_16 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1009556909361):ℝ):ℂ) + (((-0.9948909228992):ℝ):ℂ) * I)‖ ≤ 0.00000013803 := by
  have hl := lg_16
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.7869626409572 70.7869626920192 (-1.6719243) 0.00000003802 (-0.1009556909361) (-0.9948909228992) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_17 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9969487125291):ℝ):ℂ) + ((0.0780593624759:ℝ):ℂ) * I)‖ ≤ 0.00000012562 := by
  have hl := lg_17
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.334769860552576454 72.334769911614601985 3.0634538 0.00000002561 (-0.9969487125291) 0.0780593624759 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_18 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0333397936844):ℝ):ℂ) + ((0.9994440745519:ℝ):ℂ) * I)‖ ≤ 0.00000015523 := by
  have hl := lg_18
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.794081330936970168 73.79408136923352123 1.6041423 0.00000005522 (-0.0333397936844) 0.9994440745519 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_19 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9750717624249:ℝ):ℂ) + ((0.2218897431646:ℝ):ℂ) * I)‖ ≤ 0.00000012898 := by
  have hl := lg_19
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.174471557188361193 75.174471595484937786 0.2237521 0.00000002897 0.9750717624249 0.2218897431646 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_20 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4661900702824:ℝ):ℂ) + (((-0.8846845869405):ℝ):ℂ) * I)‖ ≤ 0.00000013661 := by
  have hl := lg_20
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.484040649560269979 76.48404070062229551 (-1.085817) 0.0000000366 0.4661900702824 (-0.8846845869405) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_21 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6894158933488):ℝ):ℂ) + (((-0.7243657404765):ℝ):ℂ) * I)‖ ≤ 0.00000014856 := by
  have hl := lg_21
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.729702337606694166 77.729702375903270759 (-2.3314787) 0.00000004855 (-0.6894158933488) (-0.7243657404765) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_22 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9295563893666):ℝ):ℂ) + ((0.3686799680332:ℝ):ℂ) * I)‖ ≤ 0.00000014321 := by
  have hl := lg_22
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.917404850144466023 78.917404901206517085 2.7640041 0.0000000432 (-0.9295563893666) 0.3686799680332 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_23 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.058276836159):ℝ):ℂ) + ((0.998300460967:ℝ):ℂ) * I)‖ ≤ 0.00000015808 := by
  have hl := lg_23
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.052302800340403346 80.052302851402479939 1.6291062 0.00000005807 (-0.058276836159) 0.998300460967 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_24 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8564120404124:ℝ):ℂ) + ((0.5162929566018:ℝ):ℂ) * I)‖ ≤ 0.00000017381 := by
  have hl := lg_24
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.138892316066735084 81.138892367128760615 0.5425167 0.0000000738 0.8564120404124 0.5162929566018 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_25 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8777217021435:ℝ):ℂ) + (((-0.4791707561885):ℝ):ℂ) * I)‖ ≤ 0.00000013519 := by
  have hl := lg_25
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.181118658163339958 82.18111870922539102 (-0.4997097) 0.00000003518 0.8777217021435 (-0.4791707561885) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_26 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0696861021256:ℝ):ℂ) + (((-0.9975689686284):ℝ):ℂ) * I)‖ ≤ 0.00000014342 := by
  have hl := lg_26
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.1824626856797827 83.182462736741833762 (-1.5010537) 0.00000004341 0.0696861021256 (-0.9975689686284) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_27 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7794614510054):ℝ):ℂ) + (((-0.626450194632):ℝ):ℂ) * I)‖ ≤ 0.00000015102 := by
  have hl := lg_27
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.146011006046505252 84.146011044343081845 (-2.464602) 0.00000005101 (-0.7794614510054) (-0.626450194632) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_28 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9685373256385):ℝ):ℂ) + ((0.2488683358321:ℝ):ℂ) * I)‖ ≤ 0.0000001733 := by
  have hl := lg_28
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.074513322736459082 85.074513373798510144 2.890081 0.00000007329 (-0.9685373256385) 0.2488683358321 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_29 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4108335760118):ℝ):ℂ) + ((0.9117103557698:ℝ):ℂ) * I)‖ ≤ 0.0000001594 := by
  have hl := lg_29
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.970429808837993452 85.970429859900070045 1.9941645 0.00000005939 (-0.4108335760118) 0.9117103557698 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_30 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4279038747964:ℝ):ℂ) + ((0.9038242494723:ℝ):ℂ) * I)‖ ≤ 0.00000017523 := by
  have hl := lg_30
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.835970324669805063 86.835970375731856125 1.128624 0.00000007522 0.4279038747964 0.9038242494723 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_31 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9578233526361:ℝ):ℂ) + ((0.2873576606687:ℝ):ℂ) * I)‖ ≤ 0.00000014173 := by
  have hl := lg_31
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.673127291163562753 87.673127342225639346 0.291467 0.00000004172 0.9578233526361 0.2873576606687 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_32 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8682615553493:ℝ):ℂ) + (((-0.4961067138251):ℝ):ℂ) * I)‖ ≤ 0.00000016452 := by
  have hl := lg_32
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.4837033011965 88.483703365024 (-0.519109) 0.00000006451 0.8682615553493 (-0.4961067138251) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_33 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.262928285461:ℝ):ℂ) + (((-0.9648153795958):ℝ):ℂ) * I)‖ ≤ 0.00000017528 := by
  have hl := lg_33
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.269334525254001107 89.2693345763160777 (-1.3047403) 0.00000007527 0.262928285461 (-0.9648153795958) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_34 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4760168945156):ℝ):ℂ) + (((-0.8794361353335):ℝ):ℂ) * I)‖ ≤ 0.00000017974 := by
  have hl := lg_34
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.031510520791876454 90.031510584619401985 (-2.0669163) 0.00000007973 (-0.4760168945156) (-0.8794361353335) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_35 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9445432018317):ℝ):ℂ) + (((-0.3283871795364):ℝ):ℂ) * I)‖ ≤ 0.00000016919 := by
  have hl := lg_35
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.771591331339529061 90.771591382401605654 (-2.8069971) 0.00000006918 (-0.9445432018317) (-0.3283871795364) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_36 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9269354298606):ℝ):ℂ) + ((0.3752208799027:ℝ):ℂ) * I)‖ ≤ 0.00000013456 := by
  have hl := lg_36
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.490821991176270168 91.49082204223832123 2.7569576 0.00000003455 (-0.9269354298606) 0.3752208799027 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_37 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4676568956454):ℝ):ℂ) + ((0.8839100791089:ℝ):ℂ) * I)‖ ≤ 0.00000014456 := by
  have hl := lg_37
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.190345201173008702 92.190345252235085295 2.0574344 0.00000004455 (-0.4676568956454) 0.8839100791089 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_38 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1930100178641:ℝ):ℂ) + ((0.9811967860751:ℝ):ℂ) * I)‖ ≤ 0.00000016081 := by
  have hl := lg_38
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.871212217427661193 92.871212268489737786 1.3765674 0.0000000608 0.1930100178641 0.9811967860751 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_39 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7561496384775:ℝ):ℂ) + ((0.6543987501748:ℝ):ℂ) * I)‖ ≤ 0.00000014692 := by
  have hl := lg_39
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.534392360789317784 93.534392411851394377 0.7133872 0.00000004691 0.7561496384775 0.6543987501748 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p531_40 : ‖exp (-((((((25531:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9977564533178:ℝ):ℂ) + ((0.0669481878973:ℝ):ℂ) * I)‖ ≤ 0.00000016595 := by
  have hl := lg_40
  refine (ecis_approx ((((25531:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.180781309799569979 94.18078137362709551 0.0669983 0.00000006594 0.9977564533178 0.0669481878973 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_2 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4676255639124:ℝ):ℂ) + ((0.8839266553146:ℝ):ℂ) * I)‖ ≤ 0.00000012238 := by
  have hl := lg_2
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.765362231089 17.765362243904 1.0841937 0.00000002237 0.4676255639124 0.8839266553146 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_3 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9931748612391):ℝ):ℂ) + (((-0.1166348770999):ℝ):ℂ) * I)‖ ≤ 0.00000013601 := by
  have hl := lg_3
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.15743295190124332 28.15743296471626895 (-3.0246917) 0.000000036 (-0.9931748612391) (-0.1166348770999) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_4 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5626526639507):ℝ):ℂ) + ((0.826693401292:ℝ):ℂ) * I)‖ ≤ 0.00000014475 := by
  have hl := lg_4
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.530724462178 35.530724487808 2.1683874 0.00000004474 (-0.5626526639507) 0.826693401292 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_5 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9174437321897):ℝ):ℂ) + ((0.3978655528275:ℝ):ℂ) * I)‖ ≤ 0.00000015775 := by
  have hl := lg_5
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.24989368236117667 41.2498937079912023 2.7324035 0.00000005774 (-0.9174437321897) 0.3978655528275 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_6 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3613372776487):ℝ):ℂ) + (((-0.9324351836878):ℝ):ℂ) * I)‖ ≤ 0.00000015838 := by
  have hl := lg_6
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.92279518299024332 45.92279520862026895 (-1.940498) 0.00000005837 (-0.3613372776487) (-0.9324351836878) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_7 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9242211988954:ℝ):ℂ) + ((0.3818575330045:ℝ):ℂ) * I)‖ ≤ 0.00000015049 := by
  have hl := lg_7
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.87367710696286586 49.87367713259291712 0.3918053 0.00000005048 0.9242211988954 0.3818575330045 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_8 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9938471125216):ℝ):ℂ) + (((-0.1107606269205):ℝ):ℂ) * I)‖ ≤ 0.00000016418 := by
  have hl := lg_8
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.296086693267 53.296086731712 (-3.0306043) 0.00000006417 (-0.9938471125216) (-0.1107606269205) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_9 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9727926356199:ℝ):ℂ) + ((0.2316775519631:ℝ):ℂ) * I)‖ ≤ 0.00000016083 := by
  have hl := lg_9
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.31486590380248664 56.3148659294325379 0.2338018 0.00000006082 0.9727926356199 0.2316775519631 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_10 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7807041680803):ℝ):ℂ) + (((-0.6249007936461):ℝ):ℂ) * I)‖ ≤ 0.00000015118 := by
  have hl := lg_10
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.01525591345017667 59.0152559518952023 (-2.4665882) 0.00000005117 (-0.7807041680803) (-0.6249007936461) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_11 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1957273851447:ℝ):ℂ) + ((0.9806583455538:ℝ):ℂ) * I)‖ ≤ 0.00000014998 := by
  have hl := lg_11
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.45805582183500079 61.45805586028005205 1.3737972 0.00000004997 0.1957273851447 0.9806583455538 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_12 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6552336894504:ℝ):ℂ) + (((-0.7554262453802):ℝ):ℂ) * I)‖ ≤ 0.00000015773 := by
  have hl := lg_12
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.68815741407924332 63.68815745252426895 (-0.8563044) 0.00000005772 0.6552336894504 (-0.7554262453802) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_13 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9727945228158):ℝ):ℂ) + (((-0.2316696270447):ℝ):ℂ) * I)‖ ≤ 0.00000016006 := by
  have hl := lg_13
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.739652011751971 65.73965205019702226 (-2.907799) 0.00000006005 (-0.9727945228158) (-0.2316696270447) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_14 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0946554073578:ℝ):ℂ) + ((0.9955100973159:ℝ):ℂ) * I)‖ ≤ 0.00000014094 := by
  have hl := lg_14
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.63903933805186586 67.63903937649691712 1.475999 0.00000004093 0.0946554073578 0.9955100973159 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_15 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9575870227738:ℝ):ℂ) + (((-0.2881442239836):ℝ):ℂ) * I)‖ ≤ 0.00000014473 := by
  have hl := lg_15
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.40732663426241999 69.40732667270747125 (-0.2922883) 0.00000004472 0.9575870227738 (-0.2881442239836) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_16 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3668440458464):ℝ):ℂ) + (((-0.9302824549697):ℝ):ℂ) * I)‖ ≤ 0.00000015463 := by
  have hl := lg_16
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.061448924356 71.061448975616 (-1.9464106) 0.00000005462 (-0.3668440458464) (-0.9302824549697) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_17 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9363796301369):ℝ):ℂ) + ((0.3509888717509:ℝ):ℂ) * I)‖ ≤ 0.00000014663 := by
  have hl := lg_17
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.61525798151120342 72.61525803277122905 2.7829657 0.00000004662 (-0.9363796301369) 0.3509888717509 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_18 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2501167411834:ℝ):ℂ) + ((0.9682156866008:ℝ):ℂ) * I)‖ ≤ 0.00000015128 := by
  have hl := lg_18
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.08022813489148664 74.0802281733365379 1.3179955 0.00000005127 0.2501167411834 0.9682156866008 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_19 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9977060292586:ℝ):ℂ) + (((-0.067695488632):ℝ):ℂ) * I)‖ ≤ 0.00000016835 := by
  have hl := lg_19
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.46597101604863489 75.46597105449371178 (-0.0677473) 0.00000006834 0.9977060292586 (-0.067695488632) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_20 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1872892416011:ℝ):ℂ) + (((-0.9823048101177):ℝ):ℂ) * I)‖ ≤ 0.00000014163 := by
  have hl := lg_20
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.78061814453917667 76.7806181957992023 (-1.3823945) 0.00000004162 0.1872892416011 (-0.9823048101177) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_21 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8733753546151):ℝ):ℂ) + (((-0.487047728524):ℝ):ℂ) * I)‖ ≤ 0.00000012731 := by
  have hl := lg_21
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.03111005886410918 78.03111009730918607 (-2.6328864) 0.0000000273 (-0.8733753546151) (-0.487047728524) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_22 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7753029225327):ℝ):ℂ) + ((0.6315895647265:ℝ):ℂ) * I)‖ ≤ 0.00000014043 := by
  have hl := lg_22
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.22341805292400079 79.22341810418405205 2.4579909 0.00000004042 (-0.7753029225327) 0.6315895647265 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_23 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2494421246669:ℝ):ℂ) + ((0.9683897079387:ℝ):ℂ) * I)‖ ≤ 0.00000016574 := by
  have hl := lg_23
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.36271672761445058 80.36271677887452747 1.3186922 0.00000006573 0.2494421246669 0.9683897079387 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_24 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9741454179394:ℝ):ℂ) + ((0.2259218995752:ℝ):ℂ) * I)‖ ≤ 0.00000014818 := by
  have hl := lg_24
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.45351964516824332 81.45351969642826895 0.2278893 0.00000004817 0.9741454179394 0.2259218995752 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_25 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6834059358658:ℝ):ℂ) + (((-0.7300385789966):ℝ):ℂ) * I)‖ ≤ 0.00000012863 := by
  have hl := lg_25
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.49978736472235334 82.4997874159824046 (-0.8183784) 0.00000002862 0.6834059358658 (-0.7300385789966) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_26 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2501246286573):ℝ):ℂ) + (((-0.9682136490144):ℝ):ℂ) * I)‖ ≤ 0.00000015051 := by
  have hl := lg_26
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.505014242840971 83.50501429410102226 (-1.8236053) 0.0000000505 (-0.2501246286573) (-0.9682136490144) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_27 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9391315081811):ℝ):ℂ) + (((-0.3435578701819):ℝ):ℂ) * I)‖ ≤ 0.00000013765 := by
  have hl := lg_27
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.47229885570372996 84.47229889414880685 (-2.7908899) 0.00000003764 (-0.9391315081811) (-0.3435578701819) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_28 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.835694622394):ℝ):ℂ) + ((0.5491944082347:ℝ):ℂ) * I)‖ ≤ 0.00000013139 := by
  have hl := lg_28
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.40440156914086586 85.40440162040091712 2.5601927 0.00000003138 (-0.835694622394) 0.5491944082347 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_29 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0898843986312):ℝ):ℂ) + ((0.9959522051195:ℝ):ℂ) * I)‖ ≤ 0.00000014666 := by
  have hl := lg_29
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.30379209590371596 86.30379214716379285 1.6608022 0.00000004665 (-0.0898843986312) 0.9959522051195 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_30 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7024905316738:ℝ):ℂ) + ((0.7116930889847:ℝ):ℂ) * I)‖ ≤ 0.00000013518 := by
  have hl := lg_30
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.17268886535141999 87.17268891661147125 0.7919054 0.00000003517 0.7024905316738 0.7116930889847 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_31 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9988242170306:ℝ):ℂ) + (((-0.0484786909198):ℝ):ℂ) * I)‖ ≤ 0.00000017507 := by
  have hl := lg_31
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.01309202430465369 88.01309207556473058 (-0.0484977) 0.00000007506 0.9988242170306 (-0.0484786909198) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_32 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6507558051137:ℝ):ℂ) + (((-0.7592870880707):ℝ):ℂ) * I)‖ ≤ 0.00000014508 := by
  have hl := lg_32
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.826811155445 88.82681121952 (-0.8622169) 0.00000004507 0.6507558051137 (-0.7592870880707) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_33 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0800125528023):ℝ):ℂ) + (((-0.9967938560172):ℝ):ℂ) * I)‖ ≤ 0.00000012679 := by
  have hl := lg_33
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.61548877373624411 89.615488824996321 (-1.6508945) 0.00000002678 (-0.0800125528023) (-0.9967938560172) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_34 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7481234673754):ℝ):ℂ) + (((-0.6635595508534):ℝ):ℂ) * I)‖ ≤ 0.00000017618 := by
  have hl := lg_34
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.38062021260020342 90.38062027667522905 (-2.4160259) 0.00000007617 (-0.7481234673754) (-0.6635595508534) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_35 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998489043045):ℝ):ℂ) + ((0.0173829777517:ℝ):ℂ) * I)‖ ≤ 0.00000013291 := by
  have hl := lg_35
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.12357078932404253 91.12357084058411942 3.1242088 0.0000000329 (-0.9998489043045) 0.0173829777517 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_36 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7388706713353):ℝ):ℂ) + ((0.6738472608902:ℝ):ℂ) * I)‖ ≤ 0.00000014173 := by
  have hl := lg_36
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.84559036598048664 91.8455904172405379 2.4021892 0.00000004172 (-0.7388706713353) 0.6738472608902 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_37 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1287983817426):ℝ):ℂ) + ((0.9916708006491:ℝ):ℂ) * I)‖ ≤ 0.00000013329 := by
  have hl := lg_37
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.54782607442184846 92.54782612568192535 1.6999535 0.00000003328 (-0.1287983817426) 0.9916708006491 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_38 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5263907764214:ℝ):ℂ) + ((0.8502427597448:ℝ):ℂ) * I)‖ ≤ 0.00000016057 := by
  have hl := lg_38
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.23133324713763489 93.23133329839771178 1.0164463 0.00000006056 0.5263907764214 0.8502427597448 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_39 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9391343094403:ℝ):ℂ) + ((0.3435502129705:ℝ):ℂ) * I)‖ ≤ 0.00000014406 := by
  have hl := lg_39
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.89708496365321432 93.89708501491329121 0.3506946 0.00000004405 0.9391343094403 0.3435502129705 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p63_40 : ‖exp (-((((((25630:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9558666425253:ℝ):ℂ) + (((-0.2938008878603):ℝ):ℂ) * I)‖ ≤ 0.00000013208 := by
  have hl := lg_40
  refine (ecis_approx ((((25630:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.54598037562817667 94.5459804397032023 (-0.2982008) 0.00000003207 0.9558666425253 (-0.2938008878603) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_2 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5271338574067:ℝ):ℂ) + ((0.849782264098:ℝ):ℂ) * I)‖ ≤ 0.00000011962 := by
  have hl := lg_2
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.8339838019387 17.8339838148032 1.0155721 0.00000001961 0.5271338574067 0.849782264098 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_3 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999668834518):ℝ):ℂ) + (((-0.0081382634551):ℝ):ℂ) * I)‖ ≤ 0.00000015261 := by
  have hl := lg_3
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.266195568453651556 28.266195581318177285 (-3.1334543) 0.0000000526 (-0.9999668834518) (-0.0081382634551) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_4 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4442597927511):ℝ):ℂ) + ((0.8958980056571:ℝ):ℂ) * I)‖ ≤ 0.00000013922 := by
  have hl := lg_4
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.6679676038774 35.6679676296064 2.0311442 0.00000003921 (-0.4442597927511) 0.8958980056571 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_5 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8426967950301):ℝ):ℂ) + ((0.5383884393044:ℝ):ℂ) * I)‖ ≤ 0.00000011463 := by
  have hl := lg_5
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.409228035640683361 41.40922806136970909 2.5730691 0.00000001462 (-0.8426967950301) 0.5383884393044 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_6 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.52020064853):ℝ):ℂ) + (((-0.8540440768847):ℝ):ℂ) * I)‖ ≤ 0.00000014588 := by
  have hl := lg_6
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.100179370392351556 46.100179396121377285 (-2.1178822) 0.00000004587 (-0.52020064853) (-0.8540440768847) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_7 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9802330747228:ℝ):ℂ) + ((0.1978462009226:ℝ):ℂ) * I)‖ ≤ 0.00000014578 := by
  have hl := lg_7
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.066322211667872638 50.066322237396924096 0.1991602 0.00000004577 0.9802330747228 0.1978462009226 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_8 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9955026136719):ℝ):ℂ) + ((0.0947340788068:ℝ):ℂ) * I)‖ ≤ 0.00000015882 := by
  have hl := lg_8
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.5019514058161 53.5019514444096 3.0467163 0.00000005881 (-0.9955026136719) 0.0947340788068 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_9 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9998675390706:ℝ):ℂ) + ((0.0162758813225:ℝ):ℂ) * I)‖ ≤ 0.00000012772 := by
  have hl := lg_9
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.532391136907303112 56.53239116263635457 0.0162766 0.00000002771 0.9998675390706 0.0162758813225 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_10 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9017269560073):ℝ):ℂ) + (((-0.4323060220392):ℝ):ℂ) * I)‖ ≤ 0.00000012705 := by
  have hl := lg_10
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.243211837579383361 59.24321187617290909 (-2.6945441) 0.00000002704 (-0.9017269560073) (-0.4323060220392) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_11 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4208577915669:ℝ):ℂ) + ((0.907126628028:ℝ):ℂ) * I)‖ ≤ 0.00000012058 := by
  have hl := lg_11
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.695447453764835557 61.695447492358387015 1.1364056 0.00000002057 0.4208577915669 0.907126628028 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_12 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4515361348129:ℝ):ℂ) + (((-0.8922528335389):ℝ):ℂ) * I)‖ ≤ 0.00000013914 := by
  have hl := lg_12
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.934163172331051556 63.934163210924577285 (-1.1023101) 0.00000003913 0.4515361348129 (-0.8922528335389) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_13 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997972721819):ℝ):ℂ) + ((0.0201348925604:ℝ):ℂ) * I)‖ ≤ 0.0000001577 := by
  have hl := lg_13
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 65.9935819980634593 65.993582036657010758 3.1214564 0.00000005769 (-0.9997972721819) 0.0201348925604 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_14 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.348587849273:ℝ):ℂ) + ((0.9372761126473:ℝ):ℂ) * I)‖ ≤ 0.00000016538 := by
  have hl := lg_14
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.900306013606572638 67.900306052200124096 1.2147323 0.00000006537 0.348587849273 0.9372761126473 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_15 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8470504352376:ℝ):ℂ) + (((-0.5315125211731):ℝ):ℂ) * I)‖ ≤ 0.00000016373 := by
  have hl := lg_15
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.675423604094334917 69.675423642687886375 (-0.5603852) 0.00000006372 0.8470504352376 (-0.5315125211731) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_16 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6052664673734):ℝ):ℂ) + (((-0.7960229289794):ℝ):ℂ) * I)‖ ≤ 0.00000017124 := by
  have hl := lg_16
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.3359352077548 71.3359352592128 (-2.2208969) 0.00000007123 (-0.6052664673734) (-0.7960229289794) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_17 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8026239296943):ℝ):ℂ) + ((0.5964853958245:ℝ):ℂ) * I)‖ ≤ 0.00000016779 := by
  have hl := lg_17
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.895746102469830386 72.895746153927856115 2.5024776 0.00000006778 (-0.8026239296943) 0.5964853958245 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_18 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5132330774856:ℝ):ℂ) + ((0.8582492692538:ℝ):ℂ) * I)‖ ≤ 0.00000014732 := by
  have hl := lg_18
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.366374938846003112 74.36637497743955457 1.0318487 0.00000004731 0.5132330774856 0.8582492692538 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_19 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9361618911334:ℝ):ℂ) + (((-0.3515692159298):ℝ):ℂ) * I)‖ ≤ 0.00000012736 := by
  have hl := lg_19
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.757470474908908587 75.757470513502485774 (-0.3592468) 0.00000002735 0.9361618911334 (-0.3515692159298) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_20 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1079648184203):ℝ):ℂ) + (((-0.994154715315):ℝ):ℂ) * I)‖ ≤ 0.00000014665 := by
  have hl := lg_20
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.077195639518083361 77.07719569097610909 (-1.678972) 0.00000004664 (-0.1079648184203) (-0.994154715315) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_21 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9785904884179):ℝ):ℂ) + (((-0.2058170441492):ℝ):ℂ) * I)‖ ≤ 0.00000013258 := by
  have hl := lg_21
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.332517780121524194 78.332517818715101381 (-2.9342941) 0.00000003257 (-0.9785904884179) (-0.2058170441492) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_22 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5490117287005):ℝ):ℂ) + ((0.8358146455648:ℝ):ℂ) * I)‖ ≤ 0.00000013765 := by
  have hl := lg_22
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.529431255703535557 79.529431307161587015 2.1519777 0.00000003764 (-0.5490117287005) 0.8358146455648 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_23 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5333179227568:ℝ):ℂ) + ((0.8459148853557:ℝ):ℂ) * I)‖ ≤ 0.00000013846 := by
  have hl := lg_23
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.673130654888497814 80.673130706346575001 1.0082783 0.00000003845 0.5333179227568 0.8459148853557 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_24 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.996240617535:ℝ):ℂ) + (((-0.0866292789621):ℝ):ℂ) * I)‖ ≤ 0.00000013241 := by
  have hl := lg_24
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.768146974269751556 81.768147025727777285 (-0.086738) 0.0000000324 0.996240617535 (-0.0866292789621) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_25 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4202757832787:ℝ):ℂ) + (((-0.9073964216314):ℝ):ℂ) * I)‖ ≤ 0.00000012942 := by
  have hl := lg_25
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.818456071281366722 82.81845612273941818 (-1.1370471) 0.00000002941 0.4202757832787 (-0.9073964216314) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_26 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5441372616825):ℝ):ℂ) + (((-0.8389962100274):ℝ):ℂ) * I)‖ ≤ 0.00000015814 := by
  have hl := lg_26
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.8275658000021593 83.827565851460210758 (-2.1461568) 0.00000005813 (-0.5441372616825) (-0.8389962100274) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_27 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997019695176):ℝ):ℂ) + (((-0.0244125277941):ℝ):ℂ) * I)‖ ≤ 0.00000015063 := by
  have hl := lg_27
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.798586705360954668 84.798586743954531855 (-3.1171777) 0.00000005062 (-0.9997019695176) (-0.0244125277941) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_28 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6127282384863):ℝ):ℂ) + ((0.7902936832269:ℝ):ℂ) * I)‖ ≤ 0.0000001665 := by
  have hl := lg_28
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.734289815545272638 85.734289867003324096 2.2303045 0.00000006649 (-0.6127282384863) 0.7902936832269 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_29 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2409615061812:ℝ):ℂ) + ((0.9705346735377:ℝ):ℂ) * I)‖ ≤ 0.00000013393 := by
  have hl := lg_29
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.637154382969438468 86.637154434427515655 1.3274399 0.00000003392 0.2409615061812 0.9705346735377 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p729_30 : ‖exp (-((((((25729:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8981788769837:ℝ):ℂ) + ((0.4396301911155:ℝ):ℂ) * I)‖ ≤ 0.00000015699 := by
  have hl := lg_30
  refine (ecis_approx ((((25729:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.509407406033034917 87.509407457491086375 0.4551869 0.00000005698 0.8981788769837 0.4396301911155 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_2 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6025717023012:ℝ):ℂ) + ((0.7980647489934:ℝ):ℂ) * I)‖ ≤ 0.00000012115 := by
  have hl := lg_2
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.9254792297383 17.9254792426688 0.9240767 0.00000002114 0.6025717023012 0.7980647489934 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_3 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9906467476329):ℝ):ℂ) + ((0.1364515334846:ℝ):ℂ) * I)‖ ≤ 0.00000014539 := by
  have hl := lg_3
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.411212390523529204 28.411212403454055065 3.0047141 0.00000004538 (-0.9906467476329) 0.1364515334846 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_4 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2738146871718):ℝ):ℂ) + ((0.9617824686942:ℝ):ℂ) * I)‖ ≤ 0.00000014228 := by
  have hl := lg_4
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.8509584594766 35.8509584853376 1.8481534 0.00000004227 (-0.2738146871718) 0.9617824686942 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_5 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7102314776822):ℝ):ℂ) + ((0.7039682152512:ℝ):ℂ) * I)‖ ≤ 0.00000011563 := by
  have hl := lg_5
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.621673840013358949 41.62167386587438481 2.3606233 0.00000001562 (-0.7102314776822) 0.7039682152512 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_6 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7058328510991):ℝ):ℂ) + (((-0.7083784202561):ℝ):ℂ) * I)‖ ≤ 0.00000013001 := by
  have hl := lg_6
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.336691620261829204 46.336691646122855065 (-2.3543945) 0.00000003 (-0.7058328510991) (-0.7083784202561) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_7 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.998335822556:ℝ):ℂ) + (((-0.0576678888235):ℝ):ℂ) * I)‖ ≤ 0.00000011971 := by
  have hl := lg_7
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.323182351274548342 50.323182377135600064 (-0.0576999) 0.0000000197 0.998335822556 (-0.0576678888235) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_8 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9325576665749):ℝ):ℂ) + ((0.3610210497299:ℝ):ℂ) * I)‖ ≤ 0.00000016341 := by
  have hl := lg_8
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 53.7764376892149 53.7764377280064 2.7722301 0.0000000634 (-0.9325576665749) 0.3610210497299 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_9 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.962761986887:ℝ):ℂ) + (((-0.2703504329669):ℝ):ℂ) * I)‖ ≤ 0.00000014231 := by
  have hl := lg_9
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.822424781047058408 56.82242480690811013 (-0.273757) 0.0000000423 0.962761986887 (-0.2703504329669) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_10 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9897776063521):ℝ):ℂ) + (((-0.1426193870395):ℝ):ℂ) * I)‖ ≤ 0.00000014394 := by
  have hl := lg_10
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.547153069751658949 59.54715310854318481 (-2.9984853) 0.00000004393 (-0.9897776063521) (-0.1426193870395) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_11 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6823064542536:ℝ):ℂ) + ((0.7310662777641:ℝ):ℂ) * I)‖ ≤ 0.00000014214 := by
  have hl := lg_11
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.011969629671281913 62.011969668462833635 0.8198834 0.00000004213 0.6823064542536 0.7310662777641 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_12 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1400169435362:ℝ):ℂ) + (((-0.990149107722):ℝ):ℂ) * I)‖ ≤ 0.00000012181 := by
  have hl := lg_12
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.262170850000129204 64.262170888791655065 (-1.4303178) 0.0000000218 0.1400169435362 (-0.990149107722) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_13 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9363506001551):ℝ):ℂ) + ((0.351066309146:ℝ):ℂ) * I)‖ ≤ 0.00000016585 := by
  have hl := lg_13
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.3321553131454437 66.332155351936995422 2.782883 0.00000006584 (-0.9363506001551) 0.351066309146 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_14 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6475916252847:ℝ):ℂ) + ((0.7619875897028:ℝ):ℂ) * I)‖ ≤ 0.00000014084 := by
  have hl := lg_14
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.248661581012848342 68.248661619804400064 0.8663768 0.00000004083 0.6475916252847 0.7619875897028 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_15 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6075309666303:ℝ):ℂ) + (((-0.7942959930562):ℝ):ℂ) * I)‖ ≤ 0.00000014845 := by
  have hl := lg_15
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.032886230536888153 70.032886269328439875 (-0.9178479) 0.00000004844 0.6075309666303 (-0.7942959930562) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_16 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8500510830485):ℝ):ℂ) + (((-0.526700252643):ℝ):ℂ) * I)‖ ≤ 0.00000016004 := by
  have hl := lg_16
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.7019169189532 71.7019169706752 (-2.5868786) 0.00000006003 (-0.8500510830485) (-0.526700252643) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_17 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5292336245831):ℝ):ℂ) + ((0.8484761461603:ℝ):ℂ) * I)‖ ≤ 0.00000012933 := by
  have hl := lg_17
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.269730263747999674 73.269730315470025535 2.1284934 0.00000002932 (-0.5292336245831) 0.8484761461603 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_18 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7958902797753:ℝ):ℂ) + ((0.6054408827946:ℝ):ℂ) * I)‖ ≤ 0.00000016344 := by
  have hl := lg_18
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.747904010785358408 74.74790404957691013 0.6503197 0.00000006343 0.7958902797753 0.6054408827946 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_19 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7331099904952:ℝ):ℂ) + (((-0.6801100953787):ℝ):ℂ) * I)‖ ≤ 0.00000016611 := by
  have hl := lg_19
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.146136420055940183 76.146136458847517766 (-0.7479128) 0.0000000661 0.7331099904952 (-0.6801100953787) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_20 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4825924717907):ℝ):ℂ) + (((-0.875845024057):ℝ):ℂ) * I)‖ ≤ 0.00000016507 := by
  have hl := lg_20
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.472632299489958949 77.47263235121198481 (-2.0744086) 0.00000006506 (-0.4825924717907) (-0.875845024057) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_21 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9811292638309):ℝ):ℂ) + ((0.1933529604714:ℝ):ℂ) * I)‖ ≤ 0.00000015155 := by
  have hl := lg_21
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.734394741798077546 78.734394780589655129 2.9470142 0.00000005154 (-0.9811292638309) 0.1933529604714 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_22 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1722996638308):ℝ):ℂ) + ((0.9850445806374:ℝ):ℂ) * I)‖ ≤ 0.00000013394 := by
  have hl := lg_22
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.937448859409581913 79.937448911131633635 1.7439601 0.00000003393 (-0.1722996638308) 0.9850445806374 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_23 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8284885190668:ℝ):ℂ) + ((0.5600060479802:ℝ):ℂ) * I)‖ ≤ 0.00000014966 := by
  have hl := lg_23
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.087015891253894126 81.087015942975971709 0.5943931 0.00000004965 0.8284885190668 0.5600060479802 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_24 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8745733471378:ℝ):ℂ) + (((-0.484893246474):ℝ):ℂ) * I)‖ ≤ 0.00000013814 := by
  have hl := lg_24
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.187650079738429204 82.187650131460455065 (-0.5062411) 0.00000003813 0.8745733471378 (-0.484893246474) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_25 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0088575109707:ℝ):ℂ) + (((-0.9999607714802):ℝ):ℂ) * I)‖ ≤ 0.00000013843 := by
  have hl := lg_25
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.243347680026717898 83.24334773174876962 (-1.5619387) 0.00000003842 0.0088575109707 (-0.9999607714802) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_26 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8443920172185):ℝ):ℂ) + (((-0.5357257891751):ℝ):ℂ) * I)‖ ≤ 0.00000015047 := by
  have hl := lg_26
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.2576345428837437 84.257634594605795422 (-2.5762256) 0.00000005046 (-0.8443920172185) (-0.5357257891751) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_27 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9168672999755):ℝ):ℂ) + ((0.3991921267978:ℝ):ℂ) * I)‖ ≤ 0.00000012896 := by
  have hl := lg_27
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.233637171570587612 85.233637210362165195 2.7309571 0.00000002895 (-0.9168672999755) 0.3991921267978 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_28 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2178950464685):ℝ):ℂ) + ((0.9759722069421:ℝ):ℂ) * I)‖ ≤ 0.00000016197 := by
  have hl := lg_28
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.174140810751148342 86.174140862473200064 1.7904535 0.00000006196 (-0.2178950464685) 0.9759722069421 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_29 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6348694416042:ℝ):ℂ) + ((0.7726194355031:ℝ):ℂ) * I)‖ ≤ 0.00000016814 := by
  have hl := lg_29
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.081637432390401812 87.081637484112479395 0.8829568 0.00000006813 0.6348694416042 0.7726194355031 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p861_30 : ‖exp (-((((((25861:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.999980601088:ℝ):ℂ) + ((0.0062287597226:ℝ):ℂ) * I)‖ ≤ 0.00000014025 := by
  have hl := lg_30
  refine (ecis_approx ((((25861:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.958365460275188153 87.958365511997239875 0.0062288 0.00000004024 0.999980601088 0.0062287597226 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_2 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.672968691554:ℝ):ℂ) + ((0.7396709675174:ℝ):ℂ) * I)‖ ≤ 0.00000014901 := by
  have hl := lg_2
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.0169746575379 18.0169746705344 0.8325813 0.000000049 0.672968691554 0.7396709675174 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_3 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9605299206358):ℝ):ℂ) + ((0.2781766908432:ℝ):ℂ) * I)‖ ≤ 0.00000012332 := by
  have hl := lg_3
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.556229212593406852 28.556229225589932845 2.8596973 0.00000002331 (-0.9605299206358) 0.2781766908432 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_4 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0942261808212):ℝ):ℂ) + ((0.9955508158037:ℝ):ℂ) * I)‖ ≤ 0.00000012802 := by
  have hl := lg_4
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.0339493150758 36.0339493410688 1.6651625 0.00000002801 (-0.0942261808212) 0.9955508158037 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_5 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5458315092523):ℝ):ℂ) + ((0.8378949597049:ℝ):ℂ) * I)‖ ≤ 0.00000012014 := by
  have hl := lg_5
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.834119644386034537 41.83411967037906053 2.1481775 0.00000002013 (-0.5458315092523) 0.8378949597049 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_6 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8521657823178):ℝ):ℂ) + (((-0.523271898129):ℝ):ℂ) * I)‖ ≤ 0.00000014588 := by
  have hl := lg_6
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.573203870131306852 46.573203896124332845 (-2.5909067) 0.00000004587 (-0.8521657823178) (-0.523271898129) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_7 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9509326061199:ℝ):ℂ) + (((-0.3093980908441):ℝ):ℂ) * I)‖ ≤ 0.00000015945 := by
  have hl := lg_7
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.580042490881224046 50.580042516874276032 (-0.31456) 0.00000005944 0.9509326061199 (-0.3093980908441) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_8 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7997913047457):ℝ):ℂ) + ((0.6002781595261:ℝ):ℂ) * I)‖ ≤ 0.000000147 := by
  have hl := lg_8
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.0509239726137 54.0509240116032 2.4977438 0.00000004699 (-0.7997913047457) 0.6002781595261 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_9 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.845235461046:ℝ):ℂ) + (((-0.5343940637679):ℝ):ℂ) * I)‖ ≤ 0.00000013944 := by
  have hl := lg_9
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.112458425186813704 57.11245845117986569 (-0.5637907) 0.00000003943 0.845235461046 (-0.5343940637679) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_10 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9870940919555):ℝ):ℂ) + ((0.1601413539616:ℝ):ℂ) * I)‖ ≤ 0.00000016913 := by
  have hl := lg_10
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.851094301923934537 59.85109434091346053 2.9807588 0.00000006912 (-0.9870940919555) 0.1601413539616 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_11 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8759661624919:ℝ):ℂ) + ((0.4823725553649:ℝ):ℂ) * I)‖ ≤ 0.00000016623 := by
  have hl := lg_11
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.328491805577728269 62.328491844567280255 0.5033612 0.00000006622 0.8759661624919 0.4823725553649 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_12 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1864319585785):ℝ):ℂ) + (((-0.9824678747011):ℝ):ℂ) * I)‖ ≤ 0.00000014414 := by
  have hl := lg_12
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.590178527669206852 64.590178566658732845 (-1.7583255) 0.00000004413 (-0.1864319585785) (-0.9824678747011) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_13 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7665897313172):ℝ):ℂ) + ((0.6421372001378:ℝ):ℂ) * I)‖ ≤ 0.00000015076 := by
  have hl := lg_13
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.6707286282274281 66.670728667216980086 2.4443097 0.00000005075 (-0.7665897313172) 0.6421372001378 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_14 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8688007064155:ℝ):ℂ) + ((0.4951619255678:ℝ):ℂ) * I)‖ ≤ 0.00000013057 := by
  have hl := lg_14
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.597017148419124046 68.597017187408676032 0.5180212 0.00000003056 0.8688007064155 0.4951619255678 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_15 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2912046559122:ℝ):ℂ) + (((-0.9566607802011):ℝ):ℂ) * I)‖ ≤ 0.00000012201 := by
  have hl := lg_15
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.390348856979441389 70.390348895968993375 (-1.2753105) 0.000000022 0.2912046559122 (-0.9566607802011) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_16 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9822428522079):ℝ):ℂ) + (((-0.1876139092582):ℝ):ℂ) * I)‖ ≤ 0.00000014884 := by
  have hl := lg_16
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.0678986301516 72.0678986821376 (-2.9528603) 0.00000004883 (-0.9822428522079) (-0.1876139092582) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_17 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1826812179199):ℝ):ℂ) + ((0.9831721988637:ℝ):ℂ) * I)‖ ≤ 0.00000016114 := by
  have hl := lg_17
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.643714425026168962 73.643714477012194955 1.7545092 0.00000006113 (-0.1826812179199) 0.9831721988637 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_18 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9640927764579:ℝ):ℂ) + ((0.2655656573838:ℝ):ℂ) * I)‖ ≤ 0.00000013557 := by
  have hl := lg_18
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.129433082724713704 75.12943312171426569 0.2687906 0.00000003556 0.9640927764579 0.2655656573838 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_19 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4207007616431:ℝ):ℂ) + (((-0.907199464921):ℝ):ℂ) * I)‖ ≤ 0.00000012097 := by
  have hl := lg_19
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.534802365202971779 76.534802404192549758 (-1.1365787) 0.00000002096 0.4207007616431 (-0.907199464921) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v25p993_20 : ‖exp (-((((((25993:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7827353877318):ℝ):ℂ) + (((-0.6223546519062):ℝ):ℂ) * I)‖ ≤ 0.00000012671 := by
  have hl := lg_20
  refine (ecis_approx ((((25993:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.868068959461834537 77.86806901144786053 (-2.4698453) 0.0000000267 (-0.7827353877318) (-0.6223546519062) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_2 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7584308357589:ℝ):ℂ) + ((0.651753532687:ℝ):ℂ) * I)‖ ≤ 0.0000001131 := by
  have hl := lg_2
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.139661708451 18.139661721536 0.7098942 0.00000001309 0.7584308357589 0.651753532687 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_3 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8886746174982):ℝ):ℂ) + ((0.4585383562037:ℝ):ℂ) * I)‖ ≤ 0.00000014827 := by
  have hl := lg_3
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.75068358764165188 28.75068360072667805 2.6652429 0.00000004826 (-0.8886746174982) 0.4585383562037 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_4 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.15043466526:ℝ):ℂ) + ((0.9886199530093:ℝ):ℂ) * I)‖ ≤ 0.00000012619 := by
  have hl := lg_4
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.279323416902 36.279323443072 1.4197884 0.00000002618 0.15043466526 0.9886199530093 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_5 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2883571585531):ℝ):ℂ) + ((0.9575229235426:ℝ):ℂ) * I)‖ ≤ 0.00000013072 := by
  have hl := lg_5
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.11899015479484953 42.1189901809648757 1.863307 0.00000003071 (-0.2883571585531) 0.9575229235426 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_6 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9728522246806):ℝ):ℂ) + (((-0.2314271994586):ℝ):ℂ) * I)‖ ≤ 0.00000015418 := by
  have hl := lg_6
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.89034529609265188 46.89034532226267805 (-2.9080482) 0.00000005417 (-0.9728522246806) (-0.2314271994586) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_7 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7906134645138:ℝ):ℂ) + (((-0.6123155638472):ℝ):ℂ) * I)‖ ≤ 0.00000015592 := by
  have hl := lg_7
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.92446858717199374 50.92446861334204608 (-0.6589861) 0.00000005591 0.7906134645138 (-0.6123155638472) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_8 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5302422579581):ℝ):ℂ) + ((0.8478461817263:ℝ):ℂ) * I)‖ ≤ 0.00000013928 := by
  have hl := lg_8
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.418985125353 54.418985164608 2.1296826 0.00000003927 (-0.5302422579581) 0.8478461817263 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_9 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5794852390255:ℝ):ℂ) + (((-0.814982734634):ℝ):ℂ) * I)‖ ≤ 0.00000013685 := by
  have hl := lg_9
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.50136717528330376 57.5013672014533561 (-0.9526994) 0.00000003684 0.5794852390255 (-0.814982734634) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_10 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.84276790879):ℝ):ℂ) + ((0.5382771143605:ℝ):ℂ) * I)‖ ≤ 0.00000013072 := by
  have hl := lg_10
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.25865186324584953 60.2586519025008757 2.5732012 0.00000003071 (-0.84276790879) 0.5382771143605 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_11 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9968863447599:ℝ):ℂ) + ((0.0788518587685:ℝ):ℂ) * I)‖ ≤ 0.0000001362 := by
  have hl := lg_11
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.75291926872500861 62.75291930798006095 0.0789338 0.00000003619 0.9968863447599 0.0788518587685 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_12 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5870076310187):ℝ):ℂ) + (((-0.8095813986961):ℝ):ℂ) * I)‖ ≤ 0.00000016727 := by
  have hl := lg_12
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.03000700454365188 65.03000704379867805 (-2.198154) 0.00000006726 (-0.5870076310187) (-0.8095813986961) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_13 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4073197243985):ℝ):ℂ) + ((0.913285630081:ℝ):ℂ) * I)‖ ≤ 0.00000012465 := by
  have hl := lg_13
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.124724664360089 67.12472470361514134 1.9903137 0.00000002464 (-0.4073197243985) 0.913285630081 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_14 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9987044625101:ℝ):ℂ) + ((0.0508861136499:ℝ):ℂ) * I)‖ ≤ 0.00000015592 := by
  have hl := lg_14
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.06413029562299374 69.06413033487804608 0.0509081 0.00000005591 0.9987044625101 0.0508861136499 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_15 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1828052927964):ℝ):ℂ) + (((-0.9831491366649):ℝ):ℂ) * I)‖ ≤ 0.00000013655 := by
  have hl := lg_15
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.86967374243650141 70.86967378169155375 (-1.7546354) 0.00000003654 (-0.1828052927964) (-0.9831491366649) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_16 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9547388228976):ℝ):ℂ) + ((0.2974454232889:ℝ):ℂ) * I)‖ ≤ 0.00000015237 := by
  have hl := lg_16
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.558646833804 72.558646886144 2.8395768 0.00000005236 (-0.9547388228976) 0.2974454232889 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_17 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3124450209601:ℝ):ℂ) + ((0.9499358446112:ℝ):ℂ) * I)‖ ≤ 0.00000015294 := by
  have hl := lg_17
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.14519318674007778 74.14519323908010395 1.2530305 0.00000005293 0.3124450209601 0.9499358446112 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_18 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9706673505207:ℝ):ℂ) + (((-0.2404264848827):ℝ):ℂ) * I)‖ ≤ 0.00000013685 := by
  have hl := lg_18
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.64102888373430376 75.6410289229893561 (-0.2428052) 0.00000003684 0.9706673505207 (-0.2404264848827) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_19 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0868385605087):ℝ):ℂ) + (((-0.9962223970622):ℝ):ℂ) * I)‖ ≤ 0.00000012179 := by
  have hl := lg_19
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.05596806437740051 77.05596810363247902 (-1.6577444) 0.00000002178 (-0.0868385605087) (-0.9962223970622) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p17_20 : ‖exp (-((((((26170:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.990005179111):ℝ):ℂ) + (((-0.1410310069686):ℝ):ℂ) * I)‖ ≤ 0.0000001379 := by
  have hl := lg_20
  refine (ecis_approx ((((26170:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.39831357169684953 78.3983136240368757 (-3.0000899) 0.00000003789 (-0.990005179111) (-0.1410310069686) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_2 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8544466502266:ℝ):ℂ) + ((0.519539143777:ℝ):ℂ) * I)‖ ≤ 0.00000013468 := by
  have hl := lg_2
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.3032444430018 18.3032444562048 0.5463115 0.00000003467 0.8544466502266 0.519539143777 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_3 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.741413334541):ℝ):ℂ) + ((0.6710486326139:ℝ):ℂ) * I)‖ ≤ 0.00000014821 := by
  have hl := lg_3
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.009956087705978584 29.00995610090900499 2.4059704 0.0000000482 (-0.741413334541) 0.6710486326139 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_4 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4601582449506:ℝ):ℂ) + ((0.8878369161079:ℝ):ℂ) * I)‖ ≤ 0.00000015709 := by
  have hl := lg_4
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 36.6064888860036 36.6064889124096 1.0926229 0.00000005708 0.4601582449506 0.8878369161079 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_5 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0872058155623:ℝ):ℂ) + ((0.99619031602:ℝ):ℂ) * I)‖ ≤ 0.00000014827 := by
  have hl := lg_5
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.498817502006602854 42.49881752841262926 1.4834796 0.00000004826 0.0872058155623 0.99619031602 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_6 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9821341720262):ℝ):ℂ) + ((0.1881820071099:ℝ):ℂ) * I)‖ ≤ 0.00000012674 := by
  have hl := lg_6
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.313200530707778584 47.31320055711380499 2.9522819 0.00000002673 (-0.9821341720262) 0.1881820071099 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_7 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4372831246185:ℝ):ℂ) + (((-0.8993238954481):ℝ):ℂ) * I)‖ ≤ 0.00000015121 := by
  have hl := lg_7
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.383703382226353332 51.383703408632406144 (-1.1182209) 0.0000000512 0.4372831246185 (-0.8993238954481) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_8 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0680853602362):ℝ):ℂ) + ((0.9976794994993:ℝ):ℂ) * I)‖ ≤ 0.00000013563 := by
  have hl := lg_8
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.9097333290054 54.9097333686144 1.6389344 0.00000003562 (-0.0680853602362) 0.9976794994993 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_9 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0993875719345:ℝ):ℂ) + (((-0.9950487980722):ℝ):ℂ) * I)‖ ≤ 0.00000013722 := by
  have hl := lg_9
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.019912175411957168 58.01991220181800998 (-1.4712444) 0.00000003721 0.0993875719345 (-0.9950487980722) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_10 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4430471468366):ℝ):ℂ) + ((0.8964983132587:ℝ):ℂ) * I)‖ ≤ 0.0000001268 := by
  have hl := lg_10
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.802061945008402854 60.80206198461742926 2.0297911 0.00000002679 (-0.4430471468366) 0.8964983132587 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_11 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8837550365425:ℝ):ℂ) + (((-0.46794982144):ℝ):ℂ) * I)‖ ≤ 0.00000012075 := by
  have hl := lg_11
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.318822552921382398 63.31882259253043521 (-0.4869695) 0.00000002074 0.8837550365425 (-0.46794982144) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_12 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9369491698481):ℝ):ℂ) + (((-0.3494656677673):ℝ):ℂ) * I)‖ ≤ 0.00000014154 := by
  have hl := lg_12
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.616444973709578584 65.61644501331860499 (-2.7845919) 0.00000004153 (-0.9369491698481) (-0.3494656677673) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_13 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1847433657448:ℝ):ℂ) + ((0.9827867972318:ℝ):ℂ) * I)‖ ≤ 0.00000016645 := by
  have hl := lg_13
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.7300527125369702 67.730052752146023012 1.3849856 0.00000006644 0.1847433657448 0.9827867972318 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_14 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8408690135263:ℝ):ℂ) + (((-0.5412386738688):ℝ):ℂ) * I)‖ ≤ 0.00000015376 := by
  have hl := lg_14
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.686947825228153332 69.686947864837206144 (-0.5719095) 0.00000005375 0.8408690135263 (-0.5412386738688) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_15 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.73314763102):ℝ):ℂ) + (((-0.6800695193139):ℝ):ℂ) * I)‖ ≤ 0.00000015036 := by
  have hl := lg_15
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.508773589712581438 71.50877362932163425 (-2.3937352) 0.00000005035 (-0.73314763102) (-0.6800695193139) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v26p406_16 : ‖exp (-((((((26406:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5765088609165):ℝ):ℂ) + ((0.8170908965804:ℝ):ℂ) * I)‖ ≤ 0.00000013868 := by
  have hl := lg_16
  refine (ecis_approx ((((26406:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.2129777720072 73.2129778248192 2.1852459 0.00000003867 (-0.5765088609165) 0.8170908965804 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
