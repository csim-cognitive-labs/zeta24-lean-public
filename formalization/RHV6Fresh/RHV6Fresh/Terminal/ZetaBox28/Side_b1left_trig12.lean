/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b1left (b1), angles 12

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

lemma cs_b1left_v24p846_36 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4787927883362:ℝ):ℂ) + (((-0.8779279388636):ℝ):ℂ) * I)‖ ≤ 0.00000016824 := by
  have hl := lg_36
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.036111519046085488 89.03611156873813518 (-1.0715172) 0.00000006823 0.4787927883362 (-0.8779279388636) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_37 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1804814064618):ℝ):ℂ) + (((-0.9835783964285):ℝ):ℂ) * I)‖ ≤ 0.00000016881 := by
  have hl := lg_37
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.716866431723965932 89.71686648141604047 (-1.7522722) 0.0000000688 (-0.1804814064618) (-0.9835783964285) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_38 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7473568894685):ℝ):ℂ) + (((-0.6644228169854):ℝ):ℂ) * I)‖ ≤ 0.00000014792 := by
  have hl := lg_38
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.379465698727338138 90.379465748419412676 (-2.4148714) 0.00000004791 (-0.7473568894685) (-0.6644228169854) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_39 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.996694192361):ℝ):ℂ) + (((-0.0812446084585):ℝ):ℂ) * I)‖ ≤ 0.00000016663 := by
  have hl := lg_39
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 91.024852633902760944 91.024852683594835482 (-3.0602584) 0.00000006662 (-0.996694192361) (-0.0812446084585) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_40 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8537182220862):ℝ):ℂ) + ((0.5207352467442:ℝ):ℂ) * I)‖ ≤ 0.00000013906 := by
  have hl := lg_40
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.653898884621836814 91.65389894673686166 2.5938807 0.00000003905 (-0.8537182220862) 0.5207352467442 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_41 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3982164640088):ℝ):ℂ) + ((0.9172914737362:ℝ):ℂ) * I)‖ ≤ 0.00000017067 := by
  have hl := lg_41
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.26741153704219468 92.267411599157244372 1.980368 0.00000007066 (-0.3982164640088) 0.9172914737362 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_42 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1880300425519:ℝ):ℂ) + ((0.982163277209:ℝ):ℂ) * I)‖ ≤ 0.00000015205 := by
  have hl := lg_42
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.866139310034137756 92.866139359726212294 1.3816403 0.00000005204 0.1880300425519 0.982163277209 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_43 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.698854566319:ℝ):ℂ) + ((0.7152637940893:ℝ):ℂ) * I)‖ ≤ 0.00000015902 := by
  have hl := lg_43
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.45077804868781788 93.450778098379917264 0.7970015 0.00000005901 0.698854566319 0.7152637940893 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_44 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9746144145119:ℝ):ℂ) + ((0.2238900243996:ℝ):ℂ) * I)‖ ≤ 0.00000016648 := by
  have hl := lg_44
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.021975612040070918 94.02197567415512061 0.225804 0.00000006647 0.9746144145119 0.2238900243996 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_45 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9452108042635:ℝ):ℂ) + (((-0.3264606186105):ℝ):ℂ) * I)‖ ≤ 0.00000013701 := by
  have hl := lg_45
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.580336194998922302 94.58033624469099684 (-0.3325566) 0.000000037 0.9452108042635 (-0.3264606186105) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_46 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6381952950846:ℝ):ℂ) + (((-0.7698745127174):ℝ):ℂ) * I)‖ ≤ 0.00000015931 := by
  have hl := lg_46
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.126424104874987636 95.126424166990062174 (-0.8786445) 0.0000000593 0.6381952950846 (-0.7698745127174) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_47 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1571544423974:ℝ):ℂ) + (((-0.987574038356):ℝ):ℂ) * I)‖ ≤ 0.00000013423 := by
  have hl := lg_47
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.660767279795034334 95.660767341910133718 (-1.4129877) 0.00000003422 0.1571544423974 (-0.987574038356) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_48 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3572149198085):ℝ):ℂ) + (((-0.9340222165793):ℝ):ℂ) * I)‖ ≤ 0.00000013916 := by
  have hl := lg_48
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.183860284724442744 96.18386034683946759 (-1.9360807) 0.00000003915 (-0.3572149198085) (-0.9340222165793) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_49 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7692018575431):ℝ):ℂ) + (((-0.6390058703277):ℝ):ℂ) * I)‖ ≤ 0.00000014304 := by
  have hl := lg_49
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.696167101022190024 96.696167150714289408 (-2.4483875) 0.00000004303 (-0.7692018575431) (-0.6390058703277) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_50 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9817676501634):ℝ):ℂ) + (((-0.1900849303774):ℝ):ℂ) * I)‖ ≤ 0.00000014713 := by
  have hl := lg_50
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 97.198123560574673628 97.19812362268972332 (-2.950344) 0.00000004712 (-0.9817676501634) (-0.1900849303774) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_51 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9551094096858):ℝ):ℂ) + ((0.2962532958667:ℝ):ℂ) * I)‖ ≤ 0.00000017651 := by
  have hl := lg_51
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.690139638375561908 97.6901397004906116 2.8408252 0.0000000765 (-0.9551094096858) 0.2962532958667 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_52 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.708638838196):ℝ):ℂ) + ((0.7055713975035:ℝ):ℂ) * I)‖ ≤ 0.00000014684 := by
  have hl := lg_52
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.1726013995811182 98.172601461696167892 2.3583635 0.00000004683 (-0.708638838196) 0.7055713975035 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_53 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3091467230706):ℝ):ℂ) + ((0.9510143551035:ℝ):ℂ) * I)‖ ≤ 0.00000016307 := by
  have hl := lg_53
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.645872851822981324 98.645872913938055862 1.885092 0.00000006306 (-0.3091467230706) 0.9510143551035 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_54 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1495657091924:ℝ):ℂ) + ((0.9887517881823:ℝ):ℂ) * I)‖ ≤ 0.00000012994 := by
  have hl := lg_54
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.110297595101528232 99.11029764479360277 1.4206673 0.00000002993 0.1495657091924 0.9887517881823 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_55 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5696103708491:ℝ):ℂ) + ((0.8219148529022:ℝ):ℂ) * I)‖ ≤ 0.00000013525 := by
  have hl := lg_55
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.566200287992907732 99.56620035010798227 0.9647646 0.00000003524 0.5696103708491 0.8219148529022 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_56 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8692679498306:ℝ):ℂ) + ((0.4943412094873:ℝ):ℂ) * I)‖ ≤ 0.00000013918 := by
  have hl := lg_56
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.013888075712495012 100.013888137827544704 0.5170768 0.00000003917 0.8692679498306 0.4943412094873 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_57 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9970128306668:ℝ):ℂ) + ((0.077236102218:ℝ):ℂ) * I)‖ ≤ 0.00000014011 := by
  have hl := lg_57
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.453651774782780882 100.453651824474880266 0.0773131 0.0000000401 0.9970128306668 0.077236102218 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_58 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.937715258591:ℝ):ℂ) + (((-0.3474047981903):ℝ):ℂ) * I)‖ ≤ 0.000000155 := by
  have hl := lg_58
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.885767007743309432 100.88576706985838397 (-0.3548021) 0.00000005499 0.937715258591 (-0.3474047981903) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_59 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7112437196286:ℝ):ℂ) + (((-0.7029454966702):ℝ):ℂ) * I)‖ ≤ 0.00000014625 := by
  have hl := lg_59
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.310495298988477232 101.310495361103576616 (-0.7795304) 0.00000004624 0.7112437196286 (-0.7029454966702) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_60 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3650404274653:ℝ):ℂ) + (((-0.9309916682312):ℝ):ℂ) * I)‖ ≤ 0.00000015421 := by
  have hl := lg_60
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.728084960677279558 101.72808502279232925 (-1.1971201) 0.0000000542 0.3650404274653 (-0.9309916682312) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_61 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0370023242408):ℝ):ℂ) + (((-0.9993151795107):ℝ):ℂ) * I)‖ ≤ 0.00000014421 := by
  have hl := lg_61
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.138771996957043218 102.138772059072117756 (-1.6078071) 0.0000000442 (-0.0370023242408) (-0.9993151795107) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_62 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4268617945027):ℝ):ℂ) + (((-0.9043168738833):ℝ):ℂ) * I)‖ ≤ 0.00000014579 := by
  have hl := lg_62
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.542780898537289098 102.542780960652363636 (-2.011816) 0.00000004578 (-0.4268617945027) (-0.9043168738833) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_63 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7436839917074):ℝ):ℂ) + (((-0.6685313159799):ℝ):ℂ) * I)‖ ≤ 0.0000001288 := by
  have hl := lg_63
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.9403253860895805 102.940325435781679884 (-2.4093605) 0.00000002879 (-0.7436839917074) (-0.6685313159799) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_64 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9424379444482):ℝ):ℂ) + (((-0.3343811009604):ℝ):ℂ) * I)‖ ≤ 0.00000016449 := by
  have hl := lg_64
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.3316090504028 103.3316091249408 (-2.8006442) 0.00000006448 (-0.9424379444482) (-0.3343811009604) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_65 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9990203073085):ℝ):ℂ) + ((0.0442540958567:ℝ):ℂ) * I)‖ ≤ 0.00000014653 := by
  have hl := lg_65
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 103.716826075533955014 103.716826137649029552 3.0973241 0.00000004652 (-0.9990203073085) 0.0442540958567 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_66 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9116133816821):ℝ):ℂ) + ((0.4110487102611:ℝ):ℂ) * I)‖ ≤ 0.00000013397 := by
  have hl := lg_66
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.096161688095513662 104.0961617502105882 2.7179885 0.00000003396 (-0.9116133816821) 0.4110487102611 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_67 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6986873517449):ℝ):ℂ) + ((0.7154271342969:ℝ):ℂ) * I)‖ ≤ 0.00000013297 := by
  have hl := lg_67
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.469792789094874502 104.469792851209973886 2.3443574 0.00000003296 (-0.6986873517449) 0.7154271342969 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_68 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.394446535209):ℝ):ℂ) + ((0.9189188924266:ℝ):ℂ) * I)‖ ≤ 0.00000015655 := by
  have hl := lg_68
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.837888404053919164 104.83788847859194401 1.9762618 0.00000005654 (-0.394446535209) 0.9189188924266 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_69 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0427306587917):ℝ):ℂ) + ((0.9990866282755:ℝ):ℂ) * I)‖ ≤ 0.00000014114 := by
  have hl := lg_69
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.20061018093043038 105.200610243045529764 1.61354 0.00000004113 (-0.0427306587917) 0.9990866282755 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_70 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3095872506967:ℝ):ℂ) + ((0.9508710397347:ℝ):ℂ) * I)‖ ≤ 0.0000001704 := by
  have hl := lg_70
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.558112751665331826 105.558112813780406364 1.2560374 0.00000007039 0.3095872506967 0.9508710397347 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_71 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.61878125609:ℝ):ℂ) + ((0.7855633374284:ℝ):ℂ) * I)‖ ≤ 0.00000013275 := by
  have hl := lg_71
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.910544192675470602 105.910544254790569986 0.903606 0.00000003274 0.61878125609 0.7855633374284 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_72 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8493182826247:ℝ):ℂ) + ((0.5278810991117:ℝ):ℂ) * I)‖ ≤ 0.00000016129 := by
  have hl := lg_72
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.258046360779885488 106.25804642289493518 0.5561038 0.00000006128 0.8493182826247 0.5278810991117 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_73 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9773175795026:ℝ):ℂ) + ((0.2117790093354:ℝ):ℂ) * I)‖ ≤ 0.00000017959 := by
  have hl := lg_73
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.600755242479880898 106.600755304594955436 0.2133949 0.00000007958 0.9773175795026 0.2117790093354 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_74 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9922411058522:ℝ):ℂ) + (((-0.1243285480378):ℝ):ℂ) * I)‖ ≤ 0.00000014861 := by
  have hl := lg_74
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.938801273457765932 106.93880133557284047 (-0.1246511) 0.0000000486 0.9922411058522 (-0.1243285480378) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_75 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8968681101232:ℝ):ℂ) + (((-0.4422980816645):ℝ):ℂ) * I)‖ ≤ 0.00000017671 := by
  have hl := lg_75
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.272309636630116372 107.27230969874519091 (-0.4581594) 0.0000000767 0.8968681101232 (-0.4422980816645) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_76 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7057959107512:ℝ):ℂ) + (((-0.7084152259564):ℝ):ℂ) * I)‖ ≤ 0.00000018054 := by
  have hl := lg_76
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.601400540461138138 107.601400602576212676 (-0.7872503) 0.00000008053 0.7057959107512 (-0.7084152259564) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_77 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4428339950616:ℝ):ℂ) + (((-0.8966036207923):ℝ):ℂ) * I)‖ ≤ 0.00000014298 := by
  have hl := lg_77
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.92618947908356593 107.926189541198665314 (-1.1120393) 0.00000004297 0.4428339950616 (-0.8966036207923) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_78 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1377199180892:ℝ):ℂ) + (((-0.9904712131917):ℝ):ℂ) * I)‖ ≤ 0.00000014643 := by
  have hl := lg_78
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.246787475636560944 108.246787537751635482 (-1.4326373) 0.00000004642 0.1377199180892 (-0.9904712131917) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_79 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1774106858548):ℝ):ℂ) + (((-0.9841369053865):ℝ):ℂ) * I)‖ ≤ 0.00000015018 := by
  have hl := lg_79
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.563301310102561878 108.563301372217661262 (-1.7491511) 0.00000005017 (-0.1774106858548) (-0.9841369053865) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p846_80 : ‖exp (-((((((24846:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4714084849293):ℝ):ℂ) + (((-0.8819149847527):ℝ):ℂ) * I)‖ ≤ 0.00000017886 := by
  have hl := lg_80
  refine (ecis_approx ((((24846:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.875833726355636814 108.87583380089366166 (-2.0616835) 0.00000007885 (-0.4714084849293) (-0.8819149847527) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_2 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0284018533536):ℝ):ℂ) + ((0.9995965859915:ℝ):ℂ) * I)‖ ≤ 0.00000014543 := by
  have hl := lg_2
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.2503538761261 17.2503538885696 1.599202 0.00000004542 (-0.0284018533536) 0.9995965859915 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_3 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5952899651876):ℝ):ℂ) + (((-0.8035109565745):ℝ):ℂ) * I)‖ ≤ 0.00000010712 := by
  have hl := lg_3
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.341164021613977468 27.341164034057502355 (-2.2084228) 0.00000000711 (-0.5952899651876) (-0.8035109565745) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_4 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9983866631012):ℝ):ℂ) + (((-0.0567808980462):ℝ):ℂ) * I)‖ ≤ 0.00000014126 := by
  have hl := lg_4
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.5007077522522 34.5007077771392 (-3.0847812) 0.00000004125 (-0.9983866631012) (-0.0567808980462) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_5 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7062400519853):ℝ):ℂ) + (((-0.7079724492853):ℝ):ℂ) * I)‖ ≤ 0.00000012928 := by
  have hl := lg_5
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.054081313808919383 40.05408133869594427 (-2.3549695) 0.00000002927 (-0.7062400519853) (-0.7079724492853) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_6 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8200941472995:ℝ):ℂ) + (((-0.5722286165206):ℝ):ℂ) * I)‖ ≤ 0.00000015253 := by
  have hl := lg_6
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.591517897740077468 44.591517922627102355 (-0.6092208) 0.00000005252 0.8200941472995 (-0.5722286165206) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_7 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2636655652951):ℝ):ℂ) + ((0.9646141558552:ℝ):ℂ) * I)‖ ≤ 0.00000013407 := by
  have hl := lg_7
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.427865866601047314 48.427865891488097088 1.8376166 0.00000003406 (-0.2636655652951) 0.9646141558552 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_8 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.085114023696:ℝ):ℂ) + (((-0.9963712174537):ℝ):ℂ) * I)‖ ≤ 0.00000012907 := by
  have hl := lg_8
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.7510616283783 51.7510616657088 (-1.4855792) 0.00000002906 0.085114023696 (-0.9963712174537) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_9 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2912597078238):ℝ):ℂ) + ((0.9566440208337:ℝ):ℂ) * I)‖ ≤ 0.0000001214 := by
  have hl := lg_9
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.682328043227954936 54.68232806811500471 1.8663397 0.00000002139 (-0.2912597078238) 0.9566440208337 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_10 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7277454382694:ℝ):ℂ) + (((-0.6858473424007):ℝ):ℂ) * I)‖ ≤ 0.00000016266 := by
  have hl := lg_10
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.304435189935019383 57.30443522726554427 (-0.7557674) 0.00000006265 0.7277454382694 (-0.6858473424007) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_11 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999042179761):ℝ):ℂ) + (((-0.0138403113977):ℝ):ℂ) * I)‖ ≤ 0.00000012991 := by
  have hl := lg_11
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.676419634725230771 59.676419672055780545 (-3.1277519) 0.0000000299 (-0.9999042179761) (-0.0138403113977) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_12 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5487054941715:ℝ):ℂ) + ((0.836015717954:ℝ):ℂ) * I)‖ ≤ 0.00000013942 := by
  have hl := lg_12
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.841871773866177468 61.841871811196702355 0.9899813 0.00000003941 0.5487054941715 0.836015717954 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_13 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5385832338741:ℝ):ℂ) + (((-0.8425723115494):ℝ):ℂ) * I)‖ ≤ 0.00000013207 := by
  have hl := lg_13
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.8338946397374679 63.833894677068017674 (-1.0020416) 0.00000003206 0.5385832338741 (-0.8425723115494) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_14 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9567364241024):ℝ):ℂ) + (((-0.2909560354642):ℝ):ℂ) * I)‖ ≤ 0.00000012908 := by
  have hl := lg_14
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.678219742727147314 65.678219780057697088 (-2.8463667) 0.00000002907 (-0.9567364241024) (-0.2909560354642) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_15 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1484459969066):ℝ):ℂ) + ((0.9889205155126:ℝ):ℂ) * I)‖ ≤ 0.00000014357 := by
  have hl := lg_15
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.395245335422896851 67.395245372753446625 1.719793 0.00000004356 (-0.1484459969066) 0.9889205155126 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_16 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9935518713277:ℝ):ℂ) + ((0.1133784767103:ℝ):ℂ) * I)‖ ≤ 0.00000017449 := by
  have hl := lg_16
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.0014155045044 69.0014155542784 0.1136228 0.00000007448 0.9935518713277 0.1133784767103 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_17 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1747523347748:ℝ):ℂ) + (((-0.9846124219665):ℝ):ℂ) * I)‖ ≤ 0.00000013846 := by
  have hl := lg_17
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.510180467649992958 70.510180517424017845 (-1.3951421) 0.00000003845 0.1747523347748 (-0.9846124219665) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_18 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9479857793708):ℝ):ℂ) + (((-0.3183126794719):ℝ):ℂ) * I)‖ ≤ 0.00000015964 := by
  have hl := lg_18
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.932681919354054936 71.93268195668460471 (-2.8176436) 0.00000005963 (-0.9479857793708) (-0.3183126794719) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_19 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5219832690699):ℝ):ℂ) + ((0.8529557238239:ℝ):ℂ) * I)‖ ≤ 0.00000013106 := by
  have hl := lg_19
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.278252855107388861 73.278252892437963522 2.1199708 0.00000003105 (-0.5219832690699) 0.8529557238239 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_20 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6649013427587:ℝ):ℂ) + ((0.7469311912069:ℝ):ℂ) * I)‖ ≤ 0.0000001297 := by
  have hl := lg_20
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.554789066061119383 74.55478911583514427 0.8434346 0.00000002969 0.6649013427587 0.7469311912069 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_21 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9320355082894:ℝ):ℂ) + (((-0.3623669566721):ℝ):ℂ) * I)‖ ≤ 0.00000013941 := by
  have hl := lg_21
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.769029888215024782 75.769029925545599443 (-0.3708062) 0.0000000394 0.9320355082894 (-0.3623669566721) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_22 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0422339612008:ℝ):ℂ) + (((-0.9991077482039):ℝ):ℂ) * I)‖ ≤ 0.00000017449 := by
  have hl := lg_22
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.926773510851330771 76.926773560625380545 (-1.5285498) 0.00000007448 0.0422339612008 (-0.9991077482039) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_23 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8743159136465):ℝ):ℂ) + (((-0.4853572736171):ℝ):ℂ) * I)‖ ≤ 0.00000016022 := by
  have hl := lg_23
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.033044525951651642 78.033044575725726303 (-2.6348209) 0.00000006021 (-0.8743159136465) (-0.4853572736171) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_24 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8512627104634):ℝ):ℂ) + ((0.5247397428248:ℝ):ℂ) * I)‖ ≤ 0.00000014336 := by
  have hl := lg_24
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.092225649992277468 79.092225699766302355 2.5891833 0.00000004335 (-0.8512627104634) 0.5247397428248 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_25 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0024499707542):ℝ):ℂ) + ((0.999996998817:ℝ):ℂ) * I)‖ ≤ 0.00000016573 := by
  have hl := lg_25
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.108162627617838766 80.10816267739188854 1.5732463 0.00000006572 (-0.0024499707542) 0.999996998817 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_26 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.826935587819:ℝ):ℂ) + ((0.5622966597788:ℝ):ℂ) * I)‖ ≤ 0.00000017232 := by
  have hl := lg_26
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.0842485158635679 81.084248565637617674 0.5971605 0.00000007231 0.826935587819 0.5622966597788 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_27 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9420579336196:ℝ):ℂ) + (((-0.3354502194133):ℝ):ℂ) * I)‖ ≤ 0.00000012851 := by
  have hl := lg_27
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.023492064841932404 82.023492102172507065 (-0.3420831) 0.0000000285 0.9420579336196 (-0.3354502194133) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_28 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3180117474558:ℝ):ℂ) + (((-0.9480867726533):ℝ):ℂ) * I)‖ ≤ 0.0000001745 := by
  have hl := lg_28
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.928573618853247314 82.928573668627297088 (-1.2471647) 0.00000007449 0.3180117474558 (-0.9480867726533) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_29 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5224194876197):ℝ):ℂ) + (((-0.852688617813):ℝ):ℂ) * I)‖ ≤ 0.00000015145 := by
  have hl := lg_29
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.801891294996323804 83.801891344770398465 (-2.1204823) 0.00000005144 (-0.5224194876197) (-0.852688617813) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_30 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9843054106255):ℝ):ℂ) + (((-0.1764733924957):ℝ):ℂ) * I)‖ ≤ 0.000000168 := by
  have hl := lg_30
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.645599211548996851 84.645599261323046625 (-2.9641902) 0.00000006799 (-0.9843054106255) (-0.1764733924957) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_31 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8029084215174):ℝ):ℂ) + ((0.5961023960748:ℝ):ℂ) * I)‖ ≤ 0.00000016838 := by
  have hl := lg_31
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.461639532144748981 85.461639581918823642 2.5029547 0.00000006837 (-0.8029084215174) 0.5961023960748 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_32 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1415515517863):ℝ):ℂ) + ((0.9899308855603:ℝ):ℂ) * I)‖ ≤ 0.00000014235 := by
  have hl := lg_32
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.2517693806305 86.251769442848 1.7128249 0.00000004234 (-0.1415515517863) 0.9899308855603 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_33 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5841121110451:ℝ):ℂ) + ((0.8116729894055:ℝ):ℂ) * I)‖ ≤ 0.00000014419 := by
  have hl := lg_33
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.017583656339208239 87.0175837061132829 0.9470106 0.00000004418 0.5841121110451 0.8116729894055 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_34 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9792519253372:ℝ):ℂ) + ((0.2026466548537:ℝ):ℂ) * I)‖ ≤ 0.00000015675 := by
  have hl := lg_34
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.760534343776092958 87.760534405993617845 0.2040599 0.00000005674 0.9792519253372 0.2026466548537 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_35 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8691314290917:ℝ):ℂ) + (((-0.4945811955231):ℝ):ℂ) * I)‖ ≤ 0.00000012968 := by
  have hl := lg_35
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.481947180409966697 88.481947230184041358 (-0.5173529) 0.00000002967 0.8691314290917 (-0.4945811955231) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_36 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3451089147261:ℝ):ℂ) + (((-0.9385626441408):ℝ):ℂ) * I)‖ ≤ 0.00000014475 := by
  have hl := lg_36
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.183035795480154936 89.18303584525420471 (-1.2184415) 0.00000004474 0.3451089147261 (-0.9385626441408) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_37 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3235921770948):ℝ):ℂ) + (((-0.9461966512946):ℝ):ℂ) * I)‖ ≤ 0.00000013443 := by
  have hl := lg_37
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.864914066099748054 89.864914115873822715 (-1.9003198) 0.00000003442 (-0.3235921770948) (-0.9461966512946) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_38 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8377863333436):ℝ):ℂ) + (((-0.5459982230704):ℝ):ℂ) * I)‖ ≤ 0.0000001693 := by
  have hl := lg_38
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.528606731233488861 90.528606781007563522 (-2.5640125) 0.00000006929 (-0.8377863333436) (-0.5459982230704) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_39 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.997629277841):ℝ):ℂ) + ((0.0688173194777:ℝ):ℂ) * I)‖ ≤ 0.00000014636 := by
  have hl := lg_39
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.175058661351445368 91.175058711125520029 3.0727209 0.00000004635 (-0.997629277841) 0.0688173194777 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_40 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7655142991258):ℝ):ℂ) + ((0.6434188820636:ℝ):ℂ) * I)‖ ≤ 0.00000016552 := by
  have hl := lg_40
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.805142942187219383 91.80514300440474427 2.4426366 0.00000006551 (-0.7655142991258) 0.6434188820636 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_41 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2544851354538):ℝ):ℂ) + ((0.9670766856004:ℝ):ℂ) * I)‖ ≤ 0.00000014626 := by
  have hl := lg_41
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.41966799172378246 92.419668053941332234 1.8281116 0.00000004625 (-0.2544851354538) 0.9670766856004 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_42 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3357492369388:ℝ):ℂ) + ((0.9419514052726:ℝ):ℂ) * I)‖ ≤ 0.00000014337 := by
  have hl := lg_42
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.019383764341124782 93.019383814115199443 1.2283958 0.00000004336 0.3357492369388 0.9419514052726 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_43 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8004250842764:ℝ):ℂ) + ((0.5994328022899:ℝ):ℂ) * I)‖ ≤ 0.00000015432 := by
  have hl := lg_43
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.60498725338862286 93.604987303162722408 0.6427923 0.00000005431 0.8004250842764 0.5994328022899 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_44 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9975051713699:ℝ):ℂ) + ((0.0705934351782:ℝ):ℂ) * I)‖ ≤ 0.00000014152 := by
  have hl := lg_44
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.177127386977430771 94.177127449194980545 0.0706522 0.00000004151 0.9975051713699 0.0705934351782 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_45 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8829768817334:ℝ):ℂ) + (((-0.4694164742788):ℝ):ℂ) * I)‖ ≤ 0.00000015067 := by
  have hl := lg_45
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.736409357036874319 94.73640940681094898 (-0.4886298) 0.00000005066 0.8829768817334 (-0.4694164742788) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_46 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5099937521264:ℝ):ℂ) + (((-0.8601781052736):ℝ):ℂ) * I)‖ ≤ 0.00000015662 := by
  have hl := lg_46
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.283398402077751642 95.283398464295326303 (-1.0356188) 0.00000005661 0.5099937521264 (-0.8601781052736) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_47 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0000474732051):ℝ):ℂ) + (((-0.999999998873):ℝ):ℂ) * I)‖ ≤ 0.0000001763 := by
  have hl := lg_47
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.818623331411857823 95.818623393629457371 (-1.5708438) 0.00000007629 (-0.0000474732051) (-0.999999998873) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_48 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5003505240359):ℝ):ℂ) + (((-0.8658229340291):ℝ):ℂ) * I)‖ ≤ 0.00000018066 := by
  have hl := lg_48
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.342579526118377468 96.342579588335902355 (-2.0947999) 0.00000008065 (-0.5003505240359) (-0.8658229340291) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_49 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8609609865497):ℝ):ℂ) + (((-0.5086709934312):ℝ):ℂ) * I)‖ ≤ 0.00000017451 := by
  have hl := lg_49
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.855731733202094628 96.855731782976194176 (-2.6079522) 0.0000000745 (-0.8609609865497) (-0.5086709934312) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_50 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9995239987039):ℝ):ℂ) + (((-0.0308508573668):ℝ):ℂ) * I)‖ ≤ 0.00000015828 := by
  have hl := lg_50
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 97.358516503743938766 97.35851656596148854 (-3.1107369) 0.00000005827 (-0.9995239987039) (-0.0308508573668) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_51 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8951751770886):ℝ):ℂ) + ((0.4457144850837:ℝ):ℂ) * I)‖ ≤ 0.00000013662 := by
  have hl := lg_51
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.851344489263970426 97.8513445514815202 2.6796204 0.00000003661 (-0.8951751770886) 0.4457144850837 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_52 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5855563247267):ℝ):ℂ) + ((0.8106317231404:ℝ):ℂ) * I)‖ ≤ 0.00000013935 := by
  have hl := lg_52
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.3346023919896679 98.334602454207217674 2.1963625 0.00000003934 (-0.5855563247267) 0.8106317231404 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_53 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1509347358464):ℝ):ℂ) + ((0.9885437296925:ℝ):ℂ) * I)‖ ≤ 0.00000016758 := by
  have hl := lg_53
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.808654820225329478 98.808654882442904139 1.7223101 0.00000006757 (-0.1509347358464) 0.9885437296925 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_54 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3085587028145:ℝ):ℂ) + ((0.9512053021916:ℝ):ℂ) * I)‖ ≤ 0.00000017392 := by
  have hl := lg_54
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.273845940968032404 99.273845990742107065 1.2571189 0.00000007391 0.3085587028145 0.9512053021916 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_55 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6963738529018:ℝ):ℂ) + ((0.7176792159417:ℝ):ℂ) * I)‖ ≤ 0.00000016635 := by
  have hl := lg_55
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.730500948534150154 99.730501010751724815 0.8004639 0.00000006634 0.6963738529018 0.7176792159417 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_56 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.938672143671:ℝ):ℂ) + ((0.3448109724126:ℝ):ℂ) * I)‖ ≤ 0.00000014234 := by
  have hl := lg_56
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.178927494979347314 100.178927557196897088 0.3520374 0.00000004233 0.938672143671 0.3448109724126 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_57 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9960906716481:ℝ):ℂ) + (((-0.0883367072949):ℝ):ℂ) * I)‖ ≤ 0.00000013817 := by
  have hl := lg_57
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.619416876721366329 100.619416926495465877 (-0.088452) 0.00000003816 0.9960906716481 (-0.0883367072949) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_58 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8671823129603:ℝ):ℂ) + (((-0.497990799201):ℝ):ℂ) * I)‖ ≤ 0.00000014377 := by
  have hl := lg_58
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.052245171122423804 101.052245233339998465 (-0.5212803) 0.00000004376 0.8671823129603 (-0.497990799201) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_59 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5843564793003:ℝ):ℂ) + (((-0.8114970764579):ℝ):ℂ) * I)‖ ≤ 0.00000018075 := by
  have hl := lg_59
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.477674334135322904 101.477674396352922452 (-0.9467095) 0.00000008074 0.5843564793003 (-0.8114970764579) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_60 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2043582987624:ℝ):ℂ) + (((-0.9788961567638):ℝ):ℂ) * I)‖ ≤ 0.00000013503 := by
  have hl := lg_60
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.895953087675096851 101.895953149892646625 (-1.3649882) 0.00000003502 0.2043582987624 (-0.9788961567638) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_61 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.204112047457):ℝ):ℂ) + (((-0.9789475328545):ℝ):ℂ) * I)‖ ≤ 0.00000017269 := by
  have hl := lg_61
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.307317825334860121 102.307317887552434782 (-1.7763529) 0.00000007268 (-0.204112047457) (-0.9789475328545) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_62 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5730577449655):ℝ):ℂ) + (((-0.8195149912753):ℝ):ℂ) * I)‖ ≤ 0.00000015563 := by
  have hl := lg_62
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.711993408270848981 102.711993470488423642 (-2.1810285) 0.00000005562 (-0.5730577449655) (-0.8195149912753) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_63 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8459972052556):ℝ):ℂ) + (((-0.533187329771):ℝ):ℂ) * I)‖ ≤ 0.00000014474 := by
  have hl := lg_63
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.11019390982900225 103.110193959603101798 (-2.579229) 0.00000004473 (-0.8459972052556) (-0.533187329771) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_64 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9855112057864):ℝ):ℂ) + (((-0.1696103266471):ℝ):ℂ) * I)‖ ≤ 0.00000015813 := by
  have hl := lg_64
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.5021232567566 103.5021233314176 (-2.9711584) 0.00000005812 (-0.9855112057864) (-0.1696103266471) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_65 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9768870325531):ℝ):ℂ) + ((0.2137562287369:ℝ):ℂ) * I)‖ ≤ 0.00000016852 := by
  have hl := lg_65
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 103.887975953546387283 103.887976015763961944 2.9261742 0.00000006851 (-0.9768870325531) 0.2137562287369 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_66 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8279354717397):ℝ):ℂ) + ((0.5608233719932:ℝ):ℂ) * I)‖ ≤ 0.00000017264 := by
  have hl := lg_66
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.267937532465308239 104.2679375946828829 2.5462127 0.00000007263 (-0.8279354717397) 0.5608233719932 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_67 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5656066351998):ℝ):ℂ) + ((0.8246751689049:ℝ):ℂ) * I)‖ ≤ 0.00000013563 := by
  have hl := lg_67
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.642185186436615219 104.642185248654214767 2.171965 0.00000003562 (-0.5656066351998) 0.8246751689049 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_68 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2303775712442):ℝ):ℂ) + ((0.9731013177807:ℝ):ℂ) * I)‖ ≤ 0.00000017253 := by
  have hl := lg_68
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.010888219902192958 105.010888294563217845 1.803262 0.00000007252 (-0.2303775712442) 0.9731013177807 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_69 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1304816096832:ℝ):ℂ) + ((0.9914507297564:ℝ):ℂ) * I)‖ ≤ 0.0000001745 := by
  have hl := lg_69
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.37420854756562911 105.374208609783228658 1.4399416 0.00000007449 0.1304816096832 0.9914507297564 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_70 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4696967311465:ℝ):ℂ) + ((0.8828278318847:ℝ):ℂ) * I)‖ ≤ 0.00000016553 := by
  have hl := lg_70
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.732301056536066697 105.732301118753641358 1.0818491 0.00000006552 0.4696967311465 0.8828278318847 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_71 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7459500670077:ℝ):ℂ) + ((0.6660018750208:ℝ):ℂ) * I)‖ ≤ 0.00000015449 := by
  have hl := lg_71
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.085314067580875669 106.085314129798475217 0.7288361 0.00000005448 0.7459500670077 0.6660018750208 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_72 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9283822820354:ℝ):ℂ) + ((0.3716266115374:ℝ):ℂ) * I)‖ ≤ 0.00000015046 := by
  have hl := lg_72
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.433389671606254936 106.43338973382380471 0.3807605 0.00000005045 0.9283822820354 0.3716266115374 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_73 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9992974784249:ℝ):ℂ) + ((0.0374773213241:ℝ):ℂ) * I)‖ ≤ 0.00000014255 := by
  have hl := lg_73
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.776664079513676081 106.776664141731250742 0.0374861 0.00000004254 0.9992974784249 0.0374773213241 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_74 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.955005559872:ℝ):ℂ) + (((-0.2965878969437):ℝ):ℂ) * I)‖ ≤ 0.00000017984 := by
  have hl := lg_74
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.115267942225848054 107.115268004443422715 (-0.3011178) 0.00000007983 0.955005559872 (-0.2965878969437) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_75 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8049669881028:ℝ):ℂ) + (((-0.5933196002701):ℝ):ℂ) * I)‖ ≤ 0.00000017284 := by
  have hl := lg_75
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.449326649231816234 107.449326711449390895 (-0.6351765) 0.00000007283 0.8049669881028 (-0.5933196002701) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_76 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5695727265514:ℝ):ℂ) + (((-0.8219409401951):ℝ):ℂ) * I)‖ ≤ 0.00000014754 := by
  have hl := lg_76
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.778960607359588861 107.778960669577163522 (-0.9648104) 0.00000004753 0.5695727265514 (-0.8219409401951) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_77 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2769908715363:ℝ):ℂ) + (((-0.9608725498658):ℝ):ℂ) * I)‖ ≤ 0.00000014151 := by
  have hl := lg_77
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.104285501326278085 108.104285563543877633 (-1.2901353) 0.0000000415 0.2769908715363 (-0.9608725498658) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_78 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0404549303046):ℝ):ℂ) + (((-0.9991813642246):ℝ):ℂ) * I)‖ ≤ 0.00000017766 := by
  have hl := lg_78
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.425412537477545368 108.425412599695120029 (-1.6112623) 0.00000007765 (-0.0404549303046) (-0.9991813642246) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_79 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3499354285993):ℝ):ℂ) + (((-0.9367738231871):ℝ):ℂ) * I)‖ ≤ 0.00000015007 := by
  have hl := lg_79
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.742448672000420891 108.742448734218020439 (-1.9282985) 0.00000005006 (-0.3499354285993) (-0.9367738231871) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p887_80 : ‖exp (-((((((24887:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6214172090564):ℝ):ℂ) + (((-0.78347983527):ℝ):ℂ) * I)‖ ≤ 0.00000017094 := by
  have hl := lg_80
  refine (ecis_approx ((((24887:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 109.055496818313319383 109.05549689297434427 (-2.2413466) 0.00000007093 (-0.6214172090564) (-0.78347983527) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_2 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0076111997166):ℝ):ℂ) + ((0.9999710343998:ℝ):ℂ) * I)‖ ≤ 0.00000013002 := by
  have hl := lg_2
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.2711482915351 17.2711483039936 1.5784076 0.00000003001 (-0.0076111997166) 0.9999710343998 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_3 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6214443170868):ℝ):ℂ) + (((-0.7834583337655):ℝ):ℂ) * I)‖ ≤ 0.00000013847 := by
  have hl := lg_3
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.374122390266222388 27.374122402724747305 (-2.2413812) 0.00000003846 (-0.6214443170868) (-0.7834583337655) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_4 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998841388475):ℝ):ℂ) + (((-0.0152219653949):ℝ):ℂ) * I)‖ ≤ 0.00000015284 := by
  have hl := lg_4
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.5422965830702 34.5422966079872 (-3.1263701) 0.00000005283 (-0.9998841388475) (-0.0152219653949) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_5 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7395868226128):ℝ):ℂ) + (((-0.6730611649665):ℝ):ℂ) * I)‖ ≤ 0.00000013302 := by
  have hl := lg_5
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.102364451166345653 40.10236447608337057 (-2.4032526) 0.00000003301 (-0.7395868226128) (-0.6730611649665) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_6 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7881656387891:ℝ):ℂ) + (((-0.6154631799159):ℝ):ℂ) * I)‖ ≤ 0.00000015648 := by
  have hl := lg_6
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.645270681801322388 44.645270706718347305 (-0.6629735) 0.00000005647 0.7881656387891 (-0.6154631799159) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_7 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.206936827433):ℝ):ℂ) + ((0.9783543067064:ℝ):ℂ) * I)‖ ≤ 0.00000013855 := by
  have hl := lg_7
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.486243171057109974 48.486243195974159808 1.7792393 0.00000003854 (-0.206936827433) 0.9783543067064 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_8 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0228319426232:ℝ):ℂ) + (((-0.9997393172202):ℝ):ℂ) * I)‖ ≤ 0.00000015456 := by
  have hl := lg_8
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.8134448746053 51.8134449119808 (-1.5479624) 0.00000005455 0.0228319426232 (-0.9997393172202) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_9 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2276140119022):ℝ):ℂ) + ((0.9737514372696:ℝ):ℂ) * I)‖ ≤ 0.00000014085 := by
  have hl := lg_9
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.748244780532444776 54.74824480544949461 1.800423 0.00000004084 (-0.2276140119022) 0.9737514372696 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_10 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6786708123785:ℝ):ℂ) + (((-0.7344425970936):ℝ):ℂ) * I)‖ ≤ 0.00000012193 := by
  have hl := lg_10
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.373512742701445653 57.37351278007697057 (-0.824845) 0.00000002192 0.6786708123785 (-0.7344425970936) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_11 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9983128986135):ℝ):ℂ) + ((0.0580633783524:ℝ):ℂ) * I)‖ ≤ 0.00000015848 := by
  have hl := lg_11
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.748356492885786761 59.748356530261336595 3.0834966 0.00000005847 (-0.9983128986135) 0.0580633783524 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_12 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.609446466569:ℝ):ℂ) + ((0.792827222279:ℝ):ℂ) * I)‖ ≤ 0.00000013893 := by
  have hl := lg_12
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.916418973336422388 61.916419010711947305 0.9154341 0.00000003892 0.609446466569 0.792827222279 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_13 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4722188128581:ℝ):ℂ) + (((-0.8814813626974):ℝ):ℂ) * I)‖ ≤ 0.00000015137 := by
  have hl := lg_13
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.9108431204379189 63.910843157813468734 (-1.0789901) 0.00000005136 0.4722188128581 (-0.8814813626974) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_14 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9767509289031):ℝ):ℂ) + (((-0.2143772902662):ℝ):ℂ) * I)‖ ≤ 0.00000012819 := by
  have hl := lg_14
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.757391462592209974 65.757391499967759808 (-2.9255384) 0.00000002818 (-0.9767509289031) (-0.2143772902662) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_15 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0677033437741):ℝ):ℂ) + ((0.997705496247:ℝ):ℂ) * I)‖ ≤ 0.00000013756 := by
  have hl := lg_15
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.476486841432568041 67.476486878808117875 1.6385515 0.00000003755 (-0.0677033437741) 0.997705496247 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_16 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9995365806958:ℝ):ℂ) + ((0.0304404968902:ℝ):ℂ) * I)‖ ≤ 0.00000013701 := by
  have hl := lg_16
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.0845931661404 69.0845932159744 0.0304452 0.000000037 0.9995365806958 0.0304404968902 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_17 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0905336940981:ℝ):ℂ) + (((-0.9958933930059):ℝ):ℂ) * I)‖ ≤ 0.00000013881 := by
  have hl := lg_17
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.595176867940485978 70.595176917774510895 (-1.4801385) 0.0000000388 0.0905336940981 (-0.9958933930059) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_18 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.971990814475):ℝ):ℂ) + (((-0.2350188424265):ℝ):ℂ) * I)‖ ≤ 0.00000013048 := by
  have hl := lg_18
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.019393072067544776 72.01939310944309461 (-2.9043547) 0.00000003047 (-0.971990814475) (-0.2350188424265) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_19 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4447017747331):ℝ):ℂ) + ((0.8956786988339:ℝ):ℂ) * I)‖ ≤ 0.00000016171 := by
  have hl := lg_19
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.366586024458986951 73.366586061834561702 2.0316376 0.0000000617 (-0.4447017747331) 0.8956786988339 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_20 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7292558244282:ℝ):ℂ) + ((0.684241143558:ℝ):ℂ) * I)‖ ≤ 0.00000015193 := by
  have hl := lg_20
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.644661034236545653 74.64466108407057057 0.7535626 0.00000005192 0.7292558244282 0.684241143558 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_21 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8950995503771:ℝ):ℂ) + (((-0.4458663419846):ℝ):ℂ) * I)‖ ≤ 0.00000012485 := by
  have hl := lg_21
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.860365561323332362 75.860365598698907113 (-0.4621419) 0.00000002484 0.8950995503771 (-0.4458663419846) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_22 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0504633307439):ℝ):ℂ) + (((-0.998725914478):ℝ):ℂ) * I)‖ ≤ 0.00000014811 := by
  have hl := lg_22
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.019504784420886761 77.019504834254936595 (-1.6212811) 0.0000000481 (-0.0504633307439) (-0.998725914478) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_23 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9160384469961):ℝ):ℂ) + (((-0.4010904679594):ℝ):ℂ) * I)‖ ≤ 0.00000013377 := by
  have hl := lg_23
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.127109352398332622 78.127109402232407373 (-2.7288857) 0.00000003376 (-0.9160384469961) (-0.4010904679594) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_24 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7974428763266):ℝ):ℂ) + ((0.6033944472298:ℝ):ℂ) * I)‖ ≤ 0.00000012848 := by
  have hl := lg_24
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.187567264871522388 79.187567314705547305 2.4938417 0.00000002847 (-0.7974428763266) 0.6033944472298 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_25 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0939773435278:ℝ):ℂ) + ((0.9955743362017:ℝ):ℂ) * I)‖ ≤ 0.00000015885 := by
  have hl := lg_25
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.204728902332691306 80.20472895216674114 1.4766801 0.00000005884 0.0939773435278 0.9955743362017 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_26 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8778616304748:ℝ):ℂ) + ((0.4789143532409:ℝ):ℂ) * I)‖ ≤ 0.00000016849 := by
  have hl := lg_26
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.1819914119730189 81.181991461807068734 0.4994176 0.00000006848 0.8778616304748 0.4789143532409 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_27 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9043431127394:ℝ):ℂ) + (((-0.4268062024395):ℝ):ℂ) * I)‖ ≤ 0.00000012255 := by
  have hl := lg_27
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.122367170798667164 82.122367208174241915 (-0.4409582) 0.00000002254 0.9043431127394 (-0.4268062024395) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_28 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2218053272455:ℝ):ℂ) + (((-0.975090968477):ℝ):ℂ) * I)‖ ≤ 0.00000013922 := by
  have hl := lg_28
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.028539754127309974 83.028539803961359808 (-1.3471308) 0.00000003921 0.2218053272455 (-0.975090968477) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_29 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6057473934849):ℝ):ℂ) + (((-0.7956570211302):ℝ):ℂ) * I)‖ ≤ 0.00000012638 := by
  have hl := lg_29
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.902910169864724564 83.902910219698799315 (-2.2215012) 0.00000002637 (-0.6057473934849) (-0.7956570211302) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_30 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.997161292654):ℝ):ℂ) + (((-0.0752951254134):ℝ):ℂ) * I)‖ ≤ 0.00000016038 := by
  have hl := lg_30
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.747635132967668041 84.747635182801717875 (-3.0662262) 0.00000006037 (-0.997161292654) (-0.0752951254134) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_31 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.737349876423):ℝ):ℂ) + ((0.6755110359633:ℝ):ℂ) * I)‖ ≤ 0.00000015228 := by
  have hl := lg_31
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.564659148248109871 85.564659198082184622 2.3999351 0.00000005227 (-0.737349876423) 0.6755110359633 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_32 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0380472877027):ℝ):ℂ) + ((0.9992759398175:ℝ):ℂ) * I)‖ ≤ 0.00000014285 := by
  have hl := lg_32
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.3557414576755 86.355741519968 1.6088528 0.00000004284 (-0.0380472877027) 0.9992759398175 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_33 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6658861155403:ℝ):ℂ) + ((0.7460534036721:ℝ):ℂ) * I)‖ ≤ 0.00000013249 := by
  have hl := lg_33
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.122478883152009149 87.1224789329860839 0.8421154 0.00000003248 0.6658861155403 0.7460534036721 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_34 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9951754763294:ℝ):ℂ) + ((0.098111015246:ℝ):ℂ) * I)‖ ≤ 0.00000014105 := by
  have hl := lg_34
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.866325159475585978 87.866325221768110895 0.0982691 0.00000004104 0.9951754763294 0.098111015246 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_35 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8115400401233:ℝ):ℂ) + (((-0.5842968109417):ℝ):ℂ) * I)‖ ≤ 0.00000017156 := by
  have hl := lg_35
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.588607622223455627 88.588607672057530378 (-0.6240133) 0.00000007155 0.8115400401233 (-0.5842968109417) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_36 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2424100513183:ℝ):ℂ) + (((-0.9701738849401):ℝ):ℂ) * I)‖ ≤ 0.00000013693 := by
  have hl := lg_36
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.290541363602644776 89.29054141343669461 (-1.3259471) 0.00000003692 0.2424100513183 (-0.9701738849401) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_37 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4239941474345):ℝ):ℂ) + (((-0.9056649286229):ℝ):ℂ) * I)‖ ≤ 0.00000015278 := by
  have hl := lg_37
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.973241603447881314 89.973241653281956065 (-2.0086473) 0.00000005277 (-0.4239941474345) (-0.9056649286229) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_38 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8922679925205):ℝ):ℂ) + (((-0.4515061787125):ℝ):ℂ) * I)‖ ≤ 0.00000016533 := by
  have hl := lg_38
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.637734315994086951 90.637734365828161702 (-2.67314) 0.00000006532 (-0.8922679925205) (-0.4515061787125) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_39 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9840616337021):ℝ):ℂ) + ((0.1778277276552:ℝ):ℂ) * I)‖ ≤ 0.00000015286 := by
  have hl := lg_39
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.284965510704141288 91.284965560538216039 2.9628141 0.00000005285 (-0.9840616337021) 0.1778277276552 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_40 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6897719082267):ℝ):ℂ) + ((0.724026736108:ℝ):ℂ) * I)‖ ≤ 0.00000018039 := by
  have hl := lg_40
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.915809325771645653 91.91580938806417057 2.3319703 0.00000008038 (-0.6897719082267) 0.724026736108 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_41 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1453909138125):ℝ):ℂ) + ((0.9893742882146:ℝ):ℂ) * I)‖ ≤ 0.00000015402 := by
  have hl := lg_41
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.53107515368591986 92.531075215978469694 1.7167044 0.00000005401 (-0.1453909138125) 0.9893742882146 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_42 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4390406457543:ℝ):ℂ) + ((0.8984672010573:ℝ):ℂ) * I)‖ ≤ 0.00000015485 := by
  have hl := lg_42
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.131513852858432362 93.131513902692507113 1.1162657 0.00000005484 0.4390406457543 0.8984672010573 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_43 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8628291614979:ℝ):ℂ) + ((0.5054956360532:ℝ):ℂ) * I)‖ ≤ 0.00000015088 := by
  have hl := lg_43
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.71782325682823626 93.717823306662335928 0.5299563 0.00000005087 0.8628291614979 0.5054956360532 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_44 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9990810722714:ℝ):ℂ) + (((-0.042860366646):ℝ):ℂ) * I)‖ ≤ 0.00000013175 := by
  have hl := lg_44
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.290653075955986761 94.290653138248536595 (-0.0428735) 0.00000003174 0.9990810722714 (-0.042860366646) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_45 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8237346006202:ℝ):ℂ) + (((-0.5669755794927):ℝ):ℂ) * I)‖ ≤ 0.00000017385 := by
  have hl := lg_45
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.850609231698790429 94.85060928153286518 (-0.6028296) 0.00000007384 0.8237346006202 (-0.5669755794927) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_46 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.408051001775:ℝ):ℂ) + (((-0.912959133779):ℝ):ℂ) * I)‖ ≤ 0.00000016378 := by
  have hl := lg_46
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.398257643933432622 95.398257706226007373 (-1.1504781) 0.00000006377 0.408051001775 (-0.912959133779) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_47 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1152948988556):ℝ):ℂ) + (((-0.9933313074183):ℝ):ℂ) * I)‖ ≤ 0.00000014828 := by
  have hl := lg_47
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.934127759424167693 95.934127821716767361 (-1.6863482) 0.00000004827 (-0.1152948988556) (-0.9933313074183) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_48 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5973074668212):ℝ):ℂ) + (((-0.8020123378526):ℝ):ℂ) * I)‖ ≤ 0.0000001513 := by
  have hl := lg_48
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.458715556406622388 96.458715618699147305 (-2.210936) 0.00000005129 (-0.5973074668212) (-0.8020123378526) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_49 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9143543364466):ℝ):ℂ) + (((-0.4049149877278):ℝ):ℂ) * I)‖ ≤ 0.00000016559 := by
  have hl := lg_49
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.972486342114219948 96.972486391948319616 (-2.7247068) 0.00000006558 (-0.9143543364466) (-0.4049149877278) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_50 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9962607788932):ℝ):ℂ) + ((0.0863971060783:ℝ):ℂ) * I)‖ ≤ 0.0000001413 := by
  have hl := lg_50
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.475877193867791306 97.47587725616034114 3.0550877 0.00000004129 (-0.9962607788932) 0.0863971060783 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_51 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8365026240531):ℝ):ℂ) + ((0.5479629183497:ℝ):ℂ) * I)‖ ≤ 0.00000015668 := by
  have hl := lg_51
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.969299258206708366 97.9692993204992582 2.5616656 0.00000005667 (-0.8365026240531) 0.5479629183497 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_52 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4855820613923):ℝ):ℂ) + ((0.874191089893:ℝ):ℂ) * I)‖ ≤ 0.00000015094 := by
  have hl := lg_52
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.4531397035081189 98.453139765800668734 2.0778252 0.00000005093 (-0.4855820613923) 0.874191089893 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_53 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0323993021882):ℝ):ℂ) + ((0.9994750047987:ℝ):ℂ) * I)‖ ≤ 0.0000001373 := by
  have hl := lg_53
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.927763577592901298 98.927763639885476049 1.6032013 0.00000003729 (-0.0323993021882) 0.9994750047987 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_54 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4199107036983:ℝ):ℂ) + ((0.9075654251455:ℝ):ℂ) * I)‖ ≤ 0.00000015255 := by
  have hl := lg_54
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.393515462333767164 99.393515512167841915 1.1374494 0.00000005254 0.4199107036983 0.9075654251455 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_55 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7774193330061:ℝ):ℂ) + ((0.6289826553001:ℝ):ℂ) * I)‖ ≤ 0.00000017084 := by
  have hl := lg_55
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.850720944052132414 99.850721006344707165 0.6802439 0.00000007083 0.7774193330061 0.6289826553001 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_56 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9733745197382:ℝ):ℂ) + ((0.229220514624:ℝ):ℂ) * I)‖ ≤ 0.00000016923 := by
  have hl := lg_56
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.299688045662409974 100.299688107954959808 0.2312768 0.00000006922 0.9733745197382 0.229220514624 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_57 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9780843525144:ℝ):ℂ) + (((-0.2082090280617):ℝ):ℂ) * I)‖ ≤ 0.0000001497 := by
  have hl := lg_57
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.740708414725209339 100.740708464559309007 (-0.2097435) 0.00000004969 0.9780843525144 (-0.2082090280617) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_58 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8002444388438:ℝ):ℂ) + (((-0.5996739431554):ℝ):ℂ) * I)‖ ≤ 0.00000015349 := by
  have hl := lg_58
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.174058461399824564 101.174058523692399315 (-0.6430936) 0.00000005348 0.8002444388438 (-0.5996739431554) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_59 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4809699777898:ℝ):ℂ) + (((-0.8767370646122):ℝ):ℂ) * I)‖ ≤ 0.00000015747 := by
  have hl := lg_59
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.600000457413502664 101.600000519706102332 (-1.0690356) 0.00000005746 0.4809699777898 (-0.8767370646122) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_60 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0828826380929:ℝ):ℂ) + (((-0.9965593149947):ℝ):ℂ) * I)‖ ≤ 0.00000017194 := by
  have hl := lg_60
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.018783424502768041 102.018783486795317875 (-1.4878185) 0.00000007193 0.0828826380929 (-0.9965593149947) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_61 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3229859771654):ℝ):ℂ) + (((-0.9464037502845):ℝ):ℂ) * I)‖ ≤ 0.00000017367 := by
  have hl := lg_61
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.430644041221067611 102.430644103513642362 (-1.8996792) 0.00000007366 (-0.3229859771654) (-0.9464037502845) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_62 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6698793468948):ℝ):ℂ) + (((-0.7424699728504):ℝ):ℂ) * I)‖ ≤ 0.00000017511 := by
  have hl := lg_62
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 102.835807439783209871 102.835807502075784622 (-2.3048426) 0.0000000751 (-0.6698793468948) (-0.7424699728504) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_63 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9055722301498):ℝ):ℂ) + (((-0.4241920978265):ℝ):ℂ) * I)‖ ≤ 0.0000001633 := by
  have hl := lg_63
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.23448795158955475 103.234488001423654418 (-2.7035231) 0.00000006329 (-0.9055722301498) (-0.4241920978265) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_64 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.998957409078):ℝ):ℂ) + (((-0.0456518812967):ℝ):ℂ) * I)‖ ≤ 0.00000016568 := by
  have hl := lg_64
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 103.6268897492106 103.6268898239616 (-3.0959249) 0.00000006567 (-0.998957409078) (-0.0456518812967) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_65 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9425376818086):ℝ):ℂ) + ((0.3340998625948:ℝ):ℂ) * I)‖ ≤ 0.00000015046 := by
  have hl := lg_65
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.013207571604264553 104.013207633896839304 2.8009426 0.00000005045 (-0.9425376818086) 0.3340998625948 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_66 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7510999859957):ℝ):ℂ) + ((0.6601884662755:ℝ):ℂ) * I)‖ ≤ 0.00000014738 := by
  have hl := lg_66
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.393627174687109149 104.3936272369796839 2.420523 0.00000004737 (-0.7510999859957) 0.6601884662755 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_67 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4573632344397):ℝ):ℂ) + ((0.8892799737867:ℝ):ℂ) * I)‖ ≤ 0.00000015709 := by
  have hl := lg_67
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 104.768325964979352329 104.768326027271951997 2.0458242 0.00000005708 (-0.4573632344397) 0.8892799737867 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_68 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.105682652705):ℝ):ℂ) + ((0.9943999079429:ℝ):ℂ) * I)‖ ≤ 0.00000017106 := by
  have hl := lg_68
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.137473451010685978 105.137473525761710895 1.6766767 0.00000007105 (-0.105682652705) 0.9943999079429 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_69 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2550292243114:ℝ):ℂ) + ((0.9669333455555:ℝ):ℂ) * I)‖ ≤ 0.0000001794 := by
  have hl := lg_69
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.50123174266455501 105.501231804957154678 1.3129184 0.00000007939 0.2550292243114 0.9669333455555 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_70 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5781030931106:ℝ):ℂ) + ((0.8159637331009:ℝ):ℂ) * I)‖ ≤ 0.00000015401 := by
  have hl := lg_70
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 105.859755913758555627 105.859755976051130378 0.9543943 0.000000054 0.5781030931106 0.8159637331009 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_71 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8247956092647:ℝ):ℂ) + ((0.5654309886605:ℝ):ℂ) * I)‖ ≤ 0.00000015821 := by
  have hl := lg_71
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.213194463853123279 106.213194526145722947 0.6009557 0.0000000582 0.8247956092647 0.5654309886605 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_72 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9683007519575:ℝ):ℂ) + ((0.2497872169638:ℝ):ℂ) * I)‖ ≤ 0.00000016693 := by
  have hl := lg_72
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.561689655137744776 106.56168971743029461 0.2524605 0.00000006692 0.9683007519575 0.2497872169638 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_73 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9958416385714:ℝ):ℂ) + (((-0.0911012123266):ℝ):ℂ) * I)‖ ≤ 0.00000015936 := by
  have hl := lg_73
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 106.905377862709135971 106.905377925001710722 (-0.0912277) 0.00000005935 0.9958416385714 (-0.0911012123266) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_74 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9088657996317:ℝ):ℂ) + (((-0.4170886695414):ℝ):ℂ) * I)‖ ≤ 0.00000013524 := by
  have hl := lg_74
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.244389894982981314 107.244389957275556065 (-0.4302397) 0.00000003523 0.9088657996317 (-0.4170886695414) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_75 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7215893245178:ℝ):ℂ) + (((-0.6923213464439):ℝ):ℂ) * I)‖ ≤ 0.00000013285 := by
  have hl := lg_75
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.578851292598913694 107.578851354891488445 (-0.7647011) 0.00000003284 0.7215893245178 (-0.6923213464439) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_76 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4582843305156:ℝ):ℂ) + (((-0.8888056437736):ℝ):ℂ) * I)‖ ≤ 0.00000014778 := by
  have hl := lg_76
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 107.908882607529186951 107.908882669821761702 (-1.0947324) 0.00000004777 0.4582843305156 (-0.8888056437736) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_77 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1497810557827:ℝ):ℂ) + (((-0.9887191893195):ℝ):ℂ) * I)‖ ≤ 0.00000015813 := by
  have hl := lg_77
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.234599663942896735 108.234599726235496403 (-1.4204495) 0.00000005812 0.1497810557827 (-0.9887191893195) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_78 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1703326802379):ℝ):ℂ) + (((-0.9853866134885):ℝ):ℂ) * I)‖ ≤ 0.00000014249 := by
  have hl := lg_78
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.556113802239241288 108.556113864531816039 (-1.7419636) 0.00000004248 (-0.1703326802379) (-0.9853866134885) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_79 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4693774225823):ℝ):ℂ) + (((-0.8829976416531):ℝ):ℂ) * I)‖ ≤ 0.00000014779 := by
  have hl := lg_79
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 108.873532107535439681 108.873532169828039349 (-2.0593819) 0.00000004778 (-0.4693774225823) (-0.8829976416531) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_80 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7187557675035):ℝ):ℂ) + (((-0.6952626458061):ℝ):ℂ) * I)‖ ≤ 0.00000017002 := by
  have hl := lg_80
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 109.186957617306745653 109.18695769205777057 (-2.3728074) 0.00000007001 (-0.7187557675035) (-0.6952626458061) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_81 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((81:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8963837642843):ℝ):ℂ) + (((-0.4432788592016):ℝ):ℂ) * I)‖ ≤ 0.000000161 := by
  have hl := lg_81
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((81:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 109.496489561064889552 109.49648961089898922 (-2.6823394) 0.00000006099 (-0.8963837642843) (-0.4432788592016) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_82 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((82:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9882390298476):ℝ):ℂ) + (((-0.1529170346866):ℝ):ℂ) * I)‖ ≤ 0.00000017685 := by
  have hl := lg_82
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((82:ℕ):ℝ)) (17) 106.81415022205297010764 106.81415022205297010798 109.80222344522101986 109.802223519972069694 (-2.9880733) 0.00000007684 (-0.9882390298476) (-0.1529170346866) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_83 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((83:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9889928569309):ℝ):ℂ) + ((0.1479632675484:ℝ):ℂ) * I)‖ ≤ 0.00000014364 := by
  have hl := lg_83
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((83:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 110.104251385605435308 110.104251460356510059 2.9930841 0.00000004363 (-0.9889928569309) 0.1479632675484 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_84 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((84:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9017828456381):ℝ):ℂ) + ((0.4321894251303:ℝ):ℂ) * I)‖ ≤ 0.00000017747 := by
  have hl := lg_84
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((84:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 110.402662144393532362 110.402662206686107113 2.6946734 0.00000007746 (-0.9017828456381) 0.4321894251303 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_85 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((85:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7372546895991):ℝ):ℂ) + ((0.6756149218551:ℝ):ℂ) * I)‖ ≤ 0.00000016464 := by
  have hl := lg_85
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((85:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 110.697541319106831631 110.697541393857881465 2.3997942 0.00000006463 (-0.7372546895991) 0.6756149218551 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_86 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((86:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.512048159138):ℝ):ℂ) + ((0.8589567408878:ℝ):ℂ) * I)‖ ≤ 0.00000018088 := by
  have hl := lg_86
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((86:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 110.98897154836333626 110.988971610655935928 2.1083639 0.00000008087 (-0.512048159138) 0.8589567408878 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_87 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((87:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2469258418055):ℝ):ℂ) + ((0.9690343794971:ℝ):ℂ) * I)‖ ≤ 0.00000016912 := by
  have hl := lg_87
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((87:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 111.277032560130946952 111.27703262242354662 1.8203029 0.00000006911 (-0.2469258418055) 0.9690343794971 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_88 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((88:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0352549195956:ℝ):ℂ) + ((0.999378352099:ℝ):ℂ) * I)‖ ≤ 0.00000016176 := by
  have hl := lg_88
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((88:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 111.561801367491086761 111.561801442242136595 1.5355341 0.00000006175 0.0352549195956 0.999378352099 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_89 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((89:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3115399704478:ℝ):ℂ) + ((0.9502330486851:ℝ):ℂ) * I)‖ ≤ 0.00000014349 := by
  have hl := lg_89
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((89:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 111.843352385753335322 111.843352460504410073 1.2539831 0.00000004348 0.3115399704478 0.9502330486851 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_90 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((90:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.560689548146:ℝ):ℂ) + ((0.8280261050232:ℝ):ℂ) * I)‖ ≤ 0.00000015631 := by
  have hl := lg_90
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((90:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 112.121757523233890429 112.12175758552646518 0.975578 0.0000000563 0.560689548146 0.8280261050232 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_91 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((91:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7646816244899:ℝ):ℂ) + ((0.6444082659056:ℝ):ℂ) * I)‖ ≤ 0.00000013775 := by
  have hl := lg_91
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((91:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 112.397086291495028874 112.397086353787628542 0.7002492 0.00000003774 0.7646816244899 0.6444082659056 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_92 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((92:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.909826890202:ℝ):ℂ) + ((0.4149879876158:ℝ):ℂ) * I)‖ ≤ 0.000000181 := by
  have hl := lg_92
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((92:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 112.669405935468532622 112.669406010219607373 0.4279296 0.00000008099 0.909826890202 0.4149879876158 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_93 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((93:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9874566253176:ℝ):ℂ) + ((0.1578905098995:ℝ):ℂ) * I)‖ ≤ 0.00000017159 := by
  have hl := lg_93
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((93:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 112.938781538514332259 112.938781600806931927 0.158554 0.00000007158 0.9874566253176 0.1578905098995 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_94 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((94:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9941800674827:ℝ):ℂ) + (((-0.1077311163041):ℝ):ℂ) * I)‖ ≤ 0.00000017829 := by
  have hl := lg_94
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((94:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 113.205276050959267693 113.205276125710367361 (-0.1079406) 0.00000007828 0.9941800674827 (-0.1077311163041) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_95 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((95:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9317421210778:ℝ):ℂ) + (((-0.3631206683865):ℝ):ℂ) * I)‖ ≤ 0.00000015362 := by
  have hl := lg_95
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((95:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 113.468950475625332604 113.468950537917932272 (-0.371615) 0.00000005361 0.9317421210778 (-0.3631206683865) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_96 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((96:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8065353335129:ℝ):ℂ) + (((-0.5911858893743):ℝ):ℂ) * I)‖ ≤ 0.00000018131 := by
  have hl := lg_96
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((96:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 113.729863847941722388 113.729863922692747305 (-0.6325284) 0.0000000813 0.8065353335129 (-0.5911858893743) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_97 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((97:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6288384540269:ℝ):ℂ) + (((-0.7775359790627):ℝ):ℂ) * I)‖ ≤ 0.00000015804 := by
  have hl := lg_97
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((97:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 113.98807341250642207 113.988073487257471904 (-0.8907379) 0.00000005803 0.6288384540269 (-0.7775359790627) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_98 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((98:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4118626837856:ℝ):ℂ) + (((-0.9112459216397):ℝ):ℂ) * I)‖ ≤ 0.00000016672 := by
  have hl := lg_98
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((98:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 114.243634633649319948 114.243634695941919616 (-1.1462991) 0.00000006671 0.4118626837856 (-0.9112459216397) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_99 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((99:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1706906142166:ℝ):ℂ) + (((-0.9853246745202):ℝ):ℂ) * I)‖ ≤ 0.00000015583 := by
  have hl := lg_99
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((99:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 114.496601273418231537 114.496601335710831205 (-1.3992658) 0.00000005582 0.1706906142166 (-0.9853246745202) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_100 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((100:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0788118568512):ℝ):ℂ) + (((-0.9968895080295):ℝ):ℂ) * I)‖ ≤ 0.00000014384 := by
  have hl := lg_100
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((100:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 114.747025485402891306 114.74702556015394114 (-1.64969) 0.00000004383 (-0.0788118568512) (-0.9968895080295) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_101 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((101:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3210387321204):ℝ):ℂ) + (((-0.947066065529):ℝ):ℂ) * I)‖ ≤ 0.00000014998 := by
  have hl := lg_101
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((101:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 114.994957879271253445 114.994957954022353113 (-1.8976224) 0.00000004997 (-0.3210387321204) (-0.947066065529) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_102 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((102:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5415802517404):ℝ):ℂ) + (((-0.8406490533609):ℝ):ℂ) * I)‖ ≤ 0.00000017951 := by
  have hl := lg_102
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((102:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 115.240447549741808366 115.2404476244928582 (-2.1431121) 0.0000000795 (-0.5415802517404) (-0.8406490533609) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_103 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((103:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7280069993214):ℝ):ℂ) + (((-0.6855696966102):ℝ):ℂ) * I)‖ ≤ 0.00000016839 := by
  have hl := lg_103
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((103:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 115.483542160855443154 115.483542235606517905 (-2.3862067) 0.00000006838 (-0.7280069993214) (-0.6855696966102) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_104 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((104:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8704699028214):ℝ):ℂ) + (((-0.4922216453935):ℝ):ℂ) * I)‖ ≤ 0.00000014058 := by
  have hl := lg_104
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((104:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 115.7242879950432189 115.724288069794268734 (-2.6269525) 0.00000004057 (-0.8704699028214) (-0.4922216453935) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_105 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((105:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9620991518634):ℝ):ℂ) + (((-0.2726998748503):ℝ):ℂ) * I)‖ ≤ 0.00000014556 := by
  have hl := lg_105
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((105:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 115.962730012489678015 115.962730074782277683 (-2.8653945) 0.00000004555 (-0.9620991518634) (-0.2726998748503) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_106 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((106:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9991994562721):ℝ):ℂ) + (((-0.0400055744999):ℝ):ℂ) * I)‖ ≤ 0.00000016012 := by
  have hl := lg_106
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((106:ℕ):ℝ)) (18) 113.09733552923255658456 113.09733552923255658492 116.198911869128001298 116.198911943879076049 (-3.1015764) 0.00000006011 (-0.9991994562721) (-0.0400055744999) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_107 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((107:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9812509971232):ℝ):ℂ) + ((0.1927342219541:ℝ):ℂ) * I)‖ ≤ 0.00000016778 := by
  have hl := lg_107
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((107:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 116.432876029424914744 116.432876104176039329 2.9476448 0.00000006777 (-0.9812509971232) 0.1927342219541 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_108 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((108:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9107352024568):ℝ):ℂ) + ((0.4129907878831:ℝ):ℂ) * I)‖ ≤ 0.00000017976 := by
  have hl := lg_108
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((108:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 116.664663753868867164 116.664663816161441915 2.7158571 0.00000007975 (-0.9107352024568) 0.4129907878831 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_109 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((109:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7928121523695):ℝ):ℂ) + ((0.6094660704326:ℝ):ℂ) * I)‖ ≤ 0.00000017501 := by
  have hl := lg_109
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((109:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 116.894315149118233555 116.89431521141085814 2.4862057 0.000000075 (-0.7928121523695) 0.6094660704326 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_110 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((110:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6348816075066):ℝ):ℂ) + ((0.772609438484:ℝ):ℂ) * I)‖ ≤ 0.00000017394 := by
  have hl := lg_110
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((110:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 117.121869235587232414 117.121869310338307165 2.2586516 0.00000007393 (-0.6348816075066) 0.772609438484 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_111 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((111:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4460619761102):ℝ):ℂ) + ((0.8950020745586:ℝ):ℂ) * I)‖ ≤ 0.00000014271 := by
  have hl := lg_111
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((111:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 117.347363993714103702 117.34736405600670337 2.0331568 0.0000000427 (-0.4460619761102) 0.8950020745586 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_112 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((112:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2366225201433):ℝ):ℂ) + ((0.9716016585823:ℝ):ℂ) * I)‖ ≤ 0.00000017555 := by
  have hl := lg_112
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((112:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 117.570836337197509974 117.570836411948559808 1.8096845 0.00000007554 (-0.2366225201433) 0.9716016585823 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_113 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((113:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0174013948703):ℝ):ℂ) + ((0.9998485842648:ℝ):ℂ) * I)‖ ≤ 0.00000017835 := by
  have hl := lg_113
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((113:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 117.792322239993003639 117.792322314744103307 1.5881986 0.00000007834 (-0.0174013948703) 0.9998485842648 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_114 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((114:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2007586018156:ℝ):ℂ) + ((0.9796407422096:ℝ):ℂ) * I)‖ ≤ 0.00000013216 := by
  have hl := lg_114
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((114:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 118.011856706260309339 118.011856768552909007 1.3686641 0.00000003215 0.2007586018156 0.9796407422096 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_115 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((115:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4075315533195:ℝ):ℂ) + ((0.913191126243:ℝ):ℂ) * I)‖ ≤ 0.00000014192 := by
  have hl := lg_115
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((115:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 118.229473803564678275 118.229473878315777943 1.151047 0.00000004191 0.4075315533195 0.913191126243 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_116 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((116:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5935657529936:ℝ):ℂ) + ((0.8047854974297:ℝ):ℂ) * I)‖ ≤ 0.00000018349 := by
  have hl := lg_116
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((116:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 118.445206752934924564 118.445206827685999315 0.935314 0.00000008348 0.5935657529936 0.8047854974297 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_117 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((117:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7508601253632:ℝ):ℂ) + ((0.6604612571071:ℝ):ℂ) * I)‖ ≤ 0.00000013546 := by
  have hl := lg_117
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((117:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 118.659087900970363676 118.659087963262963344 0.7214329 0.00000003545 0.7508601253632 0.6604612571071 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_118 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((118:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8730508620755:ℝ):ℂ) + ((0.4876291544086:ℝ):ℂ) * I)‖ ≤ 0.0000001873 := by
  have hl := lg_118
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((118:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 118.871148748948602664 118.871148823699702332 0.5093721 0.00000008729 0.8730508620755 0.4876291544086 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_119 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((119:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9556018346359:ℝ):ℂ) + ((0.2946610487331:ℝ):ℂ) * I)‖ ≤ 0.00000017735 := by
  have hl := lg_119
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((119:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 119.081420038997595952 119.081420113748670703 0.2991008 0.00000007734 0.9556018346359 0.2946610487331 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p917_120 : ‖exp (-((((((24917:ℤ):ℝ)/1000) * Real.log ((120:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9958996127446:ℝ):ℂ) + ((0.0904652493234:ℝ):ℂ) * I)‖ ≤ 0.00000015439 := by
  have hl := lg_120
  refine (ecis_approx ((((24917:ℤ):ℝ)/1000) * Real.log ((120:ℕ):ℝ)) (19) 119.38052083641214306148 119.38052083641214306186 119.289931716037868041 119.289931790788917875 0.0905891 0.00000005438 0.9958996127446 0.0904652493234 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_2 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0131827449383:ℝ):ℂ) + ((0.9999131038424:ℝ):ℂ) * I)‖ ≤ 0.00000011461 := by
  have hl := lg_2
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.2919427069441 17.2919427194176 1.5576132 0.0000000146 0.0131827449383 0.9999131038424 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_3 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6469236061351):ℝ):ℂ) + (((-0.7625548162648):ℝ):ℂ) * I)‖ ≤ 0.00000014269 := by
  have hl := lg_3
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.407080758918467308 27.407080771391992255 (-2.2743395) 0.00000004268 (-0.6469236061351) (-0.7625548162648) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_4 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996524301667):ℝ):ℂ) + ((0.0263631985353:ℝ):ℂ) * I)‖ ≤ 0.0000001292 := by
  have hl := lg_4
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.5838854138882 34.5838854388352 3.1152264 0.00000002919 (-0.9996524301667) 0.0263631985353 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_5 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7712098243196):ℝ):ℂ) + (((-0.6365810292755):ℝ):ℂ) * I)‖ ≤ 0.00000015457 := by
  have hl := lg_5
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 40.150647588523771923 40.15064761347079687 (-2.4515358) 0.00000005456 (-0.7712098243196) (-0.6365810292755) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_6 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7539603242964:ℝ):ℂ) + (((-0.6569199566057):ℝ):ℂ) * I)‖ ≤ 0.00000014057 := by
  have hl := lg_6
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.699023465862567308 44.699023490809592255 (-0.7167263) 0.00000004056 0.7539603242964 (-0.6569199566057) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_7 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1495030679172):ℝ):ℂ) + ((0.9887612617223:ℝ):ℂ) * I)‖ ≤ 0.00000014304 := by
  have hl := lg_7
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.544620475513172634 48.544620500460222528 1.720862 0.00000004303 (-0.1495030679172) 0.9887612617223 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_8 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0395390638002):ℝ):ℂ) + (((-0.9992180254747):ℝ):ℂ) * I)‖ ≤ 0.00000013662 := by
  have hl := lg_8
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.8758281208323 51.8758281582528 (-1.6103457) 0.00000003661 (-0.0395390638002) (-0.9992180254747) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_9 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1629795898994):ℝ):ℂ) + ((0.9866294407099:ℝ):ℂ) * I)‖ ≤ 0.00000014679 := by
  have hl := lg_9
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.814161517836934616 54.81416154278398451 1.7345062 0.00000004678 (-0.1629795898994) 0.9866294407099 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_10 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6263591283978:ℝ):ℂ) + (((-0.7795346318623):ℝ):ℂ) * I)‖ ≤ 0.00000016829 := by
  have hl := lg_10
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.442590295467871923 57.44259033288839687 (-0.8939225) 0.00000006828 0.6263591283978 (-0.7795346318623) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_11 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9915576210784):ℝ):ℂ) + ((0.12966681787:ℝ):ℂ) * I)‖ ≤ 0.00000012076 := by
  have hl := lg_11
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 59.820293351046342751 59.820293388466892645 3.0115597 0.00000002075 (-0.9915576210784) 0.12966681787 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_12 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6668021394345:ℝ):ℂ) + ((0.7452347998085:ℝ):ℂ) * I)‖ ≤ 0.00000013845 := by
  have hl := lg_12
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.990966172806667308 61.990966210227192255 0.8408869 0.00000003844 0.6668021394345 0.7452347998085 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_13 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4030598212909:ℝ):ℂ) + (((-0.9151736340504):ℝ):ℂ) * I)‖ ≤ 0.00000016678 := by
  have hl := lg_13
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.9877916011383699 63.987791638558919794 (-1.1559385) 0.00000006677 0.4030598212909 (-0.9151736340504) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_14 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9906462018189):ℝ):ℂ) + (((-0.1364554960705):ℝ):ℂ) * I)‖ ≤ 0.0000001481 := by
  have hl := lg_14
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.836563182457272634 65.836563219877822528 (-3.0047101) 0.00000004809 (-0.9906462018189) (-0.1364554960705) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_15 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0134859179808:ℝ):ℂ) + ((0.9999090608731:ℝ):ℂ) * I)‖ ≤ 0.00000013155 := by
  have hl := lg_15
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.557728347442239231 67.557728384862789125 1.55731 0.00000003154 0.0134859179808 0.9999090608731 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_16 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9986099638747:ℝ):ℂ) + (((-0.052708064375):ℝ):ℂ) * I)‖ ≤ 0.00000015121 := by
  have hl := lg_16
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.1677708277764 69.1677708776704 (-0.0527325) 0.0000000512 0.9986099638747 (-0.052708064375) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_17 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0056613965518:ℝ):ℂ) + (((-0.999983974166):ℝ):ℂ) * I)‖ ≤ 0.00000013916 := by
  have hl := lg_17
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.680173268230978998 70.680173318125003945 (-1.5651349) 0.00000003915 0.0056613965518 (-0.999983974166) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_18 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9886922235202):ℝ):ℂ) + (((-0.1499589502421):ℝ):ℂ) * I)‖ ≤ 0.00000015421 := by
  have hl := lg_18
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.106104224781034616 72.10610426220158451 (-2.9910659) 0.0000000542 (-0.9886922235202) (-0.1499589502421) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_19 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3639527305313):ℝ):ℂ) + ((0.9314174198157:ℝ):ℂ) * I)‖ ≤ 0.00000014509 := by
  have hl := lg_19
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.454919193810585041 73.454919231231159882 1.9433045 0.00000004508 (-0.3639527305313) 0.9314174198157 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_20 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7877240259276:ℝ):ℂ) + ((0.6160282939739:ℝ):ℂ) * I)‖ ≤ 0.00000016617 := by
  have hl := lg_20
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.734533002411971923 74.73453305230599687 0.6636907 0.00000006616 0.7877240259276 0.6160282939739 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_21 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8507016735325:ℝ):ℂ) + (((-0.5256488016243):ℝ):ℂ) * I)‖ ≤ 0.00000015174 := by
  have hl := lg_21
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.951701234431639942 75.951701271852214783 (-0.5534776) 0.00000005173 0.8507016735325 (-0.5256488016243) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_22 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1427269946318):ℝ):ℂ) + (((-0.9897620951536):ℝ):ℂ) * I)‖ ≤ 0.00000012818 := by
  have hl := lg_22
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.112236057990442751 77.112236107884492645 (-1.7140124) 0.00000002817 (-0.1427269946318) (-0.9897620951536) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_23 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9496616758795):ℝ):ℂ) + (((-0.3132773550118):ℝ):ℂ) * I)‖ ≤ 0.0000001426 := by
  have hl := lg_23
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.221174178845013602 78.221174228739088443 (-2.8229505) 0.00000004259 (-0.9496616758795) (-0.3132773550118) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_24 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7363797592346):ℝ):ℂ) + ((0.6765684371584:ℝ):ℂ) * I)‖ ≤ 0.00000013633 := by
  have hl := lg_24
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.282908879750767308 79.282908929644792255 2.3985001 0.00000003632 (-0.7363797592346) 0.6765684371584 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_25 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1895290951383:ℝ):ℂ) + ((0.9818751051412:ℝ):ℂ) * I)‖ ≤ 0.00000013362 := by
  have hl := lg_25
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.301295177047543846 80.30129522694159374 1.3801138 0.00000003361 0.1895290951383 0.9818751051412 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_26 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9204075437971:ℝ):ℂ) + ((0.3909602963492:ℝ):ℂ) * I)‖ ≤ 0.00000016466 := by
  have hl := lg_26
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.2797343080824699 81.279734357976519794 0.4016747 0.00000006465 0.9204075437971 0.3909602963492 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_27 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8577943759158:ℝ):ℂ) + (((-0.513993004473):ℝ):ℂ) * I)‖ ≤ 0.00000012086 := by
  have hl := lg_27
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.221242276755401924 82.221242314175976765 (-0.5398333) 0.00000002085 0.8577943759158 (-0.513993004473) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_28 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1233842026058:ℝ):ℂ) + (((-0.9923589766547):ℝ):ℂ) * I)‖ ≤ 0.00000014598 := by
  have hl := lg_28
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.128505889401372634 83.128505939295422528 (-1.4470969) 0.00000004597 0.1233842026058 (-0.9923589766547) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_29 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6828990123543):ℝ):ℂ) + (((-0.7305127917459):ℝ):ℂ) * I)‖ ≤ 0.00000014862 := by
  have hl := lg_29
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.003929044733125324 84.003929094627200165 (-2.3225201) 0.00000004861 (-0.6828990123543) (-0.7305127917459) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_30 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996443908962):ℝ):ℂ) + ((0.0266662919361:ℝ):ℂ) * I)‖ ≤ 0.00000014614 := by
  have hl := lg_30
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 84.849671054386339231 84.849671104280389125 3.1149232 0.00000004613 (-0.9996443908962) 0.0266662919361 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_31 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6639727276788):ℝ):ℂ) + ((0.7477567899259:ℝ):ℂ) * I)‖ ≤ 0.00000013618 := by
  have hl := lg_31
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.667678764351470761 85.667678814245545602 2.2969155 0.00000003617 (-0.6639727276788) 0.7477567899259 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_32 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0658679046934:ℝ):ℂ) + ((0.9978283515371:ℝ):ℂ) * I)‖ ≤ 0.00000016581 := by
  have hl := lg_32
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.4597135347205 86.459713597088 1.5048807 0.0000000658 0.0658679046934 0.9978283515371 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_33 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7403400886746:ℝ):ℂ) + ((0.6722325141656:ℝ):ℂ) * I)‖ ≤ 0.00000015936 := by
  have hl := lg_33
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.227374109964810059 87.2273741598588849 0.7372202 0.00000005935 0.7403400886746 0.6722325141656 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_34 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9999717121479:ℝ):ℂ) + (((-0.0075216290756):ℝ):ℂ) * I)‖ ≤ 0.00000013704 := by
  have hl := lg_34
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.972115975175078998 87.972116037542603945 (-0.0075217) 0.00000003703 0.9999717121479 (-0.0075216290756) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_35 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7447248964618:ℝ):ℂ) + (((-0.6673715820965):ℝ):ℂ) * I)‖ ≤ 0.00000013649 := by
  have hl := lg_35
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.695268064036944557 88.695268113931019398 (-0.7306738) 0.00000003648 0.7447248964618 (-0.6673715820965) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_36 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.136912242168:ℝ):ℂ) + (((-0.9905831807296):ℝ):ℂ) * I)‖ ≤ 0.0000001688 := by
  have hl := lg_36
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.398046931725134616 89.39804698161918451 (-1.4334527) 0.00000006879 0.136912242168 (-0.9905831807296) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_37 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5194255603325):ℝ):ℂ) + (((-0.8545157033467):ℝ):ℂ) * I)‖ ≤ 0.00000015973 := by
  have hl := lg_37
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.081569140796014574 90.081569190690089415 (-2.1169749) 0.00000005972 (-0.5194255603325) (-0.8545157033467) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_38 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9361343766562):ℝ):ℂ) + (((-0.3516424727918):ℝ):ℂ) * I)‖ ≤ 0.00000015015 := by
  have hl := lg_38
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.746861900754685041 90.746861950648759882 (-2.7822676) 0.00000005014 (-0.9361343766562) (-0.3516424727918) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_39 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.958618944853):ℝ):ℂ) + ((0.2846923222364:ℝ):ℂ) * I)‖ ≤ 0.00000014765 := by
  have hl := lg_39
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.394872360056837208 91.394872409950912049 2.8529072 0.00000004764 (-0.958618944853) 0.2846923222364 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_40 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6055903985656):ℝ):ℂ) + ((0.7957765196037:ℝ):ℂ) * I)‖ ≤ 0.00000016404 := by
  have hl := lg_40
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.026475709356071923 92.02647577172359687 2.2213039 0.00000006403 (-0.6055903985656) 0.7957765196037 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_41 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0344941290958):ℝ):ℂ) + ((0.9994049004571:ℝ):ℂ) * I)‖ ≤ 0.00000017034 := by
  have hl := lg_41
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.64248231564805726 92.642482378015607154 1.6052973 0.00000007033 (-0.0344941290958) 0.9994049004571 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_42 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.536817707944:ℝ):ℂ) + ((0.8436982567469:ℝ):ℂ) * I)‖ ≤ 0.00000016633 := by
  have hl := lg_42
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.243643941375739942 93.243643991269814783 1.0041356 0.00000006632 0.536817707944 0.8436982567469 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_43 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9142593804951:ℝ):ℂ) + ((0.4051293437616:ℝ):ℂ) * I)‖ ≤ 0.00000014744 := by
  have hl := lg_43
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 93.83065926026784966 93.830659310161949448 0.4171203 0.00000004743 0.9142593804951 0.4051293437616 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_44 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9877945550649:ℝ):ℂ) + (((-0.1557623734543):ℝ):ℂ) * I)‖ ≤ 0.00000014277 := by
  have hl := lg_44
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.404178764934542751 94.404178827302092645 (-0.1563992) 0.00000004276 0.9877945550649 (-0.1557623734543) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_45 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7537611115128:ℝ):ℂ) + (((-0.6571485271771):ℝ):ℂ) * I)‖ ≤ 0.00000014858 := by
  have hl := lg_45
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 94.964809106360706539 94.96480915625478138 (-0.7170295) 0.00000004857 0.7537611115128 (-0.6571485271771) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_46 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3007309848666:ℝ):ℂ) + (((-0.9537090094684):ℝ):ℂ) * I)‖ ≤ 0.00000014048 := by
  have hl := lg_46
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 95.513116885789113602 95.513116948156688443 (-1.2653373) 0.00000004047 0.3007309848666 (-0.9537090094684) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_47 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2290058538891):ℝ):ℂ) + (((-0.973425045334):ℝ):ℂ) * I)‖ ≤ 0.00000014213 := by
  have hl := lg_47
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.049632187436477563 96.049632249804077351 (-1.8018526) 0.00000004212 (-0.2290058538891) (-0.973425045334) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_48 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6862171472969):ℝ):ℂ) + (((-0.7273967464418):ℝ):ℂ) * I)‖ ≤ 0.00000014138 := by
  have hl := lg_48
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 96.574851586694867308 96.574851649062392255 (-2.327072) 0.00000004137 (-0.6862171472969) (-0.7273967464418) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_49 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9552976927293):ℝ):ℂ) + (((-0.2956455953466):ℝ):ℂ) * I)‖ ≤ 0.00000015668 := by
  have hl := lg_49
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 97.089240951026345268 97.089241000920445056 (-2.8414614) 0.00000005667 (-0.9552976927293) (-0.2956455953466) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_50 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9792912701172):ℝ):ℂ) + ((0.2024564347021:ℝ):ℂ) * I)‖ ≤ 0.0000001315 := by
  have hl := lg_50
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 97.593237883991643846 97.59323794635919374 2.937727 0.00000003149 (-0.9792912701172) 0.2024564347021 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_51 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.76620508215):ℝ):ℂ) + ((0.6425961189187:ℝ):ℂ) * I)‖ ≤ 0.00000017466 := by
  have hl := lg_51
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.087254027149446306 98.0872540895169962 2.4437109 0.00000007465 (-0.76620508215) 0.6425961189187 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_52 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3787928255126):ℝ):ℂ) + ((0.9254814937844:ℝ):ℂ) * I)‖ ≤ 0.00000016254 := by
  have hl := lg_52
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 98.5716770150265699 98.571677077394119794 1.9592879 0.00000006253 (-0.3787928255126) 0.9254814937844 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_53 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0865952341765:ℝ):ℂ) + ((0.9962435773534:ℝ):ℂ) * I)‖ ≤ 0.00000017993 := by
  have hl := lg_53
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.046872334960473118 99.046872397328047959 1.4840925 0.00000007992 0.0865952341765 0.9962435773534 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_54 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5252564249231:ℝ):ℂ) + ((0.8509439982026:ℝ):ℂ) * I)‖ ≤ 0.00000013119 := by
  have hl := lg_54
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.513184983699501924 99.513185033593576765 1.0177799 0.00000003118 0.5252564249231 0.8509439982026 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_55 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8472424154213:ℝ):ℂ) + ((0.5312064471663:ℝ):ℂ) * I)‖ ≤ 0.00000017532 := by
  have hl := lg_55
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 99.970940939570114674 99.970941001937689515 0.5600239 0.00000007531 0.8472424154213 0.5312064471663 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_56 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9938992869452:ℝ):ℂ) + ((0.1102914657162:ℝ):ℂ) * I)‖ ≤ 0.00000014385 := by
  have hl := lg_56
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.420448596345472634 100.420448658713022528 0.1105163 0.00000004384 0.9938992869452 0.1102914657162 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_57 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9457064198396:ℝ):ℂ) + (((-0.3250221030548):ℝ):ℂ) * I)‖ ≤ 0.00000016216 := by
  have hl := lg_57
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 100.861999952729052349 100.862000002623152137 (-0.3310351) 0.00000006215 0.9457064198396 (-0.3250221030548) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v24p947_58 : ‖exp (-((((((24947:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7214468295047:ℝ):ℂ) + (((-0.6924698348647):ℝ):ℂ) * I)‖ ≤ 0.00000016321 := by
  have hl := lg_58
  refine (ecis_approx ((((24947:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (16) 100.53096491487338363072 100.53096491487338363104 101.295871751677225324 101.295871814044800165 (-0.7649069) 0.0000000632 0.7214468295047 (-0.6924698348647) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
