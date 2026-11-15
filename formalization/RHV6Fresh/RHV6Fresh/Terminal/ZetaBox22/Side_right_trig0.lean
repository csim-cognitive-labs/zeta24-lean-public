/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox22.Base
/-!
# Certificat (V2), côté right (b1), angles 0

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

lemma cs_right_vm1_2 : ‖exp (-((((((-1000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7692388889425:ℝ):ℂ) + ((0.6389612912677:ℝ):ℂ) * I)‖ ≤ 0.00000011971 := by
  have hl := lg_2
  refine (ecis_approx ((((-1000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.6931471808) (-0.6931471803) 0.6931472 0.0000000197 0.7692388889425 0.6389612912677 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_vm1_3 : ‖exp (-((((((-1000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4548324127347:ℝ):ℂ) + ((0.8905770468219:ℝ):ℂ) * I)‖ ≤ 0.00000011161 := by
  have hl := lg_3
  refine (ecis_approx ((((-1000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-1.098612288908165) (-1.098612288408164) 1.0986123 0.0000000116 0.4548324127347 0.8905770468219 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_vm1_4 : ‖exp (-((((((-1000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1834569365231:ℝ):ℂ) + ((0.983027747544:ℝ):ℂ) * I)‖ ≤ 0.00000013941 := by
  have hl := lg_4
  refine (ecis_approx ((((-1000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-1.3862943616) (-1.3862943606) 1.3862944 0.0000000394 0.1834569365231 0.983027747544 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_vm1_5 : ‖exp (-((((((-1000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0386319575092):ℝ):ℂ) + ((0.9992535073037:ℝ):ℂ) * I)‖ ≤ 0.00000011293 := by
  have hl := lg_5
  refine (ecis_approx ((((-1000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-1.60943791291421) (-1.609437911914209) 1.6094379 0.00000001292 (-0.0386319575092) 0.9992535073037 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_vm0p438_2 : ‖exp (-((((((-438:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.954266876541:ℝ):ℂ) + ((0.2989560642247:ℝ):ℂ) * I)‖ ≤ 0.00000013504 := by
  have hl := lg_2
  refine (ecis_approx ((((-438:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.3035984651904) (-0.3035984649714) 0.3035985 0.00000003503 0.954266876541 0.2989560642247 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_vm0p438_3 : ‖exp (-((((((-438:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8864437594156:ℝ):ℂ) + ((0.4628363224652:ℝ):ℂ) * I)‖ ≤ 0.00000011769 := by
  have hl := lg_3
  refine (ecis_approx ((((-438:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-0.48119218254177627) (-0.481192182322775832) 0.4811922 0.00000001768 0.8864437594156 0.4628363224652 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_vm0p438_4 : ‖exp (-((((((-438:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8212506003834:ℝ):ℂ) + ((0.5705676571362:ℝ):ℂ) * I)‖ ≤ 0.0000001304 := by
  have hl := lg_4
  refine (ecis_approx ((((-438:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-0.6071969303808) (-0.6071969299428) 0.6071969 0.00000003039 0.8212506003834 0.5705676571362 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_vm0p438_5 : ‖exp (-((((((-438:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7616544499327:ℝ):ℂ) + ((0.6479834094309:ℝ):ℂ) * I)‖ ≤ 0.00000010587 := by
  have hl := lg_5
  refine (ecis_approx ((((-438:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-0.70493380585642398) (-0.704933805418423542) 0.7049338 0.00000000586 0.7616544499327 0.6479834094309 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v0p124_2 : ‖exp (-((((((124:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9963085463416:ℝ):ℂ) + (((-0.0858445134333):ℝ):ℂ) * I)‖ ≤ 0.00000014966 := by
  have hl := lg_2
  refine (ecis_approx ((((124:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.0859502503572 0.0859502504192 (-0.0859503) 0.00000004965 0.9963085463416 (-0.0858445134333) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v0p124_3 : ‖exp (-((((((124:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9907353207933:ℝ):ℂ) + (((-0.1358069369827):ℝ):ℂ) * I)‖ ≤ 0.00000012384 := by
  have hl := lg_3
  refine (ecis_approx ((((124:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.136227923762612336 0.13622792382461246 (-0.1362279) 0.00000002383 0.9907353207933 (-0.1358069369827) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v0p124_4 : ‖exp (-((((((124:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9852614561323:ℝ):ℂ) + (((-0.1710551462541):ℝ):ℂ) * I)‖ ≤ 0.00000010085 := by
  have hl := lg_4
  refine (ecis_approx ((((124:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.1719005007144 0.1719005008384 (-0.1719005) 0.00000000084 0.9852614561323 (-0.1710551462541) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v0p124_5 : ‖exp (-((((((124:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9801518555693:ℝ):ℂ) + (((-0.1982481778582):ℝ):ℂ) * I)‖ ≤ 0.00000010122 := by
  have hl := lg_5
  refine (ecis_approx ((((124:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 0.199570301077361916 0.19957030120136204 (-0.1995703) 0.00000000121 0.9801518555693 (-0.1982481778582) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v0p686_2 : ‖exp (-((((((686:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8890643990301:ℝ):ℂ) + (((-0.4577821472898):ℝ):ℂ) * I)‖ ≤ 0.00000013433 := by
  have hl := lg_2
  refine (ecis_approx ((((686:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.4754989656858 0.4754989660288 (-0.475499) 0.00000003432 0.8890643990301 (-0.4577821472898) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v0p686_3 : ‖exp (-((((((686:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7291973875753:ℝ):ℂ) + (((-0.6843034195102):ℝ):ℂ) * I)‖ ≤ 0.00000013021 := by
  have hl := lg_3
  refine (ecis_approx ((((686:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 0.753648029848000504 0.75364803019100119 (-0.753648) 0.0000000302 0.7291973875753 (-0.6843034195102) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v0p686_4 : ‖exp (-((((((686:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5808710926451:ℝ):ℂ) + (((-0.8139955612467):ℝ):ℂ) * I)‖ ≤ 0.00000013207 := by
  have hl := lg_4
  refine (ecis_approx ((((686:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 0.9509979313716 0.9509979320576 (-0.9509979) 0.00000003206 0.5808710926451 (-0.8139955612467) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v0p686_5 : ‖exp (-((((((686:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4499612311949:ℝ):ℂ) + (((-0.8930480896466):ℝ):ℂ) * I)‖ ≤ 0.00000010827 := by
  have hl := lg_5
  refine (ecis_approx ((((686:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 1.104074407573147374 1.10407440825914806 (-1.1040744) 0.00000000826 0.4499612311949 (-0.8930480896466) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v1p248_2 : ‖exp (-((((((1248:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6486038107046:ℝ):ℂ) + (((-0.761126202899):ℝ):ℂ) * I)‖ ≤ 0.000000119 := by
  have hl := lg_2
  refine (ecis_approx ((((1248:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 0.8650476810144 0.8650476816384 (-0.8650477) 0.00000001899 0.6486038107046 (-0.761126202899) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v1p248_3 : ‖exp (-((((((1248:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1984029676263:ℝ):ℂ) + (((-0.9801205346472):ℝ):ℂ) * I)‖ ≤ 0.00000013657 := by
  have hl := lg_3
  refine (ecis_approx ((((1248:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.371068135933388672 1.37106813655738992 (-1.3710681) 0.00000003656 0.1984029676263 (-0.9801205346472) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v1p248_4 : ‖exp (-((((((1248:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.158626193479):ℝ):ℂ) + (((-0.9873387112545):ℝ):ℂ) * I)‖ ≤ 0.00000013799 := by
  have hl := lg_4
  refine (ecis_approx ((((1248:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 1.7300953620288 1.7300953632768 (-1.7300954) 0.00000003798 (-0.158626193479) (-0.9873387112545) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v1p248_5 : ‖exp (-((((((1248:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.423931836684):ℝ):ℂ) + (((-0.9056940972767):ℝ):ℂ) * I)‖ ≤ 0.00000011533 := by
  have hl := lg_5
  refine (ecis_approx ((((1248:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 2.008578514068932832 2.00857851531693408 (-2.0085785) 0.00000001532 (-0.423931836684) (-0.9056940972767) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v1p81_2 : ‖exp (-((((((1810:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3109571339648:ℝ):ℂ) + (((-0.9504239374281):ℝ):ℂ) * I)‖ ≤ 0.00000010367 := by
  have hl := lg_2
  refine (ecis_approx ((((1810:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.254596396343 1.254596397248 (-1.2545964) 0.00000000366 0.3109571339648 (-0.9504239374281) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v1p81_3 : ‖exp (-((((((1810:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4056518437206):ℝ):ℂ) + (((-0.9140276700859):ℝ):ℂ) * I)‖ ≤ 0.00000014294 := by
  have hl := lg_3
  refine (ecis_approx ((((1810:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 1.98848824201877684 1.98848824292377865 (-1.9884882) 0.00000004293 (-0.4056518437206) (-0.9140276700859) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v1p81_4 : ‖exp (-((((((1810:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.806611321662):ℝ):ℂ) + (((-0.5910822072393):ℝ):ℂ) * I)‖ ≤ 0.00000010733 := by
  have hl := lg_4
  refine (ecis_approx ((((1810:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (0) 0 0 2.509192792686 2.509192794496 (-2.5091928) 0.00000000732 (-0.806611321662) (-0.5910822072393) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v1p81_5 : ‖exp (-((((((1810:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9740049883168):ℝ):ℂ) + (((-0.2265265601283):ℝ):ℂ) * I)‖ ≤ 0.00000012239 := by
  have hl := lg_5
  refine (ecis_approx ((((1810:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (0) 0 0 2.91308262056471829 2.9130826223747201 (-2.9130826) 0.00000002238 (-0.9740049883168) (-0.2265265601283) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v2p372_2 : ‖exp (-((((((2372:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0732830209752):ℝ):ℂ) + (((-0.9973111845539):ℝ):ℂ) * I)‖ ≤ 0.00000011287 := by
  have hl := lg_2
  refine (ecis_approx ((((2372:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 1.6441451116716 1.6441451128576 (-1.6441451) 0.00000001286 (-0.0732830209752) (-0.9973111845539) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v2p372_3 : ‖exp (-((((((2372:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8599195162869):ℝ):ℂ) + (((-0.5104296478737):ℝ):ℂ) * I)‖ ≤ 0.00000014931 := by
  have hl := lg_3
  refine (ecis_approx ((((2372:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (0) 0 0 2.605908348104165008 2.60590834929016738 (-2.6059083) 0.0000000493 (-0.8599195162869) (-0.5104296478737) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v2p372_4 : ‖exp (-((((((2372:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9892591964509):ℝ):ℂ) + ((0.1461719598231:ℝ):ℂ) * I)‖ ≤ 0.00000011855 := by
  have hl := lg_4
  refine (ecis_approx ((((2372:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.2882902233432 3.2882902257152 2.9948951 0.00000001854 (-0.9892591964509) 0.1461719598231 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v2p372_5 : ‖exp (-((((((2372:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7800853840809):ℝ):ℂ) + ((0.6256730723797:ℝ):ℂ) * I)‖ ≤ 0.00000012227 := by
  have hl := lg_5
  refine (ecis_approx ((((2372:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.817586727060503748 3.81758672943250612 2.4655986 0.00000002226 (-0.7800853840809) 0.6256730723797 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v2p934_2 : ‖exp (-((((((2934:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4465425278859):ℝ):ℂ) + (((-0.8947624102435):ℝ):ℂ) * I)‖ ≤ 0.00000012848 := by
  have hl := lg_2
  refine (ecis_approx ((((2934:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.0336938270002 2.0336938284672 (-2.0336938) 0.00000002847 (-0.4465425278859) (-0.8947624102435) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v2p934_3 : ‖exp (-((((((2934:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9966614923173):ℝ):ℂ) + ((0.081644774618:ℝ):ℂ) * I)‖ ≤ 0.00000014849 := by
  have hl := lg_3
  refine (ecis_approx ((((2934:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.223328454189553176 3.22332845565655611 3.0598569 0.00000004848 (-0.9966614923173) 0.081644774618 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v2p934_4 : ‖exp (-((((((2934:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6011995358404):ℝ):ℂ) + ((0.7990989413665:ℝ):ℂ) * I)‖ ≤ 0.00000014977 := by
  have hl := lg_4
  refine (ecis_approx ((((2934:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.0673876540004 4.0673876569344 2.2157977 0.00000004976 (-0.6011995358404) 0.7990989413665 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v2p934_5 : ‖exp (-((((((2934:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0097016745975:ℝ):ℂ) + ((0.9999529376475:ℝ):ℂ) * I)‖ ≤ 0.00000012933 := by
  have hl := lg_5
  refine (ecis_approx ((((2934:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.722090833556289206 4.72209083649029214 1.5610945 0.00000002932 0.0097016745975 0.9999529376475 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v3p496_2 : ‖exp (-((((((3496:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7528925888707):ℝ):ℂ) + (((-0.6581434111112):ℝ):ℂ) * I)‖ ≤ 0.00000014409 := by
  have hl := lg_2
  refine (ecis_approx ((((3496:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.4232425423288 2.4232425440768 (-2.4232425) 0.00000004408 (-0.7528925888707) (-0.6581434111112) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v3p496_3 : ‖exp (-((((((3496:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7653856643972):ℝ):ℂ) + ((0.6435718955155:ℝ):ℂ) * I)‖ ≤ 0.00000014692 := by
  have hl := lg_3
  refine (ecis_approx ((((3496:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.840748560274941344 3.84074856202294484 2.4424367 0.00000004691 (-0.7653856643972) 0.6435718955155 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v3p496_4 : ‖exp (-((((((3496:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1336946069879:ℝ):ℂ) + ((0.9910225789871:ℝ):ℂ) * I)‖ ≤ 0.00000012254 := by
  have hl := lg_4
  refine (ecis_approx ((((3496:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.8464850846576 4.8464850881536 1.4367002 0.00000002253 0.1336946069879 0.9910225789871 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v3p496_5 : ‖exp (-((((((3496:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.792078118693:ℝ):ℂ) + ((0.6104197358275:ℝ):ℂ) * I)‖ ≤ 0.00000013638 := by
  have hl := lg_5
  refine (ecis_approx ((((3496:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.626594940052074664 5.62659494354807816 0.6565904 0.00000003637 0.792078118693 0.6104197358275 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v4p058_2 : ‖exp (-((((((4058:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9464300767654):ℝ):ℂ) + (((-0.3229088255214):ℝ):ℂ) * I)‖ ≤ 0.00000014236 := by
  have hl := lg_2
  refine (ecis_approx ((((4058:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (0) 0 0 2.8127912576574 2.8127912596864 (-2.8127913) 0.00000004235 (-0.9464300767654) (-0.3229088255214) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v4p058_3 : ‖exp (-((((((4058:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2514908190316):ℝ):ℂ) + ((0.967859684015:ℝ):ℂ) * I)‖ ≤ 0.00000014083 := by
  have hl := lg_3
  refine (ecis_approx ((((4058:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.458168666360329512 4.45816866838933357 1.8250166 0.00000004082 (-0.2514908190316) 0.967859684015 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v4p058_4 : ‖exp (-((((((4058:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7914597239363:ℝ):ℂ) + ((0.6112213227519:ℝ):ℂ) * I)‖ ≤ 0.00000011221 := by
  have hl := lg_4
  refine (ecis_approx ((((4058:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.6255825153148 5.6255825193728 0.6576028 0.0000000122 0.7914597239363 0.6112213227519 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v4p058_5 : ‖exp (-((((((4058:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.96942647155:ℝ):ℂ) + (((-0.2453819803046):ℝ):ℂ) * I)‖ ≤ 0.00000014344 := by
  have hl := lg_5
  refine (ecis_approx ((((4058:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.531099046547860122 6.53109905060586418 (-0.2479137) 0.00000004343 0.96942647155 (-0.2453819803046) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v4p62_2 : ‖exp (-((((((4620:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9981554465973):ℝ):ℂ) + ((0.0607099981673:ℝ):ℂ) * I)‖ ≤ 0.00000013421 := by
  have hl := lg_2
  refine (ecis_approx ((((4620:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.202339972986 3.202339975296 3.0808453 0.0000000342 (-0.9981554465973) 0.0607099981673 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v4p62_3 : ‖exp (-((((((4620:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.355267132451:ℝ):ℂ) + ((0.9347648178018:ℝ):ℂ) * I)‖ ≤ 0.00000013475 := by
  have hl := lg_3
  refine (ecis_approx ((((4620:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.07558877244571768 5.0755887747557223 1.2075965 0.00000003474 0.355267132451 0.9347648178018 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v4p62_4 : ‖exp (-((((((4620:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9926286051732:ℝ):ℂ) + (((-0.1211959248153):ℝ):ℂ) * I)‖ ≤ 0.00000014343 := by
  have hl := lg_4
  refine (ecis_approx ((((4620:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.404679945972 6.404679950592 (-0.1214946) 0.00000004342 0.9926286051732 (-0.1211959248153) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v4p62_5 : ‖exp (-((((((4620:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.406279368421:ℝ):ℂ) + (((-0.9137489123361):ℝ):ℂ) * I)‖ ≤ 0.0000001505 := by
  have hl := lg_5
  refine (ecis_approx ((((4620:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.43560315304364558 7.4356031576636502 (-1.1524178) 0.00000005049 0.406279368421 (-0.9137489123361) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v5p182_2 : ‖exp (-((((((5182:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9003182897513):ℝ):ℂ) + ((0.4352320955795:ℝ):ℂ) * I)‖ ≤ 0.00000011888 := by
  have hl := lg_2
  refine (ecis_approx ((((5182:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.5918886883146 3.5918886909056 2.6912966 0.00000001887 (-0.9003182897513) 0.4352320955795 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v5p182_3 : ‖exp (-((((((5182:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8308425240881:ℝ):ℂ) + ((0.5565075921917:ℝ):ℂ) * I)‖ ≤ 0.00000012866 := by
  have hl := lg_3
  refine (ecis_approx ((((5182:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.693008878531105848 5.69300888112211103 0.5901764 0.00000002865 0.8308425240881 0.5565075921917 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v5p182_4 : ‖exp (-((((((5182:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6211460514718:ℝ):ℂ) + (((-0.7836948275579):ℝ):ℂ) * I)‖ ≤ 0.00000013057 := by
  have hl := lg_4
  refine (ecis_approx ((((5182:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.1837773766292 7.1837773818112 (-0.9005921) 0.00000003056 0.6211460514718 (-0.7836948275579) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v5p182_5 : ‖exp (-((((((5182:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4672039187481):ℝ):ℂ) + (((-0.8841495904548):ℝ):ℂ) * I)‖ ≤ 0.00000014766 := by
  have hl := lg_5
  refine (ecis_approx ((((5182:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.340107259539431038 8.34010726472143622 (-2.056922) 0.00000004765 (-0.4672039187481) (-0.8841495904548) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v5p744_2 : ‖exp (-((((((5744:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6675784209665):ℝ):ℂ) + ((0.7445394897793:ℝ):ℂ) * I)‖ ≤ 0.00000010355 := by
  have hl := lg_2
  refine (ecis_approx ((((5744:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 3.9814374036432 3.9814374065152 2.3017479 0.00000000354 (-0.6675784209665) 0.7445394897793 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v5p744_3 : ‖exp (-((((((5744:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9996289133583:ℝ):ℂ) + (((-0.0272403299922):ℝ):ℂ) * I)‖ ≤ 0.00000012258 := by
  have hl := lg_3
  refine (ecis_approx ((((5744:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.310428984616494016 6.31042898748849976 (-0.0272437) 0.00000002257 0.9996289133583 (-0.0272403299922) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v5p744_4 : ‖exp (-((((((5744:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1086780965769):ℝ):ℂ) + (((-0.9940769946659):ℝ):ℂ) * I)‖ ≤ 0.00000010587 := by
  have hl := lg_4
  refine (ecis_approx ((((5744:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.9628748072864 7.9628748130304 (-1.6796895) 0.00000000586 (-0.1086780965769) (-0.9940769946659) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v5p744_5 : ‖exp (-((((((5744:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9838138609772):ℝ):ℂ) + (((-0.1791934334688):ℝ):ℂ) * I)‖ ≤ 0.00000014116 := by
  have hl := lg_5
  refine (ecis_approx ((((5744:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.244611366035216496 9.24461137177922224 (-2.9614261) 0.00000004115 (-0.9838138609772) (-0.1791934334688) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v6p306_2 : ‖exp (-((((((6306:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3348093288063):ℝ):ℂ) + ((0.9422858978793:ℝ):ℂ) * I)‖ ≤ 0.00000011496 := by
  have hl := lg_2
  refine (ecis_approx ((((6306:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.3709861189718 4.3709861221248 1.9121992 0.00000001495 (-0.3348093288063) 0.9422858978793 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v6p306_3 : ‖exp (-((((((6306:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7993018446929:ℝ):ℂ) + (((-0.6009297472006):ℝ):ℂ) * I)‖ ≤ 0.00000011649 := by
  have hl := lg_3
  refine (ecis_approx ((((6306:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.927849090701882184 6.92784909385488849 (-0.6446638) 0.00000001648 0.7993018446929 (-0.6009297472006) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v6p306_4 : ‖exp (-((((((6306:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.775805422151):ℝ):ℂ) + (((-0.6309722235726):ℝ):ℂ) * I)‖ ≤ 0.00000013709 := by
  have hl := lg_4
  refine (ecis_approx ((((6306:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.7419722379436 8.7419722442496 (-2.4587869) 0.00000003708 (-0.775805422151) (-0.6309722235726) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v6p306_5 : ‖exp (-((((((6306:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7489385493879):ℝ):ℂ) + ((0.6626394564219:ℝ):ℂ) * I)‖ ≤ 0.00000014184 := by
  have hl := lg_5
  refine (ecis_approx ((((6306:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.149115472531001954 10.14911547883700826 2.4172551 0.00000004183 (-0.7489385493879) 0.6626394564219 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v6p868_2 : ‖exp (-((((((6868:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0481272284472:ℝ):ℂ) + ((0.9988412135479:ℝ):ℂ) * I)‖ ≤ 0.00000013057 := by
  have hl := lg_2
  refine (ecis_approx ((((6868:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 4.7605348343004 4.7605348377344 1.5226505 0.00000003056 0.0481272284472 0.9988412135479 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v6p868_3 : ‖exp (-((((((6868:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3038321847254:ℝ):ℂ) + (((-0.9527255656929):ℝ):ℂ) * I)‖ ≤ 0.00000011041 := by
  have hl := lg_3
  refine (ecis_approx ((((6868:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.545269196787270352 7.54526920022127722 (-1.2620839) 0.0000000104 0.3038321847254 (-0.9527255656929) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v6p868_4 : ‖exp (-((((((6868:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9953675299292):ℝ):ℂ) + ((0.096143017844:ℝ):ℂ) * I)‖ ≤ 0.00000014577 := by
  have hl := lg_4
  refine (ecis_approx ((((6868:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.5210696686008 9.5210696754688 3.0453009 0.00000004576 (-0.9953675299292) 0.096143017844 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v6p868_5 : ‖exp (-((((((6868:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0580127373195:ℝ):ℂ) + ((0.9983158429618:ℝ):ℂ) * I)‖ ≤ 0.00000013535 := by
  have hl := lg_5
  refine (ecis_approx ((((6868:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.053619579026787412 11.05361958589479428 1.512751 0.00000003534 0.0580127373195 0.9983158429618 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v7p43_2 : ‖exp (-((((((7430:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4238524542193:ℝ):ℂ) + ((0.9057312499038:ℝ):ℂ) * I)‖ ≤ 0.00000014618 := by
  have hl := lg_2
  refine (ecis_approx ((((7430:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.150083549629 5.150083553344 1.1331018 0.00000004617 0.4238524542193 0.9057312499038 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v7p43_3 : ‖exp (-((((((7430:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3038276558556):ℝ):ℂ) + (((-0.9527270099748):ℝ):ℂ) * I)‖ ≤ 0.00000010432 := by
  have hl := lg_3
  refine (ecis_approx ((((7430:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.16268930287265852 8.16268930658766595 (-1.879504) 0.00000000431 (-0.3038276558556) (-0.9527270099748) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v7p43_4 : ‖exp (-((((((7430:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6406981173236):ℝ):ℂ) + ((0.7677928903306:ℝ):ℂ) * I)‖ ≤ 0.00000011512 := by
  have hl := lg_4
  refine (ecis_approx ((((7430:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.300167099258 10.300167106688 2.2662035 0.00000001511 (-0.6406981173236) 0.7677928903306 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v7p43_5 : ‖exp (-((((((7430:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8206510517391:ℝ):ℂ) + ((0.5714296555828:ℝ):ℂ) * I)‖ ≤ 0.00000012885 := by
  have hl := lg_5
  refine (ecis_approx ((((7430:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.95812368552257287 11.9581236929525803 0.6082469 0.00000002884 0.8206510517391 0.5714296555828 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v7p992_2 : ‖exp (-((((((7992:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.736068157682:ℝ):ℂ) + ((0.6769074288605:ℝ):ℂ) * I)‖ ≤ 0.00000014224 := by
  have hl := lg_2
  refine (ecis_approx ((((7992:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.5396322649576 5.5396322689536 0.743553 0.00000004223 0.736068157682 0.6769074288605 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v7p992_3 : ‖exp (-((((((7992:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7992989881003):ℝ):ℂ) + (((-0.6009335467195):ℝ):ℂ) * I)‖ ≤ 0.00000010579 := by
  have hl := lg_3
  refine (ecis_approx ((((7992:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.780109408958046688 8.78010941295405468 (-2.4969241) 0.00000000578 (-0.7992989881003) (-0.6009335467195) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v7p992_4 : ‖exp (-((((((7992:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0835925658568:ℝ):ℂ) + ((0.9965000165245:ℝ):ℂ) * I)‖ ≤ 0.00000012356 := by
  have hl := lg_4
  refine (ecis_approx ((((7992:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.0792645299152 11.0792645379072 1.4871061 0.00000002355 0.0835925658568 0.9965000165245 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v7p992_5 : ‖exp (-((((((7992:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9564358681401:ℝ):ℂ) + (((-0.2919425116954):ℝ):ℂ) * I)‖ ≤ 0.00000012236 := by
  have hl := lg_5
  refine (ecis_approx ((((7992:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.862627792018358328 12.86262780001036632 (-0.2962572) 0.00000002235 0.9564358681401 (-0.2919425116954) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v8p554_2 : ‖exp (-((((((8554:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9379921196888:ℝ):ℂ) + ((0.3466565784774:ℝ):ℂ) * I)‖ ≤ 0.00000012691 := by
  have hl := lg_2
  refine (ecis_approx ((((8554:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 5.9291809802862 5.9291809845632 0.3540043 0.0000000269 0.9379921196888 0.3466565784774 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v8p554_3 : ‖exp (-((((((8554:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996287835538):ℝ):ℂ) + (((-0.0272450815369):ℝ):ℂ) * I)‖ ≤ 0.00000011216 := by
  have hl := lg_3
  refine (ecis_approx ((((8554:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.397529515043434856 9.39752951932044341 (-3.1143442) 0.00000001215 (-0.9996287835538) (-0.0272450815369) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v8p554_4 : ‖exp (-((((((8554:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7596584331967:ℝ):ℂ) + ((0.6503222777002:ℝ):ℂ) * I)‖ ≤ 0.0000001538 := by
  have hl := lg_4
  refine (ecis_approx ((((8554:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.8583619605724 11.8583619691264 0.7080086 0.00000005379 0.7596584331967 0.6503222777002 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v8p554_5 : ‖exp (-((((((8554:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3616480881818:ℝ):ℂ) + (((-0.9323146788045):ℝ):ℂ) * I)‖ ≤ 0.00000011586 := by
  have hl := lg_5
  refine (ecis_approx ((((8554:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.767131898514143786 13.76713190706815234 (-1.2007613) 0.00000001585 0.3616480881818 (-0.9323146788045) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v9p116_2 : ‖exp (-((((((9116:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9993683643195:ℝ):ℂ) + (((-0.0355369159811):ℝ):ℂ) * I)‖ ≤ 0.00000011158 := by
  have hl := lg_2
  refine (ecis_approx ((((9116:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.3187296956148 6.3187297001728 (-0.0355444) 0.00000001157 0.9993683643195 (-0.0355369159811) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v9p116_3 : ‖exp (-((((((9116:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8308451654776):ℝ):ℂ) + ((0.556503648631:ℝ):ℂ) * I)‖ ≤ 0.00000011134 := by
  have hl := lg_3
  refine (ecis_approx ((((9116:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.014949621128823024 10.01494962568683214 2.551421 0.00000001133 (-0.8308451654776) 0.556503648631 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v9p116_4 : ‖exp (-((((((9116:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9974742552051:ℝ):ℂ) + (((-0.0710289391939):ℝ):ℂ) * I)‖ ≤ 0.00000012314 := by
  have hl := lg_4
  refine (ecis_approx ((((9116:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.6374593912296 12.6374594003456 (-0.0710888) 0.00000002313 0.9974742552051 (-0.0710289391939) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v9p116_5 : ‖exp (-((((((9116:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5093842279261):ℝ):ℂ) + (((-0.8605391962796):ℝ):ℂ) * I)‖ ≤ 0.00000010936 := by
  have hl := lg_5
  refine (ecis_approx ((((9116:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.671636005009929244 14.67163601412593836 (-2.1052654) 0.00000000935 (-0.5093842279261) (-0.8605391962796) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v9p678_2 : ‖exp (-((((((9678:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.911000341941:ℝ):ℂ) + (((-0.4124055976624):ℝ):ℂ) * I)‖ ≤ 0.00000010862 := by
  have hl := lg_2
  refine (ecis_approx ((((9678:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 6.7082784109434 6.7082784157824 (-0.4250931) 0.00000000861 0.911000341941 (-0.4124055976624) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v9p678_3 : ‖exp (-((((((9678:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3552715692244):ℝ):ℂ) + ((0.9347631315464:ℝ):ℂ) * I)‖ ≤ 0.00000011771 := by
  have hl := lg_3
  refine (ecis_approx ((((9678:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.632369727214211192 10.63236973205322087 1.9340009 0.0000000177 (-0.3552715692244) 0.9347631315464 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v9p678_4 : ‖exp (-((((((9678:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6598432460334:ℝ):ℂ) + (((-0.7514032809777):ℝ):ℂ) * I)‖ ≤ 0.00000011722 := by
  have hl := lg_4
  refine (ecis_approx ((((9678:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.4165568218868 13.4165568315648 (-0.8501862) 0.00000001721 0.6598432460334 (-0.7514032809777) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v9p678_5 : ‖exp (-((((((9678:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9913239027868):ℝ):ℂ) + (((-0.1314416955976):ℝ):ℂ) * I)‖ ≤ 0.00000010684 := by
  have hl := lg_5
  refine (ecis_approx ((((9678:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.576140111505714702 15.57614012118372438 (-3.0097695) 0.00000000683 (-0.9913239027868) (-0.1314416955976) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v10p24_2 : ‖exp (-((((((10240:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6861290207596:ℝ):ℂ) + (((-0.72747987386):ℝ):ℂ) * I)‖ ≤ 0.00000012423 := by
  have hl := lg_2
  refine (ecis_approx ((((10240:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.097827126272 7.097827131392 (-0.8146418) 0.00000002422 0.6861290207596 (-0.72747987386) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v10p24_3 : ‖exp (-((((((10240:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2514862251695:ℝ):ℂ) + ((0.9678608776833:ℝ):ℂ) * I)‖ ≤ 0.00000012408 := by
  have hl := lg_3
  refine (ecis_approx ((((10240:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.24978983329959936 11.2497898384196096 1.3165808 0.00000002407 0.2514862251695 0.9678608776833 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v10p24_4 : ‖exp (-((((((10240:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0584539337429):ℝ):ℂ) + (((-0.9982901069477):ℝ):ℂ) * I)‖ ≤ 0.00000014844 := by
  have hl := lg_4
  refine (ecis_approx ((((10240:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.195654252544 14.195654262784 (-1.6292836) 0.00000004843 (-0.0584539337429) (-0.9982901069477) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v10p24_5 : ‖exp (-((((((10240:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7160417855815):ℝ):ℂ) + ((0.6980574197548:ℝ):ℂ) * I)‖ ≤ 0.00000010672 := by
  have hl := lg_5
  refine (ecis_approx ((((10240:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.48064421800150016 16.4806442282415104 2.3689117 0.00000000671 (-0.7160417855815) 0.6980574197548 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v10p802_2 : ‖exp (-((((((10802:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3584488745688:ℝ):ℂ) + (((-0.9335493582668):ℝ):ℂ) * I)‖ ≤ 0.00000013984 := by
  have hl := lg_2
  refine (ecis_approx ((((10802:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.4873758416006 7.4873758470016 (-1.2041905) 0.00000003983 0.3584488745688 (-0.9335493582668) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v10p802_3 : ‖exp (-((((((10802:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7653826097391:ℝ):ℂ) + ((0.6435755283639:ℝ):ℂ) * I)‖ ≤ 0.00000013044 := by
  have hl := lg_3
  refine (ecis_approx ((((10802:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.867209939384987528 11.86720994478599833 0.6991607 0.00000003043 0.7653826097391 0.6435755283639 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v10p802_4 : ‖exp (-((((((10802:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7430288755614):ℝ):ℂ) + (((-0.6692593593293):ℝ):ℂ) * I)‖ ≤ 0.00000013117 := by
  have hl := lg_4
  refine (ecis_approx ((((10802:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.9747516832012 14.9747516940032 (-2.4083811) 0.00000003116 (-0.7430288755614) (-0.6692593593293) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v10p802_5 : ‖exp (-((((((10802:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1061881457906:ℝ):ℂ) + ((0.9943460553014:ℝ):ℂ) * I)‖ ≤ 0.00000011378 := by
  have hl := lg_5
  refine (ecis_approx ((((10802:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.385148324497285618 17.38514833529929642 1.4644076 0.00000001377 0.1061881457906 0.9943460553014 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v11p364_2 : ‖exp (-((((((11364:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.022940960471):ℝ):ℂ) + (((-0.9997368215348):ℝ):ℂ) * I)‖ ≤ 0.00000015027 := by
  have hl := lg_2
  refine (ecis_approx ((((11364:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 7.8769245569292 7.8769245626112 (-1.5937393) 0.00000005026 (-0.022940960471) (-0.9997368215348) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v11p364_3 : ‖exp (-((((((11364:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9966610968577:ℝ):ℂ) + ((0.0816496050848:ℝ):ℂ) * I)‖ ≤ 0.00000013681 := by
  have hl := lg_3
  refine (ecis_approx ((((11364:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.484630045470375696 12.48463005115238706 0.0817406 0.0000000368 0.9966610968577 0.0816496050848 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v11p364_4 : ‖exp (-((((((11364:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.998947428644):ℝ):ℂ) + ((0.0458697528204:ℝ):ℂ) * I)‖ ≤ 0.0000001077 := by
  have hl := lg_4
  refine (ecis_approx ((((11364:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 15.7538491138584 15.7538491252224 3.0957068 0.00000000769 (-0.998947428644) 0.0458697528204 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v11p364_5 : ‖exp (-((((((11364:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8473063665365:ℝ):ℂ) + ((0.5311044353295:ℝ):ℂ) * I)‖ ≤ 0.00000012083 := by
  have hl := lg_5
  refine (ecis_approx ((((11364:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.289652430993071076 18.28965244235708244 0.5599035 0.00000002082 0.8473063665365 0.5311044353295 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v11p926_2 : ‖exp (-((((((11926:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4008932536305):ℝ):ℂ) + (((-0.9161247727194):ℝ):ℂ) * I)‖ ≤ 0.00000013494 := by
  have hl := lg_2
  refine (ecis_approx ((((11926:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.2664732722578 8.2664732782208 (-1.983288) 0.00000003493 (-0.4008932536305) (-0.9161247727194) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v11p926_3 : ‖exp (-((((((11926:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8599219937134:ℝ):ℂ) + (((-0.5104254742153):ℝ):ℂ) * I)‖ ≤ 0.00000014317 := by
  have hl := lg_3
  refine (ecis_approx ((((11926:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.102050151555763864 13.10205015751877579 (-0.5356795) 0.00000004316 0.8599219937134 (-0.5104254742153) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v11p926_4 : ‖exp (-((((((11926:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6785692665647):ℝ):ℂ) + ((0.7345364187387:ℝ):ℂ) * I)‖ ≤ 0.00000013492 := by
  have hl := lg_4
  refine (ecis_approx ((((11926:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.5329465445156 16.5329465564416 2.3166094 0.00000003491 (-0.6785692665647) 0.7345364187387 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v11p926_5 : ‖exp (-((((((11926:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9412104532955:ℝ):ℂ) + (((-0.3378207847474):ℝ):ℂ) * I)‖ ≤ 0.00000012789 := by
  have hl := lg_5
  refine (ecis_approx ((((11926:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.194156537488856534 19.19415654941486846 (-0.3446006) 0.00000002788 0.9412104532955 (-0.3378207847474) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v12p488_2 : ‖exp (-((((((12488:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7187761383905):ℝ):ℂ) + (((-0.6952415859637):ℝ):ℂ) * I)‖ ≤ 0.00000011961 := by
  have hl := lg_2
  refine (ecis_approx ((((12488:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 8.6560219875864 8.6560219938304 (-2.3728367) 0.0000000196 (-0.7187761383905) (-0.6952415859637) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v12p488_3 : ‖exp (-((((((12488:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4056562800311:ℝ):ℂ) + (((-0.9140257012094):ℝ):ℂ) * I)‖ ≤ 0.00000014954 := by
  have hl := lg_3
  refine (ecis_approx ((((12488:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.719470257641152032 13.71947026388516452 (-1.1530996) 0.00000004953 0.4056562800311 (-0.9140257012094) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v12p488_4 : ‖exp (-((((((12488:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0332782814262:ℝ):ℂ) + ((0.9994461246036:ℝ):ℂ) * I)‖ ≤ 0.00000014638 := by
  have hl := lg_4
  refine (ecis_approx ((((12488:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.3120439751728 17.3120439876608 1.5375119 0.00000004637 0.0332782814262 0.9994461246036 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v12p488_5 : ‖exp (-((((((12488:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3161718618363:ℝ):ℂ) + (((-0.9487019309472):ℝ):ℂ) * I)‖ ≤ 0.00000013495 := by
  have hl := lg_5
  refine (ecis_approx ((((12488:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.098660643984641992 20.09866065647265448 (-1.2491047) 0.00000003494 0.3161718618363 (-0.9487019309472) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v13p05_2 : ‖exp (-((((((13050:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9289583895565):ℝ):ℂ) + (((-0.3701841572986):ℝ):ℂ) * I)‖ ≤ 0.00000010428 := by
  have hl := lg_2
  refine (ecis_approx ((((13050:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (1) 6.28318530717958647692 6.28318530717958647694 9.045570702915 9.04557070944 (-2.7623854) 0.00000000427 (-0.9289583895565) (-0.3701841572986) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v13p05_3 : ‖exp (-((((((13050:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1983983085332):ℝ):ℂ) + (((-0.980121477762):ℝ):ℂ) * I)‖ ≤ 0.00000015065 := by
  have hl := lg_3
  refine (ecis_approx ((((13050:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.3368903637265402 14.33689037025155325 (-1.7705198) 0.00000005064 (-0.1983983085332) (-0.980121477762) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v13p05_4 : ‖exp (-((((((13050:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7259273841846:ℝ):ℂ) + ((0.6877713521883:ℝ):ℂ) * I)‖ ≤ 0.00000011572 := by
  have hl := lg_4
  refine (ecis_approx ((((13050:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.09114140583 18.09114141888 0.7584145 0.00000001571 0.7259273841846 0.6877713521883 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v13p05_5 : ‖exp (-((((((13050:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5503742950452):ℝ):ℂ) + (((-0.8349180410943):ℝ):ℂ) * I)‖ ≤ 0.00000014201 := by
  have hl := lg_5
  refine (ecis_approx ((((13050:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.00316475048042745 21.0031647635304405 (-2.1536088) 0.000000042 (-0.5503742950452) (-0.8349180410943) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v13p612_2 : ‖exp (-((((((13612:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999465273173):ℝ):ℂ) + ((0.0103412689664:ℝ):ℂ) * I)‖ ≤ 0.00000011071 := by
  have hl := lg_2
  refine (ecis_approx ((((13612:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.4351194182436 9.4351194250496 3.1312512 0.0000000107 (-0.9999465273173) 0.0103412689664 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v13p612_3 : ‖exp (-((((((13612:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7291941346648):ℝ):ℂ) + (((-0.6843068857912):ℝ):ℂ) * I)‖ ≤ 0.00000014456 := by
  have hl := lg_3
  refine (ecis_approx ((((13612:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.954310469811928368 14.95431047661794198 (-2.3879399) 0.00000004455 (-0.7291941346648) (-0.6843068857912) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v13p612_4 : ‖exp (-((((((13612:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9997861164486:ℝ):ℂ) + (((-0.0206814254016):ℝ):ℂ) * I)‖ ≤ 0.00000012858 := by
  have hl := lg_4
  refine (ecis_approx ((((13612:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.8702388364872 18.8702388500992 (-0.0206829) 0.00000002857 0.9997861164486 (-0.0206814254016) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v13p612_5 : ‖exp (-((((((13612:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9965175882135):ℝ):ℂ) + (((-0.0833828272185):ℝ):ℂ) * I)‖ ≤ 0.00000014906 := by
  have hl := lg_5
  refine (ecis_approx ((((13612:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.907668856976212908 21.90766887058822652 (-3.0581129) 0.00000004905 (-0.9965175882135) (-0.0833828272185) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v14p174_2 : ‖exp (-((((((14174:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9211037646069):ℝ):ℂ) + ((0.3893171646387:ℝ):ℂ) * I)‖ ≤ 0.00000012632 := by
  have hl := lg_2
  refine (ecis_approx ((((14174:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 9.8246681335722 9.8246681406592 2.7417025 0.00000002631 (-0.9211037646069) 0.3893171646387 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v14p174_3 : ‖exp (-((((((14174:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9907346750295):ℝ):ℂ) + (((-0.1358116463314):ℝ):ℂ) * I)‖ ≤ 0.00000013848 := by
  have hl := lg_3
  refine (ecis_approx ((((14174:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.571730575897316536 15.57173058298433071 (-3.00536) 0.00000003847 (-0.9907346750295) (-0.1358116463314) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v14p174_4 : ‖exp (-((((((14174:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6968642239444:ℝ):ℂ) + (((-0.7172030768104):ℝ):ℂ) * I)‖ ≤ 0.00000015441 := by
  have hl := lg_4
  refine (ecis_approx ((((14174:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.6493362671444 19.6493362813184 (-0.7997804) 0.0000000544 0.6968642239444 (-0.7172030768104) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v14p174_5 : ‖exp (-((((((14174:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6814718976333):ℝ):ℂ) + ((0.7318442817398:ℝ):ℂ) * I)‖ ≤ 0.00000014894 := by
  have hl := lg_5
  refine (ecis_approx ((((14174:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.812172963471998366 22.81217297764601254 2.3205683 0.00000004893 (-0.6814718976333) 0.7318442817398 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v14p736_2 : ‖exp (-((((((14736:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7042438170015):ℝ):ℂ) + ((0.7099582003124:ℝ):ℂ) * I)‖ ≤ 0.00000014192 := by
  have hl := lg_2
  refine (ecis_approx ((((14736:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.2142168489008 10.2142168562688 2.3521538 0.00000004191 (-0.7042438170015) 0.7099582003124 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v14p736_3 : ‖exp (-((((((14736:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8864459561881):ℝ):ℂ) + ((0.4628321149787:ℝ):ℂ) * I)‖ ≤ 0.00000013957 := by
  have hl := lg_3
  refine (ecis_approx ((((14736:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.189150681982704704 16.18915068935071944 2.6604052 0.00000003956 (-0.8864459561881) 0.4628321149787 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v14p736_4 : ‖exp (-((((((14736:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0080813852383):ℝ):ℂ) + (((-0.999967345073):ℝ):ℂ) * I)‖ ≤ 0.00000012375 := by
  have hl := lg_4
  refine (ecis_approx ((((14736:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.4284336978016 20.4284337125376 (-1.5788778) 0.00000002374 (-0.0080813852383) (-0.999967345073) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v14p736_5 : ‖exp (-((((((14736:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.15411543194:ℝ):ℂ) + ((0.9880528496178:ℝ):ℂ) * I)‖ ≤ 0.000000156 := by
  have hl := lg_5
  refine (ecis_approx ((((14736:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.716677069967783824 23.71667708470379856 1.4160642 0.00000005599 0.15411543194 0.9880528496178 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v15p298_2 : ‖exp (-((((((15298:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3818606505901):ℝ):ℂ) + ((0.9242199108048:ℝ):ℂ) * I)‖ ≤ 0.00000015014 := by
  have hl := lg_2
  refine (ecis_approx ((((15298:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.6037655642294 10.6037655718784 1.962605 0.00000005013 (-0.3818606505901) 0.9242199108048 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v15p298_3 : ‖exp (-((((((15298:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4548366397735):ℝ):ℂ) + ((0.890574887988:ℝ):ℂ) * I)‖ ≤ 0.00000013349 := by
  have hl := lg_3
  refine (ecis_approx ((((15298:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.806570788068092872 16.80657079571710817 2.0429851 0.00000003348 (-0.4548366397735) 0.890574887988 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v15p298_4 : ‖exp (-((((((15298:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.708364811406):ℝ):ℂ) + (((-0.7058465087656):ℝ):ℂ) * I)‖ ≤ 0.00000012223 := by
  have hl := lg_4
  refine (ecis_approx ((((15298:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.2075311284588 21.2075311437568 (-2.3579752) 0.00000002222 (-0.708364811406) (-0.7058465087656) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v15p298_5 : ‖exp (-((((((15298:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8719818894942:ℝ):ℂ) + ((0.4895381337487:ℝ):ℂ) * I)‖ ≤ 0.00000015227 := by
  have hl := lg_5
  refine (ecis_approx ((((15298:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.621181176463569282 24.62118119176158458 0.51156 0.00000005226 0.8719818894942 0.4895381337487 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v15p86_2 : ‖exp (-((((((15860:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0022599712813):ℝ):ℂ) + ((0.9999974462615:ℝ):ℂ) * I)‖ ≤ 0.00000013482 := by
  have hl := lg_2
  refine (ecis_approx ((((15860:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.993314279558 10.993314287488 1.5730563 0.00000003481 (-0.0022599712813) 0.9999974462615 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v15p86_3 : ‖exp (-((((((15860:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1447213250722:ℝ):ℂ) + ((0.9894724544267:ℝ):ℂ) * I)‖ ≤ 0.0000001274 := by
  have hl := lg_3
  refine (ecis_approx ((((15860:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 17.42399089415348104 17.4239909020834969 1.425565 0.00000002739 0.1447213250722 0.9894724544267 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v15p86_4 : ‖exp (-((((((15860:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999897842383):ℝ):ℂ) + (((-0.0045200378978):ℝ):ℂ) * I)‖ ≤ 0.00000015345 := by
  have hl := lg_4
  refine (ecis_approx ((((15860:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.986628559116 21.986628574976 (-3.1370726) 0.00000005344 (-0.9999897842383) (-0.0045200378978) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v15p86_5 : ‖exp (-((((((15860:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9237857403356:ℝ):ℂ) + (((-0.3829097882695):ℝ):ℂ) * I)‖ ≤ 0.00000014577 := by
  have hl := lg_5
  refine (ecis_approx ((((15860:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.52568528295935474 25.5256852988193706 (-0.3929441) 0.00000004576 0.9237857403356 (-0.3829097882695) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v16p422_2 : ‖exp (-((((((16422:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3776793396622:ℝ):ℂ) + ((0.925936453755:ℝ):ℂ) * I)‖ ≤ 0.00000011949 := by
  have hl := lg_2
  refine (ecis_approx ((((16422:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.3828629948866 11.3828630030976 1.1835076 0.00000001948 0.3776793396622 0.925936453755 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v16p422_3 : ‖exp (-((((((16422:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6908408709:ℝ):ℂ) + ((0.7230068402817:ℝ):ℂ) * I)‖ ≤ 0.00000012131 := by
  have hl := lg_3
  refine (ecis_approx ((((16422:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.041411000238869208 18.04141100844988563 0.8081449 0.0000000213 0.6908408709 0.7230068402817 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v16p422_4 : ‖exp (-((((((16422:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7147166327808):ℝ):ℂ) + ((0.6994141368318:ℝ):ℂ) * I)‖ ≤ 0.00000013896 := by
  have hl := lg_4
  refine (ecis_approx ((((16422:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.7657259897732 22.7657260061952 2.3670152 0.00000003895 (-0.7147166327808) 0.6994141368318 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v16p422_5 : ‖exp (-((((((16422:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2699567628003:ℝ):ℂ) + (((-0.962872445456):ℝ):ℂ) * I)‖ ≤ 0.00000013928 := by
  have hl := lg_5
  refine (ecis_approx ((((16422:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.430189389455140198 26.43018940587715662 (-1.2974482) 0.00000003927 0.2699567628003 (-0.962872445456) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v16p984_2 : ‖exp (-((((((16984:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7010275897904:ℝ):ℂ) + ((0.7131341517223:ℝ):ℂ) * I)‖ ≤ 0.00000010436 := by
  have hl := lg_2
  refine (ecis_approx ((((16984:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 11.7724117102152 11.7724117187072 0.7939589 0.00000000435 0.7010275897904 0.7131341517223 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v16p984_3 : ‖exp (-((((((16984:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9818670922616:ℝ):ℂ) + ((0.1895706019767:ℝ):ℂ) * I)‖ ≤ 0.00000011523 := by
  have hl := lg_3
  refine (ecis_approx ((((16984:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 18.658831106324257376 18.65883111481627436 0.1907248 0.00000001522 0.9818670922616 0.1895706019767 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v16p984_4 : ‖exp (-((((((16984:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0171206367055):ℝ):ℂ) + ((0.9998534311581:ℝ):ℂ) * I)‖ ≤ 0.00000010871 := by
  have hl := lg_4
  refine (ecis_approx ((((16984:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.5448234204304 23.5448234374144 1.5879178 0.0000000087 (-0.0171206367055) 0.9998534311581 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v16p984_5 : ‖exp (-((((((16984:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5900784222527):ℝ):ℂ) + (((-0.8073459330303):ℝ):ℂ) * I)‖ ≤ 0.00000013278 := by
  have hl := lg_5
  refine (ecis_approx ((((16984:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.334693495950925656 27.33469351293494264 (-2.2019523) 0.00000003277 (-0.5900784222527) (-0.8073459330303) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v17p546_2 : ‖exp (-((((((17546:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9193346295558:ℝ):ℂ) + ((0.3934766052759:ℝ):ℂ) * I)‖ ≤ 0.00000011997 := by
  have hl := lg_2
  refine (ecis_approx ((((17546:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.1619604255438 12.1619604343168 0.4044102 0.00000001996 0.9193346295558 0.3934766052759 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v17p546_3 : ‖exp (-((((((17546:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9103384166861:ℝ):ℂ) + (((-0.4138646724541):ℝ):ℂ) * I)‖ ≤ 0.00000010914 := by
  have hl := lg_3
  refine (ecis_approx ((((17546:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.276251212409645544 19.27625122118266309 (-0.4266953) 0.00000000913 0.9103384166861 (-0.4138646724541) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v17p546_4 : ‖exp (-((((((17546:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6903523222011:ℝ):ℂ) + ((0.7234733383004:ℝ):ℂ) * I)‖ ≤ 0.00000013993 := by
  have hl := lg_4
  refine (ecis_approx ((((17546:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.3239208510876 24.3239208686336 0.8088204 0.00000003992 0.6903523222011 0.7234733383004 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v17p546_5 : ‖exp (-((((((17546:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9993827850515):ℝ):ℂ) + (((-0.0351290241479):ℝ):ℂ) * I)‖ ≤ 0.00000012629 := by
  have hl := lg_5
  refine (ecis_approx ((((17546:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.239197602446711114 28.23919761999272866 (-3.1064564) 0.00000002628 (-0.9993827850515) (-0.0351290241479) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v18p108_2 : ‖exp (-((((((18108:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9998895699414:ℝ):ℂ) + ((0.0148609529439:ℝ):ℂ) * I)‖ ≤ 0.00000013558 := by
  have hl := lg_2
  refine (ecis_approx ((((18108:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.5515091408724 12.5515091499264 0.0148615 0.00000003557 0.9998895699414 0.0148609529439 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v18p108_3 : ‖exp (-((((((18108:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5026668420963:ℝ):ℂ) + (((-0.8644802171576):ℝ):ℂ) * I)‖ ≤ 0.00000010603 := by
  have hl := lg_3
  refine (ecis_approx ((((18108:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.893671318495033712 19.89367132754905182 (-1.0441154) 0.00000000602 0.5026668420963 (-0.8644802171576) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v18p108_4 : ‖exp (-((((((18108:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9995583071271:ℝ):ℂ) + ((0.0297185237401:ℝ):ℂ) * I)‖ ≤ 0.00000014699 := by
  have hl := lg_4
  refine (ecis_approx ((((18108:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.1030182817448 25.1030182998528 0.0297229 0.00000004698 0.9995583071271 0.0297185237401 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v18p108_5 : ‖exp (-((((((18108:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6453095861607):ℝ):ℂ) + ((0.7639211595399:ℝ):ℂ) * I)‖ ≤ 0.00000012697 := by
  have hl := lg_5
  refine (ecis_approx ((((18108:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.143701708942496572 29.14370172705051468 2.2722248 0.00000002696 (-0.6453095861607) 0.7639211595399 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v18p67_2 : ‖exp (-((((((18670:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9306221464353:ℝ):ℂ) + (((-0.3659814483879):ℝ):ℂ) * I)‖ ≤ 0.00000015119 := by
  have hl := lg_2
  refine (ecis_approx ((((18670:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 12.941057856201 12.941057865536 (-0.3746872) 0.00000005118 0.9306221464353 (-0.3659814483879) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v18p67_3 : ‖exp (-((((((18670:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.090614706151):ℝ):ℂ) + (((-0.9958860251197):ℝ):ℂ) * I)‖ ≤ 0.00000011239 := by
  have hl := lg_3
  refine (ecis_approx ((((18670:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.51109142458042188 20.51109143391544055 (-1.6615355) 0.00000001238 (-0.090614706151) (-0.9958860251197) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v18p67_4 : ‖exp (-((((((18670:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7321150907537:ℝ):ℂ) + (((-0.68118095532):ℝ):ℂ) * I)‖ ≤ 0.00000011633 := by
  have hl := lg_4
  refine (ecis_approx ((((18670:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 25.882115712402 25.882115731072 (-0.7493745) 0.00000001632 0.7321150907537 (-0.68118095532) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v18p67_5 : ‖exp (-((((((18670:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2016827054168:ℝ):ℂ) + ((0.9794509106309:ℝ):ℂ) * I)‖ ≤ 0.00000012047 := by
  have hl := lg_5
  refine (ecis_approx ((((18670:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.04820581543828203 30.0482058341083007 1.3677207 0.00000002046 0.2016827054168 0.9794509106309 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v19p232_2 : ‖exp (-((((((19232:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.721911245118:ℝ):ℂ) + (((-0.6919856603804):ℝ):ℂ) * I)‖ ≤ 0.00000014284 := by
  have hl := lg_2
  refine (ecis_approx ((((19232:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.3306065715296 13.3306065811456 (-0.764236) 0.00000004283 0.721911245118 (-0.6919856603804) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v19p232_3 : ‖exp (-((((((19232:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6504367304869):ℝ):ℂ) + (((-0.7595604384225):ℝ):ℂ) * I)‖ ≤ 0.00000011876 := by
  have hl := lg_3
  refine (ecis_approx ((((19232:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.128511530665810048 21.12851154028182928 (-2.2789556) 0.00000001875 (-0.6504367304869) (-0.7595604384225) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v19p232_4 : ‖exp (-((((((19232:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0423117915662:ℝ):ℂ) + (((-0.9991044551469):ℝ):ℂ) * I)‖ ≤ 0.00000013359 := by
  have hl := lg_4
  refine (ecis_approx ((((19232:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 26.6612131430592 26.6612131622912 (-1.5284719) 0.00000003358 0.0423117915662 (-0.9991044551469) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v19p232_5 : ‖exp (-((((((19232:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8946198610006:ℝ):ℂ) + ((0.4468280478029:ℝ):ℂ) * I)‖ ≤ 0.00000011398 := by
  have hl := lg_5
  refine (ecis_approx ((((19232:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.952709921934067488 30.95270994116608672 0.4632166 0.00000001397 0.8946198610006 0.4468280478029 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v19p794_2 : ‖exp (-((((((19794:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4050299858724:ℝ):ℂ) + (((-0.9143034018006):ℝ):ℂ) * I)‖ ≤ 0.00000012752 := by
  have hl := lg_2
  refine (ecis_approx ((((19794:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 13.7201552868582 13.7201552967552 (-1.1537847) 0.00000002751 0.4050299858724 (-0.9143034018006) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v19p794_3 : ‖exp (-((((((19794:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9700846785702):ℝ):ℂ) + (((-0.2427667937166):ℝ):ℂ) * I)‖ ≤ 0.00000012512 := by
  have hl := lg_3
  refine (ecis_approx ((((19794:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 21.745931636751198216 21.74593164664821801 (-2.8963757) 0.00000002511 (-0.9700846785702) (-0.2427667937166) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v19p794_4 : ‖exp (-((((((19794:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6719014210862):ℝ):ℂ) + (((-0.7406405878176):ℝ):ℂ) * I)‖ ≤ 0.00000015502 := by
  have hl := lg_4
  refine (ecis_approx ((((19794:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 27.4403105737164 27.4403105935104 (-2.3075694) 0.00000005501 (-0.6719014210862) (-0.7406405878176) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v19p794_5 : ‖exp (-((((((19794:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9042025164267:ℝ):ℂ) + (((-0.42710397948):ℝ):ℂ) * I)‖ ≤ 0.00000011234 := by
  have hl := lg_5
  refine (ecis_approx ((((19794:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 31.857214028429852946 31.85721404822387274 (-0.4412875) 0.00000001233 0.9042025164267 (-0.42710397948) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v20p356_2 : ‖exp (-((((((20356:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0274594747786:ℝ):ℂ) + (((-0.9996229175268):ℝ):ℂ) * I)‖ ≤ 0.00000011219 := by
  have hl := lg_2
  refine (ecis_approx ((((20356:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.1097040021868 14.1097040123648 (-1.5433334) 0.00000001218 0.0274594747786 (-0.9996229175268) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v20p356_3 : ‖exp (-((((((20356:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9315283891555):ℝ):ℂ) + ((0.3636686129362:ℝ):ℂ) * I)‖ ≤ 0.00000012431 := by
  have hl := lg_3
  refine (ecis_approx ((((20356:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.363351742836586384 22.36335175301460674 2.7693895 0.0000000243 (-0.9315283891555) 0.3636686129362 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v20p356_4 : ‖exp (-((((((20356:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9984919542222):ℝ):ℂ) + (((-0.054898240326):ℝ):ℂ) * I)‖ ≤ 0.00000012436 := by
  have hl := lg_4
  refine (ecis_approx ((((20356:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 28.2194080043736 28.2194080247296 (-3.0866668) 0.00000002435 (-0.9984919542222) (-0.054898240326) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v20p356_5 : ‖exp (-((((((20356:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2231109697811:ℝ):ℂ) + (((-0.97479305248):ℝ):ℂ) * I)‖ ≤ 0.0000001194 := by
  have hl := lg_5
  refine (ecis_approx ((((20356:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 32.761718134925638404 32.76171815528165876 (-1.3457916) 0.00000001939 0.2231109697811 (-0.97479305248) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v20p918_2 : ‖exp (-((((((20918:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.354225534102):ℝ):ℂ) + (((-0.9351600242674):ℝ):ℂ) * I)‖ ≤ 0.00000011363 := by
  have hl := lg_2
  refine (ecis_approx ((((20918:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.4992527175154 14.4992527279744 (-1.9328821) 0.00000001362 (-0.354225534102) (-0.9351600242674) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v20p918_3 : ‖exp (-((((((20918:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5490047914201):ℝ):ℂ) + ((0.8358192023334:ℝ):ℂ) * I)‖ ≤ 0.00000013068 := by
  have hl := lg_3
  refine (ecis_approx ((((20918:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 22.980771848921974552 22.98077185938099547 2.1519694 0.00000003067 (-0.5490047914201) 0.8358192023334 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v20p918_4 : ‖exp (-((((((20918:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7490485372183):ℝ):ℂ) + ((0.6625151234934:ℝ):ℂ) * I)‖ ≤ 0.00000012007 := by
  have hl := lg_4
  refine (ecis_approx ((((20918:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 28.9985054350308 28.9985054559488 2.4174211 0.00000002006 (-0.7490485372183) 0.6625151234934 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v20p918_5 : ‖exp (-((((((20918:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6284036714991):ℝ):ℂ) + (((-0.7778874119253):ℝ):ℂ) * I)‖ ≤ 0.00000012646 := by
  have hl := lg_5
  refine (ecis_approx ((((20918:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 33.666222241421423862 33.66622226233944478 (-2.2502957) 0.00000002645 (-0.6284036714991) (-0.7778874119253) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v21p48_2 : ‖exp (-((((((21480:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6828337748392):ℝ):ℂ) + (((-0.7305737717149):ℝ):ℂ) * I)‖ ≤ 0.00000012924 := by
  have hl := lg_2
  refine (ecis_approx ((((21480:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.888801432844 14.888801443584 (-2.3224308) 0.00000002923 (-0.6828337748392) (-0.7305737717149) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v21p48_3 : ‖exp (-((((((21480:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.036239090142:ℝ):ℂ) + ((0.9993431484458:ℝ):ℂ) * I)‖ ≤ 0.00000013704 := by
  have hl := lg_3
  refine (ecis_approx ((((21480:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.59819195500736272 23.5981919657473842 1.5345493 0.00000003703 0.036239090142 0.9993431484458 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v21p48_4 : ‖exp (-((((((21480:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0674760647074):ℝ):ℂ) + ((0.9977208931817:ℝ):ℂ) * I)‖ ≤ 0.00000015129 := by
  have hl := lg_4
  refine (ecis_approx ((((21480:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.777602865688 29.777602887168 1.6383237 0.00000005128 (-0.0674760647074) 0.9977208931817 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v21p48_5 : ‖exp (-((((((21480:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999127864909):ℝ):ℂ) + ((0.0132067693487:ℝ):ℂ) * I)‖ ≤ 0.00000012633 := by
  have hl := lg_5
  refine (ecis_approx ((((21480:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 34.57072634791720932 34.5707263693972308 3.1283855 0.00000002632 (-0.9999127864909) 0.0132067693487 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v22_2 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8966176905623):ℝ):ℂ) + (((-0.4428055068064):ℝ):ℂ) * I)‖ ≤ 0.00000014777 := by
  have hl := lg_2
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.2492379666 15.2492379776 (-2.6828674) 0.00000004776 (-0.8966176905623) (-0.4428055068064) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v22_3 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5708374291683:ℝ):ℂ) + ((0.8210631093044:ℝ):ℂ) * I)‖ ≤ 0.00000012728 := by
  have hl := lg_3
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.169470344979608 24.16947035597963 0.9632709 0.00000002727 0.5708374291683 0.8210631093044 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v22_4 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6078464924715:ℝ):ℂ) + ((0.7940545583208:ℝ):ℂ) * I)‖ ≤ 0.00000011932 := by
  have hl := lg_4
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.4984759332 30.4984759552 0.9174506 0.00000001931 0.6078464924715 0.7940545583208 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v22_5 : ‖exp (-((((((22000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6598968542787):ℝ):ℂ) + ((0.7513562016082:ℝ):ℂ) * I)‖ ≤ 0.00000014105 := by
  have hl := lg_5
  refine (ecis_approx ((((22000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.407634062112598 35.40763408411262 2.2914778 0.00000004104 (-0.6598968542787) 0.7513562016082 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H22
end Cert
end ZB
end RHV6Fresh
