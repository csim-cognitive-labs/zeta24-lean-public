/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox.Base
/-!
# Certificat (V2), côté right (b1)

Fichier GENERE par `experiments/e192_zeta_box_certificate_generator.py` : constantes rationnelles calculees en
arithmetique exacte puis verifiees par Lean (`norm_num`, `linarith`, `decide`). Aucune preuve admise, aucun axiome ajoute.
-/

set_option maxHeartbeats 4000000
set_option linter.style.longLine false

namespace RHV6Fresh
namespace ZB
namespace Cert

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

lemma cs_right_v14p793_2 : ‖exp (-((((((14793:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6756515033325):ℝ):ℂ) + ((0.7372211649325:ℝ):ℂ) * I)‖ ≤ 0.00000013123 := by
  have hl := lg_2
  refine (ecis_approx ((((14793:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.2537262381779 10.2537262455744 2.3126444 0.00000003122 (-0.6756515033325) 0.7372211649325 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v14p793_3 : ‖exp (-((((((14793:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.855744454522):ℝ):ℂ) + ((0.5173987132543:ℝ):ℂ) * I)‖ ≤ 0.00000013913 := by
  have hl := lg_3
  refine (ecis_approx ((((14793:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.251771582421970052 16.251771589818484845 2.5977843 0.00000003912 (-0.855744454522) 0.5173987132543 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v14p793_4 : ‖exp (-((((((14793:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0869901845511):ℝ):ℂ) + (((-0.9962091686947):ℝ):ℂ) * I)‖ ≤ 0.0000001452 := by
  have hl := lg_4
  refine (ecis_approx ((((14793:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.5074524763558 20.5074524911488 (-1.6578966) 0.00000004519 (-0.0869901845511) (-0.9962091686947) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v14p793_5 : ‖exp (-((((((14793:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2439822870358:ℝ):ℂ) + ((0.9697796881832:ℝ):ℂ) * I)‖ ≤ 0.00000011704 := by
  have hl := lg_5
  refine (ecis_approx ((((14793:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.808415030946893737 23.80841504573990853 1.3243262 0.00000001703 0.2439822870358 0.9697796881832 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v15_2 : ‖exp (-((((((15000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5632935954295):ℝ):ℂ) + ((0.826256815608:ℝ):ℂ) * I)‖ ≤ 0.00000010987 := by
  have hl := lg_2
  refine (ecis_approx ((((15000:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 10.3972077045 10.397207712 2.1691629 0.00000000986 (-0.5632935954295) 0.826256815608 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v15_3 : ‖exp (-((((((15000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7170601161939):ℝ):ℂ) + ((0.6970113268357:ℝ):ℂ) * I)‖ ≤ 0.0000001121 := by
  have hl := lg_3
  refine (ecis_approx ((((15000:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 16.47918432612246 16.479184333622475 2.3703716 0.00000001209 (-0.7170601161939) 0.6970113268357 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v15_4 : ‖exp (-((((((15000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3654006440121):ℝ):ℂ) + (((-0.9308503474528):ℝ):ℂ) * I)‖ ≤ 0.00000011255 := by
  have hl := lg_4
  refine (ecis_approx ((((15000:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 20.794415409 20.794415424 (-1.9448595) 0.00000001254 (-0.3654006440121) (-0.9308503474528) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_right_v15_5 : ‖exp (-((((((15000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5477092431889:ℝ):ℂ) + ((0.8366687426487:ℝ):ℂ) * I)‖ ≤ 0.00000015002 := by
  have hl := lg_5
  refine (ecis_approx ((((15000:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.141568678713135 24.14156869371315 0.9911725 0.00000005001 0.5477092431889 0.8366687426487 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]
lemma bv_right_m1_0_5 : (1.149751453998:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((-1000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((-1000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((-1000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((-1000:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((-1000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.7692388889425 0.6389612912677 0.00000011971 cs_right_vm1_2 0.19230969230812 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((-1000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.4548324127347 0.8905770468219 0.00000011161 cs_right_vm1_3 0.05053692234718 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((-1000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.1834569365231 0.983027747544 0.00000013941 cs_right_vm1_4 0.01146604981956 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((-1000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_right_vm1_5 (-0.00154528281757) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((-1000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.0386319575092) 0.9992535073037 0.00000011293 cs_right_vm1_5 2 (by norm_num) (by norm_num) 2.57539819146265 0.10301592765851 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.25276738165729:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((-1000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma bv_right_m0p438_0_5 : (1.483806246535:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((-438:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((-438:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((-438:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((-438:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((-438:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.954266876541 0.2989560642247 0.00000013504 cs_right_vm0p438_2 0.23856668537525 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((-438:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.8864437594156 0.4628363224652 0.00000011769 cs_right_vm0p438_3 0.0984937379695 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((-438:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.8212506003834 0.5705676571362 0.0000001304 cs_right_vm0p438_4 0.05132815437396 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((-438:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.7616544499327 0.6479834094309 0.00000010587 cs_right_vm0p438_5 0.0304661737625 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((-438:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.7616544499327 0.6479834094309 0.00000010587 cs_right_vm0p438_5 1.191844 (by norm_num) (by norm_num) (-1.62378737635294) (-0.06495149505411) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.41885475148121:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((-438:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_0 : mainRemConst 5 (2:ℝ) 1.091716 ≤ 1.42806985 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 1.091716 (by norm_num) _ 0.04 1.60943791291421 1.42806985 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_0 : ∀ y ∈ Set.Icc (((-1000:ℤ):ℝ)/1000) (((-438:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((-1000:ℤ):ℝ)/1000) (((-438:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.091716 0.438 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 1.42806985 rb_right_0 0.04 2.236068 3.162278 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.149751453998 1.483806246535 (by rw [hrot]; exact bv_right_m1_0_5) (by rw [hrot]; exact bv_right_m0p438_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_0p124_0_5 : (1.628560384538:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((124:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((124:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((124:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((124:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((124:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.9963085463416 (-0.0858445134333) 0.00000014966 cs_right_v0p124_2 0.2490770991704 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((124:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.9907353207933 (-0.1358069369827) 0.00000012384 cs_right_v0p124_3 0.11008168855035 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((124:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.9852614561323 (-0.1710551462541) 0.00000010085 cs_right_v0p124_4 0.06157883470514 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((124:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9801518555693 (-0.1982481778582) 0.00000010122 cs_right_v0p124_5 0.03920607017397 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((124:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9801518555693 (-0.1982481778582) 0.00000010122 cs_right_v0p124_5 1.015376 (by norm_num) (by norm_num) (-4.21541729847458) (-0.16861669193898) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.45994369259986:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((124:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_1 : mainRemConst 5 (2:ℝ) 1 ≤ 1.56969504 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 1 (by norm_num) _ 0.04 1.60943791291421 1.56969504 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_1 : ∀ y ∈ Set.Icc (((-438:ℤ):ℝ)/1000) (((124:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((-438:ℤ):ℝ)/1000) (((124:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1 0 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 1.56969504 rb_right_1 0.04 2.0474 3.031806 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.483806246535 1.628560384538 (by rw [hrot]; exact bv_right_m0p438_0_5) (by rw [hrot]; exact bv_right_0p124_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_0p686_0_5 : (1.326468646008:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((686:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((686:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((686:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((686:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((686:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.8890643990301 (-0.4577821472898) 0.00000013433 cs_right_v0p686_2 0.22226606617502 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((686:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.7291973875753 (-0.6843034195102) 0.00000013021 cs_right_v0p686_3 0.08102191748502 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((686:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.5808710926451 (-0.8139955612467) 0.00000013207 cs_right_v0p686_4 0.03630443503594 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((686:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.4499612311949 (-0.8930480896466) 0.00000010827 cs_right_v0p686_5 0.01799844491699 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((686:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.4499612311949 (-0.8930480896466) 0.00000010827 cs_right_v0p686_5 1.470596 (by norm_num) (by norm_num) 0.77805544010311 0.03112221760413 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.35759086361297:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((686:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_2 : mainRemConst 5 (2:ℝ) 1.007658 ≤ 1.55635861 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 1.007658 (by norm_num) _ 0.04 1.60943791291421 1.55635861 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_2 : ∀ y ∈ Set.Icc (((124:ℤ):ℝ)/1000) (((686:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((124:ℤ):ℝ)/1000) (((686:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.007658 0.124 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 1.55635861 rb_right_2 0.04 2.114379 3.077434 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.628560384538 1.326468646008 (by rw [hrot]; exact bv_right_0p124_0_5) (by rw [hrot]; exact bv_right_0p686_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_1p248_0_5 : (1.044259522905:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((1248:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((1248:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((1248:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((1248:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((1248:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.6486038107046 (-0.761126202899) 0.000000119 cs_right_v1p248_2 0.16215092292615 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((1248:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.1984029676263 (-0.9801205346472) 0.00000013657 cs_right_v1p248_3 0.02204475900625 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((1248:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.158626193479) (-0.9873387112545) 0.00000013799 cs_right_v1p248_4 (-0.00991414571682) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((1248:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.423931836684) (-0.9056940972767) 0.00000011533 cs_right_v1p248_5 (-0.01695727808056) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((1248:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.423931836684) (-0.9056940972767) 0.00000011533 cs_right_v1p248_5 2.557504 (by norm_num) (by norm_num) 2.82661838074702 0.11306473522989 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.15732425813502:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((1248:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_3 : mainRemConst 5 (2:ℝ) 1.212681 ≤ 1.28798019 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 1.212681 (by norm_num) _ 0.04 1.60943791291421 1.28798019 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_3 : ∀ y ∈ Set.Icc (((686:ℤ):ℝ)/1000) (((1248:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((686:ℤ):ℝ)/1000) (((1248:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.212681 0.686 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 1.28798019 rb_right_3 0.04 2.357436 3.249232 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.326468646008 1.044259522905 (by rw [hrot]; exact bv_right_0p686_0_5) (by rw [hrot]; exact bv_right_1p248_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_1p81_0_5 : (0.898040755349:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((1810:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((1810:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((1810:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((1810:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((1810:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.3109571339648 (-0.9504239374281) 0.00000010367 cs_right_v1p81_2 0.0777392575737 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((1810:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.4056518437206) (-0.9140276700859) 0.00000014294 cs_right_v1p81_3 (-0.04507244296233) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((1810:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.806611321662) (-0.5910822072393) 0.00000010733 cs_right_v1p81_4 (-0.050413214312) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((1810:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9740049883168) (-0.2265265601283) 0.00000012239 cs_right_v1p81_5 (-0.03896020442828) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((1810:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9740049883168) (-0.2265265601283) 0.00000012239 cs_right_v1p81_5 4.2761 (by norm_num) (by norm_num) 1.13131601304412 0.04525264052177 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.94329339587109:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((1810:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_4 : mainRemConst 5 (2:ℝ) 1.599219 ≤ 1.02845368 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 1.599219 (by norm_num) _ 0.04 1.60943791291421 1.02845368 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_4 : ∀ y ∈ Set.Icc (((1248:ℤ):ℝ)/1000) (((1810:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((1248:ℤ):ℝ)/1000) (((1810:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 1.599219 1.248 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 1.02845368 rb_right_4 0.04 2.697425 3.503727 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.044259522905 0.898040755349 (by rw [hrot]; exact bv_right_1p248_0_5) (by rw [hrot]; exact bv_right_1p81_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_2p372_0_5 : (0.829950884889:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((2372:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((2372:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((2372:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((2372:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((2372:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.0732830209752) (-0.9973111845539) 0.00000011287 cs_right_v2p372_2 (-0.0183207834613) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((2372:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.8599195162869) (-0.5104296478737) 0.00000014931 cs_right_v2p372_3 (-0.09554662951085) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((2372:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.9892591964509) 0.1461719598231 0.00000011855 cs_right_v2p372_4 (-0.06182870718756) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((2372:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.7800853840809) 0.6256730723797 0.00000012227 cs_right_v2p372_5 (-0.03120342025404) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((2372:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.7800853840809) 0.6256730723797 0.00000012227 cs_right_v2p372_5 6.626384 (by norm_num) (by norm_num) (-0.92126063257189) (-0.03685042530287) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.79310045958625:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((2372:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_5 : mainRemConst 5 (2:ℝ) 2.067873 ≤ 0.87817062 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 2.067873 (by norm_num) _ 0.04 1.60943791291421 0.87817062 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_5 : ∀ y ∈ Set.Icc (((1810:ℤ):ℝ)/1000) (((2372:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((1810:ℤ):ℝ)/1000) (((2372:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 2.067873 1.81 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.87817062 rb_right_5 0.04 3.102642 3.824446 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.898040755349 0.829950884889 (by rw [hrot]; exact bv_right_1p81_0_5) (by rw [hrot]; exact bv_right_2p372_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_2p934_0_5 : (0.801514103873:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((2934:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((2934:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((2934:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.4465425278859) (-0.8947624102435) 0.00000012848 cs_right_v2p934_2 (-0.11163566409148) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.9966614923173) 0.081644774618 0.00000014849 cs_right_v2p934_3 (-0.11074018231202) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.6011995358404) 0.7990989413665 0.00000014977 cs_right_v2p934_4 (-0.03757498035065) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.0097016745975 0.9999529376475 0.00000012933 cs_right_v2p934_5 0.0003880618107 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((2934:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.0097016745975 0.9999529376475 0.00000012933 cs_right_v2p934_5 9.608356 (by norm_num) (by norm_num) (-1.52692172042908) (-0.06107686881716) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.74043723505655:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((2934:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_6 : mainRemConst 5 (2:ℝ) 2.574176 ≤ 0.79130312 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 2.574176 (by norm_num) _ 0.04 1.60943791291421 0.79130312 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_6 : ∀ y ∈ Set.Icc (((2372:ℤ):ℝ)/1000) (((2934:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((2372:ℤ):ℝ)/1000) (((2934:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 2.574176 2.372 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.79130312 rb_right_6 0.04 3.550825 4.196232 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.829950884889 0.801514103873 (by rw [hrot]; exact bv_right_2p372_0_5) (by rw [hrot]; exact bv_right_2p934_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_3p496_0_5 : (0.795192513036:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((3496:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((3496:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((3496:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((3496:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((3496:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.7528925888707) (-0.6581434111112) 0.00000014409 cs_right_v3p496_2 (-0.18822318324018) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((3496:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.7653856643972) 0.6435718955155 0.00000014692 cs_right_v3p496_3 (-0.08504286792421) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((3496:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.1336946069879 0.9910225789871 0.00000012254 cs_right_v3p496_4 0.00835590527799 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((3496:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.792078118693 0.6104197358275 0.00000013638 cs_right_v3p496_5 0.03168311929252 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((3496:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.792078118693 0.6104197358275 0.00000013638 cs_right_v3p496_5 13.222016 (by norm_num) (by norm_num) (-0.71048849077127) (-0.02841953963085) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.76677297340612:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((3496:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_7 : mainRemConst 5 (2:ℝ) 3.099734 ≤ 0.73709521 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 3.099734 (by norm_num) _ 0.04 1.60943791291421 0.73709521 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_7 : ∀ y ∈ Set.Icc (((2934:ℤ):ℝ)/1000) (((3496:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((2934:ℤ):ℝ)/1000) (((3496:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 3.099734 2.934 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.73709521 rb_right_7 0.04 4.027657 4.606736 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.801514103873 0.795192513036 (by rw [hrot]; exact bv_right_2p934_0_5) (by rw [hrot]; exact bv_right_3p496_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_4p058_0_5 : (0.804002228983:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((4058:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((4058:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((4058:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((4058:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((4058:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9464300767654) (-0.3229088255214) 0.00000014236 cs_right_v4p058_2 (-0.23660755478135) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((4058:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.2514908190316) 0.967859684015 0.00000014083 cs_right_v4p058_3 (-0.02794343998465) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((4058:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.7914597239363 0.6112213227519 0.00000011221 cs_right_v4p058_4 0.04946622573289 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((4058:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.96942647155 (-0.2453819803046) 0.00000014344 cs_right_v4p058_5 0.0387770531244 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((4058:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.96942647155 (-0.2453819803046) 0.00000014344 cs_right_v4p058_5 17.467364 (by norm_num) (by norm_num) 0.49225137768281 0.01969005510732 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.82369228409129:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((4058:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_8 : mainRemConst 5 (2:ℝ) 3.636209 ≤ 0.70072613 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 3.636209 (by norm_num) _ 0.04 1.60943791291421 0.70072613 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_8 : ∀ y ∈ Set.Icc (((3496:ℤ):ℝ)/1000) (((4058:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((3496:ℤ):ℝ)/1000) (((4058:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 3.636209 3.496 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.70072613 rb_right_8 0.04 4.524088 5.04652 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.795192513036 0.804002228983 (by rw [hrot]; exact bv_right_3p496_0_5) (by rw [hrot]; exact bv_right_4p058_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_4p62_0_5 : (0.825950655982:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((4620:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((4620:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((4620:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((4620:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((4620:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9981554465973) 0.0607099981673 0.00000013421 cs_right_v4p62_2 (-0.24953889520183) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((4620:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.355267132451 0.9347648178018 0.00000013475 cs_right_v4p62_3 0.03947411085566 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((4620:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.9926286051732 (-0.1211959248153) 0.00000014343 cs_right_v4p62_4 0.06203927885895 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((4620:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.406279368421 (-0.9137489123361) 0.0000001505 cs_right_v4p62_5 0.01625116871684 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((4620:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.406279368421 (-0.9137489123361) 0.0000001505 cs_right_v4p62_5 22.3444 (by norm_num) (by norm_num) 1.05687518117283 0.04227500724692 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.86822566322962:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((4620:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_9 : mainRemConst 5 (2:ℝ) 4.179397 ≤ 0.67487216 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 4.179397 (by norm_num) _ 0.04 1.60943791291421 0.67487216 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_9 : ∀ y ∈ Set.Icc (((4058:ℤ):ℝ)/1000) (((4620:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((4058:ℤ):ℝ)/1000) (((4620:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 4.179397 4.058 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.67487216 rb_right_9 0.04 5.034323 5.508576 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.804002228983 0.825950655982 (by rw [hrot]; exact bv_right_4p058_0_5) (by rw [hrot]; exact bv_right_4p62_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_5p182_0_5 : (0.860460241181:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((5182:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((5182:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((5182:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((5182:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((5182:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9003182897513) 0.4352320955795 0.00000011888 cs_right_v5p182_2 (-0.22507960215783) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((5182:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.8308425240881 0.5565075921917 0.00000012866 cs_right_v5p182_3 0.09231582171422 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((5182:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.6211460514718 (-0.7836948275579) 0.00000013057 cs_right_v5p182_4 0.03882162005636 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((5182:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.4672039187481) (-0.8841495904548) 0.00000014766 cs_right_v5p182_5 (-0.01868816265633) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((5182:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.4672039187481) (-0.8841495904548) 0.00000014766 cs_right_v5p182_5 27.853124 (by norm_num) (by norm_num) 0.6727358943759 0.02690943577504 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.88736967695642:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((5182:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_10 : mainRemConst 5 (2:ℝ) 4.726986 ≤ 0.65564452 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 4.726986 (by norm_num) _ 0.04 1.60943791291421 0.65564452 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_10 : ∀ y ∈ Set.Icc (((4620:ℤ):ℝ)/1000) (((5182:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((4620:ℤ):ℝ)/1000) (((5182:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 4.726986 4.62 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.65564452 rb_right_10 0.04 5.554559 5.987748 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.825950655982 0.860460241181 (by rw [hrot]; exact bv_right_4p62_0_5) (by rw [hrot]; exact bv_right_5p182_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_5p744_0_5 : (0.905862535221:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((5744:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((5744:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((5744:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((5744:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((5744:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.6675784209665) 0.7445394897793 0.00000010355 cs_right_v5p744_2 (-0.16689463112913) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((5744:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.9996289133583 (-0.0272403299922) 0.00000012258 cs_right_v5p744_3 0.11106986564202 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((5744:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.1086780965769) (-0.9940769946659) 0.00000010587 cs_right_v5p744_4 (-0.00679238765294) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((5744:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9838138609772) (-0.1791934334688) 0.00000014116 cs_right_v5p744_5 (-0.03935256008549) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((5744:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9838138609772) (-0.1791934334688) 0.00000014116 cs_right_v5p744_5 33.993536 (by norm_num) (by norm_num) (-0.19580621117275) (-0.00783224844691) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.89803028677446:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((5744:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_11 : mainRemConst 5 (2:ℝ) 5.277605 ≤ 0.64082814 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 5.277605 (by norm_num) _ 0.04 1.60943791291421 0.64082814 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_11 : ∀ y ∈ Set.Icc (((5182:ℤ):ℝ)/1000) (((5744:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((5182:ℤ):ℝ)/1000) (((5744:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 5.277605 5.182 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.64082814 rb_right_11 0.04 6.082232 6.480242 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.860460241181 0.905862535221 (by rw [hrot]; exact bv_right_5p182_0_5) (by rw [hrot]; exact bv_right_5p744_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_6p306_0_5 : (0.958468571111:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((6306:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((6306:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((6306:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((6306:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((6306:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.3348093288063) 0.9422858978793 0.00000011496 cs_right_v6p306_2 (-0.08370236094158) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((6306:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.7993018446929 (-0.6009297472006) 0.00000011649 cs_right_v6p306_3 0.08881130313364 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((6306:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.775805422151) (-0.6309722235726) 0.00000013709 cs_right_v6p306_4 (-0.04848784745257) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((6306:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.7489385493879) 0.6626394564219 0.00000014184 cs_right_v6p306_5 (-0.02995754764912) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((6306:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.7489385493879) 0.6626394564219 0.00000014184 cs_right_v6p306_5 40.765636 (by norm_num) (by norm_num) (-0.79512560052507) (-0.031805024021) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.92666354709037:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((6306:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_12 : mainRemConst 5 (2:ℝ) 5.830397 ≤ 0.62908225 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 5.830397 (by norm_num) _ 0.04 1.60943791291421 0.62908225 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_12 : ∀ y ∈ Set.Icc (((5744:ℤ):ℝ)/1000) (((6306:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((5744:ℤ):ℝ)/1000) (((6306:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 5.830397 5.744 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.62908225 rb_right_12 0.04 6.615561 6.98324 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.905862535221 0.958468571111 (by rw [hrot]; exact bv_right_5p744_0_5) (by rw [hrot]; exact bv_right_6p306_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_6p868_0_5 : (1.013449516177:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((6868:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((6868:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((6868:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((6868:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((6868:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.0481272284472 0.9988412135479 0.00000013057 cs_right_v6p868_2 0.0120317744693 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((6868:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.3038321847254 (-0.9527255656929) 0.00000011041 cs_right_v6p868_3 0.03375911936837 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((6868:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.9953675299292) 0.096143017844 0.00000014577 cs_right_v6p868_4 (-0.0622104797312) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((6868:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.0580127373195 0.9983158429618 0.00000013535 cs_right_v6p868_5 0.00232050407878 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((6868:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.0580127373195 0.9983158429618 0.00000013535 cs_right_v6p868_5 48.169424 (by norm_num) (by norm_num) (-0.68871494980299) (-0.02754859799211) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.98590091818525:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((6868:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_13 : mainRemConst 5 (2:ℝ) 6.384797 ≤ 0.61955315 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 6.384797 (by norm_num) _ 0.04 1.60943791291421 0.61955315 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_13 : ∀ y ∈ Set.Icc (((6306:ℤ):ℝ)/1000) (((6868:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((6306:ℤ):ℝ)/1000) (((6868:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 6.384797 6.306 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.61955315 rb_right_13 0.04 7.153281 7.494627 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.958468571111 1.013449516177 (by rw [hrot]; exact bv_right_6p306_0_5) (by rw [hrot]; exact bv_right_6p868_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_7p43_0_5 : (1.066602034512:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((7430:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((7430:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((7430:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((7430:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((7430:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.4238524542193 0.9057312499038 0.00000014618 cs_right_v7p43_2 0.10596307700982 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((7430:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.3038276558556) (-0.9527270099748) 0.00000010432 cs_right_v7p43_3 (-0.03375864001954) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((7430:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.6406981173236) 0.7677928903306 0.00000011512 cs_right_v7p43_4 (-0.04004363952773) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((7430:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.8206510517391 0.5714296555828 0.00000012885 cs_right_v7p43_5 0.03282603691556 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((7430:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.8206510517391 0.5714296555828 0.00000012885 cs_right_v7p43_5 56.2049 (by norm_num) (by norm_num) (-0.04038000336488) (-0.00161520013459) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.06498683437811:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((7430:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_14 : mainRemConst 5 (2:ℝ) 6.940419 ≤ 0.61167365 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 6.940419 (by norm_num) _ 0.04 1.60943791291421 0.61167365 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_14 : ∀ y ∈ Set.Icc (((6868:ℤ):ℝ)/1000) (((7430:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((6868:ℤ):ℝ)/1000) (((7430:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 6.940419 6.868 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.61167365 rb_right_14 0.04 7.694473 8.012797 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.013449516177 1.066602034512 (by rw [hrot]; exact bv_right_6p868_0_5) (by rw [hrot]; exact bv_right_7p43_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_7p992_0_5 : (1.115314662765:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((7992:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((7992:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((7992:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((7992:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((7992:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.736068157682 0.6769074288605 0.00000014224 cs_right_v7p992_2 0.1840170038605 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((7992:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.7992989881003) (-0.6009335467195) 0.00000010579 cs_right_v7p992_3 (-0.08881101043233) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((7992:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.0835925658568 0.9965000165245 0.00000012356 cs_right_v7p992_4 0.00522452764355 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((7992:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9564358681401 (-0.2919425116954) 0.00000012236 cs_right_v7p992_5 0.0382574298312 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((7992:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9564358681401 (-0.2919425116954) 0.00000012236 cs_right_v7p992_5 64.872064 (by norm_num) (by norm_num) 0.58433220342992 0.0233732881372 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.13868795090292:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((7992:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_15 : mainRemConst 5 (2:ℝ) 7.496992 ≤ 0.60505318 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 7.496992 (by norm_num) _ 0.04 1.60943791291421 0.60505318 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_15 : ∀ y ∈ Set.Icc (((7430:ℤ):ℝ)/1000) (((7992:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((7430:ℤ):ℝ)/1000) (((7992:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 7.496992 7.43 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.60505318 rb_right_15 0.04 8.238451 8.536514 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.066602034512 1.115314662765 (by rw [hrot]; exact bv_right_7p43_0_5) (by rw [hrot]; exact bv_right_7p992_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_8p554_0_5 : (1.157610451548:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((8554:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((8554:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((8554:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((8554:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((8554:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.9379921196888 0.3466565784774 0.00000012691 cs_right_v8p554_2 0.2344979981947 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((8554:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.9996287835538) (-0.0272450815369) 0.00000011216 cs_right_v8p554_3 (-0.11106987730163) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((8554:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.7596584331967 0.6503222777002 0.0000001538 cs_right_v8p554_4 0.04747864246229 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((8554:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.3616480881818 (-0.9323146788045) 0.00000011586 cs_right_v8p554_5 0.01446591889287 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((8554:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.3616480881818 (-0.9323146788045) 0.00000011586 cs_right_v8p554_5 74.170916 (by norm_num) (by norm_num) 0.69405576748384 0.02776223069936 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.18537268224823:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((8554:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_16 : mainRemConst 5 (2:ℝ) 8.054319 ≤ 0.59941457 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 8.054319 (by norm_num) _ 0.04 1.60943791291421 0.59941457 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_16 : ∀ y ∈ Set.Icc (((7992:ℤ):ℝ)/1000) (((8554:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((7992:ℤ):ℝ)/1000) (((8554:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 8.054319 7.992 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.59941457 rb_right_16 0.04 8.784698 9.064818 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.115314662765 1.157610451548 (by rw [hrot]; exact bv_right_7p992_0_5) (by rw [hrot]; exact bv_right_8p554_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_9p116_0_5 : (1.18981373848:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((9116:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((9116:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((9116:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((9116:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((9116:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.9993683643195 (-0.0355369159811) 0.00000011158 cs_right_v9p116_2 0.24984206318487 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((9116:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.8308451654776) 0.556503648631 0.00000011134 cs_right_v9p116_3 (-0.0923161418687) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((9116:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.9974742552051 (-0.0710289391939) 0.00000012314 cs_right_v9p116_4 0.06234213325406 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((9116:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.5093842279261) (-0.8605391962796) 0.00000010936 cs_right_v9p116_5 (-0.02037537349145) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((9116:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.5093842279261) (-0.8605391962796) 0.00000010936 cs_right_v9p116_5 84.101456 (by norm_num) (by norm_num) 0.24197356495875 0.00967894259835 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.19949268107878:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((9116:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_17 : mainRemConst 5 (2:ℝ) 8.612253 ≤ 0.59455589 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 8.612253 (by norm_num) _ 0.04 1.60943791291421 0.59455589 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_17 : ∀ y ∈ Set.Icc (((8554:ℤ):ℝ)/1000) (((9116:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((8554:ℤ):ℝ)/1000) (((9116:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 8.612253 8.554 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.59455589 rb_right_17 0.04 9.332817 9.596951 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.157610451548 1.18981373848 (by rw [hrot]; exact bv_right_8p554_0_5) (by rw [hrot]; exact bv_right_9p116_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_9p678_0_5 : (1.204907118781:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((9678:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((9678:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((9678:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((9678:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((9678:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.911000341941 (-0.4124055976624) 0.00000010862 cs_right_v9p678_2 0.22775005833025 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((9678:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.3552715692244) 0.9347631315464 0.00000011771 cs_right_v9p678_3 (-0.03947463188164) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((9678:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.6598432460334 (-0.7514032809777) 0.00000011722 cs_right_v9p678_4 0.04124019555083 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((9678:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9913239027868) (-0.1314416955976) 0.00000010684 cs_right_v9p678_5 (-0.03965296038508) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((9678:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9913239027868) (-0.1314416955976) 0.00000010684 cs_right_v9p678_5 94.663684 (by norm_num) (by norm_num) (-0.37611142918233) (-0.01504445716729) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.18986266161436:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((9678:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_18 : mainRemConst 5 (2:ℝ) 9.170684 ≤ 0.59032673 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 9.170684 (by norm_num) _ 0.04 1.60943791291421 0.59032673 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_18 : ∀ y ∈ Set.Icc (((9116:ℤ):ℝ)/1000) (((9678:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((9116:ℤ):ℝ)/1000) (((9678:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 9.170684 9.116 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.59032673 rb_right_18 0.04 9.882494 10.132309 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.18981373848 1.204907118781 (by rw [hrot]; exact bv_right_9p116_0_5) (by rw [hrot]; exact bv_right_9p678_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_10p24_0_5 : (1.19365319944:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((10240:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((10240:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((10240:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((10240:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((10240:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.6861290207596 (-0.72747987386) 0.00000012423 cs_right_v10p24_2 0.1715322241324 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((10240:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.2514862251695 0.9678608776833 0.00000012408 cs_right_v10p24_3 0.02794290012105 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((10240:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.0584539337429) (-0.9982901069477) 0.00000014844 cs_right_v10p24_4 (-0.00365338013644) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((10240:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.7160417855815) 0.6980574197548 0.00000010672 cs_right_v10p24_5 (-0.02864167569206) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((10240:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.7160417855815) 0.6980574197548 0.00000010672 cs_right_v10p24_5 105.8576 (by norm_num) (by norm_num) (-0.66182827539259) (-0.0264731310157) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.16718006842495:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((10240:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_19 : mainRemConst 5 (2:ℝ) 9.729526 ≤ 0.58661282 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 9.729526 (by norm_num) _ 0.04 1.60943791291421 0.58661282 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_19 : ∀ y ∈ Set.Icc (((9678:ℤ):ℝ)/1000) (((10240:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((9678:ℤ):ℝ)/1000) (((10240:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 9.729526 9.678 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.58661282 rb_right_19 0.04 10.433485 10.670408 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.204907118781 1.19365319944 (by rw [hrot]; exact bv_right_9p678_0_5) (by rw [hrot]; exact bv_right_10p24_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_10p802_0_5 : (1.14877355317:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((10802:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((10802:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((10802:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((10802:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((10802:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) 0.3584488745688 (-0.9335493582668) 0.00000013984 cs_right_v10p802_2 0.0896121836822 (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((10802:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.7653826097391 0.6435755283639 0.00000013044 cs_right_v10p802_3 0.08504249769989 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((10802:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.7430288755614) (-0.6692593593293) 0.00000013117 cs_right_v10p802_4 (-0.04643931292072) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((10802:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.1061881457906 0.9943460553014 0.00000011378 cs_right_v10p802_5 0.00424752128042 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((10802:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.1061881457906 0.9943460553014 0.00000011378 cs_right_v10p802_5 117.683204 (by norm_num) (by norm_num) (-0.40776658572873) (-0.01631066342914) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.13246288974179:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((10802:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_20 : mainRemConst 5 (2:ℝ) 10.288712 ≤ 0.58332585 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 10.288712 (by norm_num) _ 0.04 1.60943791291421 0.58332585 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_20 : ∀ y ∈ Set.Icc (((10240:ℤ):ℝ)/1000) (((10802:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((10240:ℤ):ℝ)/1000) (((10802:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 10.288712 10.24 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.58332585 rb_right_20 0.04 10.985591 11.210853 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.19365319944 1.14877355317 (by rw [hrot]; exact bv_right_10p24_0_5) (by rw [hrot]; exact bv_right_10p802_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_11p364_0_5 : (1.07009418261:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((11364:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((11364:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((11364:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((11364:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((11364:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.022940960471) (-0.9997368215348) 0.00000015027 cs_right_v11p364_2 (-0.00573527768525) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((11364:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.9966610968577 0.0816496050848 0.00000013681 cs_right_v11p364_3 0.11074010667195 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((11364:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.998947428644) 0.0458697528204 0.0000001077 cs_right_v11p364_4 (-0.0624342210215) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((11364:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.8473063665365 0.5311044353295 0.00000012083 cs_right_v11p364_5 0.03389224982826 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((11364:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.8473063665365 0.5311044353295 0.00000012083 cs_right_v11p364_5 130.140496 (by norm_num) (by norm_num) 0.15921687956571 0.00636867518263 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (1.07646285779346:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((11364:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_21 : mainRemConst 5 (2:ℝ) 10.848188 ≤ 0.5803965 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 10.848188 (by norm_num) _ 0.04 1.60943791291421 0.5803965 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_21 : ∀ y ∈ Set.Icc (((10802:ℤ):ℝ)/1000) (((11364:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((10802:ℤ):ℝ)/1000) (((11364:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 10.848188 10.802 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.5803965 rb_right_21 0.04 11.538653 11.753319 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.14877355317 1.07009418261 (by rw [hrot]; exact bv_right_10p802_0_5) (by rw [hrot]; exact bv_right_11p364_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_11p926_0_5 : (0.967425677766:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((11926:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((11926:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((11926:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((11926:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((11926:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.4008932536305) (-0.9161247727194) 0.00000013494 cs_right_v11p926_2 (-0.10022334714263) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((11926:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.8599219937134 (-0.5104254742153) 0.00000014317 cs_right_v11p926_3 0.09554687228259 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((11926:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.6785692665647) 0.7345364187387 0.00000013492 cs_right_v11p926_4 (-0.0424105875928) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((11926:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9412104532955 (-0.3378207847474) 0.00000012789 cs_right_v11p926_5 0.03764841301622 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((11926:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.9412104532955 (-0.3378207847474) 0.00000012789 cs_right_v11p926_5 143.229476 (by norm_num) (by norm_num) 0.5783918199147 0.02313567279659 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.99056135056338:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((11926:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_22 : mainRemConst 5 (2:ℝ) 11.407913 ≤ 0.57776964 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 11.407913 (by norm_num) _ 0.04 1.60943791291421 0.57776964 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_22 : ∀ y ∈ Set.Icc (((11364:ℤ):ℝ)/1000) (((11926:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((11364:ℤ):ℝ)/1000) (((11926:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 11.407913 11.364 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.57776964 rb_right_22 0.04 12.092539 12.29754 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 1.07009418261 0.967425677766 (by rw [hrot]; exact bv_right_11p364_0_5) (by rw [hrot]; exact bv_right_11p926_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_12p488_0_5 : (0.859088033822:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((12488:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((12488:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((12488:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((12488:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((12488:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.7187761383905) (-0.6952415859637) 0.00000011961 cs_right_v12p488_2 (-0.17969406450013) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((12488:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) 0.4056562800311 (-0.9140257012094) 0.00000014954 cs_right_v12p488_3 0.04507290338789 (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((12488:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.0332782814262 0.9994461246036 0.00000014638 cs_right_v12p488_4 0.00207988344038 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((12488:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.3161718618363 (-0.9487019309472) 0.00000013495 cs_right_v12p488_5 0.01264686907545 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((12488:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.3161718618363 (-0.9487019309472) 0.00000013495 cs_right_v12p488_5 156.950144 (by norm_num) (by norm_num) 0.52543893953279 0.02101755758132 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.88010559140359:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((12488:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_23 : mainRemConst 5 (2:ℝ) 11.967851 ≤ 0.57540089 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 11.967851 (by norm_num) _ 0.04 1.60943791291421 0.57540089 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_23 : ∀ y ∈ Set.Icc (((11926:ℤ):ℝ)/1000) (((12488:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((11926:ℤ):ℝ)/1000) (((12488:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 11.967851 11.926 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.57540089 rb_right_23 0.04 12.64714 12.843292 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.967425677766 0.859088033822 (by rw [hrot]; exact bv_right_11p926_0_5) (by rw [hrot]; exact bv_right_12p488_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_13p05_0_5 : (0.766715502854:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((13050:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((13050:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((13050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((13050:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((13050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9289583895565) (-0.3701841572986) 0.00000010428 cs_right_v13p05_2 (-0.23223962345913) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((13050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.1983983085332) (-0.980121477762) 0.00000015065 cs_right_v13p05_3 (-0.0220442732426) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((13050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.7259273841846 0.6877713521883 0.00000011572 cs_right_v13p05_4 0.04537045427903 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((13050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.5503742950452) (-0.8349180410943) 0.00000014201 cs_right_v13p05_5 (-0.02201497748221) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((13050:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.5503742950452) (-0.8349180410943) 0.00000014201 cs_right_v13p05_5 171.3025 (by norm_num) (by norm_num) 0.05890193101429 0.00235607724058 (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.76907158009509:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((13050:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_24 : mainRemConst 5 (2:ℝ) 12.527974 ≤ 0.57325409 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 12.527974 (by norm_num) _ 0.04 1.60943791291421 0.57325409 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_24 : ∀ y ∈ Set.Icc (((12488:ℤ):ℝ)/1000) (((13050:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((12488:ℤ):ℝ)/1000) (((13050:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 12.527974 12.488 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.57325409 rb_right_24 0.04 13.202368 13.390389 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.859088033822 0.766715502854 (by rw [hrot]; exact bv_right_12p488_0_5) (by rw [hrot]; exact bv_right_13p05_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_13p612_0_5 : (0.709259578929:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((13612:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((13612:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((13612:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((13612:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((13612:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9999465273173) 0.0103412689664 0.00000011071 cs_right_v13p612_2 (-0.24998665950683) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((13612:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.7291941346648) (-0.6843068857912) 0.00000014456 cs_right_v13p612_3 (-0.0810215865806) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((13612:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.9997861164486 (-0.0206814254016) 0.00000012858 cs_right_v13p612_4 0.06248662424178 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((13612:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9965175882135) (-0.0833828272185) 0.00000014906 cs_right_v13p612_5 (-0.03986070949094) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((13612:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.9965175882135) (-0.0833828272185) 0.00000014906 cs_right_v13p612_5 186.286544 (by norm_num) (by norm_num) (-0.44104775665673) (-0.01764191026626) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.69161766866341:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((13612:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_25 : mainRemConst 5 (2:ℝ) 13.088258 ≤ 0.57129954 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 13.088258 (by norm_num) _ 0.04 1.60943791291421 0.57129954 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_25 : ∀ y ∈ Set.Icc (((13050:ℤ):ℝ)/1000) (((13612:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((13050:ℤ):ℝ)/1000) (((13612:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 13.088258 13.05 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.57129954 rb_right_25 0.04 13.758145 13.938671 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.766715502854 0.709259578929 (by rw [hrot]; exact bv_right_13p05_0_5) (by rw [hrot]; exact bv_right_13p612_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_14p174_0_5 : (0.699167312962:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((14174:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((14174:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((14174:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((14174:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((14174:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.9211037646069) 0.3893171646387 0.00000012632 cs_right_v14p174_2 (-0.23027597273173) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((14174:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.9907346750295) (-0.1358116463314) 0.00000013848 cs_right_v14p174_3 (-0.11008164594559) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((14174:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) 0.6968642239444 (-0.7172030768104) 0.00000015441 cs_right_v14p174_4 0.0435540043459 (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((14174:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.6814718976333) 0.7318442817398 0.00000014894 cs_right_v14p174_5 (-0.02725888186294) (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((14174:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) (-0.6814718976333) 0.7318442817398 0.00000014894 cs_right_v14p174_5 201.902276 (by norm_num) (by norm_num) (-0.58074522891209) (-0.02322980915648) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.67593750380564:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((14174:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_26 : mainRemConst 5 (2:ℝ) 13.648682 ≤ 0.56951259 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 13.648682 (by norm_num) _ 0.04 1.60943791291421 0.56951259 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_26 : ∀ y ∈ Set.Icc (((13612:ℤ):ℝ)/1000) (((14174:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((13612:ℤ):ℝ)/1000) (((14174:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 13.648682 13.612 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.56951259 rb_right_26 0.04 14.314408 14.488005 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.709259578929 0.699167312962 (by rw [hrot]; exact bv_right_13p612_0_5) (by rw [hrot]; exact bv_right_14p174_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_14p793_0_5 : (0.748720761046:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((14793:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((14793:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((14793:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((14793:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((14793:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.6756515033325) 0.7372211649325 0.00000013123 cs_right_v14p793_2 (-0.16891290864063) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((14793:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.855744454522) 0.5173987132543 0.00000013913 cs_right_v14p793_3 (-0.09508273262808) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((14793:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.0869901845511) (-0.9962091686947) 0.0000001452 cs_right_v14p793_4 (-0.00543689560945) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((14793:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.2439822870358 0.9697796881832 0.00000011704 cs_right_v14p793_5 0.00975928679983 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((14793:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.2439822870358 0.9697796881832 0.00000011704 cs_right_v14p793_5 219.832849 (by norm_num) (by norm_num) (-0.20985027812226) (-0.00839401112489) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.74032674992167:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((14793:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_27 : mainRemConst 5 (2:ℝ) 14.209232 ≤ 0.56787262 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 14.209232 (by norm_num) _ 0.04 1.60943791291421 0.56787262 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_27 : ∀ y ∈ Set.Icc (((14174:ℤ):ℝ)/1000) (((14793:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((14174:ℤ):ℝ)/1000) (((14793:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 14.209232 14.174 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.56787262 rb_right_27 0.04 14.927587 15.094133 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.699167312962 0.748720761046 (by rw [hrot]; exact bv_right_14p174_0_5) (by rw [hrot]; exact bv_right_14p793_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)
lemma bv_right_15_0_5 : (0.779210762387:ℝ) ≤ ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * eulerMaclaurinMain 5 (((((2:ℝ):ℝ)):ℂ) + ((((((15000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re := by
  rw [re_main_split 5 (by norm_num) _ _ (by intro h; have := congrArg Complex.re h; norm_num at this)]
  have c0 : (0:ℝ) ≤ ∑ k ∈ Finset.range 0, (fun n : ℕ => ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((15000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re) k := by simp
  have c1 := sum_lb_step c0 (term_lb 1 (by norm_num) (2:ℝ) (((15000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 1 1 (pw1_lo (2:ℝ)) (pw1_hi (2:ℝ)) 1 0 0 (cs_one (((15000:ℤ):ℝ)/1000)) 1 (by norm_num) (by norm_num))
  have c2 := sum_lb_step c1 (term_lb 2 (by norm_num) (2:ℝ) (((15000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.25 0.25 (pwl_2_8_4 (2:ℝ) (by norm_num)) (pwh_2_8_4 (2:ℝ) (by norm_num)) (-0.5632935954295) 0.826256815608 0.00000010987 cs_right_v15_2 (-0.14082342632488) (by norm_num) (by norm_num))
  have c3 := sum_lb_step c2 (term_lb 3 (by norm_num) (2:ℝ) (((15000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.1111111111111 0.1111111111112 (pwl_3_8_4 (2:ℝ) (by norm_num)) (pwh_3_8_4 (2:ℝ) (by norm_num)) (-0.7170601161939) 0.6970113268357 0.0000001121 cs_right_v15_3 (-0.07967335869939) (by norm_num) (by norm_num))
  have c4 := sum_lb_step c3 (term_lb 4 (by norm_num) (2:ℝ) (((15000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.0625 0.0625 (pwl_4_8_4 (2:ℝ) (by norm_num)) (pwh_4_8_4 (2:ℝ) (by norm_num)) (-0.3654006440121) (-0.9308503474528) 0.00000011255 cs_right_v15_4 (-0.02283754728514) (by norm_num) (by norm_num))
  have c5 := sum_lb_step c4 (term_lb 5 (by norm_num) (2:ℝ) (((15000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.5477092431889 0.8366687426487 0.00000015002 cs_right_v15_5 0.02190836372675 (by norm_num) (by norm_num))
  have ht := tail_ub 5 (by norm_num) (2:ℝ) (((15000:ℤ):ℝ)/1000) (1:ℝ) (0:ℝ) (by norm_num) 0.04 0.04 (pwl_5_8_4 (2:ℝ) (by norm_num)) (pwh_5_8_4 (2:ℝ) (by norm_num)) 0.5477092431889 0.8366687426487 0.00000015002 cs_right_v15_5 226 (by norm_num) (by norm_num) (-0.0159182742504) (-0.00063673097001) (by norm_num [abs_of_nonneg, abs_of_nonpos]) (by norm_num) (by norm_num)
  have cN : (0.77857403141734:ℝ) ≤ ∑ n ∈ Finset.range 5, ((((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I) * ez (Real.log ((n + 1 : ℕ) : ℝ)) (((((2:ℝ):ℝ)):ℂ) + ((((((15000:ℤ):ℝ)/1000):ℝ)):ℂ) * I)).re :=
    le_trans (by norm_num) c5
  linarith [cN, ht]
lemma rb_right_28 : mainRemConst 5 (2:ℝ) 14.826761 ≤ 0.56621572 := by
  have c0 : ∑ k ∈ Finset.range 0, (fun n : ℕ => Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * (2:ℝ))) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) k ≤ 0 := by simp
  have c1 := sum_ub_step c0 (remTerm_ub 1 (by norm_num) (2:ℝ) 1 0 (pw1_hi (2:ℝ)) (lg_1).2 0 (by norm_num))
  have c2 := sum_ub_step c1 (remTerm_ub 2 (by norm_num) (2:ℝ) 0.25 0.6931471808 (pwh_2_8_4 (2:ℝ) (by norm_num)) (lg_2).2 0.12011325356275 (by norm_num))
  have c3 := sum_ub_step c2 (remTerm_ub 3 (by norm_num) (2:ℝ) 0.1111111111112 1.098612288908165 (pwh_3_8_4 (2:ℝ) (by norm_num)) (lg_3).2 0.13410544014901 (by norm_num))
  have c4 := sum_ub_step c3 (remTerm_ub 4 (by norm_num) (2:ℝ) 0.0625 1.3862943616 (pwh_4_8_4 (2:ℝ) (by norm_num)) (lg_4).2 0.12011325356275 (by norm_num))
  have c5 := sum_ub_step c4 (remTerm_ub 5 (by norm_num) (2:ℝ) 0.04 1.60943791291421 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 0.10361161582103 (by norm_num))
  exact mainRemConst_le 5 (by norm_num) (2:ℝ) 14.826761 (by norm_num) _ 0.04 1.60943791291421 0.56621572 c5 (pwh_5_8_4 (2:ℝ) (by norm_num)) (lg_5).2 (by norm_num)
lemma pc_right_28 : ∀ y ∈ Set.Icc (((14793:ℤ):ℝ)/1000) (((15000:ℤ):ℝ)/1000), 0 < (I ^ ((0):ℤ) * riemannZeta (((2:ℝ):ℂ) + (y:ℂ) * I)).re := by
  have hrot : I ^ ((0):ℤ) = ((1:ℝ):ℂ) + ((0:ℝ):ℂ) * I := (by rw [I_zpow_eq (0) (0) 0 (by norm_num), rot0])
  refine vertical_piece 5 (by norm_num) (2:ℝ) (((14793:ℤ):ℝ)/1000) (((15000:ℤ):ℝ)/1000) (I ^ ((0):ℤ)) (norm_I_zpow _).le (by norm_num) (by norm_num) (by norm_num) 1.60943791291421 (lg_5).2 (by norm_num) 14.826761 14.793 (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2]) 0.56621572 rb_right_28 0.04 15.132746 15.297059 (pwh_5_8_4 (2:ℝ) (by norm_num)) (by norm_num) (by norm_num) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) (fun y hy => by nlinarith [hy.1, hy.2, mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]) 0.748720761046 0.779210762387 (by rw [hrot]; exact bv_right_14p793_0_5) (by rw [hrot]; exact bv_right_15_0_5) (by rw [lt_min_iff]; constructor <;> norm_num)

def yL_right : List ℤ := [-1000, -438, 124, 686, 1248, 1810, 2372, 2934, 3496, 4058, 4620, 5182, 5744, 6306, 6868, 7430, 7992, 8554, 9116, 9678, 10240, 10802, 11364, 11926, 12488, 13050, 13612, 14174, 14793, 15000]
def zL_right : List ℤ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
noncomputable def yF_right (k : ℕ) : ℝ := ((yL_right.getD k 0 : ℤ) : ℝ) / 1000
def zF_right (k : ℕ) : ℤ := zL_right.getD k 0

theorem side_right : I * ∫ t in (-1:ℝ)..(15:ℝ), logDeriv zetaFactor (((2:ℝ):ℂ) + (t:ℂ) * I) =
    log (I ^ ((-2):ℤ) * I ^ ((0):ℤ) * zetaFactor (((2:ℝ):ℂ) + (((15:ℝ)):ℂ) * I)) -
      log (I ^ ((-2):ℤ) * I ^ ((0):ℤ) * zetaFactor (((2:ℝ):ℂ) + (((-1:ℝ)):ℂ) * I)) -
      ((((0) - (0) : ℤ)) : ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  have h := vertical_side (2:ℝ) (by norm_num) yF_right zF_right (-2) 28 (list_mono yL_right 1000 (by norm_num) 29 (by decide)) (by decide) (fun t _ => u1_right t)
    (fun k hk => by interval_cases k; exacts [pc_right_0, pc_right_1, pc_right_2, pc_right_3, pc_right_4, pc_right_5, pc_right_6, pc_right_7, pc_right_8, pc_right_9, pc_right_10, pc_right_11, pc_right_12, pc_right_13, pc_right_14, pc_right_15, pc_right_16, pc_right_17, pc_right_18, pc_right_19, pc_right_20, pc_right_21, pc_right_22, pc_right_23, pc_right_24, pc_right_25, pc_right_26, pc_right_27, pc_right_28])
  have e0 : yF_right 0 = -1 := by norm_num [yF_right, yL_right]
  have e1 : yF_right (28 + 1) = 15 := by norm_num [yF_right, yL_right]
  have f0 : zF_right 0 = 0 := rfl
  have f1 : zF_right 28 = 0 := rfl
  rw [e0, e1, f0, f1] at h
  exact h

theorem nz_right : ∀ t ∈ Set.Icc (-1:ℝ) (15:ℝ), riemannZeta (((2:ℝ):ℂ) + (t:ℂ) * I) ≠ 0 := by
  have h := cover yF_right (fun t => riemannZeta (((2:ℝ):ℂ) + (t:ℂ) * I) ≠ 0) 28 (list_mono yL_right 1000 (by norm_num) 29 (by decide))
    (fun k hk t ht => by interval_cases k; exacts [zeta_ne_of_re_pos (pc_right_0 t ht), zeta_ne_of_re_pos (pc_right_1 t ht), zeta_ne_of_re_pos (pc_right_2 t ht), zeta_ne_of_re_pos (pc_right_3 t ht), zeta_ne_of_re_pos (pc_right_4 t ht), zeta_ne_of_re_pos (pc_right_5 t ht), zeta_ne_of_re_pos (pc_right_6 t ht), zeta_ne_of_re_pos (pc_right_7 t ht), zeta_ne_of_re_pos (pc_right_8 t ht), zeta_ne_of_re_pos (pc_right_9 t ht), zeta_ne_of_re_pos (pc_right_10 t ht), zeta_ne_of_re_pos (pc_right_11 t ht), zeta_ne_of_re_pos (pc_right_12 t ht), zeta_ne_of_re_pos (pc_right_13 t ht), zeta_ne_of_re_pos (pc_right_14 t ht), zeta_ne_of_re_pos (pc_right_15 t ht), zeta_ne_of_re_pos (pc_right_16 t ht), zeta_ne_of_re_pos (pc_right_17 t ht), zeta_ne_of_re_pos (pc_right_18 t ht), zeta_ne_of_re_pos (pc_right_19 t ht), zeta_ne_of_re_pos (pc_right_20 t ht), zeta_ne_of_re_pos (pc_right_21 t ht), zeta_ne_of_re_pos (pc_right_22 t ht), zeta_ne_of_re_pos (pc_right_23 t ht), zeta_ne_of_re_pos (pc_right_24 t ht), zeta_ne_of_re_pos (pc_right_25 t ht), zeta_ne_of_re_pos (pc_right_26 t ht), zeta_ne_of_re_pos (pc_right_27 t ht), zeta_ne_of_re_pos (pc_right_28 t ht)])
  have e0 : yF_right 0 = -1 := by norm_num [yF_right, yL_right]
  have e1 : yF_right (28 + 1) = 15 := by norm_num [yF_right, yL_right]
  rw [e0, e1] at h
  exact h

end Cert
end ZB
end RHV6Fresh
