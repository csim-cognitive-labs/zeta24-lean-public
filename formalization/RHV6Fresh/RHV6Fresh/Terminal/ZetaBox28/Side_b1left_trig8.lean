/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Base
/-!
# Certificat (V2), côté b1left (b1), angles 8

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

lemma cs_b1left_v21p163_49 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.776827682962:ℝ):ℂ) + (((-0.6297132291638):ℝ):ℂ) * I)‖ ≤ 0.00000014644 := by
  have hl := lg_49
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.362592946910271572 82.362592989236356224 (-0.681184) 0.00000004643 0.776827682962 (-0.6297132291638) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_50 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4457952041465:ℝ):ℂ) + (((-0.8951349819776):ℝ):ℂ) * I)‖ ≤ 0.00000015698 := by
  have hl := lg_50
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.790142836369710134 82.79014288927725246 (-1.1087339) 0.00000005697 0.4457952041465 (-0.8951349819776) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_51 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0429661958611:ℝ):ℂ) + (((-0.999076526605):ℝ):ℂ) * I)‖ ≤ 0.00000015551 := by
  have hl := lg_51
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.209225837838767474 83.2092258907463098 (-1.5278169) 0.0000000555 0.0429661958611 (-0.999076526605) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_52 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3597178398904):ℝ):ℂ) + (((-0.9330611317926):ℝ):ℂ) * I)‖ ≤ 0.00000014842 := by
  have hl := lg_52
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.6201707888326171 83.620170841740159426 (-1.9387618) 0.00000004841 (-0.3597178398904) (-0.9330611317926) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_53 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6969119496884):ℝ):ℂ) + (((-0.7171567013967):ℝ):ℂ) * I)‖ ≤ 0.00000015435 := by
  have hl := lg_53
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.023287738997414222 84.023287791904977711 (-2.3418788) 0.00000005434 (-0.6969119496884) (-0.7171567013967) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_54 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9194439594083):ℝ):ℂ) + (((-0.3932210642445):ℝ):ℂ) * I)‖ ≤ 0.00000013791 := by
  have hl := lg_54
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.418869355434824196 84.418869397760887685 (-2.7374604) 0.0000000379 (-0.9194439594083) (-0.3932210642445) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_55 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998750328714):ℝ):ℂ) + (((-0.0158087947414):ℝ):ℂ) * I)‖ ≤ 0.00000013116 := by
  have hl := lg_55
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.807192171568618946 84.807192224476182435 (-3.1257832) 0.00000003115 (-0.9998750328714) (-0.0158087947414) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_56 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9339393960253):ℝ):ℂ) + ((0.3574313981519:ℝ):ℂ) * I)‖ ≤ 0.00000015593 := by
  have hl := lg_56
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.188517803521835786 85.188517856429378112 2.7760765 0.00000005592 (-0.9339393960253) 0.3574313981519 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_57 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7384062826662):ℝ):ℂ) + ((0.6743561089572:ℝ):ℂ) * I)‖ ≤ 0.00000014135 := by
  have hl := lg_57
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.563093959177654021 85.563094001503738673 2.4015003 0.00000004134 (-0.7384062826662) 0.6743561089572 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_58 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4463144384432):ℝ):ℂ) + ((0.8948762048645:ℝ):ℂ) * I)‖ ≤ 0.0000001571 := by
  have hl := lg_58
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.931155404687742796 85.931155457595306285 2.0334389 0.00000005709 (-0.4463144384432) 0.8948762048645 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_59 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1007020899629):ℝ):ℂ) + ((0.9949166241835:ℝ):ℂ) * I)‖ ≤ 0.00000015028 := by
  have hl := lg_59
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.292924897870608696 86.292924950778193348 1.6716694 0.00000005027 (-0.1007020899629) 0.9949166241835 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_60 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2520673802486:ℝ):ℂ) + ((0.9677096857088:ℝ):ℂ) * I)‖ ≤ 0.00000015773 := by
  have hl := lg_60
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.648613942800179799 86.648613995707722125 1.3159803 0.00000005772 0.2520673802486 0.9677096857088 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_61 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5684541136621:ℝ):ℂ) + ((0.8227149692698:ℝ):ℂ) * I)‖ ≤ 0.00000014054 := by
  have hl := lg_61
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((61:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.998423559993637029 86.998423612901200518 0.9661707 0.00000004053 0.5684541136621 0.8227149692698 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_62 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8126860331477:ℝ):ℂ) + ((0.5827018204251:ℝ):ℂ) * I)‖ ≤ 0.00000013733 := by
  have hl := lg_62
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((62:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.342544963203117169 87.342545016110680658 0.6220493 0.00000003732 0.8126860331477 0.5827018204251 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_63 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.960100740365:ℝ):ℂ) + ((0.2796543730225:ℝ):ℂ) * I)‖ ≤ 0.00000013445 := by
  have hl := lg_63
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((63:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 87.68116019261908525 87.681160234945169902 0.2834341 0.00000003444 0.960100740365 0.2796543730225 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_64 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9987578257601:ℝ):ℂ) + (((-0.0498277581575):ℝ):ℂ) * I)‖ ≤ 0.0000001404 := by
  have hl := lg_64
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((64:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.0144426601334 88.0144427236224 (-0.0498484) 0.00000004039 0.9987578257601 (-0.0498277581575) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_65 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9294180888506:ℝ):ℂ) + (((-0.3690284760249):ℝ):ℂ) * I)‖ ≤ 0.00000013523 := by
  have hl := lg_65
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((65:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.342557765295222167 88.342557818202785656 (-0.3779635) 0.00000003522 0.9294180888506 (-0.3690284760249) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_66 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7641530816921:ℝ):ℂ) + (((-0.6450349352868):ℝ):ℂ) * I)‖ ≤ 0.00000013041 := by
  have hl := lg_66
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((66:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.665663277999088611 88.6656633309066521 (-0.701069) 0.0000000304 0.7641530816921 (-0.6450349352868) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_67 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5239490113632:ℝ):ℂ) + (((-0.8517496307552):ℝ):ℂ) * I)‖ ≤ 0.00000012907 := by
  have hl := lg_67
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((67:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 88.983909876664848631 88.983909929572433283 (-1.0193156) 0.00000002906 0.5239490113632 (-0.8517496307552) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_68 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2357099397175:ℝ):ℂ) + (((-0.9718234532663):ℝ):ℂ) * I)‖ ≤ 0.00000016889 := by
  have hl := lg_68
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((68:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.297441531634592742 89.297441595123613905 (-1.3328473) 0.00000006888 0.2357099397175 (-0.9718234532663) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_69 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0709457228668):ℝ):ℂ) + (((-0.9974801774504):ℝ):ℂ) * I)‖ ≤ 0.00000017124 := by
  have hl := lg_69
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((69:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.60639592928562739 89.606395982193212042 (-1.6418017) 0.00000007123 (-0.0709457228668) (-0.9974801774504) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_70 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3667509227349):ℝ):ℂ) + (((-0.9303191713979):ℝ):ℂ) * I)‖ ≤ 0.00000013239 := by
  have hl := lg_70
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((70:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 89.910904779984440853 89.910904832892004342 (-1.9463105) 0.00000003238 (-0.3667509227349) (-0.9303191713979) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_71 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6254464465061):ℝ):ℂ) + (((-0.7802670969217):ℝ):ℂ) * I)‖ ≤ 0.00000016273 := by
  have hl := lg_71
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((71:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.211094210319205681 90.211094263226790333 (-2.2464999) 0.00000006272 (-0.6254464465061) (-0.7802670969217) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_72 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8258424135529):ℝ):ℂ) + (((-0.5639009735021):ℝ):ℂ) * I)‖ ≤ 0.0000001513 := by
  have hl := lg_72
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((72:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.507085049230649464 90.50708510213819179 (-2.5424908) 0.00000005129 (-0.8258424135529) (-0.5639009735021) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_73 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9531858885691):ℝ):ℂ) + (((-0.3023849560092):ℝ):ℂ) * I)‖ ≤ 0.00000017501 := by
  have hl := lg_73
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((73:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 90.798993125517255069 90.798993178424818558 (-2.8343989) 0.000000075 (-0.9531858885691) (-0.3023849560092) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_74 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9998145825814):ℝ):ℂ) + (((-0.0192561630732):ℝ):ℂ) * I)‖ ≤ 0.00000016056 := by
  have hl := lg_74
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((74:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 91.086929539973706046 91.086929592881269535 (-3.1223353) 0.00000006055 (-0.9998145825814) (-0.0192561630732) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_75 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.965141211362):ℝ):ℂ) + ((0.2617297114946:ℝ):ℂ) * I)‖ ≤ 0.00000016449 := by
  have hl := lg_75
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((75:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.371000919262784866 91.371000972170348355 2.8767787 0.00000006448 (-0.965141211362) 0.2617297114946 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_76 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.855063646637):ℝ):ℂ) + ((0.5185230565006:ℝ):ℂ) * I)‖ ≤ 0.00000015474 := by
  have hl := lg_76
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((76:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.651309652973479289 91.651309705881042778 2.5964699 0.00000005473 (-0.855063646637) 0.5185230565006 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_77 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6809280957491):ℝ):ℂ) + ((0.7323502771207:ℝ):ℂ) * I)‖ ≤ 0.00000016041 := by
  have hl := lg_77
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((77:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 91.927954115183349665 91.927954168090934317 2.3198255 0.0000000604 (-0.6809280957491) 0.7323502771207 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_78 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4581869559168):ℝ):ℂ) + ((0.8888558451307:ℝ):ℂ) * I)‖ ≤ 0.00000013598 := by
  have hl := lg_78
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((78:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.201028871725691832 92.201028924633255321 2.0467507 0.00000003597 (-0.4581869559168) 0.8888558451307 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_79 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2048969018946):ℝ):ℂ) + ((0.978783561158:ℝ):ℂ) * I)‖ ≤ 0.00000013346 := by
  have hl := lg_79
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((79:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.470624874253421759 92.470624927161006411 1.7771547 0.00000003345 (-0.2048969018946) 0.978783561158 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p163_80 : ‖exp (-((((((21163:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0598107089166:ℝ):ℂ) + ((0.9982097370286:ℝ):ℂ) * I)‖ ≤ 0.00000017111 := by
  have hl := lg_80
  refine (ecis_approx ((((21163:ℤ):ℝ)/1000) * Real.log ((80:ℕ):ℝ)) (15) 94.2477796076937971538 94.2477796076937971541 92.736829636596005067 92.73682970008502623 1.5109499 0.0000000711 0.0598107089166 0.9982097370286 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_2 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5249882207868):ℝ):ℂ) + (((-0.8511094923849):ℝ):ℂ) * I)‖ ≤ 0.00000012228 := by
  have hl := lg_2
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.6898681920979 14.6898682026944 (-2.1234976) 0.00000002227 (-0.5249882207868) (-0.8511094923849) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_3 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2754470137607):ℝ):ℂ) + ((0.9613162552505:ℝ):ℂ) * I)‖ ≤ 0.00000011013 := by
  have hl := lg_3
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.282890228234219652 23.282890238830740845 1.849851 0.00000001012 (-0.2754470137607) 0.9613162552505 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_4 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4487747296536):ℝ):ℂ) + ((0.8936449194282:ℝ):ℂ) * I)‖ ≤ 0.00000015172 := by
  have hl := lg_4
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.3797363841958 29.3797364053888 2.0361901 0.00000005171 (-0.4487747296536) 0.8936449194282 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_5 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9010111225354):ℝ):ℂ) + (((-0.4337959854008):ℝ):ℂ) * I)‖ ≤ 0.00000015251 := by
  have hl := lg_5
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.108817667197831337 34.10881768839085253 (-2.6928911) 0.0000000525 (-0.9010111225354) (-0.4337959854008) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_6 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9627918277076:ℝ):ℂ) + (((-0.2702441423962):ℝ):ℂ) * I)‖ ≤ 0.00000012276 := by
  have hl := lg_6
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 37.972758420332119652 37.972758441525140845 (-0.2736466) 0.00000002275 0.9627918277076 (-0.2702441423962) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_7 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9214618961589):ℝ):ℂ) + ((0.3884687552199:ℝ):ℂ) * I)‖ ≤ 0.00000014886 := by
  have hl := lg_7
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.239673777911198446 41.239673799104240832 2.7426234 0.00000004885 (-0.9214618961589) 0.3884687552199 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_8 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9961911293275:ℝ):ℂ) + (((-0.0871965242957):ℝ):ℂ) * I)‖ ≤ 0.00000015784 := by
  have hl := lg_8
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.0696045762937 44.0696046080832 (-0.0873074) 0.00000005783 0.9961911293275 (-0.0871965242957) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_9 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8482578814008):ℝ):ℂ) + (((-0.5295833896269):ℝ):ℂ) * I)‖ ≤ 0.00000012742 := by
  have hl := lg_9
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.565780456468439304 46.56578047766148169 (-2.5834833) 0.00000002741 (-0.8482578814008) (-0.5295833896269) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_10 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1038123522993:ℝ):ℂ) + ((0.9945969010157:ℝ):ℂ) * I)‖ ≤ 0.00000013366 := by
  have hl := lg_10
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.798685859295731337 48.79868589108525253 1.4667966 0.00000003365 0.1038123522993 0.9945969010157 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_11 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8508937413425:ℝ):ℂ) + (((-0.5253378350587):ℝ):ℂ) * I)‖ ≤ 0.00000015756 := by
  have hl := lg_11
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.818594499888769869 50.818594531678312255 (-0.5531121) 0.00000005755 0.8508937413425 (-0.5253378350587) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_12 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7354617234677):ℝ):ℂ) + (((-0.6775662722446):ℝ):ℂ) * I)‖ ≤ 0.00000014502 := by
  have hl := lg_12
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.662626612430019652 52.662626644219540845 (-2.3971442) 0.00000004501 (-0.7354617234677) (-0.6775662722446) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_13 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5801392767085):ℝ):ℂ) + ((0.8145172923944:ℝ):ℂ) * I)‖ ≤ 0.00000014848 := by
  have hl := lg_13
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.3589717161552681 54.358971747944810486 2.189696 0.00000004847 (-0.5801392767085) 0.8145172923944 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_14 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8143860865418:ℝ):ℂ) + ((0.5803234460601:ℝ):ℂ) * I)‖ ≤ 0.0000001372 := by
  have hl := lg_14
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.929541970009098446 55.929542001798640832 0.6191258 0.00000003719 0.8143860865418 0.5803234460601 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_15 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6651959553666:ℝ):ℂ) + (((-0.7466688295114):ℝ):ℂ) * I)‖ ≤ 0.00000016262 := by
  have hl := lg_15
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.391707895432050989 57.391707927221593375 (-0.8430401) 0.00000006261 0.6651959553666 (-0.7466688295114) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_16 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5972023980801):ℝ):ℂ) + (((-0.8020905782489):ℝ):ℂ) * I)‖ ≤ 0.00000014618 := by
  have hl := lg_16
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.7594727683916 58.7594728107776 (-2.210805) 0.00000004617 (-0.5972023980801) (-0.8020905782489) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_17 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9379832263351):ℝ):ℂ) + ((0.3466806411365:ℝ):ℂ) * I)‖ ≤ 0.00000014915 := by
  have hl := lg_17
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.044290378547285762 60.044290420933306955 2.7875627 0.00000004914 (-0.9379832263351) 0.3466806411365 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_18 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0054080468433):ℝ):ℂ) + ((0.9999853764076:ℝ):ℂ) * I)‖ ≤ 0.00000012324 := by
  have hl := lg_18
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.255648648566339304 61.25564868035588169 1.5762044 0.00000002323 (-0.0054080468433) 0.9999853764076 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_19 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9088165351217:ℝ):ℂ) + ((0.4171960036834:ℝ):ℂ) * I)‖ ≤ 0.00000012896 := by
  have hl := lg_19
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.401495268947277379 62.401495300736840958 0.4303578 0.00000002895 0.9088165351217 0.4171960036834 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_20 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7920106014259:ℝ):ℂ) + (((-0.6105073359338):ℝ):ℂ) * I)‖ ≤ 0.000000122 := by
  have hl := lg_20
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.488554051393631337 63.48855409377965253 (-0.656701) 0.00000002199 0.7920106014259 (-0.6105073359338) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_21 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1196274936745):ℝ):ℂ) + (((-0.9928188468984):ℝ):ℂ) * I)‖ ≤ 0.00000016567 := by
  have hl := lg_21
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.522564006145418098 64.522564037934981677 (-1.690711) 0.00000006566 (-0.1196274936745) (-0.9928188468984) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_22 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8938291646036):ℝ):ℂ) + (((-0.448407654255):ℝ):ℂ) * I)‖ ≤ 0.00000016259 := by
  have hl := lg_22
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.508462691986669869 65.508462734372712255 (-2.6766096) 0.00000006258 (-0.8938291646036) (-0.448407654255) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_23 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8883380864999):ℝ):ℂ) + ((0.4591899867917:ℝ):ℂ) * I)‖ ≤ 0.00000015958 := by
  have hl := lg_23
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.450528896150333638 66.450528938536397217 2.6645095 0.00000005957 (-0.8883380864999) 0.4591899867917 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_24 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1905744355013):ℝ):ℂ) + ((0.9816727481868:ℝ):ℂ) * I)‖ ≤ 0.00000016795 := by
  have hl := lg_24
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.352494804527919652 67.352494846913940845 1.7625436 0.00000006794 (-0.1905744355013) 0.9816727481868 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_25 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6236421697735:ℝ):ℂ) + ((0.7817099488174:ℝ):ℂ) * I)‖ ≤ 0.00000014459 := by
  have hl := lg_25
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.217635334395662674 68.21763537678170506 0.897403 0.00000004458 0.6236421697735 0.7817099488174 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_26 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9978096859653:ℝ):ℂ) + ((0.0661500611773:ℝ):ℂ) * I)‖ ≤ 0.00000017074 := by
  have hl := lg_26
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.0488399082531681 69.048839950639210486 0.0661984 0.00000007073 0.9978096859653 0.0661500611773 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_27 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7427472213337:ℝ):ℂ) + (((-0.6695719268316):ℝ):ℂ) * I)‖ ≤ 0.00000013753 := by
  have hl := lg_27
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.848670684702658956 69.848670716492222535 (-0.7336323) 0.00000003752 0.7427472213337 (-0.6695719268316) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_28 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0663756909904:ℝ):ℂ) + (((-0.9977947021534):ℝ):ℂ) * I)‖ ≤ 0.00000012553 := by
  have hl := lg_28
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.619410162106998446 70.619410204493040832 (-1.5043718) 0.00000002552 0.0663756909904 (-0.9977947021534) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_29 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.626664616078):ℝ):ℂ) + (((-0.7792890727717):ℝ):ℂ) * I)‖ ≤ 0.00000016629 := by
  have hl := lg_29
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.363100502867243556 71.363100545253307135 (-2.2480621) 0.00000006628 (-0.626664616078) (-0.7792890727717) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_30 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9847169694002):ℝ):ℂ) + (((-0.174162251414):ℝ):ℂ) * I)‖ ≤ 0.00000015096 := by
  have hl := lg_30
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.081576087529950989 72.081576129915993375 (-2.9665377) 0.00000005095 (-0.9847169694002) (-0.174162251414) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_31 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8678888567759):ℝ):ℂ) + ((0.4967584243856:ℝ):ℂ) * I)‖ ≤ 0.00000015886 := by
  have hl := lg_31
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.776490802617578059 72.776490845003641638 2.6217329 0.00000005885 (-0.8678888567759) 0.4967584243856 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_32 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3691426738185):ℝ):ℂ) + ((0.9293727381215:ℝ):ℂ) * I)‖ ≤ 0.00000012733 := by
  have hl := lg_32
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.4493409604895 73.449341013472 1.9488827 0.00000002732 (-0.3691426738185) 0.9293727381215 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_33 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2706396602601:ℝ):ℂ) + ((0.9626807229265:ℝ):ℂ) * I)‖ ≤ 0.00000015805 := by
  have hl := lg_33
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.101484728122989521 74.1014847705090531 1.2967389 0.00000005804 0.2706396602601 0.9626807229265 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_34 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.78749332973:ℝ):ℂ) + ((0.6163231746663:ℝ):ℂ) * I)‖ ≤ 0.00000013749 := by
  have hl := lg_34
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.734158570645185762 74.734158623627706955 0.6640651 0.00000003748 0.78749332973 0.6163231746663 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_35 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9987636090027:ℝ):ℂ) + ((0.049711702162:ℝ):ℂ) * I)‖ ≤ 0.00000014106 := by
  have hl := lg_35
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.348491445109029783 75.348491487495093362 0.0497322 0.00000004105 0.9987636090027 0.049711702162 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_36 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8539362070011:ℝ):ℂ) + (((-0.5203777035698):ℝ):ℂ) * I)‖ ≤ 0.00000014551 := by
  have hl := lg_36
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.945516840664239304 75.94551688305028169 (-0.5472932) 0.0000000455 0.8539362070011 (-0.5203777035698) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_37 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4285042811393:ℝ):ℂ) + (((-0.9035397506725):ℝ):ℂ) * I)‖ ≤ 0.00000015688 := by
  have hl := lg_37
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.526183300632939306 76.526183343019002885 (-1.1279596) 0.00000005687 0.4285042811393 (-0.9035397506725) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_38 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1220384968737):ℝ):ℂ) + (((-0.9925253675752):ℝ):ℂ) * I)‖ ≤ 0.00000012512 := by
  have hl := lg_38
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.091363461045177379 77.091363503431240958 (-1.6931398) 0.00000002511 (-0.1220384968737) (-0.9925253675752) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_39 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6232110764169):ℝ):ℂ) + (((-0.7820536773248):ℝ):ℂ) * I)‖ ≤ 0.00000014178 := by
  have hl := lg_39
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.641861944389487752 77.641861986775551331 (-2.2436383) 0.00000004177 (-0.6232110764169) (-0.7820536773248) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_40 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9354048252165):ℝ):ℂ) + (((-0.3535785807876):ℝ):ℂ) * I)‖ ≤ 0.00000014268 := by
  have hl := lg_40
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.178422243491531337 78.17842229647405253 (-2.7801986) 0.00000004267 (-0.9354048252165) (-0.3535785807876) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_41 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9869201445119):ℝ):ℂ) + ((0.161209887973:ℝ):ℂ) * I)‖ ≤ 0.00000014178 := by
  have hl := lg_41
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.70173278211926394 78.701732835101806326 2.9796762 0.00000004177 (-0.9869201445119) 0.161209887973 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_42 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.782194577579):ℝ):ℂ) + ((0.6230342227864:ℝ):ℂ) * I)‖ ≤ 0.00000014731 := by
  have hl := lg_42
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.212432198243318098 79.212432240629381677 2.4689768 0.0000000473 (-0.782194577579) 0.6230342227864 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_43 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3889564487105):ℝ):ℂ) + ((0.9212561429936:ℝ):ℂ) * I)‖ ≤ 0.00000016349 := by
  have hl := lg_43
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.71111402985755954 79.711114072243644312 1.9702949 0.00000006348 (-0.3889564487105) 0.9212561429936 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_44 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0876057789345:ℝ):ℂ) + ((0.9961552225919:ℝ):ℂ) * I)‖ ≤ 0.00000014375 := by
  have hl := lg_44
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.198330884084569869 80.198330937067112255 1.4830781 0.00000004374 0.0876057789345 0.9961552225919 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_45 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5345587281405:ℝ):ℂ) + ((0.8451313307225:ℝ):ℂ) * I)‖ ≤ 0.00000016968 := by
  have hl := lg_45
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.674598123666270641 80.67459816605233422 1.0068108 0.00000006967 0.5345587281405 0.8451313307225 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_46 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8571879881209:ℝ):ℂ) + ((0.5150036436971:ℝ):ℂ) * I)‖ ≤ 0.00000014791 := by
  have hl := lg_46
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.140397088248233638 81.140397141230797217 0.5410119 0.0000000479 0.8571879881209 0.5150036436971 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_47 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9963700450663:ℝ):ℂ) + ((0.0851277469131:ℝ):ℂ) * I)‖ ≤ 0.00000015516 := by
  have hl := lg_47
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.596178095496102497 81.596178148478687269 0.0852309 0.00000005515 0.9963700450663 0.0851277469131 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_48 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9355603282231:ℝ):ℂ) + (((-0.3531669184043):ℝ):ℂ) * I)‖ ≤ 0.00000015629 := by
  have hl := lg_48
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.042362996625819652 82.042363049608340845 (-0.360954) 0.00000005628 0.9355603282231 (-0.3531669184043) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_49 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6981839858639:ℝ):ℂ) + (((-0.7159183765509):ℝ):ℂ) * I)‖ ≤ 0.00000013753 := by
  have hl := lg_49
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.479347555822396892 82.479347598208481664 (-0.7979386) 0.00000003752 0.6981839858639 (-0.7159183765509) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_50 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3379159646163:ℝ):ℂ) + (((-0.9411762857496):ℝ):ℂ) * I)‖ ≤ 0.00000016686 := by
  have hl := lg_50
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.907503526493562674 82.90750357947610506 (-1.2260946) 0.00000006685 0.3379159646163 (-0.9411762857496) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_51 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0749050499665):ℝ):ℂ) + (((-0.9971906705787):ℝ):ℂ) * I)‖ ≤ 0.00000016644 := by
  have hl := lg_51
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.327180606781505414 83.3271806597640478 (-1.6457716) 0.00000006643 (-0.0749050499665) (-0.9971906705787) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_52 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4675372983316):ℝ):ℂ) + (((-0.8839733449962):ℝ):ℂ) * I)‖ ≤ 0.00000016001 := by
  have hl := lg_52
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.7387081003510681 83.738708153333610486 (-2.0572991) 0.00000006 (-0.4675372983316) (-0.8839733449962) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_53 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7771920600329):ℝ):ℂ) + (((-0.6292634597531):ℝ):ℂ) * I)‖ ≤ 0.00000015603 := by
  have hl := lg_53
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.142396496364986042 84.142396549347549621 (-2.4609875) 0.00000005602 (-0.7771920600329) (-0.6292634597531) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_54 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9598125648999):ℝ):ℂ) + (((-0.2806418358473):ℝ):ℂ) * I)‖ ≤ 0.00000012587 := by
  have hl := lg_54
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.538538876800558956 84.538538919186622535 (-2.8571299) 0.00000002586 (-0.9598125648999) (-0.2806418358473) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_55 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9945541679754):ℝ):ℂ) + ((0.1042209503635:ℝ):ℂ) * I)‖ ≤ 0.00000013344 := by
  have hl := lg_55
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 84.927412167086601206 84.927412220069164785 3.0371821 0.00000003343 (-0.9945541679754) 0.1042209503635 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_56 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8840789949919):ℝ):ℂ) + ((0.4673374910215:ℝ):ℂ) * I)‖ ≤ 0.00000014632 := by
  have hl := lg_56
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.309278354204898446 85.309278407187440832 2.6553159 0.00000004631 (-0.8840789949919) 0.4673374910215 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_57 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6513881006205):ℝ):ℂ) + ((0.7587447148765:ℝ):ℂ) * I)‖ ≤ 0.00000013907 := by
  have hl := lg_57
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.684385497181497031 85.684385539567581803 2.2802088 0.00000003906 (-0.6513881006205) 0.7587447148765 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_58 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3342687785659):ℝ):ℂ) + ((0.9424777894857:ℝ):ℂ) * I)‖ ≤ 0.00000014745 := by
  have hl := lg_58
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.052968694965143556 86.052968747947707135 1.9116256 0.00000004744 (-0.3342687785659) 0.9424777894857 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_59 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0214513812699:ℝ):ℂ) + ((0.999769892646:ℝ):ℂ) * I)‖ ≤ 0.00000017363 := by
  have hl := lg_59
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.415251021148788456 86.415251074131373228 1.5493433 0.00000007362 0.0214513812699 0.999769892646 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p193_60 : ‖exp (-((((((21193:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3687336709538:ℝ):ℂ) + ((0.929535088044:ℝ):ℂ) * I)‖ ≤ 0.00000013211 := by
  have hl := lg_60
  refine (ecis_approx ((((21193:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.771444279627850989 86.771444332610393375 1.19315 0.0000000321 0.3687336709538 0.929535088044 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_2 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5489606594009):ℝ):ℂ) + (((-0.8358481886213):ℝ):ℂ) * I)‖ ≤ 0.00000012276 := by
  have hl := lg_2
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.7182872264902 14.7182872371072 (-2.1519166) 0.00000002275 (-0.5489606594009) (-0.8358481886213) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_3 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2318816126933):ℝ):ℂ) + ((0.9727440144733:ℝ):ℂ) * I)‖ ≤ 0.00000011397 := by
  have hl := lg_3
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.327933332058954376 23.32793334267597561 1.8048079 0.00000001396 (-0.2318816126933) 0.9727440144733 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_4 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3972843822707):ℝ):ℂ) + ((0.9176955484258:ℝ):ℂ) * I)‖ ≤ 0.00000013833 := by
  have hl := lg_4
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.4365744529804 29.4365744742144 1.9793521 0.00000003832 (-0.3972843822707) 0.9176955484258 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_5 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9276543317002):ℝ):ℂ) + (((-0.3734400095361):ℝ):ℂ) * I)‖ ≤ 0.00000011433 := by
  have hl := lg_5
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.174804621586313906 34.17480464282033514 (-2.7588781) 0.00000001432 (-0.9276543317002) (-0.3734400095361) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_6 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9403602055021:ℝ):ℂ) + (((-0.340180369669):ℝ):ℂ) * I)‖ ≤ 0.00000013672 := by
  have hl := lg_6
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.046220558549154376 38.04622057978317561 (-0.3471087) 0.00000003671 0.9403602055021 (-0.340180369669) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_7 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8875706918441):ℝ):ℂ) + ((0.4606715390342:ℝ):ℂ) * I)‖ ≤ 0.00000015627 := by
  have hl := lg_7
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.319456094001150748 41.319456115235193216 2.662841 0.00000005626 (-0.8875706918441) 0.4606715390342 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_8 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9851476583246:ℝ):ℂ) + (((-0.1717093221042):ℝ):ℂ) * I)‖ ≤ 0.00000016108 := by
  have hl := lg_8
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.1548616794706 44.1548617113216 (-0.1725645) 0.00000006107 0.9851476583246 (-0.1717093221042) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_9 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8924618321198):ℝ):ℂ) + (((-0.4511229079766):ℝ):ℂ) * I)‖ ≤ 0.00000013511 := by
  have hl := lg_9
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.655866664117908752 46.65586668535195122 (-2.6735695) 0.0000000351 (-0.8924618321198) (-0.4511229079766) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_10 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1971065850931:ℝ):ℂ) + ((0.980382065377:ℝ):ℂ) * I)‖ ≤ 0.00000012251 := by
  have hl := lg_10
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.893091848076513906 48.89309187992753514 1.3723906 0.0000000225 0.1971065850931 0.980382065377 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_11 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7952201148826:ℝ):ℂ) + (((-0.6063208464881):ℝ):ℂ) * I)‖ ≤ 0.00000015141 := by
  have hl := lg_11
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.916908206041529722 50.91690823789257219 (-0.6514258) 0.0000000514 0.7952201148826 (-0.6063208464881) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_12 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.800559904271):ℝ):ℂ) + (((-0.5992527343484):ℝ):ℂ) * I)‖ ≤ 0.00000015947 := by
  have hl := lg_12
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.764507785039354376 52.76450781689037561 (-2.4990253) 0.00000005946 (-0.800559904271) (-0.5992527343484) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_13 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.491435079263):ℝ):ℂ) + ((0.8709142109668:ℝ):ℂ) * I)‖ ≤ 0.00000012485 := by
  have hl := lg_13
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.4641346397792178 54.464134671630260268 2.0845331 0.00000002484 (-0.491435079263) 0.8709142109668 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_14 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8722928637762:ℝ):ℂ) + ((0.4889838032134:ℝ):ℂ) * I)‖ ≤ 0.00000014414 := by
  have hl := lg_14
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.037743320491350748 56.037743352342393216 0.5109244 0.00000004413 0.8722928637762 0.4889838032134 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_15 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5783675165896:ℝ):ℂ) + (((-0.815776327037):ℝ):ℂ) * I)‖ ≤ 0.0000001209 := by
  have hl := lg_15
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.502737953645268282 57.50273798549631075 (-0.9540702) 0.00000002089 0.5783675165896 (-0.815776327037) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_16 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6843303068871):ℝ):ℂ) + (((-0.7291721546072):ℝ):ℂ) * I)‖ ≤ 0.00000015867 := by
  have hl := lg_16
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.8731489059608 58.8731489484288 (-2.3244812) 0.00000005866 (-0.6843303068871) (-0.7291721546072) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_17 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8914814292031):ℝ):ℂ) + ((0.4530572384135:ℝ):ℂ) * I)‖ ≤ 0.0000001462 := by
  have hl := lg_17
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.160452125610959556 60.16045216807898079 2.6714009 0.00000004619 (-0.8914814292031) 0.4530572384135 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_18 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1128561774727:ℝ):ℂ) + ((0.9936113340769:ℝ):ℂ) * I)‖ ≤ 0.00000015068 := by
  have hl := lg_18
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.374153890608108752 61.37415392245915122 1.4576992 0.00000005067 0.1128561774727 0.9936113340769 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_19 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9524446090791:ℝ):ℂ) + ((0.3047117763332:ℝ):ℂ) * I)‖ ≤ 0.00000012713 := by
  have hl := lg_19
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.522217267061128102 62.522217298912191804 0.3096358 0.00000002712 0.9524446090791 0.3047117763332 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_20 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7112468125819:ℝ):ℂ) + (((-0.702942367191):ℝ):ℂ) * I)‖ ≤ 0.00000014525 := by
  have hl := lg_20
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.611379074566713906 63.61137911703473514 (-0.779526) 0.00000004524 0.7112468125819 (-0.702942367191) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_21 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2423041519122):ℝ):ℂ) + (((-0.9702003390872):ℝ):ℂ) * I)‖ ≤ 0.00000014575 := by
  have hl := lg_21
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.647389426060105124 64.647389457911168826 (-1.8155364) 0.00000004574 (-0.2423041519122) (-0.9702003390872) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_22 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9433367398338):ℝ):ℂ) + (((-0.3318370007892):ℝ):ℂ) * I)‖ ≤ 0.00000013928 := by
  have hl := lg_22
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.635195432531729722 65.63519547499977219 (-2.8033424) 0.00000003927 (-0.9433367398338) (-0.3318370007892) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_23 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8221388018193):ℝ):ℂ) + ((0.5692870896872:ℝ):ℂ) * I)‖ ≤ 0.00000012247 := by
  have hl := lg_23
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.579084158960797644 66.579084201428861346 2.5359542 0.00000002246 (-0.8221388018193) 0.5692870896872 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_24 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0614083126358):ℝ):ℂ) + ((0.9981127286729:ℝ):ℂ) * I)‖ ≤ 0.00000016746 := by
  have hl := lg_24
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.482795011529554376 67.48279505399757561 1.6322433 0.00000006745 (-0.0614083126358) 0.9981127286729 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_25 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7210851234067:ℝ):ℂ) + ((0.6928464799662:ℝ):ℂ) * I)‖ ≤ 0.00000013582 := by
  have hl := lg_25
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.349609243172627812 68.34960928564067028 0.7654291 0.00000003581 0.7210851234067 0.6928464799662 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_26 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9977305908534:ℝ):ℂ) + (((-0.0673325187068):ℝ):ℂ) * I)‖ ≤ 0.00000012978 := by
  have hl := lg_26
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.1824218662694178 69.182421908737460268 (-0.0673835) 0.00000002977 0.9977305908534 (-0.0673325187068) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_27 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6457725974896:ℝ):ℂ) + (((-0.763529797933):ℝ):ℂ) * I)‖ ≤ 0.00000014907 := by
  have hl := lg_27
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.983799996176863128 69.98380002802792683 (-0.8687616) 0.00000004906 0.6457725974896 (-0.763529797933) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_28 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0701382395063):ℝ):ℂ) + (((-0.9975372811873):ℝ):ℂ) * I)‖ ≤ 0.00000013201 := by
  have hl := lg_28
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.756030546981550748 70.756030589449593216 (-1.6409922) 0.000000032 (-0.0701382395063) (-0.9975372811873) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_29 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7279484490146):ℝ):ℂ) + (((-0.6856318659079):ℝ):ℂ) * I)‖ ≤ 0.00000014714 := by
  have hl := lg_29
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.501159631854057928 71.50115967432212163 (-2.3861213) 0.00000004713 (-0.7279484490146) (-0.6856318659079) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_30 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9993661782689):ℝ):ℂ) + (((-0.0355983304136):ℝ):ℂ) * I)‖ ≤ 0.00000014364 := by
  have hl := lg_30
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.221025180135468282 72.22102522260351075 (-3.1059868) 0.00000004363 (-0.9993661782689) (-0.0355983304136) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_31 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7895915421716):ℝ):ℂ) + ((0.6136327863515:ℝ):ℂ) * I)‖ ≤ 0.00000013429 := by
  have hl := lg_31
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.917284277958837942 72.917284320426901644 2.4809394 0.00000003428 (-0.7895915421716) 0.6136327863515 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_32 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2338068011361):ℝ):ℂ) + ((0.9722830759308:ℝ):ℂ) * I)‖ ≤ 0.00000015372 := by
  have hl := lg_32
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.591436132451 73.591436185536 1.8067875 0.00000005371 (-0.2338068011361) 0.9722830759308 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_33 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.405398051587:ℝ):ℂ) + ((0.9141402626345:ℝ):ℂ) * I)‖ ≤ 0.00000014807 := by
  have hl := lg_33
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.244841538100484098 74.2448415805685478 1.1533821 0.00000004806 0.405398051587 0.9141402626345 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_34 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8680753053566:ℝ):ℂ) + ((0.4964325374409:ℝ):ℂ) * I)‖ ≤ 0.00000013407 := by
  have hl := lg_34
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.878739352101159556 74.87873940518618079 0.5194843 0.00000003406 0.8680753053566 0.4964325374409 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_35 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9953919810401:ℝ):ℂ) + (((-0.0958895410413):ℝ):ℂ) * I)‖ ≤ 0.00000017058 := by
  have hl := lg_35
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.494260715587464654 75.494260758055528356 (-0.0960371) 0.00000007057 0.9953919810401 (-0.0958895410413) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_36 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7685545682053:ℝ):ℂ) + (((-0.6397842415148):ℝ):ℂ) * I)‖ ≤ 0.00000016907 := by
  have hl := lg_36
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.092441117098308752 76.09244115956635122 (-0.6942175) 0.00000006906 0.7685545682053 (-0.6397842415148) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_37 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2905379840401:ℝ):ℂ) + (((-0.9568634593451):ℝ):ℂ) * I)‖ ≤ 0.00000015116 := by
  have hl := lg_37
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.674230935008721428 76.67423097747678513 (-1.2760073) 0.00000005115 0.2905379840401 (-0.9568634593451) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_38 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2681618343423):ℝ):ℂ) + (((-0.963373878928):ℝ):ℂ) * I)‖ ≤ 0.00000014988 := by
  have hl := lg_38
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.240504493551328102 77.240504536019391804 (-1.8422808) 0.00000004987 (-0.2681618343423) (-0.963373878928) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_39 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7332218222411):ℝ):ℂ) + (((-0.6799895288601):ℝ):ℂ) * I)‖ ≤ 0.00000012817 := by
  have hl := lg_39
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.792067971838172176 77.792068014306235878 (-2.3938443) 0.00000002816 (-0.7332218222411) (-0.6799895288601) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_40 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9779996234308):ℝ):ℂ) + (((-0.2086066543933):ℝ):ℂ) * I)‖ ≤ 0.000000168 := by
  have hl := lg_40
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.329666301056913906 78.32966635414193514 (-2.9314426) 0.00000006799 (-0.9779996234308) (-0.2086066543933) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_41 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9510522862364):ℝ):ℂ) + ((0.3090300125203:ℝ):ℂ) * I)‖ ≤ 0.00000015655 := by
  have hl := lg_41
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((41:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.85398923680085172 78.853989289885894188 2.8274197 0.00000005654 (-0.9510522862364) 0.3090300125203 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_42 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6779247437413):ℝ):ℂ) + ((0.7351313092251:ℝ):ℂ) * I)‖ ≤ 0.0000001408 := by
  have hl := lg_42
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((42:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.365676652550305124 79.365676695018368826 2.3157323 0.00000004079 (-0.6779247437413) 0.7351313092251 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_43 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2428370463764):ℝ):ℂ) + ((0.9700670950537:ℝ):ℂ) * I)‖ ≤ 0.00000015879 := by
  have hl := lg_43
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((43:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 79.86532323455836452 79.865323277026449456 1.8160857 0.00000005878 (-0.2428370463764) 0.9700670950537 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_44 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2404894096307:ℝ):ℂ) + ((0.9706517624027:ℝ):ℂ) * I)‖ ≤ 0.00000013433 := by
  have hl := lg_44
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((44:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.353482659021929722 80.35348271210697219 1.3279263 0.00000003432 0.2404894096307 0.9706517624027 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_45 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6594287467985:ℝ):ℂ) + ((0.751767070239:ℝ):ℂ) * I)‖ ≤ 0.00000013485 := by
  have hl := lg_45
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((45:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 80.830671285704222658 80.83067132817228636 0.8507377 0.00000003484 0.6594287467985 0.751767070239 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_46 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9271594415239:ℝ):ℂ) + ((0.3746670121496:ℝ):ℂ) * I)‖ ≤ 0.00000014522 := by
  have hl := lg_46
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((46:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.297371385450997644 81.297371438536061346 0.3840376 0.00000004521 0.9271594415239 0.3746670121496 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_47 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9973639491047:ℝ):ℂ) + (((-0.0725613742039):ℝ):ℂ) * I)‖ ≤ 0.00000014624 := by
  have hl := lg_47
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((47:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 81.754034147112925986 81.754034200198010922 (-0.0726252) 0.00000004623 0.9973639491047 (-0.0725613742039) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_48 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8679814641034:ℝ):ℂ) + (((-0.4965965948061):ℝ):ℂ) * I)‖ ≤ 0.00000015533 := by
  have hl := lg_48
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((48:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.201082238019754376 82.20108229110477561 (-0.5196733) 0.00000005532 0.8679814641034 (-0.4965965948061) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_49 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5755635537913:ℝ):ℂ) + (((-0.8177570516646):ℝ):ℂ) * I)‖ ≤ 0.00000013715 := by
  have hl := lg_49
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((49:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 82.638912188002301496 82.638912230470386432 (-0.9575032) 0.00000003714 0.5755635537913 (-0.8177570516646) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_50 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1832671104459:ℝ):ℂ) + (((-0.9830631547509):ℝ):ℂ) * I)‖ ≤ 0.00000012943 := by
  have hl := lg_50
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((50:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.067896469662827812 83.06789652274787028 (-1.3864875) 0.00000002942 0.1832671104459 (-0.9830631547509) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_51 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2339905584605):ℝ):ℂ) + (((-0.9722388690802):ℝ):ℂ) * I)‖ ≤ 0.00000013568 := by
  have hl := lg_51
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((51:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.488385457669913932 83.4883855107549564 (-1.8069765) 0.00000003567 (-0.2339905584605) (-0.9722388690802) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_52 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6039946068555):ℝ):ℂ) + (((-0.7969884032262):ℝ):ℂ) * I)‖ ≤ 0.00000015253 := by
  have hl := lg_52
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((52:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 83.9007090927596178 83.900709145844660268 (-2.2193001) 0.00000005252 (-0.6039946068555) (-0.7969884032262) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_53 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8688987543955):ℝ):ℂ) + (((-0.4949898529494):ℝ):ℂ) * I)‖ ≤ 0.00000012858 := by
  have hl := lg_53
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((53:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.305178464767334196 84.305178517852397898 (-2.6237695) 0.00000002857 (-0.8688987543955) (-0.4949898529494) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_54 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9926987613715):ℝ):ℂ) + (((-0.120619935051):ℝ):ℂ) * I)‖ ≤ 0.00000017068 := by
  have hl := lg_54
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((54:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 84.702087222667063128 84.70208726513512683 (-3.0206783) 0.00000007067 (-0.9926987613715) (-0.120619935051) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_55 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9641138450109):ℝ):ℂ) + ((0.2654891591208:ℝ):ℂ) * I)‖ ≤ 0.0000001729 := by
  have hl := lg_55
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((55:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.091712827627843628 85.09171288071290733 2.8728814 0.00000007289 (-0.9641138450109) 0.2654891591208 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_56 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.795286590997):ℝ):ℂ) + ((0.606233649786:ℝ):ℂ) * I)‖ ≤ 0.00000012706 := by
  have hl := lg_56
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((56:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.474317773471750748 85.474317826556793216 2.4902765 0.00000002705 (-0.795286590997) 0.606233649786 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_57 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5172609485218):ℝ):ℂ) + ((0.8558277344929:ℝ):ℂ) * I)‖ ≤ 0.00000014109 := by
  have hl := lg_57
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((57:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 85.850150599120082478 85.850150641588167414 2.1144437 0.00000004108 (-0.5172609485218) 0.8558277344929 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_58 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1734690855428):ℝ):ℂ) + ((0.9848393149952:ℝ):ℂ) * I)‖ ≤ 0.00000014218 := by
  have hl := lg_58
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((58:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.219446858344257928 86.21944691142932163 1.7451474 0.00000004217 (-0.1734690855428) 0.9848393149952 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_59 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1875154614301:ℝ):ℂ) + ((0.982261651356:ℝ):ℂ) * I)‖ ≤ 0.00000014423 := by
  have hl := lg_59
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((59:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.582430056295634128 86.582430109380719064 1.3821642 0.00000004422 0.1875154614301 0.982261651356 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p234_60 : ‖exp (-((((((21234:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5188579222808:ℝ):ℂ) + ((0.8548604894873:ℝ):ℂ) * I)‖ ≤ 0.00000015921 := by
  have hl := lg_60
  refine (ecis_approx ((((21234:ℤ):ℝ)/1000) * Real.log ((60:ℕ):ℝ)) (14) 87.96459430051421067688 87.96459430051421067716 86.939312406625668282 86.93931245971071075 1.0252819 0.0000000592 0.5188579222808 0.8548604894873 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_2 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5724898474992):ℝ):ℂ) + (((-0.8199118089772):ℝ):ℂ) * I)‖ ≤ 0.00000015349 := by
  have hl := lg_2
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.7467062608825 14.74670627152 (-2.1803357) 0.00000005348 (-0.5724898474992) (-0.8199118089772) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_3 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1878458309976):ℝ):ℂ) + ((0.9821985256434:ℝ):ℂ) * I)‖ ≤ 0.00000011782 := by
  have hl := lg_3
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.3729764358836891 23.372976446521210375 1.7597648 0.00000001781 (-0.1878458309976) 0.9821985256434 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_4 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3445108361577):ℝ):ℂ) + ((0.9387823409969:ℝ):ℂ) * I)‖ ≤ 0.00000011415 := by
  have hl := lg_4
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.493412521765 29.49341254304 1.922514 0.00000001414 (-0.3445108361577) 0.9387823409969 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_5 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9502597357528):ℝ):ℂ) + (((-0.3114585596879):ℝ):ℂ) * I)‖ ≤ 0.00000015994 := by
  have hl := lg_5
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.240791575974796475 34.24079159724981775 (-2.8248651) 0.00000005993 (-0.9502597357528) (-0.3114585596879) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_6 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9128560010822:ℝ):ℂ) + (((-0.4082816690572):ℝ):ℂ) * I)‖ ≤ 0.00000014633 := by
  have hl := lg_6
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.1196826967661891 38.119682718041210375 (-0.4205709) 0.00000004632 0.9128560010822 (-0.4082816690572) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_7 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8480329438362):ℝ):ℂ) + ((0.5299435121746:ℝ):ℂ) * I)‖ ≤ 0.00000014018 := by
  have hl := lg_7
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.39923841009110305 41.3992384313661456 2.5830587 0.00000004017 (-0.8480329438362) 0.5299435121746 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_8 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9669477090004:ℝ):ℂ) + (((-0.2549747596506):ℝ):ℂ) * I)‖ ≤ 0.00000016432 := by
  have hl := lg_8
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.2401187826475 44.24011881456 (-0.2578216) 0.00000006431 0.9669477090004 (-0.2549747596506) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_9 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9294278848524):ℝ):ℂ) + (((-0.3690038030972):ℝ):ℂ) * I)‖ ≤ 0.0000001428 := by
  have hl := lg_9
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.7459528717673782 46.74595289304242075 (-2.7636557) 0.00000004279 (-0.9294278848524) (-0.3690038030972) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_10 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2886454111946:ℝ):ℂ) + ((0.9574360691954:ℝ):ℂ) * I)‖ ≤ 0.00000012059 := by
  have hl := lg_10
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.987497836857296475 48.98749786876981775 1.2779846 0.00000002058 0.2886454111946 0.9574360691954 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_11 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7318664109425:ℝ):ℂ) + (((-0.6814481319471):ℝ):ℂ) * I)‖ ≤ 0.00000014526 := by
  have hl := lg_11
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.015221912194289575 51.015221944106832125 (-0.7497395) 0.00000004525 0.7318664109425 (-0.6814481319471) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_12 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8573557032078):ℝ):ℂ) + (((-0.514724390425):ℝ):ℂ) * I)‖ ≤ 0.00000013214 := by
  have hl := lg_12
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.8663889576486891 52.866388989561210375 (-2.6009065) 0.00000003213 (-0.8573557032078) (-0.514724390425) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_13 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.397300992495):ℝ):ℂ) + ((0.9176883574282:ℝ):ℂ) * I)‖ ≤ 0.00000013071 := by
  have hl := lg_13
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.5692975634031675 54.56929759531571005 1.9793702 0.0000000307 (-0.397300992495) 0.9176883574282 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_14 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.919997155268:ℝ):ℂ) + ((0.3919250365808:ℝ):ℂ) * I)‖ ≤ 0.00000013828 := by
  have hl := lg_14
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.14594467097360305 56.1459447028861456 0.4027231 0.00000003827 0.919997155268 0.3919250365808 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_15 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4844164679681:ℝ):ℂ) + (((-0.8748375195208):ℝ):ℂ) * I)‖ ≤ 0.00000015277 := by
  have hl := lg_15
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.613768011858485575 57.613768043771028125 (-1.0651003) 0.00000005276 0.4844164679681 (-0.8748375195208) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_16 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7626245628894):ℝ):ℂ) + (((-0.6468413839888):ℝ):ℂ) * I)‖ ≤ 0.00000012148 := by
  have hl := lg_16
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.98682504353 58.98682508608 (-2.4381573) 0.00000002147 (-0.7626245628894) (-0.6468413839888) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_17 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8329639462521):ℝ):ℂ) + ((0.5533272667962:ℝ):ℂ) * I)‖ ≤ 0.00000014344 := by
  have hl := lg_17
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.27661387267463335 60.276613915224654625 2.5552392 0.00000004343 (-0.8329639462521) 0.5533272667962 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_18 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2295374592911:ℝ):ℂ) + ((0.9732998277931:ℝ):ℂ) * I)‖ ≤ 0.00000013916 := by
  have hl := lg_18
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.4926591326498782 61.49265916456242075 1.3391939 0.00000003915 0.2295374592911 0.9732998277931 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_19 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9822087943095:ℝ):ℂ) + ((0.1877921307753:ℝ):ℂ) * I)‖ ≤ 0.00000012531 := by
  have hl := lg_19
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.642939265174978825 62.64293929708754265 0.1889138 0.0000000253 0.9822087943095 0.1877921307753 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_20 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6197666505218:ℝ):ℂ) + (((-0.784786148515):ℝ):ℂ) * I)‖ ≤ 0.00000016851 := by
  have hl := lg_20
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.734204097739796475 63.73420414028981775 (-0.902351) 0.0000000685 0.6197666505218 (-0.784786148515) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_21 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3612102766256):ℝ):ℂ) + (((-0.9324843891763):ℝ):ℂ) * I)‖ ≤ 0.00000012584 := by
  have hl := lg_21
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.77221484597479215 64.772214877887355975 (-1.9403618) 0.00000002583 (-0.3612102766256) (-0.9324843891763) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_22 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9777134394634):ℝ):ℂ) + (((-0.2099438734093):ℝ):ℂ) * I)‖ ≤ 0.00000014385 := by
  have hl := lg_22
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.761928173076789575 65.761928215626832125 (-2.9300751) 0.00000004384 (-0.9777134394634) (-0.2099438734093) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_23 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7423711707182):ℝ):ℂ) + ((0.6699888393507:ℝ):ℂ) * I)‖ ≤ 0.00000015722 := by
  have hl := lg_23
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.70763942177126165 66.707639464321325475 2.4073989 0.00000005721 (-0.7423711707182) 0.6699888393507 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_24 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0687988368399:ℝ):ℂ) + ((0.9976305528849:ℝ):ℂ) * I)‖ ≤ 0.00000016046 := by
  have hl := lg_24
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.6130952185311891 67.613095261081210375 1.5019431 0.00000006045 0.0687988368399 0.9976305528849 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_25 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.805987076119:ℝ):ℂ) + ((0.5919331323124:ℝ):ℂ) * I)‖ ≤ 0.00000012704 := by
  have hl := lg_25
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.48158315194959295 68.4815831944996355 0.6334552 0.00000002703 0.805987076119 0.5919331323124 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_26 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9798743058279:ℝ):ℂ) + (((-0.1996154923302):ℝ):ℂ) * I)‖ ≤ 0.0000001547 := by
  have hl := lg_26
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.3160038242856675 69.31600386683571005 (-0.2009655) 0.00000005469 0.9798743058279 (-0.1996154923302) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_27 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5370241448335:ℝ):ℂ) + (((-0.8435668721956):ℝ):ℂ) * I)‖ ≤ 0.0000001606 := by
  have hl := lg_27
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.1189293076510673 70.118929339563631125 (-1.0038909) 0.00000006059 0.5370241448335 (-0.8435668721956) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_28 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.205345065391):ℝ):ℂ) + (((-0.9786896362579):ℝ):ℂ) * I)‖ ≤ 0.00000014713 := by
  have hl := lg_28
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.89265093185610305 70.8926509744061456 (-1.7776126) 0.00000004712 (-0.205345065391) (-0.9786896362579) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_29 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8153793015841):ℝ):ℂ) + (((-0.5789271063723):ℝ):ℂ) * I)‖ ≤ 0.00000012443 := by
  have hl := lg_29
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.6392187608408723 71.639218803390936125 (-2.5241804) 0.00000002442 (-0.8153793015841) (-0.5789271063723) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_30 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9946131324786):ℝ):ℂ) + ((0.103656723043:ℝ):ℂ) * I)‖ ≤ 0.00000012915 := by
  have hl := lg_30
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.360474272740985575 72.360474315291028125 3.0377494 0.00000002914 (-0.9946131324786) 0.103656723043 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_31 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6956681430696):ℝ):ℂ) + ((0.7183633027202:ℝ):ℂ) * I)‖ ≤ 0.00000013287 := by
  have hl := lg_31
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.058077753300097825 73.05807779585016165 2.3401459 0.00000003286 (-0.6956681430696) 0.7183633027202 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_32 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0937581619882):ℝ):ℂ) + ((0.9955950015243:ℝ):ℂ) * I)‖ ≤ 0.00000017146 := by
  have hl := lg_32
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.7335313044125 73.7335313576 1.6646924 0.00000007145 (-0.0937581619882) 0.9955950015243 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_33 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5318392963585:ℝ):ℂ) + ((0.8468453004232:ℝ):ℂ) * I)‖ ≤ 0.00000013809 := by
  have hl := lg_33
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.388198348077978675 74.3881983906280425 1.0100253 0.00000003808 0.5318392963585 0.8468453004232 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_34 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9305429628788:ℝ):ℂ) + ((0.3661827333953:ℝ):ℂ) * I)‖ ≤ 0.00000015261 := by
  have hl := lg_34
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.02332013355713335 75.023320186744654625 0.3749035 0.0000000526 0.9305429628788 0.3661827333953 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_35 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9709070282301:ℝ):ℂ) + (((-0.2394567654786):ℝ):ℂ) * I)‖ ≤ 0.00000014248 := by
  have hl := lg_35
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.640029986065899525 75.64003002861596335 (-0.2418063) 0.00000004247 0.9709070282301 (-0.2394567654786) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_36 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6666122319641:ℝ):ℂ) + (((-0.7454046768003):ℝ):ℂ) * I)‖ ≤ 0.00000014994 := by
  have hl := lg_36
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.2393653935323782 76.23936543608242075 (-0.8411417) 0.00000004993 0.6666122319641 (-0.7454046768003) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_37 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1462153618463:ℝ):ℂ) + (((-0.9892527826395):ℝ):ℂ) * I)‖ ≤ 0.00000012579 := by
  have hl := lg_37
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.82227856938450355 76.822278611934567375 (-1.4240549) 0.00000002578 0.1462153618463 (-0.9892527826395) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_38 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4083315772105):ℝ):ℂ) + (((-0.9128336776485):ℝ):ℂ) * I)‖ ≤ 0.00000016011 := by
  have hl := lg_38
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.389645526057478825 77.38964556860754265 (-1.9914219) 0.0000000601 (-0.4083315772105) (-0.9128336776485) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_39 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8267208125238):ℝ):ℂ) + (((-0.5626123870652):ℝ):ℂ) * I)‖ ≤ 0.0000001557 := by
  have hl := lg_39
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.9422739992868566 77.942274041836920425 (-2.5440503) 0.00000005569 (-0.8267208125238) (-0.5626123870652) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p275_40 : ‖exp (-((((((21275:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9982655456737):ℝ):ℂ) + (((-0.0588718928385):ℝ):ℂ) * I)‖ ≤ 0.00000012755 := by
  have hl := lg_40
  refine (ecis_approx ((((21275:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.480910358622296475 78.48091041180981775 (-3.0826867) 0.00000002754 (-0.9982655456737) (-0.0588718928385) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_2 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.603323807092):ℝ):ℂ) + (((-0.797496322113):ℝ):ℂ) * I)‖ ≤ 0.00000015212 := by
  have hl := lg_2
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.784829355799 14.784829366464 (-2.2184587) 0.00000005211 (-0.603323807092) (-0.797496322113) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_3 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1281910584304):ℝ):ℂ) + ((0.9917494908181:ℝ):ℂ) * I)‖ ≤ 0.00000011699 := by
  have hl := lg_3
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.43340011174613812 23.43340012241115945 1.6993411 0.00000001698 (-0.1281910584304) 0.9917494908181 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_4 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2720006644513):ℝ):ℂ) + ((0.9622970635602:ℝ):ℂ) * I)‖ ≤ 0.00000012431 := by
  have hl := lg_4
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.569658711598 29.569658732928 1.8462678 0.0000000243 (-0.2720006644513) 0.9622970635602 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_5 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9740732418039):ℝ):ℂ) + (((-0.2262328873327):ℝ):ℂ) * I)‖ ≤ 0.00000014658 := by
  have hl := lg_5
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.32931066113007797 34.3293106824600993 (-2.9133841) 0.00000004657 (-0.9740732418039) (-0.2262328873327) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_6 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8682572887995:ℝ):ℂ) + (((-0.4961141808561):ℝ):ℂ) * I)‖ ≤ 0.00000014581 := by
  have hl := lg_6
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.21822946754513812 38.21822948887515945 (-0.5191176) 0.0000000458 0.8682572887995 (-0.4961141808561) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_7 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7865717547925):ℝ):ℂ) + ((0.6174988862485:ℝ):ℂ) * I)‖ ≤ 0.00000013935 := by
  have hl := lg_7
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.50626346826055126 41.50626348959059392 2.4760337 0.00000003934 (-0.7865717547925) 0.6174988862485 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_8 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9315328453853:ℝ):ℂ) + (((-0.3636571984279):ℝ):ℂ) * I)‖ ≤ 0.00000014915 := by
  have hl := lg_8
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.354488067397 44.354488099392 (-0.3721909) 0.00000004914 0.9315328453853 (-0.3636571984279) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_9 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9671341031519):ℝ):ℂ) + (((-0.2542668406636):ℝ):ℂ) * I)‖ ≤ 0.00000012678 := by
  have hl := lg_9
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.86680022349227624 46.8668002448223189 (-2.8845031) 0.00000002677 (-0.9671341031519) (-0.2542668406636) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_10 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4072617788839:ℝ):ℂ) + ((0.913311471219:ℝ):ℂ) * I)‖ ≤ 0.00000014052 := by
  have hl := lg_10
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.11414001692907797 49.1141400489240993 1.1513424 0.00000004051 0.4072617788839 0.913311471219 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_11 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6358988561378:ℝ):ℂ) + (((-0.7717724047688):ℝ):ℂ) * I)‖ ≤ 0.00000012673 := by
  have hl := lg_11
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.14710615215530889 51.14710618415035155 (-0.8816237) 0.00000002672 0.6358988561378 (-0.7717724047688) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_12 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9194895668656):ℝ):ℂ) + (((-0.3931144060998):ℝ):ℂ) * I)‖ ≤ 0.00000013411 := by
  have hl := lg_12
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.00305882334413812 53.00305885533915945 (-2.7375764) 0.0000000341 (-0.9194895668656) (-0.3931144060998) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_13 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2643227921193):ℝ):ℂ) + ((0.9644342702149:ℝ):ℂ) * I)‖ ≤ 0.00000014541 := by
  have hl := lg_13
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.710369778020661 54.71036981001570366 1.838298 0.0000000454 (-0.2643227921193) 0.9644342702149 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_14 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9670105818483:ℝ):ℂ) + ((0.2547362058942:ℝ):ℂ) * I)‖ ≤ 0.00000014057 := by
  have hl := lg_14
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.29109282405955126 56.29109285605459392 0.2575749 0.00000004056 0.9670105818483 0.2547362058942 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_15 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3492338308333:ℝ):ℂ) + (((-0.9370356083957):ℝ):ℂ) * I)‖ ≤ 0.00000014027 := by
  have hl := lg_15
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.76271077287621609 57.76271080487125875 (-1.214043) 0.00000004026 0.3492338308333 (-0.9370356083957) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_16 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8520312732991):ℝ):ℂ) + (((-0.5234908874519):ℝ):ℂ) * I)‖ ≤ 0.00000014144 := by
  have hl := lg_16
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.139317423196 59.139317465856 (-2.5906497) 0.00000004143 (-0.8520312732991) (-0.5234908874519) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_17 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7369966860929):ℝ):ℂ) + ((0.6758963564462:ℝ):ℂ) * I)‖ ≤ 0.00000016527 := by
  have hl := lg_17
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.43244060654053722 60.43244064920055855 2.3994124 0.00000006526 (-0.7369966860929) 0.6758963564462 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_18 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3807181654108:ℝ):ℂ) + ((0.9246911260125:ℝ):ℂ) * I)‖ ≤ 0.00000013951 := by
  have hl := lg_18
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.65162957929127624 61.6516296112863189 1.1802235 0.0000000395 0.3807181654108 0.9246911260125 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_19 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9996363423812:ℝ):ℂ) + ((0.0269663306872:ℝ):ℂ) * I)‖ ≤ 0.00000016282 := by
  have hl := lg_19
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.80488340898624199 62.80488344098130598 0.0269696 0.00000006281 0.9996363423812 0.0269663306872 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_20 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4826518123275:ℝ):ℂ) + (((-0.8758123246775):ℝ):ℂ) * I)‖ ≤ 0.00000014361 := by
  have hl := lg_20
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.89896937272807797 63.8989694153880993 (-1.0671163) 0.0000000436 0.4826518123275 (-0.8758123246775) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_21 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5115727340941):ℝ):ℂ) + (((-0.8592399767962):ℝ):ℂ) * I)‖ ≤ 0.00000014022 := by
  have hl := lg_21
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.93966358000668938 64.93966361200175337 (-2.1078105) 0.00000004021 (-0.5115727340941) (-0.8592399767962) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_22 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9991385769931):ℝ):ℂ) + (((-0.0414982333731):ℝ):ℂ) * I)‖ ≤ 0.00000016386 := by
  have hl := lg_22
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.93193550795430889 65.93193555061435155 (-3.1000825) 0.00000006385 (-0.9991385769931) (-0.0414982333731) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_23 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6163904032486):ℝ):ℂ) + ((0.7874407093678:ℝ):ℂ) * I)‖ ≤ 0.00000016729 := by
  have hl := lg_23
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.88009160359017678 66.88009164625024077 2.2349468 0.00000006728 (-0.6163904032486) 0.7874407093678 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_24 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2412426599607:ℝ):ℂ) + ((0.9704648262637:ℝ):ℂ) * I)‖ ≤ 0.00000014284 := by
  have hl := lg_24
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.78788817914313812 67.78788822180315945 1.3271502 0.00000004283 0.2412426599607 0.9704648262637 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_25 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8976374084842:ℝ):ℂ) + ((0.4407347080611:ℝ):ℂ) * I)‖ ≤ 0.00000015673 := by
  have hl := lg_25
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.65862132226015594 68.6586213649201986 0.456417 0.00000005672 0.8976374084842 0.4407347080611 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_26 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9286049795592:ℝ):ℂ) + (((-0.3710697938904):ℝ):ℂ) * I)‖ ≤ 0.00000014517 := by
  have hl := lg_26
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.495199133819661 69.49519917647970366 (-0.3801608) 0.00000004516 0.9286049795592 (-0.3710697938904) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_27 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3761469542304:ℝ):ℂ) + (((-0.9265600190075):ℝ):ℂ) * I)‖ ≤ 0.00000014375 := by
  have hl := lg_27
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.30020033523841436 70.30020036723347835 (-1.185162) 0.00000004374 0.3761469542304 (-0.9265600190075) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_28 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3802693184285):ℝ):ℂ) + (((-0.924875800018):ℝ):ℂ) * I)‖ ≤ 0.00000014356 := by
  have hl := lg_28
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.07592217985855126 71.07592222251859392 (-1.9608838) 0.00000004355 (-0.3802693184285) (-0.924875800018) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_29 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9080418467356):ℝ):ℂ) + (((-0.4188794629137):ℝ):ℂ) * I)‖ ≤ 0.00000014756 := by
  have hl := lg_29
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.82442003143294036 71.82442007409300435 (-2.7093817) 0.00000004755 (-0.9080418467356) (-0.4188794629137) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_30 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.95798350495):ℝ):ℂ) + ((0.2868232975494:ℝ):ℂ) * I)‖ ≤ 0.00000015749 := by
  have hl := lg_30
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.54754012867521609 72.54754017133525875 2.8506835 0.00000005748 (-0.95798350495) 0.2868232975494 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_31 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5484256041696):ℝ):ℂ) + ((0.8361993522376:ℝ):ℂ) * I)‖ ≤ 0.00000013668 := by
  have hl := lg_31
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.24694704948959279 73.24694709214965678 2.1512766 0.00000003667 (-0.5484256041696) 0.8361993522376 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_32 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.096568701287:ℝ):ℂ) + ((0.9953263213297:ℝ):ℂ) * I)‖ ≤ 0.00000014618 := by
  have hl := lg_32
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.924146778995 73.92414683232 1.4740769 0.00000004617 0.096568701287 0.9953263213297 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_33 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6838883420342:ℝ):ℂ) + ((0.7295866882213:ℝ):ℂ) * I)‖ ≤ 0.00000012227 := by
  have hl := lg_33
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.58050626390144701 74.580506306561511 0.8177174 0.00000002226 0.6838883420342 0.7295866882213 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_34 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9836725048855:ℝ):ℂ) + ((0.1799677835958:ℝ):ℂ) * I)‖ ≤ 0.00000012952 := by
  have hl := lg_34
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.21726996233953722 75.21727001566455855 0.1809537 0.00000002951 0.9836725048855 0.1799677835958 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_35 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9058770129036:ℝ):ℂ) + (((-0.4235408333241):ℝ):ℂ) * I)‖ ≤ 0.00000015678 := by
  have hl := lg_35
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.83557412939062923 75.83557417205069322 (-0.4373505) 0.00000005677 0.9058770129036 (-0.4235408333241) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_36 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5077413529559:ℝ):ℂ) + (((-0.8615095579844):ℝ):ℂ) * I)‖ ≤ 0.00000015108 := by
  have hl := lg_36
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.43645893509027624 76.4364589777503189 (-1.0382353) 0.00000005107 0.5077413529559 (-0.8615095579844) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_37 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0518358316811):ℝ):ℂ) + (((-0.9986556195975):ℝ):ℂ) * I)‖ ≤ 0.00000013165 := by
  have hl := lg_37
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.02087905452274786 77.02087909718281185 (-1.6226554) 0.00000003164 (-0.0518358316811) (-0.9986556195975) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_38 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.581598854249):ℝ):ℂ) + (((-0.813475735794):ℝ):ℂ) * I)‖ ≤ 0.00000012138 := by
  have hl := lg_38
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.58971276478524199 77.58971280744530598 (-2.1914891) 0.00000002137 (-0.581598854249) (-0.813475735794) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_39 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9225933751084):ℝ):ℂ) + (((-0.3857738509269):ℝ):ℂ) * I)‖ ≤ 0.00000014629 := by
  have hl := lg_39
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.14376988976679912 78.14376993242686311 (-2.7455462) 0.00000004628 (-0.9225933751084) (-0.3857738509269) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p33_40 : ‖exp (-((((((21330:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9896524211572):ℝ):ℂ) + ((0.143485486704:ℝ):ℂ) * I)‖ ≤ 0.00000016482 := by
  have hl := lg_40
  refine (ecis_approx ((((21330:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.68379872852707797 78.6837987818520993 2.9976102 0.00000006481 (-0.9896524211572) 0.143485486704 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_2 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6332811016939):ℝ):ℂ) + (((-0.7739218605404):ℝ):ℂ) * I)‖ ≤ 0.00000014706 := by
  have hl := lg_2
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.8229524507155 14.822952461408 (-2.2565818) 0.00000004705 (-0.6332811016939) (-0.7739218605404) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_3 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0680683996749):ℝ):ℂ) + ((0.9976806568063:ℝ):ℂ) * I)‖ ≤ 0.00000014112 := by
  have hl := lg_3
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.49382378760858714 23.493823798301108525 1.6389174 0.00000004111 (-0.0680683996749) 0.9976806568063 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_4 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1979099874117):ℝ):ℂ) + ((0.9802201981605:ℝ):ℂ) * I)‖ ≤ 0.00000013448 := by
  have hl := lg_4
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.645904901431 29.645904922816 1.7700216 0.00000003447 (-0.1979099874117) 0.9802201981605 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_5 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9902592828984):ℝ):ℂ) + (((-0.1392355997007):ℝ):ℂ) * I)‖ ≤ 0.00000013179 := by
  have hl := lg_5
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.417829746285359465 34.41782976767038085 (-3.0019032) 0.00000003178 (-0.9902592828984) (-0.1392355997007) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_6 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8152333012861:ℝ):ℂ) + (((-0.5791326829615):ℝ):ℂ) * I)‖ ≤ 0.00000011665 := by
  have hl := lg_6
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.31677623832408714 38.316776259709108525 (-0.6176644) 0.00000001664 0.8152333012861 (-0.5791326829615) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_7 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7161094239837):ℝ):ℂ) + ((0.6979880320286:ℝ):ℂ) * I)‖ ≤ 0.00000012384 := by
  have hl := lg_7
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.61328852642999947 41.61328854781504224 2.3690086 0.00000002383 (-0.7161094239837) 0.6979880320286 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_8 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8839464943729:ℝ):ℂ) + (((-0.4675880613166):ℝ):ℂ) * I)‖ ≤ 0.00000013398 := by
  have hl := lg_8
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.4688573521465 44.468857384224 (-0.4865602) 0.00000003397 0.8839464943729 (-0.4675880613166) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_9 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.990733371192):ℝ):ℂ) + (((-0.135821157378):ℝ):ℂ) * I)‖ ≤ 0.00000014636 := by
  have hl := lg_9
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 46.98764757521717428 46.98764759660221705 (-3.0053504) 0.00000004635 (-0.990733371192) (-0.135821157378) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_10 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5193551068152:ℝ):ℂ) + ((0.8545585252193:ℝ):ℂ) * I)‖ ≤ 0.00000016045 := by
  have hl := lg_10
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.240782197000859465 49.24078222907838085 1.0247002 0.00000006044 0.5193551068152 0.8545585252193 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_11 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5288867688037:ℝ):ℂ) + (((-0.8486923976238):ℝ):ℂ) * I)‖ ≤ 0.00000016534 := by
  have hl := lg_11
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.278990392116328205 51.278990424193870975 (-1.013508) 0.00000006533 0.5288867688037 (-0.8486923976238) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_12 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9644752865851):ℝ):ℂ) + (((-0.2641730896924):ℝ):ℂ) * I)‖ ≤ 0.0000001637 := by
  have hl := lg_12
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.13972868903958714 53.139728721117108525 (-2.8742462) 0.00000006369 (-0.9644752865851) (-0.2641730896924) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_13 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.126092925502):ℝ):ℂ) + ((0.992018434374:ℝ):ℂ) * I)‖ ≤ 0.00000016011 := by
  have hl := lg_13
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.8514419926381545 54.85144202471569727 1.6972258 0.0000000601 (-0.126092925502) 0.992018434374 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_14 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9936867613574:ℝ):ℂ) + ((0.1121901078663:ℝ):ℂ) * I)‖ ≤ 0.00000014462 := by
  have hl := lg_14
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.43624097714549947 56.43624100922304224 0.1124268 0.00000004461 0.9936867613574 0.1121901078663 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_15 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2063180294188:ℝ):ℂ) + (((-0.9784849874866):ℝ):ℂ) * I)‖ ≤ 0.00000013074 := by
  have hl := lg_15
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 57.911653533893946605 57.911653565971489375 (-1.3629858) 0.00000003073 0.2063180294188 (-0.9784849874866) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_16 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9216632709336):ℝ):ℂ) + (((-0.3879907406969):ℝ):ℂ) * I)‖ ≤ 0.00000016177 := by
  have hl := lg_16
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.291809802862 59.291809845632 (-2.7431421) 0.00000006176 (-0.9216632709336) (-0.3879907406969) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_17 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6231699395314):ℝ):ℂ) + ((0.7820864571455:ℝ):ℂ) * I)‖ ≤ 0.0000001314 := by
  have hl := lg_17
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.58826734040644109 60.588267383176462475 2.2435857 0.00000003139 (-0.6231699395314) 0.7820864571455 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_18 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.522297849335:ℝ):ℂ) + ((0.8527631304061:ℝ):ℂ) * I)‖ ≤ 0.00000014588 := by
  have hl := lg_18
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.81060002593267428 61.81060005801021705 1.021253 0.00000004587 0.522297849335 0.8527631304061 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_19 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9909047629353:ℝ):ℂ) + (((-0.1345650429796):ℝ):ℂ) * I)‖ ≤ 0.00000011901 := by
  have hl := lg_19
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.966827552797505155 62.96682758487506931 (-0.1349745) 0.000000019 0.9909047629353 (-0.1345650429796) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_20 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3324637495707:ℝ):ℂ) + (((-0.943116034866):ℝ):ℂ) * I)‖ ≤ 0.00000012409 := by
  have hl := lg_20
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.063734647716359465 64.06373469048638085 (-1.2318816) 0.00000002408 0.3324637495707 (-0.943116034866) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_21 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6476247302972):ℝ):ℂ) + (((-0.7619594534428):ℝ):ℂ) * I)‖ ≤ 0.00000015777 := by
  have hl := lg_21
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.10711231403858661 65.107112346116150765 (-2.2752593) 0.00000005776 (-0.6476247302972) (-0.7619594534428) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_22 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9917555939137):ℝ):ℂ) + ((0.1281438313515:ℝ):ℂ) * I)‖ ≤ 0.00000013616 := by
  have hl := lg_22
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.101942842831828205 66.101942885601870975 3.0130955 0.00000003615 (-0.9917555939137) 0.1281438313515 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_23 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4721236510292):ℝ):ℂ) + ((0.881532335274:ℝ):ℂ) * I)‖ ≤ 0.00000014922 := by
  have hl := lg_23
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.05254378540909191 67.052543828179156065 2.0624946 0.00000004921 (-0.4721236510292) 0.881532335274 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_24 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.406334740859:ℝ):ℂ) + ((0.9137242901286:ℝ):ℂ) * I)‖ ≤ 0.00000013924 := by
  have hl := lg_24
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.96268113975508714 67.962681182525108525 1.1523572 0.00000003923 0.406334740859 0.9137242901286 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_25 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9612268974222:ℝ):ℂ) + ((0.2757586837656:ℝ):ℂ) * I)‖ ≤ 0.00000015638 := by
  have hl := lg_25
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.83565949257071893 68.8356595353407617 0.2793789 0.00000005637 0.9612268974222 0.2757586837656 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_26 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8475969661436:ℝ):ℂ) + (((-0.5306405402758):ℝ):ℂ) * I)‖ ≤ 0.00000013564 := by
  have hl := lg_26
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.6743944433536545 69.67439448612369727 (-0.5593561) 0.00000003563 0.8475969661436 (-0.5306405402758) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_27 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2029437767936:ℝ):ℂ) + (((-0.9791903918343):ℝ):ℂ) * I)‖ ≤ 0.00000011616 := by
  have hl := lg_27
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.48147136282576142 70.481471394903325575 (-1.366433) 0.00000001615 0.2029437767936 (-0.9791903918343) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_28 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.5424567539654):ℝ):ℂ) + (((-0.8400837280111):ℝ):ℂ) * I)‖ ≤ 0.00000015113 := by
  have hl := lg_28
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.25919342786099947 71.25919347063104224 (-2.1441551) 0.00000005112 (-0.5424567539654) (-0.8400837280111) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_29 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9696478875067):ℝ):ℂ) + (((-0.2445055704556):ℝ):ℂ) * I)‖ ≤ 0.00000016583 := by
  have hl := lg_29
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 72.00962130202500842 72.009621344795072575 (-2.8945829) 0.00000006582 (-0.9696478875067) (-0.2445055704556) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_30 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8879282276732):ℝ):ℂ) + ((0.4599820239939:ℝ):ℂ) * I)‖ ≤ 0.00000014124 := by
  have hl := lg_30
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.734605984609446605 72.734606027379489375 2.6636177 0.00000004123 (-0.8879282276732) 0.4599820239939 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_31 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3816779248524):ℝ):ℂ) + ((0.9242953865932:ℝ):ℂ) * I)‖ ≤ 0.00000014049 := by
  have hl := lg_31
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.435816345679087755 73.43581638844915191 1.9624073 0.00000004048 (-0.3816779248524) 0.9242953865932 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_32 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2833974225476:ℝ):ℂ) + ((0.9590025552069:ℝ):ℂ) * I)‖ ≤ 0.00000013259 := by
  have hl := lg_32
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.1147622535775 74.11476230704 1.2834614 0.00000003258 0.2833974225476 0.9590025552069 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_33 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8107234541833:ℝ):ℂ) + ((0.5854293132711:ℝ):ℂ) * I)‖ ≤ 0.00000013635 := by
  have hl := lg_33
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.772814179724915345 74.7728142224949795 0.6254095 0.00000003634 0.8107234541833 0.5854293132711 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_34 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.999915551881:ℝ):ℂ) + (((-0.0129957341659):ℝ):ℂ) * I)‖ ≤ 0.00000015844 := by
  have hl := lg_34
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.41121979112194109 75.411219844584462475 (-0.0129961) 0.00000005843 0.999915551881 (-0.0129957341659) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_35 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8063187871659:ℝ):ℂ) + (((-0.5914812029671):ℝ):ℂ) * I)‖ ≤ 0.00000012935 := by
  have hl := lg_35
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((35:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.031118272715358935 76.03111831548542309 (-0.6328946) 0.00000002934 0.8063187871659 (-0.5914812029671) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_36 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3292106710515:ℝ):ℂ) + (((-0.9442564980268):ℝ):ℂ) * I)‖ ≤ 0.00000013328 := by
  have hl := lg_36
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((36:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 76.63355247664817428 76.63355251941821705 (-1.2353288) 0.00000003327 0.3292106710515 (-0.9442564980268) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_37 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2478492192993):ℝ):ℂ) + (((-0.9687986191627):ℝ):ℂ) * I)‖ ≤ 0.00000014651 := by
  have hl := lg_37
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((37:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.21947953966099217 77.219479582431056325 (-1.8212559) 0.0000000465 (-0.2478492192993) (-0.9687986191627) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_38 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7316640883698):ℝ):ℂ) + (((-0.6816653590731):ℝ):ℂ) * I)‖ ≤ 0.00000016014 := by
  have hl := lg_38
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((38:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 77.789780003513005155 77.78978004628306931 (-2.3915563) 0.00000006013 (-0.7316640883698) (-0.6816653590731) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_39 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9811346579966):ℝ):ℂ) + (((-0.1933255868896):ℝ):ℂ) * I)‖ ≤ 0.00000013688 := by
  have hl := lg_39
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((39:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 78.34526578024674164 78.345265823016805795 (-2.9470421) 0.00000003687 (-0.9811346579966) (-0.1933255868896) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p385_40 : ‖exp (-((((((21385:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9404411235164):ℝ):ℂ) + ((0.3399566046112:ℝ):ℂ) * I)‖ ≤ 0.00000015857 := by
  have hl := lg_40
  refine (ecis_approx ((((21385:ℤ):ℝ)/1000) * Real.log ((40:ℕ):ℝ)) (13) 81.68140899333462419996 81.68140899333462420022 78.886687098431859465 78.88668715189438085 2.7947219 0.00000005856 (-0.9404411235164) 0.3399566046112 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_2 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6721275073408):ℝ):ℂ) + (((-0.7404354218001):ℝ):ℂ) * I)‖ ≤ 0.00000013844 := by
  have hl := lg_2
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 14.8742453420577 14.8742453527872 (-2.3078747) 0.00000003843 (-0.6721275073408) (-0.7404354218001) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_3 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0131758455376:ℝ):ℂ) + ((0.9999131947795:ℝ):ℂ) * I)‖ ≤ 0.00000013178 := by
  have hl := lg_3
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 23.575121096950791276 23.575121107680312735 1.5576201 0.00000003177 0.0131758455376 0.9999131947795 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_4 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0964891210661):ℝ):ℂ) + ((0.9953340391625:ℝ):ℂ) * I)‖ ≤ 0.0000001518 := by
  have hl := lg_4
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 29.7484906841154 29.7484907055744 1.6674358 0.00000005179 (-0.0964891210661) 0.9953340391625 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_5 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9997880114331):ℝ):ℂ) + (((-0.0205895982622):ℝ):ℂ) * I)‖ ≤ 0.00000013734 := by
  have hl := lg_5
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((5:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 34.536928151767010931 34.53692817322603239 (-3.1210016) 0.00000003733 (-0.9997880114331) (-0.0205895982622) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_6 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7315152999329:ℝ):ℂ) + (((-0.681825025915):ℝ):ℂ) * I)‖ ≤ 0.0000001174 := by
  have hl := lg_6
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.449366439008491276 38.449366460467512735 (-0.7502546) 0.00000001739 0.7315152999329 (-0.681825025915) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_7 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6085364918168):ℝ):ℂ) + ((0.793525890009:ℝ):ℂ) * I)‖ ≤ 0.00000014864 := by
  have hl := lg_7
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 41.757285877421620698 41.757285898880663616 2.2250113 0.00000004863 (-0.6085364918168) 0.793525890009 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_8 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8018335715584:ℝ):ℂ) + (((-0.5975474236594):ℝ):ℂ) * I)‖ ≤ 0.0000001241 := by
  have hl := lg_8
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 44.6227360261731 44.6227360583616 (-0.6404389) 0.00000002409 0.8018335715584 (-0.5975474236594) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_9 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9996527965186):ℝ):ℂ) + ((0.026349303364:ℝ):ℂ) * I)‖ ≤ 0.00000015794 := by
  have hl := lg_9
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 47.150242193901582552 47.15024221536062547 3.1152403 0.00000005793 (-0.9996527965186) 0.026349303364 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_10 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6567398369462:ℝ):ℂ) + ((0.7541172233598:ℝ):ℂ) * I)‖ ≤ 0.00000016363 := by
  have hl := lg_10
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 49.411173493824710931 49.41117352601323239 0.8543089 0.00000006362 0.6567398369462 0.7541172233598 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_11 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3707757109743:ℝ):ℂ) + (((-0.928722440857):ℝ):ℂ) * I)‖ ≤ 0.00000011701 := by
  have hl := lg_11
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 51.456434642245699647 51.456434674434242565 (-1.1909522) 0.000000017 0.3707757109743 (-0.928722440857) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_12 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9965189555579):ℝ):ℂ) + (((-0.0833664843188):ℝ):ℂ) * I)‖ ≤ 0.00000015583 := by
  have hl := lg_12
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((12:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 53.323611781066191276 53.323611813254712735 (-3.0581293) 0.00000005582 (-0.9965189555579) (-0.0833664843188) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_13 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.06333440852:ℝ):ℂ) + ((0.9979923610416:ℝ):ℂ) * I)‖ ≤ 0.0000001196 := by
  have hl := lg_13
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 55.0412482450326003 55.041248277221143218 1.5074195 0.00000001959 0.06333440852 0.9979923610416 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_14 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9965687841883:ℝ):ℂ) + (((-0.0827687041191):ℝ):ℂ) * I)‖ ≤ 0.00000014515 := by
  have hl := lg_14
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.631531219479320698 56.631531251667863616 (-0.0828635) 0.00000004514 0.9965687841883 (-0.0827687041191) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_15 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0074147588509:ℝ):ℂ) + (((-0.9999725102977):ℝ):ℂ) * I)‖ ≤ 0.00000011631 := by
  have hl := lg_15
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.112049248717802207 58.112049280906345125 (-1.5633815) 0.0000000163 0.0074147588509 (-0.9999725102977) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_16 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9813796783073):ℝ):ℂ) + (((-0.1920779182313):ℝ):ℂ) * I)‖ ≤ 0.00000014655 := by
  have hl := lg_16
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((16:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.4969813682308 59.4969814111488 (-2.9483136) 0.00000004654 (-0.9813796783073) (-0.1920779182313) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_17 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4467519795283):ℝ):ℂ) + ((0.894657850121:ℝ):ℂ) * I)‖ ≤ 0.00000014402 := by
  have hl := lg_17
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.797925127789657206 60.797925170707678665 2.0339279 0.00000004401 (-0.4467519795283) 0.894657850121 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_18 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6914041725437:ℝ):ℂ) + ((0.722468179361:ℝ):ℂ) * I)‖ ≤ 0.00000013585 := by
  have hl := lg_18
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.024487535959282552 62.02448756814782547 0.8073655 0.00000003584 0.6914041725437 0.722468179361 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_19 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9383871478578:ℝ):ℂ) + (((-0.3455858225321):ℝ):ℂ) * I)‖ ≤ 0.00000013461 := by
  have hl := lg_19
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.184716037198113777 63.184716069386678154 (-0.352863) 0.0000000346 0.9383871478578 (-0.3455858225321) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_20 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.116962194794:ℝ):ℂ) + (((-0.9931363677708):ℝ):ℂ) * I)‖ ≤ 0.00000013593 := by
  have hl := lg_20
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.285418835882410931 64.28541887880043239 (-1.4535658) 0.00000003592 0.116962194794 (-0.9931363677708) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_21 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8014749863428):ℝ):ℂ) + (((-0.5980282988429):ℝ):ℂ) * I)‖ ≤ 0.00000013478 := by
  have hl := lg_21
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((21:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.332406974372411974 65.332407006560976351 (-2.5005539) 0.00000003477 (-0.8014749863428) (-0.5980282988429) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_22 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9368675440732):ℝ):ℂ) + ((0.3496844358697:ℝ):ℂ) * I)‖ ≤ 0.00000014826 := by
  have hl := lg_22
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((22:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 66.330679984303399647 66.330680027221442565 2.7843584 0.00000004825 (-0.9368675440732) 0.3496844358697 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_23 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2567632463174):ℝ):ℂ) + ((0.9664743324782:ℝ):ℂ) * I)‖ ≤ 0.00000012168 := by
  have hl := lg_23
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((23:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.284570357310904994 67.284570400228969371 1.830468 0.00000002167 (-0.2567632463174) 0.9664743324782 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_24 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6080603887093:ℝ):ℂ) + ((0.7938907756629:ℝ):ℂ) * I)‖ ≤ 0.00000015587 := by
  have hl := lg_24
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((24:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 68.197857123123891276 68.197857166041912735 0.9171812 0.00000005586 0.6080603887093 0.7938907756629 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_25 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9991521371588:ℝ):ℂ) + ((0.0411704604179:ℝ):ℂ) * I)‖ ≤ 0.00000016749 := by
  have hl := lg_25
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((25:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.073856303534021862 69.07385634645206478 0.0411821 0.00000006748 0.9991521371588 0.0411704604179 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_26 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6963800966846:ℝ):ℂ) + (((-0.7176731574621):ℝ):ℂ) * I)‖ ≤ 0.00000015105 := by
  have hl := lg_26
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((26:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.9154935870903003 69.915493630008343218 (-0.8004552) 0.00000005104 0.6963800966846 (-0.7176731574621) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_27 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0395182800567):ℝ):ℂ) + (((-0.9992188476711):ℝ):ℂ) * I)‖ ≤ 0.00000014408 := by
  have hl := lg_27
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((27:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 70.725363290852373828 70.725363323040938205 (-1.6103249) 0.00000004407 (-0.0395182800567) (-0.9992188476711) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_28 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.731106173155):ℝ):ℂ) + (((-0.682263705282):ℝ):ℂ) * I)‖ ≤ 0.00000012549 := by
  have hl := lg_28
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((28:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.505776561537020698 71.505776604455063616 (-2.3907382) 0.00000002548 (-0.731106173155) (-0.682263705282) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_29 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9999976448772):ℝ):ℂ) + ((0.0021701515837:ℝ):ℂ) * I)‖ ≤ 0.00000015015 := by
  have hl := lg_29
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((29:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.258801193367063628 72.258801236285128005 3.1394225 0.00000005014 (-0.9999976448772) 0.0021701515837 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_30 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7453987260546):ℝ):ℂ) + ((0.6666188859937:ℝ):ℂ) * I)‖ ≤ 0.00000014755 := by
  have hl := lg_30
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((30:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 72.986294590775502207 72.986294633693545125 2.4119291 0.00000004754 (-0.7453987260546) 0.6666188859937 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_31 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1370631523703):ℝ):ℂ) + ((0.9905623111454:ℝ):ℂ) * I)‖ ≤ 0.00000015551 := by
  have hl := lg_31
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((31:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.689931398734044617 73.689931441652108994 1.7082923 0.0000000555 (-0.1370631523703) 0.9905623111454 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_32 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5173910742212:ℝ):ℂ) + ((0.8557490732196:ℝ):ℂ) * I)‖ ≤ 0.00000017588 := by
  have hl := lg_32
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((32:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 74.3712267102885 74.371226763936 1.0269969 0.00000007587 0.5173910742212 0.8557490732196 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_33 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9335271063978:ℝ):ℂ) + ((0.358506822279:ℝ):ℂ) * I)‖ ≤ 0.00000014697 := by
  have hl := lg_33
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((33:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.031555739196490923 75.0315557821145553 0.3666679 0.00000004696 0.9335271063978 0.358506822279 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_b1left_v21p459_34 : ‖exp (-((((((21459:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9627106570339:ℝ):ℂ) + (((-0.2705331603213):ℝ):ℂ) * I)‖ ≤ 0.00000013735 := by
  have hl := lg_34
  refine (ecis_approx ((((21459:ℤ):ℝ)/1000) * Real.log ((34:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.672170469847357206 75.672170523494878665 (-0.2739468) 0.00000003734 0.9627106570339 (-0.2705331603213) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
