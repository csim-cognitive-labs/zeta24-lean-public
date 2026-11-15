/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric

/-!
# Certificat (V2), logarithmes et puissances

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

lemma lg_1 : (0:ℝ) ≤ Real.log ((1:ℕ):ℝ) ∧ Real.log ((1:ℕ):ℝ) ≤ 0 := by simp
lemma lg_2 : (0.6931471803:ℝ) ≤ Real.log ((2:ℕ):ℝ) ∧ Real.log ((2:ℕ):ℝ) ≤ 0.6931471808 := by
  rw [Nat.cast_ofNat]; exact ⟨Real.log_two_gt_d9.le, Real.log_two_lt_d9.le⟩

lemma lg_3 : (1.098612288408164:ℝ) ≤ Real.log ((3:ℕ):ℝ) ∧ Real.log ((3:ℕ):ℝ) ≤ 1.098612288908165 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/3)) (by rw [abs_of_pos (by norm_num)]; norm_num) 33
  have e : (1:ℝ) - 1/3 = ((2:ℕ):ℝ) / ((3:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_2
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_4 : (1.3862943606:ℝ) ≤ Real.log ((4:ℕ):ℝ) ∧ Real.log ((4:ℕ):ℝ) ≤ 1.3862943616 := by
  have ha := lg_2
  have hb := lg_2
  have e : Real.log ((4:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((2:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_5 : (1.609437911914209:ℝ) ≤ Real.log ((5:ℕ):ℝ) ∧ Real.log ((5:ℕ):ℝ) ≤ 1.60943791291421 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/5)) (by rw [abs_of_pos (by norm_num)]; norm_num) 23
  have e : (1:ℝ) - 1/5 = ((4:ℕ):ℝ) / ((5:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_4
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_6 : (1.791759468708164:ℝ) ≤ Real.log ((6:ℕ):ℝ) ∧ Real.log ((6:ℕ):ℝ) ≤ 1.791759469708165 := by
  have ha := lg_2
  have hb := lg_3
  have e : Real.log ((6:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((3:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_7 : (1.945910148535422:ℝ) ≤ Real.log ((7:ℕ):ℝ) ∧ Real.log ((7:ℕ):ℝ) ≤ 1.945910149535424 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/7)) (by rw [abs_of_pos (by norm_num)]; norm_num) 19
  have e : (1:ℝ) - 1/7 = ((6:ℕ):ℝ) / ((7:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_6
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_8 : (2.0794415409:ℝ) ≤ Real.log ((8:ℕ):ℝ) ∧ Real.log ((8:ℕ):ℝ) ≤ 2.0794415424 := by
  have ha := lg_2
  have hb := lg_4
  have e : Real.log ((8:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((4:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_9 : (2.197224576816328:ℝ) ≤ Real.log ((9:ℕ):ℝ) ∧ Real.log ((9:ℕ):ℝ) ≤ 2.19722457781633 := by
  have ha := lg_3
  have hb := lg_3
  have e : Real.log ((9:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((3:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_10 : (2.302585092214209:ℝ) ≤ Real.log ((10:ℕ):ℝ) ∧ Real.log ((10:ℕ):ℝ) ≤ 2.30258509371421 := by
  have ha := lg_2
  have hb := lg_5
  have e : Real.log ((10:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((5:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_11 : (2.397895272018533:ℝ) ≤ Real.log ((11:ℕ):ℝ) ∧ Real.log ((11:ℕ):ℝ) ≤ 2.397895273518535 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/11)) (by rw [abs_of_pos (by norm_num)]; norm_num) 15
  have e : (1:ℝ) - 1/11 = ((10:ℕ):ℝ) / ((11:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_10
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_12 : (2.484906649008164:ℝ) ≤ Real.log ((12:ℕ):ℝ) ∧ Real.log ((12:ℕ):ℝ) ≤ 2.484906650508165 := by
  have ha := lg_2
  have hb := lg_6
  have e : Real.log ((12:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((6:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_13 : (2.5649493566817:ℝ) ≤ Real.log ((13:ℕ):ℝ) ∧ Real.log ((13:ℕ):ℝ) ≤ 2.564949358181702 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/13)) (by rw [abs_of_pos (by norm_num)]; norm_num) 14
  have e : (1:ℝ) - 1/13 = ((12:ℕ):ℝ) / ((13:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_12
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_14 : (2.639057328835422:ℝ) ≤ Real.log ((14:ℕ):ℝ) ∧ Real.log ((14:ℕ):ℝ) ≤ 2.639057330335424 := by
  have ha := lg_2
  have hb := lg_7
  have e : Real.log ((14:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((7:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_15 : (2.708050200322373:ℝ) ≤ Real.log ((15:ℕ):ℝ) ∧ Real.log ((15:ℕ):ℝ) ≤ 2.708050201822375 := by
  have ha := lg_3
  have hb := lg_5
  have e : Real.log ((15:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((5:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_16 : (2.7725887212:ℝ) ≤ Real.log ((16:ℕ):ℝ) ∧ Real.log ((16:ℕ):ℝ) ≤ 2.7725887232 := by
  have ha := lg_2
  have hb := lg_8
  have e : Real.log ((16:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((8:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_17 : (2.833213343016434:ℝ) ≤ Real.log ((17:ℕ):ℝ) ∧ Real.log ((17:ℕ):ℝ) ≤ 2.833213345016435 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/17)) (by rw [abs_of_pos (by norm_num)]; norm_num) 13
  have e : (1:ℝ) - 1/17 = ((16:ℕ):ℝ) / ((17:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_16
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_18 : (2.890371757116328:ℝ) ≤ Real.log ((18:ℕ):ℝ) ∧ Real.log ((18:ℕ):ℝ) ≤ 2.89037175861633 := by
  have ha := lg_2
  have hb := lg_9
  have e : Real.log ((18:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((9:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_19 : (2.944438978386603:ℝ) ≤ Real.log ((19:ℕ):ℝ) ∧ Real.log ((19:ℕ):ℝ) ≤ 2.944438979886606 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/19)) (by rw [abs_of_pos (by norm_num)]; norm_num) 12
  have e : (1:ℝ) - 1/19 = ((18:ℕ):ℝ) / ((19:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_18
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_20 : (2.995732272514209:ℝ) ≤ Real.log ((20:ℕ):ℝ) ∧ Real.log ((20:ℕ):ℝ) ≤ 2.99573227451421 := by
  have ha := lg_2
  have hb := lg_10
  have e : Real.log ((20:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((10:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_21 : (3.044522436943586:ℝ) ≤ Real.log ((21:ℕ):ℝ) ∧ Real.log ((21:ℕ):ℝ) ≤ 3.044522438443589 := by
  have ha := lg_3
  have hb := lg_7
  have e : Real.log ((21:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((7:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_22 : (3.091042452318533:ℝ) ≤ Real.log ((22:ℕ):ℝ) ∧ Real.log ((22:ℕ):ℝ) ≤ 3.091042454318535 := by
  have ha := lg_2
  have hb := lg_11
  have e : Real.log ((22:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((11:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_23 : (3.135494214889366:ℝ) ≤ Real.log ((23:ℕ):ℝ) ∧ Real.log ((23:ℕ):ℝ) ≤ 3.135494216889369 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/23)) (by rw [abs_of_pos (by norm_num)]; norm_num) 11
  have e : (1:ℝ) - 1/23 = ((22:ℕ):ℝ) / ((23:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_22
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_24 : (3.178053829308164:ℝ) ≤ Real.log ((24:ℕ):ℝ) ∧ Real.log ((24:ℕ):ℝ) ≤ 3.178053831308165 := by
  have ha := lg_2
  have hb := lg_12
  have e : Real.log ((24:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((12:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_25 : (3.218875823828418:ℝ) ≤ Real.log ((25:ℕ):ℝ) ∧ Real.log ((25:ℕ):ℝ) ≤ 3.21887582582842 := by
  have ha := lg_5
  have hb := lg_5
  have e : Real.log ((25:ℕ):ℝ) = Real.log ((5:ℕ):ℝ) + Real.log ((5:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_26 : (3.2580965369817:ℝ) ≤ Real.log ((26:ℕ):ℝ) ∧ Real.log ((26:ℕ):ℝ) ≤ 3.258096538981702 := by
  have ha := lg_2
  have hb := lg_13
  have e : Real.log ((26:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((13:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_27 : (3.295836865224492:ℝ) ≤ Real.log ((27:ℕ):ℝ) ∧ Real.log ((27:ℕ):ℝ) ≤ 3.295836866724495 := by
  have ha := lg_3
  have hb := lg_9
  have e : Real.log ((27:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((9:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_28 : (3.332204509135422:ℝ) ≤ Real.log ((28:ℕ):ℝ) ∧ Real.log ((28:ℕ):ℝ) ≤ 3.332204511135424 := by
  have ha := lg_2
  have hb := lg_14
  have e : Real.log ((28:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((14:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_29 : (3.367295828946692:ℝ) ≤ Real.log ((29:ℕ):ℝ) ∧ Real.log ((29:ℕ):ℝ) ≤ 3.367295830946695 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/29)) (by rw [abs_of_pos (by norm_num)]; norm_num) 10
  have e : (1:ℝ) - 1/29 = ((28:ℕ):ℝ) / ((29:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_28
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_30 : (3.401197380622373:ℝ) ≤ Real.log ((30:ℕ):ℝ) ∧ Real.log ((30:ℕ):ℝ) ≤ 3.401197382622375 := by
  have ha := lg_2
  have hb := lg_15
  have e : Real.log ((30:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((15:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_31 : (3.433987203445363:ℝ) ≤ Real.log ((31:ℕ):ℝ) ∧ Real.log ((31:ℕ):ℝ) ≤ 3.433987205445366 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/31)) (by rw [abs_of_pos (by norm_num)]; norm_num) 10
  have e : (1:ℝ) - 1/31 = ((30:ℕ):ℝ) / ((31:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_30
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_32 : (3.4657359015:ℝ) ≤ Real.log ((32:ℕ):ℝ) ∧ Real.log ((32:ℕ):ℝ) ≤ 3.465735904 := by
  have ha := lg_2
  have hb := lg_16
  have e : Real.log ((32:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((16:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_33 : (3.496507560426697:ℝ) ≤ Real.log ((33:ℕ):ℝ) ∧ Real.log ((33:ℕ):ℝ) ≤ 3.4965075624267 := by
  have ha := lg_3
  have hb := lg_11
  have e : Real.log ((33:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((11:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_34 : (3.526360523316434:ℝ) ≤ Real.log ((34:ℕ):ℝ) ∧ Real.log ((34:ℕ):ℝ) ≤ 3.526360525816435 := by
  have ha := lg_2
  have hb := lg_17
  have e : Real.log ((34:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((17:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_35 : (3.555348060449631:ℝ) ≤ Real.log ((35:ℕ):ℝ) ∧ Real.log ((35:ℕ):ℝ) ≤ 3.555348062449634 := by
  have ha := lg_5
  have hb := lg_7
  have e : Real.log ((35:ℕ):ℝ) = Real.log ((5:ℕ):ℝ) + Real.log ((7:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_36 : (3.583518937416328:ℝ) ≤ Real.log ((36:ℕ):ℝ) ∧ Real.log ((36:ℕ):ℝ) ≤ 3.58351893941633 := by
  have ha := lg_2
  have hb := lg_18
  have e : Real.log ((36:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((18:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_37 : (3.610917911604442:ℝ) ≤ Real.log ((37:ℕ):ℝ) ∧ Real.log ((37:ℕ):ℝ) ≤ 3.610917913604445 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/37)) (by rw [abs_of_pos (by norm_num)]; norm_num) 10
  have e : (1:ℝ) - 1/37 = ((36:ℕ):ℝ) / ((37:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_36
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_38 : (3.637586158686603:ℝ) ≤ Real.log ((38:ℕ):ℝ) ∧ Real.log ((38:ℕ):ℝ) ≤ 3.637586160686606 := by
  have ha := lg_2
  have hb := lg_19
  have e : Real.log ((38:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((19:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_39 : (3.663561645089864:ℝ) ≤ Real.log ((39:ℕ):ℝ) ∧ Real.log ((39:ℕ):ℝ) ≤ 3.663561647089867 := by
  have ha := lg_3
  have hb := lg_13
  have e : Real.log ((39:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((13:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_40 : (3.688879452814209:ℝ) ≤ Real.log ((40:ℕ):ℝ) ∧ Real.log ((40:ℕ):ℝ) ≤ 3.68887945531421 := by
  have ha := lg_2
  have hb := lg_20
  have e : Real.log ((40:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((20:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_41 : (3.71357206540458:ℝ) ≤ Real.log ((41:ℕ):ℝ) ∧ Real.log ((41:ℕ):ℝ) ≤ 3.713572067904582 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/41)) (by rw [abs_of_pos (by norm_num)]; norm_num) 9
  have e : (1:ℝ) - 1/41 = ((40:ℕ):ℝ) / ((41:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_40
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_42 : (3.737669617243586:ℝ) ≤ Real.log ((42:ℕ):ℝ) ∧ Real.log ((42:ℕ):ℝ) ≤ 3.737669619243589 := by
  have ha := lg_2
  have hb := lg_21
  have e : Real.log ((42:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((21:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_43 : (3.76120011465378:ℝ) ≤ Real.log ((43:ℕ):ℝ) ∧ Real.log ((43:ℕ):ℝ) ≤ 3.761200116653784 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/43)) (by rw [abs_of_pos (by norm_num)]; norm_num) 9
  have e : (1:ℝ) - 1/43 = ((42:ℕ):ℝ) / ((43:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_42
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_44 : (3.784189632618533:ℝ) ≤ Real.log ((44:ℕ):ℝ) ∧ Real.log ((44:ℕ):ℝ) ≤ 3.784189635118535 := by
  have ha := lg_2
  have hb := lg_22
  have e : Real.log ((44:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((22:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_45 : (3.806662488730537:ℝ) ≤ Real.log ((45:ℕ):ℝ) ∧ Real.log ((45:ℕ):ℝ) ≤ 3.80666249073054 := by
  have ha := lg_3
  have hb := lg_15
  have e : Real.log ((45:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((15:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_46 : (3.828641395189366:ℝ) ≤ Real.log ((46:ℕ):ℝ) ∧ Real.log ((46:ℕ):ℝ) ≤ 3.828641397689369 := by
  have ha := lg_2
  have hb := lg_23
  have e : Real.log ((46:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((23:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_47 : (3.850147600410329:ℝ) ≤ Real.log ((47:ℕ):ℝ) ∧ Real.log ((47:ℕ):ℝ) ≤ 3.850147602910333 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/47)) (by rw [abs_of_pos (by norm_num)]; norm_num) 9
  have e : (1:ℝ) - 1/47 = ((46:ℕ):ℝ) / ((47:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_46
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_48 : (3.871201009608164:ℝ) ≤ Real.log ((48:ℕ):ℝ) ∧ Real.log ((48:ℕ):ℝ) ≤ 3.871201012108165 := by
  have ha := lg_2
  have hb := lg_24
  have e : Real.log ((48:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((24:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_49 : (3.891820297070844:ℝ) ≤ Real.log ((49:ℕ):ℝ) ∧ Real.log ((49:ℕ):ℝ) ≤ 3.891820299070848 := by
  have ha := lg_7
  have hb := lg_7
  have e : Real.log ((49:ℕ):ℝ) = Real.log ((7:ℕ):ℝ) + Real.log ((7:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_50 : (3.912023004128418:ℝ) ≤ Real.log ((50:ℕ):ℝ) ∧ Real.log ((50:ℕ):ℝ) ≤ 3.91202300662842 := by
  have ha := lg_2
  have hb := lg_25
  have e : Real.log ((50:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((25:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_51 : (3.931825631424598:ℝ) ≤ Real.log ((51:ℕ):ℝ) ∧ Real.log ((51:ℕ):ℝ) ≤ 3.9318256339246 := by
  have ha := lg_3
  have hb := lg_17
  have e : Real.log ((51:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((17:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_52 : (3.9512437172817:ℝ) ≤ Real.log ((52:ℕ):ℝ) ∧ Real.log ((52:ℕ):ℝ) ≤ 3.951243719781702 := by
  have ha := lg_2
  have hb := lg_26
  have e : Real.log ((52:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((26:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_53 : (3.970291912252394:ℝ) ≤ Real.log ((53:ℕ):ℝ) ∧ Real.log ((53:ℕ):ℝ) ≤ 3.970291914752397 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/53)) (by rw [abs_of_pos (by norm_num)]; norm_num) 9
  have e : (1:ℝ) - 1/53 = ((52:ℕ):ℝ) / ((53:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_52
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_54 : (3.988984045524492:ℝ) ≤ Real.log ((54:ℕ):ℝ) ∧ Real.log ((54:ℕ):ℝ) ≤ 3.988984047524495 := by
  have ha := lg_2
  have hb := lg_27
  have e : Real.log ((54:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((27:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_55 : (4.007333183932742:ℝ) ≤ Real.log ((55:ℕ):ℝ) ∧ Real.log ((55:ℕ):ℝ) ≤ 4.007333186432745 := by
  have ha := lg_5
  have hb := lg_11
  have e : Real.log ((55:ℕ):ℝ) = Real.log ((5:ℕ):ℝ) + Real.log ((11:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_56 : (4.025351689435422:ℝ) ≤ Real.log ((56:ℕ):ℝ) ∧ Real.log ((56:ℕ):ℝ) ≤ 4.025351691935424 := by
  have ha := lg_2
  have hb := lg_28
  have e : Real.log ((56:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((28:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_57 : (4.043051266794767:ℝ) ≤ Real.log ((57:ℕ):ℝ) ∧ Real.log ((57:ℕ):ℝ) ≤ 4.043051268794771 := by
  have ha := lg_3
  have hb := lg_19
  have e : Real.log ((57:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((19:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_58 : (4.060443009246692:ℝ) ≤ Real.log ((58:ℕ):ℝ) ∧ Real.log ((58:ℕ):ℝ) ≤ 4.060443011746695 := by
  have ha := lg_2
  have hb := lg_29
  have e : Real.log ((58:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((29:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_59 : (4.077537442605992:ℝ) ≤ Real.log ((59:ℕ):ℝ) ∧ Real.log ((59:ℕ):ℝ) ≤ 4.077537445105996 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/59)) (by rw [abs_of_pos (by norm_num)]; norm_num) 9
  have e : (1:ℝ) - 1/59 = ((58:ℕ):ℝ) / ((59:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_58
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_60 : (4.094344560922373:ℝ) ≤ Real.log ((60:ℕ):ℝ) ∧ Real.log ((60:ℕ):ℝ) ≤ 4.094344563422375 := by
  have ha := lg_2
  have hb := lg_30
  have e : Real.log ((60:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((30:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_61 : (4.110873862873583:ℝ) ≤ Real.log ((61:ℕ):ℝ) ∧ Real.log ((61:ℕ):ℝ) ≤ 4.110873865373586 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/61)) (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  have e : (1:ℝ) - 1/61 = ((60:ℕ):ℝ) / ((61:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_60
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_62 : (4.127134383745363:ℝ) ≤ Real.log ((62:ℕ):ℝ) ∧ Real.log ((62:ℕ):ℝ) ≤ 4.127134386245366 := by
  have ha := lg_2
  have hb := lg_31
  have e : Real.log ((62:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((31:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_63 : (4.14313472535175:ℝ) ≤ Real.log ((63:ℕ):ℝ) ∧ Real.log ((63:ℕ):ℝ) ≤ 4.143134727351754 := by
  have ha := lg_3
  have hb := lg_21
  have e : Real.log ((63:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((21:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_64 : (4.1588830818:ℝ) ≤ Real.log ((64:ℕ):ℝ) ∧ Real.log ((64:ℕ):ℝ) ≤ 4.1588830848 := by
  have ha := lg_2
  have hb := lg_32
  have e : Real.log ((64:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((32:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_65 : (4.174387268595909:ℝ) ≤ Real.log ((65:ℕ):ℝ) ∧ Real.log ((65:ℕ):ℝ) ≤ 4.174387271095912 := by
  have ha := lg_5
  have hb := lg_13
  have e : Real.log ((65:ℕ):ℝ) = Real.log ((5:ℕ):ℝ) + Real.log ((13:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_66 : (4.189654740726697:ℝ) ≤ Real.log ((66:ℕ):ℝ) ∧ Real.log ((66:ℕ):ℝ) ≤ 4.1896547432267 := by
  have ha := lg_2
  have hb := lg_33
  have e : Real.log ((66:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((33:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_67 : (4.204692618091237:ℝ) ≤ Real.log ((67:ℕ):ℝ) ∧ Real.log ((67:ℕ):ℝ) ≤ 4.204692620591241 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/67)) (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  have e : (1:ℝ) - 1/67 = ((66:ℕ):ℝ) / ((67:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_66
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_68 : (4.219507703616434:ℝ) ≤ Real.log ((68:ℕ):ℝ) ∧ Real.log ((68:ℕ):ℝ) ≤ 4.219507706616435 := by
  have ha := lg_2
  have hb := lg_34
  have e : Real.log ((68:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((34:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_69 : (4.23410650329753:ℝ) ≤ Real.log ((69:ℕ):ℝ) ∧ Real.log ((69:ℕ):ℝ) ≤ 4.234106505797534 := by
  have ha := lg_3
  have hb := lg_23
  have e : Real.log ((69:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((23:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_70 : (4.248495240749631:ℝ) ≤ Real.log ((70:ℕ):ℝ) ∧ Real.log ((70:ℕ):ℝ) ≤ 4.248495243249634 := by
  have ha := lg_2
  have hb := lg_35
  have e : Real.log ((70:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((35:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_71 : (4.262679875741587:ℝ) ≤ Real.log ((71:ℕ):ℝ) ∧ Real.log ((71:ℕ):ℝ) ≤ 4.262679878241591 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/71)) (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  have e : (1:ℝ) - 1/71 = ((70:ℕ):ℝ) / ((71:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_70
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_72 : (4.276666117716328:ℝ) ≤ Real.log ((72:ℕ):ℝ) ∧ Real.log ((72:ℕ):ℝ) ≤ 4.27666612021633 := by
  have ha := lg_2
  have hb := lg_36
  have e : Real.log ((72:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((36:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_73 : (4.290459439848663:ℝ) ≤ Real.log ((73:ℕ):ℝ) ∧ Real.log ((73:ℕ):ℝ) ≤ 4.290459442348666 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/73)) (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  have e : (1:ℝ) - 1/73 = ((72:ℕ):ℝ) / ((73:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_72
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_74 : (4.304065091904442:ℝ) ≤ Real.log ((74:ℕ):ℝ) ∧ Real.log ((74:ℕ):ℝ) ≤ 4.304065094404445 := by
  have ha := lg_2
  have hb := lg_37
  have e : Real.log ((74:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((37:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_75 : (4.317488112236582:ℝ) ≤ Real.log ((75:ℕ):ℝ) ∧ Real.log ((75:ℕ):ℝ) ≤ 4.317488114736585 := by
  have ha := lg_3
  have hb := lg_25
  have e : Real.log ((75:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((25:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_76 : (4.330733338986603:ℝ) ≤ Real.log ((76:ℕ):ℝ) ∧ Real.log ((76:ℕ):ℝ) ≤ 4.330733341486606 := by
  have ha := lg_2
  have hb := lg_38
  have e : Real.log ((76:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((38:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_77 : (4.343805420553955:ℝ) ≤ Real.log ((77:ℕ):ℝ) ∧ Real.log ((77:ℕ):ℝ) ≤ 4.343805423053959 := by
  have ha := lg_7
  have hb := lg_11
  have e : Real.log ((77:ℕ):ℝ) = Real.log ((7:ℕ):ℝ) + Real.log ((11:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_78 : (4.356708825389864:ℝ) ≤ Real.log ((78:ℕ):ℝ) ∧ Real.log ((78:ℕ):ℝ) ≤ 4.356708827889867 := by
  have ha := lg_2
  have hb := lg_39
  have e : Real.log ((78:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((39:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_79 : (4.369447851167293:ℝ) ≤ Real.log ((79:ℕ):ℝ) ∧ Real.log ((79:ℕ):ℝ) ≤ 4.369447853667297 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/79)) (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  have e : (1:ℝ) - 1/79 = ((78:ℕ):ℝ) / ((79:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_78
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_80 : (4.382026633114209:ℝ) ≤ Real.log ((80:ℕ):ℝ) ∧ Real.log ((80:ℕ):ℝ) ≤ 4.38202663611421 := by
  have ha := lg_2
  have hb := lg_40
  have e : Real.log ((80:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((40:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_81 : (4.394449153632656:ℝ) ≤ Real.log ((81:ℕ):ℝ) ∧ Real.log ((81:ℕ):ℝ) ≤ 4.39444915563266 := by
  have ha := lg_3
  have hb := lg_27
  have e : Real.log ((81:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((27:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_82 : (4.40671924570458:ℝ) ≤ Real.log ((82:ℕ):ℝ) ∧ Real.log ((82:ℕ):ℝ) ≤ 4.406719248704582 := by
  have ha := lg_2
  have hb := lg_41
  have e : Real.log ((82:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((41:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_83 : (4.418840606236924:ℝ) ≤ Real.log ((83:ℕ):ℝ) ∧ Real.log ((83:ℕ):ℝ) ≤ 4.418840609236927 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/83)) (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  have e : (1:ℝ) - 1/83 = ((82:ℕ):ℝ) / ((83:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_82
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_84 : (4.430816797543586:ℝ) ≤ Real.log ((84:ℕ):ℝ) ∧ Real.log ((84:ℕ):ℝ) ≤ 4.430816800043589 := by
  have ha := lg_2
  have hb := lg_42
  have e : Real.log ((84:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((42:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_85 : (4.442651254930643:ℝ) ≤ Real.log ((85:ℕ):ℝ) ∧ Real.log ((85:ℕ):ℝ) ≤ 4.442651257930645 := by
  have ha := lg_5
  have hb := lg_17
  have e : Real.log ((85:ℕ):ℝ) = Real.log ((5:ℕ):ℝ) + Real.log ((17:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_86 : (4.45434729495378:ℝ) ≤ Real.log ((86:ℕ):ℝ) ∧ Real.log ((86:ℕ):ℝ) ≤ 4.454347297453784 := by
  have ha := lg_2
  have hb := lg_43
  have e : Real.log ((86:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((43:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_87 : (4.465908117354856:ℝ) ≤ Real.log ((87:ℕ):ℝ) ∧ Real.log ((87:ℕ):ℝ) ≤ 4.46590811985486 := by
  have ha := lg_3
  have hb := lg_29
  have e : Real.log ((87:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((29:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_88 : (4.477336812918533:ℝ) ≤ Real.log ((88:ℕ):ℝ) ∧ Real.log ((88:ℕ):ℝ) ≤ 4.477336815918535 := by
  have ha := lg_2
  have hb := lg_44
  have e : Real.log ((88:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((44:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_89 : (4.488636368172466:ℝ) ≤ Real.log ((89:ℕ):ℝ) ∧ Real.log ((89:ℕ):ℝ) ≤ 4.488636371172469 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/89)) (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  have e : (1:ℝ) - 1/89 = ((88:ℕ):ℝ) / ((89:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_88
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_90 : (4.499809669030537:ℝ) ≤ Real.log ((90:ℕ):ℝ) ∧ Real.log ((90:ℕ):ℝ) ≤ 4.49980967153054 := by
  have ha := lg_2
  have hb := lg_45
  have e : Real.log ((90:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((45:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_91 : (4.510859505217122:ℝ) ≤ Real.log ((91:ℕ):ℝ) ∧ Real.log ((91:ℕ):ℝ) ≤ 4.510859507717126 := by
  have ha := lg_7
  have hb := lg_13
  have e : Real.log ((91:ℕ):ℝ) = Real.log ((7:ℕ):ℝ) + Real.log ((13:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_92 : (4.521788575489366:ℝ) ≤ Real.log ((92:ℕ):ℝ) ∧ Real.log ((92:ℕ):ℝ) ≤ 4.521788578489369 := by
  have ha := lg_2
  have hb := lg_46
  have e : Real.log ((92:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((46:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_93 : (4.532599491853527:ℝ) ≤ Real.log ((93:ℕ):ℝ) ∧ Real.log ((93:ℕ):ℝ) ≤ 4.532599494353531 := by
  have ha := lg_3
  have hb := lg_31
  have e : Real.log ((93:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((31:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_94 : (4.543294780710329:ℝ) ≤ Real.log ((94:ℕ):ℝ) ∧ Real.log ((94:ℕ):ℝ) ≤ 4.543294783710333 := by
  have ha := lg_2
  have hb := lg_47
  have e : Real.log ((94:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((47:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_95 : (4.553876890300812:ℝ) ≤ Real.log ((95:ℕ):ℝ) ∧ Real.log ((95:ℕ):ℝ) ≤ 4.553876892800816 := by
  have ha := lg_5
  have hb := lg_19
  have e : Real.log ((95:ℕ):ℝ) = Real.log ((5:ℕ):ℝ) + Real.log ((19:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_96 : (4.564348189908164:ℝ) ≤ Real.log ((96:ℕ):ℝ) ∧ Real.log ((96:ℕ):ℝ) ≤ 4.564348192908165 := by
  have ha := lg_2
  have hb := lg_48
  have e : Real.log ((96:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((48:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_97 : (4.57471097694371:ℝ) ≤ Real.log ((97:ℕ):ℝ) ∧ Real.log ((97:ℕ):ℝ) ≤ 4.574710979943712 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/97)) (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  have e : (1:ℝ) - 1/97 = ((96:ℕ):ℝ) / ((97:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_96
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_98 : (4.584967477370844:ℝ) ≤ Real.log ((98:ℕ):ℝ) ∧ Real.log ((98:ℕ):ℝ) ≤ 4.584967479870848 := by
  have ha := lg_2
  have hb := lg_49
  have e : Real.log ((98:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((49:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_99 : (4.595119848834861:ℝ) ≤ Real.log ((99:ℕ):ℝ) ∧ Real.log ((99:ℕ):ℝ) ≤ 4.595119851334865 := by
  have ha := lg_3
  have hb := lg_33
  have e : Real.log ((99:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((33:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_100 : (4.605170184428418:ℝ) ≤ Real.log ((100:ℕ):ℝ) ∧ Real.log ((100:ℕ):ℝ) ≤ 4.60517018742842 := by
  have ha := lg_2
  have hb := lg_50
  have e : Real.log ((100:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((50:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_101 : (4.615120515281585:ℝ) ≤ Real.log ((101:ℕ):ℝ) ∧ Real.log ((101:ℕ):ℝ) ≤ 4.615120518281589 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/101)) (by rw [abs_of_pos (by norm_num)]; norm_num) 7
  have e : (1:ℝ) - 1/101 = ((100:ℕ):ℝ) / ((101:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_100
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_102 : (4.624972811724598:ℝ) ≤ Real.log ((102:ℕ):ℝ) ∧ Real.log ((102:ℕ):ℝ) ≤ 4.6249728147246 := by
  have ha := lg_2
  have hb := lg_51
  have e : Real.log ((102:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((51:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_103 : (4.634728986669962:ℝ) ≤ Real.log ((103:ℕ):ℝ) ∧ Real.log ((103:ℕ):ℝ) ≤ 4.634728989669965 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/103)) (by rw [abs_of_pos (by norm_num)]; norm_num) 7
  have e : (1:ℝ) - 1/103 = ((102:ℕ):ℝ) / ((103:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_102
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_104 : (4.6443908975817:ℝ) ≤ Real.log ((104:ℕ):ℝ) ∧ Real.log ((104:ℕ):ℝ) ≤ 4.644390900581702 := by
  have ha := lg_2
  have hb := lg_52
  have e : Real.log ((104:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((52:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_105 : (4.653960348857795:ℝ) ≤ Real.log ((105:ℕ):ℝ) ∧ Real.log ((105:ℕ):ℝ) ≤ 4.653960351357799 := by
  have ha := lg_3
  have hb := lg_35
  have e : Real.log ((105:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((35:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_106 : (4.663439092552394:ℝ) ≤ Real.log ((106:ℕ):ℝ) ∧ Real.log ((106:ℕ):ℝ) ≤ 4.663439095552397 := by
  have ha := lg_2
  have hb := lg_53
  have e : Real.log ((106:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((53:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_107 : (4.672828832902232:ℝ) ≤ Real.log ((107:ℕ):ℝ) ∧ Real.log ((107:ℕ):ℝ) ≤ 4.672828835902237 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/107)) (by rw [abs_of_pos (by norm_num)]; norm_num) 7
  have e : (1:ℝ) - 1/107 = ((106:ℕ):ℝ) / ((107:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_106
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_108 : (4.682131225824492:ℝ) ≤ Real.log ((108:ℕ):ℝ) ∧ Real.log ((108:ℕ):ℝ) ≤ 4.682131228324495 := by
  have ha := lg_2
  have hb := lg_54
  have e : Real.log ((108:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((54:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_109 : (4.691347880929415:ℝ) ≤ Real.log ((109:ℕ):ℝ) ∧ Real.log ((109:ℕ):ℝ) ≤ 4.69134788342942 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/109)) (by rw [abs_of_pos (by norm_num)]; norm_num) 7
  have e : (1:ℝ) - 1/109 = ((108:ℕ):ℝ) / ((109:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_108
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_110 : (4.700480364232742:ℝ) ≤ Real.log ((110:ℕ):ℝ) ∧ Real.log ((110:ℕ):ℝ) ≤ 4.700480367232745 := by
  have ha := lg_2
  have hb := lg_55
  have e : Real.log ((110:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((55:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_111 : (4.709530200012606:ℝ) ≤ Real.log ((111:ℕ):ℝ) ∧ Real.log ((111:ℕ):ℝ) ≤ 4.70953020251261 := by
  have ha := lg_3
  have hb := lg_37
  have e : Real.log ((111:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((37:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_112 : (4.718498869735422:ℝ) ≤ Real.log ((112:ℕ):ℝ) ∧ Real.log ((112:ℕ):ℝ) ≤ 4.718498872735424 := by
  have ha := lg_2
  have hb := lg_56
  have e : Real.log ((112:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((56:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_113 : (4.727387817152667:ℝ) ≤ Real.log ((113:ℕ):ℝ) ∧ Real.log ((113:ℕ):ℝ) ≤ 4.727387820152671 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/113)) (by rw [abs_of_pos (by norm_num)]; norm_num) 7
  have e : (1:ℝ) - 1/113 = ((112:ℕ):ℝ) / ((113:ℕ):ℝ) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have hq := lg_112
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith [hq.1, hq.2]

lemma lg_114 : (4.736198447094767:ℝ) ≤ Real.log ((114:ℕ):ℝ) ∧ Real.log ((114:ℕ):ℝ) ≤ 4.736198449594771 := by
  have ha := lg_2
  have hb := lg_57
  have e : Real.log ((114:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((57:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_115 : (4.744932126803575:ℝ) ≤ Real.log ((115:ℕ):ℝ) ∧ Real.log ((115:ℕ):ℝ) ≤ 4.744932129803579 := by
  have ha := lg_5
  have hb := lg_23
  have e : Real.log ((115:ℕ):ℝ) = Real.log ((5:ℕ):ℝ) + Real.log ((23:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_116 : (4.753590189546692:ℝ) ≤ Real.log ((116:ℕ):ℝ) ∧ Real.log ((116:ℕ):ℝ) ≤ 4.753590192546695 := by
  have ha := lg_2
  have hb := lg_58
  have e : Real.log ((116:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((58:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_117 : (4.762173933498028:ℝ) ≤ Real.log ((117:ℕ):ℝ) ∧ Real.log ((117:ℕ):ℝ) ≤ 4.762173935998032 := by
  have ha := lg_3
  have hb := lg_39
  have e : Real.log ((117:ℕ):ℝ) = Real.log ((3:ℕ):ℝ) + Real.log ((39:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_118 : (4.770684622905992:ℝ) ≤ Real.log ((118:ℕ):ℝ) ∧ Real.log ((118:ℕ):ℝ) ≤ 4.770684625905996 := by
  have ha := lg_2
  have hb := lg_59
  have e : Real.log ((118:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((59:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_119 : (4.779123491551856:ℝ) ≤ Real.log ((119:ℕ):ℝ) ∧ Real.log ((119:ℕ):ℝ) ≤ 4.779123494551859 := by
  have ha := lg_7
  have hb := lg_17
  have e : Real.log ((119:ℕ):ℝ) = Real.log ((7:ℕ):ℝ) + Real.log ((17:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma lg_120 : (4.787491741222373:ℝ) ≤ Real.log ((120:ℕ):ℝ) ∧ Real.log ((120:ℕ):ℝ) ≤ 4.787491744222375 := by
  have ha := lg_2
  have hb := lg_60
  have e : Real.log ((120:ℕ):ℝ) = Real.log ((2:ℕ):ℝ) + Real.log ((60:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma pwl_2_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.8408964152537:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.8408964152538 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.5946035575013:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.5946035575014 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_8_4 (σ : ℝ) (h : σ ≤ (8:ℕ) / (4:ℕ)) : (0.25:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_8_4 (σ : ℝ) (h : (8:ℕ) / (4:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.25 :=
  pwq_hi _ σ 4 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.8408964152537:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.8408964152538 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_11_32 (σ : ℝ) (h : σ ≤ (11:ℕ) / (32:ℕ)) : (0.7879904225539:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_11_32 (σ : ℝ) (h : (11:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.787990422554 :=
  pwq_hi _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_17_32 (σ : ℝ) (h : σ ≤ (17:ℕ) / (32:ℕ)) : (0.6919549409819:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_17_32 (σ : ℝ) (h : (17:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.691954940982 :=
  pwq_hi _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_20_32 (σ : ℝ) (h : σ ≤ (20:ℕ) / (32:ℕ)) : (0.6484197773255:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_20_32 (σ : ℝ) (h : (20:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.6484197773256 :=
  pwq_hi _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_24_32 (σ : ℝ) (h : σ ≤ (24:ℕ) / (32:ℕ)) : (0.5946035575013:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_24_32 (σ : ℝ) (h : (24:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.5946035575014 :=
  pwq_hi _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_30_32 (σ : ℝ) (h : σ ≤ (30:ℕ) / (32:ℕ)) : (0.5221368912137:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 30 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_30_32 (σ : ℝ) (h : (30:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.5221368912138 :=
  pwq_hi _ σ 32 30 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_33_32 (σ : ℝ) (h : σ ≤ (33:ℕ) / (32:ℕ)) : (0.4892860310438:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_33_32 (σ : ℝ) (h : (33:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.4892860310439 :=
  pwq_hi _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_34_32 (σ : ℝ) (h : σ ≤ (34:ℕ) / (32:ℕ)) : (0.4788016403492:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_34_32 (σ : ℝ) (h : (34:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.4788016403493 :=
  pwq_hi _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_37_32 (σ : ℝ) (h : σ ≤ (37:ℕ) / (32:ℕ)) : (0.4486772687507:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 37 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_37_32 (σ : ℝ) (h : (37:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.4486772687508 :=
  pwq_hi _ σ 32 37 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_46_32 (σ : ℝ) (h : σ ≤ (46:ℕ) / (32:ℕ)) : (0.3692065364848:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_46_32 (σ : ℝ) (h : (46:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.3692065364849 :=
  pwq_hi _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_48_32 (σ : ℝ) (h : σ ≤ (48:ℕ) / (32:ℕ)) : (0.3535533905932:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 48 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_48_32 (σ : ℝ) (h : (48:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.3535533905933 :=
  pwq_hi _ σ 32 48 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_52_32 (σ : ℝ) (h : σ ≤ (52:ℕ) / (32:ℕ)) : (0.3242098886627:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 52 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_52_32 (σ : ℝ) (h : (52:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.3242098886628 :=
  pwq_hi _ σ 32 52 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_64_32 (σ : ℝ) (h : σ ≤ (64:ℕ) / (32:ℕ)) : (0.25:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 64 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_64_32 (σ : ℝ) (h : (64:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.25 :=
  pwq_hi _ σ 32 64 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.7598356856515:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.7598356856516 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.4386913376508:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.4386913376509 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_8_4 (σ : ℝ) (h : σ ≤ (8:ℕ) / (4:ℕ)) : (0.1111111111111:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_8_4 (σ : ℝ) (h : (8:ℕ) / (4:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.1111111111112 :=
  pwq_hi _ σ 4 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.7598356856515:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.7598356856516 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_11_32 (σ : ℝ) (h : σ ≤ (11:ℕ) / (32:ℕ)) : (0.6854717619233:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_11_32 (σ : ℝ) (h : (11:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.6854717619234 :=
  pwq_hi _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_17_32 (σ : ℝ) (h : σ ≤ (17:ℕ) / (32:ℕ)) : (0.5578652806066:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_17_32 (σ : ℝ) (h : (17:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.5578652806067 :=
  pwq_hi _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_20_32 (σ : ℝ) (h : σ ≤ (20:ℕ) / (32:ℕ)) : (0.5032678828257:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_20_32 (σ : ℝ) (h : (20:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.5032678828258 :=
  pwq_hi _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_24_32 (σ : ℝ) (h : σ ≤ (24:ℕ) / (32:ℕ)) : (0.4386913376508:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_24_32 (σ : ℝ) (h : (24:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.4386913376509 :=
  pwq_hi _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_30_32 (σ : ℝ) (h : σ ≤ (30:ℕ) / (32:ℕ)) : (0.3570251610243:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 30 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_30_32 (σ : ℝ) (h : (30:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.3570251610244 :=
  pwq_hi _ σ 32 30 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_33_32 (σ : ℝ) (h : σ ≤ (33:ℕ) / (32:ℕ)) : (0.3220836699297:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_33_32 (σ : ℝ) (h : (33:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.3220836699298 :=
  pwq_hi _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_34_32 (σ : ℝ) (h : σ ≤ (34:ℕ) / (32:ℕ)) : (0.3112136713063:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_34_32 (σ : ℝ) (h : (34:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.3112136713064 :=
  pwq_hi _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_37_32 (σ : ℝ) (h : σ ≤ (37:ℕ) / (32:ℕ)) : (0.2807556786728:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 37 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_37_32 (σ : ℝ) (h : (37:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.2807556786729 :=
  pwq_hi _ σ 32 37 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_46_32 (σ : ℝ) (h : σ ≤ (46:ℕ) / (32:ℕ)) : (0.2061285728248:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_46_32 (σ : ℝ) (h : (46:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.2061285728249 :=
  pwq_hi _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_48_32 (σ : ℝ) (h : σ ≤ (48:ℕ) / (32:ℕ)) : (0.1924500897298:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 48 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_48_32 (σ : ℝ) (h : (48:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.1924500897299 :=
  pwq_hi _ σ 32 48 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_52_32 (σ : ℝ) (h : σ ≤ (52:ℕ) / (32:ℕ)) : (0.1677559609419:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 52 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_52_32 (σ : ℝ) (h : (52:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.167755960942 :=
  pwq_hi _ σ 32 52 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_64_32 (σ : ℝ) (h : σ ≤ (64:ℕ) / (32:ℕ)) : (0.1111111111111:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 64 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_64_32 (σ : ℝ) (h : (64:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.1111111111112 :=
  pwq_hi _ σ 32 64 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.7071067811865:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.7071067811866 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.3535533905932:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.3535533905933 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_8_4 (σ : ℝ) (h : σ ≤ (8:ℕ) / (4:ℕ)) : (0.0625:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_8_4 (σ : ℝ) (h : (8:ℕ) / (4:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.0625 :=
  pwq_hi _ σ 4 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.7071067811865:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.7071067811866 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_11_32 (σ : ℝ) (h : σ ≤ (11:ℕ) / (32:ℕ)) : (0.6209289060367:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_11_32 (σ : ℝ) (h : (11:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.6209289060368 :=
  pwq_hi _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_17_32 (σ : ℝ) (h : σ ≤ (17:ℕ) / (32:ℕ)) : (0.4788016403492:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_17_32 (σ : ℝ) (h : (17:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.4788016403493 :=
  pwq_hi _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_20_32 (σ : ℝ) (h : σ ≤ (20:ℕ) / (32:ℕ)) : (0.4204482076268:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_20_32 (σ : ℝ) (h : (20:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.4204482076269 :=
  pwq_hi _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_24_32 (σ : ℝ) (h : σ ≤ (24:ℕ) / (32:ℕ)) : (0.3535533905932:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_24_32 (σ : ℝ) (h : (24:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.3535533905933 :=
  pwq_hi _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_30_32 (σ : ℝ) (h : σ ≤ (30:ℕ) / (32:ℕ)) : (0.2726269331663:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 30 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_30_32 (σ : ℝ) (h : (30:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.2726269331664 :=
  pwq_hi _ σ 32 30 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_33_32 (σ : ℝ) (h : σ ≤ (33:ℕ) / (32:ℕ)) : (0.2394008201746:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_33_32 (σ : ℝ) (h : (33:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.2394008201747 :=
  pwq_hi _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_34_32 (σ : ℝ) (h : σ ≤ (34:ℕ) / (32:ℕ)) : (0.2292510108011:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_34_32 (σ : ℝ) (h : (34:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.2292510108012 :=
  pwq_hi _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_37_32 (σ : ℝ) (h : σ ≤ (37:ℕ) / (32:ℕ)) : (0.2013112914936:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 37 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_37_32 (σ : ℝ) (h : (37:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.2013112914937 :=
  pwq_hi _ σ 32 37 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_46_32 (σ : ℝ) (h : σ ≤ (46:ℕ) / (32:ℕ)) : (0.1363134665831:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_46_32 (σ : ℝ) (h : (46:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.1363134665832 :=
  pwq_hi _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_48_32 (σ : ℝ) (h : σ ≤ (48:ℕ) / (32:ℕ)) : (0.125:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 48 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_48_32 (σ : ℝ) (h : (48:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.125 :=
  pwq_hi _ σ 32 48 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_52_32 (σ : ℝ) (h : σ ≤ (52:ℕ) / (32:ℕ)) : (0.1051120519067:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 52 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_52_32 (σ : ℝ) (h : (52:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.1051120519068 :=
  pwq_hi _ σ 32 52 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_64_32 (σ : ℝ) (h : σ ≤ (64:ℕ) / (32:ℕ)) : (0.0625:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 64 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_64_32 (σ : ℝ) (h : (64:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.0625 :=
  pwq_hi _ σ 32 64 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.6687403049764:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.6687403049765 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.2990697562442:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.2990697562443 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_8_4 (σ : ℝ) (h : σ ≤ (8:ℕ) / (4:ℕ)) : (0.04:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_8_4 (σ : ℝ) (h : (8:ℕ) / (4:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.04 :=
  pwq_hi _ σ 4 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.6687403049764:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.6687403049765 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_11_32 (σ : ℝ) (h : σ ≤ (11:ℕ) / (32:ℕ)) : (0.5750810552891:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_11_32 (σ : ℝ) (h : (11:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.5750810552892 :=
  pwq_hi _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_17_32 (σ : ℝ) (h : σ ≤ (17:ℕ) / (32:ℕ)) : (0.4252772835227:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_17_32 (σ : ℝ) (h : (17:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.4252772835228 :=
  pwq_hi _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_20_32 (σ : ℝ) (h : σ ≤ (20:ℕ) / (32:ℕ)) : (0.3657158199959:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_20_32 (σ : ℝ) (h : (20:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.365715819996 :=
  pwq_hi _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_24_32 (σ : ℝ) (h : σ ≤ (24:ℕ) / (32:ℕ)) : (0.2990697562442:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_24_32 (σ : ℝ) (h : (24:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.2990697562443 :=
  pwq_hi _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_30_32 (σ : ℝ) (h : σ ≤ (30:ℕ) / (32:ℕ)) : (0.221164603406:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 30 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_30_32 (σ : ℝ) (h : (30:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.2211646034061 :=
  pwq_hi _ σ 32 30 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_33_32 (σ : ℝ) (h : σ ≤ (33:ℕ) / (32:ℕ)) : (0.1901897830486:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_33_32 (σ : ℝ) (h : (33:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.1901897830487 :=
  pwq_hi _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_34_32 (σ : ℝ) (h : σ ≤ (34:ℕ) / (32:ℕ)) : (0.1808607678804:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_34_32 (σ : ℝ) (h : (34:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.1808607678805 :=
  pwq_hi _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_37_32 (σ : ℝ) (h : σ ≤ (37:ℕ) / (32:ℕ)) : (0.1555306304691:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 37 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_37_32 (σ : ℝ) (h : (37:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.1555306304692 :=
  pwq_hi _ σ 32 37 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_46_32 (σ : ℝ) (h : σ ≤ (46:ℕ) / (32:ℕ)) : (0.0989078174865:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_46_32 (σ : ℝ) (h : (46:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.0989078174866 :=
  pwq_hi _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_48_32 (σ : ℝ) (h : σ ≤ (48:ℕ) / (32:ℕ)) : (0.0894427190999:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 48 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_48_32 (σ : ℝ) (h : (48:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.0894427191 :=
  pwq_hi _ σ 32 48 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_52_32 (σ : ℝ) (h : σ ≤ (52:ℕ) / (32:ℕ)) : (0.0731431639991:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 52 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_52_32 (σ : ℝ) (h : (52:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.0731431639992 :=
  pwq_hi _ σ 32 52 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_64_32 (σ : ℝ) (h : σ ≤ (64:ℕ) / (32:ℕ)) : (0.04:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 64 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_64_32 (σ : ℝ) (h : (64:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.04 :=
  pwq_hi _ σ 32 64 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_6_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.6389431042462:ℝ) ≤ ((6:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_6_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((6:ℕ):ℝ) ^ (-σ) ≤ 0.6389431042463 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_6_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.2608474300122:ℝ) ≤ ((6:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_6_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((6:ℕ):ℝ) ^ (-σ) ≤ 0.2608474300123 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_6_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.6389431042462:ℝ) ≤ ((6:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_6_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((6:ℕ):ℝ) ^ (-σ) ≤ 0.6389431042463 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_6_11_32 (σ : ℝ) (h : σ ≤ (11:ℕ) / (32:ℕ)) : (0.5401451833267:ℝ) ≤ ((6:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_6_11_32 (σ : ℝ) (h : (11:ℕ) / (32:ℕ) ≤ σ) : ((6:ℕ):ℝ) ^ (-σ) ≤ 0.5401451833268 :=
  pwq_hi _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_6_20_32 (σ : ℝ) (h : σ ≤ (20:ℕ) / (32:ℕ)) : (0.3263288485169:ℝ) ≤ ((6:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_6_20_32 (σ : ℝ) (h : (20:ℕ) / (32:ℕ) ≤ σ) : ((6:ℕ):ℝ) ^ (-σ) ≤ 0.326328848517 :=
  pwq_hi _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_6_24_32 (σ : ℝ) (h : σ ≤ (24:ℕ) / (32:ℕ)) : (0.2608474300122:ℝ) ≤ ((6:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_6_24_32 (σ : ℝ) (h : (24:ℕ) / (32:ℕ) ≤ σ) : ((6:ℕ):ℝ) ^ (-σ) ≤ 0.2608474300123 :=
  pwq_hi _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_6_33_32 (σ : ℝ) (h : σ ≤ (33:ℕ) / (32:ℕ)) : (0.1575910405239:ℝ) ≤ ((6:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_6_33_32 (σ : ℝ) (h : (33:ℕ) / (32:ℕ) ≤ σ) : ((6:ℕ):ℝ) ^ (-σ) ≤ 0.157591040524 :=
  pwq_hi _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_6_34_32 (σ : ℝ) (h : σ ≤ (34:ℕ) / (32:ℕ)) : (0.1490096163205:ℝ) ≤ ((6:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_6_34_32 (σ : ℝ) (h : (34:ℕ) / (32:ℕ) ≤ σ) : ((6:ℕ):ℝ) ^ (-σ) ≤ 0.1490096163206 :=
  pwq_hi _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_6_46_32 (σ : ℝ) (h : σ ≤ (46:ℕ) / (32:ℕ)) : (0.0761040164432:ℝ) ≤ ((6:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_6_46_32 (σ : ℝ) (h : (46:ℕ) / (32:ℕ) ≤ σ) : ((6:ℕ):ℝ) ^ (-σ) ≤ 0.0761040164433 :=
  pwq_hi _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_7_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.6147881529512:ℝ) ≤ ((7:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_7_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((7:ℕ):ℝ) ^ (-σ) ≤ 0.6147881529513 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_7_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.2323680802425:ℝ) ≤ ((7:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_7_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((7:ℕ):ℝ) ^ (-σ) ≤ 0.2323680802426 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_7_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.6147881529512:ℝ) ≤ ((7:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_7_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((7:ℕ):ℝ) ^ (-σ) ≤ 0.6147881529513 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_7_11_32 (σ : ℝ) (h : σ ≤ (11:ℕ) / (32:ℕ)) : (0.5122683788994:ℝ) ≤ ((7:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_7_11_32 (σ : ℝ) (h : (11:ℕ) / (32:ℕ) ≤ σ) : ((7:ℕ):ℝ) ^ (-σ) ≤ 0.5122683788995 :=
  pwq_hi _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_7_20_32 (σ : ℝ) (h : σ ≤ (20:ℕ) / (32:ℕ)) : (0.2963560004336:ℝ) ≤ ((7:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_7_20_32 (σ : ℝ) (h : (20:ℕ) / (32:ℕ) ≤ σ) : ((7:ℕ):ℝ) ^ (-σ) ≤ 0.2963560004337 :=
  pwq_hi _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_7_24_32 (σ : ℝ) (h : σ ≤ (24:ℕ) / (32:ℕ)) : (0.2323680802425:ℝ) ≤ ((7:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_7_24_32 (σ : ℝ) (h : (24:ℕ) / (32:ℕ) ≤ σ) : ((7:ℕ):ℝ) ^ (-σ) ≤ 0.2323680802426 :=
  pwq_hi _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_7_33_32 (σ : ℝ) (h : σ ≤ (33:ℕ) / (32:ℕ)) : (0.1344289004077:ℝ) ≤ ((7:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_7_33_32 (σ : ℝ) (h : (33:ℕ) / (32:ℕ) ≤ σ) : ((7:ℕ):ℝ) ^ (-σ) ≤ 0.1344289004078 :=
  pwq_hi _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_7_34_32 (σ : ℝ) (h : σ ≤ (34:ℕ) / (32:ℕ)) : (0.1264979048539:ℝ) ≤ ((7:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_7_34_32 (σ : ℝ) (h : (34:ℕ) / (32:ℕ) ≤ σ) : ((7:ℕ):ℝ) ^ (-σ) ≤ 0.126497904854 :=
  pwq_hi _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_7_46_32 (σ : ℝ) (h : σ ≤ (46:ℕ) / (32:ℕ)) : (0.0609777741581:ℝ) ≤ ((7:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_7_46_32 (σ : ℝ) (h : (46:ℕ) / (32:ℕ) ≤ σ) : ((7:ℕ):ℝ) ^ (-σ) ≤ 0.0609777741582 :=
  pwq_hi _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_8_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.5946035575013:ℝ) ≤ ((8:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_8_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((8:ℕ):ℝ) ^ (-σ) ≤ 0.5946035575014 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_8_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.2102241038134:ℝ) ≤ ((8:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_8_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((8:ℕ):ℝ) ^ (-σ) ≤ 0.2102241038135 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_8_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.5946035575013:ℝ) ≤ ((8:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_8_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((8:ℕ):ℝ) ^ (-σ) ≤ 0.5946035575014 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_8_11_32 (σ : ℝ) (h : σ ≤ (11:ℕ) / (32:ℕ)) : (0.4892860310438:ℝ) ≤ ((8:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_8_11_32 (σ : ℝ) (h : (11:ℕ) / (32:ℕ) ≤ σ) : ((8:ℕ):ℝ) ^ (-σ) ≤ 0.4892860310439 :=
  pwq_hi _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_8_20_32 (σ : ℝ) (h : σ ≤ (20:ℕ) / (32:ℕ)) : (0.2726269331663:ℝ) ≤ ((8:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_8_20_32 (σ : ℝ) (h : (20:ℕ) / (32:ℕ) ≤ σ) : ((8:ℕ):ℝ) ^ (-σ) ≤ 0.2726269331664 :=
  pwq_hi _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_8_24_32 (σ : ℝ) (h : σ ≤ (24:ℕ) / (32:ℕ)) : (0.2102241038134:ℝ) ≤ ((8:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_8_24_32 (σ : ℝ) (h : (24:ℕ) / (32:ℕ) ≤ σ) : ((8:ℕ):ℝ) ^ (-σ) ≤ 0.2102241038135 :=
  pwq_hi _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_8_33_32 (σ : ℝ) (h : σ ≤ (33:ℕ) / (32:ℕ)) : (0.1171354771318:ℝ) ≤ ((8:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_8_33_32 (σ : ℝ) (h : (33:ℕ) / (32:ℕ) ≤ σ) : ((8:ℕ):ℝ) ^ (-σ) ≤ 0.1171354771319 :=
  pwq_hi _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_8_34_32 (σ : ℝ) (h : σ ≤ (34:ℕ) / (32:ℕ)) : (0.1097657600233:ℝ) ≤ ((8:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_8_34_32 (σ : ℝ) (h : (34:ℕ) / (32:ℕ) ≤ σ) : ((8:ℕ):ℝ) ^ (-σ) ≤ 0.1097657600234 :=
  pwq_hi _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_8_46_32 (σ : ℝ) (h : σ ≤ (46:ℕ) / (32:ℕ)) : (0.0503278228734:ℝ) ≤ ((8:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_8_46_32 (σ : ℝ) (h : (46:ℕ) / (32:ℕ) ≤ σ) : ((8:ℕ):ℝ) ^ (-σ) ≤ 0.0503278228735 :=
  pwq_hi _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_9_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.5773502691896:ℝ) ≤ ((9:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_9_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((9:ℕ):ℝ) ^ (-σ) ≤ 0.5773502691897 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_9_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.1924500897298:ℝ) ≤ ((9:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_9_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((9:ℕ):ℝ) ^ (-σ) ≤ 0.1924500897299 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_9_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.5773502691896:ℝ) ≤ ((9:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_9_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((9:ℕ):ℝ) ^ (-σ) ≤ 0.5773502691897 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_9_11_32 (σ : ℝ) (h : σ ≤ (11:ℕ) / (32:ℕ)) : (0.4698715363942:ℝ) ≤ ((9:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_9_11_32 (σ : ℝ) (h : (11:ℕ) / (32:ℕ) ≤ σ) : ((9:ℕ):ℝ) ^ (-σ) ≤ 0.4698715363943 :=
  pwq_hi _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_9_20_32 (σ : ℝ) (h : σ ≤ (20:ℕ) / (32:ℕ)) : (0.2532785618838:ℝ) ≤ ((9:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_9_20_32 (σ : ℝ) (h : (20:ℕ) / (32:ℕ) ≤ σ) : ((9:ℕ):ℝ) ^ (-σ) ≤ 0.2532785618839 :=
  pwq_hi _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_9_24_32 (σ : ℝ) (h : σ ≤ (24:ℕ) / (32:ℕ)) : (0.1924500897298:ℝ) ≤ ((9:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_9_24_32 (σ : ℝ) (h : (24:ℕ) / (32:ℕ) ≤ σ) : ((9:ℕ):ℝ) ^ (-σ) ≤ 0.1924500897299 :=
  pwq_hi _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_9_33_32 (σ : ℝ) (h : σ ≤ (33:ℕ) / (32:ℕ)) : (0.1037378904354:ℝ) ≤ ((9:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_9_33_32 (σ : ℝ) (h : (33:ℕ) / (32:ℕ) ≤ σ) : ((9:ℕ):ℝ) ^ (-σ) ≤ 0.1037378904355 :=
  pwq_hi _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_9_34_32 (σ : ℝ) (h : σ ≤ (34:ℕ) / (32:ℕ)) : (0.0968539492079:ℝ) ≤ ((9:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_9_34_32 (σ : ℝ) (h : (34:ℕ) / (32:ℕ) ≤ σ) : ((9:ℕ):ℝ) ^ (-σ) ≤ 0.096853949208 :=
  pwq_hi _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_9_46_32 (σ : ℝ) (h : σ ≤ (46:ℕ) / (32:ℕ)) : (0.0424889885348:ℝ) ≤ ((9:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_9_46_32 (σ : ℝ) (h : (46:ℕ) / (32:ℕ) ≤ σ) : ((9:ℕ):ℝ) ^ (-σ) ≤ 0.0424889885349 :=
  pwq_hi _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_10_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.5623413251903:ℝ) ≤ ((10:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_10_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((10:ℕ):ℝ) ^ (-σ) ≤ 0.5623413251904 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_10_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.1778279410038:ℝ) ≤ ((10:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_10_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((10:ℕ):ℝ) ^ (-σ) ≤ 0.1778279410039 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_10_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.5623413251903:ℝ) ≤ ((10:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_10_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((10:ℕ):ℝ) ^ (-σ) ≤ 0.5623413251904 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_10_11_32 (σ : ℝ) (h : σ ≤ (11:ℕ) / (32:ℕ)) : (0.45315836376:ℝ) ≤ ((10:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_10_11_32 (σ : ℝ) (h : (11:ℕ) / (32:ℕ) ≤ σ) : ((10:ℕ):ℝ) ^ (-σ) ≤ 0.4531583637601 :=
  pwq_hi _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_10_20_32 (σ : ℝ) (h : σ ≤ (20:ℕ) / (32:ℕ)) : (0.2371373705661:ℝ) ≤ ((10:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_10_20_32 (σ : ℝ) (h : (20:ℕ) / (32:ℕ) ≤ σ) : ((10:ℕ):ℝ) ^ (-σ) ≤ 0.2371373705662 :=
  pwq_hi _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_10_24_32 (σ : ℝ) (h : σ ≤ (24:ℕ) / (32:ℕ)) : (0.1778279410038:ℝ) ≤ ((10:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_10_24_32 (σ : ℝ) (h : (24:ℕ) / (32:ℕ) ≤ σ) : ((10:ℕ):ℝ) ^ (-σ) ≤ 0.1778279410039 :=
  pwq_hi _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_10_33_32 (σ : ℝ) (h : σ ≤ (33:ℕ) / (32:ℕ)) : (0.0930572040929:ℝ) ≤ ((10:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_10_33_32 (σ : ℝ) (h : (33:ℕ) / (32:ℕ) ≤ σ) : ((10:ℕ):ℝ) ^ (-σ) ≤ 0.093057204093 :=
  pwq_hi _ σ 32 33 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_10_34_32 (σ : ℝ) (h : σ ≤ (34:ℕ) / (32:ℕ)) : (0.086596432336:ℝ) ≤ ((10:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_10_34_32 (σ : ℝ) (h : (34:ℕ) / (32:ℕ) ≤ σ) : ((10:ℕ):ℝ) ^ (-σ) ≤ 0.0865964323361 :=
  pwq_hi _ σ 32 34 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_10_46_32 (σ : ℝ) (h : σ ≤ (46:ℕ) / (32:ℕ)) : (0.0365174127254:ℝ) ≤ ((10:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_10_46_32 (σ : ℝ) (h : (46:ℕ) / (32:ℕ) ≤ σ) : ((10:ℕ):ℝ) ^ (-σ) ≤ 0.0365174127255 :=
  pwq_hi _ σ 32 46 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_11_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.5491004867761:ℝ) ≤ ((11:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_11_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((11:ℕ):ℝ) ^ (-σ) ≤ 0.5491004867762 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_11_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.1655600260761:ℝ) ≤ ((11:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_11_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((11:ℕ):ℝ) ^ (-σ) ≤ 0.1655600260762 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_11_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.5491004867761:ℝ) ≤ ((11:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_11_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((11:ℕ):ℝ) ^ (-σ) ≤ 0.5491004867762 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_11_11_32 (σ : ℝ) (h : σ ≤ (11:ℕ) / (32:ℕ)) : (0.4385521701964:ℝ) ≤ ((11:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_11_11_32 (σ : ℝ) (h : (11:ℕ) / (32:ℕ) ≤ σ) : ((11:ℕ):ℝ) ^ (-σ) ≤ 0.4385521701965 :=
  pwq_hi _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_11_20_32 (σ : ℝ) (h : σ ≤ (20:ℕ) / (32:ℕ)) : (0.223423870861:ℝ) ≤ ((11:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_11_20_32 (σ : ℝ) (h : (20:ℕ) / (32:ℕ) ≤ σ) : ((11:ℕ):ℝ) ^ (-σ) ≤ 0.2234238708611 :=
  pwq_hi _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_12_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.5372849659117:ℝ) ≤ ((12:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_12_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((12:ℕ):ℝ) ^ (-σ) ≤ 0.5372849659118 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_12_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.1551008098503:ℝ) ≤ ((12:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_12_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((12:ℕ):ℝ) ^ (-σ) ≤ 0.1551008098504 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_12_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.5372849659117:ℝ) ≤ ((12:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_12_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((12:ℕ):ℝ) ^ (-σ) ≤ 0.5372849659118 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_12_11_32 (σ : ℝ) (h : σ ≤ (11:ℕ) / (32:ℕ)) : (0.4256292312501:ℝ) ≤ ((12:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_12_11_32 (σ : ℝ) (h : (11:ℕ) / (32:ℕ) ≤ σ) : ((12:ℕ):ℝ) ^ (-σ) ≤ 0.4256292312502 :=
  pwq_hi _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_12_20_32 (σ : ℝ) (h : σ ≤ (20:ℕ) / (32:ℕ)) : (0.2115980792902:ℝ) ≤ ((12:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_12_20_32 (σ : ℝ) (h : (20:ℕ) / (32:ℕ) ≤ σ) : ((12:ℕ):ℝ) ^ (-σ) ≤ 0.2115980792903 :=
  pwq_hi _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_13_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.5266403878479:ℝ) ≤ ((13:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_13_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((13:ℕ):ℝ) ^ (-σ) ≤ 0.526640387848 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_13_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.1460637632396:ℝ) ≤ ((13:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_13_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((13:ℕ):ℝ) ^ (-σ) ≤ 0.1460637632397 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_13_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.5266403878479:ℝ) ≤ ((13:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_13_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((13:ℕ):ℝ) ^ (-σ) ≤ 0.526640387848 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_13_11_32 (σ : ℝ) (h : σ ≤ (11:ℕ) / (32:ℕ)) : (0.414077824215:ℝ) ≤ ((13:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_13_11_32 (σ : ℝ) (h : (11:ℕ) / (32:ℕ) ≤ σ) : ((13:ℕ):ℝ) ^ (-σ) ≤ 0.4140778242151 :=
  pwq_hi _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_13_20_32 (σ : ℝ) (h : σ ≤ (20:ℕ) / (32:ℕ)) : (0.2012729466799:ℝ) ≤ ((13:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_13_20_32 (σ : ℝ) (h : (20:ℕ) / (32:ℕ) ≤ σ) : ((13:ℕ):ℝ) ^ (-σ) ≤ 0.20127294668 :=
  pwq_hi _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_14_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.5169731539571:ℝ) ≤ ((14:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_14_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((14:ℕ):ℝ) ^ (-σ) ≤ 0.5169731539572 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_14_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.1381668871619:ℝ) ≤ ((14:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_14_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((14:ℕ):ℝ) ^ (-σ) ≤ 0.138166887162 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_14_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.5169731539571:ℝ) ≤ ((14:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_14_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((14:ℕ):ℝ) ^ (-σ) ≤ 0.5169731539572 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_14_11_32 (σ : ℝ) (h : σ ≤ (11:ℕ) / (32:ℕ)) : (0.4036625763499:ℝ) ≤ ((14:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_14_11_32 (σ : ℝ) (h : (11:ℕ) / (32:ℕ) ≤ σ) : ((14:ℕ):ℝ) ^ (-σ) ≤ 0.40366257635 :=
  pwq_hi _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_14_20_32 (σ : ℝ) (h : σ ≤ (20:ℕ) / (32:ℕ)) : (0.1921630918102:ℝ) ≤ ((14:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_14_20_32 (σ : ℝ) (h : (20:ℕ) / (32:ℕ) ≤ σ) : ((14:ℕ):ℝ) ^ (-σ) ≤ 0.1921630918103 :=
  pwq_hi _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_15_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.5081327481546:ℝ) ≤ ((15:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_15_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((15:ℕ):ℝ) ^ (-σ) ≤ 0.5081327481547 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_15_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.1311993114176:ℝ) ≤ ((15:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_15_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((15:ℕ):ℝ) ^ (-σ) ≤ 0.1311993114177 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_15_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.5081327481546:ℝ) ≤ ((15:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_15_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((15:ℕ):ℝ) ^ (-σ) ≤ 0.5081327481547 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_15_11_32 (σ : ℝ) (h : σ ≤ (11:ℕ) / (32:ℕ)) : (0.3942018242177:ℝ) ≤ ((15:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_15_11_32 (σ : ℝ) (h : (11:ℕ) / (32:ℕ) ≤ σ) : ((15:ℕ):ℝ) ^ (-σ) ≤ 0.3942018242178 :=
  pwq_hi _ σ 32 11 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_15_20_32 (σ : ℝ) (h : σ ≤ (20:ℕ) / (32:ℕ)) : (0.1840530264452:ℝ) ≤ ((15:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_15_20_32 (σ : ℝ) (h : (20:ℕ) / (32:ℕ) ≤ σ) : ((15:ℕ):ℝ) ^ (-σ) ≤ 0.1840530264453 :=
  pwq_hi _ σ 32 20 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_16_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.5:ℝ) ≤ ((16:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_16_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((16:ℕ):ℝ) ^ (-σ) ≤ 0.5 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_16_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.125:ℝ) ≤ ((16:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_16_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((16:ℕ):ℝ) ^ (-σ) ≤ 0.125 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_17_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4924790605054:ℝ) ≤ ((17:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_17_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((17:ℕ):ℝ) ^ (-σ) ≤ 0.4924790605055 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_17_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.1194437167569:ℝ) ≤ ((17:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_17_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((17:ℕ):ℝ) ^ (-σ) ≤ 0.119443716757 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_18_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4854917717073:ℝ) ≤ ((18:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_18_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((18:ℕ):ℝ) ^ (-σ) ≤ 0.4854917717074 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_18_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.1144315079948:ℝ) ≤ ((18:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_18_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((18:ℕ):ℝ) ^ (-σ) ≤ 0.1144315079949 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_19_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4789736254435:ℝ) ≤ ((19:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_19_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((19:ℕ):ℝ) ^ (-σ) ≤ 0.4789736254436 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_19_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.1098840857857:ℝ) ≤ ((19:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_19_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((19:ℕ):ℝ) ^ (-σ) ≤ 0.1098840857858 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_20_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4728708045015:ℝ) ≤ ((20:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_20_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((20:ℕ):ℝ) ^ (-σ) ≤ 0.4728708045016 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_20_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.105737126344:ℝ) ≤ ((20:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_20_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((20:ℕ):ℝ) ^ (-σ) ≤ 0.1057371263441 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_21_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4671379777282:ℝ) ≤ ((21:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_21_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((21:ℕ):ℝ) ^ (-σ) ≤ 0.4671379777283 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_21_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.1019378639489:ℝ) ≤ ((21:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_21_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((21:ℕ):ℝ) ^ (-σ) ≤ 0.101937863949 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_22_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4617366309441:ℝ) ≤ ((22:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_22_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((22:ℕ):ℝ) ^ (-σ) ≤ 0.4617366309442 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_22_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.0984425804849:ℝ) ≤ ((22:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_22_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((22:ℕ):ℝ) ^ (-σ) ≤ 0.098442580485 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_23_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4566337854967:ℝ) ≤ ((23:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_23_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((23:ℕ):ℝ) ^ (-σ) ≤ 0.4566337854968 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_23_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.0952147262215:ℝ) ≤ ((23:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_23_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((23:ℕ):ℝ) ^ (-σ) ≤ 0.0952147262216 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_24_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4518010018049:ℝ) ≤ ((24:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_24_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((24:ℕ):ℝ) ^ (-σ) ≤ 0.451801001805 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_24_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.0922234933083:ℝ) ≤ ((24:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_24_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((24:ℕ):ℝ) ^ (-σ) ≤ 0.0922234933084 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_25_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4472135954999:ℝ) ≤ ((25:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_25_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((25:ℕ):ℝ) ^ (-σ) ≤ 0.4472135955 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_25_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.0894427190999:ℝ) ≤ ((25:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_25_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((25:ℕ):ℝ) ^ (-σ) ≤ 0.0894427191 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_26_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4428500142691:ℝ) ≤ ((26:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_26_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((26:ℕ):ℝ) ^ (-σ) ≤ 0.4428500142692 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_26_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.0868500332443:ℝ) ≤ ((26:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_26_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((26:ℕ):ℝ) ^ (-σ) ≤ 0.0868500332444 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_27_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4386913376508:ℝ) ≤ ((27:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_27_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((27:ℕ):ℝ) ^ (-σ) ≤ 0.4386913376509 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_27_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.0844261872946:ℝ) ≤ ((27:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_27_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((27:ℕ):ℝ) ^ (-σ) ≤ 0.0844261872947 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_28_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4347208719449:ℝ) ≤ ((28:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_28_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((28:ℕ):ℝ) ^ (-σ) ≤ 0.434720871945 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_28_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.0821545226354:ℝ) ≤ ((28:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_28_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((28:ℕ):ℝ) ^ (-σ) ≤ 0.0821545226355 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_29_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4309238194589:ℝ) ≤ ((29:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_29_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((29:ℕ):ℝ) ^ (-σ) ≤ 0.430923819459 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_29_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.0800205443829:ℝ) ≤ ((29:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_29_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((29:ℕ):ℝ) ^ (-σ) ≤ 0.080020544383 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_30_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4272870063962:ℝ) ≤ ((30:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_30_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((30:ℕ):ℝ) ^ (-σ) ≤ 0.4272870063963 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_30_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.0780115773106:ℝ) ≤ ((30:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_30_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((30:ℕ):ℝ) ^ (-σ) ≤ 0.0780115773107 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_31_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.423798657415:ℝ) ≤ ((31:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_31_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((31:ℕ):ℝ) ^ (-σ) ≤ 0.4237986574151 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_32_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4204482076268:ℝ) ≤ ((32:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_32_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((32:ℕ):ℝ) ^ (-σ) ≤ 0.4204482076269 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_33_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4172261448611:ℝ) ≤ ((33:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_33_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((33:ℕ):ℝ) ^ (-σ) ≤ 0.4172261448612 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_34_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4141238765665:ℝ) ≤ ((34:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_34_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((34:ℕ):ℝ) ^ (-σ) ≤ 0.4141238765666 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_35_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4111336169005:ℝ) ≤ ((35:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_35_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((35:ℕ):ℝ) ^ (-σ) ≤ 0.4111336169006 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_36_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4082482904638:ℝ) ≤ ((36:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_36_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((36:ℕ):ℝ) ^ (-σ) ≤ 0.4082482904639 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_37_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4054614498387:ℝ) ≤ ((37:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_37_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((37:ℕ):ℝ) ^ (-σ) ≤ 0.4054614498388 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_38_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4027672046365:ℝ) ≤ ((38:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_38_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((38:ℕ):ℝ) ^ (-σ) ≤ 0.4027672046366 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_39_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4001601601922:ℝ) ≤ ((39:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_39_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((39:ℕ):ℝ) ^ (-σ) ≤ 0.4001601601923 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_40_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3976353643835:ℝ) ≤ ((40:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_40_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((40:ℕ):ℝ) ^ (-σ) ≤ 0.3976353643836 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_41_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3951882613244:ℝ) ≤ ((41:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_41_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((41:ℕ):ℝ) ^ (-σ) ≤ 0.3951882613245 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_42_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3928146509005:ℝ) ≤ ((42:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_42_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((42:ℕ):ℝ) ^ (-σ) ≤ 0.3928146509006 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_43_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3905106532895:ℝ) ≤ ((43:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_43_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((43:ℕ):ℝ) ^ (-σ) ≤ 0.3905106532896 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_44_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3882726777522:ℝ) ≤ ((44:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_44_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((44:ℕ):ℝ) ^ (-σ) ≤ 0.3882726777523 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_45_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.386097395096:ℝ) ≤ ((45:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_45_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((45:ℕ):ℝ) ^ (-σ) ≤ 0.3860973950961 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_46_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3839817133079:ℝ) ≤ ((46:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_46_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((46:ℕ):ℝ) ^ (-σ) ≤ 0.383981713308 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_47_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3819227559309:ℝ) ≤ ((47:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_47_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((47:ℕ):ℝ) ^ (-σ) ≤ 0.381922755931 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_48_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3799178428257:ℝ) ≤ ((48:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_48_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((48:ℕ):ℝ) ^ (-σ) ≤ 0.3799178428258 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_49_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3779644730092:ℝ) ≤ ((49:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_49_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((49:ℕ):ℝ) ^ (-σ) ≤ 0.3779644730093 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_50_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3760603093086:ℝ) ≤ ((50:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_50_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((50:ℕ):ℝ) ^ (-σ) ≤ 0.3760603093087 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_51_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3742031646082:ℝ) ≤ ((51:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_51_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((51:ℕ):ℝ) ^ (-σ) ≤ 0.3742031646083 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_52_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3723909894939:ℝ) ≤ ((52:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_52_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((52:ℕ):ℝ) ^ (-σ) ≤ 0.372390989494 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_53_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3706218611316:ℝ) ≤ ((53:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_53_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((53:ℕ):ℝ) ^ (-σ) ≤ 0.3706218611317 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_54_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3688939732334:ℝ) ≤ ((54:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_54_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((54:ℕ):ℝ) ^ (-σ) ≤ 0.3688939732335 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_55_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3672056269893:ℝ) ≤ ((55:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_55_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((55:ℕ):ℝ) ^ (-σ) ≤ 0.3672056269894 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_56_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3655552228545:ℝ) ≤ ((56:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_56_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((56:ℕ):ℝ) ^ (-σ) ≤ 0.3655552228546 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_57_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3639412530979:ℝ) ≤ ((57:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_57_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((57:ℕ):ℝ) ^ (-σ) ≤ 0.363941253098 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_58_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3623622950304:ℝ) ≤ ((58:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_58_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((58:ℕ):ℝ) ^ (-σ) ≤ 0.3623622950305 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_59_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3608170048387:ℝ) ≤ ((59:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_59_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((59:ℕ):ℝ) ^ (-σ) ≤ 0.3608170048388 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_60_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.359304111963:ℝ) ≤ ((60:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_60_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((60:ℕ):ℝ) ^ (-σ) ≤ 0.3593041119631 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_61_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.357822413961:ℝ) ≤ ((61:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_61_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((61:ℕ):ℝ) ^ (-σ) ≤ 0.3578224139611 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_62_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3563707718096:ℝ) ≤ ((62:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_62_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((62:ℕ):ℝ) ^ (-σ) ≤ 0.3563707718097 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_63_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.354948105601:ℝ) ≤ ((63:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_63_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((63:ℕ):ℝ) ^ (-σ) ≤ 0.3549481056011 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_64_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3535533905932:ℝ) ≤ ((64:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_64_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((64:ℕ):ℝ) ^ (-σ) ≤ 0.3535533905933 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_65_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3521856535823:ℝ) ≤ ((65:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_65_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((65:ℕ):ℝ) ^ (-σ) ≤ 0.3521856535824 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_66_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3508439695638:ℝ) ≤ ((66:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_66_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((66:ℕ):ℝ) ^ (-σ) ≤ 0.3508439695639 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_67_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3495274586585:ℝ) ≤ ((67:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_67_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((67:ℕ):ℝ) ^ (-σ) ≤ 0.3495274586586 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_68_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3482352832757:ℝ) ≤ ((68:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_68_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((68:ℕ):ℝ) ^ (-σ) ≤ 0.3482352832758 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_69_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3469666454945:ℝ) ≤ ((69:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_69_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((69:ℕ):ℝ) ^ (-σ) ≤ 0.3469666454946 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_70_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3457207846419:ℝ) ≤ ((70:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_70_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((70:ℕ):ℝ) ^ (-σ) ≤ 0.345720784642 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_71_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3444969750511:ℝ) ≤ ((71:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_71_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((71:ℕ):ℝ) ^ (-σ) ≤ 0.3444969750512 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_72_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3432945239845:ℝ) ≤ ((72:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_72_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((72:ℕ):ℝ) ^ (-σ) ≤ 0.3432945239846 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_73_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3421127697063:ℝ) ≤ ((73:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_73_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((73:ℕ):ℝ) ^ (-σ) ≤ 0.3421127697064 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_74_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3409510796929:ℝ) ≤ ((74:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_74_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((74:ℕ):ℝ) ^ (-σ) ≤ 0.340951079693 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_75_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3398088489694:ℝ) ≤ ((75:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_75_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((75:ℕ):ℝ) ^ (-σ) ≤ 0.3398088489695 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_76_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3386854985606:ℝ) ≤ ((76:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_76_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((76:ℕ):ℝ) ^ (-σ) ≤ 0.3386854985607 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_77_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3375804740497:ℝ) ≤ ((77:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_77_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((77:ℕ):ℝ) ^ (-σ) ≤ 0.3375804740498 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_78_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.336493244233:ℝ) ≤ ((78:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_78_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((78:ℕ):ℝ) ^ (-σ) ≤ 0.3364932442331 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_79_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3354232998654:ℝ) ≤ ((79:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_79_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((79:ℕ):ℝ) ^ (-σ) ≤ 0.3354232998655 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_80_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3343701524882:ℝ) ≤ ((80:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_80_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((80:ℕ):ℝ) ^ (-σ) ≤ 0.3343701524883 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_81_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3333333333333:ℝ) ≤ ((81:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_81_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((81:ℕ):ℝ) ^ (-σ) ≤ 0.3333333333334 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_82_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.332312392298:ℝ) ≤ ((82:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_82_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((82:ℕ):ℝ) ^ (-σ) ≤ 0.3323123922981 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_83_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3313068969847:ℝ) ≤ ((83:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_83_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((83:ℕ):ℝ) ^ (-σ) ≤ 0.3313068969848 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_84_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3303164318013:ℝ) ≤ ((84:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_84_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((84:ℕ):ℝ) ^ (-σ) ≤ 0.3303164318014 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_85_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3293405971169:ℝ) ≤ ((85:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_85_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((85:ℕ):ℝ) ^ (-σ) ≤ 0.329340597117 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_86_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3283790084695:ℝ) ≤ ((86:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_86_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((86:ℕ):ℝ) ^ (-σ) ≤ 0.3283790084696 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_87_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3274312958221:ℝ) ≤ ((87:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_87_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((87:ℕ):ℝ) ^ (-σ) ≤ 0.3274312958222 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_88_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3264971028628:ℝ) ≤ ((88:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_88_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((88:ℕ):ℝ) ^ (-σ) ≤ 0.3264971028629 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_89_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3255760863463:ℝ) ≤ ((89:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_89_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((89:ℕ):ℝ) ^ (-σ) ≤ 0.3255760863464 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_90_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.324667915475:ℝ) ≤ ((90:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_90_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((90:ℕ):ℝ) ^ (-σ) ≤ 0.3246679154751 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_91_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3237722713145:ℝ) ≤ ((91:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_91_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((91:ℕ):ℝ) ^ (-σ) ≤ 0.3237722713146 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_92_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3228888462436:ℝ) ≤ ((92:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_92_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((92:ℕ):ℝ) ^ (-σ) ≤ 0.3228888462437 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_93_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3220173434351:ℝ) ≤ ((93:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_93_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((93:ℕ):ℝ) ^ (-σ) ≤ 0.3220173434352 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_94_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3211574763661:ℝ) ≤ ((94:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_94_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((94:ℕ):ℝ) ^ (-σ) ≤ 0.3211574763662 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_95_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3203089683547:ℝ) ≤ ((95:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_95_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((95:ℕ):ℝ) ^ (-σ) ≤ 0.3203089683548 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_96_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3194715521231:ℝ) ≤ ((96:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_96_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((96:ℕ):ℝ) ^ (-σ) ≤ 0.3194715521232 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_97_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3186449693834:ℝ) ≤ ((97:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_97_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((97:ℕ):ℝ) ^ (-σ) ≤ 0.3186449693835 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_98_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3178289704467:ℝ) ≤ ((98:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_98_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((98:ℕ):ℝ) ^ (-σ) ≤ 0.3178289704468 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_99_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3170233138523:ℝ) ≤ ((99:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_99_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((99:ℕ):ℝ) ^ (-σ) ≤ 0.3170233138524 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_100_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3162277660168:ℝ) ≤ ((100:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_100_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((100:ℕ):ℝ) ^ (-σ) ≤ 0.3162277660169 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_101_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3154421009012:ℝ) ≤ ((101:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_101_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((101:ℕ):ℝ) ^ (-σ) ≤ 0.3154421009013 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_102_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3146660996956:ℝ) ≤ ((102:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_102_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((102:ℕ):ℝ) ^ (-σ) ≤ 0.3146660996957 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_103_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3138995505196:ℝ) ≤ ((103:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_103_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((103:ℕ):ℝ) ^ (-σ) ≤ 0.3138995505197 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_104_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3131422481382:ℝ) ≤ ((104:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_104_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((104:ℕ):ℝ) ^ (-σ) ≤ 0.3131422481383 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_105_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.312393993692:ℝ) ≤ ((105:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_105_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((105:ℕ):ℝ) ^ (-σ) ≤ 0.3123939936921 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_106_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3116545944402:ℝ) ≤ ((106:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_106_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((106:ℕ):ℝ) ^ (-σ) ≤ 0.3116545944403 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_107_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3109238635173:ℝ) ≤ ((107:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_107_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((107:ℕ):ℝ) ^ (-σ) ≤ 0.3109238635174 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_108_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3102016197006:ℝ) ≤ ((108:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_108_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((108:ℕ):ℝ) ^ (-σ) ≤ 0.3102016197007 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_109_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3094876871898:ℝ) ≤ ((109:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_109_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((109:ℕ):ℝ) ^ (-σ) ≤ 0.3094876871899 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_110_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3087818953963:ℝ) ≤ ((110:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_110_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((110:ℕ):ℝ) ^ (-σ) ≤ 0.3087818953964 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_111_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3080840787435:ℝ) ≤ ((111:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_111_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((111:ℕ):ℝ) ^ (-σ) ≤ 0.3080840787436 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_112_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3073940764756:ℝ) ≤ ((112:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_112_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((112:ℕ):ℝ) ^ (-σ) ≤ 0.3073940764757 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_113_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3067117324758:ℝ) ≤ ((113:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_113_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((113:ℕ):ℝ) ^ (-σ) ≤ 0.3067117324759 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_114_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.306036895093:ℝ) ≤ ((114:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_114_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((114:ℕ):ℝ) ^ (-σ) ≤ 0.3060368950931 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_115_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3053694169756:ℝ) ≤ ((115:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_115_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((115:ℕ):ℝ) ^ (-σ) ≤ 0.3053694169757 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_116_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3047091549141:ℝ) ≤ ((116:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_116_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((116:ℕ):ℝ) ^ (-σ) ≤ 0.3047091549142 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_117_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3040559696901:ℝ) ≤ ((117:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_117_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((117:ℕ):ℝ) ^ (-σ) ≤ 0.3040559696902 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_118_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3034097259315:ℝ) ≤ ((118:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_118_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((118:ℕ):ℝ) ^ (-σ) ≤ 0.3034097259316 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_119_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3027702919753:ℝ) ≤ ((119:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_119_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((119:ℕ):ℝ) ^ (-σ) ≤ 0.3027702919754 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_120_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.3021375397356:ℝ) ≤ ((120:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_120_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((120:ℕ):ℝ) ^ (-σ) ≤ 0.3021375397357 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma u1_top (x : ℝ) : 0 < (I ^ (-3 : ℤ) * (1 - ((x : ℂ) + ((28 : ℝ) : ℂ) * I))).re := by
  rw [I_zpow_eq (-3) (-1) 1 (by norm_num), pow_one]; simp

lemma cs_hm1_2 : ‖exp (-((((-1:ℝ) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7692388889425:ℝ):ℂ) + ((0.6389612912677:ℝ):ℂ) * I)‖ ≤ 0.00000011971 := by
  have hl := lg_2
  refine (ecis_approx ((-1:ℝ) * Real.log ((2:ℕ):ℝ)) (0) 0 0 (-0.6931471808) (-0.6931471803) 0.6931472 0.0000000197 0.7692388889425 0.6389612912677 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_hm1_3 : ‖exp (-((((-1:ℝ) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4548324127347:ℝ):ℂ) + ((0.8905770468219:ℝ):ℂ) * I)‖ ≤ 0.00000011161 := by
  have hl := lg_3
  refine (ecis_approx ((-1:ℝ) * Real.log ((3:ℕ):ℝ)) (0) 0 0 (-1.098612288908165) (-1.098612288408164) 1.0986123 0.0000000116 0.4548324127347 0.8905770468219 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_hm1_4 : ‖exp (-((((-1:ℝ) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.1834569365231:ℝ):ℂ) + ((0.983027747544:ℝ):ℂ) * I)‖ ≤ 0.00000013941 := by
  have hl := lg_4
  refine (ecis_approx ((-1:ℝ) * Real.log ((4:ℕ):ℝ)) (0) 0 0 (-1.3862943616) (-1.3862943606) 1.3862944 0.0000000394 0.1834569365231 0.983027747544 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_hm1_5 : ‖exp (-((((-1:ℝ) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0386319575092):ℝ):ℂ) + ((0.9992535073037:ℝ):ℂ) * I)‖ ≤ 0.00000011293 := by
  have hl := lg_5
  refine (ecis_approx ((-1:ℝ) * Real.log ((5:ℕ):ℝ)) (0) 0 0 (-1.60943791291421) (-1.609437911914209) 1.6094379 0.00000001292 (-0.0386319575092) 0.9992535073037 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h28_2 : ‖exp (-((((28:ℝ) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8480164376045:ℝ):ℂ) + (((-0.5299699251396):ℝ):ℂ) * I)‖ ≤ 0.00000014088 := by
  have hl := lg_2
  refine (ecis_approx ((28:ℝ) * Real.log ((2:ℕ):ℝ)) (3) 18.84955592153875943076 18.84955592153875943082 19.4081210484 19.4081210624 (-0.5585651) 0.00000004087 0.8480164376045 (-0.5299699251396) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h28_3 : ‖exp (-((((28:ℝ) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.793180401478:ℝ):ℂ) + ((0.6089867409979:ℝ):ℂ) * I)‖ ≤ 0.00000015355 := by
  have hl := lg_3
  refine (ecis_approx ((28:ℝ) * Real.log ((3:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.761144075428592 30.76114408942862 0.6547825 0.00000005354 0.793180401478 0.6089867409979 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h28_4 : ‖exp (-((((28:ℝ) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4382636670103:ℝ):ℂ) + (((-0.8988464597353):ℝ):ℂ) * I)‖ ≤ 0.00000014629 := by
  have hl := lg_4
  refine (ecis_approx ((28:ℝ) * Real.log ((4:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 38.8162420968 38.8162421248 (-1.1171303) 0.00000004628 0.4382636670103 (-0.8988464597353) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h28_5 : ‖exp (-((((28:ℝ) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.4695949379756:ℝ):ℂ) + (((-0.8828819820495):ℝ):ℂ) * I)‖ ≤ 0.00000011667 := by
  have hl := lg_5
  refine (ecis_approx ((28:ℝ) * Real.log ((5:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.064261533597852 45.06426156159788 (-1.0819644) 0.00000001666 0.4695949379756 (-0.8828819820495) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h28_6 : ‖exp (-((((28:ℝ) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9953746855837:ℝ):ℂ) + ((0.0960689091184:ℝ):ℂ) * I)‖ ≤ 0.00000013362 := by
  have hl := lg_6
  refine (ecis_approx ((28:ℝ) * Real.log ((6:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.169265123828592 50.16926515182862 0.0962173 0.00000003361 0.9953746855837 0.0960689091184 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h28_7 : ‖exp (-((((28:ℝ) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.4727309146966):ℝ):ℂ) + ((0.8812068328632:ℝ):ℂ) * I)‖ ≤ 0.00000012239 := by
  have hl := lg_7
  refine (ecis_approx ((28:ℝ) * Real.log ((7:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.485484158991816 54.485484186991872 2.0631836 0.00000002238 (-0.4727309146966) 0.8812068328632 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h28_8 : ‖exp (-((((28:ℝ) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1047067973484):ℝ):ℂ) + (((-0.9945031355348):ℝ):ℂ) * I)‖ ≤ 0.0000001226 := by
  have hl := lg_8
  refine (ecis_approx ((28:ℝ) * Real.log ((8:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.2243631452 58.2243631872 (-1.6756954) 0.00000002259 (-0.1047067973484) (-0.9945031355348) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h28_9 : ‖exp (-((((28:ℝ) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.2582703951848:ℝ):ℂ) + ((0.9660726696119:ℝ):ℂ) * I)‖ ≤ 0.00000012095 := by
  have hl := lg_9
  refine (ecis_approx ((28:ℝ) * Real.log ((9:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 61.522288150857184 61.52228817885724 1.3095649 0.00000002094 0.2582703951848 0.9660726696119 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h28_10 : ‖exp (-((((28:ℝ) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.0696766715148):ℝ):ℂ) + (((-0.9975696273676):ℝ):ℂ) * I)‖ ≤ 0.00000015222 := by
  have hl := lg_10
  refine (ecis_approx ((28:ℝ) * Real.log ((10:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.472382581997852 64.47238262399788 (-1.6405295) 0.00000005221 (-0.0696766715148) (-0.9975696273676) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h28_11 : ‖exp (-((((28:ℝ) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3923401667244):ℝ):ℂ) + ((0.9198201963273:ℝ):ℂ) * I)‖ ≤ 0.00000016247 := by
  have hl := lg_11
  refine (ecis_approx ((28:ℝ) * Real.log ((11:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 67.141067616518924 67.14106765851898 1.9739707 0.00000006246 (-0.3923401667244) 0.9198201963273 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h28_12 : ‖exp (-((((28:ℝ) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8950077275241:ℝ):ℂ) + (((-0.4460506335295):ℝ):ℂ) * I)‖ ≤ 0.00000013527 := by
  have hl := lg_12
  refine (ecis_approx ((28:ℝ) * Real.log ((12:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 69.577386172228592 69.57738621422862 (-0.4623478) 0.00000003526 0.8950077275241 (-0.4460506335295) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h28_13 : ‖exp (-((((28:ℝ) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9055809258975):ℝ):ℂ) + (((-0.4241735335066):ℝ):ℂ) * I)‖ ≤ 0.00000015013 := by
  have hl := lg_13
  refine (ecis_approx ((28:ℝ) * Real.log ((13:ℕ):ℝ)) (11) 69.11503837897545124612 69.11503837897545124634 71.8185819870876 71.818582029087656 (-2.7035436) 0.00000005012 (-0.9055809258975) (-0.4241735335066) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h28_14 : ‖exp (-((((28:ℝ) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.06612953302:ℝ):ℂ) + ((0.9978110466729:ℝ):ℂ) * I)‖ ≤ 0.00000016325 := by
  have hl := lg_14
  refine (ecis_approx ((28:ℝ) * Real.log ((14:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 73.893605207391816 73.893605249391872 1.5046185 0.00000006324 0.06612953302 0.9978110466729 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h28_15 : ‖exp (-((((28:ℝ) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9101369223696:ℝ):ℂ) + (((-0.4143075941128):ℝ):ℂ) * I)‖ ≤ 0.00000016489 := by
  have hl := lg_15
  refine (ecis_approx ((28:ℝ) * Real.log ((15:ℕ):ℝ)) (12) 75.39822368615503772304 75.39822368615503772328 75.825405609026444 75.8254056510265 (-0.4271819) 0.00000006488 0.9101369223696 (-0.4143075941128) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H28
end Cert
end ZB
end RHV6Fresh
