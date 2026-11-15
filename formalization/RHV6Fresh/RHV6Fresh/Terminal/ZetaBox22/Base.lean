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
namespace H22

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

lemma pwl_2_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.8052451659746:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.8052451659747 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.7545822137967:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.7545822137968 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_17_32 (σ : ℝ) (h : σ ≤ (17:ℕ) / (32:ℕ)) : (0.6919549409819:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_17_32 (σ : ℝ) (h : (17:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.691954940982 :=
  pwq_hi _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_2_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.6771277734684:ℝ) ≤ ((2:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_2_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((2:ℕ):ℝ) ^ (-σ) ≤ 0.6771277734685 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

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

lemma pwl_3_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.7094137599636:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.7094137599637 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.6399845508149:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.639984550815 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_17_32 (σ : ℝ) (h : σ ≤ (17:ℕ) / (32:ℕ)) : (0.5578652806066:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_17_32 (σ : ℝ) (h : (17:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.5578652806067 :=
  pwq_hi _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_3_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.5390378907126:ℝ) ≤ ((3:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_3_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((3:ℕ):ℝ) ^ (-σ) ≤ 0.5390378907127 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

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

lemma pwl_4_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.6484197773255:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.6484197773256 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.5693943173783:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.5693943173784 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_17_32 (σ : ℝ) (h : σ ≤ (17:ℕ) / (32:ℕ)) : (0.4788016403492:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_17_32 (σ : ℝ) (h : (17:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.4788016403493 :=
  pwq_hi _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_4_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.4585020216023:ℝ) ≤ ((4:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_4_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((4:ℕ):ℝ) ^ (-σ) ≤ 0.4585020216024 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

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

lemma pwl_5_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.6047444253533:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.6047444253534 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.5200480062655:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.5200480062656 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_17_32 (σ : ℝ) (h : σ ≤ (17:ℕ) / (32:ℕ)) : (0.4252772835227:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_17_32 (σ : ℝ) (h : (17:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.4252772835228 :=
  pwq_hi _ σ 32 17 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_5_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.4044169714435:ℝ) ≤ ((5:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_5_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((5:ℕ):ℝ) ^ (-σ) ≤ 0.4044169714436 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

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

lemma pwl_6_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.5712520008865:ℝ) ≤ ((6:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_6_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((6:ℕ):ℝ) ^ (-σ) ≤ 0.5712520008866 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_6_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.4829209591496:ℝ) ≤ ((6:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_6_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((6:ℕ):ℝ) ^ (-σ) ≤ 0.4829209591497 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_6_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.3649975267533:ℝ) ≤ ((6:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_6_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((6:ℕ):ℝ) ^ (-σ) ≤ 0.3649975267534 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

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

lemma pwl_7_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.5443858929414:ℝ) ≤ ((7:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_7_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((7:ℕ):ℝ) ^ (-σ) ≤ 0.5443858929415 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_7_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.4536061365758:ℝ) ≤ ((7:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_7_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((7:ℕ):ℝ) ^ (-σ) ≤ 0.4536061365759 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_7_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.3346819976142:ℝ) ≤ ((7:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_7_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((7:ℕ):ℝ) ^ (-σ) ≤ 0.3346819976143 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

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

lemma pwl_8_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.5221368912137:ℝ) ≤ ((8:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_8_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((8:ℕ):ℝ) ^ (-σ) ≤ 0.5221368912138 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_8_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.4296548245306:ℝ) ≤ ((8:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_8_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((8:ℕ):ℝ) ^ (-σ) ≤ 0.4296548245307 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_8_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.3104644530183:ℝ) ≤ ((8:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_8_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((8:ℕ):ℝ) ^ (-σ) ≤ 0.3104644530184 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

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

lemma pwl_9_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.5032678828257:ℝ) ≤ ((9:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_9_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((9:ℕ):ℝ) ^ (-σ) ≤ 0.5032678828258 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_9_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.4095802252818:ℝ) ≤ ((9:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_9_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((9:ℕ):ℝ) ^ (-σ) ≤ 0.4095802252819 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_9_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.2905618476239:ℝ) ≤ ((9:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_9_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((9:ℕ):ℝ) ^ (-σ) ≤ 0.290561847624 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

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

lemma pwl_10_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.4869675251658:ℝ) ≤ ((10:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_10_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((10:ℕ):ℝ) ^ (-σ) ≤ 0.4869675251659 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_10_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.3924189758484:ℝ) ≤ ((10:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_10_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((10:ℕ):ℝ) ^ (-σ) ≤ 0.3924189758485 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_10_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.2738419634264:ℝ) ≤ ((10:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_10_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((10:ℕ):ℝ) ^ (-σ) ≤ 0.2738419634265 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

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

lemma pwl_11_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.4726773432914:ℝ) ≤ ((11:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_11_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((11:ℕ):ℝ) ^ (-σ) ≤ 0.4726773432915 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_11_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.3775150080821:ℝ) ≤ ((11:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_11_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((11:ℕ):ℝ) ^ (-σ) ≤ 0.3775150080822 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_11_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.2595473592893:ℝ) ≤ ((11:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_11_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((11:ℕ):ℝ) ^ (-σ) ≤ 0.2595473592894 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_11_24_32 (σ : ℝ) (h : σ ≤ (24:ℕ) / (32:ℕ)) : (0.1655600260761:ℝ) ≤ ((11:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_11_24_32 (σ : ℝ) (h : (24:ℕ) / (32:ℕ) ≤ σ) : ((11:ℕ):ℝ) ^ (-σ) ≤ 0.1655600260762 :=
  pwq_hi _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

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

lemma pwl_12_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.4599979122672:ℝ) ≤ ((12:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_12_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((12:ℕ):ℝ) ^ (-σ) ≤ 0.4599979122673 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_12_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.3644035664439:ℝ) ≤ ((12:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_12_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((12:ℕ):ℝ) ^ (-σ) ≤ 0.364403566444 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_12_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.2471499626119:ℝ) ≤ ((12:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_12_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((12:ℕ):ℝ) ^ (-σ) ≤ 0.247149962612 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_12_24_32 (σ : ℝ) (h : σ ≤ (24:ℕ) / (32:ℕ)) : (0.1551008098503:ℝ) ≤ ((12:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_12_24_32 (σ : ℝ) (h : (24:ℕ) / (32:ℕ) ≤ σ) : ((12:ℕ):ℝ) ^ (-σ) ≤ 0.1551008098504 :=
  pwq_hi _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

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

lemma pwl_13_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.4486345357637:ℝ) ≤ ((13:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_13_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((13:ℕ):ℝ) ^ (-σ) ≤ 0.4486345357638 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_13_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.3527447129451:ℝ) ≤ ((13:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_13_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((13:ℕ):ℝ) ^ (-σ) ≤ 0.3527447129452 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_13_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.2362690659165:ℝ) ≤ ((13:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_13_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((13:ℕ):ℝ) ^ (-σ) ≤ 0.2362690659166 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_13_24_32 (σ : ℝ) (h : σ ≤ (24:ℕ) / (32:ℕ)) : (0.1460637632396:ℝ) ≤ ((13:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_13_24_32 (σ : ℝ) (h : (24:ℕ) / (32:ℕ) ≤ σ) : ((13:ℕ):ℝ) ^ (-σ) ≤ 0.1460637632397 :=
  pwq_hi _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

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

lemma pwl_14_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.4383641087158:ℝ) ≤ ((14:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_14_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((14:ℕ):ℝ) ^ (-σ) ≤ 0.4383641087159 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_14_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.3422831227291:ℝ) ≤ ((14:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_14_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((14:ℕ):ℝ) ^ (-σ) ≤ 0.3422831227292 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_14_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.2266224758644:ℝ) ≤ ((14:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_14_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((14:ℕ):ℝ) ^ (-σ) ≤ 0.2266224758645 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_14_24_32 (σ : ℝ) (h : σ ≤ (24:ℕ) / (32:ℕ)) : (0.1381668871619:ℝ) ≤ ((14:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_14_24_32 (σ : ℝ) (h : (24:ℕ) / (32:ℕ) ≤ σ) : ((14:ℕ):ℝ) ^ (-σ) ≤ 0.138166887162 :=
  pwq_hi _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

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

lemma pwl_15_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.4290140166069:ℝ) ≤ ((15:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_15_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((15:ℕ):ℝ) ^ (-σ) ≤ 0.429014016607 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_15_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.332822689692:ℝ) ≤ ((15:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_15_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((15:ℕ):ℝ) ^ (-σ) ≤ 0.3328226896921 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_15_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.2179960712553:ℝ) ≤ ((15:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_15_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((15:ℕ):ℝ) ^ (-σ) ≤ 0.2179960712554 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_15_24_32 (σ : ℝ) (h : σ ≤ (24:ℕ) / (32:ℕ)) : (0.1311993114176:ℝ) ≤ ((15:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_15_24_32 (σ : ℝ) (h : (24:ℕ) / (32:ℕ) ≤ σ) : ((15:ℕ):ℝ) ^ (-σ) ≤ 0.1311993114177 :=
  pwq_hi _ σ 32 24 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_16_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.5:ℝ) ≤ ((16:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_16_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((16:ℕ):ℝ) ^ (-σ) ≤ 0.5 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_16_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.125:ℝ) ≤ ((16:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_16_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((16:ℕ):ℝ) ^ (-σ) ≤ 0.125 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_16_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.5:ℝ) ≤ ((16:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_16_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((16:ℕ):ℝ) ^ (-σ) ≤ 0.5 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_16_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.4204482076268:ℝ) ≤ ((16:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_16_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((16:ℕ):ℝ) ^ (-σ) ≤ 0.4204482076269 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_16_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.3242098886627:ℝ) ≤ ((16:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_16_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((16:ℕ):ℝ) ^ (-σ) ≤ 0.3242098886628 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_16_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.2102241038134:ℝ) ≤ ((16:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_16_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((16:ℕ):ℝ) ^ (-σ) ≤ 0.2102241038135 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_17_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4924790605054:ℝ) ≤ ((17:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_17_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((17:ℕ):ℝ) ^ (-σ) ≤ 0.4924790605055 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_17_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.1194437167569:ℝ) ≤ ((17:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_17_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((17:ℕ):ℝ) ^ (-σ) ≤ 0.119443716757 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_17_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.4924790605054:ℝ) ≤ ((17:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_17_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((17:ℕ):ℝ) ^ (-σ) ≤ 0.4924790605055 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_17_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.4125577141029:ℝ) ≤ ((17:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_17_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((17:ℕ):ℝ) ^ (-σ) ≤ 0.412557714103 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_17_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.3163225301073:ℝ) ≤ ((17:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_17_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((17:ℕ):ℝ) ^ (-σ) ≤ 0.3163225301074 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_17_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.2031760354456:ℝ) ≤ ((17:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_17_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((17:ℕ):ℝ) ^ (-σ) ≤ 0.2031760354457 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_18_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4854917717073:ℝ) ≤ ((18:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_18_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((18:ℕ):ℝ) ^ (-σ) ≤ 0.4854917717074 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_18_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.1144315079948:ℝ) ≤ ((18:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_18_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((18:ℕ):ℝ) ^ (-σ) ≤ 0.1144315079949 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_18_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.4854917717073:ℝ) ≤ ((18:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_18_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((18:ℕ):ℝ) ^ (-σ) ≤ 0.4854917717074 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_18_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.4052540298356:ℝ) ≤ ((18:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_18_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((18:ℕ):ℝ) ^ (-σ) ≤ 0.4052540298357 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_18_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.3090619531205:ℝ) ≤ ((18:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_18_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((18:ℕ):ℝ) ^ (-σ) ≤ 0.3090619531206 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_18_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.1967474969364:ℝ) ≤ ((18:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_18_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((18:ℕ):ℝ) ^ (-σ) ≤ 0.1967474969365 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_19_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4789736254435:ℝ) ≤ ((19:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_19_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((19:ℕ):ℝ) ^ (-σ) ≤ 0.4789736254436 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_19_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.1098840857857:ℝ) ≤ ((19:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_19_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((19:ℕ):ℝ) ^ (-σ) ≤ 0.1098840857858 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_19_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.4789736254435:ℝ) ≤ ((19:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_19_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((19:ℕ):ℝ) ^ (-σ) ≤ 0.4789736254436 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_19_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.3984643755977:ℝ) ≤ ((19:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_19_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((19:ℕ):ℝ) ^ (-σ) ≤ 0.3984643755978 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_19_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.3023474774973:ℝ) ≤ ((19:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_19_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((19:ℕ):ℝ) ^ (-σ) ≤ 0.3023474774974 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_19_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.1908539265901:ℝ) ≤ ((19:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_19_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((19:ℕ):ℝ) ^ (-σ) ≤ 0.1908539265902 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_20_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4728708045015:ℝ) ≤ ((20:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_20_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((20:ℕ):ℝ) ^ (-σ) ≤ 0.4728708045016 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_20_3_4 (σ : ℝ) (h : σ ≤ (3:ℕ) / (4:ℕ)) : (0.105737126344:ℝ) ≤ ((20:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_20_3_4 (σ : ℝ) (h : (3:ℕ) / (4:ℕ) ≤ σ) : ((20:ℕ):ℝ) ^ (-σ) ≤ 0.1057371263441 :=
  pwq_hi _ σ 4 3 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_20_8_32 (σ : ℝ) (h : σ ≤ (8:ℕ) / (32:ℕ)) : (0.4728708045015:ℝ) ≤ ((20:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_20_8_32 (σ : ℝ) (h : (8:ℕ) / (32:ℕ) ≤ σ) : ((20:ℕ):ℝ) ^ (-σ) ≤ 0.4728708045016 :=
  pwq_hi _ σ 32 8 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_20_10_32 (σ : ℝ) (h : σ ≤ (10:ℕ) / (32:ℕ)) : (0.3921282456264:ℝ) ≤ ((20:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_20_10_32 (σ : ℝ) (h : (10:ℕ) / (32:ℕ) ≤ σ) : ((20:ℕ):ℝ) ^ (-σ) ≤ 0.3921282456265 :=
  pwq_hi _ σ 32 10 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_20_13_32 (σ : ℝ) (h : σ ≤ (13:ℕ) / (32:ℕ)) : (0.2961123795315:ℝ) ≤ ((20:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_20_13_32 (σ : ℝ) (h : (13:ℕ) / (32:ℕ) ≤ σ) : ((20:ℕ):ℝ) ^ (-σ) ≤ 0.2961123795316 :=
  pwq_hi _ σ 32 13 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_20_18_32 (σ : ℝ) (h : σ ≤ (18:ℕ) / (32:ℕ)) : (0.1854259989771:ℝ) ≤ ((20:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_20_18_32 (σ : ℝ) (h : (18:ℕ) / (32:ℕ) ≤ σ) : ((20:ℕ):ℝ) ^ (-σ) ≤ 0.1854259989772 :=
  pwq_hi _ σ 32 18 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_21_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4671379777282:ℝ) ≤ ((21:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_21_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((21:ℕ):ℝ) ^ (-σ) ≤ 0.4671379777283 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_22_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4617366309441:ℝ) ≤ ((22:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_22_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((22:ℕ):ℝ) ^ (-σ) ≤ 0.4617366309442 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_23_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4566337854967:ℝ) ≤ ((23:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_23_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((23:ℕ):ℝ) ^ (-σ) ≤ 0.4566337854968 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_24_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4518010018049:ℝ) ≤ ((24:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_24_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((24:ℕ):ℝ) ^ (-σ) ≤ 0.451801001805 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_25_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4472135954999:ℝ) ≤ ((25:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_25_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((25:ℕ):ℝ) ^ (-σ) ≤ 0.4472135955 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_26_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4428500142691:ℝ) ≤ ((26:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_26_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((26:ℕ):ℝ) ^ (-σ) ≤ 0.4428500142692 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_27_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4386913376508:ℝ) ≤ ((27:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_27_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((27:ℕ):ℝ) ^ (-σ) ≤ 0.4386913376509 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_28_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4347208719449:ℝ) ≤ ((28:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_28_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((28:ℕ):ℝ) ^ (-σ) ≤ 0.434720871945 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_29_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4309238194589:ℝ) ≤ ((29:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_29_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((29:ℕ):ℝ) ^ (-σ) ≤ 0.430923819459 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

lemma pwl_30_1_4 (σ : ℝ) (h : σ ≤ (1:ℕ) / (4:ℕ)) : (0.4272870063962:ℝ) ≤ ((30:ℕ):ℝ) ^ (-σ) :=
  pwq_lo _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)
lemma pwh_30_1_4 (σ : ℝ) (h : (1:ℕ) / (4:ℕ) ≤ σ) : ((30:ℕ):ℝ) ^ (-σ) ≤ 0.4272870063963 :=
  pwq_hi _ σ 4 1 (by norm_num) (by norm_num) h _ (by norm_num) (by norm_num)

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

lemma u1_top (x : ℝ) : 0 < (I ^ (-3 : ℤ) * (1 - ((x : ℂ) + ((22 : ℝ) : ℂ) * I))).re := by
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

lemma cs_h22_2 : ‖exp (-((((22:ℝ) * Real.log ((2:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.8966176905623):ℝ):ℂ) + (((-0.4428055068064):ℝ):ℂ) * I)‖ ≤ 0.00000014777 := by
  have hl := lg_2
  refine (ecis_approx ((22:ℝ) * Real.log ((2:ℕ):ℝ)) (2) 12.56637061435917295384 12.56637061435917295388 15.2492379666 15.2492379776 (-2.6828674) 0.00000004776 (-0.8966176905623) (-0.4428055068064) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_3 : ‖exp (-((((22:ℝ) * Real.log ((3:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.5708374291683:ℝ):ℂ) + ((0.8210631093044:ℝ):ℂ) * I)‖ ≤ 0.00000012728 := by
  have hl := lg_3
  refine (ecis_approx ((22:ℝ) * Real.log ((3:ℕ):ℝ)) (4) 25.13274122871834590768 25.13274122871834590776 24.169470344979608 24.16947035597963 0.9632709 0.00000002727 0.5708374291683 0.8210631093044 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_4 : ‖exp (-((((22:ℝ) * Real.log ((4:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.6078464924715:ℝ):ℂ) + ((0.7940545583208:ℝ):ℂ) * I)‖ ≤ 0.00000011932 := by
  have hl := lg_4
  refine (ecis_approx ((22:ℝ) * Real.log ((4:ℕ):ℝ)) (5) 31.4159265358979323846 31.4159265358979323847 30.4984759332 30.4984759552 0.9174506 0.00000001931 0.6078464924715 0.7940545583208 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_5 : ‖exp (-((((22:ℝ) * Real.log ((5:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.6598968542787):ℝ):ℂ) + ((0.7513562016082:ℝ):ℂ) * I)‖ ≤ 0.00000014105 := by
  have hl := lg_5
  refine (ecis_approx ((22:ℝ) * Real.log ((5:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 35.407634062112598 35.40763408411262 2.2914778 0.00000004104 (-0.6598968542787) 0.7513562016082 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_6 : ‖exp (-((((22:ℝ) * Real.log ((6:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1482516711606):ℝ):ℂ) + (((-0.9889496660586):ℝ):ℂ) * I)‖ ≤ 0.00000013151 := by
  have hl := lg_6
  refine (ecis_approx ((22:ℝ) * Real.log ((6:ℕ):ℝ)) (6) 37.69911184307751886152 37.69911184307751886164 39.418708311579608 39.41870833357963 (-1.7195965) 0.0000000315 (-0.1482516711606) (-0.9889496660586) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_7 : ‖exp (-((((22:ℝ) * Real.log ((7:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.3880569826655:ℝ):ℂ) + ((0.9216353824613:ℝ):ℂ) * I)‖ ≤ 0.00000013954 := by
  have hl := lg_7
  refine (ecis_approx ((22:ℝ) * Real.log ((7:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 42.810023267779284 42.810023289779328 1.1722739 0.00000003953 0.3880569826655 0.9216353824613 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_8 : ‖exp (-((((22:ℝ) * Real.log ((8:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.1933941871387):ℝ):ℂ) + (((-0.981121138484):ℝ):ℂ) * I)‖ ≤ 0.00000015047 := by
  have hl := lg_8
  refine (ecis_approx ((22:ℝ) * Real.log ((8:ℕ):ℝ)) (7) 43.98229715025710533844 43.98229715025710533858 45.7477138998 45.7477139328 (-1.7654168) 0.00000005046 (-0.1933941871387) (-0.981121138484) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_9 : ‖exp (-((((22:ℝ) * Real.log ((9:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3482892589212):ℝ):ℂ) + ((0.9373871089991:ℝ):ℂ) * I)‖ ≤ 0.00000015454 := by
  have hl := lg_9
  refine (ecis_approx ((22:ℝ) * Real.log ((9:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 48.338940689959216 48.33894071195926 1.9265418 0.00000005453 (-0.3482892589212) 0.9373871089991 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_10 : ‖exp (-((((22:ℝ) * Real.log ((10:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9243798572116:ℝ):ℂ) + (((-0.3814733012695):ℝ):ℂ) * I)‖ ≤ 0.00000012874 := by
  have hl := lg_10
  refine (ecis_approx ((22:ℝ) * Real.log ((10:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 50.656872028712598 50.65687206171262 (-0.3913896) 0.00000002873 0.9243798572116 (-0.3814733012695) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_11 : ‖exp (-((((22:ℝ) * Real.log ((11:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.7940342395077):ℝ):ℂ) + (((-0.6078730348044):ℝ):ℂ) * I)‖ ≤ 0.00000015999 := by
  have hl := lg_11
  refine (ecis_approx ((22:ℝ) * Real.log ((11:ℕ):ℝ)) (8) 50.26548245743669181536 50.26548245743669181552 52.753695984407726 52.75369601740777 (-2.4882135) 0.00000005998 (-0.7940342395077) (-0.6078730348044) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_12 : ‖exp (-((((22:ℝ) * Real.log ((12:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3049873755209):ℝ):ℂ) + ((0.9523563937787:ℝ):ℂ) * I)‖ ≤ 0.00000014658 := by
  have hl := lg_12
  refine (ecis_approx ((22:ℝ) * Real.log ((12:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 54.667946278179608 54.66794631117963 1.8807215 0.00000004657 (-0.3049873755209) 0.9523563937787 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_13 : ‖exp (-((((22:ℝ) * Real.log ((13:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.9928347214733:ℝ):ℂ) + ((0.1194956728799:ℝ):ℂ) * I)‖ ≤ 0.00000011763 := by
  have hl := lg_13
  refine (ecis_approx ((22:ℝ) * Real.log ((13:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 56.4288858469974 56.428885879997444 0.1197819 0.00000001762 0.9928347214733 0.1194956728799 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_14 : ‖exp (-((((22:ℝ) * Real.log ((14:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.0601664670608:ℝ):ℂ) + (((-0.9981883570956):ℝ):ℂ) * I)‖ ≤ 0.00000013025 := by
  have hl := lg_14
  refine (ecis_approx ((22:ℝ) * Real.log ((14:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 58.059261234379284 58.059261267379328 (-1.5105935) 0.00000003024 0.0601664670608 (-0.9981883570956) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_15 : ‖exp (-((((22:ℝ) * Real.log ((15:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.993604693187):ℝ):ℂ) + (((-0.1129146280329):ℝ):ℂ) * I)‖ ≤ 0.00000015754 := by
  have hl := lg_15
  refine (ecis_approx ((22:ℝ) * Real.log ((15:ℕ):ℝ)) (9) 56.54866776461627829228 56.54866776461627829246 59.577104407092206 59.57710444009225 (-3.0284367) 0.00000005753 (-0.993604693187) (-0.1129146280329) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_16 : ‖exp (-((((22:ℝ) * Real.log ((16:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.2610452831803):ℝ):ℂ) + ((0.9653265562119:ℝ):ℂ) * I)‖ ≤ 0.00000013862 := by
  have hl := lg_16
  refine (ecis_approx ((22:ℝ) * Real.log ((16:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 60.9969518664 60.9969519104 1.8349012 0.00000003861 (-0.2610452831803) 0.9653265562119 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_17 : ‖exp (-((((22:ℝ) * Real.log ((17:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.8770260781743:ℝ):ℂ) + ((0.4804427730772:ℝ):ℂ) * I)‖ ≤ 0.00000012545 := by
  have hl := lg_17
  refine (ecis_approx ((22:ℝ) * Real.log ((17:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 62.330693546361548 62.33069359036157 0.5011595 0.00000002544 0.8770260781743 0.4804427730772 ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_18 : ‖exp (-((((22:ℝ) * Real.log ((18:ℕ):ℝ) : ℝ) : ℂ) * I)) - (((0.7273624849247:ℝ):ℂ) + (((-0.6862534630326):ℝ):ℂ) * I)‖ ≤ 0.00000011778 := by
  have hl := lg_18
  refine (ecis_approx ((22:ℝ) * Real.log ((18:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 63.588178656559216 63.58817868955926 (-0.7563256) 0.00000001777 0.7273624849247 (-0.6862534630326) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_19 : ‖exp (-((((22:ℝ) * Real.log ((19:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.3662801343036):ℝ):ℂ) + (((-0.9305046282593):ℝ):ℂ) * I)‖ ≤ 0.00000014731 := by
  have hl := lg_19
  refine (ecis_approx ((22:ℝ) * Real.log ((19:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 64.777657524505266 64.777657557505332 (-1.9458045) 0.0000000473 (-0.3662801343036) (-0.9305046282593) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

lemma cs_h22_20 : ‖exp (-((((22:ℝ) * Real.log ((20:ℕ):ℝ) : ℝ) : ℂ) * I)) - ((((-0.9977338043496):ℝ):ℂ) + (((-0.0672848803277):ℝ):ℂ) * I)‖ ≤ 0.00000016753 := by
  have hl := lg_20
  refine (ecis_approx ((22:ℝ) * Real.log ((20:ℕ):ℝ)) (10) 62.8318530717958647692 62.8318530717958647694 65.906109995312598 65.90611003931262 (-3.0742569) 0.00000006752 (-0.9977338043496) (-0.0672848803277) ?_ ?_ (by norm_num) (by norm_num) (by norm_num [abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le]) (by norm_num [EM10.tC1, EM10.tS1, abs_le])).trans (by norm_num)
  · have hp1 := Real.pi_gt_d20
    have hp2 := Real.pi_lt_d20
    push_cast
    constructor <;> nlinarith
  · constructor <;> nlinarith [hl.1, hl.2]

end H22
end Cert
end ZB
end RHV6Fresh
