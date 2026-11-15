/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.BreakAmplitudeSequence

/-!
# La cassure de la paire au premier partagé, cellules comprises (E450, §19.72, K1, 2026-11-08)

Module isolé (non ajouté à `RHV6Fresh.lean`). Une paire `(β, T)`, `(1−β, T)` au premier partagé `x`. Ce qu'E445 avait
compilé sans facteurs de cellule (`pair_amplitude_eq_price`), écrit ici avec les cellules : les deux membres ont deux
MOTS différents à la même fréquence (décalage `mirrorPhaseShift`), donc deux fractions de cellule au même premier.

* L1 `break_amplitude_exact` : `|v_β(k_β(x))| = x^β e^{−βπ f_β(x)/T}/‖(β,T)‖` (généralise `line_break_amplitude_exact`).
* L2 `mirror_cellFraction` : `f_{1−β}(x) = fract(f_β(x) + mirrorPhaseShift β T/π)` ; `mirror_word_difference_le_one` :
  les deux mots diffèrent d'au plus une cellule en chaque point (`|mirrorPhaseShift| < π`).
* L3 `pair_break_product` : le produit des deux cassures est `x · e^{−π(β f_β + (1−β) f_{1−β})/T}/(‖(β,T)‖‖(1−β,T)‖)`,
  une cassure de type ligne à fraction effective dans `[0,1)` (`pair_effective_fraction_mem`).
* L4 `break_amplitude_bounds`, `pair_break_sum_bounds` : la somme des deux cassures retrouve le prix d'E445 à un facteur
  de cellule `e^{−π/T}` près.
* L5 `pair_break_ratio` : `x^{2β−1} e^{−π(β f_β − (1−β) f_{1−β})/T} ‖(1−β,T)‖/‖(β,T)‖` ; `pair_break_ratio_unbounded` :
  non borné le long de `x → ∞` dès que `β > 1/2`.
* L6 `pair_break_product_on_line` : à `β = 1/2`, L3 redonne le carré de `line_break_amplitude_exact`.

Aucune hypothèse, aucun objet spectral, aucune conclusion sur les OFF : K1 fournit les objets, K2 posera la question.
-/

namespace RHV6Fresh

open Real Filter

theorem break_amplitude_exact {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    |contactRealValue β T (lastContactBefore β T x)| =
      x ^ β * Real.exp (-(β * Real.pi * cellFraction β T x / T)) / ‖(⟨β, T⟩ : ℂ)‖ := by
  rw [abs_contactRealValue hβ, contact_of_fraction hT hx, Real.mul_rpow hx.le (Real.exp_pos _).le,
    ← Real.exp_mul]
  congr 3
  ring

theorem mirror_cellFraction (β T x : ℝ) :
    cellFraction (1 - β) T x = Int.fract (cellFraction β T x + mirrorPhaseShift β T / Real.pi) := by
  have h := mirror_stagePosition_difference β T x
  rw [neg_div] at h
  have h2 : stagePosition (1 - β) T x = stagePosition β T x + mirrorPhaseShift β T / Real.pi := by
    linarith
  rw [show cellFraction (1 - β) T x = Int.fract (stagePosition (1 - β) T x) from rfl, h2,
    stagePosition_eq_last_add_fraction β T x, add_assoc, Int.fract_intCast_add]

theorem abs_mirrorPhaseShift_lt_pi (β T : ℝ) : |mirrorPhaseShift β T| < Real.pi := by
  unfold mirrorPhaseShift
  have h1 := Real.arctan_lt_pi_div_two (T / β)
  have h2 := Real.neg_pi_div_two_lt_arctan (T / β)
  have h3 := Real.arctan_lt_pi_div_two (T / (1 - β))
  have h4 := Real.neg_pi_div_two_lt_arctan (T / (1 - β))
  rw [abs_lt]
  constructor <;> linarith

theorem floor_sub_floor_le_one_of_abs_sub_le {a b : ℝ} (h : |a - b| ≤ 1) : |⌊a⌋ - ⌊b⌋| ≤ 1 := by
  rw [abs_le] at h
  have h1 : ⌊b⌋ ≤ ⌊a⌋ + 1 := by
    rw [← Int.floor_add_one]
    exact Int.floor_mono (by linarith)
  have h2 : ⌊a⌋ ≤ ⌊b⌋ + 1 := by
    rw [← Int.floor_add_one]
    exact Int.floor_mono (by linarith)
  rw [abs_le]
  omega

theorem mirror_word_difference_le_one (β T x : ℝ) :
    |lastContactBefore (1 - β) T x - lastContactBefore β T x| ≤ 1 := by
  unfold lastContactBefore
  apply floor_sub_floor_le_one_of_abs_sub_le
  have h := mirror_stagePosition_difference β T x
  rw [neg_div] at h
  have h2 : stagePosition (1 - β) T x - stagePosition β T x = mirrorPhaseShift β T / Real.pi := by
    linarith
  rw [h2, abs_div, abs_of_pos Real.pi_pos, div_le_one Real.pi_pos]
  exact (abs_mirrorPhaseShift_lt_pi β T).le

theorem pair_break_product {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    |contactRealValue β T (lastContactBefore β T x)| *
        |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| =
      x * Real.exp (-(Real.pi * (β * cellFraction β T x + (1 - β) * cellFraction (1 - β) T x) / T)) /
        (‖(⟨β, T⟩ : ℂ)‖ * ‖(⟨1 - β, T⟩ : ℂ)‖) := by
  rw [break_amplitude_exact hβ hT hx, break_amplitude_exact (by linarith : 0 < 1 - β) hT hx]
  have hx1 : x ^ β * x ^ (1 - β) = x := by
    rw [← Real.rpow_add hx]; simp
  rw [div_mul_div_comm]
  congr 1
  rw [mul_mul_mul_comm, hx1, ← Real.exp_add]
  congr 2
  ring

theorem pair_effective_fraction_mem {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (T x : ℝ) :
    0 ≤ β * cellFraction β T x + (1 - β) * cellFraction (1 - β) T x ∧
      β * cellFraction β T x + (1 - β) * cellFraction (1 - β) T x < 1 := by
  have hf0 := cellFraction_nonneg β T x
  have hf1 := cellFraction_lt_one β T x
  have hf0' := cellFraction_nonneg (1 - β) T x
  have hf1' := cellFraction_lt_one (1 - β) T x
  have hb : 0 ≤ 1 - β := by linarith
  constructor
  · nlinarith
  · nlinarith [mul_lt_mul_of_pos_left hf1 hβ, mul_le_mul_of_nonneg_left hf1'.le hb]

theorem break_amplitude_bounds {β T : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    Real.exp (-(Real.pi / T)) * (x ^ β / ‖(⟨β, T⟩ : ℂ)‖) ≤
        |contactRealValue β T (lastContactBefore β T x)| ∧
      |contactRealValue β T (lastContactBefore β T x)| ≤ x ^ β / ‖(⟨β, T⟩ : ℂ)‖ := by
  rw [break_amplitude_exact hβ hT hx]
  have hn := norm_mk_pos (T := T) hβ
  have hxb : 0 < x ^ β := Real.rpow_pos_of_pos hx β
  have hf0 := cellFraction_nonneg β T x
  have hf1 := cellFraction_lt_one β T x
  have hbf : β * cellFraction β T x ≤ 1 := by nlinarith
  constructor
  · have e : Real.exp (-(Real.pi / T)) * (x ^ β / ‖(⟨β, T⟩ : ℂ)‖) =
        x ^ β * Real.exp (-(Real.pi / T)) / ‖(⟨β, T⟩ : ℂ)‖ := by ring
    rw [e]
    apply div_le_div_of_nonneg_right _ hn.le
    apply mul_le_mul_of_nonneg_left _ hxb.le
    apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff, div_le_div_iff_of_pos_right hT]
    calc β * Real.pi * cellFraction β T x = Real.pi * (β * cellFraction β T x) := by ring
      _ ≤ Real.pi * 1 := mul_le_mul_of_nonneg_left hbf Real.pi_pos.le
      _ = Real.pi := mul_one _
  · apply div_le_div_of_nonneg_right _ hn.le
    have : Real.exp (-(β * Real.pi * cellFraction β T x / T)) ≤ 1 := by
      calc Real.exp (-(β * Real.pi * cellFraction β T x / T)) ≤ Real.exp 0 := by
            apply Real.exp_le_exp.mpr
            apply neg_nonpos.mpr
            positivity
        _ = 1 := Real.exp_zero
    calc x ^ β * Real.exp (-(β * Real.pi * cellFraction β T x / T)) ≤ x ^ β * 1 :=
          mul_le_mul_of_nonneg_left this hxb.le
      _ = x ^ β := mul_one _

theorem pair_break_sum_bounds {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    Real.exp (-(Real.pi / T)) * (x ^ β / ‖(⟨β, T⟩ : ℂ)‖ + x ^ (1 - β) / ‖(⟨1 - β, T⟩ : ℂ)‖) ≤
        |contactRealValue β T (lastContactBefore β T x)| +
          |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| ∧
      |contactRealValue β T (lastContactBefore β T x)| +
          |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| ≤
        x ^ β / ‖(⟨β, T⟩ : ℂ)‖ + x ^ (1 - β) / ‖(⟨1 - β, T⟩ : ℂ)‖ := by
  have h1 := break_amplitude_bounds hβ hβ1.le hT hx
  have h2 := break_amplitude_bounds (by linarith : 0 < 1 - β) (by linarith) hT hx
  constructor
  · rw [mul_add]; exact add_le_add h1.1 h2.1
  · exact add_le_add h1.2 h2.2

theorem pair_break_ratio {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    |contactRealValue β T (lastContactBefore β T x)| /
        |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| =
      x ^ (2 * β - 1) *
        Real.exp (-(Real.pi * (β * cellFraction β T x - (1 - β) * cellFraction (1 - β) T x) / T)) *
        (‖(⟨1 - β, T⟩ : ℂ)‖ / ‖(⟨β, T⟩ : ℂ)‖) := by
  rw [break_amplitude_exact hβ hT hx, break_amplitude_exact (by linarith : 0 < 1 - β) hT hx]
  have hn := norm_mk_pos (T := T) hβ
  have hn' := norm_mk_pos (T := T) (by linarith : 0 < 1 - β)
  have hxb := Real.rpow_pos_of_pos hx (1 - β)
  rw [div_eq_iff (by positivity)]
  have hx2 : x ^ (2 * β - 1) * x ^ (1 - β) = x ^ β := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have he : Real.exp (-(Real.pi * (β * cellFraction β T x - (1 - β) * cellFraction (1 - β) T x) / T)) *
      Real.exp (-((1 - β) * Real.pi * cellFraction (1 - β) T x / T)) =
      Real.exp (-(β * Real.pi * cellFraction β T x / T)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc x ^ β * Real.exp (-(β * Real.pi * cellFraction β T x / T)) / ‖(⟨β, T⟩ : ℂ)‖
      = (x ^ (2 * β - 1) * x ^ (1 - β)) *
          (Real.exp (-(Real.pi * (β * cellFraction β T x - (1 - β) * cellFraction (1 - β) T x) / T)) *
            Real.exp (-((1 - β) * Real.pi * cellFraction (1 - β) T x / T))) *
          (‖(⟨1 - β, T⟩ : ℂ)‖ / ‖(⟨β, T⟩ : ℂ)‖ / ‖(⟨1 - β, T⟩ : ℂ)‖) := by
        rw [hx2, he]; field_simp
    _ = _ := by ring

theorem pair_break_ratio_unbounded {β T : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) (hT : 0 < T) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, K < |contactRealValue β T (lastContactBefore β T x)| /
        |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| := by
  have hβ0 : 0 < β := by linarith
  have hn := norm_mk_pos (T := T) hβ0
  have hn' := norm_mk_pos (T := T) (by linarith : 0 < 1 - β)
  have hcpos : 0 < Real.exp (-(Real.pi / T)) * (‖(⟨1 - β, T⟩ : ℂ)‖ / ‖(⟨β, T⟩ : ℂ)‖) := by positivity
  have hlim : Tendsto (fun x : ℝ => x ^ (2 * β - 1) *
      (Real.exp (-(Real.pi / T)) * (‖(⟨1 - β, T⟩ : ℂ)‖ / ‖(⟨β, T⟩ : ℂ)‖))) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).atTop_mul_const hcpos
  filter_upwards [hlim.eventually_gt_atTop K, eventually_gt_atTop (0 : ℝ)] with x hK hx
  rw [pair_break_ratio hβ0 hβ1 hT hx]
  have hf0 := cellFraction_nonneg β T x
  have hf1 := cellFraction_lt_one β T x
  have hf0' := cellFraction_nonneg (1 - β) T x
  have hf1' := cellFraction_lt_one (1 - β) T x
  have hbf : β * cellFraction β T x - (1 - β) * cellFraction (1 - β) T x ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - β) hf0', mul_lt_mul_of_pos_left hf1 hβ0]
  have hexp : Real.exp (-(Real.pi / T)) ≤
      Real.exp (-(Real.pi * (β * cellFraction β T x - (1 - β) * cellFraction (1 - β) T x) / T)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff, div_le_div_iff_of_pos_right hT]
    calc Real.pi * (β * cellFraction β T x - (1 - β) * cellFraction (1 - β) T x) ≤ Real.pi * 1 :=
          mul_le_mul_of_nonneg_left hbf Real.pi_pos.le
      _ = Real.pi := mul_one _
  have hxp : 0 ≤ x ^ (2 * β - 1) := (Real.rpow_pos_of_pos hx _).le
  calc K < x ^ (2 * β - 1) * (Real.exp (-(Real.pi / T)) * (‖(⟨1 - β, T⟩ : ℂ)‖ / ‖(⟨β, T⟩ : ℂ)‖)) := hK
    _ = x ^ (2 * β - 1) * Real.exp (-(Real.pi / T)) * (‖(⟨1 - β, T⟩ : ℂ)‖ / ‖(⟨β, T⟩ : ℂ)‖) := by ring
    _ ≤ x ^ (2 * β - 1) *
        Real.exp (-(Real.pi * (β * cellFraction β T x - (1 - β) * cellFraction (1 - β) T x) / T)) *
        (‖(⟨1 - β, T⟩ : ℂ)‖ / ‖(⟨β, T⟩ : ℂ)‖) := by gcongr

theorem pair_break_product_on_line {T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x)| ^ 2 =
      x * Real.exp (-(Real.pi * cellFraction (1 / 2) T x / T)) / ‖(⟨1 / 2, T⟩ : ℂ)‖ ^ 2 := by
  have h := pair_break_product (β := 1 / 2) (by norm_num) (by norm_num) hT hx
  have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [e] at h
  rw [sq, h, sq]
  congr 3
  ring

#print axioms break_amplitude_exact
#print axioms mirror_cellFraction
#print axioms mirror_word_difference_le_one
#print axioms pair_break_product
#print axioms pair_break_sum_bounds
#print axioms pair_break_ratio
#print axioms pair_break_ratio_unbounded
#print axioms pair_break_product_on_line

end RHV6Fresh
