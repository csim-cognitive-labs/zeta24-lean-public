/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaQuantitativeGoodHeightsP4_4b
import RHV3Lean.Objects.P4Port.NumberTheory.LSeries.RiemannZetaHadamard
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# P4.4c: horizontal logarithmic-derivative bounds

This module begins the quantitative horizontal selection layer needed for P4.4c.
The finite-grid lemmas in this section keep multiplicities by working over the
original finite index set rather than over an image of heights.
-/

open Complex Set Finset BigOperators
open scoped Topology ComplexConjugate

noncomputable section

namespace RHV3Lean

namespace P4_4c

/-! ## Discrete harmonic rearrangement -/

lemma fin_orderIso_positive_nat_bound
    (s : Finset ℕ) (hpos : ∀ k ∈ s, 1 ≤ k) :
    let e := Finset.orderIsoOfFin s rfl
    ∀ i : Fin s.card, (i : ℕ) + 1 ≤ ((e i : s) : ℕ) := by
  classical
  intro e i
  obtain ⟨n, hn⟩ := i
  dsimp only at hn ⊢
  induction n with
  | zero =>
      exact hpos (((e ⟨0, hn⟩ : s) : ℕ)) (e ⟨0, hn⟩).property
  | succ n ih =>
      have hnprev : n < s.card := lt_trans (Nat.lt_succ_self n) hn
      have hprev := ih hnprev
      have hfinlt : (⟨n, hnprev⟩ : Fin s.card) < ⟨n + 1, hn⟩ := by
        exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self n)
      have hlt_sub :
          e (⟨n, hnprev⟩ : Fin s.card) < e ⟨n + 1, hn⟩ :=
        e.strictMono hfinlt
      have hlt_nat :
          ((e (⟨n, hnprev⟩ : Fin s.card) : s) : ℕ) <
            ((e ⟨n + 1, hn⟩ : s) : ℕ) := hlt_sub
      omega

lemma inv_orderIso_le_inv_succ
    (s : Finset ℕ) (hpos : ∀ k ∈ s, 1 ≤ k)
    (i : Fin s.card) :
    1 / ((((Finset.orderIsoOfFin s rfl) i : s) : ℕ) : ℝ) ≤
      1 / (((i : ℕ) + 1 : ℕ) : ℝ) := by
  have hb := fin_orderIso_positive_nat_bound s hpos i
  have hdenpos : 0 < (((i : ℕ) + 1 : ℕ) : ℝ) := by positivity
  apply one_div_le_one_div_of_le hdenpos
  exact_mod_cast hb

lemma sum_inv_natCast_le_harmonic_card
    (s : Finset ℕ) (hpos : ∀ k ∈ s, 1 ≤ k) :
    ∑ k ∈ s, (1 / (k : ℝ)) ≤ (harmonic s.card : ℝ) := by
  classical
  let e := Finset.orderIsoOfFin s rfl
  have hsum_sub :
      ∑ k : s, (1 / ((k : ℕ) : ℝ)) =
        ∑ i : Fin s.card, (1 / (((e i : s) : ℕ) : ℝ)) := by
    exact (Equiv.sum_comp e.toEquiv
      (fun k : s => (1 / ((k : ℕ) : ℝ)))).symm
  calc
    ∑ k ∈ s, (1 / (k : ℝ)) = ∑ k : s, (1 / ((k : ℕ) : ℝ)) := by
      exact (Finset.sum_coe_sort s (fun k : ℕ => (1 / (k : ℝ)))).symm
    _ = ∑ i : Fin s.card, (1 / (((e i : s) : ℕ) : ℝ)) := hsum_sub
    _ ≤ ∑ i : Fin s.card, (1 / (((i : ℕ) + 1 : ℕ) : ℝ)) := by
      exact Finset.sum_le_sum (fun i _ => inv_orderIso_le_inv_succ s hpos i)
    _ = (harmonic s.card : ℝ) := by
      rw [harmonic]
      simp_rw [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      simpa [one_div] using
        (Fin.sum_univ_eq_sum_range
          (fun i : ℕ => (1 / (((i : ℕ) + 1 : ℕ) : ℝ))) s.card)

lemma harmonic_mono_real {m n : ℕ} (h : m ≤ n) :
    (harmonic m : ℝ) ≤ (harmonic n : ℝ) := by
  induction h with
  | refl => rfl
  | @step n _ ih =>
      rw [harmonic_succ]
      norm_num
      have hnonneg : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
      linarith

/-! ## Grid normalization -/

lemma grid_distance_eq_abs_sub_u_div
    {M : ℕ} (hM : M ≠ 0) (H x : ℝ) (j : ℕ) :
    |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x|
      = |(j : ℝ) - ((M : ℝ) * (x - H) - 1 / 2)| / (M : ℝ) := by
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hinside :
      (H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x
        = ((j : ℝ) - ((M : ℝ) * (x - H) - 1 / 2)) / (M : ℝ) := by
    field_simp [hMr]
    ring
  rw [hinside, abs_div, abs_of_pos hMpos]

lemma grid_not_close_abs_sub_u_ge_quarter
    {M : ℕ} (hM : M ≠ 0) (H x : ℝ) (j : ℕ)
    (hnot : ¬ |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x|
      < 1 / (4 * (M : ℝ))) :
    1 / 4 ≤ |(j : ℝ) - ((M : ℝ) * (x - H) - 1 / 2)| := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hdist := grid_distance_eq_abs_sub_u_div (M := M) hM H x j
  have hge :
      1 / (4 * (M : ℝ))
        ≤ |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x| :=
    le_of_not_gt hnot
  rw [hdist] at hge
  have hmul :
      (1 / (4 * (M : ℝ))) * (M : ℝ)
        ≤ |(j : ℝ) - ((M : ℝ) * (x - H) - 1 / 2)| := by
    exact (le_div_iff₀ hMpos).mp hge
  have hcalc : (1 / (4 * (M : ℝ))) * (M : ℝ) = (1 / 4 : ℝ) := by
    field_simp [(ne_of_gt hMpos)]
  calc
    (1 / 4 : ℝ) = (1 / (4 * (M : ℝ))) * (M : ℝ) := hcalc.symm
    _ ≤ |(j : ℝ) - ((M : ℝ) * (x - H) - 1 / 2)| := hmul

lemma grid_not_close_inverse_le_fourM
    {M : ℕ} (hM : M ≠ 0) (H x : ℝ) (j : ℕ)
    (hnot : ¬ |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x|
      < 1 / (4 * (M : ℝ))) :
    1 / |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x|
      ≤ 4 * (M : ℝ) := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hge :
      1 / (4 * (M : ℝ))
        ≤ |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x| :=
    le_of_not_gt hnot
  have hpos : 0 < 1 / (4 * (M : ℝ)) := by positivity
  have h := one_div_le_one_div_of_le hpos hge
  have hEq : 1 / (1 / (4 * (M : ℝ))) = 4 * (M : ℝ) := by
    field_simp [(ne_of_gt hMpos)]
  simpa [hEq] using h

lemma left_far_norm_inv_le (u : ℝ) (j : ℕ)
    (hj : ((j : ℤ) ≤ Int.floor u - 1)) :
    1 / |(j : ℝ) - u| ≤
      1 / ((((Int.floor u - (j : ℤ)).toNat : ℕ) : ℝ)) := by
  have hfloor_le : ((Int.floor u : ℤ) : ℝ) ≤ u := Int.floor_le u
  have hzpos : (0 : ℤ) < Int.floor u - (j : ℤ) := by omega
  have hnatpos :
      0 < (((Int.floor u - (j : ℤ)).toNat : ℕ) : ℝ) := by
    have : 0 < (Int.floor u - (j : ℤ)).toNat := by
      rw [Int.lt_toNat]
      exact hzpos
    exact_mod_cast this
  have hcastInt :
      (((Int.floor u - (j : ℤ)).toNat : ℤ) =
        Int.floor u - (j : ℤ)) := by
    exact Int.toNat_of_nonneg (le_of_lt hzpos)
  have hcast :
      ((((Int.floor u - (j : ℤ)).toNat : ℕ) : ℝ)) =
        ((Int.floor u - (j : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast hcastInt
  have hjleu : ((j : ℕ) : ℝ) ≤ u := by
    have hjfloor : ((j : ℤ) : ℝ) ≤ ((Int.floor u : ℤ) : ℝ) := by
      exact_mod_cast (by omega : (j : ℤ) ≤ Int.floor u)
    exact le_trans hjfloor hfloor_le
  have habs : |(j : ℝ) - u| = u - (j : ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hjleu)]
    ring
  have hdist :
      ((((Int.floor u - (j : ℤ)).toNat : ℕ) : ℝ)) ≤
        |(j : ℝ) - u| := by
    rw [hcast, habs]
    norm_num
    exact hfloor_le
  exact one_div_le_one_div_of_le hnatpos hdist

lemma right_far_norm_inv_le (u : ℝ) (j : ℕ)
    (hj : Int.floor u + 2 ≤ (j : ℤ)) :
    1 / |(j : ℝ) - u| ≤
      1 / (((((j : ℤ) - (Int.floor u + 1)).toNat : ℕ) : ℝ)) := by
  have hult : u < ((Int.floor u : ℤ) : ℝ) + 1 := Int.lt_floor_add_one u
  have hzpos : (0 : ℤ) < (j : ℤ) - (Int.floor u + 1) := by omega
  have hnatpos :
      0 < (((((j : ℤ) - (Int.floor u + 1)).toNat : ℕ) : ℝ)) := by
    have : 0 < ((j : ℤ) - (Int.floor u + 1)).toNat := by
      rw [Int.lt_toNat]
      exact hzpos
    exact_mod_cast this
  have hcastInt :
      ((((j : ℤ) - (Int.floor u + 1)).toNat : ℤ) =
        (j : ℤ) - (Int.floor u + 1)) := by
    exact Int.toNat_of_nonneg (le_of_lt hzpos)
  have hcast :
      (((((j : ℤ) - (Int.floor u + 1)).toNat : ℕ) : ℝ)) =
        (((j : ℤ) - (Int.floor u + 1) : ℤ) : ℝ) := by
    exact_mod_cast hcastInt
  have hulej : u ≤ (j : ℝ) := by
    have hfloorj : ((Int.floor u : ℤ) : ℝ) + 1 ≤ ((j : ℤ) : ℝ) := by
      exact_mod_cast (by omega : Int.floor u + 1 ≤ (j : ℤ))
    exact le_trans (le_of_lt hult) hfloorj
  have habs : |(j : ℝ) - u| = (j : ℝ) - u := by
    rw [abs_of_nonneg]
    linarith
  have hdist :
      (((((j : ℤ) - (Int.floor u + 1)).toNat : ℕ) : ℝ)) ≤
        |(j : ℝ) - u| := by
    rw [hcast, habs]
    norm_num
    linarith
  exact one_div_le_one_div_of_le hnatpos hdist

lemma left_far_norm_sum_le_harmonic (M : ℕ) (u : ℝ) :
    ∑ j ∈ (Finset.range M).filter (fun j : ℕ => ((j : ℤ) ≤ Int.floor u - 1)),
      1 / |(j : ℝ) - u| ≤ (harmonic M : ℝ) := by
  classical
  let L : Finset ℕ :=
    (Finset.range M).filter (fun j : ℕ => ((j : ℤ) ≤ Int.floor u - 1))
  let d : ℕ → ℕ := fun j => (Int.floor u - (j : ℤ)).toNat
  have hinj : Set.InjOn d (L : Set ℕ) := by
    intro a ha b hb h
    have hpa : ((a : ℤ) ≤ Int.floor u - 1) := (Finset.mem_filter.mp ha).2
    have hpb : ((b : ℤ) ≤ Int.floor u - 1) := (Finset.mem_filter.mp hb).2
    have hapos : 0 ≤ Int.floor u - (a : ℤ) := by omega
    have hbpos : 0 ≤ Int.floor u - (b : ℤ) := by omega
    have hcasta : ((d a : ℕ) : ℤ) = Int.floor u - (a : ℤ) := by
      dsimp [d]
      exact Int.toNat_of_nonneg hapos
    have hcastb : ((d b : ℕ) : ℤ) = Int.floor u - (b : ℤ) := by
      dsimp [d]
      exact Int.toNat_of_nonneg hbpos
    have hz : Int.floor u - (a : ℤ) = Int.floor u - (b : ℤ) := by
      rw [← hcasta, ← hcastb, h]
    omega
  have hposd : ∀ k ∈ L.image d, 1 ≤ k := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    have hpj : ((j : ℤ) ≤ Int.floor u - 1) := (Finset.mem_filter.mp hj).2
    dsimp [d]
    have hzpos : (0 : ℤ) < Int.floor u - (j : ℤ) := by omega
    rw [Int.le_toNat]
    · exact hzpos
    · omega
  have hterm :
      ∑ j ∈ L, 1 / |(j : ℝ) - u| ≤ ∑ j ∈ L, 1 / ((d j : ℕ) : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact left_far_norm_inv_le u j (Finset.mem_filter.mp hj).2
  have himage_eq :
      ∑ k ∈ L.image d, 1 / (k : ℝ) = ∑ j ∈ L, 1 / ((d j : ℕ) : ℝ) := by
    exact Finset.sum_image hinj
  have hdist_sum : ∑ j ∈ L, 1 / ((d j : ℕ) : ℝ) ≤
      (harmonic (L.image d).card : ℝ) := by
    rw [← himage_eq]
    exact sum_inv_natCast_le_harmonic_card (L.image d) hposd
  have hcard : (L.image d).card ≤ M := by
    calc
      (L.image d).card = L.card := Finset.card_image_of_injOn hinj
      _ ≤ (Finset.range M).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = M := Finset.card_range M
  calc
    ∑ j ∈ (Finset.range M).filter (fun j : ℕ => ((j : ℤ) ≤ Int.floor u - 1)),
      1 / |(j : ℝ) - u| = ∑ j ∈ L, 1 / |(j : ℝ) - u| := rfl
    _ ≤ ∑ j ∈ L, 1 / ((d j : ℕ) : ℝ) := hterm
    _ ≤ (harmonic (L.image d).card : ℝ) := hdist_sum
    _ ≤ (harmonic M : ℝ) := harmonic_mono_real hcard

lemma right_far_norm_sum_le_harmonic (M : ℕ) (u : ℝ) :
    ∑ j ∈ (Finset.range M).filter (fun j : ℕ => Int.floor u + 2 ≤ (j : ℤ)),
      1 / |(j : ℝ) - u| ≤ (harmonic M : ℝ) := by
  classical
  let R : Finset ℕ :=
    (Finset.range M).filter (fun j : ℕ => Int.floor u + 2 ≤ (j : ℤ))
  let d : ℕ → ℕ := fun j => ((j : ℤ) - (Int.floor u + 1)).toNat
  have hinj : Set.InjOn d (R : Set ℕ) := by
    intro a ha b hb h
    have hpa : Int.floor u + 2 ≤ (a : ℤ) := (Finset.mem_filter.mp ha).2
    have hpb : Int.floor u + 2 ≤ (b : ℤ) := (Finset.mem_filter.mp hb).2
    have hapos : 0 ≤ (a : ℤ) - (Int.floor u + 1) := by omega
    have hbpos : 0 ≤ (b : ℤ) - (Int.floor u + 1) := by omega
    have hcasta : ((d a : ℕ) : ℤ) = (a : ℤ) - (Int.floor u + 1) := by
      dsimp [d]
      exact Int.toNat_of_nonneg hapos
    have hcastb : ((d b : ℕ) : ℤ) = (b : ℤ) - (Int.floor u + 1) := by
      dsimp [d]
      exact Int.toNat_of_nonneg hbpos
    have hz : (a : ℤ) - (Int.floor u + 1) = (b : ℤ) - (Int.floor u + 1) := by
      rw [← hcasta, ← hcastb, h]
    omega
  have hposd : ∀ k ∈ R.image d, 1 ≤ k := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    have hpj : Int.floor u + 2 ≤ (j : ℤ) := (Finset.mem_filter.mp hj).2
    dsimp [d]
    have hzpos : (0 : ℤ) < (j : ℤ) - (Int.floor u + 1) := by omega
    rw [Int.le_toNat]
    · exact hzpos
    · omega
  have hterm :
      ∑ j ∈ R, 1 / |(j : ℝ) - u| ≤ ∑ j ∈ R, 1 / ((d j : ℕ) : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact right_far_norm_inv_le u j (Finset.mem_filter.mp hj).2
  have himage_eq :
      ∑ k ∈ R.image d, 1 / (k : ℝ) = ∑ j ∈ R, 1 / ((d j : ℕ) : ℝ) := by
    exact Finset.sum_image hinj
  have hdist_sum : ∑ j ∈ R, 1 / ((d j : ℕ) : ℝ) ≤
      (harmonic (R.image d).card : ℝ) := by
    rw [← himage_eq]
    exact sum_inv_natCast_le_harmonic_card (R.image d) hposd
  have hcard : (R.image d).card ≤ M := by
    calc
      (R.image d).card = R.card := Finset.card_image_of_injOn hinj
      _ ≤ (Finset.range M).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = M := Finset.card_range M
  calc
    ∑ j ∈ (Finset.range M).filter (fun j : ℕ => Int.floor u + 2 ≤ (j : ℤ)),
      1 / |(j : ℝ) - u| = ∑ j ∈ R, 1 / |(j : ℝ) - u| := rfl
    _ ≤ ∑ j ∈ R, 1 / ((d j : ℕ) : ℝ) := hterm
    _ ≤ (harmonic (R.image d).card : ℝ) := hdist_sum
    _ ≤ (harmonic M : ℝ) := harmonic_mono_real hcard

lemma normalized_grid_inverse_sum_le (M : ℕ) (u : ℝ) :
    ∑ j ∈ Finset.range M,
      (if |(j : ℝ) - u| < ((4 : ℝ)⁻¹) then 0 else |(j : ℝ) - u|⁻¹)
      ≤ 16 * (1 + (harmonic M : ℝ)) := by
  classical
  let near : Finset ℕ :=
    (Finset.range M).filter
      (fun j : ℕ => (j : ℤ) = Int.floor u ∨ (j : ℤ) = Int.floor u + 1)
  have hpoint : ∀ j ∈ Finset.range M,
      (if |(j : ℝ) - u| < ((4 : ℝ)⁻¹) then 0 else |(j : ℝ) - u|⁻¹)
        ≤ (if ((j : ℤ) ≤ Int.floor u - 1) then |(j : ℝ) - u|⁻¹ else 0)
          + (if (Int.floor u + 2 ≤ (j : ℤ)) then |(j : ℝ) - u|⁻¹ else 0)
          + (if ((j : ℤ) = Int.floor u ∨ (j : ℤ) = Int.floor u + 1) then
              (4 : ℝ) else 0) := by
    intro j hj
    by_cases hleft : ((j : ℤ) ≤ Int.floor u - 1)
    · by_cases hclose : |(j : ℝ) - u| < ((4 : ℝ)⁻¹)
      · have hrhs_nonneg :
            0 ≤ (if ((j : ℤ) ≤ Int.floor u - 1) then |(j : ℝ) - u|⁻¹ else 0)
              + (if (Int.floor u + 2 ≤ (j : ℤ)) then |(j : ℝ) - u|⁻¹ else 0)
              + (if ((j : ℤ) = Int.floor u ∨ (j : ℤ) = Int.floor u + 1) then
                  (4 : ℝ) else 0) := by
          split_ifs <;> positivity
        simpa [hclose] using hrhs_nonneg
      · have htail :
            0 ≤ (if (Int.floor u + 2 ≤ (j : ℤ)) then |(j : ℝ) - u|⁻¹ else 0)
              + (if ((j : ℤ) = Int.floor u ∨ (j : ℤ) = Int.floor u + 1) then
                  (4 : ℝ) else 0) := by
          split_ifs <;> positivity
        simpa [hleft, hclose, add_assoc] using
          (le_add_of_nonneg_right htail :
            |(j : ℝ) - u|⁻¹ ≤ |(j : ℝ) - u|⁻¹ +
              ((if (Int.floor u + 2 ≤ (j : ℤ)) then |(j : ℝ) - u|⁻¹ else 0)
              + (if ((j : ℤ) = Int.floor u ∨ (j : ℤ) = Int.floor u + 1) then
                  (4 : ℝ) else 0)))
    · by_cases hright : Int.floor u + 2 ≤ (j : ℤ)
      · by_cases hclose : |(j : ℝ) - u| < ((4 : ℝ)⁻¹)
        · have hrhs_nonneg :
              0 ≤ (if ((j : ℤ) ≤ Int.floor u - 1) then |(j : ℝ) - u|⁻¹ else 0)
                + (if (Int.floor u + 2 ≤ (j : ℤ)) then |(j : ℝ) - u|⁻¹ else 0)
                + (if ((j : ℤ) = Int.floor u ∨ (j : ℤ) = Int.floor u + 1) then
                    (4 : ℝ) else 0) := by
            split_ifs <;> positivity
          simpa [hclose] using hrhs_nonneg
        · have htail :
              0 ≤ (if ((j : ℤ) = Int.floor u ∨ (j : ℤ) = Int.floor u + 1) then
                (4 : ℝ) else 0) := by
            split_ifs <;> positivity
          simpa [hleft, hright, hclose, add_assoc] using
            (le_add_of_nonneg_right htail :
              |(j : ℝ) - u|⁻¹ ≤ |(j : ℝ) - u|⁻¹ +
                (if ((j : ℤ) = Int.floor u ∨ (j : ℤ) = Int.floor u + 1) then
                  (4 : ℝ) else 0))
      · have hnear : (j : ℤ) = Int.floor u ∨ (j : ℤ) = Int.floor u + 1 := by omega
        by_cases hclose : |(j : ℝ) - u| < ((4 : ℝ)⁻¹)
        · simpa [hleft, hright, hnear, hclose]
        · have hge : ((4 : ℝ)⁻¹) ≤ |(j : ℝ) - u| := le_of_not_gt hclose
          have hinv : |(j : ℝ) - u|⁻¹ ≤ (4 : ℝ) := by
            have hpos : (0 : ℝ) < ((4 : ℝ)⁻¹) := by norm_num
            have h := one_div_le_one_div_of_le hpos hge
            norm_num at h
            simpa [one_div] using h
          simpa [hleft, hright, hnear, hclose] using hinv
  have hsum_point := Finset.sum_le_sum hpoint
  have hleftsum :
      ∑ j ∈ Finset.range M,
        (if ((j : ℤ) ≤ Int.floor u - 1) then |(j : ℝ) - u|⁻¹ else 0)
        ≤ (harmonic M : ℝ) := by
    rw [← Finset.sum_filter]
    simpa [one_div] using left_far_norm_sum_le_harmonic M u
  have hrightsum :
      ∑ j ∈ Finset.range M,
        (if (Int.floor u + 2 ≤ (j : ℤ)) then |(j : ℝ) - u|⁻¹ else 0)
        ≤ (harmonic M : ℝ) := by
    rw [← Finset.sum_filter]
    simpa [one_div] using right_far_norm_sum_le_harmonic M u
  have hnearcard : near.card ≤ 2 := by
    let target : Finset ℤ := {Int.floor u, Int.floor u + 1}
    have hmaps : Set.MapsTo (fun j : ℕ => (j : ℤ)) (near : Set ℕ) (target : Set ℤ) := by
      intro j hj
      have hj' : (j : ℤ) = Int.floor u ∨ (j : ℤ) = Int.floor u + 1 :=
        (Finset.mem_filter.mp hj).2
      simp [target, hj']
    have hinj : Set.InjOn (fun j : ℕ => (j : ℤ)) (near : Set ℕ) := by
      intro a ha b hb h
      exact Int.ofNat.inj h
    have hc : near.card ≤ target.card := Finset.card_le_card_of_injOn _ hmaps hinj
    exact hc.trans
      (by
        simpa [target] using
          (Finset.card_le_two : ({Int.floor u, Int.floor u + 1} : Finset ℤ).card ≤ 2))
  have hnearsum :
      ∑ j ∈ Finset.range M,
        (if ((j : ℤ) = Int.floor u ∨ (j : ℤ) = Int.floor u + 1) then
          (4 : ℝ) else 0)
        ≤ 8 := by
    have hsum_eq :
        ∑ j ∈ Finset.range M,
          (if ((j : ℤ) = Int.floor u ∨ (j : ℤ) = Int.floor u + 1) then
            (4 : ℝ) else 0)
          = ∑ j ∈ near, (4 : ℝ) := by
      rw [← Finset.sum_filter]
    rw [hsum_eq, Finset.sum_const]
    have hcast : (near.card : ℝ) ≤ 2 := by exact_mod_cast hnearcard
    have hm : (near.card : ℝ) * 4 ≤ 8 := by nlinarith
    simpa [nsmul_eq_mul] using hm
  have hmain :
      ∑ j ∈ Finset.range M,
        ((if ((j : ℤ) ≤ Int.floor u - 1) then |(j : ℝ) - u|⁻¹ else 0)
          + (if (Int.floor u + 2 ≤ (j : ℤ)) then |(j : ℝ) - u|⁻¹ else 0)
          + (if ((j : ℤ) = Int.floor u ∨ (j : ℤ) = Int.floor u + 1) then
              (4 : ℝ) else 0))
        ≤ 2 * (harmonic M : ℝ) + 8 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    linarith
  have hnonneg : (0 : ℝ) ≤ (harmonic M : ℝ) := by
    simpa [harmonic] using
      (harmonic_mono_real (Nat.zero_le M) : (harmonic 0 : ℝ) ≤ (harmonic M : ℝ))
  calc
    ∑ j ∈ Finset.range M,
      (if |(j : ℝ) - u| < ((4 : ℝ)⁻¹) then 0 else |(j : ℝ) - u|⁻¹)
      ≤ ∑ j ∈ Finset.range M,
        ((if ((j : ℤ) ≤ Int.floor u - 1) then |(j : ℝ) - u|⁻¹ else 0)
          + (if (Int.floor u + 2 ≤ (j : ℤ)) then |(j : ℝ) - u|⁻¹ else 0)
          + (if ((j : ℤ) = Int.floor u ∨ (j : ℤ) = Int.floor u + 1) then
              (4 : ℝ) else 0)) := hsum_point
    _ ≤ 2 * (harmonic M : ℝ) + 8 := hmain
    _ ≤ 16 * (1 + (harmonic M : ℝ)) := by nlinarith

lemma grid_close_iff_norm_close
    {M : ℕ} (hM : M ≠ 0) (H x : ℝ) (j : ℕ) :
    |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x| < 1 / (4 * (M : ℝ)) ↔
      |(j : ℝ) - ((M : ℝ) * (x - H) - 1 / 2)| < ((4 : ℝ)⁻¹) := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
  rw [grid_distance_eq_abs_sub_u_div (M := M) hM H x j]
  constructor
  · intro h
    have hmul := (div_lt_iff₀ hMpos).mp h
    calc
      |(j : ℝ) - ((M : ℝ) * (x - H) - 1 / 2)| <
          (1 / (4 * (M : ℝ))) * (M : ℝ) := hmul
      _ = ((4 : ℝ)⁻¹) := by field_simp [(ne_of_gt hMpos)]
  · intro h
    have hmul :
        |(j : ℝ) - ((M : ℝ) * (x - H) - 1 / 2)| <
          (1 / (4 * (M : ℝ))) * (M : ℝ) := by
      calc
        |(j : ℝ) - ((M : ℝ) * (x - H) - 1 / 2)| < ((4 : ℝ)⁻¹) := h
        _ = (1 / (4 * (M : ℝ))) * (M : ℝ) := by field_simp [(ne_of_gt hMpos)]
    exact (div_lt_iff₀ hMpos).mpr hmul

lemma grid_inverse_eq_M_mul_norm_inv
    {M : ℕ} (hM : M ≠ 0) (H x : ℝ) (j : ℕ) :
    1 / |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x| =
      (M : ℝ) * |(j : ℝ) - ((M : ℝ) * (x - H) - 1 / 2)|⁻¹ := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
  rw [grid_distance_eq_abs_sub_u_div (M := M) hM H x j]
  field_simp [(ne_of_gt hMpos)]

lemma grid_inverse_distance_sum_le_harmonic
    {M : ℕ} (hM : M ≠ 0) (H x : ℝ) :
    ∑ j ∈ Finset.range M,
      (if |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x| < 1 / (4 * (M : ℝ))
        then 0
        else 1 / |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x|)
      ≤ 16 * (M : ℝ) * (1 + (harmonic M : ℝ)) := by
  let u : ℝ := (M : ℝ) * (x - H) - 1 / 2
  have hsum_eq :
      ∑ j ∈ Finset.range M,
        (if |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x| < 1 / (4 * (M : ℝ))
          then 0
          else 1 / |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x|)
        = ∑ j ∈ Finset.range M,
          (M : ℝ) *
            (if |(j : ℝ) - u| < ((4 : ℝ)⁻¹) then 0 else |(j : ℝ) - u|⁻¹) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hiff := grid_close_iff_norm_close (M := M) hM H x j
    by_cases hclose : |(j : ℝ) - u| < ((4 : ℝ)⁻¹)
    · have horig :
          |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x| < 1 / (4 * (M : ℝ)) :=
        hiff.mpr (by simpa [u] using hclose)
      rw [if_pos horig]
      rw [if_pos hclose]
      simp
    · have horig :
          ¬ |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x| <
              1 / (4 * (M : ℝ)) := by
        intro hbad
        exact hclose (by simpa [u] using hiff.mp hbad)
      rw [if_neg horig]
      rw [if_neg hclose]
      rw [grid_inverse_eq_M_mul_norm_inv (M := M) hM H x j]
  have hnorm := normalized_grid_inverse_sum_le M u
  rw [hsum_eq]
  rw [← Finset.mul_sum]
  have hMnonneg : 0 ≤ (M : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hnorm hMnonneg
  nlinarith

lemma grid_point_mem_Ioo {M : ℕ} (hM : M ≠ 0) (H : ℝ) {j : ℕ}
    (hj : j ∈ Finset.range M) :
    H < H + (((j : ℝ) + 1 / 2) / (M : ℝ)) ∧
      H + (((j : ℝ) + 1 / 2) / (M : ℝ)) < H + 1 := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hfracpos : 0 < (((j : ℝ) + 1 / 2) / (M : ℝ)) := by positivity
  have hjlt : j < M := Finset.mem_range.mp hj
  have hnumlt : (j : ℝ) + 1 / 2 < (M : ℝ) := by
    have hsucc : j + 1 ≤ M := Nat.succ_le_of_lt hjlt
    have hsucc_real : (j : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hsucc
    linarith
  have hfraclt : (((j : ℝ) + 1 / 2) / (M : ℝ)) < 1 := by
    rw [div_lt_iff₀ hMpos]
    simpa using hnumlt
  constructor <;> linarith

lemma grid_point_diff_abs
    {M : ℕ} (hM : M ≠ 0) (H : ℝ) (j k : ℕ) :
    |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) -
      (H + (((k : ℝ) + 1 / 2) / (M : ℝ)))| =
      |((j : ℝ) - (k : ℝ))| / (M : ℝ) := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hsub :
      (H + (((j : ℝ) + 1 / 2) / (M : ℝ))) -
        (H + (((k : ℝ) + 1 / 2) / (M : ℝ))) =
        (((j : ℝ) - (k : ℝ)) / (M : ℝ)) := by
    field_simp [(ne_of_gt hMpos)]
    ring
  rw [hsub, abs_div, abs_of_pos hMpos]

lemma grid_close_index_unique
    {M : ℕ} (hM : M ≠ 0) (H x : ℝ) {j k : ℕ}
    (hjclose : |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x| <
      1 / (4 * (M : ℝ)))
    (hkclose : |(H + (((k : ℝ) + 1 / 2) / (M : ℝ))) - x| <
      1 / (4 * (M : ℝ))) :
    j = k := by
  by_contra hne
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hdist_upper :
      |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) -
        (H + (((k : ℝ) + 1 / 2) / (M : ℝ)))| < 1 / (2 * (M : ℝ)) := by
    have htri :
        |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) -
          (H + (((k : ℝ) + 1 / 2) / (M : ℝ)))| ≤
          |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x| +
          |(H + (((k : ℝ) + 1 / 2) / (M : ℝ))) - x| := by
      calc
        |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) -
          (H + (((k : ℝ) + 1 / 2) / (M : ℝ)))| =
            |((H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x) +
              (x - (H + (((k : ℝ) + 1 / 2) / (M : ℝ))))| := by ring_nf
        _ ≤ |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x| +
            |x - (H + (((k : ℝ) + 1 / 2) / (M : ℝ)))| := abs_add_le _ _
        _ = |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x| +
            |(H + (((k : ℝ) + 1 / 2) / (M : ℝ))) - x| := by
          rw [abs_sub_comm x]
    have hsum :
        |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - x| +
          |(H + (((k : ℝ) + 1 / 2) / (M : ℝ))) - x| <
          1 / (2 * (M : ℝ)) := by
      have hEq : 1 / (4 * (M : ℝ)) + 1 / (4 * (M : ℝ)) =
          1 / (2 * (M : ℝ)) := by
        field_simp [(ne_of_gt hMpos)]
        norm_num
      linarith
    exact lt_of_le_of_lt htri hsum
  have hint_ne : ((j : ℕ) : ℤ) - ((k : ℕ) : ℤ) ≠ 0 := by
    intro hzero
    have hcast : ((j : ℕ) : ℤ) = ((k : ℕ) : ℤ) := by omega
    exact hne (by exact_mod_cast hcast)
  have hone_int : (1 : ℤ) ≤ |((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)| :=
    Int.one_le_abs hint_ne
  have hone_real : (1 : ℝ) ≤ |((j : ℝ) - (k : ℝ))| := by exact_mod_cast hone_int
  have hdist_lower :
      1 / (M : ℝ) ≤ |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) -
        (H + (((k : ℝ) + 1 / 2) / (M : ℝ)))| := by
    rw [grid_point_diff_abs (M := M) hM H j k]
    exact div_le_div_of_nonneg_right hone_real (le_of_lt hMpos)
  have hhalf : 1 / (2 * (M : ℝ)) < 1 / (M : ℝ) := by
    rw [one_div_lt_one_div]
    · nlinarith
    · positivity
    · positivity
  linarith

lemma grid_bad_card_le {α : Type*} [DecidableEq α]
    (S : Finset α) (a : α → ℝ) {M : ℕ} (hM : M ≠ 0) (H : ℝ) :
    ((Finset.range M).filter
      (fun j : ℕ => ∃ p ∈ S,
        |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - (|a p|)| < 1 / (4 * (M : ℝ)))).card
      ≤ S.card := by
  classical
  let bad : Finset ℕ := (Finset.range M).filter
      (fun j : ℕ => ∃ p ∈ S,
        |(H + (((j : ℝ) + 1 / 2) / (M : ℝ))) - (|a p|)| < 1 / (4 * (M : ℝ)))
  have hbad_wit : ∀ j : bad, ∃ p ∈ S,
        |(H + (((((j : bad) : ℕ) : ℝ) + 1 / 2) / (M : ℝ))) - (|a p|)| <
          1 / (4 * (M : ℝ)) := by
    intro j
    exact (Finset.mem_filter.mp j.property).2
  let nearest : bad → S :=
    fun j => ⟨Classical.choose (hbad_wit j), (Classical.choose_spec (hbad_wit j)).1⟩
  have hnearest_close : ∀ j : bad,
        |(H + (((((j : bad) : ℕ) : ℝ) + 1 / 2) / (M : ℝ))) -
            (|a (nearest j : S)|)| < 1 / (4 * (M : ℝ)) := by
    intro j
    exact (Classical.choose_spec (hbad_wit j)).2
  have hinj : Function.Injective nearest := by
    intro j k hnn
    apply Subtype.ext
    exact grid_close_index_unique (M := M) hM H (|a (nearest j : S)|)
      (j := (j : ℕ)) (k := (k : ℕ))
      (by simpa using hnearest_close j)
      (by simpa [hnn] using hnearest_close k)
  have hcard : Fintype.card bad ≤ Fintype.card S :=
    Fintype.card_le_of_injective nearest hinj
  have hbadcard : Fintype.card bad = bad.card := Fintype.card_coe bad
  have hScard : Fintype.card S = S.card := Fintype.card_coe S
  simpa [bad, hbadcard, hScard] using hcard

lemma exists_le_of_sum_le_card_mul {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f : α → ℝ) (B : ℝ)
    (h : ∑ x ∈ s, f x ≤ (s.card : ℝ) * B) :
    ∃ x ∈ s, f x ≤ B := by
  by_contra hnone
  push Not at hnone
  have hlt : (s.card : ℝ) * B < ∑ x ∈ s, f x := by
    calc
      (s.card : ℝ) * B = ∑ x ∈ s, B := by
        rw [Finset.sum_const]
        simpa [nsmul_eq_mul, mul_comm]
      _ < ∑ x ∈ s, f x := by
        exact Finset.sum_lt_sum_of_nonempty hs (fun x hx => hnone x hx)
  linarith

lemma exists_grid_point_with_separation_and_inverse_sum
    {α : Type*} [DecidableEq α]
    (S : Finset α) (a : α → ℝ) (H : ℝ) :
    let M : ℕ := 4 * (S.card + 1)
    ∃ T : ℝ,
      H < T ∧ T < H + 1 ∧
      (∀ p ∈ S, 1 / (4 * (M : ℝ)) ≤ |T - (|a p|)|) ∧
      ∑ p ∈ S, 1 / |T - (|a p|)| ≤
        64 * (M : ℝ) * (1 + (harmonic M : ℝ)) := by
  classical
  intro M
  have hMpos_nat : 0 < M := by
    dsimp [M]
    omega
  have hM : M ≠ 0 := Nat.ne_of_gt hMpos_nat
  let grid : ℕ → ℝ := fun j => H + (((j : ℝ) + 1 / 2) / (M : ℝ))
  let bad : Finset ℕ := (Finset.range M).filter
    (fun j : ℕ => ∃ p ∈ S, |grid j - (|a p|)| < 1 / (4 * (M : ℝ)))
  let good : Finset ℕ := Finset.range M \ bad
  have hbad_subset : bad ⊆ Finset.range M := Finset.filter_subset _ _
  have hbad_card : bad.card ≤ S.card := by
    simpa [bad, grid] using grid_bad_card_le S a (M := M) hM H
  have hbad_lt_range : bad.card < (Finset.range M).card := by
    rw [Finset.card_range]
    dsimp [M]
    omega
  have hgood_card_pos : 0 < good.card := by
    have hcard_good : good.card = (Finset.range M).card - bad.card := by
      exact Finset.card_sdiff_of_subset hbad_subset
    rw [hcard_good]
    exact Nat.sub_pos_of_lt hbad_lt_range
  have hgood_nonempty : good.Nonempty := by
    rwa [← Finset.card_pos]
  have hgood_subset_range : good ⊆ Finset.range M := Finset.sdiff_subset
  have hgood_not_bad : ∀ j ∈ good, j ∉ bad := by
    intro j hj
    exact (Finset.mem_sdiff.mp hj).2
  have hgood_sep_lt : ∀ j ∈ good, ∀ p ∈ S,
      ¬ |grid j - (|a p|)| < 1 / (4 * (M : ℝ)) := by
    intro j hj p hp hclose
    exact hgood_not_bad j hj (Finset.mem_filter.mpr ⟨hgood_subset_range hj, ⟨p, hp, hclose⟩⟩)
  have hgood_sep : ∀ j ∈ good, ∀ p ∈ S,
      1 / (4 * (M : ℝ)) ≤ |grid j - (|a p|)| := by
    intro j hj p hp
    exact le_of_not_gt (hgood_sep_lt j hj p hp)
  have hsum_good_eq :
      ∑ j ∈ good, (∑ p ∈ S, 1 / |grid j - (|a p|)|) =
        ∑ j ∈ good,
          ∑ p ∈ S,
            (if |grid j - (|a p|)| < 1 / (4 * (M : ℝ)) then 0
             else 1 / |grid j - (|a p|)|) := by
    refine Finset.sum_congr rfl ?_
    intro j hjgood
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [if_neg (hgood_sep_lt j hjgood p hp)]
  have hsum_good_le_total :
      ∑ j ∈ good, (∑ p ∈ S, 1 / |grid j - (|a p|)|) ≤
        ∑ j ∈ Finset.range M,
          ∑ p ∈ S,
            (if |grid j - (|a p|)| < 1 / (4 * (M : ℝ)) then 0
             else 1 / |grid j - (|a p|)|) := by
    rw [hsum_good_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hgood_subset_range
      (by
        intro j hjrange hjnot
        exact Finset.sum_nonneg (fun p hp => by split_ifs <;> positivity))
  have htotal_bound :
      ∑ j ∈ Finset.range M,
          ∑ p ∈ S,
            (if |grid j - (|a p|)| < 1 / (4 * (M : ℝ)) then 0
             else 1 / |grid j - (|a p|)|)
        ≤ (S.card : ℝ) * (16 * (M : ℝ) * (1 + (harmonic M : ℝ))) := by
    rw [Finset.sum_comm]
    calc
      ∑ p ∈ S,
          ∑ j ∈ Finset.range M,
            (if |grid j - (|a p|)| < 1 / (4 * (M : ℝ)) then 0
             else 1 / |grid j - (|a p|)|)
        ≤ ∑ p ∈ S, 16 * (M : ℝ) * (1 + (harmonic M : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro p hp
          simpa [grid] using grid_inverse_distance_sum_le_harmonic (M := M) hM H (|a p|)
      _ = (S.card : ℝ) * (16 * (M : ℝ) * (1 + (harmonic M : ℝ))) := by
          rw [Finset.sum_const]
          simpa [nsmul_eq_mul, mul_comm]
  have hgood_total_bound :
      ∑ j ∈ good, (∑ p ∈ S, 1 / |grid j - (|a p|)|) ≤
        (S.card : ℝ) * (16 * (M : ℝ) * (1 + (harmonic M : ℝ))) :=
    le_trans hsum_good_le_total htotal_bound
  let B : ℝ := 64 * (M : ℝ) * (1 + (harmonic M : ℝ))
  have hnonneg_factor : 0 ≤ 16 * (M : ℝ) * (1 + (harmonic M : ℝ)) := by
    have hh : (0 : ℝ) ≤ (harmonic M : ℝ) := by
      simpa [harmonic] using
        (harmonic_mono_real (Nat.zero_le M) : (harmonic 0 : ℝ) ≤ (harmonic M : ℝ))
    positivity
  have hsum_le_cardB :
      ∑ j ∈ good, (∑ p ∈ S, 1 / |grid j - (|a p|)|) ≤ (good.card : ℝ) * B := by
    have hScard_le : (S.card : ℝ) ≤ 4 * (good.card : ℝ) := by
      have hgood_card : good.card = (Finset.range M).card - bad.card := by
        exact Finset.card_sdiff_of_subset hbad_subset
      have hgood_ge : S.card ≤ 4 * good.card := by
        rw [hgood_card, Finset.card_range]
        dsimp [M]
        omega
      exact_mod_cast hgood_ge
    calc
      ∑ j ∈ good, (∑ p ∈ S, 1 / |grid j - (|a p|)|)
        ≤ (S.card : ℝ) * (16 * (M : ℝ) * (1 + (harmonic M : ℝ))) :=
          hgood_total_bound
      _ ≤ (4 * (good.card : ℝ)) * (16 * (M : ℝ) * (1 + (harmonic M : ℝ))) := by
          exact mul_le_mul_of_nonneg_right hScard_le hnonneg_factor
      _ = (good.card : ℝ) * B := by
          dsimp [B]
          ring
  obtain ⟨j, hjgood, hjsum⟩ := exists_le_of_sum_le_card_mul good hgood_nonempty
    (fun j => ∑ p ∈ S, 1 / |grid j - (|a p|)|) B hsum_le_cardB
  refine ⟨grid j, ?_, ?_, ?_, ?_⟩
  · exact (grid_point_mem_Ioo (M := M) hM H (hgood_subset_range hjgood)).1
  · exact (grid_point_mem_Ioo (M := M) hM H (hgood_subset_range hjgood)).2
  · intro p hp
    exact hgood_sep j hjgood p hp
  · exact hjsum

lemma grid_harmonic_constant_le_power (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    let M : ℕ := 4 * (n + 1)
    64 * (M : ℝ) * (1 + (harmonic M : ℝ)) ≤
      (512 + (64 / θ) * (4 : ℝ) ^ (1 + θ)) * ((n : ℝ) + 1) ^ (1 + θ) := by
  intro M
  let m : ℝ := (n : ℝ) + 1
  have hm_pos : 0 < m := by dsimp [m]; positivity
  have hm_ge_one : 1 ≤ m := by dsimp [m]; norm_num
  have hM_eq : (M : ℝ) = 4 * m := by
    dsimp [M, m]
    norm_num
  have hM_pos : 0 < (M : ℝ) := by rw [hM_eq]; positivity
  have hθ_nonneg : 0 ≤ θ := le_of_lt hθ
  have hmθ_ge_one : 1 ≤ m ^ θ := by
    simpa using Real.one_le_rpow hm_ge_one hθ_nonneg
  have hharm : (1 + (harmonic M : ℝ)) ≤ 2 + Real.log (M : ℝ) := by
    have h := harmonic_le_one_add_log (n := M)
    linarith
  have hlog : Real.log (M : ℝ) ≤ (M : ℝ) ^ θ / θ :=
    Real.log_le_rpow_div (le_of_lt hM_pos) hθ
  have hfactor : 1 + (harmonic M : ℝ) ≤ 2 + (M : ℝ) ^ θ / θ := by linarith
  have hmain₀ :
      64 * (M : ℝ) * (1 + (harmonic M : ℝ)) ≤
        64 * (M : ℝ) * (2 + (M : ℝ) ^ θ / θ) := by
    exact mul_le_mul_of_nonneg_left hfactor (by positivity)
  have hsplit :
      64 * (M : ℝ) * (2 + (M : ℝ) ^ θ / θ) =
        128 * (M : ℝ) + (64 / θ) * (M : ℝ) ^ (1 + θ) := by
    rw [Real.rpow_add hM_pos 1 θ, Real.rpow_one]
    field_simp [ne_of_gt hθ]
    ring
  have hlinear : 128 * (M : ℝ) ≤ 512 * m ^ (1 + θ) := by
    rw [hM_eq]
    have hm_decomp : m ^ (1 + θ) = m * m ^ θ := by
      rw [Real.rpow_add hm_pos 1 θ, Real.rpow_one]
    rw [hm_decomp]
    nlinarith
  have hpowM : (M : ℝ) ^ (1 + θ) = (4 : ℝ) ^ (1 + θ) * m ^ (1 + θ) := by
    rw [hM_eq]
    exact Real.mul_rpow (by norm_num) (le_of_lt hm_pos)
  have hpowterm : (64 / θ) * (M : ℝ) ^ (1 + θ) ≤
      ((64 / θ) * (4 : ℝ) ^ (1 + θ)) * m ^ (1 + θ) := by
    rw [hpowM]
    ring_nf
    exact le_rfl
  calc
    64 * (M : ℝ) * (1 + (harmonic M : ℝ))
      ≤ 64 * (M : ℝ) * (2 + (M : ℝ) ^ θ / θ) := hmain₀
    _ = 128 * (M : ℝ) + (64 / θ) * (M : ℝ) ^ (1 + θ) := hsplit
    _ ≤ 512 * m ^ (1 + θ) +
          ((64 / θ) * (4 : ℝ) ^ (1 + θ)) * m ^ (1 + θ) :=
        add_le_add hlinear hpowterm
    _ = (512 + (64 / θ) * (4 : ℝ) ^ (1 + θ)) *
          ((n : ℝ) + 1) ^ (1 + θ) := by
      dsimp [m]
      ring

lemma exists_height_with_separation_and_inverse_sum_bound
    {α : Type*} [DecidableEq α] (θ : ℝ) (hθ : 0 < θ) :
    ∃ Kθ : ℝ, 0 < Kθ ∧
      ∀ (S : Finset α) (a : α → ℝ) (H : ℝ),
        ∃ T : ℝ,
          H < T ∧ T < H + 1 ∧
          (∀ p ∈ S,
            1 / (Kθ * ((S.card : ℝ) + 1) ^ (1 + θ)) ≤ |T - (|a p|)|) ∧
          ∑ p ∈ S, 1 / |T - (|a p|)| ≤
            Kθ * ((S.card : ℝ) + 1) ^ (1 + θ) := by
  classical
  let Kθ : ℝ := 512 + (64 / θ) * (4 : ℝ) ^ (1 + θ)
  have hK_pos : 0 < Kθ := by
    have hpowpos : 0 < (4 : ℝ) ^ (1 + θ) := Real.rpow_pos_of_pos (by norm_num) _
    dsimp [Kθ]
    positivity
  refine ⟨Kθ, hK_pos, ?_⟩
  intro S a H
  let M : ℕ := 4 * (S.card + 1)
  obtain ⟨T, hHT, hTH, hsep_grid, hsum_grid⟩ :=
    exists_grid_point_with_separation_and_inverse_sum S a H
  have hsum_absorb :
      64 * (M : ℝ) * (1 + (harmonic M : ℝ)) ≤
        Kθ * ((S.card : ℝ) + 1) ^ (1 + θ) := by
    simpa [Kθ, M] using grid_harmonic_constant_le_power θ hθ S.card
  have hbase_pos : 0 < ((S.card : ℝ) + 1) := by positivity
  have hpow_pos : 0 < ((S.card : ℝ) + 1) ^ (1 + θ) :=
    Real.rpow_pos_of_pos hbase_pos _
  have hden_pos : 0 < Kθ * ((S.card : ℝ) + 1) ^ (1 + θ) :=
    mul_pos hK_pos hpow_pos
  have hM_eq : (M : ℝ) = 4 * ((S.card : ℝ) + 1) := by
    dsimp [M]
    norm_num
  have hsep_den_le : 4 * (M : ℝ) ≤ Kθ * ((S.card : ℝ) + 1) ^ (1 + θ) := by
    rw [hM_eq]
    have hbase_ge_one : 1 ≤ ((S.card : ℝ) + 1) := by norm_num
    have hθ_nonneg : 0 ≤ θ := le_of_lt hθ
    have hpow_ge_one : 1 ≤ ((S.card : ℝ) + 1) ^ θ :=
      Real.one_le_rpow hbase_ge_one hθ_nonneg
    have hpow_decomp :
        ((S.card : ℝ) + 1) ^ (1 + θ) =
          ((S.card : ℝ) + 1) * ((S.card : ℝ) + 1) ^ θ := by
      rw [Real.rpow_add hbase_pos 1 θ, Real.rpow_one]
    rw [hpow_decomp]
    have hK_ge : 16 ≤ Kθ := by
      have hterm_nonneg : 0 ≤ (64 / θ) * (4 : ℝ) ^ (1 + θ) := by positivity
      dsimp [Kθ]
      nlinarith
    nlinarith
  have hsep_weaken : ∀ p ∈ S,
      1 / (Kθ * ((S.card : ℝ) + 1) ^ (1 + θ)) ≤ |T - (|a p|)| := by
    intro p hp
    have hgrid := hsep_grid p hp
    have hgrid_den_pos : 0 < 4 * (M : ℝ) := by
      rw [hM_eq]
      positivity
    have hinv_le :
        1 / (Kθ * ((S.card : ℝ) + 1) ^ (1 + θ)) ≤ 1 / (4 * (M : ℝ)) :=
      one_div_le_one_div_of_le hgrid_den_pos hsep_den_le
    exact le_trans hinv_le hgrid
  refine ⟨T, hHT, hTH, hsep_weaken, ?_⟩
  exact le_trans hsum_grid hsum_absorb

/-! ## Hadamard tail algebra -/

lemma hadamard_pair_eq (s ρ : ℂ) (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) :
    1 / (s - ρ) + 1 / ρ = s / (ρ * (s - ρ)) := by
  field_simp [hρ, sub_ne_zero.mpr hsρ]
  ring

lemma hadamard_far_term_norm_le (s ρ : ℂ)
    (hfar : 2 * ‖s‖ ≤ ‖ρ‖) (hρ : ρ ≠ 0) :
    ‖1 / (s - ρ) + 1 / ρ‖ ≤ 2 * ‖s‖ * ‖ρ‖⁻¹ ^ 2 := by
  have hsρ : s ≠ ρ := by
    intro hs_eq
    have hnorm_eq : ‖s‖ = ‖ρ‖ := by rw [hs_eq]
    have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
    nlinarith
  rw [hadamard_pair_eq s ρ hρ hsρ]
  have hdist_lower : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
    have hrev : ‖ρ‖ = ‖(ρ - s) + s‖ := by ring_nf
    have htri : ‖ρ‖ ≤ ‖ρ - s‖ + ‖s‖ := by
      calc
        ‖ρ‖ = ‖(ρ - s) + s‖ := hrev
        _ ≤ ‖ρ - s‖ + ‖s‖ := norm_add_le _ _
    have hsub : ‖ρ - s‖ = ‖s - ρ‖ := by
      rw [← norm_neg (s - ρ)]
      ring_nf
    rw [hsub] at htri
    nlinarith
  have hρnorm_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  calc
    ‖s / (ρ * (s - ρ))‖ = ‖s‖ / (‖ρ‖ * ‖s - ρ‖) := by
      rw [norm_div, norm_mul]
    _ ≤ ‖s‖ / (‖ρ‖ * (‖ρ‖ / 2)) := by
      have hden_le : ‖ρ‖ * (‖ρ‖ / 2) ≤ ‖ρ‖ * ‖s - ρ‖ := by
        exact mul_le_mul_of_nonneg_left hdist_lower (norm_nonneg ρ)
      exact div_le_div_of_nonneg_left (norm_nonneg s)
        (mul_pos hρnorm_pos (by positivity)) hden_le
    _ = 2 * ‖s‖ * ‖ρ‖⁻¹ ^ 2 := by
      field_simp [ne_of_gt hρnorm_pos]

/-! ## Finite xi-divisor balls -/

abbrev XiDivisorIndex :=
  Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)

noncomputable def xiDivisorNearFinset (R : ℝ) : Finset XiDivisorIndex :=
  (Complex.Hadamard.divisorZeroIndex₀_norm_le_finite
    (f := Complex.riemannXi) (U := Set.univ) R (by simp)).toFinset

lemma mem_xiDivisorNearFinset {R : ℝ} {p : XiDivisorIndex} :
    p ∈ xiDivisorNearFinset R ↔
      ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ R := by
  unfold xiDivisorNearFinset XiDivisorIndex
  rw [Set.Finite.mem_toFinset]
  rfl

lemma xiDivisorNearFinset_card_le_divisorMassClosedBall₀ {R : ℝ} (hR : 0 < R) :
    ((xiDivisorNearFinset R).card : ℝ) ≤
      Complex.Hadamard.divisorMassClosedBall₀ Complex.riemannXi R := by
  classical
  haveI : Fintype
      {p : XiDivisorIndex // ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ R} := by
    have hfinite : Set.Finite
        {p : XiDivisorIndex | ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ R} :=
      Complex.Hadamard.divisorZeroIndex₀_norm_le_finite
        (f := Complex.riemannXi) (U := Set.univ) R (by simp)
    exact Set.Finite.fintype hfinite
  have hcard :
      (xiDivisorNearFinset R).card =
        Nat.card {p : XiDivisorIndex //
          ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ R} := by
    rw [Nat.card_eq_fintype_card]
    let e :
        {p // p ∈ xiDivisorNearFinset R} ≃
          {p : XiDivisorIndex // ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ R} :=
      { toFun := fun p => ⟨p.1, (mem_xiDivisorNearFinset.mp p.2)⟩
        invFun := fun p => ⟨p.1, (mem_xiDivisorNearFinset.mpr p.2)⟩
        left_inv := by intro p; rfl
        right_inv := by intro p; rfl }
    have h := Fintype.card_congr e
    simpa using h
  rw [hcard]
  exact Complex.Hadamard.card_ball_le_divisorMassClosedBall₀
    (f := Complex.riemannXi) Complex.differentiable_riemannXi hR

/-! ## Kadiri completed factor and xi -/

lemma completedZetaFactor_eq_riemannXi_of_im_ne_zero {s : ℂ}
    (hsim : s.im ≠ 0) :
    Kadiri.completedZetaFactor s = Complex.riemannXi s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hsim
    simp at hsim
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsim
    simp at hsim
  rw [Complex.riemannXi_eq_mul_completedRiemannZeta hs0 hs1]
  unfold Kadiri.completedZetaFactor Kadiri.zetaPoleFactor Kadiri.zetaPiFactor
    Kadiri.zetaGammaFactor
  rw [riemannZeta_def_of_ne_zero hs0]
  rw [Complex.Gammaℝ_def]
  have hs2 : s / 2 ≠ 0 := by
    exact div_ne_zero hs0 two_ne_zero
  have hGamma : Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have him : (s / 2).im = 0 := by
      rw [hm]
      simp
    have hs_im : s.im / 2 = 0 := by
      simpa using him
    exact hsim (by linarith)
  rw [Complex.Gamma_add_one (s / 2) hs2]
  have hpi_ne : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  rw [Complex.cpow_def_of_ne_zero hpi_ne]
  rw [← Complex.ofReal_log (le_of_lt Real.pi_pos)]
  field_simp [hs0, hpi_ne, Complex.exp_ne_zero, hGamma]

lemma completedZetaFactor_eventuallyEq_riemannXi_of_im_ne_zero {s : ℂ}
    (hsim : s.im ≠ 0) :
    Kadiri.completedZetaFactor =ᶠ[𝓝 s] Complex.riemannXi := by
  have hclosed0 : IsClosed (Complex.im ⁻¹' ({0} : Set ℝ)) :=
    isClosed_singleton.preimage continuous_im
  have hset : Complex.im ⁻¹' ({0} : Set ℝ) = {z : ℂ | z.im = 0} := by
    ext z
    simp
  have hclosed : IsClosed {z : ℂ | z.im = 0} := by
    simpa [hset] using hclosed0
  have hopen0 : IsOpen ({z : ℂ | z.im = 0}ᶜ) := hclosed.isOpen_compl
  have hopen : IsOpen {z : ℂ | z.im ≠ 0} := by
    simpa [Set.compl_setOf] using hopen0
  filter_upwards [hopen.mem_nhds hsim] with z hz
  exact completedZetaFactor_eq_riemannXi_of_im_ne_zero hz

lemma logDeriv_completedZetaFactor_eq_riemannXi_of_im_ne_zero {s : ℂ}
    (hsim : s.im ≠ 0) :
    logDeriv Kadiri.completedZetaFactor s = logDeriv Complex.riemannXi s := by
  have hEq := completedZetaFactor_eventuallyEq_riemannXi_of_im_ne_zero (s := s) hsim
  rw [logDeriv_apply, logDeriv_apply]
  rw [hEq.deriv_eq]
  have hval : Kadiri.completedZetaFactor s = Complex.riemannXi s :=
    completedZetaFactor_eq_riemannXi_of_im_ne_zero hsim
  rw [hval]

/-! ## Quantitative Hadamard scission on horizontal lines -/

noncomputable def xiHadamardTerm (z : ℂ) (p : XiDivisorIndex) : ℂ :=
  let ρ := Complex.Hadamard.divisorZeroIndex₀_val p
  1 / (z - ρ) + 1 / ρ

noncomputable def xiDivisorZ₂ : ℝ :=
  ∑' p : XiDivisorIndex, ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ 2

lemma xiDivisorZ₂_nonneg : 0 ≤ xiDivisorZ₂ := by
  unfold xiDivisorZ₂
  exact tsum_nonneg (fun p => by positivity)

lemma abs_abs_height_sub_im_le_norm_horizontal
    {σ τ T : ℝ} (hτ : |τ| = T) (ρ : ℂ) :
    |T - (|ρ.im|)| ≤ ‖(σ + τ * Complex.I : ℂ) - ρ‖ := by
  have h1 : |T - (|ρ.im|)| ≤ |τ - ρ.im| := by
    rw [← hτ]
    simpa [abs_sub_comm] using abs_abs_sub_abs_le_abs_sub τ ρ.im
  have h2 : |τ - ρ.im| = |((σ + τ * Complex.I : ℂ) - ρ).im| := by
    simp
  have h3 : |((σ + τ * Complex.I : ℂ) - ρ).im| ≤
      ‖(σ + τ * Complex.I : ℂ) - ρ‖ :=
    Complex.abs_im_le_norm _
  linarith

lemma xiHadamard_near_term_norm_le
    {σ τ T : ℝ} (hτ : |τ| = T) {p : XiDivisorIndex}
    (hsep : 0 < |T - (|(Complex.Hadamard.divisorZeroIndex₀_val p).im|)|) :
    ‖xiHadamardTerm (σ + τ * Complex.I) p‖ ≤
      1 / |T - (|(Complex.Hadamard.divisorZeroIndex₀_val p).im|)| +
        ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ := by
  let ρ := Complex.Hadamard.divisorZeroIndex₀_val p
  have hdist := abs_abs_height_sub_im_le_norm_horizontal (σ := σ) (τ := τ)
    (T := T) hτ ρ
  have hinv :
      ‖1 / ((σ + τ * Complex.I : ℂ) - ρ)‖ ≤
        1 / |T - (|ρ.im|)| := by
    rw [norm_div, norm_one]
    simpa [one_div] using one_div_le_one_div_of_le hsep hdist
  calc
    ‖xiHadamardTerm (σ + τ * Complex.I) p‖
        = ‖1 / ((σ + τ * Complex.I : ℂ) - ρ) + 1 / ρ‖ := by
          rfl
    _ ≤ ‖1 / ((σ + τ * Complex.I : ℂ) - ρ)‖ + ‖1 / ρ‖ := norm_add_le _ _
    _ ≤ 1 / |T - (|ρ.im|)| + ‖ρ‖⁻¹ := by
      gcongr
      rw [norm_div, norm_one, one_div]

lemma horizontal_point_ne_xi_divisor
    {S : Finset XiDivisorIndex} {σ τ T Q R : ℝ}
    (hτ : |τ| = T) (hQ_nonneg : 0 ≤ Q) (hR : R = 2 * Q)
    (hzQ : ‖(σ + τ * Complex.I : ℂ)‖ ≤ Q)
    (hS : ∀ p : XiDivisorIndex,
      p ∈ S ↔ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ R)
    (hsep : ∀ p ∈ S,
      0 < |T - (|(Complex.Hadamard.divisorZeroIndex₀_val p).im|)|)
    (p : XiDivisorIndex) :
    (σ + τ * Complex.I : ℂ) ≠ Complex.Hadamard.divisorZeroIndex₀_val p := by
  intro hpz
  by_cases hpS : p ∈ S
  · have him :
        (Complex.Hadamard.divisorZeroIndex₀_val p).im = τ := by
      rw [← hpz]
      simp
    have hzero :
        |T - (|(Complex.Hadamard.divisorZeroIndex₀_val p).im|)| = 0 := by
      rw [him, ← hτ, sub_self, abs_zero]
    have hpos := hsep p hpS
    rw [hzero] at hpos
    linarith
  · have hnotle : ¬ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ R := by
      intro hle
      exact hpS ((hS p).2 hle)
    have hgt : R < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ := lt_of_not_ge hnotle
    have hnorm : ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ Q := by
      rw [← hpz]
      exact hzQ
    have hQR : Q ≤ R := by
      rw [hR]
      nlinarith
    linarith

lemma xiDivisor_near_norm_inv_sum_le_card_add_Z₂ (S : Finset XiDivisorIndex) :
    ∑ p ∈ S, ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ≤
      (S.card : ℝ) + xiDivisorZ₂ := by
  have hpoint : ∀ p : XiDivisorIndex,
      ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ≤
        1 + ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ 2 := by
    intro p
    have hy : 0 ≤ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ := by positivity
    nlinarith [sq_nonneg (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ - 1)]
  have hfinite :
      ∑ p ∈ S, ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ≤
        (S.card : ℝ) +
          ∑ p ∈ S, ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ 2 := by
    calc
      ∑ p ∈ S, ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹
          ≤ ∑ p ∈ S,
              (1 + ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ 2) := by
            exact Finset.sum_le_sum (fun p _ => hpoint p)
      _ = (S.card : ℝ) +
            ∑ p ∈ S, ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_const]
            simp [nsmul_eq_mul]
  have htail :
      ∑ p ∈ S, ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ 2 ≤ xiDivisorZ₂ := by
    unfold xiDivisorZ₂
    exact summable_riemannXi_divisorZeroIndex₀_norm_inv_sq.sum_le_tsum S
      (fun p _ => by positivity)
  linarith

lemma hadamard_near_sum_norm_le
    {S : Finset XiDivisorIndex} {σ τ T : ℝ}
    (hτ : |τ| = T)
    (hsep : ∀ p ∈ S,
      0 < |T - (|(Complex.Hadamard.divisorZeroIndex₀_val p).im|)|) :
    ‖∑ p ∈ S, xiHadamardTerm (σ + τ * Complex.I) p‖ ≤
      (∑ p ∈ S,
        1 / |T - (|(Complex.Hadamard.divisorZeroIndex₀_val p).im|)|) +
        ((S.card : ℝ) + xiDivisorZ₂) := by
  calc
    ‖∑ p ∈ S, xiHadamardTerm (σ + τ * Complex.I) p‖
        ≤ ∑ p ∈ S, ‖xiHadamardTerm (σ + τ * Complex.I) p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ S,
          (1 / |T - (|(Complex.Hadamard.divisorZeroIndex₀_val p).im|)| +
            ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) := by
          exact Finset.sum_le_sum (fun p hp =>
            xiHadamard_near_term_norm_le (σ := σ) (τ := τ) (T := T) hτ (hsep p hp))
    _ = (∑ p ∈ S,
          1 / |T - (|(Complex.Hadamard.divisorZeroIndex₀_val p).im|)|) +
          ∑ p ∈ S, ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ p ∈ S,
          1 / |T - (|(Complex.Hadamard.divisorZeroIndex₀_val p).im|)|) +
          ((S.card : ℝ) + xiDivisorZ₂) := by
          gcongr
          exact xiDivisor_near_norm_inv_sum_le_card_add_Z₂ S

lemma hadamard_far_tsum_norm_le
    {S : Finset XiDivisorIndex} {z : ℂ} {Q : ℝ}
    (hQ_nonneg : 0 ≤ Q) (hzQ : ‖z‖ ≤ Q)
    (hfar : ∀ p : XiDivisorIndex, p ∉ S →
      2 * Q ≤ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖) :
    ‖∑' p : {p : XiDivisorIndex // p ∉ S}, xiHadamardTerm z p.1‖ ≤
      2 * Q * xiDivisorZ₂ := by
  let bound : XiDivisorIndex → ℝ :=
    fun p => 2 * Q * ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ 2
  have hbound_summ : Summable bound := by
    dsimp [bound]
    exact summable_riemannXi_divisorZeroIndex₀_norm_inv_sq.mul_left (2 * Q)
  have hnorm_le : ∀ p : {p : XiDivisorIndex // p ∉ S},
      ‖xiHadamardTerm z p.1‖ ≤ bound p.1 := by
    intro p
    have hρ : Complex.Hadamard.divisorZeroIndex₀_val p.1 ≠ 0 :=
      Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p.1
    have hfarz : 2 * ‖z‖ ≤ ‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖ := by
      nlinarith [hfar p.1 p.2, hzQ]
    have hterm := hadamard_far_term_norm_le z
      (Complex.Hadamard.divisorZeroIndex₀_val p.1) hfarz hρ
    calc
      ‖xiHadamardTerm z p.1‖
          ≤ 2 * ‖z‖ * ‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖⁻¹ ^ 2 := by
            simpa [xiHadamardTerm] using hterm
      _ ≤ bound p.1 := by
            dsimp [bound]
            gcongr
  have hnorm_summ : Summable fun p : {p : XiDivisorIndex // p ∉ S} =>
      ‖xiHadamardTerm z p.1‖ := by
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) hnorm_le ?_
    exact hbound_summ.subtype (p := fun p : XiDivisorIndex => p ∉ S)
  calc
    ‖∑' p : {p : XiDivisorIndex // p ∉ S}, xiHadamardTerm z p.1‖
        ≤ ∑' p : {p : XiDivisorIndex // p ∉ S}, ‖xiHadamardTerm z p.1‖ :=
          norm_tsum_le_tsum_norm hnorm_summ
    _ ≤ ∑' p : {p : XiDivisorIndex // p ∉ S}, bound p.1 :=
          Summable.tsum_le_tsum hnorm_le hnorm_summ (hbound_summ.subtype (p := fun p : XiDivisorIndex => p ∉ S))
    _ ≤ ∑' p : XiDivisorIndex, bound p :=
          Summable.tsum_subtype_le bound {p : XiDivisorIndex | p ∉ S}
            (fun p => by dsimp [bound]; positivity) hbound_summ
    _ = 2 * Q * xiDivisorZ₂ := by
          simp [bound, xiDivisorZ₂, tsum_mul_left]

lemma xi_logDeriv_horizontal_raw_bound
    {P : Polynomial ℂ} (hPdeg : P.degree ≤ 1)
    (hPfac : ∀ z : ℂ, Complex.riemannXi z =
      Complex.exp (Polynomial.eval z P) *
        Complex.Hadamard.divisorCanonicalProduct 1 Complex.riemannXi Set.univ z)
    {S : Finset XiDivisorIndex} {σ τ T Q R Bsel : ℝ}
    (hτ : |τ| = T) (hQ_nonneg : 0 ≤ Q) (hR : R = 2 * Q)
    (hzQ : ‖(σ + τ * Complex.I : ℂ)‖ ≤ Q)
    (hS : ∀ p : XiDivisorIndex,
      p ∈ S ↔ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ R)
    (hsep : ∀ p ∈ S,
      0 < |T - (|(Complex.Hadamard.divisorZeroIndex₀_val p).im|)|)
    (hinvsum :
      ∑ p ∈ S, 1 / |T - (|(Complex.Hadamard.divisorZeroIndex₀_val p).im|)| ≤ Bsel) :
    ‖logDeriv Complex.riemannXi (σ + τ * Complex.I)‖ ≤
      ‖Polynomial.eval 0 P.derivative‖ + (Bsel + ((S.card : ℝ) + xiDivisorZ₂)) +
        2 * Q * xiDivisorZ₂ := by
  let z : ℂ := σ + τ * Complex.I
  have hz_ne : ∀ p : XiDivisorIndex,
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p := by
    intro p
    exact horizontal_point_ne_xi_divisor (S := S) (σ := σ) (τ := τ)
      (T := T) (Q := Q) (R := R) hτ hQ_nonneg hR hzQ hS hsep p
  have hterm_summ : Summable fun p : XiDivisorIndex => xiHadamardTerm z p := by
    simpa [xiHadamardTerm, z] using
      summable_riemannXi_logDerivTerms_divisorZeroIndex₀ (z := z) hz_ne
  have hsplit := hterm_summ.sum_add_tsum_subtype_compl S
  have hnear :
      ‖∑ p ∈ S, xiHadamardTerm z p‖ ≤
        (∑ p ∈ S,
          1 / |T - (|(Complex.Hadamard.divisorZeroIndex₀_val p).im|)|) +
          ((S.card : ℝ) + xiDivisorZ₂) := by
    simpa [z] using hadamard_near_sum_norm_le (S := S) (σ := σ) (τ := τ)
      (T := T) hτ hsep
  have hnear' :
      ‖∑ p ∈ S, xiHadamardTerm z p‖ ≤
        Bsel + ((S.card : ℝ) + xiDivisorZ₂) := by
    exact le_trans hnear (by gcongr)
  have hfar_cond : ∀ p : XiDivisorIndex, p ∉ S →
      2 * Q ≤ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ := by
    intro p hp
    have hnotle : ¬ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ R := by
      intro hle
      exact hp ((hS p).2 hle)
    have hlt : R < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ := lt_of_not_ge hnotle
    rw [hR] at hlt
    exact le_of_lt hlt
  have hfar :
      ‖∑' p : {p : XiDivisorIndex // p ∉ S}, xiHadamardTerm z p.1‖ ≤
        2 * Q * xiDivisorZ₂ :=
    hadamard_far_tsum_norm_le (S := S) (z := z) (Q := Q) hQ_nonneg hzQ hfar_cond
  have hpoly :
      Polynomial.eval (σ + τ * Complex.I) P.derivative =
        Polynomial.eval 0 P.derivative :=
    Polynomial.eval_derivative_eq_eval_derivative_zero_of_degree_le_one hPdeg _
  have hlog := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
    (P := P) (z := z) hPfac hz_ne
  rw [hlog]
  rw [hpoly]
  change ‖Polynomial.eval 0 P.derivative +
      ∑' p : XiDivisorIndex, xiHadamardTerm z p‖ ≤
    ‖Polynomial.eval 0 P.derivative‖ + (Bsel + ((S.card : ℝ) + xiDivisorZ₂)) +
      2 * Q * xiDivisorZ₂
  rw [← hsplit]
  calc
    ‖Polynomial.eval 0 P.derivative +
        (∑ p ∈ S, xiHadamardTerm z p +
          ∑' p : {p : XiDivisorIndex // p ∉ S}, xiHadamardTerm z p.1)‖
        ≤ ‖Polynomial.eval 0 P.derivative‖ +
            ‖∑ p ∈ S, xiHadamardTerm z p +
              ∑' p : {p : XiDivisorIndex // p ∉ S}, xiHadamardTerm z p.1‖ :=
          norm_add_le _ _
    _ ≤ ‖Polynomial.eval 0 P.derivative‖ +
          (‖∑ p ∈ S, xiHadamardTerm z p‖ +
            ‖∑' p : {p : XiDivisorIndex // p ∉ S}, xiHadamardTerm z p.1‖) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ ‖Polynomial.eval 0 P.derivative‖ +
          ((Bsel + ((S.card : ℝ) + xiDivisorZ₂)) + 2 * Q * xiDivisorZ₂) := by
          gcongr
    _ = ‖Polynomial.eval 0 P.derivative‖ +
          (Bsel + ((S.card : ℝ) + xiDivisorZ₂)) + 2 * Q * xiDivisorZ₂ := by
          ring

lemma xi_logDeriv_horizontal_absorption
    {A K AQ H ε θ η Bsel Q polyNorm : ℝ} {S : Finset XiDivisorIndex}
    (hH : 1 ≤ H) (hε0 : 0 ≤ ε) (hθ0 : 0 ≤ θ) (hη0 : 0 ≤ η)
    (hA1 : 1 ≤ A) (hK0 : 0 ≤ K) (hAQ0 : 0 ≤ AQ) (hpoly0 : 0 ≤ polyNorm)
    (hcard : ((S.card : ℝ) + 1) ≤ A * (1 + H) ^ (1 + ε))
    (hBsel : Bsel ≤ K * ((S.card : ℝ) + 1) ^ (1 + θ))
    (hQ : Q ≤ AQ * (1 + H))
    (hexp_sel : (1 + ε) * (1 + θ) ≤ 1 + η)
    (hraw :
      ‖logDeriv Complex.riemannXi z‖ ≤
        polyNorm + (Bsel + ((S.card : ℝ) + xiDivisorZ₂)) + 2 * Q * xiDivisorZ₂) :
    ‖logDeriv Complex.riemannXi z‖ ≤
      (polyNorm + (K * A ^ (1 + θ) + (A + xiDivisorZ₂)) +
          2 * AQ * xiDivisorZ₂ + 1) * (1 + H) ^ (1 + η) := by
  have hbase_pos : 0 < 1 + H := by linarith
  have hbase_nonneg : 0 ≤ 1 + H := le_of_lt hbase_pos
  have hbase_ge_one : 1 ≤ 1 + H := by linarith
  have hηexp_nonneg : 0 ≤ 1 + η := by linarith
  have hX_nonneg : 0 ≤ (1 + H) ^ (1 + η) :=
    Real.rpow_nonneg hbase_nonneg (1 + η)
  have hX_ge_one : 1 ≤ (1 + H) ^ (1 + η) := by
    calc
      (1 : ℝ) = (1 : ℝ) ^ (1 + η) := by rw [Real.one_rpow]
      _ ≤ (1 + H) ^ (1 + η) :=
        Real.rpow_le_rpow zero_le_one hbase_ge_one hηexp_nonneg
  have hεexp_le : 1 + ε ≤ 1 + η := by
    have htheta_one : 1 ≤ 1 + θ := by linarith
    nlinarith
  have hbase_eps_le_X : (1 + H) ^ (1 + ε) ≤ (1 + H) ^ (1 + η) :=
    Real.rpow_le_rpow_of_exponent_le hbase_ge_one hεexp_le
  have hbase_le_X : 1 + H ≤ (1 + H) ^ (1 + η) := by
    calc
      1 + H = (1 + H) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (1 + H) ^ (1 + η) :=
        Real.rpow_le_rpow_of_exponent_le hbase_ge_one (by linarith)
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hApow_nonneg : 0 ≤ A ^ (1 + θ) := Real.rpow_nonneg hA0 _
  have hApow_ge_one : 1 ≤ A ^ (1 + θ) := by
    have hθexp_nonneg : 0 ≤ 1 + θ := by linarith
    calc
      (1 : ℝ) = (1 : ℝ) ^ (1 + θ) := by rw [Real.one_rpow]
      _ ≤ A ^ (1 + θ) := Real.rpow_le_rpow zero_le_one hA1 hθexp_nonneg
  have hcard_nonneg : 0 ≤ ((S.card : ℝ) + 1) := by positivity
  have hsel_pow :
      ((S.card : ℝ) + 1) ^ (1 + θ) ≤
        A ^ (1 + θ) * (1 + H) ^ (1 + η) := by
    have hθexp_nonneg : 0 ≤ 1 + θ := by linarith
    have hright_nonneg : 0 ≤ A * (1 + H) ^ (1 + ε) :=
      mul_nonneg hA0 (Real.rpow_nonneg hbase_nonneg _)
    calc
      ((S.card : ℝ) + 1) ^ (1 + θ)
          ≤ (A * (1 + H) ^ (1 + ε)) ^ (1 + θ) :=
            Real.rpow_le_rpow hcard_nonneg hcard hθexp_nonneg
      _ = A ^ (1 + θ) * ((1 + H) ^ (1 + ε)) ^ (1 + θ) := by
            rw [Real.mul_rpow hA0 (Real.rpow_nonneg hbase_nonneg _)]
      _ = A ^ (1 + θ) * (1 + H) ^ ((1 + ε) * (1 + θ)) := by
            rw [Real.rpow_mul hbase_nonneg]
      _ ≤ A ^ (1 + θ) * (1 + H) ^ (1 + η) := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hbase_ge_one hexp_sel)
              hApow_nonneg
  have hBsel_abs :
      Bsel ≤ (K * A ^ (1 + θ)) * (1 + H) ^ (1 + η) := by
    calc
      Bsel ≤ K * ((S.card : ℝ) + 1) ^ (1 + θ) := hBsel
      _ ≤ K * (A ^ (1 + θ) * (1 + H) ^ (1 + η)) :=
            mul_le_mul_of_nonneg_left hsel_pow hK0
      _ = (K * A ^ (1 + θ)) * (1 + H) ^ (1 + η) := by ring
  have hcard_abs :
      (S.card : ℝ) ≤ A * (1 + H) ^ (1 + η) := by
    have hcard_no_one : (S.card : ℝ) ≤ A * (1 + H) ^ (1 + ε) := by
      nlinarith [hcard]
    exact le_trans hcard_no_one
      (mul_le_mul_of_nonneg_left hbase_eps_le_X hA0)
  have hQ_abs : Q ≤ AQ * (1 + H) ^ (1 + η) :=
    le_trans hQ (mul_le_mul_of_nonneg_left hbase_le_X hAQ0)
  have hZ_nonneg : 0 ≤ xiDivisorZ₂ := xiDivisorZ₂_nonneg
  have hraw_abs :
      polyNorm + (Bsel + ((S.card : ℝ) + xiDivisorZ₂)) + 2 * Q * xiDivisorZ₂
        ≤ (polyNorm + (K * A ^ (1 + θ) + (A + xiDivisorZ₂)) +
            2 * AQ * xiDivisorZ₂ + 1) * (1 + H) ^ (1 + η) := by
    have hpoly_abs : polyNorm ≤ (polyNorm + 1) * (1 + H) ^ (1 + η) := by
      calc
        polyNorm ≤ (polyNorm + 1) * 1 := by nlinarith
        _ ≤ (polyNorm + 1) * (1 + H) ^ (1 + η) := by
              have : 0 ≤ polyNorm + 1 := by nlinarith
              exact mul_le_mul_of_nonneg_left hX_ge_one this
    have hZ_abs : xiDivisorZ₂ ≤ xiDivisorZ₂ * (1 + H) ^ (1 + η) := by
      simpa [mul_one] using mul_le_mul_of_nonneg_left hX_ge_one hZ_nonneg
    have hfar_abs :
        2 * Q * xiDivisorZ₂ ≤ (2 * AQ * xiDivisorZ₂) * (1 + H) ^ (1 + η) := by
      have hqmul : 2 * Q * xiDivisorZ₂ ≤ 2 * (AQ * (1 + H) ^ (1 + η)) * xiDivisorZ₂ := by
        gcongr
      calc
        2 * Q * xiDivisorZ₂ ≤ 2 * (AQ * (1 + H) ^ (1 + η)) * xiDivisorZ₂ := hqmul
        _ = (2 * AQ * xiDivisorZ₂) * (1 + H) ^ (1 + η) := by ring
    calc
      polyNorm + (Bsel + ((S.card : ℝ) + xiDivisorZ₂)) + 2 * Q * xiDivisorZ₂
          ≤ (polyNorm + 1) * (1 + H) ^ (1 + η) +
              ((K * A ^ (1 + θ)) * (1 + H) ^ (1 + η) +
                (A * (1 + H) ^ (1 + η) + xiDivisorZ₂ * (1 + H) ^ (1 + η))) +
              (2 * AQ * xiDivisorZ₂) * (1 + H) ^ (1 + η) := by
            linarith
      _ = (polyNorm + (K * A ^ (1 + θ) + (A + xiDivisorZ₂)) +
            2 * AQ * xiDivisorZ₂ + 1) * (1 + H) ^ (1 + η) := by ring
  exact le_trans hraw hraw_abs

theorem xi_horizontal_logDeriv_bound_from_quantitative_hadamard
    {σL σR : ℝ} (hσLR : σL ≤ σR)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ Cξ : ℝ, 0 < Cξ ∧
      ∀ H : ℝ, 1 ≤ H →
        ∃ T : ℝ,
          H < T ∧ T < H + 1 ∧
          (∀ ρ : ℂ, RHV3Lean.IsNontrivialZetaZero ρ → |ρ.im| ≠ T) ∧
          (∀ σ : ℝ, σL ≤ σ → σ ≤ σR →
            ‖logDeriv Complex.riemannXi (σ + T * Complex.I)‖
              ≤ Cξ * (1 + H) ^ (1 + η)) ∧
          (∀ σ : ℝ, σL ≤ σ → σ ≤ σR →
            ‖logDeriv Complex.riemannXi (σ - T * Complex.I)‖
              ≤ Cξ * (1 + H) ^ (1 + η)) := by
  classical
  let ε : ℝ := η / 8
  let θ : ℝ := η / 8
  have hε_pos : 0 < ε := by dsimp [ε]; positivity
  have hθ_pos : 0 < θ := by dsimp [θ]; positivity
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hθ_nonneg : 0 ≤ θ := le_of_lt hθ_pos
  obtain ⟨Kθ, hKθ_pos, hselect⟩ :=
    exists_height_with_separation_and_inverse_sum_bound
      (α := XiDivisorIndex) θ hθ_pos
  obtain ⟨Cmass, hCmass_pos, hmass⟩ :=
    P4_4b.riemannXi_divisorMassClosedBall₀_le_order_one_plus ε hε_pos
  obtain ⟨P, hPdeg, hPfac⟩ := riemannXi_hadamard_factorization_no_monomial
  let B : ℝ := max |σL| |σR|
  let AQ : ℝ := B + 2
  let AR : ℝ := 2 * B + 5
  let A : ℝ := Cmass * AR ^ (1 + ε) + 1
  let Cξ : ℝ :=
    ‖Polynomial.eval 0 P.derivative‖ +
      (Kθ * A ^ (1 + θ) + (A + xiDivisorZ₂)) +
      2 * AQ * xiDivisorZ₂ + 1
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact le_max_of_le_left (abs_nonneg σL)
  have hAQ_nonneg : 0 ≤ AQ := by dsimp [AQ]; linarith
  have hAR_pos : 0 < AR := by dsimp [AR]; linarith
  have hAR_ge_one : 1 ≤ AR := by dsimp [AR]; linarith
  have hA_ge_one : 1 ≤ A := by
    dsimp [A]
    have hpow_nonneg : 0 ≤ AR ^ (1 + ε) :=
      Real.rpow_nonneg (le_of_lt hAR_pos) _
    have hmul_nonneg : 0 ≤ Cmass * AR ^ (1 + ε) :=
      mul_nonneg (le_of_lt hCmass_pos) hpow_nonneg
    linarith
  have hCξ_pos : 0 < Cξ := by
    dsimp [Cξ]
    have hApow_nonneg : 0 ≤ A ^ (1 + θ) :=
      Real.rpow_nonneg (le_trans zero_le_one hA_ge_one) _
    have hZ_nonneg : 0 ≤ xiDivisorZ₂ := xiDivisorZ₂_nonneg
    positivity
  refine ⟨Cξ, hCξ_pos, ?_⟩
  intro H hH
  let Q : ℝ := B + H + 2
  let R : ℝ := 2 * Q
  let S : Finset XiDivisorIndex := xiDivisorNearFinset R
  obtain ⟨T, hHT, hTH, hsep, hinvsum⟩ :=
    hselect S (fun p => (Complex.Hadamard.divisorZeroIndex₀_val p).im) H
  have hT_pos : 0 < T := by linarith
  have hQ_nonneg : 0 ≤ Q := by dsimp [Q]; linarith
  have hR_pos : 0 < R := by dsimp [R]; linarith
  have hR_ge_one : 1 ≤ R := by dsimp [R, Q]; linarith
  have hR_def : R = 2 * Q := rfl
  have hS_mem : ∀ p : XiDivisorIndex,
      p ∈ S ↔ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ R := by
    intro p
    dsimp [S]
    exact mem_xiDivisorNearFinset
  have hQ_le : Q ≤ AQ * (1 + H) := by
    dsimp [Q, AQ]
    nlinarith [hB_nonneg, hH]
  have hR_scale : 1 + R ≤ AR * (1 + H) := by
    dsimp [R, Q, AR]
    nlinarith [hB_nonneg, hH]
  have hcard :
      ((S.card : ℝ) + 1) ≤ A * (1 + H) ^ (1 + ε) := by
    have hcard_mass :
        (S.card : ℝ) ≤
          Complex.Hadamard.divisorMassClosedBall₀ Complex.riemannXi R := by
      simpa [S] using xiDivisorNearFinset_card_le_divisorMassClosedBall₀ (R := R) hR_pos
    have hmassR :
        Complex.Hadamard.divisorMassClosedBall₀ Complex.riemannXi R
          ≤ Cmass * (1 + R) ^ (1 + ε) := hmass R hR_ge_one
    have hpow_scale :
        (1 + R) ^ (1 + ε) ≤ (AR * (1 + H)) ^ (1 + ε) := by
      exact Real.rpow_le_rpow (by positivity) hR_scale (by linarith)
    have hmul_rpow :
        (AR * (1 + H)) ^ (1 + ε) =
          AR ^ (1 + ε) * (1 + H) ^ (1 + ε) := by
      exact Real.mul_rpow (le_of_lt hAR_pos) (by linarith)
    have hcard_scaled :
        (S.card : ℝ) ≤
          (Cmass * AR ^ (1 + ε)) * (1 + H) ^ (1 + ε) := by
      calc
        (S.card : ℝ) ≤
            Complex.Hadamard.divisorMassClosedBall₀ Complex.riemannXi R := hcard_mass
        _ ≤ Cmass * (1 + R) ^ (1 + ε) := hmassR
        _ ≤ Cmass * (AR * (1 + H)) ^ (1 + ε) :=
              mul_le_mul_of_nonneg_left hpow_scale (le_of_lt hCmass_pos)
        _ = (Cmass * AR ^ (1 + ε)) * (1 + H) ^ (1 + ε) := by
              rw [hmul_rpow]
              ring
    have hX_ge_one : 1 ≤ (1 + H) ^ (1 + ε) := by
      have hbase_ge_one : 1 ≤ 1 + H := by linarith
      have hexp_nonneg : 0 ≤ 1 + ε := by linarith
      calc
        (1 : ℝ) = (1 : ℝ) ^ (1 + ε) := by rw [Real.one_rpow]
        _ ≤ (1 + H) ^ (1 + ε) :=
          Real.rpow_le_rpow zero_le_one hbase_ge_one hexp_nonneg
    calc
      ((S.card : ℝ) + 1)
          ≤ (Cmass * AR ^ (1 + ε)) * (1 + H) ^ (1 + ε) + 1 := by
            linarith
      _ ≤ (Cmass * AR ^ (1 + ε)) * (1 + H) ^ (1 + ε) +
            1 * (1 + H) ^ (1 + ε) := by
            nlinarith [hX_ge_one]
      _ = A * (1 + H) ^ (1 + ε) := by
            dsimp [A]
            ring
  have hexp_sel : (1 + ε) * (1 + θ) ≤ 1 + η := by
    dsimp [ε, θ]
    nlinarith [hη0, hη1]
  have hsigma_abs :
      ∀ σ : ℝ, σL ≤ σ → σ ≤ σR → |σ| ≤ B := by
    intro σ hL hRσ
    have hσL_abs : |σL| ≤ B := by dsimp [B]; exact le_max_left _ _
    have hσR_abs : |σR| ≤ B := by dsimp [B]; exact le_max_right _ _
    rw [abs_le]
    have hleft : -B ≤ σL := (abs_le.mp hσL_abs).1
    have hright : σR ≤ B := (abs_le.mp hσR_abs).2
    exact ⟨le_trans hleft hL, le_trans hRσ hright⟩
  have prove_branch : ∀ τ : ℝ, |τ| = T →
      ∀ σ : ℝ, σL ≤ σ → σ ≤ σR →
        ‖logDeriv Complex.riemannXi (σ + τ * Complex.I)‖
          ≤ Cξ * (1 + H) ^ (1 + η) := by
    intro τ hτ σ hσL hσR
    have hzQ : ‖(σ + τ * Complex.I : ℂ)‖ ≤ Q := by
      calc
        ‖(σ + τ * Complex.I : ℂ)‖
            ≤ |σ| + |τ| := by
              simpa using
                P4_4b.norm_complex_le_abs_re_add_abs_im
                  (σ + τ * Complex.I : ℂ)
        _ ≤ B + T := add_le_add (hsigma_abs σ hσL hσR) (le_of_eq hτ)
        _ ≤ B + (H + 1) := by linarith
        _ ≤ Q := by dsimp [Q]; linarith
    have hsep_pos : ∀ p ∈ S,
        0 < |T - (|(Complex.Hadamard.divisorZeroIndex₀_val p).im|)| := by
      intro p hp
      have hlower := hsep p hp
      have hbase_pos : 0 < ((S.card : ℝ) + 1) := by positivity
      have hpow_pos : 0 < ((S.card : ℝ) + 1) ^ (1 + θ) :=
        Real.rpow_pos_of_pos hbase_pos _
      have hden_pos : 0 < Kθ * ((S.card : ℝ) + 1) ^ (1 + θ) :=
        mul_pos hKθ_pos hpow_pos
      have hlower_pos :
          0 < 1 / (Kθ * ((S.card : ℝ) + 1) ^ (1 + θ)) := by positivity
      exact lt_of_lt_of_le hlower_pos hlower
    have hraw :=
      xi_logDeriv_horizontal_raw_bound (P := P) hPdeg hPfac
        (S := S) (σ := σ) (τ := τ) (T := T) (Q := Q) (R := R)
        (Bsel := Kθ * ((S.card : ℝ) + 1) ^ (1 + θ))
        hτ hQ_nonneg hR_def hzQ hS_mem hsep_pos hinvsum
    exact xi_logDeriv_horizontal_absorption
      (A := A) (K := Kθ) (AQ := AQ) (H := H) (ε := ε) (θ := θ) (η := η)
      (Bsel := Kθ * ((S.card : ℝ) + 1) ^ (1 + θ)) (Q := Q)
      (polyNorm := ‖Polynomial.eval 0 P.derivative‖) (S := S)
      hH hε_nonneg hθ_nonneg (le_of_lt hη0) hA_ge_one (le_of_lt hKθ_pos) hAQ_nonneg
      (norm_nonneg _) hcard le_rfl hQ_le hexp_sel hraw
  have hfree_nontrivial :
      ∀ ρ : ℂ, RHV3Lean.IsNontrivialZetaZero ρ → |ρ.im| ≠ T := by
    intro ρ hρ hheight
    obtain ⟨p, hpval⟩ :=
      P4_4b.exists_riemannXi_divisorZeroIndex₀_val_eq_of_isNontrivialZetaZero hρ
    have hstrip := RHV3Lean.isNontrivialZetaZero_re_mem_Ioo hρ
    have hre_abs : |ρ.re| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hstrip.1], le_of_lt hstrip.2⟩
    have hnormρ : ‖ρ‖ ≤ R := by
      calc
        ‖ρ‖ ≤ |ρ.re| + |ρ.im| := P4_4b.norm_complex_le_abs_re_add_abs_im ρ
        _ ≤ 1 + T := add_le_add hre_abs (le_of_eq hheight)
        _ ≤ H + 2 := by linarith
        _ ≤ R := by dsimp [R, Q]; nlinarith [hB_nonneg, hH]
    have hpS : p ∈ S := by
      exact (hS_mem p).2 (by simpa [hpval] using hnormρ)
    have hsep_p := hsep p hpS
    have hzero :
        |T - (|(Complex.Hadamard.divisorZeroIndex₀_val p).im|)| = 0 := by
      rw [hpval, hheight]
      simp
    have hbase_pos : 0 < ((S.card : ℝ) + 1) := by positivity
    have hpow_pos : 0 < ((S.card : ℝ) + 1) ^ (1 + θ) :=
      Real.rpow_pos_of_pos hbase_pos _
    have hden_pos : 0 < Kθ * ((S.card : ℝ) + 1) ^ (1 + θ) :=
      mul_pos hKθ_pos hpow_pos
    rw [hzero] at hsep_p
    have : 0 < 1 / (Kθ * ((S.card : ℝ) + 1) ^ (1 + θ)) := by positivity
    linarith
  refine ⟨T, hHT, hTH, hfree_nontrivial, ?_, ?_⟩
  · intro σ hσL hσR
    exact prove_branch T (abs_of_pos hT_pos) σ hσL hσR
  · intro σ hσL hσR
    have hneg : |(-T : ℝ)| = T := by rw [abs_neg, abs_of_pos hT_pos]
    have h := prove_branch (-T) hneg σ hσL hσR
    simpa [sub_eq_add_neg] using h

/-! ## Digamma on the horizontal Perron strip -/

lemma digamma_add_nat_eq (z : ℂ) :
    ∀ M : ℕ,
      (∀ k : ℕ, k < M → ∀ m : ℕ, z + (k : ℂ) ≠ -(m : ℂ)) →
        Complex.digamma (z + (M : ℂ)) =
          Complex.digamma z + ∑ k ∈ Finset.range M, (z + (k : ℂ))⁻¹ := by
  intro M
  induction M with
  | zero =>
      intro _hp
      simp
  | succ M ih =>
      intro hp
      have hpM : ∀ m : ℕ, z + (M : ℂ) ≠ -(m : ℂ) :=
        hp M (Nat.lt_succ_self M)
      have hprev : ∀ k : ℕ, k < M → ∀ m : ℕ, z + (k : ℂ) ≠ -(m : ℂ) := by
        intro k hk
        exact hp k (Nat.lt_trans hk (Nat.lt_succ_self M))
      have hstep := Complex.digamma_apply_add_one (z + (M : ℂ)) hpM
      calc
        Complex.digamma (z + (((M + 1 : ℕ) : ℝ) : ℂ))
            = Complex.digamma ((z + (M : ℂ)) + 1) := by
              norm_num
              ring
        _ = Complex.digamma (z + (M : ℂ)) + (z + (M : ℂ))⁻¹ := hstep
        _ = (Complex.digamma z + ∑ k ∈ Finset.range M, (z + (k : ℂ))⁻¹) +
              (z + (M : ℂ))⁻¹ := by
              rw [ih hprev]
        _ = Complex.digamma z +
              ∑ k ∈ Finset.range (M + 1), (z + (k : ℂ))⁻¹ := by
              rw [Finset.sum_range_succ]
              ring

theorem exists_horizontal_digamma_rpow_bound
    {N : ℕ} (hN : 1 ≤ N) {σR δ : ℝ} (hδ : 0 < δ) :
    ∃ CΓ : ℝ, 0 < CΓ ∧
      ∀ H : ℝ, 1 ≤ H → ∀ T : ℝ, H < T → T < H + 1 →
      ∀ τ : ℝ, |τ| = T →
      ∀ σ : ℝ, perronRectangleSigmaL N ≤ σ → σ ≤ σR →
        ‖Complex.digamma (((σ + τ * Complex.I : ℂ) / 2) + 1)‖
          ≤ CΓ * (1 + H) ^ δ := by
  classical
  let M : ℕ := N + 1
  let b : ℝ := max 2 (σR / 2 + (N : ℝ) + 2)
  obtain ⟨C0, hC0_pos, hC0⟩ :=
    Complex.exists_norm_digamma_le_log (a := 1) (b := b) one_pos
  let CΓ : ℝ := C0 * (Real.log 2 + 1 / δ) + 2 * (M : ℝ) + 1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
  have hCΓ_pos : 0 < CΓ := by
    dsimp [CΓ]
    positivity
  refine ⟨CΓ, hCΓ_pos, ?_⟩
  intro H hH T hHT hTH τ hτ σ hσL hσR
  let z : ℂ := ((σ + τ * Complex.I : ℂ) / 2) + 1
  let w : ℂ := z + (M : ℂ)
  have hT_pos : 0 < T := by linarith
  have hT_ge_one : 1 ≤ T := by linarith
  have hτ_ne : τ ≠ 0 := by
    intro hτ0
    have : |τ| = 0 := by simp [hτ0]
    linarith
  have hpoles : ∀ k : ℕ, k < M → ∀ m : ℕ, z + (k : ℂ) ≠ -(m : ℂ) := by
    intro k _hk m hbad
    have him0 : (z + (k : ℂ)).im = 0 := by
      rw [hbad]
      simp
    have him : (z + (k : ℂ)).im = τ / 2 := by
      simp [z]
    rw [him] at him0
    exact hτ_ne (by linarith)
  have hdig := digamma_add_nat_eq z M hpoles
  have hdig_z :
      Complex.digamma z =
        Complex.digamma w - ∑ k ∈ Finset.range M, (z + (k : ℂ))⁻¹ := by
    dsimp [w]
    rw [hdig]
    ring
  have hwre : w.re = σ / 2 + 1 + (M : ℝ) := by
    simp [w, z]
  have hwre_ge : 1 ≤ w.re := by
    rw [hwre]
    have hMcast : (M : ℝ) = (N : ℝ) + 1 := by
      dsimp [M]
      norm_num
    rw [hMcast]
    unfold perronRectangleSigmaL at hσL
    nlinarith [hσL]
  have hwre_le : w.re ≤ b := by
    rw [hwre]
    have hMcast : (M : ℝ) = (N : ℝ) + 1 := by
      dsimp [M]
      norm_num
    rw [hMcast]
    dsimp [b]
    have hb : σR / 2 + (N : ℝ) + 2 ≤
        max 2 (σR / 2 + (N : ℝ) + 2) := le_max_right _ _
    nlinarith [hσR, hb]
  have hwdig :
      ‖Complex.digamma w‖ ≤ C0 * Real.log (|w.im| + 2) :=
    hC0 w hwre_ge hwre_le
  have him_w_abs : |w.im| = T / 2 := by
    dsimp [w, z]
    simp [abs_div, hτ]
  have hlog_arg_le : |w.im| + 2 ≤ 2 * (1 + H) := by
    rw [him_w_abs]
    nlinarith
  have hX_ge_one : 1 ≤ (1 + H) ^ δ := by
    have hbase_ge_one : 1 ≤ 1 + H := by linarith
    calc
      (1 : ℝ) = (1 : ℝ) ^ δ := by rw [Real.one_rpow]
      _ ≤ (1 + H) ^ δ := Real.rpow_le_rpow zero_le_one hbase_ge_one hδ_nonneg
  have hlog_absorb :
      Real.log (|w.im| + 2) ≤
        (Real.log 2 + 1 / δ) * (1 + H) ^ δ := by
    have harg_pos : 0 < |w.im| + 2 := by positivity
    have htwoH_pos : 0 < 2 * (1 + H) := by positivity
    have hbase_pos : 0 < 1 + H := by linarith
    have hlogmono :
        Real.log (|w.im| + 2) ≤ Real.log (2 * (1 + H)) :=
      Real.log_le_log harg_pos hlog_arg_le
    have hlogmul : Real.log (2 * (1 + H)) = Real.log 2 + Real.log (1 + H) := by
      rw [Real.log_mul (by norm_num) hbase_pos.ne']
    have hlogH :
        Real.log (1 + H) ≤ (1 + H) ^ δ / δ :=
      Real.log_le_rpow_div (le_of_lt hbase_pos) hδ
    calc
      Real.log (|w.im| + 2) ≤ Real.log (2 * (1 + H)) := hlogmono
      _ = Real.log 2 + Real.log (1 + H) := hlogmul
      _ ≤ Real.log 2 + (1 + H) ^ δ / δ := by linarith
      _ ≤ (Real.log 2 + 1 / δ) * (1 + H) ^ δ := by
            have hX_nonneg : 0 ≤ (1 + H) ^ δ :=
              Real.rpow_nonneg (by linarith : 0 ≤ 1 + H) δ
            have hlog2_le : Real.log 2 ≤ Real.log 2 * (1 + H) ^ δ := by
              simpa [mul_one] using
                mul_le_mul_of_nonneg_left hX_ge_one (le_of_lt hlog2_pos)
            ring_nf
            nlinarith
  have hcorr_point : ∀ k ∈ Finset.range M,
      ‖(z + (k : ℂ))⁻¹‖ ≤ 2 := by
    intro k _hk
    have him_abs : |(z + (k : ℂ)).im| = T / 2 := by
      dsimp [z]
      simp [abs_div, hτ]
    have hnorm_lower : T / 2 ≤ ‖z + (k : ℂ)‖ := by
      calc
        T / 2 = |(z + (k : ℂ)).im| := him_abs.symm
        _ ≤ ‖z + (k : ℂ)‖ := Complex.abs_im_le_norm _
    have hhalf_pos : 0 < T / 2 := by positivity
    have hinv_le :
        1 / ‖z + (k : ℂ)‖ ≤ 1 / (T / 2) :=
      one_div_le_one_div_of_le hhalf_pos hnorm_lower
    calc
      ‖(z + (k : ℂ))⁻¹‖ = 1 / ‖z + (k : ℂ)‖ := by
        simpa [one_div] using norm_inv (z + (k : ℂ))
      _ ≤ 1 / (T / 2) := hinv_le
      _ = 2 / T := by field_simp [ne_of_gt hT_pos]
      _ ≤ 2 := by
        rw [div_le_iff₀ hT_pos]
        nlinarith
  have hcorr :
      ‖∑ k ∈ Finset.range M, (z + (k : ℂ))⁻¹‖ ≤ 2 * (M : ℝ) := by
    calc
      ‖∑ k ∈ Finset.range M, (z + (k : ℂ))⁻¹‖
          ≤ ∑ k ∈ Finset.range M, ‖(z + (k : ℂ))⁻¹‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range M, (2 : ℝ) :=
            Finset.sum_le_sum (fun k hk => hcorr_point k hk)
      _ = 2 * (M : ℝ) := by
            simp [nsmul_eq_mul]
            ring
  have hmain :
      ‖Complex.digamma z‖ ≤ C0 * ((Real.log 2 + 1 / δ) * (1 + H) ^ δ) +
          2 * (M : ℝ) := by
    rw [hdig_z]
    calc
      ‖Complex.digamma w - ∑ k ∈ Finset.range M, (z + (k : ℂ))⁻¹‖
          ≤ ‖Complex.digamma w‖ +
              ‖∑ k ∈ Finset.range M, (z + (k : ℂ))⁻¹‖ := norm_sub_le _ _
      _ ≤ C0 * Real.log (|w.im| + 2) + 2 * (M : ℝ) := by
            exact add_le_add hwdig hcorr
      _ ≤ C0 * ((Real.log 2 + 1 / δ) * (1 + H) ^ δ) + 2 * (M : ℝ) := by
            gcongr
  calc
    ‖Complex.digamma (((σ + τ * Complex.I : ℂ) / 2) + 1)‖
        = ‖Complex.digamma z‖ := by rfl
    _ ≤ C0 * ((Real.log 2 + 1 / δ) * (1 + H) ^ δ) + 2 * (M : ℝ) := hmain
    _ ≤ CΓ * (1 + H) ^ δ := by
          dsimp [CΓ]
          have hX_nonneg : 0 ≤ (1 + H) ^ δ :=
            Real.rpow_nonneg (by linarith : 0 ≤ 1 + H) δ
          have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
          nlinarith [hX_ge_one, hC0_pos, hlog2_pos, hM_nonneg]

/-! ## Bridge from `ξ'/ξ` to `-ζ'/ζ` on the horizontal segments -/

lemma horizontal_neg_zeta_logDeriv_norm_le_of_xi_digamma
    {Cξ CΓ H η T τ σ : ℝ}
    (hCξ_nonneg : 0 ≤ Cξ) (hCΓ_nonneg : 0 ≤ CΓ)
    (hH : 1 ≤ H) (hη0 : 0 < η) (hT : 1 ≤ T) (hτ : |τ| = T)
    (hxi :
      ‖logDeriv Complex.riemannXi (σ + τ * Complex.I)‖
        ≤ Cξ * (1 + H) ^ (1 + η))
    (hdig :
      ‖Complex.digamma (((σ + τ * Complex.I : ℂ) / 2) + 1)‖
        ≤ CΓ * (1 + H) ^ η) :
    ‖-deriv riemannZeta (σ + τ * Complex.I) /
        riemannZeta (σ + τ * Complex.I)‖
      ≤ (Cξ + CΓ + ‖(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖ + 2) *
          (1 + H) ^ (1 + η) := by
  let s : ℂ := σ + τ * Complex.I
  have hbase_ge_one : 1 ≤ 1 + H := by linarith
  have hbase_nonneg : 0 ≤ 1 + H := by linarith
  have hη_nonneg : 0 ≤ η := le_of_lt hη0
  have hX_nonneg : 0 ≤ (1 + H) ^ (1 + η) :=
    Real.rpow_nonneg hbase_nonneg _
  have hX_ge_one : 1 ≤ (1 + H) ^ (1 + η) := by
    calc
      (1 : ℝ) = (1 : ℝ) ^ (1 + η) := by rw [Real.one_rpow]
      _ ≤ (1 + H) ^ (1 + η) :=
        Real.rpow_le_rpow zero_le_one hbase_ge_one (by linarith)
  have hY_le_X : (1 + H) ^ η ≤ (1 + H) ^ (1 + η) :=
    Real.rpow_le_rpow_of_exponent_le hbase_ge_one (by linarith)
  by_cases hζ : riemannZeta s = 0
  · have hzero :
        -deriv riemannZeta s / riemannZeta s = 0 := by
      simp [hζ]
    rw [show σ + τ * Complex.I = s by rfl, hzero]
    have hconst_nonneg :
        0 ≤ Cξ + CΓ + ‖(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖ + 2 := by
      positivity
    simpa using mul_nonneg hconst_nonneg hX_nonneg
  · have hτ_ne : τ ≠ 0 := by
      intro hτ0
      have : |τ| = 0 := by simp [hτ0]
      linarith
    have hsim : s.im ≠ 0 := by
      dsimp [s]
      simpa using hτ_ne
    have hs1 : s ≠ 1 := by
      intro hs
      have him0 : s.im = 0 := by rw [hs]; simp
      exact hsim him0
    have hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) := by
      intro m hbad
      have him0 : (s / 2 + 1).im = 0 := by
        rw [hbad]
        simp
      have him : (s / 2 + 1).im = τ / 2 := by
        dsimp [s]
        simp
      rw [him] at him0
      exact hτ_ne (by linarith)
    have hΓ : Kadiri.zetaGammaFactor s ≠ 0 := by
      simpa [Kadiri.zetaGammaFactor] using Complex.Gamma_ne_zero hΓdiff
    have hbridge :=
      Kadiri.neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv s hs1 hΓdiff hΓ hζ
    have hcompnorm :
        ‖-logDeriv Kadiri.completedZetaFactor s‖ =
          ‖logDeriv Complex.riemannXi s‖ := by
      rw [logDeriv_completedZetaFactor_eq_riemannXi_of_im_ne_zero hsim]
      simp
    have hpole_norm :
        ‖1 / (s - 1)‖ ≤ 1 := by
      have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
      have him_abs : |(s - 1).im| = T := by
        dsimp [s]
        simp [hτ]
      have hnorm_lower : T ≤ ‖s - 1‖ := by
        calc
          T = |(s - 1).im| := him_abs.symm
          _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
      have hinv_le : 1 / ‖s - 1‖ ≤ 1 / T :=
        one_div_le_one_div_of_le hTpos hnorm_lower
      calc
        ‖1 / (s - 1)‖ = 1 / ‖s - 1‖ := by
          simpa [one_div] using norm_inv (s - 1)
        _ ≤ 1 / T := hinv_le
        _ ≤ 1 := by
          rw [div_le_iff₀ hTpos]
          linarith
    have hgamma_norm :
        ‖(1 / 2 : ℂ) *
            Complex.digamma (((σ + τ * Complex.I : ℂ) / 2) + 1)‖
          ≤ CΓ * (1 + H) ^ (1 + η) := by
      calc
        ‖(1 / 2 : ℂ) *
            Complex.digamma (((σ + τ * Complex.I : ℂ) / 2) + 1)‖
            = ‖(1 / 2 : ℂ)‖ *
                ‖Complex.digamma (((σ + τ * Complex.I : ℂ) / 2) + 1)‖ := norm_mul _ _
        _ ≤ 1 *
                ‖Complex.digamma (((σ + τ * Complex.I : ℂ) / 2) + 1)‖ := by
              exact mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)
        _ ≤ CΓ * (1 + H) ^ η := by
              simpa using hdig
        _ ≤ CΓ * (1 + H) ^ (1 + η) :=
              mul_le_mul_of_nonneg_left hY_le_X hCΓ_nonneg
    have hnorm_split :
        ‖-logDeriv Kadiri.completedZetaFactor s + 1 / (s - 1)
            - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ)
            + (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1)‖
          ≤ ‖-logDeriv Kadiri.completedZetaFactor s‖
            + ‖1 / (s - 1)‖
            + ‖(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖
            + ‖(1 / 2 : ℂ) * Complex.digamma (s / 2 + 1)‖ := by
      calc
        ‖-logDeriv Kadiri.completedZetaFactor s + 1 / (s - 1)
            - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ)
            + (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1)‖
            ≤ ‖-logDeriv Kadiri.completedZetaFactor s + 1 / (s - 1)
                - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖
              + ‖(1 / 2 : ℂ) * Complex.digamma (s / 2 + 1)‖ := norm_add_le _ _
        _ ≤ (‖-logDeriv Kadiri.completedZetaFactor s + 1 / (s - 1)‖
              + ‖(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖)
              + ‖(1 / 2 : ℂ) * Complex.digamma (s / 2 + 1)‖ := by
              gcongr
              simpa [sub_eq_add_neg] using
                norm_add_le (-logDeriv Kadiri.completedZetaFactor s + 1 / (s - 1))
                  (-(1 / 2 : ℂ) * (Real.log Real.pi : ℂ))
        _ ≤ (‖-logDeriv Kadiri.completedZetaFactor s‖ + ‖1 / (s - 1)‖
              + ‖(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖)
              + ‖(1 / 2 : ℂ) * Complex.digamma (s / 2 + 1)‖ := by
              gcongr
              exact norm_add_le _ _
        _ = ‖-logDeriv Kadiri.completedZetaFactor s‖
            + ‖1 / (s - 1)‖
            + ‖(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖
            + ‖(1 / 2 : ℂ) * Complex.digamma (s / 2 + 1)‖ := by ring
    rw [show σ + τ * Complex.I = s by rfl, hbridge]
    have hpi_abs :
        ‖(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖
          ≤ ‖(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖ *
              (1 + H) ^ (1 + η) := by
      simpa [mul_one] using
        mul_le_mul_of_nonneg_left hX_ge_one
          (norm_nonneg ((1 / 2 : ℂ) * (Real.log Real.pi : ℂ)))
    have hpole_abs : ‖1 / (s - 1)‖ ≤ 1 * (1 + H) ^ (1 + η) := by
      calc
        ‖1 / (s - 1)‖ ≤ 1 := hpole_norm
        _ ≤ 1 * (1 + H) ^ (1 + η) := by simpa using hX_ge_one
    have hgamma_abs :
        ‖(1 / 2 : ℂ) * Complex.digamma (s / 2 + 1)‖
          ≤ CΓ * (1 + H) ^ (1 + η) := by
      simpa [s] using hgamma_norm
    have hxi_abs :
        ‖-logDeriv Kadiri.completedZetaFactor s‖
          ≤ Cξ * (1 + H) ^ (1 + η) := by
      rw [hcompnorm]
      simpa [s] using hxi
    calc
      ‖-logDeriv Kadiri.completedZetaFactor s + 1 / (s - 1)
          - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ)
          + (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1)‖
          ≤ ‖-logDeriv Kadiri.completedZetaFactor s‖
            + ‖1 / (s - 1)‖
            + ‖(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖
            + ‖(1 / 2 : ℂ) * Complex.digamma (s / 2 + 1)‖ := hnorm_split
      _ ≤ Cξ * (1 + H) ^ (1 + η)
            + 1 * (1 + H) ^ (1 + η)
            + ‖(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖ *
                (1 + H) ^ (1 + η)
            + CΓ * (1 + H) ^ (1 + η) := by
            linarith
      _ ≤ (Cξ + CΓ + ‖(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖ + 2) *
            (1 + H) ^ (1 + η) := by
            ring_nf
            nlinarith [hX_nonneg]

theorem exists_perron_height_with_horizontal_negLogDeriv_bound
    {x σR : ℝ} {N : ℕ}
    (hx : 1 < x)
    (hσR : 1 < σR)
    (hN : 1 ≤ N)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ H : ℝ, 1 ≤ H →
        ∃ T : ℝ,
          H < T ∧
          T < H + 1 ∧
          RHV3Lean.PerronRectangleAdmissible x σR N T ∧
          (∀ σ : ℝ,
            RHV3Lean.perronRectangleSigmaL N ≤ σ →
            σ ≤ σR →
            ‖-deriv riemannZeta (σ + T * Complex.I) /
                riemannZeta (σ + T * Complex.I)‖
              ≤ C * (1 + H) ^ (1 + η)) ∧
          (∀ σ : ℝ,
            RHV3Lean.perronRectangleSigmaL N ≤ σ →
            σ ≤ σR →
            ‖-deriv riemannZeta (σ - T * Complex.I) /
                riemannZeta (σ - T * Complex.I)‖
              ≤ C * (1 + H) ^ (1 + η)) := by
  classical
  have hσLR : RHV3Lean.perronRectangleSigmaL N ≤ σR := by
    unfold RHV3Lean.perronRectangleSigmaL
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [hNreal, hσR]
  obtain ⟨Cξ, hCξ_pos, hxi_all⟩ :=
    xi_horizontal_logDeriv_bound_from_quantitative_hadamard
      (σL := RHV3Lean.perronRectangleSigmaL N) (σR := σR) hσLR η hη0 hη1
  obtain ⟨CΓ, hCΓ_pos, hdig_all⟩ :=
    exists_horizontal_digamma_rpow_bound (N := N) hN (σR := σR) (δ := η) hη0
  let C : ℝ := Cξ + CΓ + ‖(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖ + 2
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro H hH
  obtain ⟨T, hHT, hTH, hfree, hxi_plus, hxi_minus⟩ := hxi_all H hH
  have hT_pos : 0 < T := by linarith
  have hT_ge_one : 1 ≤ T := by linarith
  have hadm : RHV3Lean.PerronRectangleAdmissible x σR N T :=
    RHV3Lean.perronRectangleAdmissible_of_zero_free_height hx hσR hN hT_pos hfree
  refine ⟨T, hHT, hTH, hadm, ?_, ?_⟩
  · intro σ hσL hσRσ
    have hdig :=
      hdig_all H hH T hHT hTH T (abs_of_pos hT_pos) σ hσL hσRσ
    have hbound :=
      horizontal_neg_zeta_logDeriv_norm_le_of_xi_digamma
        (Cξ := Cξ) (CΓ := CΓ) (H := H) (η := η) (T := T) (τ := T) (σ := σ)
        (le_of_lt hCξ_pos) (le_of_lt hCΓ_pos) hH hη0 hT_ge_one
        (abs_of_pos hT_pos) (hxi_plus σ hσL hσRσ) hdig
    simpa [C] using hbound
  · intro σ hσL hσRσ
    have hτ : |(-T : ℝ)| = T := by rw [abs_neg, abs_of_pos hT_pos]
    have hdig :=
      hdig_all H hH T hHT hTH (-T) hτ σ hσL hσRσ
    have hbound :=
      horizontal_neg_zeta_logDeriv_norm_le_of_xi_digamma
        (Cξ := Cξ) (CΓ := CΓ) (H := H) (η := η) (T := T) (τ := -T) (σ := σ)
        (le_of_lt hCξ_pos) (le_of_lt hCΓ_pos) hH hη0 hT_ge_one
        hτ (by simpa [sub_eq_add_neg] using hxi_minus σ hσL hσRσ) hdig
    simpa [C, sub_eq_add_neg] using hbound

end P4_4c

end RHV3Lean
