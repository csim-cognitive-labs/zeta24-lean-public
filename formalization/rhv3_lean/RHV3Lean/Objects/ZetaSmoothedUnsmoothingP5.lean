/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.ZetaSmoothedZeroFormulaP5
import Mathlib.NumberTheory.Chebyshev

/-!
# P5.2 — exact arithmetic unsmoothing of the smoothed formula
-/

open Finset BigOperators ArithmeticFunction MeasureTheory

noncomputable section

namespace RHV3Lean

noncomputable def smoothedMangoldtPrimitive (x : ℝ) : ℂ :=
  (x : ℂ) * smoothedVonMangoldtSum x

private lemma smoothed_mangoldt_weight_difference
    (N n : ℕ)
    (hn : n < N) :
    ((N : ℂ) + 1) *
        ((Λ n : ℂ) * (1 - (n : ℂ) / ((N : ℂ) + 1))) -
      (N : ℂ) *
        ((Λ n : ℂ) * (1 - (n : ℂ) / (N : ℂ)))
      =
    (Λ n : ℂ) := by
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le n) hn
  have hN0 : (N : ℂ) ≠ 0 := by
    exact_mod_cast hNpos.ne'
  have hNp1 : (N : ℂ) + 1 ≠ 0 := by
    have h : ((N + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero N)
    simpa [Nat.cast_add, Nat.cast_one] using h
  field_simp [hN0, hNp1]
  ring

private lemma smoothed_mangoldt_new_weight
    (N : ℕ) :
    ((N : ℂ) + 1) *
        ((Λ N : ℂ) * (1 - (N : ℂ) / ((N : ℂ) + 1)))
      =
    (Λ N : ℂ) := by
  have hNp1 : (N : ℂ) + 1 ≠ 0 := by
    have h : ((N + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero N)
    simpa [Nat.cast_add, Nat.cast_one] using h
  field_simp [hNp1]
  ring

theorem smoothedMangoldtPrimitive_nat_difference
    (N : ℕ) :
    smoothedMangoldtPrimitive (N + 1)
      - smoothedMangoldtPrimitive N
      =
    (Chebyshev.psi (N : ℝ) : ℂ) := by
  unfold smoothedMangoldtPrimitive smoothedVonMangoldtSum
  rw [Chebyshev.psi_eq_sum_Icc]
  have hceil_succ : ⌈((N : ℝ) + 1)⌉₊ = N + 1 := by
    rw [Nat.ceil_add_one]
    · simp
    · exact_mod_cast Nat.zero_le N
  rw [hceil_succ, Nat.ceil_natCast, Nat.floor_natCast]
  have hIcc : Finset.Icc 0 N = Finset.range (N + 1) := by
    ext n
    simp
  rw [hIcc]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  rw [mul_add, mul_sum, mul_sum]
  norm_num [Nat.cast_add, Nat.cast_one]
  calc
    (∑ i ∈ range N,
          ((N : ℂ) + 1) *
            ((Λ i : ℂ) * (1 - (i : ℂ) / ((N : ℂ) + 1)))) +
        ((N : ℂ) + 1) *
          ((Λ N : ℂ) * (1 - (N : ℂ) / ((N : ℂ) + 1))) -
        ∑ i ∈ range N,
          (N : ℂ) *
            ((Λ i : ℂ) * (1 - (i : ℂ) / (N : ℂ)))
        =
      (∑ i ∈ range N,
          (((N : ℂ) + 1) *
            ((Λ i : ℂ) * (1 - (i : ℂ) / ((N : ℂ) + 1))) -
          (N : ℂ) *
            ((Λ i : ℂ) * (1 - (i : ℂ) / (N : ℂ))))) +
        ((N : ℂ) + 1) *
          ((Λ N : ℂ) * (1 - (N : ℂ) / ((N : ℂ) + 1))) := by
          rw [Finset.sum_sub_distrib]
          abel
    _ =
      (∑ i ∈ range N, (Λ i : ℂ)) + (Λ N : ℂ) := by
        rw [smoothed_mangoldt_new_weight N]
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        exact smoothed_mangoldt_weight_difference N n (Finset.mem_range.mp hn)

noncomputable def smoothedZeroPrimitive (x : ℝ) : ℂ :=
  (x : ℂ) * smoothedZeroFormula x

theorem smoothedZeroPrimitive_eq_arithmetic
    {x : ℝ}
    (hx : 1 < x) :
    smoothedZeroPrimitive x =
      smoothedMangoldtPrimitive x := by
  unfold smoothedZeroPrimitive smoothedMangoldtPrimitive
  rw [smoothedZeroFormula_eq_smoothedVonMangoldtSum hx]

theorem smoothedZeroPrimitive_nat_difference
    {N : ℕ}
    (hN : 2 ≤ N) :
    smoothedZeroPrimitive (N + 1)
      - smoothedZeroPrimitive N
      =
    (Chebyshev.psi (N : ℝ) : ℂ) := by
  have hN_gt_one : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN_succ_gt_one : (1 : ℝ) < (N : ℝ) + 1 := by linarith
  rw [smoothedZeroPrimitive_eq_arithmetic hN_succ_gt_one,
    smoothedZeroPrimitive_eq_arithmetic hN_gt_one,
    smoothedMangoldtPrimitive_nat_difference N]

noncomputable def psiRecoveredFromZeros (x : ℝ) : ℂ :=
  smoothedZeroPrimitive (⌊x⌋₊ + 1)
    - smoothedZeroPrimitive ⌊x⌋₊

private theorem chebyshev_psi_floor_eq
    (x : ℝ) :
    Chebyshev.psi (⌊x⌋₊ : ℝ) = Chebyshev.psi x := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc]
  simp [Nat.floor_natCast]

theorem psiRecoveredFromZeros_eq_psi
    {x : ℝ}
    (hx : 2 ≤ x) :
    psiRecoveredFromZeros x =
      (Chebyshev.psi x : ℂ) := by
  unfold psiRecoveredFromZeros
  have hfloor : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  rw [smoothedZeroPrimitive_nat_difference hfloor]
  exact congrArg (fun y : ℝ => (y : ℂ)) (chebyshev_psi_floor_eq x)

noncomputable def PiMangoldtFromZeros (x : ℝ) : ℝ :=
  (Real.log x)⁻¹ * (psiRecoveredFromZeros x).re
    - ∫ t in 2..x,
        (-t⁻¹ / Real.log t ^ 2) *
          (psiRecoveredFromZeros t).re

end RHV3Lean
