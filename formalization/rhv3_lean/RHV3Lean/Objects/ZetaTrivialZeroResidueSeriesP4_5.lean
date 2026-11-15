/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaTrivialZeroSimplicityP4_5
import RHV3Lean.Objects.ZetaPerronFiniteResidues

/-!
# P4.5 trivial zero residue series
-/

open Complex Set Filter Finset BigOperators
open scoped Topology

noncomputable section

namespace RHV3Lean

noncomputable def trivialZeroResidueTerm
    (x : ℝ)
    (n : ℕ) :
    ℂ :=
  -(zetaZeroMultiplicity (trivialZetaZeroAt n) : ℂ) *
    Perron.f x (trivialZetaZeroAt n)

theorem trivial_zero_residue_term_eq
    {x : ℝ}
    (_hx : 1 < x)
    (n : ℕ) :
    trivialZeroResidueTerm x n =
      -Perron.f x (trivialZetaZeroAt n) := by
  simp [trivialZeroResidueTerm, zetaZeroMultiplicity_trivialZetaZeroAt]

private theorem trivialZetaZeroAt_mul_succ
    (n : ℕ) :
    trivialZetaZeroAt n = -((2 * (n + 1) : ℕ) : ℂ) := by
  unfold trivialZetaZeroAt
  norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one]

private lemma perronRectangle_re_le_for_trivial_series
    {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    (perronRectangleLowerLeft N T).re ≤ (perronRectangleUpperRight σR T).re := by
  simp [perronRectangleLowerLeft, perronRectangleUpperRight, perronRectangleSigmaL]
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast h.N_ge_one
  nlinarith [h.sigmaR_gt]

private lemma perronRectangle_im_le_for_trivial_series
    {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    (perronRectangleLowerLeft N T).im ≤ (perronRectangleUpperRight σR T).im := by
  simp [perronRectangleLowerLeft, perronRectangleUpperRight]
  linarith [h.T_pos]

private theorem one_le_norm_trivial_denominator
    (n : ℕ) :
    1 ≤ ‖trivialZetaZeroAt n * (trivialZetaZeroAt n + 1)‖ := by
  have hnorm₁ : ‖trivialZetaZeroAt n‖ = (2 * (n + 1) : ℝ) := by
    rw [trivialZetaZeroAt_mul_succ, norm_neg, Complex.norm_natCast]
    norm_num
  have hnorm₂ : ‖trivialZetaZeroAt n + 1‖ = (2 * (n + 1) - 1 : ℝ) := by
    rw [trivialZetaZeroAt_mul_succ]
    have hcast :
        -(((2 * (n + 1) : ℕ) : ℂ)) + 1 =
          (((1 : ℝ) - (2 * (n + 1) : ℝ) : ℝ) : ℂ) := by
      norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    have hnonpos : (1 : ℝ) - (2 * (n + 1) : ℝ) ≤ 0 := by
      have hn : (1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      nlinarith
    rw [abs_of_nonpos hnonpos]
    ring
  rw [norm_mul, hnorm₁, hnorm₂]
  have hn : (1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  nlinarith

private noncomputable def trivialResidueGeometricRatio (x : ℝ) : ℝ :=
  (x ^ (2 : ℕ))⁻¹

private theorem norm_perron_f_trivial_le_geometric
    {x : ℝ}
    (hx : 1 < x)
    (n : ℕ) :
    ‖Perron.f x (trivialZetaZeroAt n)‖ ≤ trivialResidueGeometricRatio x ^ (n + 1) := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hden : 1 ≤ ‖trivialZetaZeroAt n * (trivialZetaZeroAt n + 1)‖ :=
    one_le_norm_trivial_denominator n
  have hden_pos : 0 < ‖trivialZetaZeroAt n * (trivialZetaZeroAt n + 1)‖ :=
    lt_of_lt_of_le zero_lt_one hden
  have hpow :
      ‖(x : ℂ) ^ trivialZetaZeroAt n‖ =
        trivialResidueGeometricRatio x ^ (n + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp [trivialZetaZeroAt]
    have hreal :
        x ^ (-(2 * ((n : ℝ) + 1))) =
          trivialResidueGeometricRatio x ^ (n + 1) := by
      rw [Real.rpow_neg hxpos.le]
      have hpow2 : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by norm_num
      rw [show x ^ (2 * ((n : ℝ) + 1)) = (x ^ (2 : ℝ)) ^ (n + 1 : ℕ) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
        congr 1
        norm_num [Nat.cast_add, Nat.cast_one]]
      rw [hpow2]
      simp [trivialResidueGeometricRatio, inv_pow]
    simpa using hreal
  calc
    ‖Perron.f x (trivialZetaZeroAt n)‖
        = ‖(x : ℂ) ^ trivialZetaZeroAt n‖ /
            ‖trivialZetaZeroAt n * (trivialZetaZeroAt n + 1)‖ := by
          simp [Perron.f]
    _ ≤ ‖(x : ℂ) ^ trivialZetaZeroAt n‖ / 1 := by
          exact div_le_div_of_nonneg_left (norm_nonneg _) zero_lt_one hden
    _ = trivialResidueGeometricRatio x ^ (n + 1) := by simp [hpow]

theorem trivial_zero_residue_series_summable
    {x : ℝ}
    (hx : 1 < x) :
    Summable
      (fun n : ℕ =>
        trivialZeroResidueTerm x n) := by
  have hq_nonneg : 0 ≤ trivialResidueGeometricRatio x := by
    simp [trivialResidueGeometricRatio]
    positivity
  have hq_lt_one : trivialResidueGeometricRatio x < 1 := by
    have hxpos : 0 < x := lt_trans zero_lt_one hx
    have hx2 : 1 < x ^ (2 : ℕ) := one_lt_pow₀ hx (by norm_num)
    rw [trivialResidueGeometricRatio, inv_lt_one_iff₀]
    exact Or.inr hx2
  have hgeom : Summable (fun n : ℕ => trivialResidueGeometricRatio x ^ (n + 1)) :=
    by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (summable_nat_add_iff (f := fun n : ℕ => trivialResidueGeometricRatio x ^ n) (k := 1)).mpr
          (summable_geometric_of_lt_one hq_nonneg hq_lt_one)
  refine Summable.of_norm_bounded hgeom ?_
  intro n
  rw [trivial_zero_residue_term_eq hx n]
  simpa using norm_perron_f_trivial_le_geometric (x := x) hx n

theorem trivial_zero_residue_partial_sums_tendsto
    {x : ℝ}
    (hx : 1 < x) :
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N,
          trivialZeroResidueTerm x n)
      atTop
      (𝓝
        (∑' n : ℕ,
        trivialZeroResidueTerm x n)) :=
  (trivial_zero_residue_series_summable hx).tendsto_sum_tsum_nat

theorem trivialZetaZeroAt_mem_rectangle_iff
    {x σR T : ℝ}
    {N n : ℕ}
    (h : PerronRectangleAdmissible x σR N T) :
    trivialZetaZeroAt n ∈
        zetaPerronTrivialZeroSet σR N T
      ↔
    n < N := by
  constructor
  · intro hmem
    have hrect := hmem.1
    rw [mem_Rect (perronRectangle_re_le_for_trivial_series h)
      (perronRectangle_im_le_for_trivial_series h)] at hrect
    simp [perronRectangleLowerLeft, perronRectangleUpperRight, perronRectangleSigmaL,
      trivialZetaZeroAt] at hrect
    by_contra hnlt
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast Nat.le_of_not_gt hnlt
    nlinarith [hrect.1]
  · intro hn
    constructor
    · rw [mem_Rect (perronRectangle_re_le_for_trivial_series h)
        (perronRectangle_im_le_for_trivial_series h)]
      simp [perronRectangleLowerLeft, perronRectangleUpperRight, perronRectangleSigmaL,
        trivialZetaZeroAt]
      have hnN : (n + 1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hn
      constructor
      · nlinarith
      · constructor
        · nlinarith [h.sigmaR_gt]
        · linarith [h.T_pos]
    · exact ⟨n, by simp [trivialZetaZeroAt]⟩

private theorem trivialZetaZeroAt_injective :
    Function.Injective trivialZetaZeroAt := by
  intro m n hmn
  have hre := congrArg Complex.re hmn
  simp [trivialZetaZeroAt, Nat.cast_add, Nat.cast_one] at hre
  exact hre

theorem zetaPerron_trivial_zero_residue_sum_eq_range
    {x σR T : ℝ}
    {N : ℕ}
    (h : PerronRectangleAdmissible x σR N T) :
    sumResiduesIn
        (zetaPerronIntegrand x)
        (zetaPerronTrivialZeroSet σR N T)
      =
    ∑ n ∈ Finset.range N,
      trivialZeroResidueTerm x n := by
  classical
  rw [zetaPerron_trivial_zero_residue_sum h.x_gt]
  have hfin : (zetaPerronTrivialZeroSet σR N T).Finite :=
    zetaPerron_trivial_zero_set_finite σR N T
  haveI : Fintype (zetaPerronTrivialZeroSet σR N T) := hfin.fintype
  rw [tsum_fintype]
  calc
    ∑ b : zetaPerronTrivialZeroSet σR N T,
        -↑(zetaZeroMultiplicity ↑b) * Perron.f x ↑b
        =
      ∑ ρ ∈ hfin.toFinset,
        -(zetaZeroMultiplicity ρ : ℂ) * Perron.f x ρ :=
        (Finset.sum_subtype (s := hfin.toFinset)
          (p := fun ρ ↦ ρ ∈ zetaPerronTrivialZeroSet σR N T)
          (f := fun ρ ↦
            -(zetaZeroMultiplicity ρ : ℂ) * Perron.f x ρ)
          (by simp)).symm
    _ =
      ∑ n ∈ Finset.range N,
        trivialZeroResidueTerm x n := by
        symm
        refine Finset.sum_bij
          (fun n _ ↦ trivialZetaZeroAt n)
          ?hmem ?hinj ?hsurj ?hterm
        · intro n hn
          rw [hfin.mem_toFinset]
          exact (trivialZetaZeroAt_mem_rectangle_iff h).mpr (Finset.mem_range.mp hn)
        · intro n₁ hn₁ n₂ hn₂ heq
          exact trivialZetaZeroAt_injective heq
        · intro ρ hρ
          have hρset : ρ ∈ zetaPerronTrivialZeroSet σR N T := by
            rw [hfin.mem_toFinset] at hρ
            exact hρ
          rcases hρset.2 with ⟨n, hnρ⟩
          have hρeq : ρ = trivialZetaZeroAt n := by
            simpa [trivialZetaZeroAt] using hnρ
          refine ⟨n, ?_, hρeq.symm⟩
          rw [Finset.mem_range]
          rw [← trivialZetaZeroAt_mem_rectangle_iff h]
          simpa [hρeq] using hρset
        · intro n hn
          rfl

end RHV3Lean
