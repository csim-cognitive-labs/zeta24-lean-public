/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.P4Port.IEANTN.KadiriZeroCounting
import RHV3Lean.Objects.ZetaPerronFiniteResidues

/-!
# P4.2: canonical height truncation of non-trivial zeta zeros

This file connects the local non-trivial-zero predicate to Kadiri's source
representation and defines the canonical symmetric strict height truncation.
-/

open Set Filter Finset BigOperators Complex
open scoped Topology ComplexConjugate

namespace RHV3Lean

private lemma complex_eq_of_im_eq_zero (z : ℂ) (hz : z.im = 0) :
    z = ((z.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [hz]

private lemma int_one_le_of_real_le_neg_one {k : ℤ} {σ : ℝ}
    (hσ : σ = -(2 * (k : ℝ))) (hle : σ ≤ -1) :
    1 ≤ k := by
  by_contra hk
  push Not at hk
  have hk0 : k ≤ 0 := by omega
  have hkreal : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
  have hnonneg : 0 ≤ -(2 * (k : ℝ)) := by nlinarith
  linarith

private lemma isTrivialZetaZero_of_real_cos_eq_zero
    {ρ : ℂ} (him : ρ.im = 0) (hre_le : ρ.re ≤ -1)
    (hcos : Complex.cos (↑Real.pi * ((1 - ρ.re : ℝ) : ℂ) / 2) = 0) :
    IsTrivialZetaZero ρ := by
  have hnot : ¬ ∀ k : ℤ,
      ↑Real.pi * ((1 - ρ.re : ℝ) : ℂ) / 2 ≠ (2 * k + 1) * ↑Real.pi / 2 := by
    intro hall
    exact (Complex.cos_ne_zero_iff.mpr hall) hcos
  push Not at hnot
  obtain ⟨k, hk⟩ := hnot
  have hre_eq : ρ.re = -(2 * (k : ℝ)) := by
    have h_re := congrArg Complex.re hk
    have hscaled :
        Real.pi * (1 - ρ.re) / 2 =
          (2 * (k : ℝ) + 1) * Real.pi / 2 := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h_re
    have hmain : 1 - ρ.re = 2 * (k : ℝ) + 1 := by
      nlinarith [Real.pi_pos]
    linarith
  have hk_one : 1 ≤ k := int_one_le_of_real_le_neg_one hre_eq hre_le
  let n : ℕ := (k - 1).toNat
  have hk_nat : (n : ℤ) = k - 1 := by
    dsimp [n]
    rw [Int.toNat_of_nonneg]
    omega
  refine ⟨n, ?_⟩
  have hρreal : ρ = ((ρ.re : ℝ) : ℂ) := complex_eq_of_im_eq_zero ρ him
  rw [hρreal, hre_eq]
  apply Complex.ext
  · simp
    have : (n : ℝ) = (k : ℝ) - 1 := by exact_mod_cast hk_nat
    nlinarith
  · simp

private lemma riemannZeta_ne_zero_of_real_nontrivial_left
    {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) (him : ρ.im = 0) (hre : ρ.re ≤ 0) :
    False := by
  have hρreal : ρ = ((ρ.re : ℝ) : ℂ) := complex_eq_of_im_eq_zero ρ him
  by_cases hnear : -1 < ρ.re
  · have hnz := Kadiri.riemannZeta_ne_zero_of_real_neg hnear hre
    have hzreal : riemannZeta ((ρ.re : ℝ) : ℂ) = 0 := by
      rw [← hρreal]
      exact hρ.1
    exact hnz hzreal
  · have hre_le_neg : ρ.re ≤ -1 := by linarith
    let w : ℂ := ((1 - ρ.re : ℝ) : ℂ)
    have hw_re : 1 ≤ w.re := by simp [w]; linarith
    have hw_ne_one : w ≠ 1 := by
      intro hw
      have hwre := congrArg Complex.re hw
      simp [w] at hwre
      linarith
    have hw_neg_nat : ∀ n : ℕ, w ≠ -↑n := by
      intro n hn
      have hwre := congrArg Complex.re hn
      simp [w] at hwre
      have hnnonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      linarith
    have hcos_ne : Complex.cos (↑Real.pi * w / 2) ≠ 0 := by
      intro hcos
      have htriv : IsTrivialZetaZero ρ :=
        isTrivialZetaZero_of_real_cos_eq_zero him hre_le_neg (by simpa [w] using hcos)
      exact hρ.2.1 htriv
    have hzeta_w : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw_re
    have hpow : (2 * ↑Real.pi : ℂ) ^ (-w) ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff]
      left
      norm_num [Complex.ofReal_ne_zero, Real.pi_ne_zero]
    have hGamma : Complex.Gamma w ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro n hn
      have hwre := congrArg Complex.re hn
      simp [w] at hwre
      have hnnonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      linarith
    have hfe := riemannZeta_one_sub (s := w) hw_neg_nat hw_ne_one
    have hone : 1 - w = ρ := by
      rw [hρreal]
      apply Complex.ext <;> simp [w]
    have hnz : riemannZeta ρ ≠ 0 := by
      rw [← hone, hfe]
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpow) hGamma) hcos_ne)
        hzeta_w
    exact hnz hρ.1

/-- Every local non-trivial zeta zero lies in the open critical strip. -/
theorem isNontrivialZetaZero_re_mem_Ioo
    {ρ : ℂ}
    (hρ : IsNontrivialZetaZero ρ) :
    ρ.re ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · by_contra hnot
    have hrele : ρ.re ≤ 0 := le_of_not_gt hnot
    by_cases him0 : ρ.im = 0
    · exact riemannZeta_ne_zero_of_real_nontrivial_left hρ him0 hrele
    · exact (Kadiri.riemannZeta_ne_zero_of_re_nonpos_im_ne_zero hrele him0) hρ.1
  · by_contra hnot
    exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hnot)) hρ.1

/-- Exact equivalence between the local non-trivial-zero predicate and Kadiri's source type. -/
def canonicalNontrivialZeroEquivKadiri :
    {ρ : ℂ // RHV3Lean.IsNontrivialZetaZero ρ} ≃
      Kadiri.NontrivialZeros where
  toFun ρ :=
    ⟨ρ, isNontrivialZetaZero_re_mem_Ioo ρ.property, Set.mem_univ _, ρ.property.1⟩
  invFun ρ :=
    ⟨ρ, by
      refine ⟨ρ.property.2.2, ?_, ?_⟩
      · intro htriv
        rcases htriv with ⟨n, hn⟩
        have hpos := ρ.property.1.1
        rw [hn] at hpos
        simp at hpos
        have hnnonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
        nlinarith
      · exact Kadiri.nontrivialZero_ne_one ρ⟩
  left_inv ρ := by ext; rfl
  right_inv ρ := by ext; rfl

/-- Canonical strict symmetric height truncation for local non-trivial zeros. -/
def nontrivialZetaZerosByHeight (T : ℝ) : Set ℂ :=
  {ρ | RHV3Lean.IsNontrivialZetaZero ρ ∧ |ρ.im| < T}

theorem nontrivialZetaZerosByHeight_finite
    (T : ℝ) :
    (nontrivialZetaZerosByHeight T).Finite := by
  refine (zetaZerosInClosedBall_finite (T + 1)).subset ?_
  intro ρ hρ
  rw [nontrivialZetaZerosByHeight] at hρ
  rw [zetaZerosInClosedBall]
  constructor
  · rw [Metric.mem_closedBall, dist_zero_right]
    have hstrip := isNontrivialZetaZero_re_mem_Ioo hρ.1
    have hre_abs : |ρ.re| < 1 := by
      rw [abs_of_nonneg (le_of_lt hstrip.1)]
      exact hstrip.2
    have hnorm : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    exact le_of_lt (lt_of_le_of_lt hnorm (by linarith [hre_abs, hρ.2]))
  · rw [mem_riemannZetaZeros]
    exact hρ.1.1

noncomputable def nontrivialZetaZerosByHeightFinset
    (T : ℝ) :
    Finset ℂ :=
  (nontrivialZetaZerosByHeight_finite T).toFinset

@[simp] theorem mem_nontrivialZetaZerosByHeightFinset
    {T : ℝ} {ρ : ℂ} :
    ρ ∈ nontrivialZetaZerosByHeightFinset T ↔
      RHV3Lean.IsNontrivialZetaZero ρ ∧ |ρ.im| < T := by
  simp [nontrivialZetaZerosByHeightFinset, nontrivialZetaZerosByHeight]

theorem nontrivialZetaZerosByHeightFinset_mono
    {T U : ℝ}
    (hTU : T ≤ U) :
    nontrivialZetaZerosByHeightFinset T ⊆
      nontrivialZetaZerosByHeightFinset U := by
  intro ρ hρ
  rw [mem_nontrivialZetaZerosByHeightFinset] at hρ ⊢
  exact ⟨hρ.1, lt_of_lt_of_le hρ.2 hTU⟩

theorem nontrivialZetaZerosByHeightFinset_conj
    {T : ℝ} {ρ : ℂ} :
    ρ ∈ nontrivialZetaZerosByHeightFinset T ↔
      starRingEnd ℂ ρ ∈ nontrivialZetaZerosByHeightFinset T := by
  rw [mem_nontrivialZetaZerosByHeightFinset, mem_nontrivialZetaZerosByHeightFinset]
  constructor
  · intro hρ
    exact ⟨(isNontrivialZetaZero_conj_iff (ρ := ρ)).mpr hρ.1, by
      simpa [Complex.conj_im, abs_neg] using hρ.2⟩
  · intro hρ
    have hnon : IsNontrivialZetaZero ρ := by
      have hc := (isNontrivialZetaZero_conj_iff (ρ := (starRingEnd ℂ ρ))).mpr hρ.1
      simpa [Complex.conj_conj] using hc
    exact ⟨hnon, by simpa [Complex.conj_im, abs_neg] using hρ.2⟩

end RHV3Lean
