/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaHorizontalPerronVanishingP4_4d
import RHV3Lean.Objects.P4Port.IEANTN.HadamardLogDerivative
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# P4.4e: left-vertical digamma support bounds

This module starts the left-vertical Perron boundary work with the finite
digamma translation required on the line `s = perronRectangleSigmaL N + t * I`.
The finite iteration reuses `P4_4c.digamma_add_nat_eq`, whose step is
`Complex.digamma_apply_add_one`.
No left-boundary vanishing theorem is stated here until the vertical integrability
and truncated-to-full passage are proved.
-/

open Complex BigOperators Filter MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

namespace RHV3Lean

namespace P4_4e

/-- Canonical point on the left Perron vertical line. -/
def sN (N : ℕ) (t : ℝ) : ℂ :=
  (perronRectangleSigmaL N : ℂ) + t * Complex.I

lemma sN_eq (N : ℕ) (t : ℝ) :
    sN N t = (perronRectangleSigmaL N : ℂ) + t * Complex.I := rfl

lemma sN_re (N : ℕ) (t : ℝ) :
    (sN N t).re = perronRectangleSigmaL N := by
  simp [sN]

lemma sN_im (N : ℕ) (t : ℝ) :
    (sN N t).im = t := by
  simp [sN]

lemma sN_ne_zero {N : ℕ} (_hN : 1 ≤ N) (t : ℝ) :
    sN N t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [sN, perronRectangleSigmaL] at hre
  have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  nlinarith

lemma sN_ne_one {N : ℕ} (_hN : 1 ≤ N) (t : ℝ) :
    sN N t ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp [sN, perronRectangleSigmaL] at hre
  have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  nlinarith

lemma one_sub_sN_ne_one {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    (1 : ℂ) - sN N t ≠ 1 := by
  intro h
  have hs0 : sN N t = 0 := by linear_combination -h
  exact sN_ne_zero hN t hs0

lemma one_lt_one_sub_sN_re {N : ℕ} (_hN : 1 ≤ N) (t : ℝ) :
    1 < ((1 : ℂ) - sN N t).re := by
  simp [sN, perronRectangleSigmaL]
  have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  nlinarith

/-- The left Perron line avoids all zeta zeros: it is neither in the critical strip nor
on a negative even integer. -/
theorem left_vertical_riemannZeta_ne_zero
    {N : ℕ} (_hN : 1 ≤ N) (t : ℝ) :
    riemannZeta
      ((perronRectangleSigmaL N : ℂ) + t * Complex.I) ≠ 0 := by
  by_contra hζ
  have hζs : riemannZeta (sN N t) = 0 := by simpa [sN] using hζ
  rcases zetaZero_trivial_or_nontrivial hζs with htriv | hnon
  · rcases htriv with ⟨m, hm⟩
    have hre := congrArg Complex.re hm
    have hparity : (2 * (m + 1) : ℕ) = 2 * N + 1 := by
      have hreal : (2 * (m + 1) : ℝ) = 2 * (N : ℝ) + 1 := by
        simp [sN, perronRectangleSigmaL] at hre
        nlinarith
      exact_mod_cast hreal
    omega
  · have hstrip := isNontrivialZetaZero_re_mem_Ioo hnon
    have hleft : (sN N t).re < 0 := by
      simp [sN, perronRectangleSigmaL]
      have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
      nlinarith
    exact not_lt_of_ge hstrip.1.le hleft

theorem left_vertical_reflected_riemannZeta_ne_zero
    {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    riemannZeta (1 - sN N t) ≠ 0 := by
  exact riemannZeta_ne_zero_of_one_le_re (le_of_lt (one_lt_one_sub_sN_re hN t))

theorem left_vertical_negLogDeriv_functional_identity
    {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    -deriv riemannZeta (sN N t) /
        riemannZeta (sN N t)
      =
    ((-Real.log Real.pi : ℝ) : ℂ)
      + deriv riemannZeta (1 - sN N t) /
          riemannZeta (1 - sN N t)
      + (1 / 2 : ℂ) *
          (Complex.digamma (sN N t / 2) +
            Complex.digamma ((1 - sN N t) / 2)) := by
  exact Kadiri.kadiri_thm_3_1_q1_functional_eq
    (s := sN N t) (sN_ne_one hN t) (sN_ne_zero hN t)
    (by simpa [sN] using left_vertical_riemannZeta_ne_zero hN t)
    (left_vertical_reflected_riemannZeta_ne_zero hN t)

theorem left_vertical_reflected_logDeriv_uniform_bound
    {N : ℕ} (hN : 1 ≤ N) :
    ∀ t : ℝ,
      ‖deriv riemannZeta (1 - sN N t) /
          riemannZeta (1 - sN N t)‖
        ≤ ‖deriv riemannZeta (4 : ℂ) / riemannZeta (4 : ℂ)‖ := by
  intro t
  let σ₁ : ℝ := 2 * (N : ℝ) + 2
  have hσ₁ : 4 ≤ σ₁ := by
    dsimp [σ₁]
    have hN_real : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hbound :=
    dlog_riemannZeta_bdd_on_vertical_lines_generalized
      (σ₀ := 4) (σ₁ := σ₁) (t := -t) (by norm_num) hσ₁
  have hpoint : (σ₁ : ℂ) + (-t) * Complex.I = 1 - sN N t := by
    dsimp [σ₁, sN]
    exact Complex.ext
      (by simp [perronRectangleSigmaL]; ring)
      (by simp [perronRectangleSigmaL])
  have hfour : ((4 : ℝ) : ℂ) = (4 : ℂ) := rfl
  calc
    ‖deriv riemannZeta (1 - sN N t) / riemannZeta (1 - sN N t)‖
        = ‖-deriv riemannZeta (1 - sN N t) / riemannZeta (1 - sN N t)‖ := by
          simp [norm_neg]
    _ = ‖-deriv riemannZeta ((σ₁ : ℂ) + (-t) * Complex.I) /
            riemannZeta ((σ₁ : ℂ) + (-t) * Complex.I)‖ := by
          rw [hpoint]
    _ ≤ ‖deriv riemannZeta (4 : ℂ) / riemannZeta (4 : ℂ)‖ := by
          simpa [hfour, norm_neg] using hbound

/-- The digamma argument on the left Perron boundary after division by two. -/
def leftDigammaPoint (N : ℕ) (t : ℝ) : ℂ :=
  -((N : ℝ) + 1 / 2) + (t / 2) * Complex.I

lemma perron_left_div_two_eq_leftDigammaPoint (N : ℕ) (t : ℝ) :
    (((perronRectangleSigmaL N : ℂ) + t * Complex.I) / 2) =
      leftDigammaPoint N t := by
  exact Complex.ext
    (by
      simp [perronRectangleSigmaL, leftDigammaPoint]
      ring)
    (by simp [perronRectangleSigmaL, leftDigammaPoint])

lemma leftDigammaPoint_add_nat_re (N : ℕ) (t : ℝ) (k : ℕ) :
    (leftDigammaPoint N t + (k : ℂ)).re = (k : ℝ) - (N : ℝ) - 1 / 2 := by
  simp [leftDigammaPoint]
  ring

lemma leftDigammaPoint_shift (N : ℕ) (t : ℝ) :
    leftDigammaPoint N t + ((N + 1 : ℕ) : ℂ) =
      (1 / 2 : ℂ) + (t / 2) * Complex.I := by
  exact Complex.ext
    (by
      simp [leftDigammaPoint]
      ring)
    (by simp [leftDigammaPoint])

lemma leftDigammaPoint_add_nat_ne_neg_nat (N : ℕ) (t : ℝ) (k m : ℕ) :
    leftDigammaPoint N t + (k : ℂ) ≠ -(m : ℂ) := by
  intro hbad
  have hreal := congrArg Complex.re hbad
  have hparity : (2 * (k + m) : ℕ) = 2 * N + 1 := by
    apply Nat.cast_injective (R := ℝ)
    simp [leftDigammaPoint] at hreal ⊢
    nlinarith
  omega

lemma leftDigammaPoint_no_poles_in_range (N : ℕ) (t : ℝ) :
    ∀ k : ℕ, k < N + 1 → ∀ m : ℕ,
      leftDigammaPoint N t + (k : ℂ) ≠ -(m : ℂ) := by
  intro k _hk m
  exact leftDigammaPoint_add_nat_ne_neg_nat N t k m

lemma leftDigammaPoint_digamma_add_nat (N : ℕ) (t : ℝ) :
    Complex.digamma (leftDigammaPoint N t + ((N + 1 : ℕ) : ℂ)) =
      Complex.digamma (leftDigammaPoint N t) +
        ∑ k ∈ Finset.range (N + 1),
          (leftDigammaPoint N t + (k : ℂ))⁻¹ := by
  exact P4_4c.digamma_add_nat_eq
    (leftDigammaPoint N t) (N + 1) (leftDigammaPoint_no_poles_in_range N t)

lemma leftDigammaPoint_digamma_eq_shift_sub_sum (N : ℕ) (t : ℝ) :
    Complex.digamma (leftDigammaPoint N t) =
      Complex.digamma (leftDigammaPoint N t + ((N + 1 : ℕ) : ℂ)) -
        ∑ k ∈ Finset.range (N + 1),
          (leftDigammaPoint N t + (k : ℂ))⁻¹ := by
  have h := leftDigammaPoint_digamma_add_nat N t
  rw [h]
  ring

lemma leftDigammaPoint_abs_re_ge_half
    {N k : ℕ} (t : ℝ) (hk : k < N + 1) :
    (1 / 2 : ℝ) ≤ |(leftDigammaPoint N t + (k : ℂ)).re| := by
  have hkN_nat : k ≤ N := Nat.le_of_lt_succ hk
  have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN_nat
  rw [leftDigammaPoint_add_nat_re]
  have hnonpos : (k : ℝ) - (N : ℝ) - 1 / 2 ≤ 0 := by nlinarith
  rw [abs_of_nonpos hnonpos]
  nlinarith

lemma leftDigammaPoint_inv_norm_le_two
    {N k : ℕ} (t : ℝ) (hk : k < N + 1) :
    ‖(leftDigammaPoint N t + (k : ℂ))⁻¹‖ ≤ (2 : ℝ) := by
  let z : ℂ := leftDigammaPoint N t + (k : ℂ)
  have hre : (1 / 2 : ℝ) ≤ |z.re| := leftDigammaPoint_abs_re_ge_half (N := N) t hk
  have hnorm_lower : (1 / 2 : ℝ) ≤ ‖z‖ :=
    le_trans hre (Complex.abs_re_le_norm z)
  have hhalf_pos : (0 : ℝ) < 1 / 2 := by norm_num
  calc
    ‖z⁻¹‖ = 1 / ‖z‖ := by
      simp [one_div, norm_inv]
    _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le hhalf_pos hnorm_lower
    _ = 2 := by norm_num

lemma leftDigammaPoint_inv_sum_norm_le (N : ℕ) (t : ℝ) :
    ‖∑ k ∈ Finset.range (N + 1),
        (leftDigammaPoint N t + (k : ℂ))⁻¹‖
      ≤ 2 * ((N : ℝ) + 1) := by
  calc
    ‖∑ k ∈ Finset.range (N + 1),
        (leftDigammaPoint N t + (k : ℂ))⁻¹‖
        ≤ ∑ k ∈ Finset.range (N + 1),
            ‖(leftDigammaPoint N t + (k : ℂ))⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (N + 1), (2 : ℝ) := by
          exact Finset.sum_le_sum fun k hk =>
            leftDigammaPoint_inv_norm_le_two (N := N) (k := k) t
              (Finset.mem_range.mp hk)
    _ = 2 * ((N : ℝ) + 1) := by
          simp [nsmul_eq_mul]
          ring

lemma shifted_leftDigammaPoint_norm_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ,
        ‖Complex.digamma ((1 / 2 : ℂ) + (t / 2) * Complex.I)‖
          ≤ C * Real.log (|t| + 2) := by
  obtain ⟨C0, hC0_pos, hC0⟩ :=
    Complex.exists_norm_digamma_le_log (a := 1 / 2) (b := 1 / 2) (by norm_num)
  refine ⟨C0, hC0_pos, ?_⟩
  intro t
  let w : ℂ := (1 / 2 : ℂ) + (t / 2) * Complex.I
  have hwre_ge : (1 / 2 : ℝ) ≤ w.re := by simp [w]
  have hwre_le : w.re ≤ (1 / 2 : ℝ) := by simp [w]
  have h := hC0 w hwre_ge hwre_le
  have him_le : |w.im| + 2 ≤ |t| + 2 := by
    have hdiv : |t / 2| ≤ |t| := by
      rw [abs_div]
      have htwo : |(2 : ℝ)| = 2 := by norm_num
      rw [htwo]
      nlinarith [abs_nonneg t]
    simp [w]
    linarith
  exact le_trans h
    (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) him_le) (le_of_lt hC0_pos))

theorem left_vertical_shifted_digamma_bound_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 1 ≤ N →
        ∀ t : ℝ,
        ‖Complex.digamma
          (sN N t / 2)‖
          ≤ C * ((N : ℝ) + 1) * Real.log (|t| + 2) := by
  obtain ⟨C0, hC0_pos, hC0⟩ := shifted_leftDigammaPoint_norm_bound
  let C : ℝ := C0 + 2 / Real.log 2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro N _hN t
  let z : ℂ := leftDigammaPoint N t
  let w : ℂ := (1 / 2 : ℂ) + (t / 2) * Complex.I
  have hshift : z + ((N + 1 : ℕ) : ℂ) = w := by
    dsimp [z, w]
    exact leftDigammaPoint_shift N t
  have hiter :
      Complex.digamma z =
        Complex.digamma w -
          ∑ k ∈ Finset.range (N + 1), (z + (k : ℂ))⁻¹ := by
    rw [← hshift]
    exact leftDigammaPoint_digamma_eq_shift_sub_sum N t
  have hsum :
      ‖∑ k ∈ Finset.range (N + 1), (z + (k : ℂ))⁻¹‖
        ≤ 2 * ((N : ℝ) + 1) := by
    dsimp [z]
    exact leftDigammaPoint_inv_sum_norm_le N t
  set L : ℝ := Real.log (|t| + 2) with hL_def
  have hL_ge_log2 : Real.log 2 ≤ L := by
    rw [hL_def]
    exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hL_nonneg : 0 ≤ L := le_trans (le_of_lt hlog2_pos) hL_ge_log2
  have hNfac_ge_one : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have hN_nonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hmain :
      ‖Complex.digamma z‖ ≤ C0 * L + 2 * ((N : ℝ) + 1) := by
    rw [hiter]
    calc
      ‖Complex.digamma w -
          ∑ k ∈ Finset.range (N + 1), (z + (k : ℂ))⁻¹‖
          ≤ ‖Complex.digamma w‖ +
              ‖∑ k ∈ Finset.range (N + 1), (z + (k : ℂ))⁻¹‖ := norm_sub_le _ _
      _ ≤ C0 * L + 2 * ((N : ℝ) + 1) := by
            exact add_le_add (by simpa [w, hL_def] using hC0 t) hsum
  have habsorb :
      C0 * L + 2 * ((N : ℝ) + 1) ≤
        C * ((N : ℝ) + 1) * L := by
    have hC0_nonneg : 0 ≤ C0 := le_of_lt hC0_pos
    have hterm1 : C0 * L ≤ C0 * ((N : ℝ) + 1) * L := by
      calc
        C0 * L ≤ C0 * (((N : ℝ) + 1) * L) := by
          exact mul_le_mul_of_nonneg_left
            (by nlinarith [hNfac_ge_one, hL_nonneg]) hC0_nonneg
        _ = C0 * ((N : ℝ) + 1) * L := by ring
    have hterm2 : 2 * ((N : ℝ) + 1) ≤
        (2 / Real.log 2) * ((N : ℝ) + 1) * L := by
      have hbase : (2 : ℝ) ≤ (2 / Real.log 2) * L := by
        rw [div_mul_eq_mul_div]
        rw [le_div_iff₀ hlog2_pos]
        nlinarith
      calc
        2 * ((N : ℝ) + 1) ≤
            ((2 / Real.log 2) * L) * ((N : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_right hbase (by positivity)
        _ = (2 / Real.log 2) * ((N : ℝ) + 1) * L := by ring
    dsimp [C]
    nlinarith
  calc
    ‖Complex.digamma (sN N t / 2)‖
        = ‖Complex.digamma z‖ := by
          dsimp [z]
          rw [sN_eq, perron_left_div_two_eq_leftDigammaPoint]
    _ ≤ C0 * L + 2 * ((N : ℝ) + 1) := hmain
    _ ≤ C * ((N : ℝ) + 1) * L := habsorb
    _ = C * ((N : ℝ) + 1) * Real.log (|t| + 2) := by rw [hL_def]

theorem left_vertical_shifted_digamma_bound
    {N : ℕ}
    (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ,
        ‖Complex.digamma
          ((((perronRectangleSigmaL N : ℂ)
             + t * Complex.I) / 2))‖
          ≤ C * ((N : ℝ) + 1) * Real.log (|t| + 2) := by
  obtain ⟨C, hCpos, hC⟩ := left_vertical_shifted_digamma_bound_uniform
  refine ⟨C, hCpos, ?_⟩
  intro t
  simpa [sN] using hC N hN t

/-- Base point for the reflected digamma argument on the left Perron line. -/
def reflectedDigammaBase (t : ℝ) : ℂ :=
  1 - (t / 2) * Complex.I

lemma one_sub_sN_div_two_eq_reflectedDigammaBase_add_nat
    (N : ℕ) (t : ℝ) :
    (1 - sN N t) / 2 =
      reflectedDigammaBase t + (N : ℂ) := by
  exact Complex.ext
    (by
      simp [sN, reflectedDigammaBase, perronRectangleSigmaL]
      ring)
    (by
      simp [sN, reflectedDigammaBase, perronRectangleSigmaL]
      ring)

lemma reflectedDigammaBase_add_nat_re
    (t : ℝ) (k : ℕ) :
    (reflectedDigammaBase t + (k : ℂ)).re =
      (k : ℝ) + 1 := by
  simp [reflectedDigammaBase]
  ring

lemma reflectedDigammaBase_add_nat_ne_neg_nat
    (t : ℝ) (k m : ℕ) :
    reflectedDigammaBase t + (k : ℂ) ≠ -(m : ℂ) := by
  intro hbad
  have hreal := congrArg Complex.re hbad
  have hleft : (reflectedDigammaBase t + (k : ℂ)).re = (k : ℝ) + 1 :=
    reflectedDigammaBase_add_nat_re t k
  have hright : (-(m : ℂ)).re = -(m : ℝ) := by simp
  rw [hleft, hright] at hreal
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

lemma reflectedDigammaBase_no_poles_in_range
    (N : ℕ) (t : ℝ) :
    ∀ k : ℕ, k < N →
      ∀ m : ℕ,
        reflectedDigammaBase t + (k : ℂ) ≠ -(m : ℂ) := by
  intro k _hk m
  exact reflectedDigammaBase_add_nat_ne_neg_nat t k m

lemma reflected_digamma_add_nat_identity
    (N : ℕ) (t : ℝ) :
    Complex.digamma
        (reflectedDigammaBase t + (N : ℂ))
      =
    Complex.digamma (reflectedDigammaBase t)
      +
    ∑ k ∈ Finset.range N,
      (reflectedDigammaBase t + (k : ℂ))⁻¹ := by
  exact P4_4c.digamma_add_nat_eq
    (reflectedDigammaBase t) N (reflectedDigammaBase_no_poles_in_range N t)

lemma reflectedDigammaBase_inv_norm_le_one
    {N k : ℕ} (t : ℝ) (_hk : k < N) :
    ‖(reflectedDigammaBase t + (k : ℂ))⁻¹‖ ≤ 1 := by
  let z : ℂ := reflectedDigammaBase t + (k : ℂ)
  have hre : (1 : ℝ) ≤ |z.re| := by
    have hzre : z.re = (k : ℝ) + 1 := by
      dsimp [z]
      exact reflectedDigammaBase_add_nat_re t k
    rw [hzre]
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) + 1)]
    linarith
  have hnorm_lower : (1 : ℝ) ≤ ‖z‖ :=
    le_trans hre (Complex.abs_re_le_norm z)
  calc
    ‖z⁻¹‖ = 1 / ‖z‖ := by
      simp [one_div, norm_inv]
    _ ≤ 1 / (1 : ℝ) := one_div_le_one_div_of_le zero_lt_one hnorm_lower
    _ = 1 := by norm_num

lemma reflectedDigammaBase_inv_sum_norm_le
    (N : ℕ) (t : ℝ) :
    ‖∑ k ∈ Finset.range N,
        (reflectedDigammaBase t + (k : ℂ))⁻¹‖
      ≤ (N : ℝ) := by
  calc
    ‖∑ k ∈ Finset.range N,
        (reflectedDigammaBase t + (k : ℂ))⁻¹‖
        ≤ ∑ k ∈ Finset.range N,
            ‖(reflectedDigammaBase t + (k : ℂ))⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, (1 : ℝ) := by
          exact Finset.sum_le_sum fun k hk =>
            reflectedDigammaBase_inv_norm_le_one (N := N) (k := k) t
              (Finset.mem_range.mp hk)
    _ = (N : ℝ) := by simp

lemma reflectedDigammaBase_norm_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ,
        ‖Complex.digamma (reflectedDigammaBase t)‖
          ≤ C * Real.log (|t| + 2) := by
  obtain ⟨C0, hC0_pos, hC0⟩ :=
    Complex.exists_norm_digamma_le_log (a := 1) (b := 1) one_pos
  refine ⟨C0, hC0_pos, ?_⟩
  intro t
  let w : ℂ := reflectedDigammaBase t
  have hwre_ge : (1 : ℝ) ≤ w.re := by simp [w, reflectedDigammaBase]
  have hwre_le : w.re ≤ (1 : ℝ) := by simp [w, reflectedDigammaBase]
  have h := hC0 w hwre_ge hwre_le
  have him_le : |w.im| + 2 ≤ |t| + 2 := by
    have hdiv : |t / 2| ≤ |t| := by
      rw [abs_div]
      have htwo : |(2 : ℝ)| = 2 := by norm_num
      rw [htwo]
      nlinarith [abs_nonneg t]
    simp [w, reflectedDigammaBase]
    linarith
  exact le_trans h
    (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) him_le) (le_of_lt hC0_pos))

theorem left_vertical_reflected_digamma_bound_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ,
        ∀ t : ℝ,
          ‖Complex.digamma ((1 - sN N t) / 2)‖
            ≤ C * ((N : ℝ) + 1) * Real.log (|t| + 2) := by
  obtain ⟨C0, hC0_pos, hC0⟩ := reflectedDigammaBase_norm_bound
  let C : ℝ := C0 + 1 / Real.log 2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro N t
  let z : ℂ := reflectedDigammaBase t
  set L : ℝ := Real.log (|t| + 2) with hL_def
  have hL_ge_log2 : Real.log 2 ≤ L := by
    rw [hL_def]
    exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hL_nonneg : 0 ≤ L := le_trans (le_of_lt hlog2_pos) hL_ge_log2
  have hNfac_ge_one : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have hN_nonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hiter :
      Complex.digamma (z + (N : ℂ)) =
        Complex.digamma z +
          ∑ k ∈ Finset.range N, (z + (k : ℂ))⁻¹ := by
    dsimp [z]
    exact reflected_digamma_add_nat_identity N t
  have hsum :
      ‖∑ k ∈ Finset.range N, (z + (k : ℂ))⁻¹‖ ≤ (N : ℝ) := by
    dsimp [z]
    exact reflectedDigammaBase_inv_sum_norm_le N t
  have hmain :
      ‖Complex.digamma (z + (N : ℂ))‖ ≤ C0 * L + (N : ℝ) := by
    rw [hiter]
    calc
      ‖Complex.digamma z +
          ∑ k ∈ Finset.range N, (z + (k : ℂ))⁻¹‖
          ≤ ‖Complex.digamma z‖ +
              ‖∑ k ∈ Finset.range N, (z + (k : ℂ))⁻¹‖ := norm_add_le _ _
      _ ≤ C0 * L + (N : ℝ) := by
            exact add_le_add (by simpa [z, hL_def] using hC0 t) hsum
  have habsorb :
      C0 * L + (N : ℝ) ≤ C * ((N : ℝ) + 1) * L := by
    have hC0_nonneg : 0 ≤ C0 := le_of_lt hC0_pos
    have hterm1 : C0 * L ≤ C0 * ((N : ℝ) + 1) * L := by
      calc
        C0 * L ≤ C0 * (((N : ℝ) + 1) * L) := by
          exact mul_le_mul_of_nonneg_left
            (by nlinarith [hNfac_ge_one, hL_nonneg]) hC0_nonneg
        _ = C0 * ((N : ℝ) + 1) * L := by ring
    have hterm2 : (N : ℝ) ≤
        (1 / Real.log 2) * ((N : ℝ) + 1) * L := by
      have hbase : (1 : ℝ) ≤ (1 / Real.log 2) * L := by
        rw [one_div_mul_eq_div]
        rw [le_div_iff₀ hlog2_pos]
        simpa using hL_ge_log2
      have hN_le : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
      calc
        (N : ℝ) ≤ (N : ℝ) + 1 := hN_le
        _ ≤ ((1 / Real.log 2) * L) * ((N : ℝ) + 1) := by
          have hNfac_nonneg : 0 ≤ (N : ℝ) + 1 := by positivity
          simpa [one_mul] using mul_le_mul_of_nonneg_right hbase hNfac_nonneg
        _ = (1 / Real.log 2) * ((N : ℝ) + 1) * L := by ring
    dsimp [C]
    nlinarith
  calc
    ‖Complex.digamma ((1 - sN N t) / 2)‖
        = ‖Complex.digamma (z + (N : ℂ))‖ := by
          dsimp [z]
          rw [one_sub_sN_div_two_eq_reflectedDigammaBase_add_nat]
    _ ≤ C0 * L + (N : ℝ) := hmain
    _ ≤ C * ((N : ℝ) + 1) * L := habsorb
    _ = C * ((N : ℝ) + 1) * Real.log (|t| + 2) := by rw [hL_def]

theorem log_abs_add_two_le_four_mul_sqrt
    (t : ℝ) :
    Real.log (|t| + 2)
      ≤ 4 * (1 + |t|) ^ (1 / 2 : ℝ) := by
  let y : ℝ := 1 + |t|
  have hy_ge_one : (1 : ℝ) ≤ y := by
    dsimp [y]
    linarith [abs_nonneg t]
  have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy_ge_one
  have hy_nonneg : 0 ≤ y := le_of_lt hy_pos
  have harg_pos : 0 < |t| + 2 := by positivity
  have harg_le : |t| + 2 ≤ 2 * y := by
    dsimp [y]
    nlinarith [abs_nonneg t]
  have hlogmono :
      Real.log (|t| + 2) ≤ Real.log (2 * y) :=
    Real.log_le_log harg_pos harg_le
  have hlogmul : Real.log (2 * y) = Real.log 2 + Real.log y := by
    rw [Real.log_mul (by norm_num) hy_pos.ne']
  have hε : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  have hlogy : Real.log y ≤ y ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
    Real.log_le_rpow_div hy_nonneg hε
  have hsqrt_ge_one : (1 : ℝ) ≤ y ^ (1 / 2 : ℝ) := by
    simpa using Real.one_le_rpow hy_ge_one (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
  have hlog2_le_sqrt : Real.log 2 ≤ y ^ (1 / 2 : ℝ) := by
    have hlog2_le_one : Real.log 2 ≤ (1 : ℝ) := by
      linarith [Real.log_two_lt_d9]
    exact le_trans hlog2_le_one hsqrt_ge_one
  calc
    Real.log (|t| + 2) ≤ Real.log (2 * y) := hlogmono
    _ = Real.log 2 + Real.log y := hlogmul
    _ ≤ y ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := by
          exact add_le_add hlog2_le_sqrt hlogy
    _ = 3 * y ^ (1 / 2 : ℝ) := by ring
    _ ≤ 4 * y ^ (1 / 2 : ℝ) := by
          have hs_nonneg : 0 ≤ y ^ (1 / 2 : ℝ) :=
            Real.rpow_nonneg hy_nonneg _
          nlinarith
    _ = 4 * (1 + |t|) ^ (1 / 2 : ℝ) := by rfl

theorem left_vertical_negLogDeriv_uniform_sqrt_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 1 ≤ N →
        ∀ t : ℝ,
          ‖-deriv riemannZeta (sN N t) /
              riemannZeta (sN N t)‖
            ≤
          C * ((N : ℝ) + 1) *
            (1 + |t|) ^ (1 / 2 : ℝ) := by
  obtain ⟨CΓL, hCΓL_pos, hCΓL⟩ := left_vertical_shifted_digamma_bound_uniform
  obtain ⟨CΓR, hCΓR_pos, hCΓR⟩ := left_vertical_reflected_digamma_bound_uniform
  let Dζ : ℝ := ‖deriv riemannZeta (4 : ℂ) / riemannZeta (4 : ℂ)‖
  let Aπ : ℝ := ‖(((-Real.log Real.pi : ℝ) : ℂ))‖
  let C : ℝ := 4 * (Aπ + Dζ + CΓL + CΓR + 1)
  have hC_pos : 0 < C := by
    dsimp [C, Aπ, Dζ]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro N hN t
  let Y : ℝ := (N : ℝ) + 1
  let S : ℝ := (1 + |t|) ^ (1 / 2 : ℝ)
  let L : ℝ := Real.log (|t| + 2)
  let Bζ : ℂ := deriv riemannZeta (1 - sN N t) /
          riemannZeta (1 - sN N t)
  let ΓL : ℂ := Complex.digamma (sN N t / 2)
  let ΓR : ℂ := Complex.digamma ((1 - sN N t) / 2)
  have hY_ge_one : (1 : ℝ) ≤ Y := by
    dsimp [Y]
    have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hY_nonneg : 0 ≤ Y := le_trans zero_le_one hY_ge_one
  have hbase_ge_one : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hS_ge_one : (1 : ℝ) ≤ S := by
    dsimp [S]
    simpa using Real.one_le_rpow hbase_ge_one
      (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
  have hS_nonneg : 0 ≤ S := le_trans zero_le_one hS_ge_one
  have hlog_sqrt : L ≤ 4 * S := by
    dsimp [L, S]
    exact log_abs_add_two_le_four_mul_sqrt t
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact le_trans (le_of_lt (Real.log_pos one_lt_two))
      (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
  have hfunc := left_vertical_negLogDeriv_functional_identity hN t
  have hζ : ‖Bζ‖ ≤ Dζ := by
    dsimp [Bζ, Dζ]
    exact left_vertical_reflected_logDeriv_uniform_bound hN t
  have hΓL : ‖ΓL‖ ≤ CΓL * Y * L := by
    dsimp [ΓL, Y, L]
    exact hCΓL N hN t
  have hΓR : ‖ΓR‖ ≤ CΓR * Y * L := by
    dsimp [ΓR, Y, L]
    exact hCΓR N t
  have hhalf :
      ‖(1 / 2 : ℂ) * (ΓL + ΓR)‖
        ≤ (1 / 2 : ℝ) * (‖ΓL‖ + ‖ΓR‖) := by
    calc
      ‖(1 / 2 : ℂ) * (ΓL + ΓR)‖
          = (1 / 2 : ℝ) * ‖ΓL + ΓR‖ := by
            simp
      _ ≤ (1 / 2 : ℝ) * (‖ΓL‖ + ‖ΓR‖) := by
            exact mul_le_mul_of_nonneg_left (norm_add_le ΓL ΓR) (by norm_num)
  have htotal :
      ‖(((-Real.log Real.pi : ℝ) : ℂ) + Bζ +
          (1 / 2 : ℂ) * (ΓL + ΓR))‖
        ≤ Aπ + Dζ + (1 / 2 : ℝ) * (CΓL * Y * L + CΓR * Y * L) := by
    calc
      ‖(((-Real.log Real.pi : ℝ) : ℂ) + Bζ +
          (1 / 2 : ℂ) * (ΓL + ΓR))‖
          ≤ ‖(((-Real.log Real.pi : ℝ) : ℂ) + Bζ)‖ +
              ‖(1 / 2 : ℂ) * (ΓL + ΓR)‖ := norm_add_le _ _
      _ ≤ (Aπ + Dζ) + (1 / 2 : ℝ) * (‖ΓL‖ + ‖ΓR‖) := by
            have hfirst :
                ‖(((-Real.log Real.pi : ℝ) : ℂ) + Bζ)‖ ≤ Aπ + Dζ := by
              calc
                ‖(((-Real.log Real.pi : ℝ) : ℂ) + Bζ)‖
                    ≤ ‖(((-Real.log Real.pi : ℝ) : ℂ))‖ + ‖Bζ‖ := norm_add_le _ _
                _ ≤ Aπ + Dζ := by
                      exact add_le_add (by rfl) hζ
            exact add_le_add hfirst hhalf
      _ ≤ Aπ + Dζ + (1 / 2 : ℝ) * (CΓL * Y * L + CΓR * Y * L) := by
            have hsumΓ : ‖ΓL‖ + ‖ΓR‖ ≤ CΓL * Y * L + CΓR * Y * L :=
              add_le_add hΓL hΓR
            have hmul := mul_le_mul_of_nonneg_left hsumΓ
              (by norm_num : (0 : ℝ) ≤ 1 / 2)
            nlinarith
  have habsorb :
      Aπ + Dζ + (1 / 2 : ℝ) * (CΓL * Y * L + CΓR * Y * L) ≤
        C * Y * S := by
    have hA_nonneg : 0 ≤ Aπ := norm_nonneg _
    have hD_nonneg : 0 ≤ Dζ := norm_nonneg _
    have hCL_nonneg : 0 ≤ CΓL := le_of_lt hCΓL_pos
    have hCR_nonneg : 0 ≤ CΓR := le_of_lt hCΓR_pos
    have hYS_ge_one : (1 : ℝ) ≤ Y * S := by nlinarith
    have hconst_le : Aπ + Dζ ≤ (Aπ + Dζ) * (Y * S) := by
      have hAD_nonneg : 0 ≤ Aπ + Dζ := add_nonneg hA_nonneg hD_nonneg
      simpa [mul_one] using mul_le_mul_of_nonneg_left hYS_ge_one hAD_nonneg
    have hL_le_4S : L ≤ 4 * S := hlog_sqrt
    have hYL_le : Y * L ≤ 4 * Y * S := by
      calc
        Y * L ≤ Y * (4 * S) := mul_le_mul_of_nonneg_left hL_le_4S hY_nonneg
        _ = 4 * Y * S := by ring
    have hdig_le :
        (1 / 2 : ℝ) * (CΓL * Y * L + CΓR * Y * L) ≤
          4 * (CΓL + CΓR) * Y * S := by
      have hLpart : CΓL * Y * L ≤ CΓL * (4 * Y * S) := by
        calc
          CΓL * Y * L = CΓL * (Y * L) := by ring
          _ ≤ CΓL * (4 * Y * S) :=
              mul_le_mul_of_nonneg_left hYL_le hCL_nonneg
          _ = CΓL * (4 * Y * S) := rfl
      have hRpart : CΓR * Y * L ≤ CΓR * (4 * Y * S) := by
        calc
          CΓR * Y * L = CΓR * (Y * L) := by ring
          _ ≤ CΓR * (4 * Y * S) :=
              mul_le_mul_of_nonneg_left hYL_le hCR_nonneg
          _ = CΓR * (4 * Y * S) := rfl
      nlinarith
    dsimp [C]
    nlinarith
  calc
    ‖-deriv riemannZeta (sN N t) / riemannZeta (sN N t)‖
        = ‖(((-Real.log Real.pi : ℝ) : ℂ) + Bζ +
            (1 / 2 : ℂ) * (ΓL + ΓR))‖ := by
          rw [hfunc]
    _ ≤ Aπ + Dζ + (1 / 2 : ℝ) * (CΓL * Y * L + CΓR * Y * L) := htotal
    _ ≤ C * Y * S := habsorb
    _ = C * ((N : ℝ) + 1) * (1 + |t|) ^ (1 / 2 : ℝ) := by rfl

theorem left_vertical_negLogDeriv_rpow_bound
    {N : ℕ} (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ,
        ‖-deriv riemannZeta (sN N t) /
            riemannZeta (sN N t)‖
          ≤
        C * ((N : ℝ) + 1) *
          (1 + |t|) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := left_vertical_negLogDeriv_uniform_sqrt_bound
  exact ⟨C, hCpos, hC N hN⟩

theorem perron_kernel_left_vertical_bound
    {x : ℝ} (hx : 1 < x)
    {N : ℕ} (hN : 1 ≤ N)
    (t : ℝ) :
    ‖Perron.f x (sN N t)‖
      ≤
    2 * x ^ (-(2 * (N : ℝ) + 1)) /
      (1 + t ^ 2) := by
  let s : ℂ := sN N t
  let X : ℝ := x ^ (-(2 * (N : ℝ) + 1))
  let A : ℝ := ‖s‖ * ‖s + 1‖
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hX_pos : 0 < X := by
    dsimp [X]
    exact Real.rpow_pos_of_pos hxpos _
  have hX_nonneg : 0 ≤ X := le_of_lt hX_pos
  have hs_re : s.re = -(2 * (N : ℝ) + 1) := by
    dsimp [s]
    simp [sN, perronRectangleSigmaL]
  have hs_im : s.im = t := by
    dsimp [s]
    simp [sN]
  have hs1_im : (s + 1).im = t := by
    dsimp [s]
    simp [sN, add_comm]
  have hs_norm_ge_one : (1 : ℝ) ≤ ‖s‖ := by
    have hre_abs : |s.re| = 2 * (N : ℝ) + 1 := by
      rw [hs_re]
      rw [abs_of_nonpos]
      · ring
      · have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        nlinarith
    have hre_ge : (1 : ℝ) ≤ |s.re| := by
      rw [hre_abs]
      have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith
    exact le_trans hre_ge (Complex.abs_re_le_norm s)
  have hs1_norm_ge_one : (1 : ℝ) ≤ ‖s + 1‖ := by
    have hs1_re : (s + 1).re = -(2 * (N : ℝ)) := by
      dsimp [s]
      simp [sN, perronRectangleSigmaL]
    have hre_abs : |(s + 1).re| = 2 * (N : ℝ) := by
      rw [hs1_re]
      rw [abs_of_nonpos]
      · ring
      · have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        nlinarith
    have hre_ge : (1 : ℝ) ≤ |(s + 1).re| := by
      rw [hre_abs]
      have hN_real : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      nlinarith
    exact le_trans hre_ge (Complex.abs_re_le_norm (s + 1))
  have hA_ge_one : (1 : ℝ) ≤ A := by
    dsimp [A]
    nlinarith [hs_norm_ge_one, hs1_norm_ge_one, norm_nonneg s, norm_nonneg (s + 1)]
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA_ge_one
  have hA_ge_tsq : t ^ 2 ≤ A := by
    have ht_abs_s : |t| ≤ ‖s‖ := by
      rw [← hs_im]
      exact Complex.abs_im_le_norm s
    have ht_abs_s1 : |t| ≤ ‖s + 1‖ := by
      rw [← hs1_im]
      exact Complex.abs_im_le_norm (s + 1)
    have ht_abs_sq : |t| * |t| = t ^ 2 := by
      rw [← sq]
      exact sq_abs t
    dsimp [A]
    nlinarith [ht_abs_s, ht_abs_s1, abs_nonneg t, norm_nonneg s, norm_nonneg (s + 1), ht_abs_sq]
  have hmax : max 1 (t ^ 2) ≤ A := max_le hA_ge_one hA_ge_tsq
  have hden_two : 1 + t ^ 2 ≤ 2 * A := by
    have hone : (1 : ℝ) ≤ max 1 (t ^ 2) := le_max_left _ _
    have htsq : t ^ 2 ≤ max 1 (t ^ 2) := le_max_right _ _
    nlinarith [hmax, hone, htsq]
  have hden_half : (1 + t ^ 2) / 2 ≤ A := by nlinarith
  have hhalf_pos : 0 < (1 + t ^ 2) / 2 := by positivity
  have hkernel_norm :
      ‖Perron.f x s‖ = X / A := by
    rw [Perron.f, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    dsimp [X, A]
    rw [hs_re]
  calc
    ‖Perron.f x (sN N t)‖
        = ‖Perron.f x s‖ := by rfl
    _ = X / A := hkernel_norm
    _ ≤ X / ((1 + t ^ 2) / 2) := by
          exact div_le_div_of_nonneg_left hX_nonneg hhalf_pos hden_half
    _ = 2 * X / (1 + t ^ 2) := by
          field_simp [show (1 + t ^ 2) ≠ 0 by positivity]
    _ = 2 * x ^ (-(2 * (N : ℝ) + 1)) / (1 + t ^ 2) := by rfl

/-- Uniform constant chosen once from the left-vertical log-derivative bound. -/
noncomputable def leftVerticalLogDerivConstant : ℝ :=
  Classical.choose left_vertical_negLogDeriv_uniform_sqrt_bound

theorem leftVerticalLogDerivConstant_pos :
    0 < leftVerticalLogDerivConstant := by
  exact (Classical.choose_spec left_vertical_negLogDeriv_uniform_sqrt_bound).1

theorem leftVerticalLogDerivConstant_spec
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) :
    ‖-deriv riemannZeta (sN N t) /
        riemannZeta (sN N t)‖
      ≤
    leftVerticalLogDerivConstant *
      ((N : ℝ) + 1) *
      (1 + |t|) ^ (1 / 2 : ℝ) := by
  exact (Classical.choose_spec left_vertical_negLogDeriv_uniform_sqrt_bound).2 N hN t

def leftVerticalUniversalMajorant (t : ℝ) : ℝ :=
  (1 + |t|) ^ (1 / 2 : ℝ) / (1 + t ^ 2)

theorem leftVerticalUniversalMajorant_nonneg
    (t : ℝ) :
    0 ≤ leftVerticalUniversalMajorant t := by
  unfold leftVerticalUniversalMajorant
  positivity

theorem leftVerticalUniversalMajorant_le
    (t : ℝ) :
    leftVerticalUniversalMajorant t
      ≤ 2 * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := by
  let a : ℝ := |t|
  have ha_nonneg : 0 ≤ a := abs_nonneg t
  have hbase_pos : 0 < 1 + a := by linarith
  have hden_pos : 0 < 1 + t ^ 2 := by positivity
  have hsq : (1 + a) ^ 2 ≤ 2 * (1 + t ^ 2) := by
    have ht_sq : a ^ 2 = t ^ 2 := by
      dsimp [a]
      rw [sq_abs]
    have htwoa : 2 * a ≤ 1 + a ^ 2 := by nlinarith [sq_nonneg (a - 1)]
    nlinarith
  have hden_lower : (1 + a) ^ 2 / 2 ≤ 1 + t ^ 2 := by nlinarith
  have hsmall_pos : 0 < (1 + a) ^ 2 / 2 := by positivity
  have hnum_nonneg : 0 ≤ (1 + a) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (le_of_lt hbase_pos) _
  calc
    leftVerticalUniversalMajorant t
        = (1 + a) ^ (1 / 2 : ℝ) / (1 + t ^ 2) := by
          simp [leftVerticalUniversalMajorant, a]
    _ ≤ (1 + a) ^ (1 / 2 : ℝ) / ((1 + a) ^ 2 / 2) := by
          exact div_le_div_of_nonneg_left hnum_nonneg hsmall_pos hden_lower
    _ = 2 * (1 + a) ^ (-(3 / 2 : ℝ)) := by
          rw [Real.rpow_neg hbase_pos.le]
          field_simp [Real.rpow_pos_of_pos hbase_pos (3 / 2 : ℝ),
            Real.rpow_pos_of_pos hbase_pos (2 : ℝ)]
          rw [← Real.rpow_add hbase_pos]
          norm_num
    _ = 2 * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := by
          simp [a, Real.norm_eq_abs]

theorem leftVerticalUniversalMajorant_continuous :
    Continuous leftVerticalUniversalMajorant := by
  unfold leftVerticalUniversalMajorant
  refine (Continuous.rpow_const ?_ (by norm_num)).div ?_ ?_
  · exact continuous_const.add continuous_abs
  · fun_prop
  · intro t
    positivity

theorem leftVerticalUniversalMajorant_integrable :
    Integrable leftVerticalUniversalMajorant := by
  have hg0 :
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
    integrable_one_add_norm (E := ℝ) (μ := volume)
      (r := (3 / 2 : ℝ)) (by norm_num)
  have hg :
      Integrable (fun t : ℝ => 2 * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
    hg0.const_mul 2
  exact hg.mono'
    leftVerticalUniversalMajorant_continuous.aestronglyMeasurable
    (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (leftVerticalUniversalMajorant_nonneg t)]
      exact leftVerticalUniversalMajorant_le t)

noncomputable def leftVerticalUniversalMajorantMass : ℝ :=
  ∫ t : ℝ, leftVerticalUniversalMajorant t

theorem leftVerticalUniversalMajorantMass_nonneg :
    0 ≤ leftVerticalUniversalMajorantMass := by
  unfold leftVerticalUniversalMajorantMass
  exact integral_nonneg (fun t => leftVerticalUniversalMajorant_nonneg t)

lemma sN_ne_neg_one
    {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    sN N t ≠ -1 := by
  intro h
  have hre := congrArg Complex.re h
  simp [sN, perronRectangleSigmaL] at hre
  have hN_real : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  nlinarith

theorem analyticAt_zetaPerronIntegrand_left
    {x : ℝ} (hx : 1 < x)
    {N : ℕ} (hN : 1 ≤ N)
    (t : ℝ) :
    AnalyticAt ℂ
      (zetaPerronIntegrand x)
      (sN N t) := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hζnz : riemannZeta (sN N t) ≠ 0 := by
    simpa [sN] using left_vertical_riemannZeta_ne_zero hN t
  have hlog : AnalyticAt ℂ (fun s => -logDeriv riemannZeta s) (sN N t) :=
    (analyticAt_logDeriv_riemannZeta (sN_ne_one hN t) hζnz).neg
  have hker : AnalyticAt ℂ (Perron.f x) (sN N t) :=
    analyticAt_perronKernel hxpos (sN_ne_zero hN t) (sN_ne_neg_one hN t)
  rw [show zetaPerronIntegrand x =
      (fun s => -logDeriv riemannZeta s) * Perron.f x from rfl]
  exact hlog.mul hker

theorem continuous_left_vertical_zetaPerronIntegrand
    {x : ℝ} (hx : 1 < x)
    {N : ℕ} (hN : 1 ≤ N) :
    Continuous
      (fun t : ℝ =>
        zetaPerronIntegrand x (sN N t)) := by
  have hs_cont : Continuous (fun t : ℝ => sN N t) := by
    unfold sN
    fun_prop
  apply continuous_iff_continuousAt.2
  intro t
  change ContinuousAt (zetaPerronIntegrand x ∘ (fun t : ℝ => sN N t)) t
  exact (analyticAt_zetaPerronIntegrand_left (x := x) hx (N := N) hN t).continuousAt.comp
    hs_cont.continuousAt

theorem left_vertical_zetaPerronIntegrand_pointwise_bound
    {x : ℝ} (hx : 1 < x)
    {N : ℕ} (hN : 1 ≤ N)
    (t : ℝ) :
    ‖zetaPerronIntegrand x (sN N t)‖
      ≤
    2 * leftVerticalLogDerivConstant *
      ((N : ℝ) + 1) *
      x ^ (-(2 * (N : ℝ) + 1)) *
      leftVerticalUniversalMajorant t := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hlog := leftVerticalLogDerivConstant_spec N hN t
  have hker := perron_kernel_left_vertical_bound (x := x) hx (N := N) hN t
  have hlog_nonneg :
      0 ≤ leftVerticalLogDerivConstant * ((N : ℝ) + 1) *
        (1 + |t|) ^ (1 / 2 : ℝ) := by
    exact mul_nonneg
      (mul_nonneg (le_of_lt leftVerticalLogDerivConstant_pos) (by positivity))
      (Real.rpow_nonneg (by positivity) _)
  rw [zetaPerronIntegrand, logDeriv_apply, norm_mul]
  calc
    ‖-(deriv riemannZeta (sN N t) / riemannZeta (sN N t))‖ *
        ‖Perron.f x (sN N t)‖
        =
      ‖-deriv riemannZeta (sN N t) / riemannZeta (sN N t)‖ *
        ‖Perron.f x (sN N t)‖ := by
        simp [neg_div]
    _ ≤
      (leftVerticalLogDerivConstant * ((N : ℝ) + 1) *
        (1 + |t|) ^ (1 / 2 : ℝ)) *
        ‖Perron.f x (sN N t)‖
        := by
        exact mul_le_mul_of_nonneg_right hlog (norm_nonneg _)
    _ ≤
      (leftVerticalLogDerivConstant * ((N : ℝ) + 1) *
        (1 + |t|) ^ (1 / 2 : ℝ)) *
      (2 * x ^ (-(2 * (N : ℝ) + 1)) / (1 + t ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hker hlog_nonneg
    _ =
      2 * leftVerticalLogDerivConstant *
        ((N : ℝ) + 1) *
        x ^ (-(2 * (N : ℝ) + 1)) *
        leftVerticalUniversalMajorant t := by
        unfold leftVerticalUniversalMajorant
        ring

theorem left_vertical_zetaPerronIntegrand_integrable
    {x : ℝ} (hx : 1 < x)
    {N : ℕ} (hN : 1 ≤ N) :
    Integrable
      (fun t : ℝ =>
        zetaPerronIntegrand x (sN N t)) := by
  let A : ℝ :=
    2 * leftVerticalLogDerivConstant *
      ((N : ℝ) + 1) *
      x ^ (-(2 * (N : ℝ) + 1))
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (le_of_lt leftVerticalLogDerivConstant_pos))
        (by positivity))
      (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hx)) _)
  have hg : Integrable (fun t : ℝ => A * leftVerticalUniversalMajorant t) :=
    leftVerticalUniversalMajorant_integrable.const_mul A
  exact hg.mono'
    (continuous_left_vertical_zetaPerronIntegrand (x := x) hx (N := N) hN).aestronglyMeasurable
    (ae_of_all _ fun t => by
      simpa [A, mul_assoc] using
        left_vertical_zetaPerronIntegrand_pointwise_bound (x := x) hx (N := N) hN t)

noncomputable def leftVerticalScalarBound
    (x : ℝ) (N : ℕ) : ℝ :=
  2 * leftVerticalLogDerivConstant *
    leftVerticalUniversalMajorantMass *
    ((N : ℝ) + 1) *
    x ^ (-(2 * (N : ℝ) + 1))

theorem leftVerticalScalarBound_nonneg
    {x : ℝ} (hx : 1 < x)
    (N : ℕ) :
    0 ≤ leftVerticalScalarBound x N := by
  unfold leftVerticalScalarBound
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (le_of_lt leftVerticalLogDerivConstant_pos))
        leftVerticalUniversalMajorantMass_nonneg)
      (by positivity))
    (Real.rpow_nonneg (le_of_lt hxpos) _)

private lemma left_vertical_normalization_norm_le_one :
    ‖(1 / (2 * Real.pi * Complex.I) : ℂ)‖ ≤ 1 := by
  rw [norm_div, norm_one, norm_mul, norm_mul, norm_I]
  simp only [Complex.norm_ofNat]
  rw [Complex.norm_of_nonneg Real.pi_pos.le]
  have hden : 1 ≤ (2 : ℝ) * Real.pi * 1 := by
    nlinarith [Real.pi_gt_three]
  simpa using one_div_le_one_div_of_le zero_lt_one hden

theorem left_vertical_full_norm_le
    {x : ℝ} (hx : 1 < x)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖VerticalIntegral'
        (zetaPerronIntegrand x)
        (perronRectangleSigmaL N)‖
      ≤ leftVerticalScalarBound x N := by
  let f : ℝ → ℂ := fun t => zetaPerronIntegrand x (sN N t)
  let A : ℝ :=
    2 * leftVerticalLogDerivConstant *
      ((N : ℝ) + 1) *
      x ^ (-(2 * (N : ℝ) + 1))
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (le_of_lt leftVerticalLogDerivConstant_pos))
        (by positivity))
      (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hx)) _)
  have hf_int : Integrable f :=
    left_vertical_zetaPerronIntegrand_integrable (x := x) hx (N := N) hN
  have hg_int : Integrable (fun t : ℝ => A * leftVerticalUniversalMajorant t) :=
    leftVerticalUniversalMajorant_integrable.const_mul A
  have hnorm_le :
      (∫ t : ℝ, ‖f t‖) ≤
        ∫ t : ℝ, A * leftVerticalUniversalMajorant t := by
    exact integral_mono_ae hf_int.norm hg_int
      (ae_of_all _ fun t => by
        dsimp [f, A]
        simpa [mul_assoc] using
          left_vertical_zetaPerronIntegrand_pointwise_bound (x := x) hx (N := N) hN t)
  have hintegral_norm :
      ‖∫ t : ℝ, f t‖ ≤ A * leftVerticalUniversalMajorantMass := by
    calc
      ‖∫ t : ℝ, f t‖ ≤ ∫ t : ℝ, ‖f t‖ := norm_integral_le_integral_norm f
      _ ≤ ∫ t : ℝ, A * leftVerticalUniversalMajorant t := hnorm_le
      _ = A * leftVerticalUniversalMajorantMass := by
            rw [MeasureTheory.integral_const_mul]
            rfl
  have hVert :
      ‖VerticalIntegral (zetaPerronIntegrand x) (perronRectangleSigmaL N)‖
        ≤ A * leftVerticalUniversalMajorantMass := by
    unfold VerticalIntegral
    simp only [smul_eq_mul, norm_mul, norm_I, one_mul]
    exact hintegral_norm
  unfold VerticalIntegral'
  calc
    ‖(1 / (2 * Real.pi * Complex.I) : ℂ) •
        VerticalIntegral (zetaPerronIntegrand x) (perronRectangleSigmaL N)‖
        = ‖(1 / (2 * Real.pi * Complex.I) : ℂ)‖ *
          ‖VerticalIntegral (zetaPerronIntegrand x) (perronRectangleSigmaL N)‖ := by
          simp
    _ ≤ 1 * (A * leftVerticalUniversalMajorantMass) := by
          exact mul_le_mul left_vertical_normalization_norm_le_one hVert
            (norm_nonneg _) (by positivity)
    _ = leftVerticalScalarBound x N := by
          simp [A, leftVerticalScalarBound]
          ring

theorem left_vertical_truncated_tendsto_full
    {x : ℝ} (hx : 1 < x)
    {N : ℕ} (hN : 1 ≤ N)
    {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n =>
        VIntegral'
          (zetaPerronIntegrand x)
          (perronRectangleSigmaL N)
          (-T n) (T n))
      atTop
      (𝓝
        (VerticalIntegral'
          (zetaPerronIntegrand x)
          (perronRectangleSigmaL N))) := by
  let f : ℝ → ℂ := fun t => zetaPerronIntegrand x (sN N t)
  have hf_int : Integrable f :=
    left_vertical_zetaPerronIntegrand_integrable (x := x) hx (N := N) hN
  have hneg : Tendsto (fun n : ℕ => -T n) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hT
  have hlim :
      Tendsto
        (fun n : ℕ => ∫ t in (-T n)..(T n), f t)
        atTop
        (𝓝 (∫ t : ℝ, f t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral hf_int hneg hT
  simpa [VIntegral', VIntegral, VerticalIntegral', VerticalIntegral, f, sN] using
    (hlim.const_smul Complex.I).const_smul
      (1 / (2 * Real.pi * Complex.I) : ℂ)

lemma leftVertical_rpow_geometric_rewrite
    {x : ℝ} (hx : 1 < x)
    (N : ℕ) :
    x ^ (-(2 * (N : ℝ) + 1))
      =
    x ^ (-1 : ℝ) *
      (x ^ (-2 : ℝ)) ^ N := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hqpos : 0 < x ^ (-2 : ℝ) := Real.rpow_pos_of_pos hxpos _
  rw [← Real.rpow_natCast (x ^ (-2 : ℝ)) N]
  rw [← Real.rpow_mul (x := x) hxpos.le (-2 : ℝ) (N : ℝ)]
  rw [← Real.rpow_add hxpos]
  congr 1
  ring

theorem left_vertical_scalar_bound_tendsto_zero
    {x : ℝ} (hx : 1 < x) :
    Tendsto
      (fun N : ℕ =>
        leftVerticalScalarBound x (N + 1))
      atTop
      (𝓝 0) := by
  let q : ℝ := x ^ (-2 : ℝ)
  let C : ℝ :=
    2 * leftVerticalLogDerivConstant *
      leftVerticalUniversalMajorantMass *
      x ^ (-1 : ℝ)
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact le_of_lt (Real.rpow_pos_of_pos hxpos _)
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
  have hNq :
      Tendsto (fun N : ℕ => (N : ℝ) * q ^ N) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one hq_nonneg hq_lt_one
  have hqpow :
      Tendsto (fun N : ℕ => q ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one
  have hvar :
      Tendsto (fun N : ℕ => ((N : ℝ) + 2) * q ^ (N + 1)) atTop (𝓝 0) := by
    have hdecomp :
        (fun N : ℕ => ((N : ℝ) + 2) * q ^ (N + 1))
          =
        (fun N : ℕ => q * ((N : ℝ) * q ^ N) + (2 * q) * q ^ N) := by
      funext N
      rw [pow_succ']
      ring
    rw [hdecomp]
    simpa using (hNq.const_mul q).add (hqpow.const_mul (2 * q))
  have hmain :
      Tendsto (fun N : ℕ => C * (((N : ℝ) + 2) * q ^ (N + 1))) atTop (𝓝 0) := by
    simpa using hvar.const_mul C
  convert hmain using 1
  funext N
  rw [leftVerticalScalarBound, leftVertical_rpow_geometric_rewrite (x := x) hx (N + 1)]
  change
    2 * leftVerticalLogDerivConstant *
      leftVerticalUniversalMajorantMass *
      (((N + 1 : ℕ) : ℝ) + 1) *
      (x ^ (-1 : ℝ) * q ^ (N + 1))
      =
    C * (((N : ℝ) + 2) * q ^ (N + 1))
  dsimp [C]
  norm_num
  ring

theorem left_vertical_boundary_tendsto_zero
    {x : ℝ} (hx : 1 < x) :
    Tendsto
      (fun N : ℕ =>
        VerticalIntegral'
          (zetaPerronIntegrand x)
          (perronRectangleSigmaL (N + 1)))
      atTop
      (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero
    (fun N => norm_nonneg _)
    (fun N => by
      exact left_vertical_full_norm_le (x := x) hx (N := N + 1) (by omega))
    (left_vertical_scalar_bound_tendsto_zero (x := x) hx)

theorem exists_admissible_heights_all_left_boundary_limits
    {x σR : ℝ} (hx : 1 < x) (hσR : 1 < σR)
    {N : ℕ} (hN : 1 ≤ N) :
    ∃ T : ℕ → ℝ,
      (∀ n, PerronRectangleAdmissible x σR N (T n)) ∧
      Tendsto
        (fun n =>
          HIntegral' (zetaPerronIntegrand x)
            (perronRectangleSigmaL N) σR (T n))
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          HIntegral' (zetaPerronIntegrand x)
            (perronRectangleSigmaL N) σR (-(T n)))
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          VIntegral' (zetaPerronIntegrand x)
            (perronRectangleSigmaL N) (-(T n)) (T n))
        atTop
        (𝓝
          (VerticalIntegral'
            (zetaPerronIntegrand x)
            (perronRectangleSigmaL N))) := by
  obtain ⟨T, hTadm, hTtop, hTplus, hTminus⟩ :=
    P4_4d.exists_admissible_heights_horizontal_perron_integrals_tendsto_zero
      (x := x) (σR := σR) (N := N) hx hσR hN
  refine ⟨T, ?_, hTplus, hTminus, ?_⟩
  · intro n
    exact (hTadm n).2.2
  · exact left_vertical_truncated_tendsto_full (x := x) hx (N := N) hN hTtop

end P4_4e

end RHV3Lean
