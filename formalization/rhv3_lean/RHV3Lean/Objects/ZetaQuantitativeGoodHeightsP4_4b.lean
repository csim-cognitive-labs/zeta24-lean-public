/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaXiHadamardP4_4aExactContract
import RHV3Lean.Objects.ZetaPerronAdmissibleHeights

/-!
# P4.4b: quantitative good heights

This module starts from the exact P4.4a xi/Hadamard port and proves the
quantitative zero-counting and separation inputs needed for good Perron
heights. It does not prove any horizontal bound for `ζ'/ζ`.
-/

open Complex Set Finset BigOperators
open scoped Topology ComplexConjugate

noncomputable section

namespace RHV3Lean

namespace P4_4b

/-! ## Zeta zeros as xi divisor zeros -/

lemma riemannXi_eq_zero_of_isNontrivialZetaZero {ρ : ℂ}
    (hρ : RHV3Lean.IsNontrivialZetaZero ρ) :
    Complex.riemannXi ρ = 0 := by
  have hstrip := RHV3Lean.isNontrivialZetaZero_re_mem_Ioo hρ
  have hρ0 : ρ ≠ 0 := by
    intro h
    have hre : ρ.re = 0 := by simp [h]
    linarith [hstrip.1]
  have hρ1 : ρ ≠ 1 := by
    intro h
    have hre : ρ.re = 1 := by simp [h]
    linarith [hstrip.2]
  have hΓ : Complex.Gammaℝ ρ ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hstrip.1
  have hζdef : riemannZeta ρ = completedRiemannZeta ρ / Complex.Gammaℝ ρ :=
    riemannZeta_def_of_ne_zero hρ0
  have hΛ : completedRiemannZeta ρ = 0 := by
    have hmul : completedRiemannZeta ρ = riemannZeta ρ * Complex.Gammaℝ ρ := by
      rw [hζdef]
      field_simp [hΓ]
    rw [hmul, hρ.1, zero_mul]
  rw [Complex.riemannXi_eq_mul_completedRiemannZeta hρ0 hρ1, hΛ]
  ring

lemma exists_divisorZeroIndex₀_val_eq_of_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    {z : ℂ} (hz0 : z ≠ 0) (hz : f z = 0) :
    ∃ p : Complex.Hadamard.divisorZeroIndex₀ f (Set.univ : Set ℂ),
      Complex.Hadamard.divisorZeroIndex₀_val p = z := by
  classical
  have hnotTop : analyticOrderAt f z ≠ ⊤ :=
    Complex.Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero (f := f) hf hnot z
  have hord_ne0 : analyticOrderNatAt f z ≠ 0 := by
    intro h0
    have hEN : (analyticOrderNatAt f z : ENat) = 0 := by simp [h0]
    have hAt0 : analyticOrderAt f z = 0 := by
      have hcast : (analyticOrderNatAt f z : ENat) = analyticOrderAt f z :=
        Nat.cast_analyticOrderNatAt (f := f) (z₀ := z) hnotTop
      simpa [hcast] using hEN
    have han : AnalyticAt ℂ f z := hf.analyticAt z
    exact ((han.analyticOrderAt_eq_zero).1 hAt0) hz
  have hcard_pos :
      0 < (Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := f) z).card := by
    have hcard :=
      Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
        (hf := hf) (z₀ := z) hz0
    have : 0 < analyticOrderNatAt f z := Nat.pos_of_ne_zero hord_ne0
    simpa [hcard] using this
  rcases Finset.card_pos.mp hcard_pos with ⟨p, hp⟩
  exact ⟨p, (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset
    (f := f) (z₀ := z) p).1 hp⟩

lemma exists_riemannXi_divisorZeroIndex₀_val_eq_of_isNontrivialZetaZero
    {ρ : ℂ} (hρ : RHV3Lean.IsNontrivialZetaZero ρ) :
    ∃ p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
      Complex.Hadamard.divisorZeroIndex₀_val p = ρ := by
  have hstrip := RHV3Lean.isNontrivialZetaZero_re_mem_Ioo hρ
  have hρ0 : ρ ≠ 0 := by
    intro h
    have hre : ρ.re = 0 := by simp [h]
    linarith [hstrip.1]
  exact exists_divisorZeroIndex₀_val_eq_of_zero
    (f := Complex.riemannXi)
    Complex.differentiable_riemannXi
    Complex.riemannXi_nontrivial hρ0
    (riemannXi_eq_zero_of_isNontrivialZetaZero hρ)

lemma norm_complex_le_abs_re_add_abs_im (z : ℂ) :
    ‖z‖ ≤ |z.re| + |z.im| := by
  have hz :
      z = ((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  calc
    ‖z‖ = ‖((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I‖ :=
      congrArg norm hz
    _ ≤ ‖((z.re : ℝ) : ℂ)‖ + ‖((z.im : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |z.re| + |z.im| := by simp

lemma norm_le_height_plus_one_of_mem_nontrivialZetaZerosByHeightFinset
    {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ RHV3Lean.nontrivialZetaZerosByHeightFinset R) :
    ‖ρ‖ ≤ R + 1 := by
  have hmem := (RHV3Lean.mem_nontrivialZetaZerosByHeightFinset (T := R) (ρ := ρ)).1 hρ
  have hstrip := RHV3Lean.isNontrivialZetaZero_re_mem_Ioo hmem.1
  have hre_abs : |ρ.re| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [hstrip.1], le_of_lt hstrip.2⟩
  have him_abs : |ρ.im| ≤ R := le_of_lt hmem.2
  calc
    ‖ρ‖ ≤ |ρ.re| + |ρ.im| := norm_complex_le_abs_re_add_abs_im ρ
    _ ≤ 1 + R := add_le_add hre_abs him_abs
    _ = R + 1 := by ring

/-! ## Quantitative xi divisor mass -/

theorem riemannXi_divisorMassClosedBall₀_le_order_one_plus
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ R : ℝ, 1 ≤ R →
        Complex.Hadamard.divisorMassClosedBall₀ Complex.riemannXi R
          ≤ C * (1 + R) ^ (1 + ε) := by
  classical
  let τ : ℝ := 1 + ε
  have hτ_gt : (1 : ℝ) < τ := by dsimp [τ]; linarith
  have hτ_pos : 0 < τ := by linarith
  have hτ_nonneg : 0 ≤ τ := le_of_lt hτ_pos
  obtain ⟨C₀, hC₀_pos, hgrowth⟩ :=
    Complex.Hadamard.EntireOfOrderAtMost.exists_log_growth
      (ρ := (1 : ℝ)) (τ := τ) (f := Complex.riemannXi)
      riemannXi_entireOfOrderAtMost_one hτ_gt hτ_nonneg
  let K : ℝ := |Real.log ‖meromorphicTrailingCoeffAt Complex.riemannXi 0‖|
  let C : ℝ := (C₀ * 2 ^ τ + K) / Real.log 2 + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have htwoτ_nonneg : 0 ≤ (2 : ℝ) ^ τ :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) τ)
  have hcoef_nonneg : 0 ≤ C₀ * 2 ^ τ + K := by
    have hmul : 0 ≤ C₀ * 2 ^ τ := mul_nonneg (le_of_lt hC₀_pos) htwoτ_nonneg
    exact add_nonneg hmul (abs_nonneg _)
  have hC_pos : 0 < C := by
    have hdiv_nonneg : 0 ≤ (C₀ * 2 ^ τ + K) / Real.log 2 :=
      div_nonneg hcoef_nonneg (le_of_lt hlog2)
    dsimp [C]
    linarith
  refine ⟨C, hC_pos, ?_⟩
  intro R hR
  have hR_nonneg : 0 ≤ R := le_trans zero_le_one hR
  have hbase_pos : 0 < 1 + R := by linarith
  have hbase_nonneg : 0 ≤ 1 + R := le_of_lt hbase_pos
  have hbase_one : 1 ≤ 1 + R := by linarith
  have hX_nonneg : 0 ≤ (1 + R) ^ τ :=
    Real.rpow_nonneg hbase_nonneg τ
  have hX_one : 1 ≤ (1 + R) ^ τ :=
    calc
      (1 : ℝ) = (1 : ℝ) ^ τ := by rw [Real.one_rpow]
      _ ≤ (1 + R) ^ τ := Real.rpow_le_rpow zero_le_one hbase_one hτ_nonneg
  have htwoR_abs : |2 * R| = 2 * R := abs_of_nonneg (by nlinarith)
  have hscale : 1 + |2 * R| ≤ 2 * (1 + R) := by
    rw [htwoR_abs]
    ring_nf
    linarith
  have hscaled_nonneg : 0 ≤ 2 * (1 + R) := by positivity
  have hpow_scale :
      (1 + |2 * R|) ^ τ ≤ (2 * (1 + R)) ^ τ :=
    Real.rpow_le_rpow (by positivity) hscale hτ_nonneg
  have hmul_rpow :
      (2 * (1 + R)) ^ τ = 2 ^ τ * (1 + R) ^ τ :=
    Real.mul_rpow (by norm_num) hbase_nonneg
  have hmass :=
    Complex.Hadamard.divisorMassClosedBall₀_le_of_growth
      (f := Complex.riemannXi) (ρ := τ) (C := C₀)
      Complex.differentiable_riemannXi hgrowth hR
  have hnum_le :
      C₀ * (1 + |2 * R|) ^ τ + K
        ≤ (C₀ * 2 ^ τ + K) * (1 + R) ^ τ := by
    calc
      C₀ * (1 + |2 * R|) ^ τ + K
          ≤ C₀ * (2 * (1 + R)) ^ τ + K := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hpow_scale (le_of_lt hC₀_pos)) le_rfl
      _ = C₀ * (2 ^ τ * (1 + R) ^ τ) + K := by rw [hmul_rpow]
      _ = (C₀ * 2 ^ τ) * (1 + R) ^ τ + K := by ring
      _ ≤ (C₀ * 2 ^ τ) * (1 + R) ^ τ + K * (1 + R) ^ τ := by
            exact add_le_add le_rfl
              (le_mul_of_one_le_right (abs_nonneg _) hX_one)
      _ = (C₀ * 2 ^ τ + K) * (1 + R) ^ τ := by ring
  have hdiv_le :
      (C₀ * (1 + |2 * R|) ^ τ + K) / Real.log 2
        ≤ ((C₀ * 2 ^ τ + K) / Real.log 2) * (1 + R) ^ τ := by
    have :=
      div_le_div_of_nonneg_right hnum_le (le_of_lt hlog2)
    calc
      (C₀ * (1 + |2 * R|) ^ τ + K) / Real.log 2
          ≤ ((C₀ * 2 ^ τ + K) * (1 + R) ^ τ) / Real.log 2 := this
      _ = ((C₀ * 2 ^ τ + K) / Real.log 2) * (1 + R) ^ τ := by ring
  calc
    Complex.Hadamard.divisorMassClosedBall₀ Complex.riemannXi R
        ≤ (C₀ * (1 + |2 * R|) ^ τ + K) / Real.log 2 := hmass
    _ ≤ ((C₀ * 2 ^ τ + K) / Real.log 2) * (1 + R) ^ τ := hdiv_le
    _ ≤ C * (1 + R) ^ τ := by
        dsimp [C]
        exact mul_le_mul_of_nonneg_right (by linarith) hX_nonneg
    _ = C * (1 + R) ^ (1 + ε) := by rfl

theorem nontrivialZetaZerosByHeightFinset_card_le_riemannXi_divisorMassClosedBall₀
    (R : ℝ) (hR : 1 ≤ R) :
    ((RHV3Lean.nontrivialZetaZerosByHeightFinset R).card : ℝ)
      ≤ Complex.Hadamard.divisorMassClosedBall₀ Complex.riemannXi (R + 1) := by
  classical
  let S : Finset ℂ := RHV3Lean.nontrivialZetaZerosByHeightFinset R
  let A : Type := {ρ : ℂ // ρ ∈ S}
  let D : Type := Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)
  let Aball : Type := {p : D // ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ R + 1}
  haveI : Fintype A := by dsimp [A]; infer_instance
  haveI : Fintype Aball := by
    have : Finite Aball := by
      have hBU : Metric.closedBall (0 : ℂ) (R + 1) ⊆ (Set.univ : Set ℂ) := by simp
      simpa [Aball, D] using
        (Complex.Hadamard.finite_divisorZeroIndex₀_subtype_norm_le
          (f := Complex.riemannXi) (U := (Set.univ : Set ℂ)) (B := R + 1) hBU)
    exact Fintype.ofFinite _
  let chooseDivisor (ρ : A) : D :=
    Classical.choose
      (exists_riemannXi_divisorZeroIndex₀_val_eq_of_isNontrivialZetaZero
        ((RHV3Lean.mem_nontrivialZetaZerosByHeightFinset (T := R) (ρ := ρ.1)).1 ρ.2).1)
  have hchoose :
      ∀ ρ : A, Complex.Hadamard.divisorZeroIndex₀_val (chooseDivisor ρ) = ρ.1 := by
    intro ρ
    exact Classical.choose_spec
      (exists_riemannXi_divisorZeroIndex₀_val_eq_of_isNontrivialZetaZero
        ((RHV3Lean.mem_nontrivialZetaZerosByHeightFinset (T := R) (ρ := ρ.1)).1 ρ.2).1)
  let Φ : A → Aball := fun ρ =>
    ⟨chooseDivisor ρ, by
      rw [hchoose ρ]
      exact norm_le_height_plus_one_of_mem_nontrivialZetaZerosByHeightFinset ρ.2⟩
  have hΦinj : Function.Injective Φ := by
    intro ρ η h
    apply Subtype.ext
    have hval :
        Complex.Hadamard.divisorZeroIndex₀_val (Φ ρ).1 =
          Complex.Hadamard.divisorZeroIndex₀_val (Φ η).1 :=
      congrArg (fun p : Aball => Complex.Hadamard.divisorZeroIndex₀_val p.1) h
    simpa [Φ, hchoose ρ, hchoose η] using hval
  have hcardA_le : Fintype.card A ≤ Fintype.card Aball :=
    Fintype.card_le_of_injective Φ hΦinj
  have hcardS : Fintype.card A = S.card :=
    by simpa [A] using (Fintype.card_coe S)
  have hRpos : 0 < R + 1 := by linarith
  have hball :
      (Nat.card Aball : ℝ)
        ≤ Complex.Hadamard.divisorMassClosedBall₀ Complex.riemannXi (R + 1) := by
    simpa [Aball, D] using
      Complex.Hadamard.card_ball_le_divisorMassClosedBall₀
        (f := Complex.riemannXi) Complex.differentiable_riemannXi hRpos
  calc
    (S.card : ℝ) = (Fintype.card A : ℝ) := by rw [hcardS]
    _ ≤ (Fintype.card Aball : ℝ) := by exact_mod_cast hcardA_le
    _ = (Nat.card Aball : ℝ) := by simp [Nat.card_eq_fintype_card]
    _ ≤ Complex.Hadamard.divisorMassClosedBall₀ Complex.riemannXi (R + 1) := hball

theorem nontrivialZetaZerosByHeightFinset_card_le_order_one_plus
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ R : ℝ, 1 ≤ R →
        ((RHV3Lean.nontrivialZetaZerosByHeightFinset R).card : ℝ)
          ≤ C * (1 + R) ^ (1 + ε) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ :=
    riemannXi_divisorMassClosedBall₀_le_order_one_plus ε hε
  let τ : ℝ := 1 + ε
  let C : ℝ := C₀ * 2 ^ τ
  have hτ_pos : 0 < τ := by dsimp [τ]; linarith
  have hτ_nonneg : 0 ≤ τ := le_of_lt hτ_pos
  have htwoτ_pos : 0 < (2 : ℝ) ^ τ := Real.rpow_pos_of_pos (by norm_num) τ
  have hC_pos : 0 < C := mul_pos hC₀_pos htwoτ_pos
  refine ⟨C, hC_pos, ?_⟩
  intro R hR
  have hR1 : 1 ≤ R + 1 := by linarith
  have hbase_nonneg : 0 ≤ 1 + R := by linarith
  have hscale : 1 + (R + 1) ≤ 2 * (1 + R) := by
    ring_nf
    linarith
  have hpow :
      (1 + (R + 1)) ^ τ ≤ (2 * (1 + R)) ^ τ :=
    Real.rpow_le_rpow (by positivity) hscale hτ_nonneg
  have hmul_rpow :
      (2 * (1 + R)) ^ τ = 2 ^ τ * (1 + R) ^ τ :=
    Real.mul_rpow (by norm_num) hbase_nonneg
  calc
    ((RHV3Lean.nontrivialZetaZerosByHeightFinset R).card : ℝ)
        ≤ Complex.Hadamard.divisorMassClosedBall₀ Complex.riemannXi (R + 1) :=
          nontrivialZetaZerosByHeightFinset_card_le_riemannXi_divisorMassClosedBall₀ R hR
    _ ≤ C₀ * (1 + (R + 1)) ^ τ := hC₀ (R + 1) hR1
    _ ≤ C₀ * (2 * (1 + R)) ^ τ :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt hC₀_pos)
    _ = C₀ * (2 ^ τ * (1 + R) ^ τ) := by rw [hmul_rpow]
    _ = C * (1 + R) ^ (1 + ε) := by
        dsimp [C, τ]
        ring

/-! ## Quantitative finite separation -/

theorem exists_point_Ioo_separated_from_finset
    (s : Finset ℝ) (H : ℝ) :
    ∃ T : ℝ,
      H < T ∧
      T < H + 1 ∧
      ∀ x : ℝ, x ∈ s →
        1 / (4 * ((s.card : ℝ) + 1)) ≤ |T - x| := by
  classical
  let n : ℕ := s.card
  let δ : ℝ := 1 / (4 * ((n : ℝ) + 1))
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hden4_pos : 0 < 4 * ((n : ℝ) + 1) := by positivity
  have hden2_pos : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  by_contra h
  push Not at h
  let grid (i : Fin (n + 1)) : ℝ :=
    H + (((i : ℕ) : ℝ) + 1) / (2 * ((n : ℝ) + 1))
  have hgrid_mem :
      ∀ i : Fin (n + 1), H < grid i ∧ grid i < H + 1 := by
    intro i
    have hnum_pos : 0 < ((i : ℕ) : ℝ) + 1 := by positivity
    have hfrac_pos :
        0 < (((i : ℕ) : ℝ) + 1) / (2 * ((n : ℝ) + 1)) := by
      positivity
    have hi_le_nat : (i : ℕ) + 1 ≤ n + 1 := Nat.succ_le_of_lt i.2
    have hi_le : (((i : ℕ) : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      exact_mod_cast hi_le_nat
    have hfrac_le_one :
        (((i : ℕ) : ℝ) + 1) / (2 * ((n : ℝ) + 1)) < 1 := by
      have hhalf :
          (((i : ℕ) : ℝ) + 1) / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 := by
        rw [div_le_iff₀ hden2_pos]
        nlinarith
      nlinarith
    constructor <;> dsimp [grid]
    · linarith
    · linarith
  have hbad :
      ∀ i : Fin (n + 1), ∃ x ∈ s, |grid i - x| < δ := by
    intro i
    exact h (grid i) (hgrid_mem i).1 (hgrid_mem i).2
  let nearest (i : Fin (n + 1)) : s :=
    ⟨Classical.choose (hbad i), (Classical.choose_spec (hbad i)).1⟩
  have hnearest_close :
      ∀ i : Fin (n + 1), |grid i - (nearest i : ℝ)| < δ := by
    intro i
    exact (Classical.choose_spec (hbad i)).2
  have hcardlt : Fintype.card s < Fintype.card (Fin (n + 1)) := by
    simp [n]
  obtain ⟨i, j, hij_ne, hij_eq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt nearest hcardlt
  have hdist_upper : |grid i - grid j| < 2 * δ := by
    have hi := hnearest_close i
    have hj := hnearest_close j
    have htri : |grid i - grid j| ≤ |grid i - (nearest i : ℝ)| +
        |grid j - (nearest i : ℝ)| := by
      calc
        |grid i - grid j|
            = |(grid i - (nearest i : ℝ)) + ((nearest i : ℝ) - grid j)| := by
              rw [sub_add_sub_cancel]
        _ ≤ |grid i - (nearest i : ℝ)| + |(nearest i : ℝ) - grid j| :=
              abs_add_le _ _
        _ = |grid i - (nearest i : ℝ)| + |grid j - (nearest i : ℝ)| := by
              exact congrArg (fun y : ℝ => |grid i - (nearest i : ℝ)| + y)
                (abs_sub_comm (nearest i : ℝ) (grid j))
    have hj' : |grid j - (nearest i : ℝ)| < δ := by
      simpa [hij_eq] using hj
    nlinarith
  have hdist_lower :
      2 * δ ≤ |grid i - grid j| := by
    have hne_nat : (i : ℕ) ≠ (j : ℕ) := by
      intro hv
      exact hij_ne (Fin.ext hv)
    have hint_ne : ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) ≠ 0 := by
      intro hzero
      have hcast : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) := by omega
      exact hne_nat (by exact_mod_cast hcast)
    have hone_int : (1 : ℤ) ≤ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| :=
      Int.one_le_abs hint_ne
    have hone_real :
        (1 : ℝ) ≤ |(((i : ℕ) : ℝ) - ((j : ℕ) : ℝ))| := by
      exact_mod_cast hone_int
    have hgrid_diff :
        |grid i - grid j|
          = |(((i : ℕ) : ℝ) - ((j : ℕ) : ℝ))| / (2 * ((n : ℝ) + 1)) := by
      dsimp [grid]
      have hsub :
          H + (((i : ℕ) : ℝ) + 1) / (2 * ((n : ℝ) + 1)) -
              (H + (((j : ℕ) : ℝ) + 1) / (2 * ((n : ℝ) + 1)))
            = (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) / (2 * ((n : ℝ) + 1)) := by
        ring
      rw [hsub, abs_div]
      have hden_abs : |2 * ((n : ℝ) + 1)| = 2 * ((n : ℝ) + 1) :=
        abs_of_pos hden2_pos
      rw [hden_abs]
    have hlower :
        1 / (2 * ((n : ℝ) + 1))
          ≤ |(((i : ℕ) : ℝ) - ((j : ℕ) : ℝ))| /
              (2 * ((n : ℝ) + 1)) := by
      exact div_le_div_of_nonneg_right hone_real (le_of_lt hden2_pos)
    calc
      2 * δ = 1 / (2 * ((n : ℝ) + 1)) := by
        dsimp [δ]
        field_simp [show (4 : ℝ) * ((n : ℝ) + 1) ≠ 0 by positivity]
        ring
      _ ≤ |(((i : ℕ) : ℝ) - ((j : ℕ) : ℝ))| /
          (2 * ((n : ℝ) + 1)) := hlower
      _ = |grid i - grid j| := hgrid_diff.symm
  exact (not_lt_of_ge hdist_lower) hdist_upper

lemma nontrivialZetaForbiddenHeightsBelow_card_le
    (U : ℝ) :
    ((RHV3Lean.nontrivialZetaForbiddenHeightsBelow U).card : ℝ)
      ≤ ((RHV3Lean.nontrivialZetaZerosByHeightFinset U).card : ℝ) := by
  classical
  exact_mod_cast
    (Finset.card_image_le
      (s := RHV3Lean.nontrivialZetaZerosByHeightFinset U)
      (f := fun ρ : ℂ => |ρ.im|))

/-! ## Quantitative good heights -/

theorem exists_quantitative_good_height_between
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ H : ℝ, 1 ≤ H →
        ∃ T : ℝ,
          H < T ∧
          T < H + 1 ∧
          ∀ ρ : ℂ,
            RHV3Lean.IsNontrivialZetaZero ρ →
            1 / (C * (1 + H) ^ (1 + ε))
              ≤ |T - (|ρ.im|)| := by
  classical
  obtain ⟨C₀, hC₀_pos, hcount⟩ :=
    nontrivialZetaZerosByHeightFinset_card_le_order_one_plus ε hε
  let τ : ℝ := 1 + ε
  let A : ℝ := C₀ * 3 ^ τ + 1
  let C : ℝ := 8 * A
  have hτ_pos : 0 < τ := by dsimp [τ]; linarith
  have hτ_nonneg : 0 ≤ τ := le_of_lt hτ_pos
  have hthreeτ_pos : 0 < (3 : ℝ) ^ τ :=
    Real.rpow_pos_of_pos (by norm_num) τ
  have hA_pos : 0 < A := by
    dsimp [A]
    have hmul_pos : 0 < C₀ * 3 ^ τ := mul_pos hC₀_pos hthreeτ_pos
    linarith
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro H hH
  let U : ℝ := H + 2
  let s : Finset ℝ := RHV3Lean.nontrivialZetaForbiddenHeightsBelow U
  obtain ⟨T, hHT, hTH, hsep⟩ := exists_point_Ioo_separated_from_finset s H
  have hH_nonneg : 0 ≤ H := le_trans zero_le_one hH
  have hbase_pos : 0 < 1 + H := by linarith
  have hbase_nonneg : 0 ≤ 1 + H := le_of_lt hbase_pos
  have hbase_ge_one : 1 ≤ 1 + H := by linarith
  have hX_nonneg : 0 ≤ (1 + H) ^ τ :=
    Real.rpow_nonneg hbase_nonneg τ
  have hX_pos : 0 < (1 + H) ^ τ :=
    Real.rpow_pos_of_pos hbase_pos τ
  have hX_ge_one : 1 ≤ (1 + H) ^ τ := by
    calc
      (1 : ℝ) = (1 : ℝ) ^ τ := by rw [Real.one_rpow]
      _ ≤ (1 + H) ^ τ :=
        Real.rpow_le_rpow zero_le_one hbase_ge_one hτ_nonneg
  have hU_ge_one : 1 ≤ U := by dsimp [U]; linarith
  have hUscale : 1 + U ≤ 3 * (1 + H) := by
    dsimp [U]
    ring_nf
    linarith
  have hUpow :
      (1 + U) ^ τ ≤ (3 * (1 + H)) ^ τ :=
    Real.rpow_le_rpow (by dsimp [U]; positivity) hUscale hτ_nonneg
  have hmul_rpow :
      (3 * (1 + H)) ^ τ = 3 ^ τ * (1 + H) ^ τ :=
    Real.mul_rpow (by norm_num) hbase_nonneg
  have hs_card_bound :
      ((s.card : ℝ) + 1) ≤ A * (1 + H) ^ τ := by
    have hs_card_le_count :
        ((s.card : ℝ) + 1)
          ≤ ((RHV3Lean.nontrivialZetaZerosByHeightFinset U).card : ℝ) + 1 := by
      have hbase :
          (s.card : ℝ)
            ≤ ((RHV3Lean.nontrivialZetaZerosByHeightFinset U).card : ℝ) := by
        simpa [s] using nontrivialZetaForbiddenHeightsBelow_card_le U
      linarith
    have hcountU :
        ((RHV3Lean.nontrivialZetaZerosByHeightFinset U).card : ℝ)
          ≤ C₀ * (1 + U) ^ τ := by
      simpa [τ] using hcount U hU_ge_one
    have hcount_scaled :
        ((RHV3Lean.nontrivialZetaZerosByHeightFinset U).card : ℝ)
          ≤ (C₀ * 3 ^ τ) * (1 + H) ^ τ := by
      calc
        ((RHV3Lean.nontrivialZetaZerosByHeightFinset U).card : ℝ)
            ≤ C₀ * (1 + U) ^ τ := hcountU
        _ ≤ C₀ * (3 * (1 + H)) ^ τ :=
            mul_le_mul_of_nonneg_left hUpow (le_of_lt hC₀_pos)
        _ = C₀ * (3 ^ τ * (1 + H) ^ τ) := by rw [hmul_rpow]
        _ = (C₀ * 3 ^ τ) * (1 + H) ^ τ := by ring
    calc
      ((s.card : ℝ) + 1)
          ≤ ((RHV3Lean.nontrivialZetaZerosByHeightFinset U).card : ℝ) + 1 :=
            hs_card_le_count
      _ ≤ (C₀ * 3 ^ τ) * (1 + H) ^ τ + 1 := by
            linarith
      _ ≤ (C₀ * 3 ^ τ) * (1 + H) ^ τ + 1 * (1 + H) ^ τ := by
            have hx1 : (1 : ℝ) ≤ 1 * (1 + H) ^ τ := by
              simpa using hX_ge_one
            linarith
      _ = A * (1 + H) ^ τ := by
            dsimp [A]
            ring
  have hden_sep_pos : 0 < 4 * ((s.card : ℝ) + 1) := by positivity
  have hden_goal_pos : 0 < C * (1 + H) ^ τ := by positivity
  have hden_order :
      4 * ((s.card : ℝ) + 1) ≤ C * (1 + H) ^ τ := by
    calc
      4 * ((s.card : ℝ) + 1)
          ≤ 4 * (A * (1 + H) ^ τ) :=
            mul_le_mul_of_nonneg_left hs_card_bound (by norm_num)
      _ ≤ 8 * A * (1 + H) ^ τ := by
            have hAX_nonneg : 0 ≤ A * (1 + H) ^ τ :=
              mul_nonneg (le_of_lt hA_pos) hX_nonneg
            nlinarith
      _ = C * (1 + H) ^ τ := by
            rfl
  have hsmall_lower :
      1 / (C * (1 + H) ^ τ)
        ≤ 1 / (4 * ((s.card : ℝ) + 1)) :=
    one_div_le_one_div_of_le hden_sep_pos hden_order
  have hlarge_lower :
      1 / (C * (1 + H) ^ τ) ≤ 1 := by
    have hden_ge_one : 1 ≤ C * (1 + H) ^ τ := by
      have hC_ge_one : 1 ≤ C := by
        dsimp [C, A]
        have hmul_pos : 0 < C₀ * 3 ^ τ := mul_pos hC₀_pos hthreeτ_pos
        nlinarith
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ C * (1 + H) ^ τ :=
          mul_le_mul hC_ge_one hX_ge_one zero_le_one (le_of_lt hC_pos)
    calc
      1 / (C * (1 + H) ^ τ) ≤ 1 / 1 :=
        one_div_le_one_div_of_le zero_lt_one hden_ge_one
      _ = 1 := by norm_num
  refine ⟨T, hHT, hTH, ?_⟩
  intro ρ hρ
  by_cases hsmall : |ρ.im| < U
  · have hmem : |ρ.im| ∈ s := by
      dsimp [s]
      exact RHV3Lean.abs_im_mem_forbiddenHeightsBelow hρ hsmall
    exact le_trans hsmall_lower (hsep |ρ.im| hmem)
  · have hU_le : U ≤ |ρ.im| := le_of_not_gt hsmall
    have hdist_ge_one : 1 ≤ |T - (|ρ.im|)| := by
      have hle : T + 1 ≤ |ρ.im| := by
        dsimp [U] at hU_le
        linarith
      have hnonpos : T - |ρ.im| ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      linarith
    exact le_trans hlarge_lower hdist_ge_one

theorem exists_quantitative_perronRectangleAdmissible_height_between
    {x σR : ℝ} {N : ℕ}
    (hx : 1 < x)
    (hσR : 1 < σR)
    (hN : 1 ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ H : ℝ, 1 ≤ H →
        ∃ T : ℝ,
          H < T ∧
          T < H + 1 ∧
          RHV3Lean.PerronRectangleAdmissible x σR N T ∧
          ∀ ρ : ℂ,
            RHV3Lean.IsNontrivialZetaZero ρ →
            1 / (C * (1 + H) ^ (1 + ε))
              ≤ |T - (|ρ.im|)| := by
  classical
  obtain ⟨C, hC_pos, hgood⟩ := exists_quantitative_good_height_between ε hε
  refine ⟨C, hC_pos, ?_⟩
  intro H hH
  obtain ⟨T, hHT, hTH, hsep⟩ := hgood H hH
  have hTpos : 0 < T := by linarith [hH, hHT]
  have hτ_pos : 0 < 1 + ε := by linarith
  have hbase_pos : 0 < 1 + H := by linarith
  have hpow_pos : 0 < (1 + H) ^ (1 + ε) :=
    Real.rpow_pos_of_pos hbase_pos (1 + ε)
  have hden_pos : 0 < C * (1 + H) ^ (1 + ε) :=
    mul_pos hC_pos hpow_pos
  have hlower_pos : 0 < 1 / (C * (1 + H) ^ (1 + ε)) := by
    positivity
  have hfree :
      ∀ ρ : ℂ,
        RHV3Lean.IsNontrivialZetaZero ρ →
        |ρ.im| ≠ T := by
    intro ρ hρ heq
    have hdist := hsep ρ hρ
    have habs0 : |T - (|ρ.im|)| = 0 := by
      simp [heq]
    rw [habs0] at hdist
    linarith
  refine ⟨T, hHT, hTH, ?_, hsep⟩
  exact RHV3Lean.perronRectangleAdmissible_of_zero_free_height hx hσR hN hTpos hfree

end P4_4b

end RHV3Lean
