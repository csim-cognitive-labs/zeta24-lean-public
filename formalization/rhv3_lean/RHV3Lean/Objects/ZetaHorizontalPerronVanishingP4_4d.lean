/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaHorizontalLogDerivBoundP4_4c
import RHV3Lean.Objects.ZetaPerronFiniteRectangle
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# P4.4d: vanishing of the two horizontal Perron-zeta integrals

This file combines the P4.4c admissible-height horizontal bound for `-ζ'/ζ`
with the exact Perron kernel `x^s/(s*(s+1))` and the genuine P3c2
horizontal integral `HIntegral'`.
-/

open Complex Set Filter MeasureTheory intervalIntegral LSeries.notation
open scoped Topology Interval

noncomputable section

namespace RHV3Lean

namespace P4_4d

private lemma one_half_pos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num

private lemma one_half_lt_one : (1 / 2 : ℝ) < 1 := by norm_num

lemma perronRectangleSigmaL_le_sigmaR {σR : ℝ} {N : ℕ}
    (hσR : 1 < σR) (hN : 1 ≤ N) :
    perronRectangleSigmaL N ≤ σR := by
  unfold perronRectangleSigmaL
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [hNreal, hσR]

lemma perron_kernel_horizontal_bound
    {x σR : ℝ} {N : ℕ}
    (hx : 1 < x) (_hσR : 1 < σR) (_hN : 1 ≤ N) :
    ∃ CK : ℝ, 0 < CK ∧
      ∀ T : ℝ, 1 ≤ T →
      ∀ σ : ℝ, perronRectangleSigmaL N ≤ σ → σ ≤ σR →
        ‖Perron.f x (σ + T * I)‖ ≤ CK / T ^ 2 ∧
        ‖Perron.f x (σ - T * I)‖ ≤ CK / T ^ 2 := by
  classical
  let CK : ℝ := x ^ σR
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hCKpos : 0 < CK := Real.rpow_pos_of_pos hxpos σR
  refine ⟨CK, hCKpos, ?_⟩
  intro T hT σ hσL hσσR
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT2pos : 0 < T ^ 2 := sq_pos_of_pos hTpos
  have hxσ_le : x ^ σ ≤ CK := by
    exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hx) hσσR
  have hxσ_nonneg : 0 ≤ x ^ σ := Real.rpow_nonneg (le_of_lt hxpos) σ
  have hplus_s_norm : T ≤ ‖(σ : ℂ) + T * I‖ := by
    simpa [abs_of_nonneg (le_of_lt hTpos)] using
      (Complex.abs_im_le_norm ((σ : ℂ) + T * I))
  have hplus_s1_norm : T ≤ ‖((σ : ℂ) + T * I) + 1‖ := by
    simpa [abs_of_nonneg (le_of_lt hTpos), add_assoc, add_comm, add_left_comm] using
      (Complex.abs_im_le_norm (((σ : ℂ) + T * I) + 1))
  have hminus_s_norm : T ≤ ‖(σ : ℂ) - T * I‖ := by
    simpa [abs_of_nonneg (le_of_lt hTpos), abs_neg] using
      (Complex.abs_im_le_norm ((σ : ℂ) - T * I))
  have hminus_s1_norm : T ≤ ‖((σ : ℂ) - T * I) + 1‖ := by
    simpa [abs_of_nonneg (le_of_lt hTpos), abs_neg, add_assoc, add_comm, add_left_comm] using
      (Complex.abs_im_le_norm (((σ : ℂ) - T * I) + 1))
  constructor
  · have hden :
        T ^ 2 ≤ ‖(σ : ℂ) + T * I‖ * ‖((σ : ℂ) + T * I) + 1‖ := by
      nlinarith [hplus_s_norm, hplus_s1_norm, hTpos,
        norm_nonneg ((σ : ℂ) + T * I), norm_nonneg (((σ : ℂ) + T * I) + 1)]
    have hdenpos : 0 < ‖(σ : ℂ) + T * I‖ * ‖((σ : ℂ) + T * I) + 1‖ :=
      lt_of_lt_of_le hT2pos hden
    rw [Perron.f, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp only [ofReal_re, add_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero, sub_zero,
      add_zero]
    calc
      x ^ σ / (‖(σ : ℂ) + T * I‖ * ‖((σ : ℂ) + T * I) + 1‖)
          ≤ CK / (T ^ 2) := by
            exact div_le_div₀ (le_of_lt hCKpos) hxσ_le hT2pos hden
      _ = CK / T ^ 2 := rfl
  · have hden :
        T ^ 2 ≤ ‖(σ : ℂ) - T * I‖ * ‖((σ : ℂ) - T * I) + 1‖ := by
      nlinarith [hminus_s_norm, hminus_s1_norm, hTpos,
        norm_nonneg ((σ : ℂ) - T * I), norm_nonneg (((σ : ℂ) - T * I) + 1)]
    have hdenpos : 0 < ‖(σ : ℂ) - T * I‖ * ‖((σ : ℂ) - T * I) + 1‖ :=
      lt_of_lt_of_le hT2pos hden
    rw [Perron.f, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp only [ofReal_re, sub_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero, sub_zero]
    calc
      x ^ σ / (‖(σ : ℂ) - T * I‖ * ‖((σ : ℂ) - T * I) + 1‖)
          ≤ CK / (T ^ 2) := by
            exact div_le_div₀ (le_of_lt hCKpos) hxσ_le hT2pos hden
      _ = CK / T ^ 2 := rfl

lemma zetaPerronIntegrand_horizontal_pointwise_bound
    {x σR : ℝ} {N : ℕ}
    (hx : 1 < x) (hσR : 1 < σR) (hN : 1 ≤ N) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ H : ℝ, 1 ≤ H →
        ∃ T : ℝ,
          H < T ∧
          T < H + 1 ∧
          PerronRectangleAdmissible x σR N T ∧
          (∀ σ : ℝ, perronRectangleSigmaL N ≤ σ → σ ≤ σR →
            ‖zetaPerronIntegrand x (σ + T * I)‖
              ≤ C0 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2) ∧
          (∀ σ : ℝ, perronRectangleSigmaL N ≤ σ → σ ≤ σR →
            ‖zetaPerronIntegrand x (σ - T * I)‖
              ≤ C0 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2) := by
  classical
  obtain ⟨Cζ, hCζpos, hCζ⟩ :=
    P4_4c.exists_perron_height_with_horizontal_negLogDeriv_bound
      (x := x) (σR := σR) (N := N) hx hσR hN (1 / 2) one_half_pos one_half_lt_one
  obtain ⟨CK, hCKpos, hCK⟩ := perron_kernel_horizontal_bound hx hσR hN
  let C0 : ℝ := Cζ * CK
  have hC0pos : 0 < C0 := mul_pos hCζpos hCKpos
  refine ⟨C0, hC0pos, ?_⟩
  intro H hH
  obtain ⟨T, hHT, hTH, hadm, hζplus, hζminus⟩ := hCζ H hH
  have hTge : 1 ≤ T := by linarith
  refine ⟨T, hHT, hTH, hadm, ?_, ?_⟩
  · intro σ hσL hσσR
    have hk := (hCK T hTge σ hσL hσσR).1
    have hζ : ‖-logDeriv riemannZeta ((σ : ℂ) + T * I)‖
        ≤ Cζ * (1 + H) ^ (1 + (1 / 2 : ℝ)) := by
      simpa [logDeriv, neg_div] using hζplus σ hσL hσσR
    have hpow :
        (1 + H) ^ (1 + (1 / 2 : ℝ)) = (1 + H) ^ (3 / 2 : ℝ) := by ring_nf
    rw [zetaPerronIntegrand, norm_mul]
    calc
      ‖-logDeriv riemannZeta ((σ : ℂ) + T * I)‖ *
          ‖Perron.f x ((σ : ℂ) + T * I)‖
          ≤ (Cζ * (1 + H) ^ (1 + (1 / 2 : ℝ))) * (CK / T ^ 2) := by
            exact mul_le_mul hζ hk (norm_nonneg _) (mul_nonneg (le_of_lt hCζpos)
              (Real.rpow_nonneg (by linarith : 0 ≤ 1 + H) _))
      _ = C0 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2 := by
            rw [hpow]
            change Cζ * (1 + H) ^ (3 / 2 : ℝ) * (CK / T ^ 2) =
              (Cζ * CK) * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2
            ring_nf
  · intro σ hσL hσσR
    have hk := (hCK T hTge σ hσL hσσR).2
    have hζ : ‖-logDeriv riemannZeta ((σ : ℂ) - T * I)‖
        ≤ Cζ * (1 + H) ^ (1 + (1 / 2 : ℝ)) := by
      simpa [logDeriv, neg_div] using hζminus σ hσL hσσR
    have hpow :
        (1 + H) ^ (1 + (1 / 2 : ℝ)) = (1 + H) ^ (3 / 2 : ℝ) := by ring_nf
    rw [zetaPerronIntegrand, norm_mul]
    calc
      ‖-logDeriv riemannZeta ((σ : ℂ) - T * I)‖ *
          ‖Perron.f x ((σ : ℂ) - T * I)‖
          ≤ (Cζ * (1 + H) ^ (1 + (1 / 2 : ℝ))) * (CK / T ^ 2) := by
            exact mul_le_mul hζ hk (norm_nonneg _) (mul_nonneg (le_of_lt hCζpos)
              (Real.rpow_nonneg (by linarith : 0 ≤ 1 + H) _))
      _ = C0 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2 := by
            rw [hpow]
            change Cζ * (1 + H) ^ (3 / 2 : ℝ) * (CK / T ^ 2) =
              (Cζ * CK) * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2
            ring_nf

lemma horizontal_HIntegral'_norm_le
    {F : ℂ → ℂ} {σL σR y B : ℝ}
    (hσ : σL ≤ σR)
    (_hB : 0 ≤ B)
    (hF : ∀ σ : ℝ, σL ≤ σ → σ ≤ σR → ‖F (σ + y * I)‖ ≤ B) :
    ‖HIntegral' F σL σR y‖ ≤ ‖(1 / (2 * Real.pi * I) : ℂ)‖ * ((σR - σL) * B) := by
  have hlen_nonneg : 0 ≤ σR - σL := sub_nonneg.mpr hσ
  have hseg :
      ‖HIntegral F σL σR y‖ ≤ B * |σR - σL| := by
    rw [HIntegral]
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun σ hσmem => by
        have hleft : σL ≤ σ := by
          have hmem : σ ∈ Ioc σL σR := by
            simpa [uIoc_of_le hσ] using hσmem
          exact le_of_lt hmem.1
        have hright : σ ≤ σR := by
          have hmem : σ ∈ Ioc σL σR := by
            simpa [uIoc_of_le hσ] using hσmem
          exact hmem.2
        exact hF σ hleft hright)
  rw [HIntegral', norm_smul]
  calc
    ‖(1 / (2 * ↑Real.pi * I) : ℂ)‖ * ‖HIntegral F σL σR y‖
        ≤ ‖(1 / (2 * ↑Real.pi * I) : ℂ)‖ * (B * |σR - σL|) := by
          exact mul_le_mul_of_nonneg_left hseg (norm_nonneg _)
    _ = ‖(1 / (2 * ↑Real.pi * I) : ℂ)‖ * ((σR - σL) * B) := by
          rw [abs_of_nonneg hlen_nonneg]
          ring

lemma zetaPerron_horizontal_integrals_bound
    {x σR : ℝ} {N : ℕ}
    (hx : 1 < x) (hσR : 1 < σR) (hN : 1 ≤ N) :
    ∃ C1 : ℝ, 0 < C1 ∧
      ∀ H : ℝ, 1 ≤ H →
        ∃ T : ℝ,
          H < T ∧
          T < H + 1 ∧
          PerronRectangleAdmissible x σR N T ∧
          ‖HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR T‖
            ≤ C1 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2 ∧
          ‖HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR (-T)‖
            ≤ C1 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2 := by
  classical
  obtain ⟨C0, hC0pos, hC0⟩ :=
    zetaPerronIntegrand_horizontal_pointwise_bound (x := x) (σR := σR) (N := N) hx hσR hN
  let Len : ℝ := σR - perronRectangleSigmaL N
  let A : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖
  let C1 : ℝ := A * Len * C0
  have hσLσR : perronRectangleSigmaL N ≤ σR := perronRectangleSigmaL_le_sigmaR hσR hN
  have hLenpos : 0 < Len := by
    dsimp [Len]
    unfold perronRectangleSigmaL
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [hNreal, hσR]
  have hApos : 0 < A := by
    dsimp [A]
    apply norm_pos_iff.mpr
    exact div_ne_zero one_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
        (ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  have hC1pos : 0 < C1 := by
    dsimp [C1]
    exact mul_pos (mul_pos hApos hLenpos) hC0pos
  refine ⟨C1, hC1pos, ?_⟩
  intro H hH
  obtain ⟨T, hHT, hTH, hadm, hp, hm⟩ := hC0 H hH
  have hTpos : 0 < T := by linarith
  have hT2nonneg : 0 ≤ T ^ 2 := sq_nonneg T
  have hbase_nonneg : 0 ≤ (1 + H) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (by linarith : 0 ≤ 1 + H) _
  have hBnonneg : 0 ≤ C0 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2 := by positivity
  refine ⟨T, hHT, hTH, hadm, ?_, ?_⟩
  · have hb := horizontal_HIntegral'_norm_le
      (F := zetaPerronIntegrand x)
      (σL := perronRectangleSigmaL N) (σR := σR) (y := T)
      (B := C0 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2)
      hσLσR hBnonneg hp
    calc
      ‖HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR T‖
          ≤ A * (Len * (C0 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2)) := by
            simpa [A, Len] using hb
      _ = C1 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2 := by
            change A * (Len * (C0 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2)) =
              (A * Len * C0) * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2
            ring_nf
  · have hm' : ∀ σ : ℝ, perronRectangleSigmaL N ≤ σ → σ ≤ σR →
        ‖zetaPerronIntegrand x ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
          C0 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2 := by
      intro σ hσl hσr
      simpa [sub_eq_add_neg, ofReal_neg, neg_mul] using hm σ hσl hσr
    have hb := horizontal_HIntegral'_norm_le
      (F := zetaPerronIntegrand x)
      (σL := perronRectangleSigmaL N) (σR := σR) (y := -T)
      (B := C0 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2)
      hσLσR hBnonneg hm'
    calc
      ‖HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR (-T)‖
          ≤ A * (Len * (C0 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2)) := by
            simpa [A, Len] using hb
      _ = C1 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2 := by
            change A * (Len * (C0 * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2)) =
              (A * Len * C0) * (1 + H) ^ (3 / 2 : ℝ) / T ^ 2
            ring_nf

lemma rpow_three_halves_div_sq_le_four_inv_sqrt {H T : ℝ}
    (hH : 1 ≤ H) (hHT : H < T) :
    (1 + H) ^ (3 / 2 : ℝ) / T ^ 2 ≤ 4 / Real.sqrt (1 + H) := by
  have hbase_pos : 0 < 1 + H := by linarith
  have hsqrt_pos : 0 < Real.sqrt (1 + H) := Real.sqrt_pos.2 hbase_pos
  have hTpos : 0 < T := by linarith
  have hT2pos : 0 < T ^ 2 := sq_pos_of_pos hTpos
  have hden : (1 + H) ^ 2 / 4 ≤ T ^ 2 := by
    have hhalf : (1 + H) / 2 ≤ H := by linarith
    have hhalf_nonneg : 0 ≤ (1 + H) / 2 := by positivity
    have hleT : (1 + H) / 2 ≤ T := le_trans hhalf (le_of_lt hHT)
    have hsquare := (sq_le_sq₀ hhalf_nonneg (le_of_lt hTpos)).2 hleT
    nlinarith
  have hnum_nonneg : 0 ≤ (1 + H) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (le_of_lt hbase_pos) _
  calc
    (1 + H) ^ (3 / 2 : ℝ) / T ^ 2
        ≤ (1 + H) ^ (3 / 2 : ℝ) / ((1 + H) ^ 2 / 4) := by
          have hsmall_pos : 0 < (1 + H) ^ 2 / 4 := by positivity
          exact div_le_div_of_nonneg_left hnum_nonneg hsmall_pos hden
    _ = 4 / Real.sqrt (1 + H) := by
          rw [Real.sqrt_eq_rpow]
          field_simp [Real.rpow_pos_of_pos hbase_pos (1 / 2 : ℝ),
            Real.rpow_pos_of_pos hbase_pos (2 : ℝ)]
          rw [← Real.rpow_add hbase_pos]
          norm_num

lemma zetaPerron_horizontal_integrals_sqrt_bound
    {x σR : ℝ} {N : ℕ}
    (hx : 1 < x) (hσR : 1 < σR) (hN : 1 ≤ N) :
    ∃ C2 : ℝ, 0 < C2 ∧
      ∀ H : ℝ, 1 ≤ H →
        ∃ T : ℝ,
          H < T ∧
          T < H + 1 ∧
          PerronRectangleAdmissible x σR N T ∧
          ‖HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR T‖
            ≤ C2 / Real.sqrt (1 + H) ∧
          ‖HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR (-T)‖
            ≤ C2 / Real.sqrt (1 + H) := by
  obtain ⟨C1, hC1pos, hC1⟩ := zetaPerron_horizontal_integrals_bound hx hσR hN
  let C2 : ℝ := 4 * C1
  have hC2pos : 0 < C2 := by dsimp [C2]; positivity
  refine ⟨C2, hC2pos, ?_⟩
  intro H hH
  obtain ⟨T, hHT, hTH, hadm, hp, hm⟩ := hC1 H hH
  have hsqrt := rpow_three_halves_div_sq_le_four_inv_sqrt hH hHT
  have hmul :
      C1 * ((1 + H) ^ (3 / 2 : ℝ) / T ^ 2) ≤ C1 * (4 / Real.sqrt (1 + H)) :=
    mul_le_mul_of_nonneg_left hsqrt (le_of_lt hC1pos)
  refine ⟨T, hHT, hTH, hadm, ?_, ?_⟩
  · exact hp.trans (by simpa [C2, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hmul)
  · exact hm.trans (by simpa [C2, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hmul)

theorem exists_admissible_heights_horizontal_perron_integrals_tendsto_zero
    {x σR : ℝ} {N : ℕ}
    (hx : 1 < x) (hσR : 1 < σR) (hN : 1 ≤ N) :
    ∃ T : ℕ → ℝ,
      (∀ n : ℕ,
        (n : ℝ) + 1 < T n ∧
        T n < (n : ℝ) + 2 ∧
        PerronRectangleAdmissible x σR N (T n)) ∧
      Tendsto T atTop atTop ∧
      Tendsto
        (fun n =>
          HIntegral' (zetaPerronIntegrand x)
            (perronRectangleSigmaL N) σR (T n))
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          HIntegral' (zetaPerronIntegrand x)
            (perronRectangleSigmaL N) σR (-T n))
        atTop (𝓝 0) := by
  classical
  obtain ⟨C2, hC2pos, hC2⟩ :=
    zetaPerron_horizontal_integrals_sqrt_bound (x := x) (σR := σR) (N := N) hx hσR hN
  have hchoice : ∀ n : ℕ, ∃ T : ℝ,
      (n : ℝ) + 1 < T ∧
      T < (n : ℝ) + 1 + 1 ∧
      PerronRectangleAdmissible x σR N T ∧
      ‖HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR T‖
        ≤ C2 / Real.sqrt (1 + ((n : ℝ) + 1)) ∧
      ‖HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR (-T)‖
        ≤ C2 / Real.sqrt (1 + ((n : ℝ) + 1)) := by
    intro n
    exact hC2 ((n : ℝ) + 1) (by exact_mod_cast Nat.succ_pos n)
  choose T hTlow hThigh hTadm hTplus hTminus using hchoice
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨hTlow n, by nlinarith [hThigh n], hTadm n⟩
  · refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    exact le_of_lt (hTlow n)
  · have hbound : ∀ n : ℕ,
        ‖HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR (T n)‖
          ≤ C2 / Real.sqrt (1 + ((n : ℝ) + 1)) := hTplus
    have hlim_bound :
        Tendsto (fun n : ℕ => C2 / Real.sqrt (1 + ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have hsqrt_atTop :
          Tendsto (fun n : ℕ => Real.sqrt (1 + ((n : ℝ) + 1))) atTop atTop := by
        have hlin : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
          tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
        convert Real.tendsto_sqrt_atTop.comp hlin using 1
        ext n
        congr 1
        ring
      simpa [div_eq_mul_inv, zero_mul] using
        (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hsqrt_atTop) : Tendsto
          (fun n : ℕ => C2 * (Real.sqrt (1 + ((n : ℝ) + 1)))⁻¹) atTop (𝓝 (C2 * 0)))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hbound hlim_bound
  · have hbound : ∀ n : ℕ,
        ‖HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR (-(T n))‖
          ≤ C2 / Real.sqrt (1 + ((n : ℝ) + 1)) := hTminus
    have hlim_bound :
        Tendsto (fun n : ℕ => C2 / Real.sqrt (1 + ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have hsqrt_atTop :
          Tendsto (fun n : ℕ => Real.sqrt (1 + ((n : ℝ) + 1))) atTop atTop := by
        have hlin : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
          tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
        convert Real.tendsto_sqrt_atTop.comp hlin using 1
        ext n
        congr 1
        ring
      simpa [div_eq_mul_inv, zero_mul] using
        (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hsqrt_atTop) : Tendsto
          (fun n : ℕ => C2 * (Real.sqrt (1 + ((n : ℝ) + 1)))⁻¹) atTop (𝓝 (C2 * 0)))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hbound hlim_bound

end P4_4d

end RHV3Lean
