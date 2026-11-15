/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
P4.4a exact-source contract for the Riemann xi / Hadamard port.
-/

import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.CompletedXi
import RHV3Lean.Objects.P4Port.Analysis.Complex.HadamardFactorization.Order
import RHV3Lean.Objects.P4Port.NumberTheory.LSeries.RiemannZetaHadamard
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.Gamma.DigammaSeries
import RHV3Lean.Objects.P4Port.IEANTN.HadamardLogDerivative

@[expose] public section

noncomputable section

open Complex Set
open scoped BigOperators

example (s : ℂ) :
    Complex.riemannXi s =
      (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2 := by
  rfl

example (ρ : ℝ) (f : ℂ → ℂ) :
    Complex.Hadamard.EntireOfOrderAtMost ρ f ↔
      Differentiable ℂ f ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ C > 0, ∀ z : ℂ,
            ‖f z‖ ≤
              Real.exp
                (C * (1 + ‖z‖) ^ (ρ + ε)) := by
  rfl

example (f : ℂ → ℂ) (U : Set ℂ) :
    Complex.Hadamard.divisorZeroIndex f U =
      (Σ z : ℂ, Fin (Int.toNat (MeromorphicOn.divisor f U z))) := by
  rfl

example (f : ℂ → ℂ) (U : Set ℂ) :
    Complex.Hadamard.divisorZeroIndex₀ f U =
      {p : Complex.Hadamard.divisorZeroIndex f U // p.1 ≠ 0} := by
  rfl

example {f : ℂ → ℂ} {U : Set ℂ} (p : Complex.Hadamard.divisorZeroIndex₀ f U) :
    Complex.Hadamard.divisorZeroIndex₀_val p = p.1.1 := by
  rfl

example (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) (z : ℂ) :
    Complex.Hadamard.divisorCanonicalProduct m f U z =
      ∏' p : Complex.Hadamard.divisorZeroIndex₀ f U,
        Complex.weierstrassFactor
          m
          (z / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  rfl

example : Complex.riemannXi 0 = 1 / 2 := by
  exact Complex.riemannXi_zero

example : ∃ s : ℂ, Complex.riemannXi s ≠ 0 := by
  exact Complex.riemannXi_nontrivial

example : Differentiable ℂ Complex.riemannXi := by
  exact Complex.differentiable_riemannXi

example (s : ℂ) : Complex.riemannXi (1 - s) = Complex.riemannXi s := by
  exact Complex.riemannXi_one_sub s

example {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    Complex.riemannXi s =
      s * (s - 1) * completedRiemannZeta s / 2 := by
  exact Complex.riemannXi_eq_mul_completedRiemannZeta hs0 hs1

example {ρ : ℝ} {f : ℂ → ℂ} (h : Complex.Hadamard.EntireOfOrderAtMost ρ f) :
    Differentiable ℂ f := by
  exact Complex.Hadamard.EntireOfOrderAtMost.differentiable h

example {ρ ε : ℝ} {f : ℂ → ℂ} (h : Complex.Hadamard.EntireOfOrderAtMost ρ f)
    (hε : 0 < ε) :
    ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε)) := by
  exact Complex.Hadamard.EntireOfOrderAtMost.exists_bound h hε

example {ρ : ℝ} {f : ℂ → ℂ}
    (h : Complex.Hadamard.EntireOfOrderAtMost ρ f) (hρ : 0 ≤ ρ)
    (hnot : ∃ z : ℂ, f z ≠ 0) :
    Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (Nat.floor ρ + 1)) := by
  exact Complex.Hadamard.EntireOfOrderAtMost.summable_norm_inv_pow_divisorZeroIndex₀
    h hρ hnot

example : Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) Complex.riemannXi := by
  exact riemannXi_entireOfOrderAtMost_one

example :
    Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi
        (Set.univ : Set ℂ) =>
      ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)) := by
  exact summable_riemannXi_divisorZeroIndex₀_norm_inv_sq

example : analyticOrderNatAt Complex.riemannXi 0 = 0 := by
  exact analyticOrderNatAt_riemannXi_zero

example {z : ℂ}
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi
        (Set.univ : Set ℂ) =>
      1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  exact summable_riemannXi_logDerivTerms_divisorZeroIndex₀ hz

example {z : ℂ}
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    logDeriv (Complex.Hadamard.divisorCanonicalProduct 1 Complex.riemannXi
        (Set.univ : Set ℂ)) z =
      ∑' p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
        (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  exact logDeriv_riemannXi_divisorCanonicalProduct_one_eq_tsum hz

example {P : Polynomial ℂ} {z : ℂ}
    (hfac : ∀ w : ℂ, Complex.riemannXi w =
      Complex.exp (Polynomial.eval w P) *
        Complex.Hadamard.divisorCanonicalProduct 1 Complex.riemannXi (Set.univ : Set ℂ) w)
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    logDeriv Complex.riemannXi z =
      Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  exact logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac hz

example :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, Complex.riemannXi z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt Complex.riemannXi 0) *
      Complex.Hadamard.divisorCanonicalProduct 1 Complex.riemannXi (Set.univ : Set ℂ) z := by
  exact riemannXi_hadamard_factorization

example :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, Complex.riemannXi z =
        Complex.exp (Polynomial.eval z P) *
      Complex.Hadamard.divisorCanonicalProduct 1 Complex.riemannXi (Set.univ : Set ℂ) z := by
  exact riemannXi_hadamard_factorization_no_monomial

example {P Q : Polynomial ℂ}
    (hPfac : ∀ w : ℂ, Complex.riemannXi w =
      Complex.exp (Polynomial.eval w P) *
        Complex.Hadamard.divisorCanonicalProduct 1 Complex.riemannXi (Set.univ : Set ℂ) w)
    (hQfac : ∀ w : ℂ, Complex.riemannXi w = Complex.exp (Polynomial.eval w Q) *
      Complex.Hadamard.divisorCanonicalProduct 1 Complex.riemannXi (Set.univ : Set ℂ) w) :
    Polynomial.eval 0 P.derivative = Polynomial.eval 0 Q.derivative := by
  exact riemannXi_hadamard_polynomial_derivative_eval_zero_eq hPfac hQfac

example :
    ∃! B : ℂ, ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ (∀ z : ℂ, Complex.riemannXi z =
        Complex.exp (Polynomial.eval z P) *
          Complex.Hadamard.divisorCanonicalProduct 1 Complex.riemannXi (Set.univ : Set ℂ) z) ∧
      B = Polynomial.eval 0 P.derivative := by
  exact existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero

example {z : ℂ} (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi
      (Set.univ : Set ℂ), z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧
      logDeriv Complex.riemannXi z = Polynomial.eval z P.derivative +
          ∑' p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
            (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  exact exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum hz

example {z : ℂ} (hz : ∀ n : ℕ, z ≠ -n) :
    HasSum
      (fun n : ℕ =>
        1 / ((n : ℂ) + 1) -
        1 / ((n : ℂ) + z))
      (Complex.digamma z +
        Real.eulerMascheroniConstant) := by
  exact Complex.hasSum_digamma hz

example {z : ℂ} (hz : ∀ n : ℕ, z ≠ -n) :
    Complex.digamma z =
      -(Real.eulerMascheroniConstant : ℂ) +
        ∑' n : ℕ,
          (1 / ((n : ℂ) + 1) -
           1 / ((n : ℂ) + z)) := by
  exact Complex.digamma_eq_tsum hz

example (z : ℂ) :
    Kadiri.hadamardGenusOneFactor z = (1 - z) * Complex.exp z := by
  rfl

example (α w : ℂ) (hα : α ≠ 0) :
    Kadiri.hadamardGenusOneFactor (w / α) *
        Kadiri.hadamardGenusOneFactor (w / (-α)) =
      1 - w ^ 2 / α ^ 2 := by
  exact Kadiri.hadamardGenusOneFactor_pair_cancellation α w hα

example (ρ s : ℂ) :
    Kadiri.genusOneZeroLogTerm ρ s = 1 / ρ + 1 / (s - ρ) := by
  rfl

example {ι : Type*} (zero : ι → ℂ) (s : ℂ) :
    Kadiri.genusOneZeroLogSum zero s =
      ∑' i : ι, Kadiri.genusOneZeroLogTerm (zero i) s := by
  rfl

example (s : ℂ) :
    Kadiri.completedZetaFactor s =
      Kadiri.zetaPoleFactor s * Kadiri.zetaPiFactor s *
        Kadiri.zetaGammaFactor s * riemannZeta s := by
  rfl

example (s : ℂ)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : Kadiri.zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0) :
    logDeriv Kadiri.completedZetaFactor s =
      1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1)
      + deriv riemannZeta s / riemannZeta s := by
  exact Kadiri.logDeriv_completedZetaFactor s hs1 hΓdiff hΓ hζ

example (s : ℂ)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : Kadiri.zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s =
      -logDeriv Kadiri.completedZetaFactor s
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1) := by
  exact Kadiri.neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv s hs1 hΓdiff hΓ hζ

example (s B Z : ℂ)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : Kadiri.zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0)
    (hHad : logDeriv Kadiri.completedZetaFactor s = B + Z) :
    -deriv riemannZeta s / riemannZeta s =
      -B - Z
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1) := by
  exact Kadiri.neg_zeta_logDeriv_eq_of_completed_hadamard_logDeriv
    s B Z hs1 hΓdiff hΓ hζ hHad

example {ι : Type*} (zero : ι → ℂ) (s B : ℂ)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : Kadiri.zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0)
    (hHad : logDeriv Kadiri.completedZetaFactor s =
      B + Kadiri.genusOneZeroLogSum zero s) :
    -deriv riemannZeta s / riemannZeta s =
      -B - Kadiri.genusOneZeroLogSum zero s
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1) := by
  exact Kadiri.neg_zeta_logDeriv_eq_of_genusOne_hadamard
    zero s B hs1 hΓdiff hΓ hζ hHad
