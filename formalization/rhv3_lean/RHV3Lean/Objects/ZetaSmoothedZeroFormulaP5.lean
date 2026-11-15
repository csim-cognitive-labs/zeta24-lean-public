/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.ZetaSmoothedExplicitFormulaP4_6

/-!
# P5.1 — zero-side smoothed formula as a distinct object
-/

open Complex BigOperators

noncomputable section

namespace RHV3Lean

/-- The spectral right-hand side of the proved P4.6 smoothed explicit formula.
This is intentionally not definitionally equal to `smoothedVonMangoldtSum`. -/
noncomputable def smoothedZeroFormula (x : ℝ) : ℂ :=
  (x : ℂ) / 2
    + (-logDeriv riemannZeta 0)
    + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹
    + (∑' n : ℕ, trivialZeroResidueTerm x n)
    + (∑' ρ : {ρ : ℂ // IsNontrivialZetaZero ρ},
        nontrivialZeroResidueTerm x ρ)

theorem smoothedZeroFormula_eq_smoothedVonMangoldtSum
    {x : ℝ}
    (hx : 1 < x) :
    smoothedZeroFormula x = smoothedVonMangoldtSum x := by
  simpa [smoothedZeroFormula] using (smoothed_riemann_explicit_formula (x := x) hx).symm

/-- The spectral background terms excluding the nontrivial-zero channel. -/
noncomputable def smoothedZeroBackground (x : ℝ) : ℂ :=
  (x : ℂ) / 2
    + (-logDeriv riemannZeta 0)
    + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹
    + (∑' n : ℕ, trivialZeroResidueTerm x n)

theorem smoothedZeroFormula_sub_background
    {x : ℝ}
    (_hx : 1 < x) :
    smoothedZeroFormula x - smoothedZeroBackground x
      =
    ∑' ρ : {ρ : ℂ // IsNontrivialZetaZero ρ},
      nontrivialZeroResidueTerm x ρ := by
  simp [smoothedZeroFormula, smoothedZeroBackground]

end RHV3Lean
