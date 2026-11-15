/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaRightVerticalTailsP4_5
import RHV3Lean.Objects.ZetaLeftVerticalPerronVanishingP4_4e
import RHV3Lean.Objects.ZetaTrivialZeroResidueSeriesP4_5
import RHV3Lean.Objects.ZetaNontrivialZeroResidueSeriesP4_5

/-!
# P4.5 closure
-/

open Complex Set Filter Finset BigOperators
open scoped Topology

noncomputable section

namespace RHV3Lean

theorem p4_5_boundary_and_zero_series_complete
    {x σR : ℝ}
    (hx : 1 < x)
    (hσR : 1 < σR) :
    (Tendsto
      (fun T : ℝ =>
        rightVerticalLowerTail'
          (zetaPerronIntegrand x)
          σR
          T)
      atTop
      (𝓝 0) ∧
    Tendsto
      (fun T : ℝ =>
        rightVerticalUpperTail'
          (zetaPerronIntegrand x)
          σR
          T)
      atTop
      (𝓝 0)) ∧
    Tendsto
      (fun N : ℕ =>
        VerticalIntegral'
          (zetaPerronIntegrand x)
          (perronRectangleSigmaL (N + 1)))
      atTop
      (𝓝 0) ∧
    Summable (fun n : ℕ => trivialZeroResidueTerm x n) ∧
    Summable
      (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
        nontrivialZeroResidueTerm x ρ) ∧
    Tendsto
      (fun T : ℝ =>
        ∑ ρ ∈ nontrivialZetaZerosByHeightFinset T,
          -(zetaZeroMultiplicity ρ : ℂ) *
            Perron.f x ρ)
      atTop
      (𝓝
        (∑' ρ : {ρ : ℂ // IsNontrivialZetaZero ρ},
          nontrivialZeroResidueTerm x ρ)) ∧
    (∀ {N : ℕ}, 1 ≤ N →
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
              (perronRectangleSigmaL N)))) := by
  refine ⟨right_vertical_tails_tendsto_zero hx hσR,
    P4_4e.left_vertical_boundary_tendsto_zero hx,
    trivial_zero_residue_series_summable hx,
    nontrivial_zero_residue_series_summable hx,
    nontrivial_zero_residue_series_symmetric_convergent hx,
    ?_⟩
  intro N hN
  exact P4_4e.exists_admissible_heights_all_left_boundary_limits hx hσR hN

end RHV3Lean
