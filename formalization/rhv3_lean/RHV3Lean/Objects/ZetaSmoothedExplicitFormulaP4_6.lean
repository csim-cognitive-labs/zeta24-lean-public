/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaP4_5Closure

/-!
# P4.6 smoothed explicit formula
-/

open Complex Filter Finset BigOperators
open scoped Topology

noncomputable section

namespace RHV3Lean

theorem smoothedVonMangoldtSum_eq_height_truncated_residues_and_boundary_terms
    {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    smoothedVonMangoldtSum x =
      (x : ℂ) / 2
      + (-logDeriv riemannZeta 0)
      + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹
      + (∑ n ∈ Finset.range N, trivialZeroResidueTerm x n)
      + (∑ ρ ∈ nontrivialZetaZerosByHeightFinset T,
          -(zetaZeroMultiplicity ρ : ℂ) * Perron.f x ρ)
      + rightVerticalLowerTail' (zetaPerronIntegrand x) σR T
      + rightVerticalUpperTail' (zetaPerronIntegrand x) σR T
      - HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR (-T)
      + HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR T
      + VIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) (-T) T := by
  let trivialRaw : ℂ :=
    ∑' ρ : zetaPerronTrivialZeroSet σR N T,
      (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ)
  let nontrivialRaw : ℂ :=
    ∑' ρ : zetaPerronNontrivialZeroSet σR N T,
      (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ)
  let special : ℂ :=
    (x : ℂ) / 2
      + (-logDeriv riemannZeta 0)
      + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹
  have hclass :=
    smoothedVonMangoldtSum_eq_classified_residues_and_boundary_terms
      (x := x) (σR := σR) (N := N) (T := T) h
  have htriv :
      -trivialRaw
        =
      ∑ n ∈ Finset.range N, trivialZeroResidueTerm x n := by
    dsimp [trivialRaw]
    calc
      - (∑' ρ : zetaPerronTrivialZeroSet σR N T,
          (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ))
          =
        ∑' ρ : zetaPerronTrivialZeroSet σR N T,
          -((zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ)) := by
            exact (tsum_neg : (∑' ρ : zetaPerronTrivialZeroSet σR N T,
              -((zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ))) =
              - (∑' ρ : zetaPerronTrivialZeroSet σR N T,
                (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ))).symm
      _ =
        ∑' ρ : zetaPerronTrivialZeroSet σR N T,
          -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ) := by
            exact tsum_congr fun ρ => by ring
      _ = ∑ n ∈ Finset.range N, trivialZeroResidueTerm x n := by
            rw [← zetaPerron_trivial_zero_residue_sum h.x_gt]
            exact zetaPerron_trivial_zero_residue_sum_eq_range h
  have hnontriv :
      -nontrivialRaw
        =
      ∑ ρ ∈ nontrivialZetaZerosByHeightFinset T,
          -(zetaZeroMultiplicity ρ : ℂ) * Perron.f x ρ := by
    dsimp [nontrivialRaw]
    calc
      - (∑' ρ : zetaPerronNontrivialZeroSet σR N T,
          (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ))
          =
        ∑' ρ : zetaPerronNontrivialZeroSet σR N T,
          -((zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ)) := by
            exact (tsum_neg : (∑' ρ : zetaPerronNontrivialZeroSet σR N T,
              -((zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ))) =
              - (∑' ρ : zetaPerronNontrivialZeroSet σR N T,
                (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ))).symm
      _ =
        ∑' ρ : zetaPerronNontrivialZeroSet σR N T,
          -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ) := by
            exact tsum_congr fun ρ => by ring
      _ =
        ∑ ρ ∈ nontrivialZetaZerosByHeightFinset T,
          -(zetaZeroMultiplicity ρ : ℂ) * Perron.f x ρ := by
            rw [← zetaPerron_nontrivial_zero_residue_sum h.x_gt]
            exact zetaPerron_nontrivial_zero_residue_sum_eq_byHeight h
  have hclass' :
      smoothedVonMangoldtSum x =
        special
        + (-trivialRaw)
        + (-nontrivialRaw)
        + rightVerticalLowerTail' (zetaPerronIntegrand x) σR T
        + rightVerticalUpperTail' (zetaPerronIntegrand x) σR T
        - HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR (-T)
        + HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR T
        + VIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) (-T) T := by
    simpa [special, trivialRaw, nontrivialRaw, sub_eq_add_neg, add_assoc] using hclass
  rw [hclass', htriv, hnontriv]

theorem exists_admissible_heights_all_boundary_limits_with_tendsto
    {x σR : ℝ} (hx : 1 < x) (hσR : 1 < σR)
    {N : ℕ} (hN : 1 ≤ N) :
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
  refine ⟨T, hTadm, hTtop, hTplus, hTminus, ?_⟩
  exact P4_4e.left_vertical_truncated_tendsto_full
    (x := x) hx (N := N) hN hTtop

theorem smoothedVonMangoldtSum_eq_fixed_left_boundary_limit
    {x σR : ℝ}
    (hx : 1 < x)
    (hσR : 1 < σR)
    {N : ℕ}
    (hN : 1 ≤ N) :
    smoothedVonMangoldtSum x
      =
    (x : ℂ) / 2
      + (-logDeriv riemannZeta 0)
      + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹
      + (∑ n ∈ Finset.range N,
          trivialZeroResidueTerm x n)
      + (∑' ρ : {ρ : ℂ // IsNontrivialZetaZero ρ},
          nontrivialZeroResidueTerm x ρ)
      + VerticalIntegral'
          (zetaPerronIntegrand x)
          (perronRectangleSigmaL N) := by
  obtain ⟨T, hTadm, hTtop, hHplus, hHminus, hVleft⟩ :=
    exists_admissible_heights_all_boundary_limits_with_tendsto
      (x := x) (σR := σR) (N := N) hx hσR hN
  let special : ℂ :=
    (x : ℂ) / 2
      + (-logDeriv riemannZeta 0)
      + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹
  let trivialN : ℂ :=
    ∑ n ∈ Finset.range N, trivialZeroResidueTerm x n
  let nontrivialSum : ℂ :=
    ∑' ρ : {ρ : ℂ // IsNontrivialZetaZero ρ},
      nontrivialZeroResidueTerm x ρ
  let leftFull : ℂ :=
    VerticalIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N)
  let rhsSeq : ℕ → ℂ := fun n =>
    special + trivialN
      + (∑ ρ ∈ nontrivialZetaZerosByHeightFinset (T n),
          -(zetaZeroMultiplicity ρ : ℂ) * Perron.f x ρ)
      + rightVerticalLowerTail' (zetaPerronIntegrand x) σR (T n)
      + rightVerticalUpperTail' (zetaPerronIntegrand x) σR (T n)
      - HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR (-(T n))
      + HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR (T n)
      + VIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) (-(T n)) (T n)
  have hrvt := right_vertical_tails_tendsto_zero hx hσR
  have hnontriv :=
    (nontrivial_zero_residue_series_symmetric_convergent (x := x) hx).comp hTtop
  have hlower := hrvt.1.comp hTtop
  have hupper := hrvt.2.comp hTtop
  have hlim :
      Tendsto rhsSeq atTop (𝓝 (special + trivialN + nontrivialSum + leftFull)) := by
    have hconstST :
        Tendsto (fun _ : ℕ => special + trivialN) atTop
          (𝓝 (special + trivialN)) :=
      tendsto_const_nhds
    have hmain :
        Tendsto rhsSeq atTop
          (𝓝 (((((((special + trivialN) + nontrivialSum) + 0) + 0) + 0) + 0) + leftFull)) := by
      simpa [rhsSeq, nontrivialSum, leftFull, VerticalIntegral', sub_eq_add_neg, add_assoc,
        add_comm, add_left_comm] using
        ((((((hconstST.add hnontriv).add hlower).add hupper).add hHminus.neg).add
          hHplus).add hVleft)
    simpa [add_assoc, add_comm, add_left_comm] using hmain
  have hseq_eq : rhsSeq = fun _ : ℕ => smoothedVonMangoldtSum x := by
    funext n
    have hformula :=
      smoothedVonMangoldtSum_eq_height_truncated_residues_and_boundary_terms (hTadm n).2.2
    simpa [rhsSeq, special, trivialN, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      using hformula.symm
  have hconst :
      Tendsto (fun _ : ℕ => smoothedVonMangoldtSum x) atTop
        (𝓝 (special + trivialN + nontrivialSum + leftFull)) := by
    simpa [hseq_eq] using hlim
  have huniq :=
    tendsto_nhds_unique (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      smoothedVonMangoldtSum x) atTop (𝓝 (smoothedVonMangoldtSum x))) hconst
  simpa [special, trivialN, nontrivialSum, leftFull, add_assoc] using huniq

theorem smoothed_riemann_explicit_formula
    {x : ℝ}
    (hx : 1 < x) :
    smoothedVonMangoldtSum x
      =
    (x : ℂ) / 2
      + (-logDeriv riemannZeta 0)
      + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹
      + (∑' n : ℕ,
          trivialZeroResidueTerm x n)
      + (∑' ρ : {ρ : ℂ // IsNontrivialZetaZero ρ},
          nontrivialZeroResidueTerm x ρ) := by
  let special : ℂ :=
    (x : ℂ) / 2
      + (-logDeriv riemannZeta 0)
      + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹
  let trivialSum : ℂ :=
    ∑' n : ℕ, trivialZeroResidueTerm x n
  let nontrivialSum : ℂ :=
    ∑' ρ : {ρ : ℂ // IsNontrivialZetaZero ρ},
      nontrivialZeroResidueTerm x ρ
  let rhsSeq : ℕ → ℂ := fun N =>
    special
      + (∑ n ∈ Finset.range (N + 1), trivialZeroResidueTerm x n)
      + nontrivialSum
      + VerticalIntegral'
          (zetaPerronIntegrand x)
          (perronRectangleSigmaL (N + 1))
  have htriv :
      Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range (N + 1), trivialZeroResidueTerm x n)
        atTop
        (𝓝 trivialSum) := by
    change Tendsto
      ((fun M : ℕ =>
        ∑ n ∈ Finset.range M, trivialZeroResidueTerm x n) ∘
        fun N : ℕ => N + 1)
      atTop
      (𝓝 trivialSum)
    simpa [trivialSum] using
      (trivial_zero_residue_partial_sums_tendsto (x := x) hx).comp
        (tendsto_add_atTop_nat 1)
  have hleft := P4_4e.left_vertical_boundary_tendsto_zero (x := x) hx
  have hlim :
      Tendsto rhsSeq atTop (𝓝 (special + trivialSum + nontrivialSum)) := by
    have hmain :
        Tendsto rhsSeq atTop (𝓝 (((special + trivialSum) + nontrivialSum) + 0)) := by
      simpa [rhsSeq, nontrivialSum, sub_eq_add_neg, add_assoc] using
        (((tendsto_const_nhds.add htriv).add tendsto_const_nhds).add hleft)
    simpa [add_assoc] using hmain
  have hseq_eq : rhsSeq = fun _ : ℕ => smoothedVonMangoldtSum x := by
    funext N
    have hfixed :=
      smoothedVonMangoldtSum_eq_fixed_left_boundary_limit
        (x := x) (σR := 2) (N := N + 1) hx (by norm_num)
        (by omega)
    simpa [rhsSeq, special, nontrivialSum, add_assoc, add_comm, add_left_comm]
      using hfixed.symm
  have hconst :
      Tendsto (fun _ : ℕ => smoothedVonMangoldtSum x) atTop
        (𝓝 (special + trivialSum + nontrivialSum)) := by
    simpa [hseq_eq] using hlim
  have huniq :=
    tendsto_nhds_unique (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      smoothedVonMangoldtSum x) atTop (𝓝 (smoothedVonMangoldtSum x))) hconst
  simpa [special, trivialSum, nontrivialSum, add_assoc] using huniq

end RHV3Lean
