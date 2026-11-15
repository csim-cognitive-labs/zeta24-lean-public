/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaPerronLineIdentity

/-!
# Tour 23-B — P3c2 : rectangle fini exact de Perron

Cette étape formalise uniquement l'identité finie sur un rectangle fixe pour
`-ζ'/ζ(s) * x^s/(s(s+1))`. Les quatre bords et les deux queues verticales droites
sont conservés exactement. Aucun passage à la limite de rectangle, aucune classification
des résidus et aucune annulation de bord n'interviennent ici.
-/

open Set Filter Complex ArithmeticFunction LSeries.notation MeasureTheory Real
open scoped Topology Interval

namespace RHV3Lean

/-- Intégrande de Perron-zêta utilisée par P3c1 et P3c2. -/
noncomputable def zetaPerronIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  -logDeriv riemannZeta s * Perron.f x s

/-- Frontière gauche du rectangle fini P3c2 : `-(2N+1)`. -/
def perronRectangleSigmaL (N : ℕ) : ℝ :=
  -((2 * (N : ℝ)) + 1)

/-- Coin inférieur gauche du rectangle P3c2. -/
noncomputable def perronRectangleLowerLeft (N : ℕ) (T : ℝ) : ℂ :=
  (perronRectangleSigmaL N : ℂ) - T * I

/-- Coin supérieur droit du rectangle P3c2. -/
noncomputable def perronRectangleUpperRight (σR T : ℝ) : ℂ :=
  (σR : ℂ) + T * I

/-- Ensemble exact des pôles intérieurs consommé par l'interface de résidus. -/
def zetaPerronRectanglePoleSet (x : ℝ) (σR : ℝ) (N : ℕ) (T : ℝ) : Set ℂ :=
  Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) ∩
    {s | meromorphicOrderAt (zetaPerronIntegrand x) s < 0}

/-- Admissibilité finie du rectangle : paramètres géométriques et absence de pôles sur le bord. -/
structure PerronRectangleAdmissible (x σR : ℝ) (N : ℕ) (T : ℝ) : Prop where
  x_gt : 1 < x
  sigmaR_gt : 1 < σR
  N_ge_one : 1 ≤ N
  T_pos : 0 < T
  no_poles_on_boundary :
    Disjoint
      (RectangleBorder (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T))
      {s | meromorphicOrderAt (zetaPerronIntegrand x) s < 0}

private lemma perronRectangleLowerLeft_re (N : ℕ) (T : ℝ) :
    (perronRectangleLowerLeft N T).re = perronRectangleSigmaL N := by
  simp [perronRectangleLowerLeft]

private lemma perronRectangleLowerLeft_im (N : ℕ) (T : ℝ) :
    (perronRectangleLowerLeft N T).im = -T := by
  simp [perronRectangleLowerLeft]

private lemma perronRectangleUpperRight_re (σR T : ℝ) :
    (perronRectangleUpperRight σR T).re = σR := by
  simp [perronRectangleUpperRight]

private lemma perronRectangleUpperRight_im (σR T : ℝ) :
    (perronRectangleUpperRight σR T).im = T := by
  simp [perronRectangleUpperRight]

private lemma perronRectangle_re_le {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    (perronRectangleLowerLeft N T).re ≤ (perronRectangleUpperRight σR T).re := by
  rw [perronRectangleLowerLeft_re, perronRectangleUpperRight_re, perronRectangleSigmaL]
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast h.N_ge_one
  nlinarith [h.sigmaR_gt]

private lemma perronRectangle_im_le {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    (perronRectangleLowerLeft N T).im ≤ (perronRectangleUpperRight σR T).im := by
  rw [perronRectangleLowerLeft_im, perronRectangleUpperRight_im]
  linarith [h.T_pos]

private lemma perronRectangle_isCompact (N : ℕ) (σR T : ℝ) :
    IsCompact (Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T)) := by
  rw [Rectangle]
  exact isCompact_uIcc.reProdIm isCompact_uIcc

/-- Méromorphie de l'intégrande P3c2 sur le rectangle admissible. -/
theorem zetaPerron_integrand_meromorphicOn {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    MeromorphicOn (zetaPerronIntegrand x)
      (Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T)) := by
  intro s _
  exact meromorphicAt_perronZetaIntegrand (x := x) (lt_trans zero_lt_one h.x_gt) s

/-- Les pôles requis par l'interface portée sont simples sur le rectangle. -/
theorem zetaPerron_integrand_hasSimplePolesOn {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    HasSimplePolesOn (zetaPerronIntegrand x)
      (Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T)) := by
  exact (hasSimplePolesOn_perronZetaIntegrand_univ (x := x) (lt_trans zero_lt_one h.x_gt)).mono
    (Set.subset_univ _)

private lemma zetaPerron_poleSet_subset_divisor_support {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    zetaPerronRectanglePoleSet x σR N T ⊆
      (MeromorphicOn.divisor (zetaPerronIntegrand x)
        (Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T))).support := by
  intro s hs
  have hmero := zetaPerron_integrand_meromorphicOn h
  have hsRect :
      s ∈ Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) :=
    hs.1
  have hsneg : meromorphicOrderAt (zetaPerronIntegrand x) s < 0 := hs.2
  rw [Function.mem_support, MeromorphicOn.divisor_apply hmero hsRect]
  intro hzero
  have hnonneg : 0 ≤ meromorphicOrderAt (zetaPerronIntegrand x) s := by
    simpa [hzero] using
      (WithTop.untop₀_nonneg (a := meromorphicOrderAt (zetaPerronIntegrand x) s))
  exact (not_le_of_gt hsneg) hnonneg

/-- Finitude de l'ensemble exact des pôles intérieurs du rectangle P3c2. -/
theorem zetaPerron_rectangle_poles_finite {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    (zetaPerronRectanglePoleSet x σR N T).Finite := by
  have hmero := zetaPerron_integrand_meromorphicOn h
  have hsupport :
      (MeromorphicOn.divisor (zetaPerronIntegrand x)
        (Rectangle (perronRectangleLowerLeft N T)
          (perronRectangleUpperRight σR T))).support.Finite :=
    hmero.divisor_support_finite_of_subset (perronRectangle_isCompact N σR T) (subset_rfl)
  exact hsupport.subset (zetaPerron_poleSet_subset_divisor_support h)

/-- Identité finie rectangle = somme des résidus intérieurs. -/
theorem zetaPerron_finite_rectangle_residue_identity {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    RectangleIntegral' (zetaPerronIntegrand x)
        (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T)
      =
    sumResiduesIn (zetaPerronIntegrand x) (zetaPerronRectanglePoleSet x σR N T) := by
  simpa [zetaPerronRectanglePoleSet] using
    RectangleIntegral'_eq_sumResiduesIn
      (z := perronRectangleLowerLeft N T)
      (w := perronRectangleUpperRight σR T)
      (f := zetaPerronIntegrand x)
      (perronRectangle_re_le h)
      (perronRectangle_im_le h)
      (zetaPerron_integrand_meromorphicOn h)
      h.no_poles_on_boundary
      (by simpa [zetaPerronRectanglePoleSet] using zetaPerron_rectangle_poles_finite h)
      (zetaPerron_integrand_hasSimplePolesOn h)

/-- Expansion exacte du rectangle fini en quatre bords orientés. -/
theorem zetaPerron_finite_rectangle_four_boundaries (F : ℂ → ℂ) (σR : ℝ) (N : ℕ) (T : ℝ) :
    RectangleIntegral' F (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T)
      =
    HIntegral' F (perronRectangleSigmaL N) σR (-T)
      - HIntegral' F (perronRectangleSigmaL N) σR T
      + VIntegral' F σR (-T) T
      - VIntegral' F (perronRectangleSigmaL N) (-T) T := by
  simp [RectangleIntegral', RectangleIntegral, HIntegral', VIntegral',
    perronRectangleLowerLeft_re, perronRectangleLowerLeft_im,
    perronRectangleUpperRight_re, perronRectangleUpperRight_im]
  ring

/-- Queue verticale droite inférieure, normalisée, sur `t <= -T`. -/
noncomputable def rightVerticalLowerTail' (F : ℂ → ℂ) (σR T : ℝ) : ℂ :=
  (1 / (2 * π * I)) • (I • ∫ t in Iic (-T), F (σR + t * I))

/-- Queue verticale droite supérieure, normalisée, sur `T <= t`. -/
noncomputable def rightVerticalUpperTail' (F : ℂ → ℂ) (σR T : ℝ) : ℂ :=
  (1 / (2 * π * I)) • (I • ∫ t in Ici T, F (σR + t * I))

/-- Décomposition exacte de la droite verticale complète en queue basse, segment et queue haute. -/
theorem verticalIntegral'_split_right_line (F : ℂ → ℂ) (σR T : ℝ)
    (hF : Integrable (fun t : ℝ ↦ F (σR + t * I))) :
    VerticalIntegral' F σR =
      rightVerticalLowerTail' F σR T + VIntegral' F σR (-T) T +
        rightVerticalUpperTail' F σR T := by
  unfold VerticalIntegral' rightVerticalLowerTail' rightVerticalUpperTail' VIntegral'
  rw [verticalIntegral_split_three (f := F) (σ := σR) (-T) T hF]
  module

/-- Intégrabilité verticale de l'intégrande P3c1/P3c2 sur toute droite `σ > 1`. -/
theorem integrable_zetaPerronIntegrand_vertical {x σR : ℝ} (x_gt : 1 < x)
    (hσR : 1 < σR) :
    Integrable (fun t : ℝ ↦ zetaPerronIntegrand x (σR + t * I)) := by
  have xpos : 0 < x := lt_trans zero_lt_one x_gt
  let C : ℝ := ∑' n : ℕ, ‖LSeries.term ↗Λ (σR : ℂ) n‖
  have hterms : ∀ n : ℕ,
      Integrable (fun t : ℝ ↦ (Λ n : ℂ) * Perron.f (x / n) (σR + t * I)) :=
    fun n ↦ integrable_vonMangoldt_perron_term xpos hσR n
  have hmeas_sum :
      AEStronglyMeasurable
        (fun t : ℝ ↦ ∑' n : ℕ, (Λ n : ℂ) * Perron.f (x / n) (σR + t * I)) :=
    (AEMeasurable.tsum fun n ↦ (hterms n).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ ↦ zetaPerronIntegrand x (σR + t * I)) := by
    refine hmeas_sum.congr (Eventually.of_forall fun t ↦ ?_)
    exact (neg_logDeriv_mul_perronKernel_eq_tsum (x := x) xpos (σ := σR) hσR t).symm
  have hlog_bound : ∀ t : ℝ, ‖-logDeriv riemannZeta (σR + t * I)‖ ≤ C := by
    intro t
    have hs_t : 1 < ((σR : ℂ) + t * I).re := by simp [hσR]
    have hsum_base : Summable fun n : ℕ ↦ ‖LSeries.term ↗Λ (σR : ℂ) n‖ :=
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp [hσR])).norm
    have hterm_norm : ∀ n : ℕ,
        ‖LSeries.term ↗Λ ((σR : ℂ) + t * I) n‖ =
          ‖LSeries.term ↗Λ (σR : ℂ) n‖ := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [LSeries.term]
      · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne',
          norm_div, norm_div, norm_natCast_cpow_of_pos hn, norm_natCast_cpow_of_pos hn]
        simp
    have hsum_t : Summable fun n : ℕ ↦ ‖LSeries.term ↗Λ ((σR : ℂ) + t * I) n‖ := by
      simpa [hterm_norm] using hsum_base
    calc
      ‖-logDeriv riemannZeta (σR + t * I)‖
          = ‖LSeries ↗Λ ((σR : ℂ) + t * I)‖ := by
              rw [negLogDeriv_riemannZeta_eq_LSeries_vonMangoldt hs_t]
      _ = ‖∑' n : ℕ, LSeries.term ↗Λ ((σR : ℂ) + t * I) n‖ := by rfl
      _ ≤ ∑' n : ℕ, ‖LSeries.term ↗Λ ((σR : ℂ) + t * I) n‖ :=
              norm_tsum_le_tsum_norm hsum_t
      _ = C := by simp [C, hterm_norm]
  have hbound : ∀ᵐ t : ℝ ∂volume,
      ‖zetaPerronIntegrand x (σR + t * I)‖ ≤
        (C * x ^ σR) * ‖Perron.f 1 ((σR : ℂ) + t * I)‖ := by
    refine Eventually.of_forall fun t ↦ ?_
    have hkernel :
        ‖Perron.f x ((σR : ℂ) + t * I)‖ =
          x ^ σR * ‖Perron.f 1 ((σR : ℂ) + t * I)‖ := by
      simpa using norm_perron_f_eq_rpow_mul (y := x) xpos ((σR : ℂ) + t * I)
    calc
      ‖zetaPerronIntegrand x (σR + t * I)‖
          = ‖-logDeriv riemannZeta ((σR : ℂ) + t * I)‖ *
              ‖Perron.f x ((σR : ℂ) + t * I)‖ := by
              simp [zetaPerronIntegrand]
      _ ≤ C * (x ^ σR * ‖Perron.f 1 ((σR : ℂ) + t * I)‖) := by
              rw [hkernel]
              exact mul_le_mul_of_nonneg_right (hlog_bound t)
                (mul_nonneg (Real.rpow_nonneg xpos.le σR) (norm_nonneg _))
      _ = (C * x ^ σR) * ‖Perron.f 1 ((σR : ℂ) + t * I)‖ := by ring
  have hbound_int :
      Integrable (fun t : ℝ ↦ (C * x ^ σR) * ‖Perron.f 1 ((σR : ℂ) + t * I)‖) :=
    (Perron.isIntegrable (x := 1) (σ := σR) (by norm_num) (by linarith)
      (by linarith)).norm.const_mul _
  exact Integrable.mono' hbound_int hmeas hbound

/-- Théorème terminal P3c2 : somme lissée = résidus finis + queues et bords conservés. -/
theorem smoothedVonMangoldtSum_eq_finite_residues_and_boundary_terms {x σR : ℝ} {N : ℕ}
    {T : ℝ} (h : PerronRectangleAdmissible x σR N T) :
    smoothedVonMangoldtSum x =
      sumResiduesIn (zetaPerronIntegrand x) (zetaPerronRectanglePoleSet x σR N T)
      + rightVerticalLowerTail' (zetaPerronIntegrand x) σR T
      + rightVerticalUpperTail' (zetaPerronIntegrand x) σR T
      - HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR (-T)
      + HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR T
      + VIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) (-T) T := by
  let F : ℂ → ℂ := zetaPerronIntegrand x
  have hP3c1 :
      VerticalIntegral' F σR = smoothedVonMangoldtSum x := by
    have hraw :=
      verticalIntegral'_eq_smoothedVonMangoldtSum (x := x) h.x_gt (σ := σR) h.sigmaR_gt
    have hfun : (fun s ↦ -logDeriv riemannZeta s * Perron.f x s) = F := by
      funext s
      simp [F, zetaPerronIntegrand, neg_mul]
    rw [hfun] at hraw
    exact hraw
  have hsplit :
      VerticalIntegral' F σR =
        rightVerticalLowerTail' F σR T + VIntegral' F σR (-T) T +
          rightVerticalUpperTail' F σR T :=
    verticalIntegral'_split_right_line F σR T
      (integrable_zetaPerronIntegrand_vertical (x := x) (σR := σR) h.x_gt h.sigmaR_gt)
  have hrect :
      RectangleIntegral' F (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T)
        =
      sumResiduesIn F (zetaPerronRectanglePoleSet x σR N T) := by
    simpa [F] using zetaPerron_finite_rectangle_residue_identity h
  have hfour :
      RectangleIntegral' F (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T)
        =
      HIntegral' F (perronRectangleSigmaL N) σR (-T)
        - HIntegral' F (perronRectangleSigmaL N) σR T
        + VIntegral' F σR (-T) T
        - VIntegral' F (perronRectangleSigmaL N) (-T) T :=
    zetaPerron_finite_rectangle_four_boundaries F σR N T
  have hVright :
      VIntegral' F σR (-T) T =
        sumResiduesIn F (zetaPerronRectanglePoleSet x σR N T)
          - HIntegral' F (perronRectangleSigmaL N) σR (-T)
          + HIntegral' F (perronRectangleSigmaL N) σR T
          + VIntegral' F (perronRectangleSigmaL N) (-T) T := by
    rw [hrect] at hfour
    calc
      VIntegral' F σR (-T) T
          =
        (HIntegral' F (perronRectangleSigmaL N) σR (-T)
          - HIntegral' F (perronRectangleSigmaL N) σR T
          + VIntegral' F σR (-T) T
          - VIntegral' F (perronRectangleSigmaL N) (-T) T)
          - HIntegral' F (perronRectangleSigmaL N) σR (-T)
          + HIntegral' F (perronRectangleSigmaL N) σR T
          + VIntegral' F (perronRectangleSigmaL N) (-T) T := by
            abel
      _ =
        sumResiduesIn F (zetaPerronRectanglePoleSet x σR N T)
          - HIntegral' F (perronRectangleSigmaL N) σR (-T)
          + HIntegral' F (perronRectangleSigmaL N) σR T
          + VIntegral' F (perronRectangleSigmaL N) (-T) T := by
            rw [← hfour]
  rw [← hP3c1, hsplit, hVright]
  abel

/-! ## Tests de contrat compilés -/

example {x σR : ℝ} {N : ℕ} {T : ℝ} (h : PerronRectangleAdmissible x σR N T) :
    MeromorphicOn (zetaPerronIntegrand x)
      (Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T)) :=
  zetaPerron_integrand_meromorphicOn h

example {x σR : ℝ} {N : ℕ} {T : ℝ} (h : PerronRectangleAdmissible x σR N T) :
    (zetaPerronRectanglePoleSet x σR N T).Finite :=
  zetaPerron_rectangle_poles_finite h

example {x σR : ℝ} {N : ℕ} {T : ℝ} (h : PerronRectangleAdmissible x σR N T) :
    RectangleIntegral' (zetaPerronIntegrand x)
        (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T)
      =
    sumResiduesIn (zetaPerronIntegrand x) (zetaPerronRectanglePoleSet x σR N T) :=
  zetaPerron_finite_rectangle_residue_identity h

example (F : ℂ → ℂ) (σR : ℝ) (N : ℕ) (T : ℝ) :
    RectangleIntegral' F (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T)
      =
    HIntegral' F (perronRectangleSigmaL N) σR (-T)
      - HIntegral' F (perronRectangleSigmaL N) σR T
      + VIntegral' F σR (-T) T
      - VIntegral' F (perronRectangleSigmaL N) (-T) T :=
  zetaPerron_finite_rectangle_four_boundaries F σR N T

example (F : ℂ → ℂ) (σR T : ℝ)
    (hF : Integrable (fun t : ℝ ↦ F (σR + t * I))) :
    VerticalIntegral' F σR =
      rightVerticalLowerTail' F σR T + VIntegral' F σR (-T) T +
        rightVerticalUpperTail' F σR T :=
  verticalIntegral'_split_right_line F σR T hF

example {x σR : ℝ} {N : ℕ} {T : ℝ} (h : PerronRectangleAdmissible x σR N T) :
    smoothedVonMangoldtSum x =
      sumResiduesIn (zetaPerronIntegrand x) (zetaPerronRectanglePoleSet x σR N T)
      + rightVerticalLowerTail' (zetaPerronIntegrand x) σR T
      + rightVerticalUpperTail' (zetaPerronIntegrand x) σR T
      - HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR (-T)
      + HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR T
      + VIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) (-T) T :=
  smoothedVonMangoldtSum_eq_finite_residues_and_boundary_terms h

#print axioms RHV3Lean.zetaPerron_integrand_meromorphicOn
#print axioms RHV3Lean.zetaPerron_rectangle_poles_finite
#print axioms RHV3Lean.zetaPerron_finite_rectangle_residue_identity
#print axioms RHV3Lean.zetaPerron_finite_rectangle_four_boundaries
#print axioms RHV3Lean.smoothedVonMangoldtSum_eq_finite_residues_and_boundary_terms

end RHV3Lean
