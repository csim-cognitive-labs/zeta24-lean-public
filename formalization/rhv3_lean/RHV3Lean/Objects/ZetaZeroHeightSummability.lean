/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaZeroHeightTruncation

/-!
# P4.2: unconditional height-square summability for non-trivial zeta zeros

The Kadiri source route proves unweighted and order-weighted height-square tails from the
P4.1 crude Backlund majorant. This file transports the weighted statements to the local
canonical subtype and bridges `riemannZeta.order` to `zetaZeroMultiplicity`.
-/

open Set Filter Finset BigOperators Complex

namespace RHV3Lean

theorem riemannZeta_order_eq_zetaZeroMultiplicity
    {ρ : ℂ}
    (hρ : RHV3Lean.IsNontrivialZetaZero ρ) :
    riemannZeta.order ρ =
      (RHV3Lean.zetaZeroMultiplicity ρ : ℤ) := by
  have han : AnalyticAt ℂ riemannZeta ρ := analyticAt_riemannZeta_of_zero hρ.1
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ :=
    riemannZeta_analyticOrderAt_ne_top hρ.1
  have hcast := Nat.cast_analyticOrderNatAt hfin
  unfold riemannZeta.order zetaZeroMultiplicity
  rw [han.meromorphicOrderAt_eq, ← hcast]
  rfl

theorem weighted_zetaZeroMultiplicity_imagSquare_summable :
    Summable
      (fun ρ : {ρ : ℂ // RHV3Lean.IsNontrivialZetaZero ρ} =>
        (RHV3Lean.zetaZeroMultiplicity (ρ : ℂ) : ℝ) *
          |(ρ : ℂ).im|⁻¹ ^ (2 : ℕ)) := by
  let e := canonicalNontrivialZeroEquivKadiri
  have hsource := Kadiri.weighted_zeroImagSquareTail_summable
  have htransport := e.summable_iff.mpr hsource
  refine htransport.congr ?_
  intro ρ
  have horder := riemannZeta_order_eq_zetaZeroMultiplicity ρ.property
  simp [e, canonicalNontrivialZeroEquivKadiri, Kadiri.zeroImagSquareTail, horder]

theorem weighted_zetaZeroMultiplicity_shiftedImagSquare_summable
    (s : ℂ) :
    Summable
      (fun ρ : {ρ : ℂ // RHV3Lean.IsNontrivialZetaZero ρ} =>
        (RHV3Lean.zetaZeroMultiplicity (ρ : ℂ) : ℝ) *
          |(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ)) := by
  let e := canonicalNontrivialZeroEquivKadiri
  have hsource := Kadiri.weighted_zeroImagSquareTail_shifted_summable s
  have htransport := e.summable_iff.mpr hsource
  refine htransport.congr ?_
  intro ρ
  have horder := riemannZeta_order_eq_zetaZeroMultiplicity ρ.property
  simp [e, canonicalNontrivialZeroEquivKadiri, horder]

end RHV3Lean
