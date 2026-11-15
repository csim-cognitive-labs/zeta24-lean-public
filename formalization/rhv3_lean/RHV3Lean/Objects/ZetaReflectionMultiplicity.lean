/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaHeightReflection

/-!
# Tour 23-B — itération 3B1 : multiplicité sous réflexion fonctionnelle

Cette étape prouve que la réflexion `ρ ↦ 1 - ρ` conserve exactement
l'ordre analytique, donc la multiplicité naturelle, de tout zéro situé dans
la bande ouverte. Elle ne traite pas encore la conjugaison et ne revendique
ni Perron, ni formule explicite, ni RH.

Dossier mathématique préalable :
`validation/p4_autoresearch_prime/rh_resolution_progression/`
`stage35_round23b_iteration3b1_math_dossier.md`.
-/

open Set Filter
open scoped Topology

namespace RHV3Lean

/-- Dans le demi-plan `Re s > 0`, ζ est localement le produit de la zêta
complétée et du facteur entier `Γℝ⁻¹`. -/
theorem riemannZeta_eventuallyEq_completed_mul_GammaR_inv {s : ℂ}
    (hs : 0 < s.re) :
    riemannZeta =ᶠ[𝓝 s]
      (fun z ↦ completedRiemannZeta z * (Complex.Gammaℝ z)⁻¹) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hmem : {z : ℂ | 0 < z.re} ∈ 𝓝 s := hopen.mem_nhds hs
  filter_upwards [hmem] with z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
  rw [riemannZeta_def_of_ne_zero hz0, div_eq_mul_inv]

/-- Le facteur `Γℝ⁻¹` a ordre analytique nul dans `Re s > 0`. -/
theorem analyticOrderAt_GammaR_inv_eq_zero_of_re_pos {s : ℂ}
    (hs : 0 < s.re) :
    analyticOrderAt (fun z ↦ (Complex.Gammaℝ z)⁻¹) s = 0 := by
  have hana : AnalyticAt ℂ (fun z ↦ (Complex.Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.analyticAt s
  exact hana.analyticOrderAt_eq_zero.mpr
    (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hs))

/-- Dans le demi-plan droit, hors du pôle, ζ et sa complétée ont exactement
le même ordre analytique. -/
theorem analyticOrderAt_riemannZeta_eq_completed_of_re_pos {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt riemannZeta s =
      analyticOrderAt completedRiemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    simp at hs
  have hbase : AnalyticAt ℂ completedRiemannZeta₀ s :=
    differentiable_completedZeta₀.analyticAt s
  have hid : AnalyticAt ℂ (fun z : ℂ ↦ z) s := analyticAt_id
  have hone : AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ)) s := analyticAt_const
  have hinv_z : AnalyticAt ℂ (fun z : ℂ ↦ z⁻¹) s :=
    hid.inv hs0
  have hsub :
      AnalyticAt ℂ ((fun _ : ℂ ↦ (1 : ℂ)) - fun z : ℂ ↦ z) s :=
    hone.sub hid
  have hsub_ne :
      (((fun _ : ℂ ↦ (1 : ℂ)) - fun z : ℂ ↦ z) s) ≠ 0 := by
    simpa only [Pi.sub_apply] using
      (sub_ne_zero.mpr (Ne.symm hs1) : (1 - s : ℂ) ≠ 0)
  have hinv_sub :
      AnalyticAt ℂ (((fun _ : ℂ ↦ (1 : ℂ)) - fun z : ℂ ↦ z)⁻¹) s :=
    hsub.inv hsub_ne
  have hformula :
      AnalyticAt ℂ
        ((completedRiemannZeta₀ - fun z : ℂ ↦ z⁻¹) -
          (((fun _ : ℂ ↦ (1 : ℂ)) - fun z : ℂ ↦ z)⁻¹)) s :=
    (hbase.sub hinv_z).sub hinv_sub
  have hcomp : AnalyticAt ℂ completedRiemannZeta s := by
    apply AnalyticAt.congr hformula
    apply Filter.Eventually.of_forall
    intro z
    simp only [Pi.sub_apply, Pi.inv_apply]
    simpa only [div_eq_mul_inv, one_mul] using
      (completedRiemannZeta_eq z).symm
  have hinv : AnalyticAt ℂ (fun z ↦ (Complex.Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.analyticAt s
  rw [analyticOrderAt_congr
    (riemannZeta_eventuallyEq_completed_mul_GammaR_inv hs)]
  change analyticOrderAt
      (completedRiemannZeta * fun z ↦ (Complex.Gammaℝ z)⁻¹) s = _
  rw [analyticOrderAt_mul hcomp hinv,
    analyticOrderAt_GammaR_inv_eq_zero_of_re_pos hs, add_zero]

/-- La réflexion affine a une dérivée non nulle. -/
theorem zetaReflect_deriv_ne_zero (s : ℂ) : deriv zetaReflect s ≠ 0 := by
  change deriv (fun z : ℂ ↦ 1 - z) s ≠ 0
  have hderiv : HasDerivAt (fun z : ℂ ↦ 1 - z) (-1) s :=
    (hasDerivAt_id s).const_sub 1
  rw [hderiv.deriv]
  norm_num

/-- L'équation fonctionnelle de la zêta complétée conserve exactement
l'ordre analytique sous `s ↦ 1 - s`. -/
theorem analyticOrderAt_completedZeta_zetaReflect (s : ℂ) :
    analyticOrderAt completedRiemannZeta (zetaReflect s) =
      analyticOrderAt completedRiemannZeta s := by
  have hreflect : AnalyticAt ℂ zetaReflect s := by
    unfold zetaReflect
    fun_prop
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := completedRiemannZeta) hreflect (zetaReflect_deriv_ne_zero s)
  have heq :
      (completedRiemannZeta ∘ zetaReflect) =ᶠ[𝓝 s]
        completedRiemannZeta := by
    apply Filter.Eventually.of_forall
    intro z
    exact completedRiemannZeta_one_sub z
  exact hcomp.symm.trans (analyticOrderAt_congr heq)

/-- Tout zéro de la bande ouverte conserve exactement sa multiplicité
analytique naturelle sous la réflexion fonctionnelle. -/
theorem zetaZeroMultiplicity_zetaReflect {ρ : ℂ}
    (hzero : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) :
    zetaZeroMultiplicity (zetaReflect ρ) = zetaZeroMultiplicity ρ := by
  have hreflect_zero : riemannZeta (zetaReflect ρ) = 0 :=
    riemannZeta_zetaReflect_eq_zero hzero hre0
  have hreflect_re : 0 < (zetaReflect ρ).re := by
    simp [zetaReflect]
    linarith
  have hρ1 : ρ ≠ 1 := zetaZero_ne_one hzero
  have hreflect1 : zetaReflect ρ ≠ 1 := zetaZero_ne_one hreflect_zero
  have hord_reflect :=
    analyticOrderAt_riemannZeta_eq_completed_of_re_pos hreflect_re hreflect1
  have hord_original :=
    analyticOrderAt_riemannZeta_eq_completed_of_re_pos hre0 hρ1
  have hcompleted := analyticOrderAt_completedZeta_zetaReflect ρ
  unfold zetaZeroMultiplicity analyticOrderNatAt
  rw [hord_reflect, hcompleted, ← hord_original]

end RHV3Lean

/-! ## Audit d'axiomes — Tour 23-B, itération 3B1 -/

#print axioms RHV3Lean.riemannZeta_eventuallyEq_completed_mul_GammaR_inv
#print axioms RHV3Lean.analyticOrderAt_GammaR_inv_eq_zero_of_re_pos
#print axioms RHV3Lean.analyticOrderAt_riemannZeta_eq_completed_of_re_pos
#print axioms RHV3Lean.zetaReflect_deriv_ne_zero
#print axioms RHV3Lean.analyticOrderAt_completedZeta_zetaReflect
#print axioms RHV3Lean.zetaZeroMultiplicity_zetaReflect
