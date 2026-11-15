/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaConjugationOrbit

/-!
# Tour 23-B — itération P1 : dérivée logarithmique de ζ et résidus exacts

Cette étape livre la donnée d'entrée du chantier Perron (itération P1 du découpage P1–P5 ;
AUCUNE redémonstration d'un théorème Mathlib existant — les points 1 ci-dessous sont des
wrappers exacts, seuls les résidus à multiplicité générale et au pôle sont nouveaux) :

1. `−ζ'/ζ = L ↗Λ` sur `Re s > 1` (wrapper exact du théorème Mathlib
   `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, rien n'est redémontré) ;
2. le résidu logarithmique général : pour `f` analytique d'ordre fini `n` en `x`,
   `(w-x)·(f'/f)(w) → n` — Mathlib ne couvre que le cas simple (`n=1` via `deriv ≠ 0`),
   cette version vaut pour TOUTE multiplicité ;
3. l'application aux zéros de ζ : `(w-ρ)·(ζ'/ζ)(w) → m(ρ)` (multiplicité analytique
   exacte, réutilise l'itération 2) ;
4. le pôle : `(w-1)·(ζ'/ζ)(w) → −1`, via le prolongement analytique explicite
   `zetaPoleFactor` de `(s-1)ζ(s)` en `s=1`.

En convention `−ζ'/ζ` : résidu `−m(ρ)` en chaque zéro, `+1` au pôle — exactement les poids
de la future formule explicite. Rien ici ne prouve Perron, la formule explicite, ni RH.

Dossier mathématique préalable :
`validation/p4_autoresearch_prime/rh_resolution_progression/`
`stage38_round23b_iterationP1_math_dossier.md`.
-/

open Set Filter Complex ArithmeticFunction LSeries.notation
open scoped Topology

namespace RHV3Lean

/-! ## 1. `−ζ'/ζ` comme série de von Mangoldt sur `Re s > 1` -/

/-- Sommabilité de la série de von Mangoldt pour `Re s > 1` (wrapper Mathlib exact). -/
theorem LSeriesSummable_vonMangoldt_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ↗Λ s :=
  ArithmeticFunction.LSeriesSummable_vonMangoldt hs

/-- **Pont arithmétique–spectral d'entrée de Perron** : sur `Re s > 1`,
`−(ζ'/ζ)(s) = Σ Λ(n)/n^s`. Wrapper exact en langage `logDeriv` du théorème Mathlib
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`. -/
theorem negLogDeriv_riemannZeta_eq_LSeries_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    -logDeriv riemannZeta s = LSeries ↗Λ s := by
  rw [logDeriv_apply, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    neg_div]

/-! ## 2. Résidu logarithmique général = ordre analytique (toute multiplicité) -/

/-- La dérivée de la translation `z ↦ z - x` vaut `1`. -/
theorem deriv_sub_const_eq_one (x w : ℂ) : deriv (fun z : ℂ ↦ z - x) w = 1 := by
  have h : HasDerivAt (fun z : ℂ ↦ z - x) 1 w := (hasDerivAt_id w).sub_const x
  exact h.deriv

/-- `logDeriv` de la translation : `1/(w-x)`. -/
theorem logDeriv_sub_const (x w : ℂ) :
    logDeriv (fun z : ℂ ↦ z - x) w = 1 / (w - x) := by
  rw [logDeriv_apply, deriv_sub_const_eq_one]

/-- `logDeriv` du monôme centré : `n/(w-x)` (identité valable aussi en `w = x`, où les deux
membres valent `0` par convention Mathlib). -/
theorem logDeriv_centered_pow (x w : ℂ) (n : ℕ) :
    logDeriv (fun z : ℂ ↦ (z - x) ^ n) w = n / (w - x) := by
  have hdiff : DifferentiableAt ℂ (fun z : ℂ ↦ z - x) w :=
    (differentiable_id.sub_const x).differentiableAt
  rw [logDeriv_fun_pow hdiff, logDeriv_sub_const, mul_one_div]

/-- **Résidu logarithmique = ordre analytique, pour toute multiplicité.** Si `f` est
analytique en `x` avec ordre analytique fini, alors `(w-x)·(f'/f)(w)` tend vers l'ordre
naturel `analyticOrderNatAt f x` sur le voisinage épointé. Mathlib ne fournit que le cas
du zéro simple (`AnalyticAt.tendsto_mul_logDeriv_simple_zero`) ; cette version générale est
la brique requise pour compter les zéros de ζ avec multiplicité dans la formule explicite. -/
theorem tendsto_mul_logDeriv_analyticOrder {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hne : analyticOrderAt f x ≠ ⊤) :
    Tendsto (fun w ↦ (w - x) * logDeriv f w) (𝓝[≠] x)
      (𝓝 (analyticOrderNatAt f x)) := by
  classical
  obtain ⟨g, hg, hgx, hfg⟩ := (hf.analyticOrderAt_ne_top).mp hne
  set n : ℕ := analyticOrderNatAt f x with hn
  -- voisinage de travail : g ≠ 0, g analytique, et f = (·-x)^n·g localement autour de chaque
  -- point
  have hg_ne : ∀ᶠ w in 𝓝 x, g w ≠ 0 := hg.continuousAt.eventually_ne hgx
  have hg_ana : ∀ᶠ w in 𝓝 x, AnalyticAt ℂ g w := hg.eventually_analyticAt
  have hfg_nhds : ∀ᶠ w in 𝓝 x, f =ᶠ[𝓝 w] fun z ↦ (z - x) ^ n • g z :=
    hfg.eventually_nhds
  -- identité exacte sur le voisinage épointé
  have hkey : ∀ᶠ w in 𝓝[≠] x,
      (w - x) * logDeriv f w = n + (w - x) * logDeriv g w := by
    filter_upwards [nhdsWithin_le_nhds hg_ne, nhdsWithin_le_nhds hg_ana,
      nhdsWithin_le_nhds hfg_nhds, self_mem_nhdsWithin] with w hgw hganaw hfgw hwx
    have hwx' : w ≠ x := hwx
    have hsub : w - x ≠ 0 := sub_ne_zero.mpr hwx'
    have hpow : (w - x) ^ n ≠ 0 := pow_ne_zero n hsub
    -- logDeriv f w = logDeriv du produit en w
    have hld_eq : logDeriv f w = logDeriv (fun z ↦ (z - x) ^ n * g z) w := by
      have hderiv_eq : deriv f w = deriv (fun z ↦ (z - x) ^ n * g z) w := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [hfgw] with z hz
        simpa [smul_eq_mul] using hz
      have hval_eq : f w = (w - x) ^ n * g w := by
        simpa [smul_eq_mul] using hfgw.self_of_nhds
      rw [logDeriv_apply, logDeriv_apply, hderiv_eq, hval_eq]
    -- produit de deux facteurs non nuls et différentiables
    have hdpow : DifferentiableAt ℂ (fun z : ℂ ↦ (z - x) ^ n) w :=
      ((differentiable_id.sub_const x).differentiableAt).pow n
    have hdg : DifferentiableAt ℂ g w := hganaw.differentiableAt
    have hmul := logDeriv_mul (f := fun z : ℂ ↦ (z - x) ^ n) (g := g) w hpow hgw hdpow hdg
    rw [hld_eq, hmul, logDeriv_centered_pow x w n, mul_add]
    congr 1
    field_simp
  -- passage à la limite
  have hlim : Tendsto (fun w ↦ (n : ℂ) + (w - x) * logDeriv g w) (𝓝[≠] x)
      (𝓝 (n : ℂ)) := by
    have h0 : Tendsto (fun w : ℂ ↦ w - x) (𝓝 x) (𝓝 (x - x)) :=
      ((continuous_id.sub continuous_const).tendsto x)
    rw [sub_self] at h0
    have hgcont : ContinuousAt (logDeriv g) x := by
      have hderiv_cont : ContinuousAt (deriv g) x := hg.deriv.continuousAt
      exact hderiv_cont.div hg.continuousAt hgx
    have hprod : Tendsto (fun w ↦ (w - x) * logDeriv g w) (𝓝 x) (𝓝 0) := by
      simpa using h0.mul hgcont.tendsto
    have hconst : Tendsto (fun _ : ℂ ↦ (n : ℂ)) (𝓝[≠] x) (𝓝 (n : ℂ)) :=
      tendsto_const_nhds
    have := hconst.add (hprod.mono_left nhdsWithin_le_nhds)
    simpa using this
  exact hlim.congr' (hkey.mono fun w hw ↦ hw.symm)

/-! ## 3. Résidus exacts aux zéros de ζ : la multiplicité analytique -/

/-- **Résidu logarithmique de ζ en un zéro = multiplicité exacte.** Pour tout zéro `ρ` de ζ,
`(w-ρ)·(ζ'/ζ)(w) → m(ρ)`. Aucune hypothèse de simplicité ni de bande : l'ordre est fini en
tout zéro (itération 2). -/
theorem tendsto_mul_logDeriv_riemannZeta_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    Tendsto (fun w ↦ (w - ρ) * logDeriv riemannZeta w) (𝓝[≠] ρ)
      (𝓝 (zetaZeroMultiplicity ρ)) :=
  tendsto_mul_logDeriv_analyticOrder (analyticAt_riemannZeta_of_zero hρ)
    (riemannZeta_analyticOrderAt_ne_top hρ)

/-- Version `−ζ'/ζ` : résidu `−m(ρ)` en chaque zéro — le poids exact du terme `−x^ρ/ρ`
de la future formule explicite, compté avec multiplicité. -/
theorem tendsto_mul_neg_logDeriv_riemannZeta_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    Tendsto (fun w ↦ (w - ρ) * (-logDeriv riemannZeta w)) (𝓝[≠] ρ)
      (𝓝 (-(zetaZeroMultiplicity ρ : ℂ))) := by
  have h := (tendsto_mul_logDeriv_riemannZeta_zero hρ).neg
  simpa [mul_neg] using h

/-! ## 4. Pôle en `s = 1` : résidu `−1` pour `ζ'/ζ` -/

/-- Prolongement analytique explicite de `s ↦ (s-1)ζ(s)` au voisinage de `s = 1`,
construit sur la décomposition Mathlib `Λ = Λ₀ - 1/s - 1/(1-s)` et `ζ = Λ/Γℝ`. -/
noncomputable def zetaPoleFactor (s : ℂ) : ℂ :=
  ((s - 1) * completedRiemannZeta₀ s - (s - 1) / s + 1) * (Complex.Gammaℝ s)⁻¹

/-- Identité exacte : hors de `{0, 1}`, `ζ(w) = zetaPoleFactor w / (w - 1)`. -/
theorem riemannZeta_eq_zetaPoleFactor_div {w : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    riemannZeta w = zetaPoleFactor w / (w - 1) := by
  have hsub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have h1w : (1 : ℂ) - w ≠ 0 := by
    intro h
    exact hw1 (by linear_combination -h)
  have hnum : completedRiemannZeta₀ w - 1 / w - 1 / (1 - w)
      = ((w - 1) * completedRiemannZeta₀ w - (w - 1) / w + 1) / (w - 1) := by
    rw [eq_div_iff hsub]
    field_simp
    ring
  rw [riemannZeta_def_of_ne_zero hw0, completedRiemannZeta_eq]
  unfold zetaPoleFactor
  calc (completedRiemannZeta₀ w - 1 / w - 1 / (1 - w)) / Complex.Gammaℝ w
      = (((w - 1) * completedRiemannZeta₀ w - (w - 1) / w + 1) / (w - 1))
          / Complex.Gammaℝ w := by rw [hnum]
    _ = ((w - 1) * completedRiemannZeta₀ w - (w - 1) / w + 1)
          * (Complex.Gammaℝ w)⁻¹ / (w - 1) := by
        rw [div_div, mul_comm (w - 1) (Complex.Gammaℝ w), ← div_div,
          div_eq_mul_inv ((w - 1) * completedRiemannZeta₀ w - (w - 1) / w + 1)
            (Complex.Gammaℝ w)]

/-- `zetaPoleFactor` est analytique en `1`. -/
theorem zetaPoleFactor_analyticAt_one : AnalyticAt ℂ zetaPoleFactor 1 := by
  unfold zetaPoleFactor
  have h₁ : AnalyticAt ℂ (fun s : ℂ ↦ (s - 1) * completedRiemannZeta₀ s) 1 :=
    ((analyticAt_id.sub analyticAt_const)).mul
      (differentiable_completedZeta₀.analyticAt 1)
  have h₂ : AnalyticAt ℂ (fun s : ℂ ↦ (s - 1) / s) 1 := by
    apply AnalyticAt.div
    · exact analyticAt_id.sub analyticAt_const
    · exact analyticAt_id
    · norm_num
  have h₃ : AnalyticAt ℂ (fun s : ℂ ↦ (Complex.Gammaℝ s)⁻¹) 1 :=
    Complex.differentiable_Gammaℝ_inv.analyticAt 1
  exact ((h₁.sub h₂).add analyticAt_const).mul h₃

/-- `zetaPoleFactor 1 = Γℝ(1)⁻¹ ≠ 0` : seule la non-nullité est requise. -/
theorem zetaPoleFactor_one_ne_zero : zetaPoleFactor 1 ≠ 0 := by
  have h1 : Complex.Gammaℝ 1 ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  unfold zetaPoleFactor
  simpa using inv_ne_zero h1

/-- **Résidu du pôle : `(w-1)·(ζ'/ζ)(w) → −1`.** Le pôle simple de ζ en `1` devient un pôle
simple de `ζ'/ζ` de résidu exactement `−1`, soit résidu `+1` pour `−ζ'/ζ` — le terme
principal `x` de la future formule explicite. -/
theorem tendsto_mul_logDeriv_riemannZeta_pole :
    Tendsto (fun w ↦ (w - 1) * logDeriv riemannZeta w) (𝓝[≠] (1 : ℂ))
      (𝓝 (-1 : ℂ)) := by
  classical
  have hG_ana := zetaPoleFactor_analyticAt_one
  have hG1 := zetaPoleFactor_one_ne_zero
  have hG_ne : ∀ᶠ w in 𝓝 (1 : ℂ), zetaPoleFactor w ≠ 0 :=
    hG_ana.continuousAt.eventually_ne hG1
  have hG_anaw : ∀ᶠ w in 𝓝 (1 : ℂ), AnalyticAt ℂ zetaPoleFactor w :=
    hG_ana.eventually_analyticAt
  have h0_ne : ∀ᶠ w in 𝓝 (1 : ℂ), w ≠ 0 :=
    continuousAt_id.eventually_ne (by norm_num)
  -- identité exacte sur le voisinage épointé
  have hkey : ∀ᶠ w in 𝓝[≠] (1 : ℂ),
      (w - 1) * logDeriv riemannZeta w
        = (w - 1) * logDeriv zetaPoleFactor w - 1 := by
    filter_upwards [nhdsWithin_le_nhds hG_ne, nhdsWithin_le_nhds hG_anaw,
      nhdsWithin_le_nhds h0_ne, self_mem_nhdsWithin] with w hGw hGanaw hw0 hw1
    have hw1' : w ≠ 1 := hw1
    have hsub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1'
    -- ζ = G/(·-1) au voisinage ouvert de w (l'identité vaut sur l'ouvert {z ≠ 0, z ≠ 1})
    have hld_eq : logDeriv riemannZeta w
        = logDeriv (fun z ↦ zetaPoleFactor z / (z - 1)) w := by
      have hopen : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
        have : {z : ℂ | z ≠ 0 ∧ z ≠ 1} = {(0 : ℂ)}ᶜ ∩ {(1 : ℂ)}ᶜ := by
          ext z; simp
        rw [this]
        exact isOpen_compl_singleton.inter isOpen_compl_singleton
      have hmem : w ∈ {z : ℂ | z ≠ 0 ∧ z ≠ 1} := ⟨hw0, hw1'⟩
      have heq : riemannZeta =ᶠ[𝓝 w] fun z ↦ zetaPoleFactor z / (z - 1) := by
        filter_upwards [hopen.mem_nhds hmem] with z hz
        exact riemannZeta_eq_zetaPoleFactor_div hz.1 hz.2
      have hderiv_eq := heq.deriv_eq
      have hval_eq : riemannZeta w = zetaPoleFactor w / (w - 1) :=
        riemannZeta_eq_zetaPoleFactor_div hw0 hw1'
      rw [logDeriv_apply, logDeriv_apply, hderiv_eq, hval_eq]
    have hdG : DifferentiableAt ℂ zetaPoleFactor w := hGanaw.differentiableAt
    have hdsub : DifferentiableAt ℂ (fun z : ℂ ↦ z - 1) w :=
      (differentiable_id.sub_const 1).differentiableAt
    have hdiv := logDeriv_div (f := zetaPoleFactor) (g := fun z : ℂ ↦ z - 1) w
      hGw hsub hdG hdsub
    rw [hld_eq, hdiv, logDeriv_sub_const, mul_sub, mul_one_div, div_self hsub]
  -- passage à la limite
  have hlim : Tendsto (fun w ↦ (w - 1) * logDeriv zetaPoleFactor w - 1)
      (𝓝[≠] (1 : ℂ)) (𝓝 (-1 : ℂ)) := by
    have h0 : Tendsto (fun w : ℂ ↦ w - 1) (𝓝 (1 : ℂ)) (𝓝 ((1 : ℂ) - 1)) :=
      ((continuous_id.sub continuous_const).tendsto (1 : ℂ))
    rw [sub_self] at h0
    have hGcont : ContinuousAt (logDeriv zetaPoleFactor) 1 := by
      have hderiv_cont : ContinuousAt (deriv zetaPoleFactor) 1 :=
        hG_ana.deriv.continuousAt
      exact hderiv_cont.div hG_ana.continuousAt hG1
    have hprod : Tendsto (fun w ↦ (w - 1) * logDeriv zetaPoleFactor w)
        (𝓝 (1 : ℂ)) (𝓝 0) := by
      simpa using h0.mul hGcont.tendsto
    have hconst : Tendsto (fun _ : ℂ ↦ (1 : ℂ)) (𝓝[≠] (1 : ℂ)) (𝓝 (1 : ℂ)) :=
      tendsto_const_nhds
    have := (hprod.mono_left nhdsWithin_le_nhds).sub hconst
    simpa using this
  exact hlim.congr' (hkey.mono fun w hw ↦ hw.symm)

/-- Version `−ζ'/ζ` : résidu `+1` au pôle — le terme principal de la formule explicite. -/
theorem tendsto_mul_neg_logDeriv_riemannZeta_pole :
    Tendsto (fun w ↦ (w - 1) * (-logDeriv riemannZeta w)) (𝓝[≠] (1 : ℂ))
      (𝓝 (1 : ℂ)) := by
  have h := tendsto_mul_logDeriv_riemannZeta_pole.neg
  simpa [mul_neg] using h

end RHV3Lean

/-! ## Audit d'axiomes — Tour 23-B, itération P1 -/

#print axioms RHV3Lean.LSeriesSummable_vonMangoldt_of_one_lt_re
#print axioms RHV3Lean.negLogDeriv_riemannZeta_eq_LSeries_vonMangoldt
#print axioms RHV3Lean.deriv_sub_const_eq_one
#print axioms RHV3Lean.logDeriv_sub_const
#print axioms RHV3Lean.logDeriv_centered_pow
#print axioms RHV3Lean.tendsto_mul_logDeriv_analyticOrder
#print axioms RHV3Lean.tendsto_mul_logDeriv_riemannZeta_zero
#print axioms RHV3Lean.tendsto_mul_neg_logDeriv_riemannZeta_zero
#print axioms RHV3Lean.riemannZeta_eq_zetaPoleFactor_div
#print axioms RHV3Lean.zetaPoleFactor_analyticAt_one
#print axioms RHV3Lean.zetaPoleFactor_one_ne_zero
#print axioms RHV3Lean.tendsto_mul_logDeriv_riemannZeta_pole
#print axioms RHV3Lean.tendsto_mul_neg_logDeriv_riemannZeta_pole
