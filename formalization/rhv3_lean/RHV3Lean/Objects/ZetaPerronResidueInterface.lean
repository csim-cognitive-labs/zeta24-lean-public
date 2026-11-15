/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaLogDerivVonMangoldt
import RHV3Lean.Objects.PerronPort.PerronFormula
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Tour 23-B — itération P3a : interface résidus / pôles simples pour la formule explicite

Obligations d'interface du réviseur externe (entrée de P3), dérivées de la factorisation
locale de P1 :

1. **(O1)** décompositions partie principale + reste borné, dans la forme exacte exigée par
   `ResidueTheoremOnRectangleWithSimplePole'` du port P2 :
   `(−ζ'/ζ) − (−m(ρ))/(·−ρ) = O(1)` sur `𝓝[≠] ρ`, et `(−ζ'/ζ) − 1/(·−1) = O(1)` sur `𝓝[≠] 1` ;
2. **(O2)** méromorphie globale et pôles AU PLUS SIMPLES (`HasSimplePolesOn` du port, i.e.
   `−1 ≤ meromorphicOrderAt`) pour `−ζ'/ζ` et pour l'intégrande complet
   `−(ζ'/ζ)(s)·x^s/(s(s+1))`, sur tout ℂ — le zéro de multiplicité `m` donne un pôle SIMPLE
   de résidu `−m` (théorème, pas hypothèse) ;
3. **(O3)** valeurs de `residue` (au sens du port) alimentées par les limites P1.

Rien ici ne déplace un contour ni ne somme sur les zéros (P3/P4), et aucune nouvelle porte
n'est créée. Aucune hypothèse RH, aucune hypothèse de zéros simples.

Dossier mathématique préalable :
`validation/p4_autoresearch_prime/rh_resolution_progression/`
`stage40_round23b_iterationP3a_math_dossier.md`.
-/

open Set Filter Complex Asymptotics
open scoped Topology

namespace RHV3Lean

/-! ## 1. Identité locale commune (extraite de P1, non multipliée) -/

/-- Pour `f` analytique d'ordre fini en `x`, la dérivée logarithmique se décompose sur le
voisinage épointé en partie principale exacte plus dérivée logarithmique du cofacteur :
`f'/f = n/(·−x) + g'/g`, avec `g` analytique et non nulle en `x`. -/
theorem exists_logDeriv_eventuallyEq_principal_add {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hne : analyticOrderAt f x ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ g x ≠ 0 ∧
      ∀ᶠ w in 𝓝[≠] x, logDeriv f w
        = (analyticOrderNatAt f x : ℂ) / (w - x) + logDeriv g w := by
  classical
  obtain ⟨g, hg, hgx, hfg⟩ := (hf.analyticOrderAt_ne_top).mp hne
  set n : ℕ := analyticOrderNatAt f x with hn
  refine ⟨g, hg, hgx, ?_⟩
  have hg_ne : ∀ᶠ w in 𝓝 x, g w ≠ 0 := hg.continuousAt.eventually_ne hgx
  have hg_ana : ∀ᶠ w in 𝓝 x, AnalyticAt ℂ g w := hg.eventually_analyticAt
  have hfg_nhds : ∀ᶠ w in 𝓝 x, f =ᶠ[𝓝 w] fun z ↦ (z - x) ^ n • g z :=
    hfg.eventually_nhds
  filter_upwards [nhdsWithin_le_nhds hg_ne, nhdsWithin_le_nhds hg_ana,
    nhdsWithin_le_nhds hfg_nhds, self_mem_nhdsWithin] with w hgw hganaw hfgw hwx
  have hwx' : w ≠ x := hwx
  have hsub : w - x ≠ 0 := sub_ne_zero.mpr hwx'
  have hpow : (w - x) ^ n ≠ 0 := pow_ne_zero n hsub
  have hld_eq : logDeriv f w = logDeriv (fun z ↦ (z - x) ^ n * g z) w := by
    have hderiv_eq : deriv f w = deriv (fun z ↦ (z - x) ^ n * g z) w := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hfgw] with z hz
      simpa [smul_eq_mul] using hz
    have hval_eq : f w = (w - x) ^ n * g w := by
      simpa [smul_eq_mul] using hfgw.self_of_nhds
    rw [logDeriv_apply, logDeriv_apply, hderiv_eq, hval_eq]
  have hdpow : DifferentiableAt ℂ (fun z : ℂ ↦ (z - x) ^ n) w :=
    ((differentiable_id.sub_const x).differentiableAt).pow n
  have hdg : DifferentiableAt ℂ g w := hganaw.differentiableAt
  have hmul := logDeriv_mul (f := fun z : ℂ ↦ (z - x) ^ n) (g := g) w hpow hgw hdpow hdg
  rw [hld_eq, hmul, logDeriv_centered_pow x w n]

/-- **(O1), forme générale.** Pour `f` analytique d'ordre fini en `x`, la dérivée
logarithmique moins sa partie principale est bornée : `f'/f − n/(·−x) = O(1)` sur `𝓝[≠] x`. -/
theorem logDeriv_sub_principal_isBigO {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hne : analyticOrderAt f x ≠ ⊤) :
    ((logDeriv f) - fun w ↦ (analyticOrderNatAt f x : ℂ) / (w - x))
      =O[𝓝[≠] x] (1 : ℂ → ℂ) := by
  obtain ⟨g, hg, hgx, hev⟩ := exists_logDeriv_eventuallyEq_principal_add hf hne
  have hcont : ContinuousAt (logDeriv g) x :=
    (hg.deriv.continuousAt).div hg.continuousAt hgx
  have hO : (logDeriv g) =O[𝓝[≠] x] (1 : ℂ → ℂ) :=
    (hcont.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  have heq : ((logDeriv f) - fun w ↦ (analyticOrderNatAt f x : ℂ) / (w - x))
      =ᶠ[𝓝[≠] x] logDeriv g := by
    filter_upwards [hev] with w hw
    simp [hw]
  exact heq.trans_isBigO hO

/-! ## 2. (O1) pour −ζ'/ζ -/

/-- **(O1) au zéro** : `(−ζ'/ζ) − (−m(ρ))/(·−ρ) = O(1)` sur `𝓝[≠] ρ`, pour TOUT zéro de ζ,
toute multiplicité. Forme d'entrée exacte de `ResidueTheoremOnRectangleWithSimplePole'`. -/
theorem neg_logDeriv_riemannZeta_sub_principal_zero_isBigO {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) :
    ((fun s ↦ -logDeriv riemannZeta s)
      - fun s ↦ (-(zetaZeroMultiplicity ρ : ℂ)) / (s - ρ))
      =O[𝓝[≠] ρ] (1 : ℂ → ℂ) := by
  have h := (logDeriv_sub_principal_isBigO
    (analyticAt_riemannZeta_of_zero hρ) (riemannZeta_analyticOrderAt_ne_top hρ)).neg_left
  have heq : ((fun s ↦ -logDeriv riemannZeta s)
        - fun s ↦ (-(zetaZeroMultiplicity ρ : ℂ)) / (s - ρ))
      =ᶠ[𝓝[≠] ρ]
      fun s ↦ -(((logDeriv riemannZeta)
        - fun w ↦ (analyticOrderNatAt riemannZeta ρ : ℂ) / (w - ρ)) s) := by
    apply Filter.Eventually.of_forall
    intro s
    have hcast : (zetaZeroMultiplicity ρ : ℂ) = (analyticOrderNatAt riemannZeta ρ : ℂ) := rfl
    simp only [Pi.sub_apply, hcast, neg_div]
    ring
  exact heq.trans_isBigO h

/-- Identité éventuelle au pôle (P1, non multipliée) :
`logDeriv ζ = logDeriv G − 1/(·−1)` sur `𝓝[≠] 1`, où `G = zetaPoleFactor`. -/
theorem logDeriv_riemannZeta_eventuallyEq_pole :
    ∀ᶠ w in 𝓝[≠] (1 : ℂ),
      logDeriv riemannZeta w = logDeriv zetaPoleFactor w - 1 / (w - 1) := by
  classical
  have hG_ne : ∀ᶠ w in 𝓝 (1 : ℂ), zetaPoleFactor w ≠ 0 :=
    zetaPoleFactor_analyticAt_one.continuousAt.eventually_ne zetaPoleFactor_one_ne_zero
  have hG_anaw : ∀ᶠ w in 𝓝 (1 : ℂ), AnalyticAt ℂ zetaPoleFactor w :=
    zetaPoleFactor_analyticAt_one.eventually_analyticAt
  have h0_ne : ∀ᶠ w in 𝓝 (1 : ℂ), w ≠ 0 :=
    continuousAt_id.eventually_ne (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hG_ne, nhdsWithin_le_nhds hG_anaw,
    nhdsWithin_le_nhds h0_ne, self_mem_nhdsWithin] with w hGw hGanaw hw0 hw1
  have hw1' : w ≠ 1 := hw1
  have hsub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1'
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
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq,
      riemannZeta_eq_zetaPoleFactor_div hw0 hw1']
  have hdG : DifferentiableAt ℂ zetaPoleFactor w := hGanaw.differentiableAt
  have hdsub : DifferentiableAt ℂ (fun z : ℂ ↦ z - 1) w :=
    (differentiable_id.sub_const 1).differentiableAt
  rw [hld_eq, logDeriv_div (f := zetaPoleFactor) (g := fun z : ℂ ↦ z - 1) w
    hGw hsub hdG hdsub, logDeriv_sub_const]

/-- **(O1) au pôle** : `(−ζ'/ζ) − 1/(·−1) = O(1)` sur `𝓝[≠] 1`. -/
theorem neg_logDeriv_riemannZeta_sub_principal_pole_isBigO :
    ((fun s ↦ -logDeriv riemannZeta s) - fun s ↦ 1 / (s - 1))
      =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  have hcont : ContinuousAt (logDeriv zetaPoleFactor) 1 :=
    (zetaPoleFactor_analyticAt_one.deriv.continuousAt).div
      zetaPoleFactor_analyticAt_one.continuousAt zetaPoleFactor_one_ne_zero
  have hO : (fun w ↦ -logDeriv zetaPoleFactor w) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) :=
    ((hcont.tendsto.mono_left nhdsWithin_le_nhds).neg).isBigO_one ℂ
  have heq : ((fun s ↦ -logDeriv riemannZeta s) - fun s ↦ 1 / (s - 1))
      =ᶠ[𝓝[≠] (1 : ℂ)] fun w ↦ -logDeriv zetaPoleFactor w := by
    filter_upwards [logDeriv_riemannZeta_eventuallyEq_pole] with w hw
    show -logDeriv riemannZeta w - 1 / (w - 1) = -logDeriv zetaPoleFactor w
    rw [hw]
    ring
  exact heq.trans_isBigO hO

/-! ## 3. (O2) méromorphie globale et pôles au plus simples pour −ζ'/ζ -/

/-- ζ est méromorphe en tout point de ℂ (analytique hors de 1 ; en 1, quotient
d'analytiques via `zetaPoleFactor`). -/
theorem meromorphicAt_riemannZeta (s : ℂ) : MeromorphicAt riemannZeta s := by
  by_cases hs : s = 1
  · subst hs
    have hmero : MeromorphicAt (fun w ↦ zetaPoleFactor w / (w - 1)) 1 :=
      (zetaPoleFactor_analyticAt_one.meromorphicAt).div
        ((analyticAt_id.sub analyticAt_const).meromorphicAt)
    apply hmero.congr
    have h0_ne : ∀ᶠ w in 𝓝 (1 : ℂ), w ≠ 0 :=
      continuousAt_id.eventually_ne (by norm_num)
    filter_upwards [nhdsWithin_le_nhds h0_ne, self_mem_nhdsWithin] with w hw0 hw1
    exact (riemannZeta_eq_zetaPoleFactor_div hw0 hw1).symm
  · exact (analyticOn_riemannZeta s (by simpa using hs)).meromorphicAt

/-- `−ζ'/ζ` est méromorphe en tout point de ℂ. -/
theorem meromorphicAt_neg_logDeriv_riemannZeta (s : ℂ) :
    MeromorphicAt (fun s ↦ -logDeriv riemannZeta s) s := by
  have h : MeromorphicAt (logDeriv riemannZeta) s :=
    ((meromorphicAt_riemannZeta s).deriv).div (meromorphicAt_riemannZeta s)
  exact h.neg

/-- **Ordre −1 général** : en un zéro d'ordre fini NON NUL d'une fonction analytique, la
dérivée logarithmique a un pôle exactement simple. La multiplicité passe intégralement dans
le résidu, jamais dans l'ordre du pôle. -/
theorem meromorphicOrderAt_logDeriv_eq_neg_one {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hne : analyticOrderAt f x ≠ ⊤)
    (hn : analyticOrderNatAt f x ≠ 0) :
    meromorphicOrderAt (logDeriv f) x = ((-1 : ℤ) : WithTop ℤ) := by
  obtain ⟨g, hg, hgx, hev⟩ := exists_logDeriv_eventuallyEq_principal_add hf hne
  set n : ℕ := analyticOrderNatAt f x with hn_def
  have hldg_ana : AnalyticAt ℂ (logDeriv g) x := (hg.deriv).div hg hgx
  set h : ℂ → ℂ := fun w ↦ (n : ℂ) + (w - x) * logDeriv g w with hh_def
  have hh_ana : AnalyticAt ℂ h x :=
    analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hldg_ana)
  have hh_ne : h x ≠ 0 := by
    simp only [hh_def, sub_self, zero_mul, add_zero]
    exact_mod_cast hn
  have hrepr : ∀ᶠ w in 𝓝[≠] x, logDeriv f w = (w - x) ^ (-1 : ℤ) • h w := by
    filter_upwards [hev, self_mem_nhdsWithin] with w hw hwx
    have hsub : w - x ≠ 0 := sub_ne_zero.mpr hwx
    rw [hw, zpow_neg_one, smul_eq_mul, hh_def]
    field_simp
  have hmero : MeromorphicAt (logDeriv f) x :=
    (hf.meromorphicAt.deriv).div hf.meromorphicAt
  exact (meromorphicOrderAt_eq_int_iff hmero).mpr ⟨h, hh_ana, hh_ne, hrepr⟩

/-- **(O2) au zéro** : `−ζ'/ζ` a un pôle exactement simple en chaque zéro de ζ,
quelle que soit la multiplicité. -/
theorem meromorphicOrderAt_neg_logDeriv_riemannZeta_zero {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) :
    meromorphicOrderAt (fun s ↦ -logDeriv riemannZeta s) ρ = ((-1 : ℤ) : WithTop ℤ) := by
  have hord : meromorphicOrderAt (logDeriv riemannZeta) ρ = ((-1 : ℤ) : WithTop ℤ) :=
    meromorphicOrderAt_logDeriv_eq_neg_one
      (analyticAt_riemannZeta_of_zero hρ) (riemannZeta_analyticOrderAt_ne_top hρ)
      (zetaZeroMultiplicity_pos hρ).ne'
  have hneg : meromorphicOrderAt (-(logDeriv riemannZeta)) ρ
      = meromorphicOrderAt (logDeriv riemannZeta) ρ := meromorphicOrderAt_neg.symm
  exact hneg.trans hord

/-- **(O2) au pôle** : `−ζ'/ζ` a un pôle exactement simple en `1`. -/
theorem meromorphicOrderAt_neg_logDeriv_riemannZeta_pole :
    meromorphicOrderAt (fun s ↦ -logDeriv riemannZeta s) 1 = ((-1 : ℤ) : WithTop ℤ) := by
  have hldG_ana : AnalyticAt ℂ (logDeriv zetaPoleFactor) 1 :=
    (zetaPoleFactor_analyticAt_one.deriv).div
      zetaPoleFactor_analyticAt_one zetaPoleFactor_one_ne_zero
  set h : ℂ → ℂ := fun w ↦ (w - 1) * logDeriv zetaPoleFactor w - 1 with hh_def
  have hh_ana : AnalyticAt ℂ h 1 :=
    (((analyticAt_id.sub analyticAt_const).mul hldG_ana).sub analyticAt_const)
  have hh_ne : h 1 ≠ 0 := by
    simp [hh_def]
  have hrepr : ∀ᶠ w in 𝓝[≠] (1 : ℂ),
      logDeriv riemannZeta w = (w - 1) ^ (-1 : ℤ) • h w := by
    filter_upwards [logDeriv_riemannZeta_eventuallyEq_pole, self_mem_nhdsWithin]
      with w hw hwx
    have hsub : w - 1 ≠ 0 := sub_ne_zero.mpr hwx
    rw [hw, zpow_neg_one, smul_eq_mul, hh_def]
    field_simp
  have hmero : MeromorphicAt (logDeriv riemannZeta) 1 :=
    ((meromorphicAt_riemannZeta 1).deriv).div (meromorphicAt_riemannZeta 1)
  have hord : meromorphicOrderAt (logDeriv riemannZeta) 1 = ((-1 : ℤ) : WithTop ℤ) :=
    (meromorphicOrderAt_eq_int_iff hmero).mpr ⟨h, hh_ana, hh_ne, hrepr⟩
  have hneg : meromorphicOrderAt (-(logDeriv riemannZeta)) 1
      = meromorphicOrderAt (logDeriv riemannZeta) 1 := meromorphicOrderAt_neg.symm
  exact hneg.trans hord

/-- Aux points réguliers (`s ≠ 1`, `ζ(s) ≠ 0`), `ζ'/ζ` est analytique. -/
theorem analyticAt_logDeriv_riemannZeta {s : ℂ} (hs1 : s ≠ 1)
    (hsz : riemannZeta s ≠ 0) :
    AnalyticAt ℂ (logDeriv riemannZeta) s := by
  have hζ : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa using hs1)
  exact (hζ.deriv).div hζ hsz

/-- **(O2), −ζ'/ζ, sur tout ℂ** : tous les pôles de `−ζ'/ζ` sont au plus simples, au sens
exact de l'échafaudage `HasSimplePolesOn` du port P2. -/
theorem hasSimplePolesOn_neg_logDeriv_riemannZeta_univ :
    HasSimplePolesOn (fun s ↦ -logDeriv riemannZeta s) Set.univ := by
  intro z _
  by_cases hz1 : z = 1
  · subst hz1
    rw [meromorphicOrderAt_neg_logDeriv_riemannZeta_pole]
  by_cases hzz : riemannZeta z = 0
  · rw [meromorphicOrderAt_neg_logDeriv_riemannZeta_zero hzz]
  · have hana : AnalyticAt ℂ (fun s ↦ -logDeriv riemannZeta s) z :=
      (analyticAt_logDeriv_riemannZeta hz1 hzz).neg
    have h0 : ((-1 : ℤ) : WithTop ℤ) ≤ 0 := by
      exact_mod_cast (by norm_num : (-1 : ℤ) ≤ 0)
    exact h0.trans hana.meromorphicOrderAt_nonneg

/-! ## 4. Les singularités du noyau évitent les zéros de ζ -/

/-- `ζ(0) = −1/2 ≠ 0`. -/
theorem riemannZeta_zero_ne_zero : riemannZeta 0 ≠ 0 := by
  rw [riemannZeta_zero]
  norm_num

/-- `ζ(−1) = −1/12 ≠ 0` (valeur de Bernoulli). -/
theorem riemannZeta_neg_one_ne_zero : riemannZeta (-1) ≠ 0 := by
  have h := riemannZeta_neg_nat_eq_bernoulli' 1
  rw [Nat.cast_one] at h
  rw [h, bernoulli'_two]
  norm_num

/-- Aucun zéro de ζ n'est en `0`. -/
theorem zetaZero_ne_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) : ρ ≠ 0 := by
  intro h; subst h; exact riemannZeta_zero_ne_zero hρ

/-- Aucun zéro de ζ n'est en `−1`. -/
theorem zetaZero_ne_negOne {ρ : ℂ} (hρ : riemannZeta ρ = 0) : ρ ≠ -1 := by
  intro h; subst h; exact riemannZeta_neg_one_ne_zero hρ

/-! ## 5. (O2) pour l'intégrande complet `−(ζ'/ζ)(s)·x^s/(s(s+1))` -/

/-- Pour `x > 0`, `s ↦ x^s` est analytique en tout point (exponentielle d'une fonction
linéaire). -/
theorem analyticAt_const_cpow_of_pos {x : ℝ} (xpos : 0 < x) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦ (x : ℂ) ^ z) s := by
  have hx : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr xpos.ne'
  have heq : (fun z : ℂ ↦ (x : ℂ) ^ z)
      = fun z : ℂ ↦ Complex.exp (Complex.log x * z) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero hx]
  rw [heq]
  exact (analyticAt_const.mul analyticAt_id).cexp

/-- Pour `x > 0`, `x^s ≠ 0` pour tout `s`. -/
theorem const_cpow_ne_zero_of_pos {x : ℝ} (xpos : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s ≠ 0 := by
  have hx : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr xpos.ne'
  rw [Complex.cpow_def_of_ne_zero hx]
  exact Complex.exp_ne_zero _

/-- Le noyau de Perron est méromorphe en tout point. -/
theorem meromorphicAt_perronKernel {x : ℝ} (xpos : 0 < x) (s : ℂ) :
    MeromorphicAt (Perron.f x) s := by
  have h1 : MeromorphicAt (fun z : ℂ ↦ (x : ℂ) ^ z) s :=
    (analyticAt_const_cpow_of_pos xpos s).meromorphicAt
  have h2 : MeromorphicAt (fun z : ℂ ↦ z * (z + 1)) s :=
    ((analyticAt_id.mul (analyticAt_id.add analyticAt_const))).meromorphicAt
  exact h1.div h2

/-- L'intégrande complet est méromorphe en tout point. -/
theorem meromorphicAt_perronZetaIntegrand {x : ℝ} (xpos : 0 < x) (s : ℂ) :
    MeromorphicAt (fun s ↦ -logDeriv riemannZeta s * Perron.f x s) s :=
  (meromorphicAt_neg_logDeriv_riemannZeta s).mul (meromorphicAt_perronKernel xpos s)

/-- Hors de `{0, −1}`, le noyau est analytique. -/
theorem analyticAt_perronKernel {x : ℝ} (xpos : 0 < x) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ -1) :
    AnalyticAt ℂ (Perron.f x) s := by
  have hden : s * (s + 1) ≠ 0 := by
    apply mul_ne_zero hs0
    intro h
    exact hs1 (by linear_combination h)
  have h1 : AnalyticAt ℂ (fun z : ℂ ↦ (x : ℂ) ^ z) s := analyticAt_const_cpow_of_pos xpos s
  have h2 : AnalyticAt ℂ (fun z : ℂ ↦ z * (z + 1)) s :=
    analyticAt_id.mul (analyticAt_id.add analyticAt_const)
  exact h1.div h2 hden

/-- Hors de `{0, −1}`, le noyau ne s'annule pas. -/
theorem perronKernel_ne_zero {x : ℝ} (xpos : 0 < x) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ -1) :
    Perron.f x s ≠ 0 := by
  have hden : s * (s + 1) ≠ 0 := by
    apply mul_ne_zero hs0
    intro h
    exact hs1 (by linear_combination h)
  exact div_ne_zero (const_cpow_ne_zero_of_pos xpos s) hden

/-- Ordre méromorphe exact du noyau en `0` : pôle simple. -/
theorem meromorphicOrderAt_perronKernel_zero {x : ℝ} (xpos : 0 < x) :
    meromorphicOrderAt (Perron.f x) 0 = ((-1 : ℤ) : WithTop ℤ) := by
  -- K = (x^s/(s+1)) * s⁻¹
  have hkey : Perron.f x = fun s : ℂ ↦ ((x : ℂ) ^ s / (s + 1)) * s⁻¹ := by
    funext s
    show (x : ℂ) ^ s / (s * (s + 1)) = ((x : ℂ) ^ s / (s + 1)) * s⁻¹
    rw [mul_comm s (s + 1), ← div_div, div_eq_mul_inv]
  have hD_ana : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s / (s + 1)) 0 := by
    have h1 := analyticAt_const_cpow_of_pos xpos 0
    have h2 : AnalyticAt ℂ (fun z : ℂ ↦ z + 1) 0 := analyticAt_id.add analyticAt_const
    exact h1.div h2 (by norm_num)
  have hD_ne : ((x : ℂ) ^ (0 : ℂ) / ((0 : ℂ) + 1)) ≠ 0 := by
    rw [Complex.cpow_zero]
    norm_num
  have hD_ord : meromorphicOrderAt (fun s : ℂ ↦ (x : ℂ) ^ s / (s + 1)) 0
      = ((0 : ℤ) : WithTop ℤ) := by
    rw [hD_ana.meromorphicOrderAt_eq, hD_ana.analyticOrderAt_eq_zero.mpr hD_ne]
    simp
  have hid_mero : MeromorphicAt (fun s : ℂ ↦ s) (0 : ℂ) :=
    (analyticAt_id (𝕜 := ℂ)).meromorphicAt
  have hinv_ord : meromorphicOrderAt (fun s : ℂ ↦ s⁻¹) 0 = ((-1 : ℤ) : WithTop ℤ) := by
    have hid : meromorphicOrderAt (fun s : ℂ ↦ s) (0 : ℂ) = ((1 : ℤ) : WithTop ℤ) :=
      meromorphicOrderAt_id
    have h : meromorphicOrderAt ((fun s : ℂ ↦ s)⁻¹) 0
        = -meromorphicOrderAt (fun s : ℂ ↦ s) (0 : ℂ) := meromorphicOrderAt_inv
    have hfun : ((fun s : ℂ ↦ s)⁻¹) = fun s : ℂ ↦ s⁻¹ := rfl
    rw [hfun, hid] at h
    rw [h]
    rfl
  have hmul := meromorphicOrderAt_mul hD_ana.meromorphicAt hid_mero.inv
  have hfunmul : ((fun s : ℂ ↦ (x : ℂ) ^ s / (s + 1)) * (fun s : ℂ ↦ s)⁻¹)
      = fun s : ℂ ↦ ((x : ℂ) ^ s / (s + 1)) * s⁻¹ := rfl
  rw [hfunmul] at hmul
  have hfuninv : meromorphicOrderAt ((fun s : ℂ ↦ s)⁻¹) (0 : ℂ)
      = meromorphicOrderAt (fun s : ℂ ↦ s⁻¹) (0 : ℂ) := rfl
  rw [hkey, hmul, hfuninv, hD_ord, hinv_ord]
  rfl

/-- Ordre méromorphe exact du noyau en `−1` : pôle simple. -/
theorem meromorphicOrderAt_perronKernel_negOne {x : ℝ} (xpos : 0 < x) :
    meromorphicOrderAt (Perron.f x) (-1) = ((-1 : ℤ) : WithTop ℤ) := by
  -- K = (x^s/s) * (s+1)⁻¹
  have hkey : Perron.f x = fun s : ℂ ↦ ((x : ℂ) ^ s / s) * (s + 1)⁻¹ := by
    funext s
    show (x : ℂ) ^ s / (s * (s + 1)) = ((x : ℂ) ^ s / s) * (s + 1)⁻¹
    rw [← div_div, div_eq_mul_inv]
  have hD_ana : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s / s) (-1) := by
    have h1 := analyticAt_const_cpow_of_pos xpos (-1)
    exact h1.div analyticAt_id (by norm_num)
  have hD_ne : ((x : ℂ) ^ (-1 : ℂ) / (-1 : ℂ)) ≠ 0 := by
    apply div_ne_zero (const_cpow_ne_zero_of_pos xpos _)
    norm_num
  have hD_ord : meromorphicOrderAt (fun s : ℂ ↦ (x : ℂ) ^ s / s) (-1)
      = ((0 : ℤ) : WithTop ℤ) := by
    rw [hD_ana.meromorphicOrderAt_eq, hD_ana.analyticOrderAt_eq_zero.mpr hD_ne]
    simp
  have haff_ana : AnalyticAt ℂ (fun s : ℂ ↦ s + 1) (-1) := analyticAt_id.add analyticAt_const
  have haff_ord : meromorphicOrderAt (fun s : ℂ ↦ s + 1) (-1) = ((1 : ℤ) : WithTop ℤ) := by
    have hmono := analyticOrderAt_centeredMonomial (𝕜 := ℂ) (z₀ := (-1 : ℂ)) (n := 1)
    have heq : ((fun z : ℂ ↦ z - (-1)) ^ (1 : ℕ)) = fun s : ℂ ↦ s + 1 := by
      funext z
      show (z - (-1)) ^ (1 : ℕ) = z + 1
      rw [pow_one, sub_neg_eq_add]
    rw [heq] at hmono
    rw [haff_ana.meromorphicOrderAt_eq, hmono]
    rfl
  have hinv_ord : meromorphicOrderAt (fun s : ℂ ↦ (s + 1)⁻¹) (-1)
      = ((-1 : ℤ) : WithTop ℤ) := by
    have h : meromorphicOrderAt ((fun s : ℂ ↦ s + 1)⁻¹) (-1)
        = -meromorphicOrderAt (fun s : ℂ ↦ s + 1) (-1) := meromorphicOrderAt_inv
    have hfun : ((fun s : ℂ ↦ s + 1)⁻¹) = fun s : ℂ ↦ (s + 1)⁻¹ := rfl
    rw [hfun, haff_ord] at h
    rw [h]
    rfl
  have hmul := meromorphicOrderAt_mul hD_ana.meromorphicAt (haff_ana.meromorphicAt.inv)
  have hfunmul : ((fun s : ℂ ↦ (x : ℂ) ^ s / s) * (fun s : ℂ ↦ s + 1)⁻¹)
      = fun s : ℂ ↦ ((x : ℂ) ^ s / s) * (s + 1)⁻¹ := rfl
  rw [hfunmul] at hmul
  have hfuninv : meromorphicOrderAt ((fun s : ℂ ↦ s + 1)⁻¹) (-1 : ℂ)
      = meromorphicOrderAt (fun s : ℂ ↦ (s + 1)⁻¹) (-1 : ℂ) := rfl
  rw [hkey, hmul, hfuninv, hD_ord, hinv_ord]
  rfl

/-- **(O2), intégrande complet, sur tout ℂ** : tous les pôles de
`s ↦ −(ζ'/ζ)(s)·x^s/(s(s+1))` sont au plus simples. Les singularités sont disjointes :
pôle de ζ en `1`, zéros de ζ (jamais en `0` ni `−1`), pôles du noyau en `0` et `−1`
(où `ζ'/ζ` est analytique). -/
theorem hasSimplePolesOn_perronZetaIntegrand_univ {x : ℝ} (xpos : 0 < x) :
    HasSimplePolesOn (fun s ↦ -logDeriv riemannZeta s * Perron.f x s) Set.univ := by
  intro z _
  have hL := meromorphicAt_neg_logDeriv_riemannZeta z
  have hK := meromorphicAt_perronKernel xpos z
  have hprod : meromorphicOrderAt (fun s ↦ -logDeriv riemannZeta s * Perron.f x s) z
      = meromorphicOrderAt (fun s ↦ -logDeriv riemannZeta s) z
        + meromorphicOrderAt (Perron.f x) z := by
    have h := meromorphicOrderAt_mul (f := fun s ↦ -logDeriv riemannZeta s)
      (g := Perron.f x) hL hK
    have hfun : ((fun s ↦ -logDeriv riemannZeta s) * Perron.f x)
        = fun s ↦ -logDeriv riemannZeta s * Perron.f x s := rfl
    rw [← hfun]
    exact h
  rw [hprod]
  by_cases hz0 : z = 0
  · subst hz0
    have hL_nonneg : 0 ≤ meromorphicOrderAt (fun s ↦ -logDeriv riemannZeta s) 0 :=
      ((analyticAt_logDeriv_riemannZeta (by norm_num) riemannZeta_zero_ne_zero).neg
        ).meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_perronKernel_zero xpos]
    exact le_add_of_nonneg_left hL_nonneg
  by_cases hz1 : z = -1
  · subst hz1
    have hL_nonneg : 0 ≤ meromorphicOrderAt (fun s ↦ -logDeriv riemannZeta s) (-1) :=
      ((analyticAt_logDeriv_riemannZeta (by norm_num) riemannZeta_neg_one_ne_zero).neg
        ).meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_perronKernel_negOne xpos]
    exact le_add_of_nonneg_left hL_nonneg
  · -- hors {0, −1} : le noyau est analytique non nul (ordre 0)
    have hK_ana : AnalyticAt ℂ (Perron.f x) z := analyticAt_perronKernel xpos hz0 hz1
    have hK_ord : meromorphicOrderAt (Perron.f x) z = ((0 : ℤ) : WithTop ℤ) := by
      rw [hK_ana.meromorphicOrderAt_eq,
        hK_ana.analyticOrderAt_eq_zero.mpr (perronKernel_ne_zero xpos hz0 hz1)]
      simp
    have hK_ord' : meromorphicOrderAt (Perron.f x) z = (0 : WithTop ℤ) := hK_ord
    rw [hK_ord', add_zero]
    exact hasSimplePolesOn_neg_logDeriv_riemannZeta_univ z (mem_univ z)

/-! ## 6. (O3) résidus au sens du port, alimentés par les limites P1 -/

/-- Résidu (au sens du port P2) de `−ζ'/ζ` en un zéro : `−m(ρ)`, toute multiplicité. -/
theorem residue_neg_logDeriv_riemannZeta_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    residue (fun s ↦ -logDeriv riemannZeta s) ρ = -(zetaZeroMultiplicity ρ : ℂ) :=
  residue_eq_of_tendsto (tendsto_mul_neg_logDeriv_riemannZeta_zero hρ)

/-- Résidu (au sens du port P2) de `−ζ'/ζ` en `1` : `+1`. -/
theorem residue_neg_logDeriv_riemannZeta_pole :
    residue (fun s ↦ -logDeriv riemannZeta s) 1 = 1 :=
  residue_eq_of_tendsto tendsto_mul_neg_logDeriv_riemannZeta_pole

/-- Résidu de l'intégrande complet en un zéro : `−m(ρ)·K_x(ρ)` — le poids exact du futur
terme spectral, multiplicité comprise. -/
theorem residue_perronZetaIntegrand_zero {x : ℝ} (xpos : 0 < x) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) :
    residue (fun s ↦ -logDeriv riemannZeta s * Perron.f x s) ρ
      = -(zetaZeroMultiplicity ρ : ℂ) * Perron.f x ρ := by
  apply residue_eq_of_tendsto
  have h1 := tendsto_mul_neg_logDeriv_riemannZeta_zero hρ
  have hK : ContinuousAt (Perron.f x) ρ :=
    (analyticAt_perronKernel xpos (zetaZero_ne_zero hρ)
      (zetaZero_ne_negOne hρ)).continuousAt
  have h2 := h1.mul (hK.tendsto.mono_left nhdsWithin_le_nhds)
  apply h2.congr
  intro w
  ring

/-- Résidu de l'intégrande complet en `1` : `K_x(1)` — le futur terme principal. -/
theorem residue_perronZetaIntegrand_pole {x : ℝ} (xpos : 0 < x) :
    residue (fun s ↦ -logDeriv riemannZeta s * Perron.f x s) 1
      = Perron.f x 1 := by
  apply residue_eq_of_tendsto
  have h1 := tendsto_mul_neg_logDeriv_riemannZeta_pole
  have hK : ContinuousAt (Perron.f x) 1 :=
    (analyticAt_perronKernel xpos (by norm_num) (by norm_num)).continuousAt
  have h2 := h1.mul (hK.tendsto.mono_left nhdsWithin_le_nhds)
  have h3 : (fun w : ℂ ↦ (w - 1) * -logDeriv riemannZeta w * Perron.f x w) =
      fun w : ℂ ↦ (w - 1) * (-logDeriv riemannZeta w * Perron.f x w) := by
    funext w; ring
  rw [← h3]
  simpa using h2

end RHV3Lean

/-! ## Audit d'axiomes — Tour 23-B, itération P3a -/

#print axioms RHV3Lean.exists_logDeriv_eventuallyEq_principal_add
#print axioms RHV3Lean.logDeriv_sub_principal_isBigO
#print axioms RHV3Lean.neg_logDeriv_riemannZeta_sub_principal_zero_isBigO
#print axioms RHV3Lean.logDeriv_riemannZeta_eventuallyEq_pole
#print axioms RHV3Lean.neg_logDeriv_riemannZeta_sub_principal_pole_isBigO
#print axioms RHV3Lean.meromorphicAt_riemannZeta
#print axioms RHV3Lean.meromorphicAt_neg_logDeriv_riemannZeta
#print axioms RHV3Lean.meromorphicOrderAt_logDeriv_eq_neg_one
#print axioms RHV3Lean.meromorphicOrderAt_neg_logDeriv_riemannZeta_zero
#print axioms RHV3Lean.meromorphicOrderAt_neg_logDeriv_riemannZeta_pole
#print axioms RHV3Lean.analyticAt_logDeriv_riemannZeta
#print axioms RHV3Lean.hasSimplePolesOn_neg_logDeriv_riemannZeta_univ
#print axioms RHV3Lean.riemannZeta_zero_ne_zero
#print axioms RHV3Lean.riemannZeta_neg_one_ne_zero
#print axioms RHV3Lean.zetaZero_ne_zero
#print axioms RHV3Lean.zetaZero_ne_negOne
#print axioms RHV3Lean.analyticAt_const_cpow_of_pos
#print axioms RHV3Lean.const_cpow_ne_zero_of_pos
#print axioms RHV3Lean.meromorphicAt_perronKernel
#print axioms RHV3Lean.meromorphicAt_perronZetaIntegrand
#print axioms RHV3Lean.analyticAt_perronKernel
#print axioms RHV3Lean.perronKernel_ne_zero
#print axioms RHV3Lean.meromorphicOrderAt_perronKernel_zero
#print axioms RHV3Lean.meromorphicOrderAt_perronKernel_negOne
#print axioms RHV3Lean.hasSimplePolesOn_perronZetaIntegrand_univ
#print axioms RHV3Lean.residue_neg_logDeriv_riemannZeta_zero
#print axioms RHV3Lean.residue_neg_logDeriv_riemannZeta_pole
#print axioms RHV3Lean.residue_perronZetaIntegrand_zero
#print axioms RHV3Lean.residue_perronZetaIntegrand_pole
