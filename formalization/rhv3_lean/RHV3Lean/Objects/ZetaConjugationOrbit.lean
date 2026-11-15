/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaReflectionMultiplicity

/-!
# Tour 23-B — itération 3B2 : conjugaison et orbite complète des zéros

Cette étape prouve, sans supposer RH :

1. `ζ(s̄) = conj(ζ(s))` pour tout `s ≠ 1` (réalité analytique de ζ, via le principe de
   réflexion de Schwarz : égalité sur la série de Dirichlet dans `Re s > 1`, puis unicité
   analytique sur `ℂ \ {1}`) ;
2. la fermeture de l'ensemble des zéros de ζ sous conjugaison ;
3. la conservation exacte de la multiplicité analytique sous conjugaison ;
4. l'orbite finie complète `{ρ, ρ̄, 1-ρ, 1-ρ̄}` avec égalité des quatre multiplicités, en
   réutilisant la conservation sous réflexion déjà prouvée (`zetaZeroMultiplicity_zetaReflect`).

Rien ici ne suppose RH, la rigidité de `T`, une formule explicite, ou une hypothèse de zéros
simples. Perron et la formule explicite quantitative restent hors du périmètre de ce fichier.

Dossier mathématique préalable :
`validation/p4_autoresearch_prime/rh_resolution_progression/`
`stage36_round23b_iteration3b2_math_dossier.md`.
-/

open Set Filter
open scoped Topology ComplexConjugate

namespace RHV3Lean

/-! ## 1. Conjugaison termwise sur la série de Dirichlet -/

/-- Un entier naturel plongé dans `ℂ` a un argument différent de `π` : c'est un réel positif
ou nul, donc son argument vaut `0`. -/
theorem natCast_arg_ne_pi (m : ℕ) : ((m : ℂ)).arg ≠ Real.pi := by
  rw [Complex.natCast_arg]
  exact Real.pi_pos.ne

/-- La conjugaison commute avec la puissance complexe d'un entier naturel : c'est le cœur
arithmétique de la réalité de la série de Dirichlet. -/
theorem conj_natCast_cpow (m : ℕ) (s : ℂ) :
    conj ((m : ℂ) ^ s) = (m : ℂ) ^ conj s := by
  have h := Complex.conj_cpow (m : ℂ) (conj s) (natCast_arg_ne_pi m)
  rw [Complex.conj_natCast, Complex.conj_conj] at h
  exact h.symm

/-- Conjugaison du terme général `1 / n ^ s` de la série de Dirichlet. -/
theorem conj_one_div_natCast_cpow (m : ℕ) (s : ℂ) :
    conj (1 / (m : ℂ) ^ s) = 1 / (m : ℂ) ^ conj s := by
  rw [map_div₀, map_one, conj_natCast_cpow]

/-- Dans le demi-plan `Re s > 1`, où la série de Dirichlet converge absolument, ζ est
réelle-analytique : `conj (ζ s) = ζ (conj s)`. Aucune hypothèse RH, aucune analytic
continuation admise sans preuve : seule la convergence absolue de Mathlib est utilisée. -/
theorem riemannZeta_conj_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    conj (riemannZeta s) = riemannZeta (conj s) := by
  have hs' : 1 < (conj s).re := by simpa [Complex.conj_re] using hs
  rw [zeta_eq_tsum_one_div_nat_cpow hs, zeta_eq_tsum_one_div_nat_cpow hs', Complex.conj_tsum]
  exact tsum_congr fun m => conj_one_div_natCast_cpow m s

/-! ## 2. Prolongement par unicité analytique (réflexion de Schwarz) -/

/-- `conj s ≠ 1` équivaut à `s ≠ 1`, puisque `conj` est une involution fixant `1`. -/
theorem conj_ne_one_iff {s : ℂ} : conj s ≠ 1 ↔ s ≠ 1 := by
  constructor
  · intro h heq
    exact h (by rw [heq]; simp)
  · intro h heq
    exact h (by
      have := congrArg conj heq
      simpa using this)

/-- `conj ∘ riemannZeta ∘ conj` est différentiable en tout point différent de `1`, car ζ est
différentiable en `conj s`. C'est l'unique ingrédient calculatoire du principe de réflexion. -/
theorem differentiableAt_conjRiemannZetaConj {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (conj ∘ riemannZeta ∘ conj) s := by
  have hcs1 : conj s ≠ 1 := conj_ne_one_iff.mpr hs
  have hf : DifferentiableAt ℂ riemannZeta (conj s) := differentiableAt_riemannZeta hcs1
  simpa using hf.conj_conj

/-- `conj ∘ riemannZeta ∘ conj` est analytique sur `ℂ \ {1}`, exactement comme ζ elle-même. -/
theorem analyticOnNhd_conjRiemannZetaConj :
    AnalyticOnNhd ℂ (conj ∘ riemannZeta ∘ conj) ({1}ᶜ : Set ℂ) :=
  DifferentiableOn.analyticOnNhd
    (fun s hs => (differentiableAt_conjRiemannZetaConj (by simpa using hs)).differentiableWithinAt)
    isOpen_compl_singleton

/-- Réécriture, pour `Re s > 1`, de l'identité de réalité sous la forme requise par le principe
d'identité : `ζ(s) = conj(ζ(conj s))`. -/
theorem riemannZeta_eq_conjRiemannZetaConj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = (conj ∘ riemannZeta ∘ conj) s := by
  have h := riemannZeta_conj_eq_of_one_lt_re hs
  simpa [Function.comp] using congrArg conj h

/-- ζ et `conj ∘ ζ ∘ conj` coïncident sur un voisinage ouvert de `2`, à savoir le demi-plan
`Re > 1`. -/
theorem riemannZeta_eventuallyEq_conjRiemannZetaConj :
    riemannZeta =ᶠ[𝓝 (2 : ℂ)] (conj ∘ riemannZeta ∘ conj) := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hmem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
  filter_upwards [hopen.mem_nhds hmem] with z hz
  exact riemannZeta_eq_conjRiemannZetaConj_of_one_lt_re hz

/-- **Principe d'identité (réflexion de Schwarz) pour ζ, sans RH.** Les deux fonctions
analytiques `ζ` et `conj ∘ ζ ∘ conj` coïncident sur le demi-plan `Re > 1` ; comme
`ℂ \ {1}` est préconnexe (déjà prouvé dans `ZetaZeroMultiplicity.lean`), elles coïncident sur
tout `ℂ \ {1}`. -/
theorem riemannZeta_eq_conjRiemannZetaConj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = (conj ∘ riemannZeta ∘ conj) s := by
  have hmem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hsmem : s ∈ ({1}ᶜ : Set ℂ) := by simpa using hs
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    analyticOn_riemannZeta analyticOnNhd_conjRiemannZetaConj
    isPreconnected_compl_one_complex hmem
    riemannZeta_eventuallyEq_conjRiemannZetaConj hsmem

/-- **Réalité analytique globale de ζ, sans RH** : `conj(ζ(s)) = ζ(conj s)` pour tout
`s ≠ 1`. Ceci est la forme unconditionnelle du principe de réflexion de Schwarz appliqué à
`riemannZeta`. -/
theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    conj (riemannZeta s) = riemannZeta (conj s) := by
  have h := riemannZeta_eq_conjRiemannZetaConj hs
  simpa [Function.comp] using congrArg conj h

/-! ## 3. Fermeture de l'ensemble des zéros sous conjugaison -/

/-- Si `ρ` est un zéro de ζ, alors `conj ρ` en est un aussi : les zéros de ζ sont stables sous
conjugaison complexe. -/
theorem riemannZeta_conj_eq_zero_of_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    riemannZeta (conj ρ) = 0 := by
  have hρ1 : ρ ≠ 1 := zetaZero_ne_one hρ
  have h := riemannZeta_conj hρ1
  rw [hρ, map_zero] at h
  exact h.symm

/-! ## 4. Conservation de la multiplicité analytique sous conjugaison -/

/-- La `n`-ième dérivée itérée de `conj ∘ f ∘ conj` en `x` est `conj` de la `n`-ième dérivée
itérée de `f` en `conj x`. C'est le transport exact des dérivées sous double conjugaison,
utilisant uniquement `deriv_conj_conj` de Mathlib (aucune hypothèse d'analyticité requise, la
formule vaut aussi en valeur "junk" hors différentiabilité). -/
theorem iteratedDeriv_conj_conj (n : ℕ) (f : ℂ → ℂ) (x : ℂ) :
    iteratedDeriv n (conj ∘ f ∘ conj) x = conj (iteratedDeriv n f (conj x)) := by
  induction n generalizing f x with
  | zero => simp
  | succ n IH =>
    have h1 : iteratedDeriv (n + 1) (conj ∘ f ∘ conj) x
        = iteratedDeriv n (deriv (conj ∘ f ∘ conj)) x := by
      rw [iteratedDeriv_succ']
    have h2 : deriv (conj ∘ f ∘ conj) = conj ∘ deriv f ∘ conj := deriv_conj_conj
    have h3 : iteratedDeriv (n + 1) f (conj x) = iteratedDeriv n (deriv f) (conj x) := by
      rw [iteratedDeriv_succ']
    rw [h1, h2, IH (deriv f) x, ← h3]

/-- L'ordre analytique naturel de ζ en `conj ρ` est égal à l'ordre analytique naturel de
`conj ∘ ζ ∘ conj` en `ρ`, pour tout zéro `ρ` de ζ. La preuve compare les motifs
d'annulation des dérivées itérées via `analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero`, en
s'appuyant sur la finitude déjà établie (`riemannZeta_analyticOrderAt_ne_top`) pour éviter tout
cas `⊤`. -/
theorem analyticOrderNatAt_conjRiemannZetaConj_eq_riemannZeta_conj {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) :
    analyticOrderNatAt (conj ∘ riemannZeta ∘ conj) ρ = analyticOrderNatAt riemannZeta (conj ρ) := by
  have hρc : riemannZeta (conj ρ) = 0 := riemannZeta_conj_eq_zero_of_zero hρ
  have hρ1 : ρ ≠ 1 := zetaZero_ne_one hρ
  have hρc1 : conj ρ ≠ 1 := zetaZero_ne_one hρc
  have hanaC : AnalyticAt ℂ (conj ∘ riemannZeta ∘ conj) ρ :=
    analyticOnNhd_conjRiemannZetaConj ρ (by simpa using hρ1)
  have hanaZ : AnalyticAt ℂ riemannZeta (conj ρ) :=
    analyticOn_riemannZeta (conj ρ) (by simpa using hρc1)
  have hfin : analyticOrderAt riemannZeta (conj ρ) ≠ ⊤ :=
    riemannZeta_analyticOrderAt_ne_top hρc
  set n : ℕ := analyticOrderNatAt riemannZeta (conj ρ) with hn_def
  have hn_eq : analyticOrderAt riemannZeta (conj ρ) = (n : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt hfin).symm
  have hpat := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hanaZ (n := n)).mp hn_eq
  obtain ⟨hzero_k, hnz_n⟩ := hpat
  have hzero_k' : ∀ k < n, iteratedDeriv k (conj ∘ riemannZeta ∘ conj) ρ = 0 := by
    intro k hk
    rw [iteratedDeriv_conj_conj, hzero_k k hk, map_zero]
  have hnz_n' : iteratedDeriv n (conj ∘ riemannZeta ∘ conj) ρ ≠ 0 := by
    rw [iteratedDeriv_conj_conj]
    exact fun h => hnz_n (by simpa using congrArg conj h)
  have hAt_h : analyticOrderAt (conj ∘ riemannZeta ∘ conj) ρ = (n : ℕ∞) :=
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hanaC (n := n)).mpr ⟨hzero_k', hnz_n'⟩
  have hfin_h : analyticOrderAt (conj ∘ riemannZeta ∘ conj) ρ ≠ ⊤ := by
    rw [hAt_h]; exact ENat.coe_ne_top n
  have : (analyticOrderNatAt (conj ∘ riemannZeta ∘ conj) ρ : ℕ∞)
      = analyticOrderAt (conj ∘ riemannZeta ∘ conj) ρ :=
    Nat.cast_analyticOrderNatAt hfin_h
  rw [hAt_h] at this
  exact_mod_cast this

/-- ζ et `conj ∘ ζ ∘ conj` ont le même ordre analytique naturel en tout point `ρ ≠ 1` : ils
coïncident sur tout un voisinage de `ρ` (le préconnexe `ℂ \ {1}`), donc `analyticOrderAt_congr`
s'applique directement. -/
theorem analyticOrderNatAt_riemannZeta_eq_conjRiemannZetaConj {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    analyticOrderNatAt riemannZeta ρ = analyticOrderNatAt (conj ∘ riemannZeta ∘ conj) ρ := by
  have heq : riemannZeta =ᶠ[𝓝 ρ] (conj ∘ riemannZeta ∘ conj) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hρ1] with z hz
    exact riemannZeta_eq_conjRiemannZetaConj hz
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr heq]

/-- **Conservation exacte de la multiplicité analytique sous conjugaison.** Pour tout zéro `ρ`
de ζ, `m(ρ̄) = m(ρ)`. Aucune hypothèse de simplicité des zéros. -/
theorem zetaZeroMultiplicity_conj {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    zetaZeroMultiplicity (conj ρ) = zetaZeroMultiplicity ρ := by
  change analyticOrderNatAt riemannZeta (conj ρ) = analyticOrderNatAt riemannZeta ρ
  rw [← analyticOrderNatAt_conjRiemannZetaConj_eq_riemannZeta_conj hρ,
    ← analyticOrderNatAt_riemannZeta_eq_conjRiemannZetaConj (zetaZero_ne_one hρ)]

/-! ## 5. Orbite finie complète sous conjugaison et réflexion fonctionnelle -/

/-- L'orbite finie `{ρ, ρ̄, 1-ρ, 1-ρ̄}` d'un zéro `ρ` situé dans la bande ouverte
`0 < Re ρ < 1`. -/
noncomputable def zetaConjugationReflectionOrbit (ρ : ℂ) : Finset ℂ := by
  classical
  exact {ρ, conj ρ, zetaReflect ρ, zetaReflect (conj ρ)}

/-- Les quatre points de l'orbite sont des zéros de ζ. -/
theorem zetaConjugationReflectionOrbit_zero {ρ : ℂ}
    (hzero : riemannZeta ρ = 0) (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) :
    ∀ z ∈ zetaConjugationReflectionOrbit ρ, riemannZeta z = 0 := by
  have hconj : riemannZeta (conj ρ) = 0 := riemannZeta_conj_eq_zero_of_zero hzero
  have hrefl : riemannZeta (zetaReflect ρ) = 0 :=
    riemannZeta_zetaReflect_eq_zero hzero hre0
  have hreflconj : riemannZeta (zetaReflect (conj ρ)) = 0 :=
    riemannZeta_zetaReflect_eq_zero hconj (by simpa [Complex.conj_re] using hre0)
  intro z hz
  simp only [zetaConjugationReflectionOrbit, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact hzero
  · exact hconj
  · exact hrefl
  · exact hreflconj

/-- **Orbite complète à multiplicités égales.** Sous les hypothèses standard (zéro non trivial
dans la bande ouverte), les quatre points de l'orbite `{ρ, ρ̄, 1-ρ, 1-ρ̄}` ont exactement la
même multiplicité analytique. Ceci combine la conservation sous réflexion
(`zetaZeroMultiplicity_zetaReflect`, itération 3A/3B1) et la conservation sous conjugaison
(`zetaZeroMultiplicity_conj`, ce fichier). Aucune hypothèse de simplicité des zéros. -/
theorem zetaConjugationReflectionOrbit_multiplicity_eq {ρ : ℂ}
    (hzero : riemannZeta ρ = 0) (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) :
    zetaZeroMultiplicity (conj ρ) = zetaZeroMultiplicity ρ ∧
    zetaZeroMultiplicity (zetaReflect ρ) = zetaZeroMultiplicity ρ ∧
    zetaZeroMultiplicity (zetaReflect (conj ρ)) = zetaZeroMultiplicity ρ := by
  have hconj : riemannZeta (conj ρ) = 0 := riemannZeta_conj_eq_zero_of_zero hzero
  have hconjre0 : 0 < (conj ρ).re := by simpa [Complex.conj_re] using hre0
  have hconjre1 : (conj ρ).re < 1 := by simpa [Complex.conj_re] using hre1
  have hEq1 : zetaZeroMultiplicity (conj ρ) = zetaZeroMultiplicity ρ :=
    zetaZeroMultiplicity_conj hzero
  have hEq2 : zetaZeroMultiplicity (zetaReflect ρ) = zetaZeroMultiplicity ρ :=
    zetaZeroMultiplicity_zetaReflect hzero hre0 hre1
  have hEq3 : zetaZeroMultiplicity (zetaReflect (conj ρ)) = zetaZeroMultiplicity (conj ρ) :=
    zetaZeroMultiplicity_zetaReflect hconj hconjre0 hconjre1
  exact ⟨hEq1, hEq2, hEq3.trans hEq1⟩

end RHV3Lean

/-! ## Audit d'axiomes — Tour 23-B, itération 3B2 -/

#print axioms RHV3Lean.natCast_arg_ne_pi
#print axioms RHV3Lean.conj_natCast_cpow
#print axioms RHV3Lean.conj_one_div_natCast_cpow
#print axioms RHV3Lean.riemannZeta_conj_eq_of_one_lt_re
#print axioms RHV3Lean.conj_ne_one_iff
#print axioms RHV3Lean.differentiableAt_conjRiemannZetaConj
#print axioms RHV3Lean.analyticOnNhd_conjRiemannZetaConj
#print axioms RHV3Lean.riemannZeta_eq_conjRiemannZetaConj_of_one_lt_re
#print axioms RHV3Lean.riemannZeta_eventuallyEq_conjRiemannZetaConj
#print axioms RHV3Lean.riemannZeta_eq_conjRiemannZetaConj
#print axioms RHV3Lean.riemannZeta_conj
#print axioms RHV3Lean.riemannZeta_conj_eq_zero_of_zero
#print axioms RHV3Lean.iteratedDeriv_conj_conj
#print axioms RHV3Lean.analyticOrderNatAt_conjRiemannZetaConj_eq_riemannZeta_conj
#print axioms RHV3Lean.analyticOrderNatAt_riemannZeta_eq_conjRiemannZetaConj
#print axioms RHV3Lean.zetaZeroMultiplicity_conj
#print axioms RHV3Lean.zetaConjugationReflectionOrbit_zero
#print axioms RHV3Lean.zetaConjugationReflectionOrbit_multiplicity_eq
