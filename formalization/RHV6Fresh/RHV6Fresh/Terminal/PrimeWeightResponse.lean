/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.SpontaneousRegimeBreak

/-!
# RHV6Fresh — réponse radiale aux poids premiers, candidat différentiel de E142 (auteur, 2026-10-01)

Numérotation : livrée sous le nom E141 ; dans la numérotation finale de l'auteur (E141 détecteur,
E142 prédiction, E143 exactitude, E144 évaluation, E145 propagation ;
`Terminal/ChangePredictor.lean`), c'est un candidat prédicteur de E142.

Demande de l'auteur : partir d'un membre engagé, construire d'abord une famille `Z_ε` avec
`Z_0 = ζ`, en dériver ensuite les coefficients premiers `Λ(n) + ε·w(n) + …`, suivre un zéro
`ρ(ε) = β(ε) + i·T(ε)` et comparer `dβ/dε` à `dT/dε` en `ε = 0`. Deux directions : une qui conserve
la réflexion par rapport à la ligne, et le contrôle par les facteurs du monde `engagedBreakWorld`.
Question : qu'est-ce qui, dans les coefficients exacts, annule la réponse radiale ?

Aucun énoncé de ce fichier ne pose un membre hors ligne ; aucune prémisse n'est ajoutée.

* **§1 Famille construite d'abord** (`weightFamily c ε s = ζ(s − ε·c)`, les facteurs du monde de
  contrôle) : `Z_0 = ζ` ; coefficients premiers dérivés de la fonction, `Λ(n)·n^{ε·c}`
  (`weightFamily_primeWeights`), de dérivée `Λ(n)·log n·c` en `ε = 0`
  (`weightFamily_weight_response`), de module `Λ(n)·n^{ε·Re c}` (`weightFamily_weight_norm`) ;
  chaque membre devient `ρ + ε·c` : réponse radiale `Re c`, réponse de hauteur `Im c`
  (`weightFamily_member_response`). Réponse radiale nulle ⟺ `Re c = 0` ⟺ le module de chaque
  poids est conservé (`weightFamily_radial_zero_iff_weight_modulus`). La direction verticale
  `c = i` conserve la réflexion par rapport à la ligne (`vertical_direction_keeps_reflection`).
* **§2 Toute direction qui conserve la réflexion** (`reflection_direction_response`) : pour une
  fonction réelle sur la ligne, un zéro simple en ligne et une direction réelle au point, la
  réponse radiale au premier ordre est nulle et la réponse de hauteur est `Φ(ρ)/Im Ξ'(ρ)`.
  Appliqué à zêta complétée (`engaged_member_reflection_response`).
* **§3 Contrôle** (`regimeWitness_reflection_response`) : le même énoncé tient, mot pour mot, pour
  le membre en ligne de la fonction fixe sans premiers, dont le régime change au membre suivant.

Borne : l'annulation de la réponse radiale au premier ordre vient de la réflexion et de la
simplicité du membre en ligne, pas des poids exacts ; elle tient dans un monde dont le régime
change. Elle porte sur un membre déjà en ligne : appliquée à l'arrivée, elle demande que l'arrivée
soit en ligne. Dans la famille de §1, tous les membres répondent de la même façon, en ligne ou
non. Non compilé : aucune série de Dirichlet autre qu'un multiple de `ζ` ne conserve son équation
fonctionnelle exacte (Hamburger, 1921, littérature).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune `def` de prémisse.
-/

open Complex ArithmeticFunction LSeries.notation Topology

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Famille construite d'abord, coefficients premiers dérivés ensuite -/

/-- **La famille** : `Z_ε(s) = ζ(s − ε·c)`. Ce sont les facteurs du monde `engagedBreakWorld`. -/
noncomputable def weightFamily (c : ℂ) (ε : ℝ) (s : ℂ) : ℂ := riemannZeta (s - (ε : ℂ) * c)

/-- `Z_0 = ζ`. -/
theorem weightFamily_zero (c : ℂ) : weightFamily c 0 = riemannZeta := by
  funext s
  simp [weightFamily]

/-- **Coefficients premiers, dérivés de la fonction** : `−Z_ε'/Z_ε(s) = Σ Λ(n)·n^{ε·c}·n^{−s}`. -/
theorem weightFamily_primeWeights (c : ℂ) (ε : ℝ) {s : ℂ} (hs : 1 < (s - (ε : ℂ) * c).re) :
    -logDeriv (weightFamily c ε) s =
      LSeries (fun n => (Λ n : ℂ) * (n : ℂ) ^ ((ε : ℂ) * c)) s := by
  have h : logDeriv (weightFamily c ε) s = logDeriv riemannZeta (s - (ε : ℂ) * c) := by
    rw [logDeriv_apply, logDeriv_apply]
    change deriv (fun s => riemannZeta (s - (ε : ℂ) * c)) s / _ = _
    rw [deriv_comp_sub_const]
    rfl
  rw [h]
  exact negLogDeriv_zeta_complex_shift _ hs

/-- **Réponse des coefficients** : la dérivée en `ε = 0` du poids de `n` est `Λ(n)·log n·c`. -/
theorem weightFamily_weight_response (c : ℂ) {n : ℕ} (hn : n ≠ 0) :
    HasDerivAt (fun ε : ℝ => (Λ n : ℂ) * (n : ℂ) ^ ((ε : ℂ) * c))
      ((Λ n : ℂ) * (Complex.log n * c)) 0 := by
  have h1 : HasDerivAt (fun w : ℂ => w * c) c ((0 : ℝ) : ℂ) := by
    simpa using (hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const c
  have h2 := h1.const_cpow (c := (n : ℂ)) (Or.inl (Nat.cast_ne_zero.mpr hn))
  have h3 := (h2.const_mul (Λ n : ℂ)).comp_ofReal
  convert h3 using 1
  simp

/-- **Module des coefficients** : `‖Λ(n)·n^{ε·c}‖ = Λ(n)·n^{ε·Re c}`. -/
theorem weightFamily_weight_norm (c : ℂ) (ε : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ‖(Λ n : ℂ) * (n : ℂ) ^ ((ε : ℂ) * c)‖ = Λ n * (n : ℝ) ^ (ε * c.re) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg, Complex.re_ofReal_mul]

/-- **Réponse de chaque membre** : dans `Z_ε`, le membre `ρ` devient `ρ + ε·c`. Position radiale
`β + ε·Re c`, hauteur `T + ε·Im c` : réponse radiale `Re c`, réponse de hauteur `Im c`, pour tout
membre, quelle que soit sa position radiale. -/
theorem weightFamily_member_response (c : ℂ) (z : TrueZero) :
    (∀ ε : ℝ, weightFamily c ε (zeroPoint z + (ε : ℂ) * c) = 0) ∧
    (∀ ε : ℝ, (zeroPoint z + (ε : ℂ) * c).re = rZeroRadialPosition z.1 + ε * c.re) ∧
    (∀ ε : ℝ, (zeroPoint z + (ε : ℂ) * c).im = rZeroHeight z.1 + ε * c.im) ∧
    HasDerivAt (fun ε : ℝ => (zeroPoint z + (ε : ℂ) * c).re) c.re 0 ∧
    HasDerivAt (fun ε : ℝ => (zeroPoint z + (ε : ℂ) * c).im) c.im 0 := by
  have hre : ∀ ε : ℝ, (zeroPoint z + (ε : ℂ) * c).re = rZeroRadialPosition z.1 + ε * c.re := by
    intro ε
    simp [zeroPoint_re]
  have him : ∀ ε : ℝ, (zeroPoint z + (ε : ℂ) * c).im = rZeroHeight z.1 + ε * c.im := by
    intro ε
    simp [zeroPoint_im]
  refine ⟨fun ε => ?_, hre, him, ?_, ?_⟩
  · unfold weightFamily
    rw [add_sub_cancel_right]
    exact z.1.2.1
  · rw [funext hre]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c.re).const_add (rZeroRadialPosition z.1)
  · rw [funext him]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c.im).const_add (rZeroHeight z.1)

/-- **Ce qui annule la réponse radiale dans cette famille** : `Re c = 0` ⟺ le module de chaque
coefficient premier reste `Λ(n)`. -/
theorem weightFamily_radial_zero_iff_weight_modulus (c : ℂ) :
    c.re = 0 ↔ ∀ (ε : ℝ) (n : ℕ), ‖(Λ n : ℂ) * (n : ℂ) ^ ((ε : ℂ) * c)‖ = Λ n := by
  constructor
  · intro hc ε n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [weightFamily_weight_norm c ε hn, hc, mul_zero, Real.rpow_zero, mul_one]
  · intro h
    have h2 := h 1 2
    rw [weightFamily_weight_norm c 1 (by norm_num), one_mul,
      vonMangoldt_apply_prime Nat.prime_two] at h2
    have hlog : (0 : ℝ) < Real.log ((2 : ℕ) : ℝ) := Real.log_pos (by norm_num)
    have hpow : ((2 : ℕ) : ℝ) ^ c.re = 1 := by
      have := mul_left_cancel₀ hlog.ne' (h2.trans (mul_one _).symm)
      exact this
    rw [Real.rpow_def_of_pos (by norm_num), Real.exp_eq_one_iff] at hpow
    rcases mul_eq_zero.mp hpow with h0 | h0
    · exact absurd h0 hlog.ne'
    · exact h0

/-- **La direction verticale conserve la réflexion par rapport à la ligne** : si `Z_ε` de direction
`c = i` s'annule en un point `s` dont l'antécédent est dans la bande, elle s'annule au point
réfléchi `1 − s̄`. -/
theorem vertical_direction_keeps_reflection (ε : ℝ) {s : ℂ}
    (h0 : 0 < (s - (ε : ℂ) * I).re) (h1 : (s - (ε : ℂ) * I).re < 1)
    (hs : weightFamily I ε s = 0) :
    weightFamily I ε (1 - (starRingEnd ℂ) s) = 0 := by
  unfold weightFamily at hs ⊢
  set w : ℂ := s - (ε : ℂ) * I with hw
  have harg : 1 - (starRingEnd ℂ) s - (ε : ℂ) * I = 1 - (starRingEnd ℂ) w := by
    rw [hw]
    simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [harg]
  have hre : 0 < (1 - (starRingEnd ℂ) w).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have hc : completedRiemannZeta w = 0 := by rw [completedZeta_eq_mul h0, hs, zero_mul]
  have hm := completedZeta_mirror h0
  rw [hc, _root_.map_zero, completedZeta_eq_mul hre] at hm
  exact (mul_eq_zero.mp hm).resolve_right (Gammaℝ_ne_zero_of_re_pos hre)

/-! ## 2. Toute direction qui conserve la réflexion : réponse radiale nulle au premier ordre -/

/-- **Réponse d'un membre simple en ligne à une direction réelle sur la ligne.** `Ξ` est réelle sur
la ligne, dérivable au point `ρ = 1/2 + iT`, de dérivée non nulle (membre simple) ; `Φ` est
dérivable en `ρ` et réelle en `ρ` ; `γ` est une courbe dérivable de zéros de `Ξ + ε·Φ` avec
`γ(0) = ρ`. Alors `Ξ'(ρ)` est imaginaire pure, la réponse radiale `Re γ'(0)` est nulle et la
réponse de hauteur vérifie `Im γ'(0)·Im Ξ'(ρ) = Φ(ρ)`. -/
theorem reflection_direction_response {Ξ Φ : ℂ → ℂ} {T : ℝ} {Ξ' Φ' γ' : ℂ} {γ : ℝ → ℂ}
    (hΞ : HasDerivAt Ξ Ξ' ((1 / 2 : ℂ) + I * (T : ℂ)))
    (hreal : ∀ t : ℝ, (Ξ ((1 / 2 : ℂ) + I * (t : ℂ))).im = 0)
    (hsimple : Ξ' ≠ 0)
    (hΦ : HasDerivAt Φ Φ' ((1 / 2 : ℂ) + I * (T : ℂ)))
    (hΦreal : (Φ ((1 / 2 : ℂ) + I * (T : ℂ))).im = 0)
    (hγ0 : γ 0 = (1 / 2 : ℂ) + I * (T : ℂ)) (hγ : HasDerivAt γ γ' 0)
    (hzero : ∀ᶠ ε : ℝ in 𝓝 0, Ξ (γ ε) + (ε : ℂ) * Φ (γ ε) = 0) :
    Ξ'.re = 0 ∧ γ'.re = 0 ∧ γ'.im * Ξ'.im = (Φ ((1 / 2 : ℂ) + I * (T : ℂ))).re := by
  have hline : HasDerivAt (fun t : ℝ => (1 / 2 : ℂ) + I * (t : ℂ)) I T := by
    simpa using (((hasDerivAt_id T).ofReal_comp).const_mul I).const_add (1 / 2 : ℂ)
  have hF : HasDerivAt (fun t : ℝ => Ξ ((1 / 2 : ℂ) + I * (t : ℂ))) (Ξ' * I) T :=
    HasDerivAt.comp T hΞ hline
  have hFim : HasDerivAt (fun t : ℝ => (Ξ ((1 / 2 : ℂ) + I * (t : ℂ))).im) (Ξ' * I).im T :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt T hF
  have hconst : HasDerivAt (fun t : ℝ => (Ξ ((1 / 2 : ℂ) + I * (t : ℂ))).im) 0 T := by
    simp only [hreal]
    exact hasDerivAt_const T 0
  have hΞre : Ξ'.re = 0 := by
    have := hFim.unique hconst
    simpa using this
  have hΞ0 : HasDerivAt Ξ Ξ' (γ 0) := by rw [hγ0]; exact hΞ
  have hΦ0 : HasDerivAt Φ Φ' (γ 0) := by rw [hγ0]; exact hΦ
  have hΞγ : HasDerivAt (fun ε : ℝ => Ξ (γ ε)) (Ξ' * γ') 0 := HasDerivAt.comp 0 hΞ0 hγ
  have hΦγ : HasDerivAt (fun ε : ℝ => Φ (γ ε)) (Φ' * γ') 0 := HasDerivAt.comp 0 hΦ0 hγ
  have hid : HasDerivAt (fun ε : ℝ => (ε : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hsum := hΞγ.add (hid.mul hΦγ)
  have hzero' : HasDerivAt (fun ε : ℝ => Ξ (γ ε) + (ε : ℂ) * Φ (γ ε)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hzero
  have heq := hsum.unique hzero'
  simp only [Complex.ofReal_zero, zero_mul, add_zero, one_mul, hγ0] at heq
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  simp only [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im, hΞre, hΦreal,
    Complex.zero_re, Complex.zero_im, zero_mul, add_zero, zero_sub, zero_add] at hre him
  have hΞim : Ξ'.im ≠ 0 := fun h => hsimple (Complex.ext hΞre h)
  refine ⟨hΞre, ?_, by linarith⟩
  rcases mul_eq_zero.mp him with h | h
  · exact absurd h hΞim
  · exact h

/-- **Appliqué à zêta** : pour un membre engagé simple, toute direction réelle au point donne une
réponse radiale nulle au premier ordre ; seule la hauteur répond. -/
theorem engaged_member_reflection_response (z : TrueZero)
    (hOn : rZeroRadialPosition z.1 = 1 / 2)
    (hsimple : deriv completedRiemannZeta (zeroPoint z) ≠ 0)
    {Φ : ℂ → ℂ} {Φ' γ' : ℂ} {γ : ℝ → ℂ}
    (hΦ : HasDerivAt Φ Φ' (zeroPoint z)) (hΦreal : (Φ (zeroPoint z)).im = 0)
    (hγ0 : γ 0 = zeroPoint z) (hγ : HasDerivAt γ γ' 0)
    (hzero : ∀ᶠ ε : ℝ in 𝓝 0, completedRiemannZeta (γ ε) + (ε : ℂ) * Φ (γ ε) = 0) :
    γ'.re = 0 ∧
      γ'.im * (deriv completedRiemannZeta (zeroPoint z)).im = (Φ (zeroPoint z)).re := by
  have hpt : zeroPoint z = (1 / 2 : ℂ) + I * ((rZeroHeight z.1 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [zeroPoint_re, hOn]
    · simp [zeroPoint_im]
  have h1 : zeroPoint z ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [zeroPoint_re, hOn] at this
    norm_num at this
  have hd : HasDerivAt completedRiemannZeta (deriv completedRiemannZeta (zeroPoint z))
      (zeroPoint z) := (differentiableAt_completedZeta (zeroPoint_ne_zero z) h1).hasDerivAt
  have hreal : ∀ t : ℝ, (completedRiemannZeta ((1 / 2 : ℂ) + I * (t : ℂ))).im = 0 := by
    intro t
    rw [← linePoint_eq]
    exact completedZeta_real_onLine t
  rw [hpt] at hd hΦ hΦreal hγ0
  have h := reflection_direction_response hd hreal (by rw [← hpt]; exact hsimple) hΦ hΦreal hγ0
    hγ hzero
  rw [← hpt] at h
  exact ⟨h.2.1, h.2.2⟩

/-! ## 3. Contrôle : la fonction fixe sans premiers -/

/-- Le membre en ligne du témoin est simple : dérivée `(2465/128)·i` au point `1/2 + i`. -/
theorem regimeWitness_hasDerivAt_line :
    HasDerivAt regimeWitness ((2465 / 128 : ℂ) * I) ((1 / 2 : ℂ) + I * ((1 : ℝ) : ℂ)) := by
  set ρ : ℂ := (1 / 2 : ℂ) + I * ((1 : ℝ) : ℂ) with hρ
  have hρ' : ρ = 1 / 2 + I := by rw [hρ]; simp
  obtain ⟨Q, hQ⟩ : ∃ Q : ℂ → ℂ, Q = fun s =>
      (s - (1 / 2 - I)) * ((((s - 1 / 2) - 1 / 4) ^ 2 + 4) * (((s - 1 / 2) + 1 / 4) ^ 2 + 4)) :=
    ⟨_, rfl⟩
  have hfac : regimeWitness = fun s => (s - ρ) * Q s := by
    funext s
    rw [hρ', hQ]
    unfold regimeWitness
    linear_combination
      ((((s - 1 / 2) - 1 / 4) ^ 2 + 4) * (((s - 1 / 2) + 1 / 4) ^ 2 + 4)) * Complex.I_sq
  have hQd : DifferentiableAt ℂ Q ρ := by
    rw [hQ]
    fun_prop
  have hprod := ((hasDerivAt_id ρ).sub_const ρ).mul hQd.hasDerivAt
  have hval : Q ρ = (2465 / 128 : ℂ) * I := by
    rw [hQ, hρ']
    beta_reduce
    linear_combination (I * (2 * I ^ 2 + 55 / 4)) * Complex.I_sq
  rw [hfac]
  exact hprod.congr_deriv (by simp [hval])

/-- **Le contrôle répond comme zêta.** Pour le membre en ligne de la fonction fixe sans premiers
(dont le membre suivant est une paire de jumeaux), toute direction réelle au point donne une
réponse radiale nulle au premier ordre. L'annulation ne lit donc aucun poids premier. -/
theorem regimeWitness_reflection_response {Φ : ℂ → ℂ} {Φ' γ' : ℂ} {γ : ℝ → ℂ}
    (hΦ : HasDerivAt Φ Φ' ((1 / 2 : ℂ) + I * ((1 : ℝ) : ℂ)))
    (hΦreal : (Φ ((1 / 2 : ℂ) + I * ((1 : ℝ) : ℂ))).im = 0)
    (hγ0 : γ 0 = (1 / 2 : ℂ) + I * ((1 : ℝ) : ℂ)) (hγ : HasDerivAt γ γ' 0)
    (hzero : ∀ᶠ ε : ℝ in 𝓝 0, regimeWitness (γ ε) + (ε : ℂ) * Φ (γ ε) = 0) :
    γ'.re = 0 ∧ γ'.im * (2465 / 128) = (Φ ((1 / 2 : ℂ) + I * ((1 : ℝ) : ℂ))).re := by
  have hreal : ∀ t : ℝ, (regimeWitness ((1 / 2 : ℂ) + I * (t : ℂ))).im = 0 := by
    intro t
    rw [mul_comm]
    exact regimeWitness_real_onLine t
  have hne : (2465 / 128 : ℂ) * I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have h := reflection_direction_response regimeWitness_hasDerivAt_line hreal hne hΦ hΦreal hγ0
    hγ hzero
  refine ⟨h.2.1, ?_⟩
  have h2 := h.2.2
  have him : ((2465 / 128 : ℂ) * I).im = 2465 / 128 := by
    rw [Complex.mul_im]
    norm_num
  rw [him] at h2
  exact h2

#print axioms weightFamily_zero
#print axioms weightFamily_primeWeights
#print axioms weightFamily_weight_response
#print axioms weightFamily_weight_norm
#print axioms weightFamily_member_response
#print axioms weightFamily_radial_zero_iff_weight_modulus
#print axioms vertical_direction_keeps_reflection
#print axioms reflection_direction_response
#print axioms engaged_member_reflection_response
#print axioms regimeWitness_hasDerivAt_line
#print axioms regimeWitness_reflection_response

end RHV6Fresh
