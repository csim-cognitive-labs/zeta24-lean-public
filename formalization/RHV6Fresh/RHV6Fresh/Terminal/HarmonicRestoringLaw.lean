/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GlobalGapSignature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# RHV6Fresh — modèle harmonique exact des Tours (mission E224–E230, 2026-10-13)

En coordonnée logarithmique `t = log x`, le terme `x^ρ` d'un zéro `ρ = β + iT`, ramené à l'échelle critique `√x`, vaut
`e^{(ρ − 1/2)t} = e^{dt}·e^{iTt}`, `d = β − 1/2` : une oscillation de fréquence `T` (hauteur) sous une enveloppe `e^{dt}`
(position radiale). Résultats (axiomes standard, aucune hypothèse de ligne) :

1. **Mode réel** `y(t) = e^{dt} cos(Tt − φ)` et son compagnon `z(t) = e^{dt} sin(Tt − φ)` : `y' = d y − T z`,
   `z' = d z + T y` (`harmonicMode_hasDerivAt`, `harmonicCompanion_hasDerivAt`).
2. **Équation du second ordre** `y'' − 2d y' + (T² + d²) y = 0` (`harmonicMode_ode`) : oscillation pure (`d = 0`), amplifiée
   (`d > 0`), amortie (`d < 0`). Identité vraie pour TOUT `(d, T, φ)`.
3. **Énergie adaptée** `E = ½((y' − d y)² + T² y²) = (T²/2) e^{2dt}` (`harmonicEnergy_eq`), `E' = 2d E`
   (`harmonicEnergy_hasDerivAt`) ; à `T ≠ 0`, énergie stationnaire en un point ⟺ `d = 0` (`harmonicEnergy_flat_iff`).
4. **Paire miroir** (exponentielles normalisées, sans les dénominateurs `1/ρ`) : somme `2 cosh(dt) e^{iTt}`, différence
   `2 sinh(dt) e^{iTt}` (`mirrorMode_add`, `mirrorMode_sub`) ; module de la somme `2 cosh(dt) ≥ 2`, égal à `2` en un `t ≠ 0`
   ⟺ `d = 0` (`mirrorMode_add_norm`, `mirrorMode_add_norm_eq_two_iff`) ; un mode est borné sur toute la droite ⟺ `d = 0`
   (`complexMode_bounded_iff`, `zero_mode_bounded_iff_radialFactor`).
5. **Lecture sur un vrai zéro** : `x^ρ/√x = e^{(ρ − 1/2) log x}` (`zeroTerm_normalized_mode`) ; énergie du mode d'un zéro
   stationnaire ⟺ `radialFactor = 1` (`harmonicEnergy_flat_iff_radialFactor`) : CARACTÉRISATION ; le mode de tout zéro
   satisfait sa propre équation quelle que soit sa partie réelle (`zero_mode_ode_all_beta`).
6. **Contre-modèle de l'équation fonctionnelle** : `Λ(s − δ)Λ(s + δ)` vérifie `F(1 − s) = F(s)` (`shiftedCompleted_one_sub`)
   et s'annule en `ρ ± δ` dès que `Λ(ρ) = 0` (`shiftedCompleted_zero_shift`) : la symétrie fonctionnelle seule n'impose pas
   `d = 0`.

Aucune de ces identités ne contraint `d` : l'énergie harmonique DÉTECTE le déplacement radial, elle ne l'interdit pas. Sa
conservation n'est jamais posée. Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Mode réel et compagnon -/

/-- Mode réel `y(t) = e^{dt} cos(Tt − φ)`. -/
noncomputable def harmonicMode (d T φ t : ℝ) : ℝ := Real.exp (d * t) * Real.cos (T * t - φ)

/-- Compagnon `z(t) = e^{dt} sin(Tt − φ)`. -/
noncomputable def harmonicCompanion (d T φ t : ℝ) : ℝ := Real.exp (d * t) * Real.sin (T * t - φ)

theorem harmonicMode_hasDerivAt (d T φ t : ℝ) :
    HasDerivAt (harmonicMode d T φ) (d * harmonicMode d T φ t - T * harmonicCompanion d T φ t) t := by
  have h1 : HasDerivAt (fun t => Real.exp (d * t)) (Real.exp (d * t) * d) t := by
    simpa using ((hasDerivAt_id t).const_mul d).exp
  have h2 : HasDerivAt (fun t => Real.cos (T * t - φ)) (-Real.sin (T * t - φ) * T) t := by
    simpa using (((hasDerivAt_id t).const_mul T).sub_const φ).cos
  exact (h1.mul h2).congr_deriv (by unfold harmonicMode harmonicCompanion; ring)

theorem harmonicCompanion_hasDerivAt (d T φ t : ℝ) :
    HasDerivAt (harmonicCompanion d T φ) (d * harmonicCompanion d T φ t + T * harmonicMode d T φ t) t := by
  have h1 : HasDerivAt (fun t => Real.exp (d * t)) (Real.exp (d * t) * d) t := by
    simpa using ((hasDerivAt_id t).const_mul d).exp
  have h2 : HasDerivAt (fun t => Real.sin (T * t - φ)) (Real.cos (T * t - φ) * T) t := by
    simpa using (((hasDerivAt_id t).const_mul T).sub_const φ).sin
  exact (h1.mul h2).congr_deriv (by unfold harmonicMode harmonicCompanion; ring)

theorem harmonicMode_deriv (d T φ : ℝ) :
    deriv (harmonicMode d T φ) = fun t => d * harmonicMode d T φ t - T * harmonicCompanion d T φ t :=
  funext fun t => (harmonicMode_hasDerivAt d T φ t).deriv

/-! ## 2. Équation du second ordre -/

/-- **Équation harmonique exacte** : `y'' − 2d y' + (T² + d²) y = 0`, pour tout `(d, T, φ)`. -/
theorem harmonicMode_ode (d T φ t : ℝ) :
    deriv (deriv (harmonicMode d T φ)) t - 2 * d * deriv (harmonicMode d T φ) t
      + (T ^ 2 + d ^ 2) * harmonicMode d T φ t = 0 := by
  have hd2 : HasDerivAt (fun t => d * harmonicMode d T φ t - T * harmonicCompanion d T φ t)
      (d * (d * harmonicMode d T φ t - T * harmonicCompanion d T φ t)
        - T * (d * harmonicCompanion d T φ t + T * harmonicMode d T φ t)) t :=
    ((harmonicMode_hasDerivAt d T φ t).const_mul d).sub ((harmonicCompanion_hasDerivAt d T φ t).const_mul T)
  rw [harmonicMode_deriv, hd2.deriv]
  ring

/-- Oscillation pure sur la ligne : `y'' + T² y = 0`. -/
theorem harmonicMode_ode_onLine (T φ t : ℝ) :
    deriv (deriv (harmonicMode 0 T φ)) t + T ^ 2 * harmonicMode 0 T φ t = 0 := by
  have h := harmonicMode_ode 0 T φ t
  simpa using h

/-! ## 3. Énergie adaptée -/

/-- Énergie adaptée `E = ½((y' − d y)² + T² y²)`. -/
noncomputable def harmonicEnergy (d T φ t : ℝ) : ℝ :=
  (1 / 2) * ((deriv (harmonicMode d T φ) t - d * harmonicMode d T φ t) ^ 2 + T ^ 2 * harmonicMode d T φ t ^ 2)

/-- **Énergie exacte** : `E(t) = (T²/2) e^{2dt}`, quelle que soit la phase. -/
theorem harmonicEnergy_eq (d T φ t : ℝ) : harmonicEnergy d T φ t = T ^ 2 / 2 * Real.exp (2 * d * t) := by
  unfold harmonicEnergy
  rw [harmonicMode_deriv]
  simp only [harmonicMode, harmonicCompanion]
  have hexp : Real.exp (2 * d * t) = Real.exp (d * t) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [hexp]
  have hsc := Real.sin_sq_add_cos_sq (T * t - φ)
  linear_combination (T ^ 2 / 2 * Real.exp (d * t) ^ 2) * hsc

/-- **Taux exact** : `E' = 2d E`. -/
theorem harmonicEnergy_hasDerivAt (d T φ t : ℝ) :
    HasDerivAt (harmonicEnergy d T φ) (2 * d * harmonicEnergy d T φ t) t := by
  have hfun : harmonicEnergy d T φ = fun t => T ^ 2 / 2 * Real.exp (2 * d * t) :=
    funext fun t => harmonicEnergy_eq d T φ t
  rw [hfun]
  have h : HasDerivAt (fun t => Real.exp (2 * d * t)) (Real.exp (2 * d * t) * (2 * d)) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * d)).exp
  exact (h.const_mul (T ^ 2 / 2)).congr_deriv (by ring)

/-- **Détecteur exact** : à `T ≠ 0`, l'énergie est stationnaire en un point si et seulement si `d = 0`. -/
theorem harmonicEnergy_flat_iff (d T φ t : ℝ) (hT : T ≠ 0) :
    deriv (harmonicEnergy d T φ) t = 0 ↔ d = 0 := by
  rw [(harmonicEnergy_hasDerivAt d T φ t).deriv, harmonicEnergy_eq]
  have hE : 0 < T ^ 2 / 2 * Real.exp (2 * d * t) := by positivity
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · linarith
    · exact absurd h' (ne_of_gt hE)
  · intro h; simp [h]

/-- Énergie croissante au-dessus de la ligne, décroissante en dessous, en tout point. -/
theorem harmonicEnergy_deriv_sign (d T φ t : ℝ) (hT : T ≠ 0) :
    (0 < deriv (harmonicEnergy d T φ) t ↔ 0 < d) ∧ (deriv (harmonicEnergy d T φ) t < 0 ↔ d < 0) := by
  rw [(harmonicEnergy_hasDerivAt d T φ t).deriv, harmonicEnergy_eq]
  have hE : 0 < T ^ 2 / 2 * Real.exp (2 * d * t) := by positivity
  constructor
  · constructor
    · intro h; nlinarith
    · intro h; positivity
  · constructor
    · intro h; nlinarith
    · intro h; nlinarith

/-! ## 4. Paire miroir (exponentielles normalisées) -/

/-- Mode complexe normalisé `v(t) = e^{dt} e^{iTt}`. -/
noncomputable def complexMode (d T t : ℝ) : ℂ := Complex.exp (((d : ℂ) + (T : ℂ) * Complex.I) * t)

theorem complexMode_eq (d T t : ℝ) :
    complexMode d T t = (Real.exp (d * t) : ℂ) * Complex.exp ((T * t : ℝ) * Complex.I) := by
  unfold complexMode
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem complexMode_norm (d T t : ℝ) : ‖complexMode d T t‖ = Real.exp (d * t) := by
  rw [complexMode_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

/-- **Somme miroir** : `v₊ + v₋ = 2 cosh(dt) e^{iTt}`. -/
theorem mirrorMode_add (d T t : ℝ) :
    complexMode d T t + complexMode (-d) T t = 2 * (Real.cosh (d * t) : ℂ) * complexMode 0 T t := by
  rw [complexMode_eq, complexMode_eq, complexMode_eq, Complex.ofReal_cosh, Complex.cosh]
  push_cast
  rw [neg_mul, zero_mul, Complex.exp_zero, one_mul]
  ring

/-- **Différence miroir** : `v₊ − v₋ = 2 sinh(dt) e^{iTt}`. -/
theorem mirrorMode_sub (d T t : ℝ) :
    complexMode d T t - complexMode (-d) T t = 2 * (Real.sinh (d * t) : ℂ) * complexMode 0 T t := by
  rw [complexMode_eq, complexMode_eq, complexMode_eq, Complex.ofReal_sinh, Complex.sinh]
  push_cast
  rw [neg_mul, zero_mul, Complex.exp_zero, one_mul]
  ring

/-- Module de la somme miroir : `2 cosh(dt)`. -/
theorem mirrorMode_add_norm (d T t : ℝ) :
    ‖complexMode d T t + complexMode (-d) T t‖ = 2 * Real.cosh (d * t) := by
  rw [mirrorMode_add, norm_mul, norm_mul, complexMode_norm, zero_mul, Real.exp_zero, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.cosh_pos _).le]
  norm_num

/-- La somme miroir n'est jamais sous l'échelle `2` ; elle vaut `2` en un `t ≠ 0` si et seulement si `d = 0`. -/
theorem mirrorMode_add_norm_eq_two_iff (d T t : ℝ) (ht : t ≠ 0) :
    ‖complexMode d T t + complexMode (-d) T t‖ = 2 ↔ d = 0 := by
  rw [mirrorMode_add_norm]
  constructor
  · intro h
    have hc : Real.cosh (d * t) = 1 := by linarith
    by_contra hd
    have := Real.one_lt_cosh.mpr (mul_ne_zero hd ht)
    linarith
  · intro h; simp [h]

theorem mirrorMode_add_norm_ge (d T t : ℝ) : 2 ≤ ‖complexMode d T t + complexMode (-d) T t‖ := by
  rw [mirrorMode_add_norm]; linarith [Real.one_le_cosh (d * t)]

/-- **Stabilité d'un mode** : le mode complexe est borné sur toute la droite (`t → ±∞`) si et seulement si `d = 0`. Un mode
amplifié diverge en `+∞`, un mode amorti en `−∞` (c'est-à-dire en `x → 0⁺`). -/
theorem complexMode_bounded_iff (d T : ℝ) :
    (∃ C : ℝ, ∀ t : ℝ, ‖complexMode d T t‖ ≤ C) ↔ d = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hd
    have h := hC ((|C| + 1) / d)
    rw [complexMode_norm, mul_div_cancel₀ _ hd] at h
    have h2 := Real.add_one_le_exp (|C| + 1)
    have h3 := le_abs_self C
    linarith
  · rintro rfl
    exact ⟨1, fun t => by rw [complexMode_norm, zero_mul, Real.exp_zero]⟩

/-- Lecture sur un vrai zéro : le mode normalisé `x^ρ/√x` (en `t = log x`) est borné sur toute la droite si et seulement si
le facteur radial vaut `1`. CARACTÉRISATION : aucun côté n'est démontré pour un zéro donné. -/
theorem zero_mode_bounded_iff_radialFactor (z : TrueZero) :
    (∃ C : ℝ, ∀ t : ℝ, ‖complexMode (rZeroRadialPosition z.1 - 1 / 2) (rZeroHeight z.1) t‖ ≤ C) ↔
      radialFactor z = 1 := by
  rw [complexMode_bounded_iff, radialFactor_eq_one_iff, sub_eq_zero]

/-! ## 5. Lecture sur un vrai zéro -/

/-- `x^ρ/√x = e^{(ρ − 1/2) log x}` pour `x > 0` : le terme d'un zéro ramené à l'échelle critique est son mode complexe. -/
theorem zeroTerm_normalized_mode (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ zeroPoint z / ((Real.sqrt x : ℝ) : ℂ) =
      complexMode (rZeroRadialPosition z.1 - 1 / 2) (rZeroHeight z.1) (Real.log x) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_def_of_ne_zero hx', Real.sqrt_eq_rpow, Complex.ofReal_cpow hx.le, Complex.cpow_def_of_ne_zero hx',
    ← Complex.exp_sub, ← Complex.ofReal_log hx.le]
  unfold complexMode
  congr 1
  have hz : zeroPoint z = (rZeroRadialPosition z.1 : ℂ) + (rZeroHeight z.1 : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [zeroPoint_re, zeroPoint_im]
  rw [hz]; push_cast; ring

/-- Le mode réel d'un vrai zéro satisfait sa propre équation harmonique, QUELLE QUE SOIT sa partie réelle. -/
theorem zero_mode_ode_all_beta (z : TrueZero) (φ t : ℝ) :
    let d := rZeroRadialPosition z.1 - 1 / 2
    let T := rZeroHeight z.1
    deriv (deriv (harmonicMode d T φ)) t - 2 * d * deriv (harmonicMode d T φ) t
      + (T ^ 2 + d ^ 2) * harmonicMode d T φ t = 0 :=
  harmonicMode_ode _ _ φ t

/-- **Caractérisation** : l'énergie du mode d'un vrai zéro est stationnaire (en un point quelconque) si et seulement si son
facteur radial vaut `1`. Ce n'est pas une dérivation : aucun côté n'est démontré pour un zéro donné. -/
theorem harmonicEnergy_flat_iff_radialFactor (z : TrueZero) (φ t : ℝ) :
    deriv (harmonicEnergy (rZeroRadialPosition z.1 - 1 / 2) (rZeroHeight z.1) φ) t = 0 ↔ radialFactor z = 1 := by
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  rw [harmonicEnergy_flat_iff (rZeroRadialPosition z.1 - 1 / 2) (rZeroHeight z.1) φ t hT, radialFactor_eq_one_iff,
    sub_eq_zero]

/-! ## 6. Contre-modèle de l'équation fonctionnelle -/

/-- `Λ(s − δ)·Λ(s + δ)` (fonction zêta complétée de Mathlib). -/
noncomputable def shiftedCompleted (δ : ℝ) (s : ℂ) : ℂ :=
  completedRiemannZeta (s - δ) * completedRiemannZeta (s + δ)

/-- **Même équation fonctionnelle** que `Λ` : `F(1 − s) = F(s)`. -/
theorem shiftedCompleted_one_sub (δ : ℝ) (s : ℂ) : shiftedCompleted δ (1 - s) = shiftedCompleted δ s := by
  unfold shiftedCompleted
  have h1 : (1 - s) - (δ : ℂ) = 1 - (s + δ) := by ring
  have h2 : (1 - s) + (δ : ℂ) = 1 - (s - δ) := by ring
  rw [h1, h2, completedRiemannZeta_one_sub, completedRiemannZeta_one_sub, mul_comm]

/-- Tout zéro de `Λ` produit deux zéros décalés de `±δ` : avec `δ ≠ 0`, un zéro de partie réelle `1/2` donne deux zéros
hors de la ligne, symétriques par `s ↦ 1 − s̄`. -/
theorem shiftedCompleted_zero_shift (δ : ℝ) {ρ : ℂ} (hρ : completedRiemannZeta ρ = 0) :
    shiftedCompleted δ (ρ + δ) = 0 ∧ shiftedCompleted δ (ρ - δ) = 0 := by
  unfold shiftedCompleted
  constructor
  · rw [add_sub_cancel_right, hρ, zero_mul]
  · rw [sub_add_cancel, hρ, mul_zero]

end RHV6Fresh
