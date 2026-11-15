/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.JointParameterReading

/-!
# Relations individuelles amplitude–phase, normalisation, incréments de `li` (auteur, 2026-10-11 ; E199)

Identités et bornes INDIVIDUELLES, vraies pour toute position radiale ; la spécialisation ON est énoncée sous l'hypothèse
explicite `β = 1/2`. Aucune ne porte sur une somme de contributions ; aucune ne change le but de la transmission.

* §1 forme polaire : `2·Re(w·e^{(β+iT)u}) = 2‖w‖e^{βu} cos(Tu + arg w)` (instance : terme lissé, `w = −m/(ρ(ρ+1))`).
* §2 incrément général de `v(u) = −A(u) cos(Tu + α)` : part de phase + terme de variation d'enveloppe ; bornes.
* §3 forme en produit de sinus ; spécialisation ON (amplitude normalisée constante, `β = 1/2` en hypothèse).
* §4 correction de normalisation `t = √x·v` : `Δt = √b·Δv + (√b − √a)·v(a)`.
* §5 incrément de `li` entre deux abscisses `2 ≤ a ≤ b` : `(b − a)/log b ≤ ∫_a^b dt/log t ≤ (b − a)/log a`.
-/

namespace RHV6Fresh

open RHV3Lean Real

/-! ## 1. Forme polaire d'une contribution conjuguée-regroupée -/

/-- **Forme polaire** : `Re(w·e^{iθ}) = ‖w‖ cos(θ + arg w)`. -/
theorem re_mul_exp_I (w : ℂ) (θ : ℝ) :
    (w * Complex.exp (θ * Complex.I)).re = ‖w‖ * Real.cos (θ + Complex.arg w) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
  rw [mul_assoc, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, add_comm]

/-- **Amplitude–phase d'une contribution** : `2·Re(w·e^{(β + iT)u}) = 2‖w‖ e^{βu} cos(Tu + arg w)`. -/
theorem pair_amplitude_phase (w : ℂ) (β T u : ℝ) :
    2 * (w * Complex.exp ((β + T * Complex.I) * u)).re =
      2 * ‖w‖ * Real.exp (β * u) * Real.cos (T * u + Complex.arg w) := by
  have h : (β + T * Complex.I) * (u : ℂ) = ((β * u : ℝ) : ℂ) + ((T * u : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_add, ← Complex.ofReal_exp, mul_left_comm w, Complex.re_ofReal_mul, re_mul_exp_I]
  ring

/-! ## 2. Incrément général -/

/-- **Incrément général** de `v(u) = −A(u) cos(Tu + α)` : part de phase à amplitude gelée + variation d'enveloppe. -/
theorem increment_split (A : ℝ → ℝ) (T α a b : ℝ) :
    (-A b * Real.cos (T * b + α)) - (-A a * Real.cos (T * a + α)) =
      -A a * (Real.cos (T * b + α) - Real.cos (T * a + α)) - (A b - A a) * Real.cos (T * b + α) := by
  ring

/-- **Bornes de l'incrément** aux deux extrémités : `|Δv| ≤ |A(a)|·min(2, |T|·|b − a|) + |A(b) − A(a)|`. -/
theorem increment_abs_le (A : ℝ → ℝ) (T α a b : ℝ) :
    |(-A b * Real.cos (T * b + α)) - (-A a * Real.cos (T * a + α))| ≤
        |A a| * (|T| * |b - a|) + |A b - A a| ∧
      |(-A b * Real.cos (T * b + α)) - (-A a * Real.cos (T * a + α))| ≤ |A a| * 2 + |A b - A a| := by
  rw [increment_split]
  have hcos : |Real.cos (T * b + α)| ≤ 1 := Real.abs_cos_le_one _
  have hlip : |Real.cos (T * b + α) - Real.cos (T * a + α)| ≤ |T| * |b - a| := by
    calc _ ≤ |(T * b + α) - (T * a + α)| := Real.abs_cos_sub_cos_le _ _
      _ = |T| * |b - a| := by rw [show (T * b + α) - (T * a + α) = T * (b - a) by ring, abs_mul]
  have h2 : |Real.cos (T * b + α) - Real.cos (T * a + α)| ≤ 2 := by
    calc _ ≤ |Real.cos (T * b + α)| + |Real.cos (T * a + α)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
      _ = 2 := by norm_num
  have key : ∀ c : ℝ, |Real.cos (T * b + α) - Real.cos (T * a + α)| ≤ c →
      |-A a * (Real.cos (T * b + α) - Real.cos (T * a + α)) - (A b - A a) * Real.cos (T * b + α)| ≤
        |A a| * c + |A b - A a| := by
    intro c hc
    calc _ ≤ |-A a * (Real.cos (T * b + α) - Real.cos (T * a + α))| + |(A b - A a) * Real.cos (T * b + α)| :=
          abs_sub _ _
      _ = |A a| * |Real.cos (T * b + α) - Real.cos (T * a + α)| + |A b - A a| * |Real.cos (T * b + α)| := by
          rw [abs_mul, abs_mul, abs_neg]
      _ ≤ |A a| * c + |A b - A a| * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hc (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hcos (abs_nonneg _))
      _ = _ := by ring
  exact ⟨key _ hlip, key _ h2⟩

/-! ## 3. Produit de sinus ; spécialisation ON (conditionnelle) -/

/-- **Produit de sinus** : `cos(Tb + α) − cos(Ta + α) = −2 sin(T(a + b)/2 + α) sin(T(b − a)/2)`. -/
theorem cos_increment_sines (T α a b : ℝ) :
    Real.cos (T * b + α) - Real.cos (T * a + α) =
      -2 * Real.sin (T * (a + b) / 2 + α) * Real.sin (T * (b - a) / 2) := by
  rw [Real.cos_sub_cos]
  have h1 : (T * b + α + (T * a + α)) / 2 = T * (a + b) / 2 + α := by ring
  have h2 : (T * b + α - (T * a + α)) / 2 = T * (b - a) / 2 := by ring
  rw [h1, h2]

/-- **Spécialisation ON, sous l'hypothèse `β = 1/2`** : la contribution normalisée par `e^{u/2}` a une amplitude
constante `2‖w‖` ; son incrément n'a pas de terme d'enveloppe et prend la forme en produit de sinus. -/
theorem onLine_normalized_increment (w : ℂ) {β : ℝ} (hβ : β = 1 / 2) (T a b : ℝ) :
    (Real.exp (-(b / 2)) * (2 * (w * Complex.exp ((β + T * Complex.I) * b)).re)) -
        (Real.exp (-(a / 2)) * (2 * (w * Complex.exp ((β + T * Complex.I) * a)).re)) =
      2 * ‖w‖ * (-2 * Real.sin (T * (a + b) / 2 + Complex.arg w) * Real.sin (T * (b - a) / 2)) := by
  have hE : ∀ u : ℝ, Real.exp (-(u / 2)) * Real.exp (β * u) = 1 := by
    intro u; rw [← Real.exp_add, hβ, show -(u / 2) + 1 / 2 * u = 0 by ring, Real.exp_zero]
  rw [pair_amplitude_phase, pair_amplitude_phase, ← cos_increment_sines]
  have hb := hE b; have ha := hE a
  calc _ = 2 * ‖w‖ * (Real.exp (-(b / 2)) * Real.exp (β * b)) * Real.cos (T * b + Complex.arg w) -
        2 * ‖w‖ * (Real.exp (-(a / 2)) * Real.exp (β * a)) * Real.cos (T * a + Complex.arg w) := by ring
    _ = _ := by rw [hb, ha]; ring

/-! ## 4. Correction de normalisation -/

/-- **Incrément brut contre incrément normalisé** : avec `t(x) = √x·v(x)`,
`t(b) − t(a) = √b·(v(b) − v(a)) + (√b − √a)·v(a)`. -/
theorem normalization_correction (v : ℝ → ℝ) (a b : ℝ) :
    Real.sqrt b * v b - Real.sqrt a * v a =
      Real.sqrt b * (v b - v a) + (Real.sqrt b - Real.sqrt a) * v a := by
  ring

/-! ## 5. Incrément de `li` entre deux abscisses -/

/-- **Encadrement de l'incrément de `li`** (canal de comptage) : pour `2 ≤ a ≤ b`,
`(b − a)/log b ≤ ∫_a^b dt/log t ≤ (b − a)/log a`. -/
theorem logIntegral_increment_bounds {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (b - a) / Real.log b ≤ ∫ t in a..b, 1 / Real.log t ∧
      ∫ t in a..b, 1 / Real.log t ≤ (b - a) / Real.log a := by
  have hb : 2 ≤ b := le_trans ha hab
  have hint := inv_log_intervalIntegrable ha hb
  have hloga : 0 < Real.log a := Real.log_pos (by linarith)
  have hmono : ∀ t ∈ Set.Icc a b, 1 / Real.log b ≤ 1 / Real.log t ∧ 1 / Real.log t ≤ 1 / Real.log a := by
    rintro t ⟨hat, htb⟩
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    exact ⟨one_div_le_one_div_of_le hlogt (Real.log_le_log (by linarith) htb),
      one_div_le_one_div_of_le hloga (Real.log_le_log (by linarith) hat)⟩
  constructor
  · have := intervalIntegral.integral_mono_on hab intervalIntegrable_const hint fun t ht => (hmono t ht).1
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    rwa [div_eq_mul_one_div]
  · have := intervalIntegral.integral_mono_on hab hint intervalIntegrable_const fun t ht => (hmono t ht).2
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    rwa [div_eq_mul_one_div]

/-- **Instance entre deux premiers consécutifs** : `(p_{n+1} − p_n)/log p_{n+1} ≤ Δli_n ≤ (p_{n+1} − p_n)/log p_n`. -/
theorem logIntegral_prime_step_bounds (n : ℕ) :
    ((fnPrimeAtRank (n + 1) : ℝ) - fnPrimeAtRank n) / Real.log (fnPrimeAtRank (n + 1)) ≤
        ∫ t in (fnPrimeAtRank n : ℝ)..(fnPrimeAtRank (n + 1) : ℝ), 1 / Real.log t ∧
      ∫ t in (fnPrimeAtRank n : ℝ)..(fnPrimeAtRank (n + 1) : ℝ), 1 / Real.log t ≤
        ((fnPrimeAtRank (n + 1) : ℝ) - fnPrimeAtRank n) / Real.log (fnPrimeAtRank n) := by
  have h2 : (2 : ℝ) ≤ fnPrimeAtRank n := by exact_mod_cast (thm_primeAtRank_isPrime n).two_le
  have hle : (fnPrimeAtRank n : ℝ) ≤ fnPrimeAtRank (n + 1) := by
    exact_mod_cast (thm_primeAtRank_strictMono (Nat.lt_succ_self n)).le
  exact logIntegral_increment_bounds h2 hle

end RHV6Fresh
