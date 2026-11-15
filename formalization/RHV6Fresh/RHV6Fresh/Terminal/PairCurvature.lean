/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RegimeWindow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# RHV6Fresh — la paire miroir contre le double en ligne : courbure radiale et horizon de lecture (E159, auteur, 2026-10-03)

Suite de E158 (la lecture côté premier est paire en la profondeur). Référence imposée par l'auteur : la paire
`1/2 ± d + iT` n'est pas comparée à « rien », mais au double membre en ligne `1/2 + iT` de même hauteur, configuration
que le certificat global de zeta23 ne sépare pas de la paire serrée.

* **Atome de séparation** (§1) : sur tout réel `q > 0`, la paire moins le double vaut le terme en ligne multiplié par la
  courbure radiale réelle `2(cosh(d log q) − 1)` (`pairOverDouble_eq`), de module `√q · 2(cosh(d log q) − 1)`
  (`norm_pairOverDouble`) ; cette courbure est `≥ (d log q)²`, nulle ⟺ `d log q = 0` (`radialCurvature_ge_sq`,
  `radialCurvature_eq_zero_iff`) : le premier ordre est absent, le second est présent et minoré.
* **Lecture à horizon fini** (§2) : toute lecture linéaire côté premier, à coefficients quelconques, portée par des
  entiers `1 ≤ n ≤ X`, sépare la paire du double d'au plus `2(cosh(d log X) − 1)` fois la masse `Σ ‖a_n‖ √n`
  (`finite_horizon_separation_le`) ; un horizon fixé confond donc la paire et le double quand `d log X → 0`.
* **Terme de la formule explicite** (§3) : le défaut de la paire contre le double dans le terme `q^ρ/ρ` est l'atome
  divisé par le point en ligne, plus deux corrections de dénominateur (`pairDefect_decomposition`), chacune bornée par
  `|d|/T²` fois l'amplitude du membre (`inv_mirrorPoint_sub_le`, `pairDefect_sub_curvature_le`).
* **Les deux signes d'un seul paramètre** (§4) : une paire en ligne serrée `1/2 + i(T ± h)` moins le double vaut le terme
  en ligne × `2(cos(h log q) − 1)` (`lineSplitOverDouble_eq`), courbure `≤ 0` et `≥ −(h log q)²`
  (`lineSplitCurvature_bounds`) ; contre le double, la paire hors ligne lit une courbure `≥ (d log q)² ≥ 0`, la paire en
  ligne une courbure `≤ 0` (`regime_sign_of_curvature`). Le double en ligne est la frontière des deux régimes ; leur
  signe se lit au premier ordre en le carré signé de l'écart.

Borne : ce sont des identités et des inégalités sur des paires données ; elles mesurent la séparation, elles n'excluent
rien. Elles disent que la séparation d'une paire et d'un double par les premiers est une courbure d'ordre `(d log X)²`,
donc qu'une loi qui exclurait toute paire serrée doit lire les premiers jusqu'à un horizon `log X` de l'ordre de
`1/d`, sans borne uniforme. Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Real

/-! ## 1. Atome de séparation : la courbure radiale -/

/-- **Courbure radiale** d'une paire de profondeur `d` lue au réel `q` : `2(cosh(d log q) − 1)`. -/
noncomputable def radialCurvature (q d : ℝ) : ℝ := 2 * (Real.cosh (d * Real.log q) - 1)

/-- **La paire moins le double en ligne**, sans dénominateur. -/
noncomputable def pairOverDouble (q T d : ℝ) : ℂ :=
  (q : ℂ) ^ mirrorPoint T d + (q : ℂ) ^ mirrorPoint T (-d) - 2 * (q : ℂ) ^ mirrorPoint T 0

theorem mirrorPoint_eq_add (T d : ℝ) : mirrorPoint T d = mirrorPoint T 0 + (d : ℂ) := by
  unfold mirrorPoint; push_cast; ring

private theorem ofReal_cpow_ofReal_eq_exp {q : ℝ} (hq : 0 < q) (d : ℝ) :
    (q : ℂ) ^ (d : ℂ) = ((Real.exp (d * Real.log q) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_cpow hq.le, Real.rpow_def_of_pos hq, mul_comm]

/-- **Atome** : paire − double = terme en ligne × courbure radiale réelle. -/
theorem pairOverDouble_eq {q : ℝ} (hq : 0 < q) (T d : ℝ) :
    pairOverDouble q T d = (q : ℂ) ^ mirrorPoint T 0 * (radialCurvature q d : ℂ) := by
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq.ne'
  unfold pairOverDouble radialCurvature
  rw [mirrorPoint_eq_add T d, mirrorPoint_eq_add T (-d), Complex.cpow_add _ _ hq0,
    Complex.cpow_add _ _ hq0, show ((-d : ℝ) : ℂ) = ((-d : ℝ) : ℂ) from rfl,
    ofReal_cpow_ofReal_eq_exp hq, ofReal_cpow_ofReal_eq_exp hq, Real.cosh_eq]
  push_cast
  rw [show -(d : ℂ) * (Real.log q : ℂ) = -((d : ℂ) * (Real.log q : ℂ)) by ring]
  ring

theorem radialCurvature_nonneg (q d : ℝ) : 0 ≤ radialCurvature q d := by
  unfold radialCurvature; linarith [Real.one_le_cosh (d * Real.log q)]

/-- **Module de l'atome** : `√q · 2(cosh(d log q) − 1)`. -/
theorem norm_pairOverDouble {q : ℝ} (hq : 0 < q) (T d : ℝ) :
    ‖pairOverDouble q T d‖ = q ^ (1 / 2 : ℝ) * radialCurvature q d := by
  rw [pairOverDouble_eq hq, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.norm_real,
    Real.norm_of_nonneg (radialCurvature_nonneg q d)]
  simp [mirrorPoint]

/-- `2(cosh x − 1) = 4 sinh²(x/2)`. -/
private theorem two_cosh_sub_one (x : ℝ) : 2 * (Real.cosh x - 1) = 4 * Real.sinh (x / 2) ^ 2 := by
  have h := Real.cosh_two_mul (x / 2)
  have h1 := Real.cosh_sq_sub_sinh_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  nlinarith

private theorem sq_le_sinh_sq (y : ℝ) : y ^ 2 ≤ Real.sinh y ^ 2 := by
  rcases le_total 0 y with hy | hy
  · have := Real.self_le_sinh_iff.2 hy
    nlinarith
  · have h := Real.self_le_sinh_iff.2 (neg_nonneg.2 hy)
    rw [Real.sinh_neg] at h
    nlinarith

/-- **Le second ordre est présent et minoré** : la courbure radiale est au moins `(d log q)²`. -/
theorem radialCurvature_ge_sq (q d : ℝ) : (d * Real.log q) ^ 2 ≤ radialCurvature q d := by
  unfold radialCurvature
  rw [two_cosh_sub_one]
  have := sq_le_sinh_sq (d * Real.log q / 2)
  nlinarith

/-- **Courbure nulle ⟺ `d log q = 0`** : la paire ne se confond avec le double, au réel `q > 1`, qu'en ligne. -/
theorem radialCurvature_eq_zero_iff (q d : ℝ) : radialCurvature q d = 0 ↔ d * Real.log q = 0 := by
  constructor
  · intro h
    have := radialCurvature_ge_sq q d
    rw [h] at this
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
  · intro h
    unfold radialCurvature
    rw [h, Real.cosh_zero]; ring

/-- **La courbure croît avec l'horizon** : pour `1 ≤ q ≤ X`, `radialCurvature q d ≤ radialCurvature X d`. -/
theorem radialCurvature_mono {q X : ℝ} (hq : 1 ≤ q) (hqX : q ≤ X) (d : ℝ) :
    radialCurvature q d ≤ radialCurvature X d := by
  unfold radialCurvature
  have hl0 : 0 ≤ Real.log q := Real.log_nonneg hq
  have hl : Real.log q ≤ Real.log X := Real.log_le_log (by linarith) hqX
  have : Real.cosh (d * Real.log q) ≤ Real.cosh (d * Real.log X) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg hl0, abs_of_nonneg (hl0.trans hl)]
    exact mul_le_mul_of_nonneg_left hl (abs_nonneg d)
  linarith

/-! ## 2. Lecture côté premier à horizon fini -/

/-- **Lecture linéaire de la paire** par des coefficients `a_n` sur un ensemble fini d'entiers. -/
noncomputable def pairReadout (S : Finset ℕ) (a : ℕ → ℂ) (T d : ℝ) : ℂ :=
  ∑ n ∈ S, a n * (((n : ℝ) : ℂ) ^ mirrorPoint T d + ((n : ℝ) : ℂ) ^ mirrorPoint T (-d))

/-- **Lecture linéaire du double en ligne**, mêmes coefficients. -/
noncomputable def doubleReadout (S : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) : ℂ :=
  ∑ n ∈ S, a n * (2 * ((n : ℝ) : ℂ) ^ mirrorPoint T 0)

/-- **Séparation à horizon fini** : toute lecture linéaire portée par `1 ≤ n ≤ X` sépare la paire du double d'au plus
`2(cosh(d log X) − 1) · Σ ‖a_n‖ √n`. -/
theorem finite_horizon_separation_le (S : Finset ℕ) (a : ℕ → ℂ) (T d X : ℝ)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ (n : ℝ) ≤ X) :
    ‖pairReadout S a T d - doubleReadout S a T‖ ≤
      radialCurvature X d * ∑ n ∈ S, ‖a n‖ * (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hdiff : pairReadout S a T d - doubleReadout S a T =
      ∑ n ∈ S, a n * pairOverDouble (n : ℝ) T d := by
    unfold pairReadout doubleReadout pairOverDouble
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [hdiff, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  obtain ⟨h1, hX⟩ := hS n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
  have hpos : (0 : ℝ) < n := by linarith
  rw [norm_mul, norm_pairOverDouble hpos]
  have hc := radialCurvature_mono hn1 hX d
  have hr : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hpos.le _
  have ha := norm_nonneg (a n)
  have hcn := radialCurvature_nonneg (n : ℝ) d
  calc ‖a n‖ * ((n : ℝ) ^ (1 / 2 : ℝ) * radialCurvature (n : ℝ) d)
      ≤ ‖a n‖ * ((n : ℝ) ^ (1 / 2 : ℝ) * radialCurvature X d) := by gcongr
    _ = radialCurvature X d * (‖a n‖ * (n : ℝ) ^ (1 / 2 : ℝ)) := by ring

/-! ## 3. Le terme de la formule explicite : courbure plus corrections de dénominateur -/

/-- **Défaut de la paire contre le double en ligne** dans le terme `q^ρ/ρ` de la formule explicite. -/
noncomputable def pairDefect (q T d : ℝ) : ℂ :=
  mirrorPairTerm q T d - 2 * (q : ℂ) ^ mirrorPoint T 0 / mirrorPoint T 0

theorem pairDefect_zero (q T : ℝ) : pairDefect q T 0 = 0 := by
  unfold pairDefect mirrorPairTerm; rw [neg_zero]; ring

theorem pairDefect_even (q T d : ℝ) : pairDefect q T (-d) = pairDefect q T d := by
  unfold pairDefect; rw [mirrorPairTerm_even]

/-- **Décomposition exacte** : atome / point en ligne + deux corrections de dénominateur. -/
theorem pairDefect_decomposition (q T d : ℝ) :
    pairDefect q T d = pairOverDouble q T d / mirrorPoint T 0 +
      (q : ℂ) ^ mirrorPoint T d * ((mirrorPoint T d)⁻¹ - (mirrorPoint T 0)⁻¹) +
      (q : ℂ) ^ mirrorPoint T (-d) * ((mirrorPoint T (-d))⁻¹ - (mirrorPoint T 0)⁻¹) := by
  unfold pairDefect mirrorPairTerm pairOverDouble
  simp only [div_eq_mul_inv]
  ring

theorem norm_mirrorPoint_ge (T d : ℝ) : |T| ≤ ‖mirrorPoint T d‖ := by
  have := Complex.abs_im_le_norm (mirrorPoint T d)
  simpa [mirrorPoint] using this

/-- **Correction de dénominateur** : `‖1/(1/2 + d + iT) − 1/(1/2 + iT)‖ ≤ |d|/T²`. -/
theorem inv_mirrorPoint_sub_le {T : ℝ} (hT : T ≠ 0) (d : ℝ) :
    ‖(mirrorPoint T d)⁻¹ - (mirrorPoint T 0)⁻¹‖ ≤ |d| / T ^ 2 := by
  have hT' : 0 < |T| := abs_pos.2 hT
  have hx := norm_mirrorPoint_ge T d
  have hz := norm_mirrorPoint_ge T 0
  have hx0 : mirrorPoint T d ≠ 0 := norm_pos_iff.1 (hT'.trans_le hx)
  have hz0 : mirrorPoint T 0 ≠ 0 := norm_pos_iff.1 (hT'.trans_le hz)
  have hdiff : (mirrorPoint T d)⁻¹ - (mirrorPoint T 0)⁻¹ =
      -(d : ℂ) / (mirrorPoint T d * mirrorPoint T 0) := by
    rw [inv_sub_inv hx0 hz0, mirrorPoint_eq_add T d]; ring
  rw [hdiff, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_mul]
  have hprod : T ^ 2 ≤ ‖mirrorPoint T d‖ * ‖mirrorPoint T 0‖ := by
    rw [← sq_abs, sq]; exact mul_le_mul hx hz (abs_nonneg _) (norm_nonneg _)
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hprod

/-- **Le défaut est la courbure, aux corrections de dénominateur près** :
`‖Δ − atome/point‖ ≤ (q^{1/2+d} + q^{1/2−d}) · |d|/T²`. -/
theorem pairDefect_sub_curvature_le {q T : ℝ} (hq : 0 < q) (hT : T ≠ 0) (d : ℝ) :
    ‖pairDefect q T d - pairOverDouble q T d / mirrorPoint T 0‖ ≤
      (q ^ (1 / 2 + d) + q ^ (1 / 2 - d)) * (|d| / T ^ 2) := by
  rw [pairDefect_decomposition, add_assoc, add_sub_cancel_left]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq,
    Complex.norm_cpow_eq_rpow_re_of_pos hq]
  have h1 := inv_mirrorPoint_sub_le hT d
  have h2 := inv_mirrorPoint_sub_le hT (-d)
  rw [abs_neg] at h2
  have e1 : (mirrorPoint T d).re = 1 / 2 + d := by simp [mirrorPoint]
  have e2 : (mirrorPoint T (-d)).re = 1 / 2 - d := by simp [mirrorPoint]; ring
  rw [e1, e2, add_mul]
  gcongr

#print axioms pairOverDouble_eq
#print axioms norm_pairOverDouble
#print axioms radialCurvature_ge_sq
#print axioms radialCurvature_eq_zero_iff
#print axioms radialCurvature_mono
#print axioms finite_horizon_separation_le
#print axioms pairDefect_zero
#print axioms pairDefect_even
#print axioms pairDefect_decomposition
#print axioms inv_mirrorPoint_sub_le
#print axioms pairDefect_sub_curvature_le

/-! ## 4. Les deux signes d'un seul paramètre : paire hors ligne, double en ligne, paire en ligne serrée -/

/-- **Courbure le long de la ligne** d'une paire en ligne `1/2 + i(T ± h)` lue au réel `q` : `2(cos(h log q) − 1)`. -/
noncomputable def lineSplitCurvature (q h : ℝ) : ℝ := 2 * (Real.cos (h * Real.log q) - 1)

/-- **La paire en ligne serrée moins le double en ligne**, sans dénominateur. -/
noncomputable def lineSplitOverDouble (q T h : ℝ) : ℂ :=
  (q : ℂ) ^ mirrorPoint (T + h) 0 + (q : ℂ) ^ mirrorPoint (T - h) 0 - 2 * (q : ℂ) ^ mirrorPoint T 0

/-- **Atome le long de la ligne** : paire en ligne − double = terme en ligne × `2(cos(h log q) − 1)`. -/
theorem lineSplitOverDouble_eq {q : ℝ} (hq : 0 < q) (T h : ℝ) :
    lineSplitOverDouble q T h = (q : ℂ) ^ mirrorPoint T 0 * (lineSplitCurvature q h : ℂ) := by
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq.ne'
  have e1 : mirrorPoint (T + h) 0 = mirrorPoint T 0 + (h : ℂ) * Complex.I := by
    unfold mirrorPoint; push_cast; ring
  have e2 : mirrorPoint (T - h) 0 = mirrorPoint T 0 + (-(h : ℂ)) * Complex.I := by
    unfold mirrorPoint; push_cast; ring
  have ex : ∀ z : ℂ, (q : ℂ) ^ z = Complex.exp (Real.log q * z) := fun z => by
    rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.ofReal_log hq.le]
  unfold lineSplitOverDouble lineSplitCurvature
  rw [e1, e2, Complex.cpow_add _ _ hq0, Complex.cpow_add _ _ hq0, ex ((h : ℂ) * Complex.I),
    ex (-(h : ℂ) * Complex.I)]
  push_cast
  have hc := Complex.two_cos ((h : ℂ) * (Real.log q : ℂ))
  rw [show (Real.log q : ℂ) * ((h : ℂ) * Complex.I) = (h : ℂ) * (Real.log q : ℂ) * Complex.I by ring,
    show (Real.log q : ℂ) * (-(h : ℂ) * Complex.I) = -((h : ℂ) * (Real.log q : ℂ)) * Complex.I by ring]
  linear_combination -((q : ℂ) ^ mirrorPoint T 0) * hc

/-- **Signe opposé** : la courbure le long de la ligne est `≤ 0`, entre `−(h log q)²` et `0`. -/
theorem lineSplitCurvature_bounds (q h : ℝ) :
    -(h * Real.log q) ^ 2 ≤ lineSplitCurvature q h ∧ lineSplitCurvature q h ≤ 0 := by
  unfold lineSplitCurvature
  have h1 := Real.one_sub_sq_div_two_le_cos (x := h * Real.log q)
  have h2 := Real.cos_le_one (h * Real.log q)
  constructor <;> nlinarith

/-- **Le régime est le signe de la courbure lue contre le double** : une paire hors ligne de profondeur `d` lit une
courbure `≥ 0`, une paire en ligne d'écart de hauteur `h` une courbure `≤ 0`, au même ordre `(· log q)²`. -/
theorem regime_sign_of_curvature (q d h : ℝ) :
    (d * Real.log q) ^ 2 ≤ radialCurvature q d ∧ lineSplitCurvature q h ≤ 0 ∧
      -(h * Real.log q) ^ 2 ≤ lineSplitCurvature q h :=
  ⟨radialCurvature_ge_sq q d, (lineSplitCurvature_bounds q h).2, (lineSplitCurvature_bounds q h).1⟩

#print axioms lineSplitOverDouble_eq
#print axioms lineSplitCurvature_bounds
#print axioms regime_sign_of_curvature

end RHV6Fresh
