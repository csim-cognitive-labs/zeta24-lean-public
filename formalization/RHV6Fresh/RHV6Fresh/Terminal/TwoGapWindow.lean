/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import RHV6Fresh.Terminal.GlobalGapSignature
import RHV6Fresh.Terminal.RaccordDetector

/-!
# RHV6Fresh — fenêtre de deux écarts : déformation de paire, charge, déterminant, battements (mission E231–E238, 2026-10-13)

Identités exactes sur la fenêtre canonique `a → e → l → b` (paire miroir centrale `1/2 ± d + iT`, trois premiers
consécutifs `p < q < r`, deux écarts). Toutes valent pour toute profondeur `d` ; aucune n'exclut la paire. Elles disent
exactement ce que chaque lecture voit :

* **Déformation additive de la paire sur un écart** (§1) : intégrande du canal de Chebyshev de la paire (avec conjugués)
  `−2 Re(x^{ρ₊−1} + x^{ρ₋−1}) = −4 x^{−1/2} cos(T log x) cosh(d log x)` (`pair_integrand_re`) ; déformation par rapport au
  témoin `d = 0` : `D_d = G_d − G_0` (`gapPairDeformation_eq_sub`), paire en `d` (`gapPairDeformation_even`), nulle en `0`,
  de signe OPPOSÉ à celui de `cos(T log x)` sur tout sous-intervalle entre deux annulations de ce cosinus
  (`gapPairDeformation_nonpos_of_cos_nonneg`, `_nonneg_of_cos_nonpos`, strict pour `d ≠ 0`, `1 ≤ a < b` :
  `gapPairDeformation_neg_of_cos_pos`). Le signe est fixé par la PHASE (hauteur), jamais par l'arithmétique de l'écart.
* **Charge** (§2) : `log(q²/(pr)) ≠ 0` pour trois premiers distincts (factorisation unique, `windowChargeLog_ne_zero`,
  depuis `fibre_charge_eq_one_iff`) ; `d·log(q²/(pr)) = 0 ⟺ d = 0` (`windowCharge_log_eq_zero_iff`). La charge est
  une LECTURE de `d` ; aucune identité de la base ne la fixe.
* **Déterminant de deux écarts** (§3) : `det M = Δ_s(p,q)Δ_t(q,r) − Δ_t(p,q)Δ_s(q,r)` nul pour `s = t`
  (`twoGapDet_self`), antisymétrique par l'échange des deux membres (`twoGapDet_swap`), alors que la lecture de la
  formule explicite (somme des colonnes, multiplicités égales dans une paire miroir) est invariante par cet échange
  (`twoGap_reading_swap_blind`) : la lecture arithmétique d'une fibre ne voit pas le signe du déterminant.
* **Battements** (§4) : battement des deux membres miroirs d'exposant `x` (module `‖x^ρ‖‖x^{1−ρ̄}‖ = x`) pour toute
  profondeur (`mirror_beat_modulus`) ; somme des modules de la paire `2√x cosh(d log x)` (`pair_modulus_sum`), paire en `d`.
* **Gram eulérien** (§5) : toute somme `Σ w_n ‖f_n‖²` à poids `w_n ≥ 0` est positive (`weighted_gram_nonneg`) ; les poids
  du monde témoin `Λ(n)(n^δ + n^{−δ})` sont positifs (`shiftedWorld_weight_ge`) : la positivité eulérienne ne sépare pas.

Aucun `sorry`, aucun `admit`, aucun axiome, aucune hypothèse de ligne.
-/

namespace RHV6Fresh

open Real

/-! ## 1. Déformation additive d'une paire miroir sur un écart -/

/-- Signal de Chebyshev d'une paire miroir `1/2 ± d + iT` (avec conjugués) sur `[a, b]`. -/
noncomputable def gapPairSignal (d T a b : ℝ) : ℝ :=
  -4 * ∫ x in a..b, x ^ (-(1 / 2 : ℝ)) * Real.cos (T * Real.log x) * Real.cosh (d * Real.log x)

/-- Déformation de la paire par rapport au témoin radial nul `d = 0` (comparaison analytique, pas deux zéros). -/
noncomputable def gapPairDeformation (d T a b : ℝ) : ℝ :=
  -4 * ∫ x in a..b, x ^ (-(1 / 2 : ℝ)) * Real.cos (T * Real.log x) * (Real.cosh (d * Real.log x) - 1)

/-- **Intégrande de la paire** : `−2 Re(x^{ρ₊−1} + x^{ρ₋−1}) = −4 x^{−1/2} cos(T log x) cosh(d log x)`. -/
theorem pair_integrand_re {x : ℝ} (hx : 0 < x) (d T : ℝ) :
    -2 * (((x : ℂ) ^ (((1 / 2 + d : ℝ) : ℂ) + T * Complex.I - 1)).re +
        ((x : ℂ) ^ (((1 / 2 - d : ℝ) : ℂ) + T * Complex.I - 1)).re) =
      -4 * (x ^ (-(1 / 2 : ℝ)) * Real.cos (T * Real.log x) * Real.cosh (d * Real.log x)) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le,
    Complex.exp_re, Complex.exp_re, Real.rpow_def_of_pos hx, Real.cosh_eq]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
  set L := Real.log x
  have h1 : Real.exp (L * (1 / 2 + d + (T * 0 - 0 * 1) - 1) - 0 * (0 + (T * 1 + 0 * 0) - 0)) =
      Real.exp (L * (-(1 / 2))) * Real.exp (d * L) := by rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (L * (1 / 2 - d + (T * 0 - 0 * 1) - 1) - 0 * (0 + (T * 1 + 0 * 0) - 0)) =
      Real.exp (L * (-(1 / 2))) * Real.exp (-(d * L)) := by rw [← Real.exp_add]; congr 1; ring
  have h3 : L * (0 + (T * 1 + 0 * 0) - 0) + 0 * (1 / 2 + d + (T * 0 - 0 * 1) - 1) = T * L := by ring
  have h4 : L * (0 + (T * 1 + 0 * 0) - 0) + 0 * (1 / 2 - d + (T * 0 - 0 * 1) - 1) = T * L := by ring
  rw [h1, h2, h3, h4]
  ring

private theorem pair_integrand_continuousOn {d T a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * Real.cos (T * Real.log x) * (Real.cosh (d * Real.log x) - c))
      (Set.uIcc a b) := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (lt_min ha hb) hx.1
  apply ContinuousAt.continuousWithinAt
  have hl : ContinuousAt Real.log x := Real.continuousAt_log hx0.ne'
  have hc1 : ContinuousAt (fun x : ℝ => Real.cos (T * Real.log x)) x :=
    Real.continuous_cos.continuousAt.comp (continuousAt_const.mul hl)
  have hc2 : ContinuousAt (fun x : ℝ => Real.cosh (d * Real.log x)) x :=
    Real.continuous_cosh.continuousAt.comp (continuousAt_const.mul hl)
  exact ((Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne')).mul hc1).mul (hc2.sub continuousAt_const)

/-- **Déformation = signal − témoin** : `D_d(a, b) = G_d(a, b) − G_0(a, b)`. -/
theorem gapPairDeformation_eq_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (d T : ℝ) :
    gapPairDeformation d T a b = gapPairSignal d T a b - gapPairSignal 0 T a b := by
  unfold gapPairDeformation gapPairSignal
  have hi1 := (pair_integrand_continuousOn (d := d) (T := T) ha hb 0).intervalIntegrable (μ := MeasureTheory.volume)
  have hi2 := (pair_integrand_continuousOn (d := 0) (T := T) ha hb 0).intervalIntegrable (μ := MeasureTheory.volume)
  simp only [sub_zero] at hi1 hi2
  rw [← mul_sub, ← intervalIntegral.integral_sub hi1 hi2]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only [zero_mul, Real.cosh_zero]
  ring

/-- **Paire en la profondeur** : la déformation ne voit que `|d|`. -/
theorem gapPairDeformation_even (d T a b : ℝ) :
    gapPairDeformation (-d) T a b = gapPairDeformation d T a b := by
  unfold gapPairDeformation
  simp only [neg_mul, Real.cosh_neg]

theorem gapPairDeformation_zero (T a b : ℝ) : gapPairDeformation 0 T a b = 0 := by
  unfold gapPairDeformation
  simp

/-- **Signe fixé par la phase** : là où `cos(T log x) ≥ 0`, la déformation est `≤ 0`. -/
theorem gapPairDeformation_nonpos_of_cos_nonneg {d T a b : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hcos : ∀ x ∈ Set.Icc a b, 0 ≤ Real.cos (T * Real.log x)) : gapPairDeformation d T a b ≤ 0 := by
  unfold gapPairDeformation
  have h : 0 ≤ ∫ x in a..b, x ^ (-(1 / 2 : ℝ)) * Real.cos (T * Real.log x) * (Real.cosh (d * Real.log x) - 1) := by
    apply intervalIntegral.integral_nonneg hab
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (hcos x hx))
      (sub_nonneg.mpr (Real.one_le_cosh _))
  linarith

/-- Là où `cos(T log x) ≤ 0`, la déformation est `≥ 0`. -/
theorem gapPairDeformation_nonneg_of_cos_nonpos {d T a b : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hcos : ∀ x ∈ Set.Icc a b, Real.cos (T * Real.log x) ≤ 0) : 0 ≤ gapPairDeformation d T a b := by
  unfold gapPairDeformation
  have h : 0 ≤ ∫ x in a..b, -(x ^ (-(1 / 2 : ℝ)) * Real.cos (T * Real.log x) *
      (Real.cosh (d * Real.log x) - 1)) := by
    apply intervalIntegral.integral_nonneg hab
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have := mul_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le (-(1 / 2 : ℝ))) (neg_nonneg.mpr (hcos x hx)))
      (sub_nonneg.mpr (Real.one_le_cosh (d * Real.log x)))
    linarith [this]
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- **Strict** : pour `d ≠ 0`, `1 ≤ a < b` et `cos(T log x) > 0` sur `]a, b[`, la déformation est `< 0`. -/
theorem gapPairDeformation_neg_of_cos_pos {d T a b : ℝ} (hd : d ≠ 0) (hab : a < b) (ha : 1 ≤ a)
    (hcos : ∀ x ∈ Set.Ioo a b, 0 < Real.cos (T * Real.log x)) : gapPairDeformation d T a b < 0 := by
  unfold gapPairDeformation
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hi := (pair_integrand_continuousOn (d := d) (T := T) ha0 hb0 1).intervalIntegrable (μ := MeasureTheory.volume)
  have h : 0 < ∫ x in a..b, x ^ (-(1 / 2 : ℝ)) * Real.cos (T * Real.log x) * (Real.cosh (d * Real.log x) - 1) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hi _ hab
    intro x hx
    have hx1 : 1 < x := lt_of_le_of_lt ha hx.1
    have hl : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    have hch : 1 < Real.cosh (d * Real.log x) := Real.one_lt_cosh.mpr (mul_ne_zero hd hl)
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by linarith) _) (hcos x hx)) (by linarith)
  linarith

/-! ## 2. Charge : `log(q²/(pr)) ≠ 0` pour trois premiers distincts -/

theorem windowChargeLog_ne_zero {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p ≠ q) (hqr : q ≠ r) :
    Real.log ((q : ℝ) ^ 2 / ((p : ℝ) * (r : ℝ))) ≠ 0 := by
  have hpos : 0 < (q : ℝ) ^ 2 / ((p : ℝ) * (r : ℝ)) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have : (0 : ℝ) < r := by exact_mod_cast hr.pos
    positivity
  have hne : (q : ℝ) ^ 2 / ((p : ℝ) * (r : ℝ)) ≠ 1 := by
    intro h1
    have := (fibre_charge_eq_one_iff hp hq hr hpq hqr 1).mp (by rw [Real.rpow_one]; exact h1)
    exact one_ne_zero this
  intro h
  rcases Real.log_eq_zero.mp h with h0 | h1 | hm
  · exact hpos.ne' h0
  · exact hne h1
  · linarith

/-- **La charge est nulle exactement à profondeur nulle.** -/
theorem windowCharge_log_eq_zero_iff {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p ≠ q)
    (hqr : q ≠ r) (d : ℝ) : d * Real.log ((q : ℝ) ^ 2 / ((p : ℝ) * (r : ℝ))) = 0 ↔ d = 0 := by
  rw [mul_eq_zero]
  exact ⟨fun h => h.resolve_right (windowChargeLog_ne_zero hp hq hr hpq hqr), Or.inl⟩

/-! ## 3. Déterminant de deux écarts -/

/-- Déterminant de la matrice des variations de deux signatures `s`, `t` sur les écarts `[p, q]`, `[q, r]`. -/
noncomputable def twoGapDet (s t : ℂ) (p q r : ℝ) : ℂ :=
  signatureGap s p q * signatureGap t q r - signatureGap t p q * signatureGap s q r

theorem twoGapDet_self (s : ℂ) (p q r : ℝ) : twoGapDet s s p q r = 0 := by
  unfold twoGapDet; ring

/-- **Antisymétrie** : échanger les deux membres de la paire (`d ↦ −d`) change le signe du déterminant. -/
theorem twoGapDet_swap (s t : ℂ) (p q r : ℝ) : twoGapDet t s p q r = -twoGapDet s t p q r := by
  unfold twoGapDet; ring

/-- **La lecture de la formule explicite ne voit pas le signe du déterminant** : la somme des colonnes (multiplicités
égales) sur chacun des deux écarts est invariante par l'échange des deux membres, le déterminant change de signe. -/
theorem twoGap_reading_swap_blind (s t : ℂ) (p q r : ℝ) :
    (signatureGap t p q + signatureGap s p q = signatureGap s p q + signatureGap t p q ∧
      signatureGap t q r + signatureGap s q r = signatureGap s q r + signatureGap t q r) ∧
      twoGapDet t s p q r = -twoGapDet s t p q r :=
  ⟨⟨add_comm _ _, add_comm _ _⟩, twoGapDet_swap s t p q r⟩

/-! ## 4. Battements -/

/-- **Battement miroir** : `‖x^ρ‖ · ‖x^{1 − ρ̄}‖ = x` pour toute profondeur : l'exposant radial du battement des deux
membres d'une paire miroir est `1`, aveugle à `d`. -/
theorem mirror_beat_modulus {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖(x : ℂ) ^ s‖ * ‖(x : ℂ) ^ (1 - (starRingEnd ℂ) s)‖ = x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← Real.rpow_add hx]
  simp

/-- **Somme des modules de la paire** : `‖x^{1/2+d+iT}‖ + ‖x^{1/2−d+iT}‖ = 2√x cosh(d log x)`, paire en `d`. -/
theorem pair_modulus_sum {x : ℝ} (hx : 0 < x) (d T : ℝ) :
    ‖(x : ℂ) ^ (((1 / 2 + d : ℝ) : ℂ) + T * Complex.I)‖ + ‖(x : ℂ) ^ (((1 / 2 - d : ℝ) : ℂ) + T * Complex.I)‖ =
      2 * x ^ (1 / 2 : ℝ) * Real.cosh (d * Real.log x) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero]
  rw [Real.rpow_add hx, Real.rpow_sub hx, Real.cosh_eq, Real.rpow_def_of_pos hx d, Real.exp_neg,
    mul_comm (Real.log x) d]
  field_simp

/-! ## 5. Gram eulérien à poids positifs -/

/-- **Positivité de Gram** : pour tous poids `w_n ≥ 0`, `Σ w_n ‖f_n‖² ≥ 0`. Vraie pour `Λ` comme pour les poids du monde
témoin `Λ(n)(n^δ + n^{−δ}) ≥ 0` (`shiftedWorld_weight_ge`) : elle ne lit aucune position radiale. -/
theorem weighted_gram_nonneg (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (f : ℕ → ℂ) (N : ℕ) :
    0 ≤ ∑ n ∈ Finset.range N, w n * ‖f n‖ ^ 2 :=
  Finset.sum_nonneg fun n _ => mul_nonneg (hw n) (sq_nonneg _)

end RHV6Fresh
