/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxGeneric
import RHV6Fresh.Terminal.EulerMaclaurinTenCertificate

/-!
# Certificat de `ζ` sur les côtés d'un rectangle : lemmes numériques génériques (vérification (V2))

Briques numériques réutilisées par le certificat généré (`experiments/e192_zeta_box_certificate_generator.py`) :
`e^{−iθ}` encadré pour tout `θ` réel (réduction modulo `2π`, Taylor d'ordre 12 et puissance quatrième, briques de (V1)),
puissances `n^{−p/q}`, minoration terme à terme de `Re(v·main_N(σ + it))`, majoration de la constante de reste.
Aucune valeur n'est admise : toutes les constantes sont vérifiées par `norm_num`.
-/

namespace RHV6Fresh
namespace ZB

open Complex Set

/-- `e^{−iθ}` approché à `η + 10⁻⁷ + 2·10⁻¹²` près, pour tout `θ` encadré, après réduction par `2kπ`. -/
lemma ecis_approx (θ : ℝ) (k : ℤ) (P1 P2 Q1 Q2 y0 η w1 w2 : ℝ)
    (hP : P1 ≤ 2 * k * Real.pi ∧ 2 * k * Real.pi ≤ P2) (hQ : Q1 ≤ θ ∧ θ ≤ Q2)
    (h1 : P2 - Q1 - y0 ≤ η) (h2 : y0 - (P1 - Q2) ≤ η) (hy : |y0| ≤ 4)
    (hw1 : |(EM10.tC1 (y0/4))^4 - 6*(EM10.tC1 (y0/4))^2*(EM10.tS1 (y0/4))^2 + (EM10.tS1 (y0/4))^4 - w1| ≤ 1/10^12)
    (hw2 : |4*(EM10.tC1 (y0/4))^3*EM10.tS1 (y0/4) - 4*EM10.tC1 (y0/4)*(EM10.tS1 (y0/4))^3 - w2| ≤ 1/10^12) :
    ‖exp (-((θ : ℂ) * I)) - ((w1 : ℂ) + (w2 : ℂ) * I)‖ ≤ η + 1/10^7 + 2/10^12 := by
  set y : ℝ := 2 * k * Real.pi - θ with hydef
  have hyy : |y - y0| ≤ η := by rw [abs_le]; constructor <;> linarith [hP.1, hP.2, hQ.1, hQ.2]
  have hper : exp (-((θ : ℂ) * I)) = exp ((y : ℂ) * I) := by
    have := (Complex.exp_periodic.int_mul k) (-((θ : ℂ) * I))
    rw [← this]; congr 1
    rw [hydef]; push_cast; ring
  have hLip : ‖exp ((y : ℂ) * I) - exp ((y0 : ℂ) * I)‖ ≤ η := by
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := y - y0)
    have e : exp ((y : ℂ) * I) - exp ((y0 : ℂ) * I) = exp ((y0 : ℂ) * I) * (exp (I * ((y - y0 : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, ← Complex.exp_add]; push_cast
      rw [mul_one]; congr 2; ring
    rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact h.trans (by simpa using hyy)
  have hc := EM10.cis4 y0 hy
  set M : ℂ := ((((EM10.tC1 (y0/4))^4 - 6*(EM10.tC1 (y0/4))^2*(EM10.tS1 (y0/4))^2 + (EM10.tS1 (y0/4))^4 : ℝ) : ℂ) +
      ((4*(EM10.tC1 (y0/4))^3*EM10.tS1 (y0/4) - 4*EM10.tC1 (y0/4)*(EM10.tS1 (y0/4))^3 : ℝ) : ℂ) * I) with hM
  have hr : ‖M - ((w1 : ℂ) + (w2 : ℂ) * I)‖ ≤ 2/10^12 := by
    have e : M - ((w1 : ℂ) + (w2 : ℂ) * I)
      = (((EM10.tC1 (y0/4))^4 - 6*(EM10.tC1 (y0/4))^2*(EM10.tS1 (y0/4))^2 + (EM10.tS1 (y0/4))^4 - w1 : ℝ) : ℂ) +
        ((4*(EM10.tC1 (y0/4))^3*EM10.tS1 (y0/4) - 4*EM10.tC1 (y0/4)*(EM10.tS1 (y0/4))^3 - w2 : ℝ) : ℂ) * I := by
      rw [hM]; push_cast; ring
    rw [e]
    refine (EM10.norm_ri_le _ _).trans ?_
    linarith
  rw [hper]
  have e : exp ((y : ℂ) * I) - ((w1 : ℂ) + (w2 : ℂ) * I) =
      (exp ((y : ℂ) * I) - exp ((y0 : ℂ) * I)) + (exp ((y0 : ℂ) * I) - M) + (M - ((w1 : ℂ) + (w2 : ℂ) * I)) := by ring
  rw [e]
  have t1 := norm_add_le (exp ((y : ℂ) * I) - exp ((y0 : ℂ) * I) + (exp ((y0 : ℂ) * I) - M)) (M - ((w1 : ℂ) + (w2 : ℂ) * I))
  have t2 := norm_add_le (exp ((y : ℂ) * I) - exp ((y0 : ℂ) * I)) (exp ((y0 : ℂ) * I) - M)
  linarith

/-- Puissance `n^{−σ}` minorée, `σ ≤ p/q`. -/
lemma pwq_lo (n σ : ℝ) (q p : ℕ) (hq : 0 < q) (hn : 1 ≤ n) (hσ : σ ≤ (p : ℝ) / q) (L : ℝ) (hL : 0 ≤ L)
    (h : L ^ q * n ^ p ≤ 1) : L ≤ n ^ (-σ) := by
  have hn0 : 0 ≤ n := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : n ^ (-((p : ℝ) / q)) ≤ n ^ (-σ) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  refine le_trans ?_ h1
  have hnp : 0 < n ^ p := by positivity
  have e : (n ^ (-((p : ℝ) / q))) ^ q = (n ^ p)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    have : -((p : ℝ) / q) * (q : ℝ) = -(p : ℝ) := by field_simp
    rw [this, Real.rpow_neg hn0, Real.rpow_natCast]
  have hpos : 0 ≤ n ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hn0 _
  have : L ^ q ≤ (n ^ (-((p : ℝ) / q))) ^ q := by
    rw [e, ← one_div, le_div_iff₀ hnp]; exact h
  exact (pow_le_pow_iff_left₀ hL hpos hq.ne').mp this

/-- Puissance `n^{−σ}` majorée, `p/q ≤ σ`. -/
lemma pwq_hi (n σ : ℝ) (q p : ℕ) (hq : 0 < q) (hn : 1 ≤ n) (hσ : (p : ℝ) / q ≤ σ) (U : ℝ) (hU : 0 ≤ U)
    (h : 1 ≤ U ^ q * n ^ p) : n ^ (-σ) ≤ U := by
  have hn0 : 0 ≤ n := by linarith
  have h1 : n ^ (-σ) ≤ n ^ (-((p : ℝ) / q)) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  refine le_trans h1 ?_
  have hnp : 0 < n ^ p := by positivity
  have e : (n ^ (-((p : ℝ) / q))) ^ q = (n ^ p)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    have : -((p : ℝ) / q) * (q : ℝ) = -(p : ℝ) := by field_simp
    rw [this, Real.rpow_neg hn0, Real.rpow_natCast]
  have hpos : 0 ≤ n ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hn0 _
  have : (n ^ (-((p : ℝ) / q))) ^ q ≤ U ^ q := by
    rw [e, ← one_div, div_le_iff₀ hnp]; linarith
  exact (pow_le_pow_iff_left₀ hpos hU hq.ne').mp this

/-- `e^{−s log n}` au point `σ + it`. -/
lemma ez_eval (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ) :
    ez (Real.log n) ((σ : ℂ) + (t : ℂ) * I) =
      (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * exp (-(((t * Real.log n : ℝ) : ℂ) * I)) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ez, Real.rpow_def_of_pos hpos, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- **Minoration d'un terme** `Re(v·n^{−s})`, `v = r1 + r2 i`. -/
lemma term_lb (n : ℕ) (hn : 1 ≤ n) (σ t r1 r2 : ℝ) (hr : r1 ^ 2 + r2 ^ 2 ≤ 1) (alo ahi : ℝ)
    (ha1 : alo ≤ (n : ℝ) ^ (-σ)) (ha2 : (n : ℝ) ^ (-σ) ≤ ahi) (w1 w2 ε : ℝ)
    (hW : ‖exp (-(((t * Real.log n : ℝ) : ℂ) * I)) - ((w1 : ℂ) + (w2 : ℂ) * I)‖ ≤ ε) (l : ℝ)
    (hl1 : l ≤ alo * (r1 * w1 - r2 * w2 - ε)) (hl2 : l ≤ ahi * (r1 * w1 - r2 * w2 - ε)) :
    l ≤ (((r1 : ℂ) + (r2 : ℂ) * I) * ez (Real.log n) ((σ : ℂ) + (t : ℂ) * I)).re := by
  rw [ez_eval n hn σ t]
  have hb := EM10.rot_bounds r1 r2 w1 w2 ε _ hr hW
  have e : (((r1 : ℂ) + (r2 : ℂ) * I) * ((((n : ℝ) ^ (-σ) : ℝ) : ℂ) * exp (-(((t * Real.log n : ℝ) : ℂ) * I)))).re =
      (n : ℝ) ^ (-σ) * (((r1 : ℂ) + r2 * I) * exp (-(((t * Real.log n : ℝ) : ℂ) * I))).re := by
    rw [mul_left_comm, Complex.re_ofReal_mul]
  rw [e]
  exact EM10.mul_lb _ _ _ alo ahi l (Real.rpow_nonneg (Nat.cast_nonneg n) _) ha1 ha2 hb.1 hl1 hl2

/-- Partie réelle de la partie principale, découpée. -/
lemma re_main_split (N : ℕ) (hN : 1 ≤ N) (s v : ℂ) (hs0 : s ≠ 0) :
    (v * eulerMaclaurinMain N s).re =
      (∑ n ∈ Finset.range N, (v * ez (Real.log ((n + 1 : ℕ) : ℝ)) s).re) -
        ((v * ((N : ℂ) * ez (Real.log N) s / (1 - s))).re + (v * (ez (Real.log N) s / 2)).re) := by
  rw [main_eq_ez N hN s hs0, mul_sub, mul_sub, Finset.mul_sum, Complex.sub_re, Complex.sub_re, Complex.re_sum]
  ring

lemma sum_lb_step {f : ℕ → ℝ} {n : ℕ} {A b : ℝ} (h : A ≤ ∑ k ∈ Finset.range n, f k) (h' : b ≤ f n) :
    A + b ≤ ∑ k ∈ Finset.range (n + 1), f k := by
  rw [Finset.sum_range_succ]; linarith

lemma sum_ub_step {f : ℕ → ℝ} {n : ℕ} {A b : ℝ} (h : ∑ k ∈ Finset.range n, f k ≤ A) (h' : f n ≤ b) :
    ∑ k ∈ Finset.range (n + 1), f k ≤ A + b := by
  rw [Finset.sum_range_succ]; linarith

/-- **Majoration des deux termes de queue** au point `σ + it`, `v = r1 + r2 i`. -/
lemma tail_ub (N : ℕ) (hN : 1 ≤ N) (σ t r1 r2 : ℝ) (hr : r1 ^ 2 + r2 ^ 2 ≤ 1) (alo ahi : ℝ)
    (ha1 : alo ≤ (N : ℝ) ^ (-σ)) (ha2 : (N : ℝ) ^ (-σ) ≤ ahi) (w1 w2 ε : ℝ)
    (hW : ‖exp (-(((t * Real.log N : ℝ) : ℂ) * I)) - ((w1 : ℂ) + (w2 : ℂ) * I)‖ ≤ ε)
    (D : ℝ) (hD : D = (1 - σ) ^ 2 + t ^ 2) (hD0 : 0 < D) (Gu U : ℝ)
    (hGu : (r1 * w1 - r2 * w2) * (N * (1 - σ) / D + 1 / 2) - (r1 * w2 + r2 * w1) * (N * t / D) +
        ε * (|N * (1 - σ) / D + 1 / 2| + |N * t / D|) ≤ Gu)
    (hU1 : alo * Gu ≤ U) (hU2 : ahi * Gu ≤ U) :
    (((r1 : ℂ) + (r2 : ℂ) * I) * ((N : ℂ) * ez (Real.log N) ((σ : ℂ) + (t : ℂ) * I) /
        (1 - ((σ : ℂ) + (t : ℂ) * I)))).re +
      (((r1 : ℂ) + (r2 : ℂ) * I) * (ez (Real.log N) ((σ : ℂ) + (t : ℂ) * I) / 2)).re ≤ U := by
  rw [ez_eval N hN σ t]
  set a : ℝ := (N : ℝ) ^ (-σ) with ha
  set E : ℂ := exp (-(((t * Real.log N : ℝ) : ℂ) * I)) with hE
  set v : ℂ := (r1 : ℂ) + (r2 : ℂ) * I with hv
  have hb := EM10.rot_bounds r1 r2 w1 w2 ε E hr hW
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD0.ne'
  have key : (((1 - σ : ℝ) : ℂ) + (t : ℂ) * I) * (1 - ((σ : ℂ) + (t : ℂ) * I)) = (D : ℂ) := by
    rw [hD]; push_cast; linear_combination (-(t : ℂ) ^ 2) * I_sq
  have hinv : (1 : ℂ) / (1 - ((σ : ℂ) + (t : ℂ) * I)) = (((1 - σ) / D : ℝ) : ℂ) + ((t / D : ℝ) : ℂ) * I := by
    have hw : (1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro h; rw [h, mul_zero] at key; exact hD' key.symm
    rw [div_eq_iff hw]
    have : ((((1 - σ) / D : ℝ) : ℂ) + ((t / D : ℝ) : ℂ) * I) =
        (((1 - σ : ℝ) : ℂ) + (t : ℂ) * I) / (D : ℂ) := by push_cast; ring
    rw [this, div_mul_eq_mul_div, key, div_self hD']
  set R : ℝ := (v * E).re
  set J : ℝ := (v * E).im
  have e1 : (v * ((N : ℂ) * ((a : ℂ) * E) / (1 - ((σ : ℂ) + (t : ℂ) * I)))).re + (v * ((a : ℂ) * E / 2)).re =
      a * (R * (N * (1 - σ) / D + 1 / 2) - J * (N * t / D)) := by
    have : v * ((N : ℂ) * ((a : ℂ) * E) / (1 - ((σ : ℂ) + (t : ℂ) * I))) =
        ((N * a : ℝ) : ℂ) * ((v * E) * (1 / (1 - ((σ : ℂ) + (t : ℂ) * I)))) := by push_cast; ring
    rw [this, hinv, Complex.re_ofReal_mul]
    have : v * ((a : ℂ) * E / 2) = ((a / 2 : ℝ) : ℂ) * (v * E) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
    have hri : ∀ (Z : ℂ) (p q : ℝ), (Z * ((p : ℂ) + (q : ℂ) * I)).re = Z.re * p - Z.im * q := by
      intro Z p q; simp [Complex.mul_re]
    rw [hri]
    field_simp
    ring
  rw [e1]
  have hG : R * (N * (1 - σ) / D + 1 / 2) - J * (N * t / D) ≤ Gu := by
    have hR1 := hb.1; have hR2 := hb.2.1; have hJ1 := hb.2.2.1; have hJ2 := hb.2.2.2
    have k1 : R * (N * (1 - σ) / D + 1 / 2) ≤
        (r1 * w1 - r2 * w2) * (N * (1 - σ) / D + 1 / 2) + ε * |N * (1 - σ) / D + 1 / 2| := by
      rcases le_total 0 (N * (1 - σ) / D + 1 / 2) with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_nonpos h]; nlinarith
    have k2 : -(J * (N * t / D)) ≤ -((r1 * w2 + r2 * w1) * (N * t / D)) + ε * |N * t / D| := by
      rcases le_total 0 (N * t / D) with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_nonpos h]; nlinarith
    linarith
  have ha0 : 0 ≤ a := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rcases le_total 0 Gu with h | h
  · calc a * _ ≤ a * Gu := mul_le_mul_of_nonneg_left hG ha0
      _ ≤ ahi * Gu := mul_le_mul_of_nonneg_right ha2 h
      _ ≤ U := hU2
  · calc a * _ ≤ a * Gu := mul_le_mul_of_nonneg_left hG ha0
      _ ≤ alo * Gu := mul_le_mul_of_nonpos_right ha1 h
      _ ≤ U := hU1

/-- Terme de la constante de reste, majoré. -/
lemma remTerm_ub (n : ℕ) (hn : 1 ≤ n) (σ ahi lhi : ℝ) (ha : (n : ℝ) ^ (-σ) ≤ ahi) (hl : Real.log n ≤ lhi) (b : ℝ)
    (hb : ahi * lhi ^ 2 ≤ b) :
    Real.exp (-(Real.log n * σ)) * Real.log n ^ 2 ≤ b := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have e : Real.exp (-(Real.log n * σ)) = (n : ℝ) ^ (-σ) := by rw [Real.rpow_def_of_pos hpos]; ring_nf
  rw [e]
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h2 : Real.log n ^ 2 ≤ lhi ^ 2 := pow_le_pow_left₀ hl0 hl 2
  have ha0 : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg hpos.le _
  calc (n : ℝ) ^ (-σ) * Real.log n ^ 2 ≤ ahi * lhi ^ 2 :=
        mul_le_mul ha h2 (sq_nonneg _) (le_trans ha0 ha)
    _ ≤ b := hb

/-- **Majoration de la constante de reste.** -/
lemma mainRemConst_le (N : ℕ) (hN : 1 ≤ N) (σ W : ℝ) (hW : 0 < W) (S ahi lhi B : ℝ)
    (hS : ∑ n ∈ Finset.range N, Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * σ)) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2 ≤ S)
    (ha : (N : ℝ) ^ (-σ) ≤ ahi) (hl : Real.log N ≤ lhi)
    (hB : S + ahi * lhi ^ 2 / 2 + N * ahi * ((lhi ^ 2 + 1 / W ^ 2 + lhi / W) / W) ≤ B) :
    mainRemConst N σ W ≤ B := by
  unfold mainRemConst
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have e : Real.exp (-(Real.log N * σ)) = (N : ℝ) ^ (-σ) := by rw [Real.rpow_def_of_pos hpos]; ring_nf
  rw [e]
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have ha0 : 0 ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg hpos.le _
  have h2 : Real.log N ^ 2 ≤ lhi ^ 2 := pow_le_pow_left₀ hl0 hl 2
  have h3 : Real.log N / W ≤ lhi / W := div_le_div_of_nonneg_right hl hW.le
  have hq : (Real.log N ^ 2 + 1 / W ^ 2 + Real.log N / W) / W ≤ (lhi ^ 2 + 1 / W ^ 2 + lhi / W) / W :=
    div_le_div_of_nonneg_right (by linarith) hW.le
  have hq0 : 0 ≤ (Real.log N ^ 2 + 1 / W ^ 2 + Real.log N / W) / W := by positivity
  have hahi : 0 ≤ ahi := le_trans ha0 ha
  have t2 : (N : ℝ) ^ (-σ) * Real.log N ^ 2 / 2 ≤ ahi * lhi ^ 2 / 2 := by
    gcongr
  have t3 : (N : ℝ) * (N : ℝ) ^ (-σ) * ((Real.log N ^ 2 + 1 / W ^ 2 + Real.log N / W) / W) ≤
      N * ahi * ((lhi ^ 2 + 1 / W ^ 2 + lhi / W) / W) := by
    gcongr
  linarith

/-! ## Rotations, facteur `(1 − s)`, recouvrement, termes `n = 1` -/

lemma rot0 : I ^ (0 : ℕ) = ((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I := by simp
lemma rot1 : I ^ (1 : ℕ) = ((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I := by simp
lemma rot2 : I ^ (2 : ℕ) = ((-1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I := by simp
lemma rot3 : I ^ (3 : ℕ) = ((0 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I := by
  rw [pow_succ, I_sq]; simp

lemma u1_left (c t : ℝ) (hc : c < 1) : 0 < (I ^ (-4 : ℤ) * (1 - ((c : ℂ) + (t : ℂ) * I))).re := by
  rw [I_zpow_eq (-4) (-1) 0 (by norm_num), pow_zero, one_mul]; simp; linarith

lemma u1_right (t : ℝ) : 0 < (I ^ (-2 : ℤ) * (1 - (((2 : ℝ) : ℂ) + (t : ℂ) * I))).re := by
  rw [I_zpow_eq (-2) (-1) 2 (by norm_num), I_sq]; simp

lemma u1_bottom (x : ℝ) : 0 < (I ^ (-1 : ℤ) * (1 - ((x : ℂ) + ((-1 : ℝ) : ℂ) * I))).re := by
  rw [I_zpow_eq (-1) (-1) 3 (by norm_num), pow_succ, I_sq]; simp

lemma u1_top (x : ℝ) : 0 < (I ^ (-3 : ℤ) * (1 - ((x : ℂ) + ((15 : ℝ) : ℂ) * I))).re := by
  rw [I_zpow_eq (-3) (-1) 1 (by norm_num), pow_one]; simp

lemma u1_bottom' (x : ℝ) : 0 < (I ^ (-5 : ℤ) * (1 - ((x : ℂ) + ((-1 : ℝ) : ℂ) * I))).re := by
  rw [I_zpow_eq (-5) (-2) 3 (by norm_num), pow_succ, I_sq]; simp

lemma pw1_lo (σ : ℝ) : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) ^ (-σ) := by simp
lemma pw1_hi (σ : ℝ) : ((1 : ℕ) : ℝ) ^ (-σ) ≤ 1 := by simp

lemma cs_one (t : ℝ) :
    ‖exp (-(((t * Real.log ((1 : ℕ) : ℝ) : ℝ) : ℂ) * I)) - (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)‖ ≤ 0 := by simp

lemma list_mono (L : List ℤ) (d : ℝ) (hd : 0 < d) (m : ℕ) (h : ∀ k < m, L.getD k 0 ≤ L.getD (k + 1) 0) :
    ∀ k < m, ((L.getD k 0 : ℤ) : ℝ) / d ≤ ((L.getD (k + 1) 0 : ℤ) : ℝ) / d := by
  intro k hk
  have := h k hk
  have : ((L.getD k 0 : ℤ) : ℝ) ≤ ((L.getD (k + 1) 0 : ℤ) : ℝ) := by exact_mod_cast this
  exact div_le_div_of_nonneg_right this hd.le

/-- Recouvrement d'un intervalle par des morceaux consécutifs. -/
lemma cover (y : ℕ → ℝ) (P : ℝ → Prop) :
    ∀ m : ℕ, (∀ k < m + 1, y k ≤ y (k + 1)) → (∀ k < m + 1, ∀ t ∈ Icc (y k) (y (k + 1)), P t) →
      ∀ t ∈ Icc (y 0) (y (m + 1)), P t := by
  intro m
  induction m with
  | zero => intro _ h t ht; exact h 0 (by omega) t ht
  | succ m ih =>
    intro hy h t ht
    rcases le_total t (y (m + 1)) with h1 | h1
    · exact ih (fun k hk => hy k (by omega)) (fun k hk => h k (by omega)) t ⟨ht.1, h1⟩
    · exact h (m + 1) (by omega) t ⟨h1, ht.2⟩

lemma zeta_ne_of_re_pos {z : ℤ} {s : ℂ} (h : 0 < (I ^ z * riemannZeta s).re) : riemannZeta s ≠ 0 := by
  intro h0; rw [h0, mul_zero] at h; simp at h

lemma I_zpow_congr (a b k : ℤ) (h : a = b + 4 * k) : I ^ a = I ^ b := by
  rw [h, zpow_add₀ I_ne_zero, zpow_mul]
  have : I ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, I_sq]; norm_num
  rw [this, one_zpow, mul_one]

end ZB
end RHV6Fresh
