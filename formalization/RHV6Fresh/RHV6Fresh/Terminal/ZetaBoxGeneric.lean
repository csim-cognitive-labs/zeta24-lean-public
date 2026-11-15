/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.EulerMaclaurinFine
import RHV6Fresh.Terminal.BoxCount

/-!
# Certificat de `ζ` sur les côtés d'un rectangle : lemmes génériques (vérification (V2))

Outils, sans aucune valeur numérique, pour certifier `Re(v·ζ(s)) > 0` sur un segment à partir de DEUX valeurs ponctuelles
de la partie principale d'Euler–Maclaurin :

* `main_eq_ez` : `main_N(s) = Σ_{n ≤ N} e^{−s log n} − N e^{−s log N}/(1 − s) − e^{−s log N}/2` ;
* `main_expand` : développement d'ordre un le long d'une direction unitaire, reste `≤ B δ²` (`mainRemConst`) ;
* `main_interp` : la dérivée s'élimine entre les deux extrémités d'un segment :
  `‖L·main(s) − ((L − α)·main(s_a) + α·main(s_b))‖ ≤ B α (L − α) L` ;
* `re_zeta_pos_of_endpoints` : `Re(v ζ(s)) ≥ min(q_a, q_b) − B L²/4 − E > 0` sur tout le segment ;
* demi-plans et logarithmes : `log_mul_of_re_pos`, `mul_mem_slitPlane_of_re_pos`, raccords d'un quart de tour.

Aucun `sorry`, aucun axiome ajouté.
-/

namespace RHV6Fresh
namespace ZB

open Complex Set

/-- `e^{−ℓ s}` (pour `ℓ = log n`, c'est `n^{−s}`). -/
noncomputable def ez (ℓ : ℝ) (s : ℂ) : ℂ := exp (-((ℓ : ℂ) * s))

theorem norm_ez (ℓ : ℝ) (s : ℂ) : ‖ez ℓ s‖ = Real.exp (-(ℓ * s.re)) := by
  rw [ez, Complex.norm_exp]; simp

theorem one_div_natCast_cpow (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    1 / (n : ℂ) ^ s = ez (Real.log n) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [one_div, ← Complex.cpow_neg, Complex.cpow_def_of_ne_zero hn0, ez]
  have hl : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hpos.le]; simp
  rw [hl]; congr 1; ring

theorem natCast_cpow_one_sub (N : ℕ) (hN : 1 ≤ N) (s : ℂ) :
    (N : ℂ) ^ (1 - s) = (N : ℂ) * ez (Real.log N) s := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hN0, Complex.cpow_one, Complex.cpow_neg, ← one_div,
    one_div_natCast_cpow N hN]

theorem natCast_cpow_neg (N : ℕ) (hN : 1 ≤ N) (s : ℂ) :
    (N : ℂ) ^ (-s) = ez (Real.log N) s := by
  rw [Complex.cpow_neg, ← one_div, one_div_natCast_cpow N hN]

/-- Partie principale réécrite par `e^{−s log n}`. -/
theorem main_eq_ez (N : ℕ) (hN : 1 ≤ N) (s : ℂ) (hs0 : s ≠ 0) :
    eulerMaclaurinMain N s =
      (∑ n ∈ Finset.range N, ez (Real.log ((n + 1 : ℕ) : ℝ)) s) -
        (N : ℂ) * ez (Real.log N) s / (1 - s) - ez (Real.log N) s / 2 := by
  unfold eulerMaclaurinMain
  rw [Finset.sum_range_succ', natCast_cpow_one_sub N hN, natCast_cpow_neg N hN]
  have e0 : 1 / ((0 : ℕ) : ℂ) ^ s = 0 := by simp [Complex.zero_cpow hs0]
  rw [e0, add_zero]
  have : ∀ n ∈ Finset.range N, 1 / ((n + 1 : ℕ) : ℂ) ^ s = ez (Real.log ((n + 1 : ℕ) : ℝ)) s :=
    fun n _ => one_div_natCast_cpow (n + 1) (by omega) s
  rw [Finset.sum_congr rfl this]
  ring

/-! ## Développement d'ordre un -/

/-- Dérivée de la partie principale le long de `e`. -/
noncomputable def mainDeriv (N : ℕ) (s e : ℂ) : ℂ :=
  (∑ n ∈ Finset.range N, (-(Real.log ((n + 1 : ℕ) : ℝ) : ℂ) * e) * ez (Real.log ((n + 1 : ℕ) : ℝ)) s) -
    (N : ℂ) * ez (Real.log N) s * (e * (1 - (Real.log N : ℂ) * (1 - s)) / (1 - s) ^ 2) -
    (-(Real.log N : ℂ) * e) * ez (Real.log N) s / 2

/-- Constante de reste. -/
noncomputable def mainRemConst (N : ℕ) (σ W : ℝ) : ℝ :=
  (∑ n ∈ Finset.range N, Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * σ)) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) +
    Real.exp (-(Real.log N * σ)) * Real.log N ^ 2 / 2 +
    N * Real.exp (-(Real.log N * σ)) * ((Real.log N ^ 2 + 1 / W ^ 2 + Real.log N / W) / W)

theorem ez_add (ℓ : ℝ) (s x : ℂ) : ez ℓ (s + x) = ez ℓ s * exp (-((ℓ : ℂ) * x)) := by
  rw [ez, ez, ← Complex.exp_add]; congr 1; ring

/-- Reste d'un terme exponentiel. -/
theorem ez_term_rem (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (s e : ℂ) (he : ‖e‖ = 1) (δ : ℝ) (hδ : |δ| * ℓ ≤ 1) :
    ‖ez ℓ (s + δ * e) - ez ℓ s - δ * ((-(ℓ : ℂ) * e) * ez ℓ s)‖ ≤
      Real.exp (-(ℓ * s.re)) * ℓ ^ 2 * δ ^ 2 := by
  have hx : ‖-((ℓ : ℂ) * (δ * e))‖ = |δ| * ℓ := by
    rw [norm_neg, norm_mul, norm_mul, he]; simp [abs_of_nonneg hℓ]; ring
  have h := Complex.norm_exp_sub_one_sub_id_le (x := -((ℓ : ℂ) * (δ * e))) (by rw [hx]; exact hδ)
  rw [hx] at h
  have e1 : ez ℓ (s + δ * e) - ez ℓ s - δ * ((-(ℓ : ℂ) * e) * ez ℓ s) =
      ez ℓ s * (exp (-((ℓ : ℂ) * (δ * e))) - 1 - -((ℓ : ℂ) * (δ * e))) := by
    rw [ez_add]; ring
  rw [e1, norm_mul, norm_ez]
  calc Real.exp (-(ℓ * s.re)) * ‖exp (-((ℓ : ℂ) * (δ * e))) - 1 - -((ℓ : ℂ) * (δ * e))‖
      ≤ Real.exp (-(ℓ * s.re)) * (|δ| * ℓ) ^ 2 := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = Real.exp (-(ℓ * s.re)) * ℓ ^ 2 * δ ^ 2 := by rw [mul_pow, sq_abs]; ring

/-- Reste du terme de queue `N e^{−ℓ s}/(1 − s)`. -/
theorem tail_term_rem (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (s e : ℂ) (he : ‖e‖ = 1) (δ : ℝ) (hδ : |δ| * ℓ ≤ 1)
    (W : ℝ) (hW : 0 < W) (hw0 : W ≤ ‖1 - s‖) (hw1 : W ≤ ‖1 - (s + δ * e)‖) :
    ‖ez ℓ (s + δ * e) / (1 - (s + δ * e)) - ez ℓ s / (1 - s) -
        δ * (ez ℓ s * (e * (1 - (ℓ : ℂ) * (1 - s)) / (1 - s) ^ 2))‖ ≤
      Real.exp (-(ℓ * s.re)) * ((ℓ ^ 2 + 1 / W ^ 2 + ℓ / W) / W) * δ ^ 2 := by
  set w0 : ℂ := 1 - s with hw0def
  set x : ℂ := δ * e with hxdef
  have hxn : ‖x‖ = |δ| := by rw [hxdef, norm_mul, he]; simp
  have hw0n : 0 < ‖w0‖ := lt_of_lt_of_le hW hw0
  have hw0z : w0 ≠ 0 := norm_pos_iff.mp hw0n
  have hw1' : W ≤ ‖w0 - x‖ := by
    have : 1 - (s + δ * e) = w0 - x := by rw [hw0def, hxdef]; ring
    rw [← this]; exact hw1
  have hw1n : 0 < ‖w0 - x‖ := lt_of_lt_of_le hW hw1'
  have hw1z : w0 - x ≠ 0 := norm_pos_iff.mp hw1n
  set r : ℂ := exp (-((ℓ : ℂ) * x)) - 1 - -((ℓ : ℂ) * x) with hr
  have hrb : ‖r‖ ≤ (|δ| * ℓ) ^ 2 := by
    have hx' : ‖-((ℓ : ℂ) * x)‖ = |δ| * ℓ := by
      rw [norm_neg, norm_mul, hxn]; simp [abs_of_nonneg hℓ]; ring
    have h := Complex.norm_exp_sub_one_sub_id_le (x := -((ℓ : ℂ) * x)) (by rw [hx']; exact hδ)
    rw [hx'] at h; exact h
  have key : ez ℓ (s + δ * e) / (1 - (s + δ * e)) - ez ℓ s / (1 - s) -
        δ * (ez ℓ s * (e * (1 - (ℓ : ℂ) * (1 - s)) / (1 - s) ^ 2)) =
      ez ℓ s * (r / (w0 - x) + x ^ 2 * (1 - (ℓ : ℂ) * w0) / (w0 ^ 2 * (w0 - x))) := by
    have e1 : 1 - (s + δ * e) = w0 - x := by rw [hw0def, hxdef]; ring
    rw [e1, ez_add, ← hw0def, hr]
    rw [← hxdef]
    field_simp
    ring
  rw [key, norm_mul, norm_ez, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hδ2 : |δ| ^ 2 = δ ^ 2 := sq_abs δ
  have b1 : ‖r / (w0 - x)‖ ≤ ℓ ^ 2 * δ ^ 2 / W := by
    rw [norm_div]
    calc ‖r‖ / ‖w0 - x‖ ≤ (|δ| * ℓ) ^ 2 / W := div_le_div₀ (by positivity) hrb hW hw1'
      _ = ℓ ^ 2 * δ ^ 2 / W := by rw [mul_pow, hδ2]; ring
  have b2 : ‖x ^ 2 * (1 - (ℓ : ℂ) * w0) / (w0 ^ 2 * (w0 - x))‖ ≤ (1 / W ^ 2 + ℓ / W) / W * δ ^ 2 := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, hxn, hδ2]
    have hn1 : ‖1 - (ℓ : ℂ) * w0‖ ≤ 1 + ℓ * ‖w0‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]; simp [abs_of_nonneg hℓ]
    have hq : (1 + ℓ * ‖w0‖) / ‖w0‖ ^ 2 ≤ 1 / W ^ 2 + ℓ / W := by
      rw [add_div]
      have h1 : 1 / ‖w0‖ ^ 2 ≤ 1 / W ^ 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_left₀ hW.le hw0 2
      have h2 : ℓ * ‖w0‖ / ‖w0‖ ^ 2 ≤ ℓ / W := by
        rw [sq, ← div_div, mul_div_assoc, div_self hw0n.ne', mul_one]
        exact div_le_div_of_nonneg_left hℓ hW hw0
      linarith
    calc δ ^ 2 * ‖1 - (ℓ : ℂ) * w0‖ / (‖w0‖ ^ 2 * ‖w0 - x‖)
        ≤ δ ^ 2 * (1 + ℓ * ‖w0‖) / (‖w0‖ ^ 2 * W) := by
          apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hn1 (sq_nonneg _))
            (by positivity) (mul_le_mul_of_nonneg_left hw1' (by positivity))
      _ = (1 + ℓ * ‖w0‖) / ‖w0‖ ^ 2 / W * δ ^ 2 := by field_simp
      _ ≤ (1 / W ^ 2 + ℓ / W) / W * δ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact div_le_div_of_nonneg_right hq hW.le
  calc ‖r / (w0 - x) + x ^ 2 * (1 - (ℓ : ℂ) * w0) / (w0 ^ 2 * (w0 - x))‖
      ≤ ‖r / (w0 - x)‖ + ‖x ^ 2 * (1 - (ℓ : ℂ) * w0) / (w0 ^ 2 * (w0 - x))‖ := norm_add_le _ _
    _ ≤ ℓ ^ 2 * δ ^ 2 / W + (1 / W ^ 2 + ℓ / W) / W * δ ^ 2 := add_le_add b1 b2
    _ = (ℓ ^ 2 + 1 / W ^ 2 + ℓ / W) / W * δ ^ 2 := by ring

theorem log_natCast_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

theorem log_le_log_N {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) : Real.log (n : ℝ) ≤ Real.log N :=
  Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnN)

/-- **Développement d'ordre un de la partie principale** le long d'une direction unitaire. -/
theorem main_expand (N : ℕ) (hN : 1 ≤ N) (s e : ℂ) (he : ‖e‖ = 1) (δ : ℝ)
    (hδ : |δ| * Real.log N ≤ 1) (W : ℝ) (hW : 0 < W) (hw0 : W ≤ ‖1 - s‖) (hw1 : W ≤ ‖1 - (s + δ * e)‖)
    (hs0 : s ≠ 0) (hs1 : s + δ * e ≠ 0) :
    ‖eulerMaclaurinMain N (s + δ * e) - eulerMaclaurinMain N s - δ * mainDeriv N s e‖ ≤
      mainRemConst N s.re W * δ ^ 2 := by
  rw [main_eq_ez N hN _ hs1, main_eq_ez N hN _ hs0, mainDeriv, mainRemConst]
  set ℓN := Real.log N with hℓN
  have hℓN0 : 0 ≤ ℓN := log_natCast_nonneg N
  have hsplit :
      (∑ n ∈ Finset.range N, ez (Real.log ((n + 1 : ℕ) : ℝ)) (s + δ * e)) -
          (N : ℂ) * ez ℓN (s + δ * e) / (1 - (s + δ * e)) - ez ℓN (s + δ * e) / 2 -
        ((∑ n ∈ Finset.range N, ez (Real.log ((n + 1 : ℕ) : ℝ)) s) - (N : ℂ) * ez ℓN s / (1 - s) - ez ℓN s / 2) -
        δ * ((∑ n ∈ Finset.range N, (-(Real.log ((n + 1 : ℕ) : ℝ) : ℂ) * e) * ez (Real.log ((n + 1 : ℕ) : ℝ)) s) -
          (N : ℂ) * ez ℓN s * (e * (1 - (ℓN : ℂ) * (1 - s)) / (1 - s) ^ 2) - (-(ℓN : ℂ) * e) * ez ℓN s / 2) =
      (∑ n ∈ Finset.range N, (ez (Real.log ((n + 1 : ℕ) : ℝ)) (s + δ * e) - ez (Real.log ((n + 1 : ℕ) : ℝ)) s -
          δ * ((-(Real.log ((n + 1 : ℕ) : ℝ) : ℂ) * e) * ez (Real.log ((n + 1 : ℕ) : ℝ)) s))) -
        (N : ℂ) * (ez ℓN (s + δ * e) / (1 - (s + δ * e)) - ez ℓN s / (1 - s) -
          δ * (ez ℓN s * (e * (1 - (ℓN : ℂ) * (1 - s)) / (1 - s) ^ 2))) -
        (ez ℓN (s + δ * e) - ez ℓN s - δ * ((-(ℓN : ℂ) * e) * ez ℓN s)) / 2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hsplit]
  have hδn : ∀ n ∈ Finset.range N, |δ| * Real.log ((n + 1 : ℕ) : ℝ) ≤ 1 := by
    intro n hn
    have := log_le_log_N (n := n + 1) (N := N) (by omega) (by simp at hn; omega)
    calc |δ| * Real.log ((n + 1 : ℕ) : ℝ) ≤ |δ| * ℓN := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ ≤ 1 := hδ
  have b1 : ‖∑ n ∈ Finset.range N, (ez (Real.log ((n + 1 : ℕ) : ℝ)) (s + δ * e) -
      ez (Real.log ((n + 1 : ℕ) : ℝ)) s -
        δ * ((-(Real.log ((n + 1 : ℕ) : ℝ) : ℂ) * e) * ez (Real.log ((n + 1 : ℕ) : ℝ)) s))‖ ≤
      (∑ n ∈ Finset.range N, Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * s.re)) *
        Real.log ((n + 1 : ℕ) : ℝ) ^ 2) * δ ^ 2 := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    exact ez_term_rem _ (log_natCast_nonneg _) s e he δ (hδn n hn)
  have b2 : ‖(N : ℂ) * (ez ℓN (s + δ * e) / (1 - (s + δ * e)) - ez ℓN s / (1 - s) -
      δ * (ez ℓN s * (e * (1 - (ℓN : ℂ) * (1 - s)) / (1 - s) ^ 2)))‖ ≤
      N * Real.exp (-(ℓN * s.re)) * ((ℓN ^ 2 + 1 / W ^ 2 + ℓN / W) / W) * δ ^ 2 := by
    rw [norm_mul, Complex.norm_natCast]
    have := tail_term_rem ℓN hℓN0 s e he δ hδ W hW hw0 hw1
    calc (N : ℝ) * _ ≤ N * (Real.exp (-(ℓN * s.re)) * ((ℓN ^ 2 + 1 / W ^ 2 + ℓN / W) / W) * δ ^ 2) :=
          mul_le_mul_of_nonneg_left this (Nat.cast_nonneg N)
      _ = _ := by ring
  have b3 : ‖(ez ℓN (s + δ * e) - ez ℓN s - δ * ((-(ℓN : ℂ) * e) * ez ℓN s)) / 2‖ ≤
      Real.exp (-(ℓN * s.re)) * ℓN ^ 2 / 2 * δ ^ 2 := by
    rw [norm_div]
    have := ez_term_rem ℓN hℓN0 s e he δ hδ
    simp only [RCLike.norm_ofNat]
    linarith
  calc _ ≤ ‖(∑ n ∈ Finset.range N, (ez (Real.log ((n + 1 : ℕ) : ℝ)) (s + δ * e) -
          ez (Real.log ((n + 1 : ℕ) : ℝ)) s -
          δ * ((-(Real.log ((n + 1 : ℕ) : ℝ) : ℂ) * e) * ez (Real.log ((n + 1 : ℕ) : ℝ)) s))) -
        (N : ℂ) * (ez ℓN (s + δ * e) / (1 - (s + δ * e)) - ez ℓN s / (1 - s) -
          δ * (ez ℓN s * (e * (1 - (ℓN : ℂ) * (1 - s)) / (1 - s) ^ 2)))‖ +
        ‖(ez ℓN (s + δ * e) - ez ℓN s - δ * ((-(ℓN : ℂ) * e) * ez ℓN s)) / 2‖ := norm_sub_le _ _
    _ ≤ _ := by
        have := norm_sub_le (∑ n ∈ Finset.range N, (ez (Real.log ((n + 1 : ℕ) : ℝ)) (s + δ * e) -
          ez (Real.log ((n + 1 : ℕ) : ℝ)) s -
          δ * ((-(Real.log ((n + 1 : ℕ) : ℝ) : ℂ) * e) * ez (Real.log ((n + 1 : ℕ) : ℝ)) s)))
          ((N : ℂ) * (ez ℓN (s + δ * e) / (1 - (s + δ * e)) - ez ℓN s / (1 - s) -
          δ * (ez ℓN s * (e * (1 - (ℓN : ℂ) * (1 - s)) / (1 - s) ^ 2))))
        nlinarith

/-- Monotonie de la constante de reste en la partie réelle. -/
theorem mainRemConst_mono (N : ℕ) {σ σ' : ℝ} (h : σ' ≤ σ) (W : ℝ) (hW : 0 < W) :
    mainRemConst N σ W ≤ mainRemConst N σ' W := by
  unfold mainRemConst
  have hq : 0 ≤ (Real.log N ^ 2 + 1 / W ^ 2 + Real.log N / W) / W := by
    have := log_natCast_nonneg N; positivity
  have hx : ∀ ℓ : ℝ, 0 ≤ ℓ → Real.exp (-(ℓ * σ)) ≤ Real.exp (-(ℓ * σ')) := fun ℓ hℓ =>
    Real.exp_le_exp.mpr (by nlinarith)
  have h1 : (∑ n ∈ Finset.range N, Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * σ)) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2) ≤
      ∑ n ∈ Finset.range N, Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ) * σ')) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2 :=
    Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (hx _ (log_natCast_nonneg _)) (sq_nonneg _)
  have h2 := hx _ (log_natCast_nonneg N)
  have h3 : Real.exp (-(Real.log N * σ)) * Real.log N ^ 2 / 2 ≤ Real.exp (-(Real.log N * σ')) * Real.log N ^ 2 / 2 := by
    gcongr
  have h4 : (N : ℝ) * Real.exp (-(Real.log N * σ)) * ((Real.log N ^ 2 + 1 / W ^ 2 + Real.log N / W) / W) ≤
      N * Real.exp (-(Real.log N * σ')) * ((Real.log N ^ 2 + 1 / W ^ 2 + Real.log N / W) / W) := by
    gcongr
  linarith

/-- **Interpolation** : la dérivée s'élimine entre deux points d'un segment. -/
theorem main_interp (N : ℕ) (hN : 1 ≤ N) (s e : ℂ) (he : ‖e‖ = 1) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαl : α * Real.log N ≤ 1) (hβl : β * Real.log N ≤ 1) (W : ℝ) (hW : 0 < W) (hw : W ≤ ‖1 - s‖)
    (hwa : W ≤ ‖1 - (s + (-α : ℝ) * e)‖) (hwb : W ≤ ‖1 - (s + β * e)‖)
    (hs0 : s ≠ 0) (hsa : s + (-α : ℝ) * e ≠ 0) (hsb : s + β * e ≠ 0) :
    ‖((α + β : ℝ) : ℂ) * eulerMaclaurinMain N s -
        ((β : ℂ) * eulerMaclaurinMain N (s + (-α : ℝ) * e) + (α : ℂ) * eulerMaclaurinMain N (s + β * e))‖ ≤
      mainRemConst N s.re W * (α * β * (α + β)) := by
  have ha := main_expand N hN s e he (-α) (by rw [abs_neg, abs_of_nonneg hα]; exact hαl) W hW hw hwa hs0 hsa
  have hb := main_expand N hN s e he β (by rw [abs_of_nonneg hβ]; exact hβl) W hW hw hwb hs0 hsb
  set A := eulerMaclaurinMain N (s + (-α : ℝ) * e)
  set Bv := eulerMaclaurinMain N (s + β * e)
  set M := eulerMaclaurinMain N s
  set D := mainDeriv N s e
  set K := mainRemConst N s.re W
  have e1 : ((α + β : ℝ) : ℂ) * M - ((β : ℂ) * A + (α : ℂ) * Bv) =
      -((β : ℂ) * (A - M - ((-α : ℝ) : ℂ) * D) + (α : ℂ) * (Bv - M - (β : ℂ) * D)) := by
    push_cast; ring
  rw [e1, norm_neg]
  calc _ ≤ ‖(β : ℂ) * (A - M - ((-α : ℝ) : ℂ) * D)‖ + ‖(α : ℂ) * (Bv - M - (β : ℂ) * D)‖ := norm_add_le _ _
    _ ≤ β * (K * (-α) ^ 2) + α * (K * β ^ 2) := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hα,
          Real.norm_of_nonneg hβ]
        exact add_le_add (mul_le_mul_of_nonneg_left ha hβ) (mul_le_mul_of_nonneg_left hb hα)
    _ = K * (α * β * (α + β)) := by ring

/-- **Positivité de `Re(v ζ)` en un point d'un segment** depuis deux valeurs aux extrémités. -/
theorem re_zeta_pos_of_endpoints (N : ℕ) (hN : 1 ≤ N) (s e v : ℂ) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 1)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hL : 0 < α + β) (hLl : (α + β) * Real.log N ≤ 1)
    (W : ℝ) (hW : 0 < W) (hw : W ≤ ‖1 - s‖)
    (hwa : W ≤ ‖1 - (s + (-α : ℝ) * e)‖) (hwb : W ≤ ‖1 - (s + β * e)‖)
    (hs0 : s ≠ 0) (hsa : s + (-α : ℝ) * e ≠ 0) (hsb : s + β * e ≠ 0)
    (σmin : ℝ) (hσ : σmin ≤ s.re) (hσ0 : 0 < s.re) (hs1 : s ≠ 1)
    (B : ℝ) (hB : mainRemConst N σmin W ≤ B) (E : ℝ)
    (hE : ‖s‖ * ‖s + 1‖ / 12 * ((N : ℝ) ^ (-s.re - 2) + (N : ℝ) ^ (-s.re - 1) / (s.re + 1)) ≤ E)
    (qa qb : ℝ) (ha : qa ≤ (v * eulerMaclaurinMain N (s + (-α : ℝ) * e)).re)
    (hb : qb ≤ (v * eulerMaclaurinMain N (s + β * e)).re)
    (hpos : B * (α + β) ^ 2 / 4 + E < min qa qb) :
    0 < (v * riemannZeta s).re := by
  have hlog0 := log_natCast_nonneg N
  have hαl : α * Real.log N ≤ 1 := le_trans (mul_le_mul_of_nonneg_right (by linarith) hlog0) hLl
  have hβl : β * Real.log N ≤ 1 := le_trans (mul_le_mul_of_nonneg_right (by linarith) hlog0) hLl
  have hI := main_interp N hN s e he α β hα hβ hαl hβl W hW hw hwa hwb hs0 hsa hsb
  have hK : mainRemConst N s.re W ≤ B := (mainRemConst_mono N hσ W hW).trans hB
  have hK0 : 0 ≤ α * β * (α + β) := by positivity
  set A := eulerMaclaurinMain N (s + (-α : ℝ) * e)
  set Bv := eulerMaclaurinMain N (s + β * e)
  set M := eulerMaclaurinMain N s
  -- partie réelle de `v·M`
  have hre : (α + β) * (v * M).re ≥ β * qa + α * qb - mainRemConst N s.re W * (α * β * (α + β)) := by
    have h1 := Complex.abs_re_le_norm (v * (((α + β : ℝ) : ℂ) * M - ((β : ℂ) * A + (α : ℂ) * Bv)))
    have h2 : ‖v * (((α + β : ℝ) : ℂ) * M - ((β : ℂ) * A + (α : ℂ) * Bv))‖ ≤
        mainRemConst N s.re W * (α * β * (α + β)) := by
      rw [norm_mul]
      calc ‖v‖ * _ ≤ 1 * (mainRemConst N s.re W * (α * β * (α + β))) :=
            mul_le_mul hv hI (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
    have e1 : (v * (((α + β : ℝ) : ℂ) * M - ((β : ℂ) * A + (α : ℂ) * Bv))).re =
        (α + β) * (v * M).re - (β * (v * A).re + α * (v * Bv).re) := by
      have : v * (((α + β : ℝ) : ℂ) * M - ((β : ℂ) * A + (α : ℂ) * Bv)) =
          ((α + β : ℝ) : ℂ) * (v * M) - ((β : ℂ) * (v * A) + (α : ℂ) * (v * Bv)) := by ring
      rw [this]; simp [Complex.sub_re, Complex.add_re]
    rw [e1] at h1
    have h3 := abs_le.mp (h1.trans h2)
    nlinarith [mul_le_mul_of_nonneg_left ha hβ, mul_le_mul_of_nonneg_left hb hα]
  -- `α β ≤ (α + β)²/4`
  have hab : α * β * (α + β) ≤ (α + β) ^ 2 / 4 * (α + β) := by
    apply mul_le_mul_of_nonneg_right _ hL.le; nlinarith [sq_nonneg (α - β)]
  have hmin : β * qa + α * qb ≥ (α + β) * min qa qb := by
    have := min_le_left qa qb; have := min_le_right qa qb; nlinarith
  have hKpos : 0 ≤ mainRemConst N s.re W := by
    unfold mainRemConst
    have : 0 ≤ (Real.log N ^ 2 + 1 / W ^ 2 + Real.log N / W) / W := by positivity
    apply add_nonneg (add_nonneg (Finset.sum_nonneg fun n _ => by positivity) (by positivity))
    positivity
  have hvM : (v * M).re ≥ min qa qb - B * (α + β) ^ 2 / 4 := by
    have h4 : mainRemConst N s.re W * (α * β * (α + β)) ≤ B * ((α + β) ^ 2 / 4 * (α + β)) :=
      mul_le_mul hK hab hK0 (le_trans hKpos hK)
    have h5 : (α + β) * (v * M).re ≥ (α + β) * (min qa qb - B * (α + β) ^ 2 / 4) := by nlinarith
    exact le_of_mul_le_mul_left h5 hL
  -- erreur d'Euler–Maclaurin
  have hs : s = (s.re : ℂ) + (s.im : ℝ) * I := (Complex.re_add_im s).symm
  have hEM := zeta_sub_eulerMaclaurinMain_le_fine N hN (σ := s.re) (t := s.im) hσ0 (by rw [← hs]; exact hs1)
  rw [← hs] at hEM
  have hz : (v * riemannZeta s).re ≥ (v * M).re - E := by
    have h1 := Complex.abs_re_le_norm (v * (riemannZeta s - M))
    have h2 : ‖v * (riemannZeta s - M)‖ ≤ E := by
      rw [norm_mul]
      calc ‖v‖ * ‖riemannZeta s - M‖ ≤ 1 * E := mul_le_mul hv (hEM.trans hE) (norm_nonneg _) (by norm_num)
        _ = E := one_mul E
    have e1 : (v * (riemannZeta s - M)).re = (v * riemannZeta s).re - (v * M).re := by
      rw [mul_sub, Complex.sub_re]
    rw [e1] at h1
    linarith [(abs_le.mp (h1.trans h2)).1]
  linarith

/-! ## Erreur d'Euler–Maclaurin uniforme sur un segment -/

theorem efine_le (N : ℕ) (hN : 1 ≤ N) (s : ℂ) (σmin A S S1 : ℝ) (hσ : σmin ≤ s.re) (hσ0 : 0 < σmin)
    (hA : (N : ℝ) ^ (-σmin) ≤ A) (hS : ‖s‖ ≤ S) (hS1 : ‖s + 1‖ ≤ S1) :
    ‖s‖ * ‖s + 1‖ / 12 * ((N : ℝ) ^ (-s.re - 2) + (N : ℝ) ^ (-s.re - 1) / (s.re + 1)) ≤
      S * S1 / 12 * (A / (N : ℝ) ^ 2 + A / ((N : ℝ) * (σmin + 1))) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hpow : (N : ℝ) ^ (-s.re) ≤ A :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hA
  have e2 : (N : ℝ) ^ (-s.re - 2) = (N : ℝ) ^ (-s.re) / (N : ℝ) ^ 2 := by
    rw [Real.rpow_sub hN0, Real.rpow_two]
  have e1 : (N : ℝ) ^ (-s.re - 1) = (N : ℝ) ^ (-s.re) / N := by
    rw [Real.rpow_sub hN0, Real.rpow_one]
  rw [e2, e1]
  have hp0 : 0 ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg hN0.le _
  have hk : (N : ℝ) ^ (-s.re) / (N : ℝ) ^ 2 + (N : ℝ) ^ (-s.re) / N / (s.re + 1) ≤
      A / (N : ℝ) ^ 2 + A / ((N : ℝ) * (σmin + 1)) := by
    have h1 : (N : ℝ) ^ (-s.re) / (N : ℝ) ^ 2 ≤ A / (N : ℝ) ^ 2 := by gcongr
    have h2 : (N : ℝ) ^ (-s.re) / N / (s.re + 1) ≤ A / ((N : ℝ) * (σmin + 1)) := by
      rw [div_div]
      apply div_le_div₀ (le_trans hp0 hpow) hpow (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) hN0.le
    linarith
  have hS0 : 0 ≤ S := le_trans (norm_nonneg _) hS
  have hS10 : 0 ≤ S1 := le_trans (norm_nonneg _) hS1
  have hk0 : 0 ≤ (N : ℝ) ^ (-s.re) / (N : ℝ) ^ 2 + (N : ℝ) ^ (-s.re) / N / (s.re + 1) := by
    have : 0 < s.re + 1 := by linarith
    positivity
  calc ‖s‖ * ‖s + 1‖ / 12 * _ ≤ S * S1 / 12 * ((N : ℝ) ^ (-s.re) / (N : ℝ) ^ 2 + (N : ℝ) ^ (-s.re) / N / (s.re + 1)) := by
        gcongr
    _ ≤ _ := by gcongr

theorem norm_le_of_sq_le {z : ℂ} {S : ℝ} (hS : 0 ≤ S) (h : z.re ^ 2 + z.im ^ 2 ≤ S ^ 2) : ‖z‖ ≤ S := by
  have : ‖z‖ ^ 2 ≤ S ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hS two_ne_zero).mp this

theorem le_norm_of_sq_le {z : ℂ} {W : ℝ} (h : W ^ 2 ≤ z.re ^ 2 + z.im ^ 2) : W ≤ ‖z‖ := by
  have : W ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
  exact abs_le_of_sq_le_sq' this (norm_nonneg _) |>.2

/-! ## Morceaux de côtés -/

/-- **Morceau vertical** `Re s = c`, `Im s ∈ [ya, yb]`. -/
theorem vertical_piece (N : ℕ) (hN : 1 ≤ N) (c ya yb : ℝ) (v : ℂ) (hv : ‖v‖ ≤ 1) (hab : ya < yb) (hc : 0 < c)
    (hc1 : c ≠ 1) (lN : ℝ) (hlN : Real.log N ≤ lN) (hlen : (yb - ya) * lN ≤ 1)
    (W m : ℝ) (hW : 0 < W) (hWm : W ^ 2 ≤ (1 - c) ^ 2 + m ^ 2) (hm : ∀ y ∈ Icc ya yb, m ^ 2 ≤ y ^ 2)
    (B : ℝ) (hB : mainRemConst N c W ≤ B) (A S S1 : ℝ) (hA : (N : ℝ) ^ (-c) ≤ A) (hS0 : 0 ≤ S) (hS1' : 0 ≤ S1)
    (hS : ∀ y ∈ Icc ya yb, c ^ 2 + y ^ 2 ≤ S ^ 2) (hS1 : ∀ y ∈ Icc ya yb, (c + 1) ^ 2 + y ^ 2 ≤ S1 ^ 2)
    (qa qb : ℝ) (ha : qa ≤ (v * eulerMaclaurinMain N ((c : ℂ) + (ya : ℂ) * I)).re)
    (hb : qb ≤ (v * eulerMaclaurinMain N ((c : ℂ) + (yb : ℂ) * I)).re)
    (hpos : B * (yb - ya) ^ 2 / 4 + S * S1 / 12 * (A / (N : ℝ) ^ 2 + A / ((N : ℝ) * (c + 1))) < min qa qb) :
    ∀ y ∈ Icc ya yb, 0 < (v * riemannZeta ((c : ℂ) + (y : ℂ) * I)).re := by
  intro y hy
  have hlog0 := log_natCast_nonneg N
  set s : ℂ := (c : ℂ) + (y : ℂ) * I with hsdef
  have hsre : s.re = c := by simp [hsdef]
  have hsim : s.im = y := by simp [hsdef]
  have hWy : ∀ u : ℝ, u ∈ Icc ya yb → W ≤ ‖1 - ((c : ℂ) + (u : ℂ) * I)‖ := by
    intro u hu
    apply le_norm_of_sq_le
    have := hm u hu
    simp; nlinarith
  have ea : s + ((-(y - ya) : ℝ) : ℂ) * I = (c : ℂ) + (ya : ℂ) * I := by rw [hsdef]; push_cast; ring
  have eb : s + ((yb - y : ℝ) : ℂ) * I = (c : ℂ) + (yb : ℂ) * I := by rw [hsdef]; push_cast; ring
  have hne : ∀ u : ℝ, (c : ℂ) + (u : ℂ) * I ≠ 0 := by
    intro u h; have := congrArg Complex.re h; simp at this; linarith
  refine re_zeta_pos_of_endpoints N hN s I v (by simp) hv (y - ya) (yb - y) (by linarith [hy.1])
    (by linarith [hy.2]) (by linarith) ?_ W hW (hWy y hy) (by rw [ea]; exact hWy ya ⟨le_rfl, hab.le⟩)
    (by rw [eb]; exact hWy yb ⟨hab.le, le_rfl⟩) (hne y) (by rw [ea]; exact hne ya) (by rw [eb]; exact hne yb)
    c (by rw [hsre]) (by rw [hsre]; exact hc) ?_ B hB _
    (efine_le N hN s c A S S1 (by rw [hsre]) hc hA
      (norm_le_of_sq_le hS0 (by rw [hsre, hsim]; exact hS y hy))
      (norm_le_of_sq_le hS1' (by simp [hsdef]; nlinarith [hS1 y hy]))) qa qb
    (by rw [ea]; exact ha) (by rw [eb]; exact hb) (by simpa using hpos)
  · have : (y - ya + (yb - y)) = yb - ya := by ring
    rw [this]; exact le_trans (mul_le_mul_of_nonneg_left hlN (by linarith)) hlen
  · intro h; have := congrArg Complex.re h; simp [hsdef] at this; exact hc1 this

/-- **Morceau horizontal** `Im s = c`, `Re s ∈ [xa, xb]`. -/
theorem horizontal_piece (N : ℕ) (hN : 1 ≤ N) (c xa xb : ℝ) (v : ℂ) (hv : ‖v‖ ≤ 1) (hab : xa < xb)
    (hx0 : 0 < xa) (hc0 : c ≠ 0) (lN : ℝ) (hlN : Real.log N ≤ lN) (hlen : (xb - xa) * lN ≤ 1)
    (W : ℝ) (hW : 0 < W) (hWc : W ^ 2 ≤ c ^ 2)
    (B : ℝ) (hB : mainRemConst N xa W ≤ B) (A S S1 : ℝ) (hA : (N : ℝ) ^ (-xa) ≤ A) (hS0 : 0 ≤ S) (hS1' : 0 ≤ S1)
    (hS : xb ^ 2 + c ^ 2 ≤ S ^ 2) (hS1 : (xb + 1) ^ 2 + c ^ 2 ≤ S1 ^ 2)
    (qa qb : ℝ) (ha : qa ≤ (v * eulerMaclaurinMain N ((xa : ℂ) + (c : ℂ) * I)).re)
    (hb : qb ≤ (v * eulerMaclaurinMain N ((xb : ℂ) + (c : ℂ) * I)).re)
    (hpos : B * (xb - xa) ^ 2 / 4 + S * S1 / 12 * (A / (N : ℝ) ^ 2 + A / ((N : ℝ) * (xa + 1))) < min qa qb) :
    ∀ x ∈ Icc xa xb, 0 < (v * riemannZeta ((x : ℂ) + (c : ℂ) * I)).re := by
  intro x hx
  have hlog0 := log_natCast_nonneg N
  set s : ℂ := (x : ℂ) + (c : ℂ) * I with hsdef
  have hsre : s.re = x := by simp [hsdef]
  have hsim : s.im = c := by simp [hsdef]
  have hWx : ∀ u : ℝ, W ≤ ‖1 - ((u : ℂ) + (c : ℂ) * I)‖ := by
    intro u
    apply le_norm_of_sq_le
    simp; nlinarith [sq_nonneg (1 - u)]
  have ea : s + ((-(x - xa) : ℝ) : ℂ) * 1 = (xa : ℂ) + (c : ℂ) * I := by rw [hsdef]; push_cast; ring
  have eb : s + ((xb - x : ℝ) : ℂ) * 1 = (xb : ℂ) + (c : ℂ) * I := by rw [hsdef]; push_cast; ring
  have hne : ∀ u : ℝ, (u : ℂ) + (c : ℂ) * I ≠ 0 := by
    intro u h; have := congrArg Complex.im h; simp at this; exact hc0 this
  refine re_zeta_pos_of_endpoints N hN s 1 v (by simp) hv (x - xa) (xb - x) (by linarith [hx.1])
    (by linarith [hx.2]) (by linarith) ?_ W hW (hWx x) (by rw [ea]; exact hWx xa)
    (by rw [eb]; exact hWx xb) (hne x) (by rw [ea]; exact hne xa) (by rw [eb]; exact hne xb)
    xa (by rw [hsre]; exact hx.1) (by rw [hsre]; linarith [hx.1]) ?_ B hB _
    (efine_le N hN s xa A S S1 (by rw [hsre]; exact hx.1) hx0 hA
      (norm_le_of_sq_le hS0 (by rw [hsre, hsim]; nlinarith [hx.1, hx.2]))
      (norm_le_of_sq_le hS1' (by simp [hsdef]; nlinarith [hx.1, hx.2]))) qa qb
    (by rw [ea]; exact ha) (by rw [eb]; exact hb) (by simpa using hpos)
  · have : (x - xa + (xb - x)) = xb - xa := by ring
    rw [this]; exact le_trans (mul_le_mul_of_nonneg_left hlN (by linarith)) hlen
  · intro h; have := congrArg Complex.im h; simp [hsdef] at this; exact hc0 this

/-! ## Demi-plans, plan fendu, logarithmes -/

theorem abs_arg_lt_of_re_pos {z : ℂ} (h : 0 < z.re) : |arg z| < Real.pi / 2 :=
  abs_arg_lt_pi_div_two_iff.mpr (Or.inl h)

theorem ne_zero_of_re_pos {z : ℂ} (h : 0 < z.re) : z ≠ 0 := fun h0 => by rw [h0] at h; simp at h

theorem log_mul_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) : log (x * y) = log x + log y := by
  apply Complex.log_mul (ne_zero_of_re_pos hx) (ne_zero_of_re_pos hy)
  have h1 := abs_lt.mp (abs_arg_lt_of_re_pos hx)
  have h2 := abs_lt.mp (abs_arg_lt_of_re_pos hy)
  constructor <;> linarith

theorem mul_mem_slitPlane_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) : x * y ∈ slitPlane := by
  rw [mem_slitPlane_iff_arg]
  have hx0 := ne_zero_of_re_pos hx
  have hy0 := ne_zero_of_re_pos hy
  have h1 := abs_lt.mp (abs_arg_lt_of_re_pos hx)
  have h2 := abs_lt.mp (abs_arg_lt_of_re_pos hy)
  have hm : arg (x * y) = arg x + arg y := Complex.arg_mul hx0 hy0 (by constructor <;> linarith)
  refine ⟨?_, mul_ne_zero hx0 hy0⟩
  rw [hm]; intro h; linarith [Real.pi_pos]

/-- Raccord d'un quart de tour `−I`. -/
theorem log_negI_mul {z : ℂ} (h1 : 0 < z.re) (h2 : 0 < (-I * z).re) : log (-I * z) = log z - (Real.pi / 2 : ℝ) * I := by
  have hz := ne_zero_of_re_pos h1
  have hm : -I * z = -I * z := rfl
  have hI : arg (-I) = -(Real.pi / 2) := by simp
  have hzi : 0 < z.im := by simpa using h2
  have ha : 0 ≤ arg z := Complex.arg_nonneg_iff.mpr hzi.le
  have hb := abs_lt.mp (abs_arg_lt_of_re_pos h1)
  rw [Complex.log_mul (by simp) hz (by rw [hI]; constructor <;> linarith), log_neg_I]
  push_cast; ring

/-- Raccord d'un quart de tour `I`. -/
theorem log_I_mul {z : ℂ} (h1 : 0 < z.re) (h2 : 0 < (I * z).re) : log (I * z) = log z + (Real.pi / 2 : ℝ) * I := by
  have hz := ne_zero_of_re_pos h1
  have hI : arg I = Real.pi / 2 := by simp
  have hzi : z.im < 0 := by simpa using h2
  have ha : arg z < 0 := Complex.arg_neg_iff.mpr hzi
  have hb := abs_lt.mp (abs_arg_lt_of_re_pos h1)
  rw [Complex.log_mul (by simp) hz (by rw [hI]; constructor <;> linarith), log_I]
  push_cast; ring

/-! ## Étiquettes de quart de tour et raccords -/

theorem I_zpow_eq (z q : ℤ) (r : ℕ) (h : z = 4 * q + r) : I ^ z = I ^ r := by
  rw [h, zpow_add₀ I_ne_zero, zpow_mul, zpow_natCast]
  have : I ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, I_sq]; norm_num
  rw [this, one_zpow, one_mul]

theorem norm_I_zpow (z : ℤ) : ‖I ^ z‖ = 1 := by rw [norm_zpow, Complex.norm_I, one_zpow]

theorem log_zpow_junction (A : ℂ) (z z' : ℤ) (h : z' = z ∨ z' = z + 1 ∨ z' = z - 1)
    (h1 : 0 < (I ^ z * A).re) (h2 : 0 < (I ^ z' * A).re) :
    log (I ^ z * A) - log (I ^ z' * A) = ((z - z' : ℤ) : ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  rcases h with rfl | rfl | rfl
  · simp
  · have e : I ^ (z + 1) * A = I * (I ^ z * A) := by rw [zpow_add_one₀ I_ne_zero]; ring
    rw [e] at h2 ⊢
    rw [log_I_mul h1 h2]; push_cast; ring
  · have e : I ^ (z - 1) * A = -I * (I ^ z * A) := by
      rw [zpow_sub_one₀ I_ne_zero, Complex.inv_I]; ring
    rw [e] at h2 ⊢
    rw [log_negI_mul h1 h2]; push_cast; ring

/-- Facteur étudié : `F(s) = (1 − s) ζ(s)`. -/
noncomputable def zetaFactor (s : ℂ) : ℂ := (1 - s) * riemannZeta s

theorem zetaFactor_differentiableOn : DifferentiableOn ℂ zetaFactor {s : ℂ | s ≠ 1} := fun s hs =>
  (((differentiableAt_const _).sub differentiableAt_id).mul
    (differentiableAt_riemannZeta hs)).differentiableWithinAt

theorem isOpen_ne_one : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne

theorem log_split_point (w z : ℤ) (P : ℂ) (h1 : 0 < (I ^ w * (1 - P)).re) (h2 : 0 < (I ^ z * riemannZeta P).re) :
    log (I ^ w * I ^ z * zetaFactor P) = log (I ^ w * (1 - P)) + log (I ^ z * riemannZeta P) := by
  rw [← log_mul_of_re_pos h1 h2, zetaFactor]; ring_nf

theorem slit_point (w z : ℤ) (P : ℂ) (h1 : 0 < (I ^ w * (1 - P)).re) (h2 : 0 < (I ^ z * riemannZeta P).re) :
    I ^ w * I ^ z * zetaFactor P ∈ slitPlane := by
  have := mul_mem_slitPlane_of_re_pos h1 h2
  rw [zetaFactor]; convert this using 1; ring

/-- Raccord générique en un point : deux étiquettes de chaque facteur, chacune à au plus un quart de tour. -/
theorem point_junction (w w' z z' : ℤ) (P : ℂ) (hw : w' = w ∨ w' = w + 1 ∨ w' = w - 1)
    (hz : z' = z ∨ z' = z + 1 ∨ z' = z - 1)
    (h1 : 0 < (I ^ w * (1 - P)).re) (h2 : 0 < (I ^ z * riemannZeta P).re)
    (h1' : 0 < (I ^ w' * (1 - P)).re) (h2' : 0 < (I ^ z' * riemannZeta P).re) :
    log (I ^ w * I ^ z * zetaFactor P) - log (I ^ w' * I ^ z' * zetaFactor P) =
      ((w - w' + (z - z') : ℤ) : ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  rw [log_split_point w z P h1 h2, log_split_point w' z' P h1' h2']
  have a := log_zpow_junction (1 - P) w w' hw h1 h1'
  have b := log_zpow_junction (riemannZeta P) z z' hz h2 h2'
  push_cast at a b ⊢
  linear_combination a + b

theorem continuousOn_logDeriv_comp {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hγ : Continuous γ) {a b : ℝ} (hseg : ∀ t ∈ Icc a b, γ t ∈ U)
    (hne : ∀ t ∈ Icc a b, f (γ t) ≠ 0) : ContinuousOn (fun t => logDeriv f (γ t)) (Icc a b) := by
  have : (fun t => logDeriv f (γ t)) = fun t => deriv f (γ t) / f (γ t) := rfl
  rw [this]
  exact ((hf.deriv hU).continuousOn.comp hγ.continuousOn hseg).div (hf.continuousOn.comp hγ.continuousOn hseg) hne

/-- **Côté vertical découpé** : intégrale = différence des logarithmes aux extrémités, corrigée des raccords internes. -/
theorem vertical_side (c : ℝ) (hc1 : c ≠ 1) (y : ℕ → ℝ) (z : ℕ → ℤ) (w : ℤ) :
    ∀ m : ℕ, (∀ k < m + 1, y k ≤ y (k + 1)) →
      (∀ k < m, z (k + 1) = z k ∨ z (k + 1) = z k + 1 ∨ z (k + 1) = z k - 1) →
      (∀ t ∈ Icc (y 0) (y (m + 1)), 0 < (I ^ w * (1 - ((c : ℂ) + (t : ℂ) * I))).re) →
      (∀ k < m + 1, ∀ t ∈ Icc (y k) (y (k + 1)), 0 < (I ^ z k * riemannZeta ((c : ℂ) + (t : ℂ) * I)).re) →
      I * ∫ t in y 0..y (m + 1), logDeriv zetaFactor ((c : ℂ) + (t : ℂ) * I) =
        log (I ^ w * I ^ z m * zetaFactor ((c : ℂ) + (y (m + 1) : ℂ) * I)) -
          log (I ^ w * I ^ z 0 * zetaFactor ((c : ℂ) + (y 0 : ℂ) * I)) -
          ((z m - z 0 : ℤ) : ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  have hU : ∀ t : ℝ, (c : ℂ) + (t : ℂ) * I ∈ {s : ℂ | s ≠ 1} := by
    intro t h; have := congrArg Complex.re h; simp at this; exact hc1 this
  -- un morceau
  have piece : ∀ (a b : ℝ) (zz : ℤ), a ≤ b →
      (∀ t ∈ Icc a b, 0 < (I ^ w * (1 - ((c : ℂ) + (t : ℂ) * I))).re) →
      (∀ t ∈ Icc a b, 0 < (I ^ zz * riemannZeta ((c : ℂ) + (t : ℂ) * I)).re) →
      I * ∫ t in a..b, logDeriv zetaFactor ((c : ℂ) + (t : ℂ) * I) =
        log (I ^ w * I ^ zz * zetaFactor ((c : ℂ) + (b : ℂ) * I)) -
          log (I ^ w * I ^ zz * zetaFactor ((c : ℂ) + (a : ℂ) * I)) := fun a b zz hab h1 h2 =>
    integral_logDeriv_vertical isOpen_ne_one zetaFactor_differentiableOn hab _ (fun t _ => hU t)
      (fun t ht => slit_point w zz _ (h1 t ht) (h2 t ht))
  have integ : ∀ (a b : ℝ) (zz : ℤ), a ≤ b →
      (∀ t ∈ Icc a b, 0 < (I ^ zz * riemannZeta ((c : ℂ) + (t : ℂ) * I)).re) →
      IntervalIntegrable (fun t : ℝ => logDeriv zetaFactor ((c : ℂ) + (t : ℂ) * I)) MeasureTheory.volume a b := by
    intro a b zz hab h2
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    refine continuousOn_logDeriv_comp (γ := fun t : ℝ => (c : ℂ) + (t : ℂ) * I) isOpen_ne_one
      zetaFactor_differentiableOn
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) (fun t _ => hU t) ?_
    intro t ht h0'
    have h0 : zetaFactor ((c : ℂ) + (t : ℂ) * I) = 0 := h0'
    have := h2 t ht
    rw [zetaFactor] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact hU t (by rw [sub_eq_zero] at h; exact h.symm)
    · rw [h, mul_zero] at this; simp at this
  intro m
  induction m with
  | zero =>
    intro hy _ hw hz
    have := piece (y 0) (y 1) (z 0) (hy 0 (by omega)) (fun t ht => hw t ht) (hz 0 (by omega))
    rw [this]; simp
  | succ m ih =>
    intro hy hzz hw hz
    have hy' : ∀ k < m + 1, y k ≤ y (k + 1) := fun k hk => hy k (by omega)
    have hmono : ∀ k ≤ m + 1, y 0 ≤ y k := by
      intro k hk
      induction k with
      | zero => exact le_rfl
      | succ k ihk => exact (ihk (by omega)).trans (hy k (by omega))
    have hle1 : y (m + 1) ≤ y (m + 2) := hy (m + 1) (by omega)
    have hw' : ∀ t ∈ Icc (y 0) (y (m + 1)), 0 < (I ^ w * (1 - ((c : ℂ) + (t : ℂ) * I))).re :=
      fun t ht => hw t ⟨ht.1, ht.2.trans hle1⟩
    have IH := ih hy' (fun k hk => hzz k (by omega)) hw' (fun k hk => hz k (by omega))
    have hP := piece (y (m + 1)) (y (m + 2)) (z (m + 1)) hle1
      (fun t ht => hw t ⟨(hmono (m + 1) le_rfl).trans ht.1, ht.2⟩) (hz (m + 1) (by omega))
    -- intégrabilité sur [y 0, y (m+1)] : morceau par morceau
    have hint : IntervalIntegrable (fun t : ℝ => logDeriv zetaFactor ((c : ℂ) + (t : ℂ) * I))
        MeasureTheory.volume (y 0) (y (m + 1)) := by
      have : ∀ j ≤ m + 1, IntervalIntegrable (fun t : ℝ => logDeriv zetaFactor ((c : ℂ) + (t : ℂ) * I))
          MeasureTheory.volume (y 0) (y j) := by
        intro j hj
        induction j with
        | zero => exact IntervalIntegrable.refl
        | succ j ihj =>
          exact (ihj (by omega)).trans (integ _ _ (z j) (hy j (by omega)) (hz j (by omega)))
      exact this (m + 1) le_rfl
    have hint2 := integ (y (m + 1)) (y (m + 2)) (z (m + 1)) hle1 (hz (m + 1) (by omega))
    rw [← intervalIntegral.integral_add_adjacent_intervals hint hint2, mul_add, IH, hP]
    -- raccord en y (m+1)
    set P : ℂ := (c : ℂ) + (y (m + 1) : ℂ) * I
    have hPw : 0 < (I ^ w * (1 - P)).re := hw _ ⟨hmono (m + 1) le_rfl, hle1⟩
    have hJ := point_junction w w (z m) (z (m + 1)) P (Or.inl rfl) (hzz m (by omega)) hPw
      (hz m (by omega) _ ⟨hy m (by omega), le_rfl⟩) hPw (hz (m + 1) (by omega) _ ⟨le_rfl, hle1⟩)
    push_cast at hJ ⊢
    linear_combination hJ

/-- **Côté horizontal découpé**. -/
theorem horizontal_side (c : ℝ) (hc0 : c ≠ 0) (x : ℕ → ℝ) (z : ℕ → ℤ) (w : ℤ) :
    ∀ m : ℕ, (∀ k < m + 1, x k ≤ x (k + 1)) →
      (∀ k < m, z (k + 1) = z k ∨ z (k + 1) = z k + 1 ∨ z (k + 1) = z k - 1) →
      (∀ t ∈ Icc (x 0) (x (m + 1)), 0 < (I ^ w * (1 - ((t : ℂ) + (c : ℂ) * I))).re) →
      (∀ k < m + 1, ∀ t ∈ Icc (x k) (x (k + 1)), 0 < (I ^ z k * riemannZeta ((t : ℂ) + (c : ℂ) * I)).re) →
      ∫ t in x 0..x (m + 1), logDeriv zetaFactor ((t : ℂ) + (c : ℂ) * I) =
        log (I ^ w * I ^ z m * zetaFactor ((x (m + 1) : ℂ) + (c : ℂ) * I)) -
          log (I ^ w * I ^ z 0 * zetaFactor ((x 0 : ℂ) + (c : ℂ) * I)) -
          ((z m - z 0 : ℤ) : ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  have hU : ∀ t : ℝ, (t : ℂ) + (c : ℂ) * I ∈ {s : ℂ | s ≠ 1} := by
    intro t h; have := congrArg Complex.im h; simp at this; exact hc0 this
  have piece : ∀ (a b : ℝ) (zz : ℤ), a ≤ b →
      (∀ t ∈ Icc a b, 0 < (I ^ w * (1 - ((t : ℂ) + (c : ℂ) * I))).re) →
      (∀ t ∈ Icc a b, 0 < (I ^ zz * riemannZeta ((t : ℂ) + (c : ℂ) * I)).re) →
      ∫ t in a..b, logDeriv zetaFactor ((t : ℂ) + (c : ℂ) * I) =
        log (I ^ w * I ^ zz * zetaFactor ((b : ℂ) + (c : ℂ) * I)) -
          log (I ^ w * I ^ zz * zetaFactor ((a : ℂ) + (c : ℂ) * I)) := fun a b zz hab h1 h2 =>
    integral_logDeriv_horizontal isOpen_ne_one zetaFactor_differentiableOn hab _ (fun t _ => hU t)
      (fun t ht => slit_point w zz _ (h1 t ht) (h2 t ht))
  have integ : ∀ (a b : ℝ) (zz : ℤ), a ≤ b →
      (∀ t ∈ Icc a b, 0 < (I ^ zz * riemannZeta ((t : ℂ) + (c : ℂ) * I)).re) →
      IntervalIntegrable (fun t : ℝ => logDeriv zetaFactor ((t : ℂ) + (c : ℂ) * I)) MeasureTheory.volume a b := by
    intro a b zz hab h2
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    refine continuousOn_logDeriv_comp (γ := fun t : ℝ => (t : ℂ) + (c : ℂ) * I) isOpen_ne_one
      zetaFactor_differentiableOn
      (Complex.continuous_ofReal.add continuous_const) (fun t _ => hU t) ?_
    intro t ht h0'
    have h0 : zetaFactor ((t : ℂ) + (c : ℂ) * I) = 0 := h0'
    have := h2 t ht
    rw [zetaFactor] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact hU t (by rw [sub_eq_zero] at h; exact h.symm)
    · rw [h, mul_zero] at this; simp at this
  intro m
  induction m with
  | zero =>
    intro hx _ hw hz
    have := piece (x 0) (x 1) (z 0) (hx 0 (by omega)) (fun t ht => hw t ht) (hz 0 (by omega))
    rw [this]; simp
  | succ m ih =>
    intro hx hzz hw hz
    have hx' : ∀ k < m + 1, x k ≤ x (k + 1) := fun k hk => hx k (by omega)
    have hmono : ∀ k ≤ m + 1, x 0 ≤ x k := by
      intro k hk
      induction k with
      | zero => exact le_rfl
      | succ k ihk => exact (ihk (by omega)).trans (hx k (by omega))
    have hle1 : x (m + 1) ≤ x (m + 2) := hx (m + 1) (by omega)
    have hw' : ∀ t ∈ Icc (x 0) (x (m + 1)), 0 < (I ^ w * (1 - ((t : ℂ) + (c : ℂ) * I))).re :=
      fun t ht => hw t ⟨ht.1, ht.2.trans hle1⟩
    have IH := ih hx' (fun k hk => hzz k (by omega)) hw' (fun k hk => hz k (by omega))
    have hP := piece (x (m + 1)) (x (m + 2)) (z (m + 1)) hle1
      (fun t ht => hw t ⟨(hmono (m + 1) le_rfl).trans ht.1, ht.2⟩) (hz (m + 1) (by omega))
    have hint : IntervalIntegrable (fun t : ℝ => logDeriv zetaFactor ((t : ℂ) + (c : ℂ) * I))
        MeasureTheory.volume (x 0) (x (m + 1)) := by
      have : ∀ j ≤ m + 1, IntervalIntegrable (fun t : ℝ => logDeriv zetaFactor ((t : ℂ) + (c : ℂ) * I))
          MeasureTheory.volume (x 0) (x j) := by
        intro j hj
        induction j with
        | zero => exact IntervalIntegrable.refl
        | succ j ihj =>
          exact (ihj (by omega)).trans (integ _ _ (z j) (hx j (by omega)) (hz j (by omega)))
      exact this (m + 1) le_rfl
    have hint2 := integ (x (m + 1)) (x (m + 2)) (z (m + 1)) hle1 (hz (m + 1) (by omega))
    rw [← intervalIntegral.integral_add_adjacent_intervals hint hint2, IH, hP]
    set P : ℂ := (x (m + 1) : ℂ) + (c : ℂ) * I
    have hPw : 0 < (I ^ w * (1 - P)).re := hw _ ⟨hmono (m + 1) le_rfl, hle1⟩
    have hJ := point_junction w w (z m) (z (m + 1)) P (Or.inl rfl) (hzz m (by omega)) hPw
      (hz m (by omega) _ ⟨hx m (by omega), le_rfl⟩) hPw (hz (m + 1) (by omega) _ ⟨le_rfl, hle1⟩)
    push_cast at hJ ⊢
    linear_combination hJ

end ZB
end RHV6Fresh
