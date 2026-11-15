/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.PerronPort.ZetaBounds

/-!
# Encadrement d'Euler–Maclaurin de `ζ` dans la bande (vérification (V1) du certificat d'E176)

Partie principale d'ordre un `eulerMaclaurinMain N s` (le `riemannZeta0` de rhv3_lean sans son intégrale de reste), borne
d'erreur d'ordre un réutilisée de rhv3_lean, puis borne FINE par annulation sur chaque intervalle unité :
`‖ζ(s) − main_N(s)‖ ≤ ‖s‖·‖s+1‖/12 · (N^{−σ−2} + N^{−σ−1}/(σ+1))`. Avec elle, `N = 10` suffit à `T = 15` (marge
numérique 0,22 sur seize sous-intervalles de `σ`), au lieu de `N = 10000` avec la borne d'ordre un.
-/

namespace RHV6Fresh

open Complex Set Filter MeasureTheory

/-- Partie principale de la formule d'Euler–Maclaurin d'ordre un (`riemannZeta0` de rhv3_lean sans son intégrale de reste). -/
noncomputable def eulerMaclaurinMain (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) + (- (N : ℂ) ^ (1 - s)) / (1 - s) + (- (N : ℂ) ^ (-s)) / 2

/-- Encadrement démontré de `ζ` dans la bande par sa partie principale d'Euler–Maclaurin : réutilise `Zeta0EqZeta` et
`ZetaBnd_aux1b` (rhv3_lean). Erreur `‖s‖·N^{−σ}/σ`, pour tout `σ > 0`. -/
theorem zeta_sub_eulerMaclaurinMain_le (N : ℕ) (hN : 1 ≤ N) {σ t : ℝ} (hσ : 0 < σ) (hs : (σ : ℂ) + t * I ≠ 1) :
    ‖riemannZeta ((σ : ℂ) + t * I) - eulerMaclaurinMain N ((σ : ℂ) + t * I)‖ ≤
      ‖(σ : ℂ) + t * I‖ * ((N : ℝ) ^ (-σ) / σ) := by
  rw [← Zeta0EqZeta (N := N) (by omega) (by simp [hσ]) hs]
  have h : riemannZeta0 N ((σ : ℂ) + t * I) - eulerMaclaurinMain N ((σ : ℂ) + t * I) =
      ((σ : ℂ) + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ : ℂ) + t * I) + 1) := by
    unfold riemannZeta0 eulerMaclaurinMain; ring
  rw [h, norm_mul]
  exact mul_le_mul_of_nonneg_left (ZetaBnd_aux1b N hN hσ) (norm_nonneg _)

/-- Non-annulation certifiée par la partie principale : si elle dépasse l'erreur démontrée, `ζ(σ + it) ≠ 0`. -/
theorem zeta_ne_zero_of_eulerMaclaurinMain (N : ℕ) (hN : 1 ≤ N) {σ t : ℝ} (hσ : 0 < σ) (hs : (σ : ℂ) + t * I ≠ 1)
    (hgt : ‖(σ : ℂ) + t * I‖ * ((N : ℝ) ^ (-σ) / σ) < ‖eulerMaclaurinMain N ((σ : ℂ) + t * I)‖) :
    riemannZeta ((σ : ℂ) + t * I) ≠ 0 := by
  intro h0
  have h := zeta_sub_eulerMaclaurinMain_le N hN hσ hs
  rw [h0, zero_sub, norm_neg] at h
  linarith

/-! ## Borne fine par annulation sur chaque intervalle unité -/

/-- Le profil `x ↦ x^{−(s+1)}` est `‖s+1‖·k^{−σ−2}`-lipschitzien sur `[k, k+1]`. -/
theorem cpow_neg_lipschitz_unit {s : ℂ} (hs : 0 < s.re) {k : ℝ} (hk : 1 ≤ k) {x y : ℝ}
    (hx : x ∈ Icc k (k + 1)) (hy : y ∈ Icc k (k + 1)) :
    ‖(y : ℂ) ^ (-(s + 1)) - (x : ℂ) ^ (-(s + 1))‖ ≤ ‖s + 1‖ * k ^ (-s.re - 2) * |y - x| := by
  have hne : -(s + 1) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hderiv : ∀ z ∈ Icc k (k + 1), HasDerivWithinAt (fun u : ℝ => (u : ℂ) ^ (-(s + 1)))
      (-(s + 1) * (z : ℂ) ^ (-(s + 1) - 1)) (Icc k (k + 1)) z := fun z hz =>
    (hasDerivAt_ofReal_cpow_const (by linarith [hz.1] : z ≠ 0) hne).hasDerivWithinAt
  have hbound : ∀ z ∈ Icc k (k + 1), ‖-(s + 1) * (z : ℂ) ^ (-(s + 1) - 1)‖ ≤ ‖s + 1‖ * k ^ (-s.re - 2) := by
    intro z hz
    have hz0 : 0 < z := by linarith [hz.1]
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hz0]
    have hre : (-(s + 1) - 1).re = -s.re - 2 := by simp; ring
    rw [hre]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith) hz.1 (by linarith))
      (norm_nonneg _)
  have := (convex_Icc k (k + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hx hy
  simpa [Real.norm_eq_abs] using this

theorem integral_sq_unit (k : ℝ) : ∫ x in k..k + 1, (x - (k + 1 / 2)) ^ 2 = 1 / 12 := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ 2), integral_pow]
  ring

theorem integral_center_unit (k : ℝ) : ∫ x in k..k + 1, ((k + 1 / 2) - x) = 0 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    intervalIntegral.integral_const, integral_id]
  simp; ring

theorem cpow_neg_continuousOn {s : ℂ} {k : ℝ} (hk : 0 < k) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-(s + 1))) (Icc k (k + 1)) := fun x hx =>
  (continuousAt_ofReal_cpow_const x (-(s + 1)) (Or.inr (by linarith [hx.1]))).continuousWithinAt

theorem unit_piece_bound {s : ℂ} (hs : 0 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    ‖∫ x in (k : ℝ)..(k : ℝ) + 1, (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      ‖s + 1‖ * (k : ℝ) ^ (-s.re - 2) / 12 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  set c : ℝ := (k : ℝ) + 1 / 2 with hc
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (-(s + 1)) with hg
  have hle : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hgc : ContinuousOn g (uIcc (k : ℝ) ((k : ℝ) + 1)) := by
    rw [uIcc_of_le hle]; exact cpow_neg_continuousOn hk0
  have hI1 : IntervalIntegrable (fun x : ℝ => ((c - x : ℝ) : ℂ) * g x) volume (k : ℝ) ((k : ℝ) + 1) :=
    ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).continuousOn.mul hgc).intervalIntegrable
  have hI2 : IntervalIntegrable (fun x : ℝ => ((c - x : ℝ) : ℂ) * g c) volume (k : ℝ) ((k : ℝ) + 1) :=
    ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul continuous_const).intervalIntegrable _ _
  have h1 : ∫ x in (k : ℝ)..(k : ℝ) + 1, (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)
      = ∫ x in (k : ℝ)..(k : ℝ) + 1, ((c - x : ℝ) : ℂ) * g x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(Set.countable_singleton ((k : ℝ) + 1)).ae_notMem volume] with x hx hmem
    rw [Set.uIoc_of_le hle] at hmem
    have hlt : x < (k : ℝ) + 1 := lt_of_le_of_ne hmem.2 (by simpa using hx)
    have hfl : ⌊x⌋ = (k : ℤ) := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [hmem.1]
    simp only [hg, hc, hfl, cpow_neg, div_eq_mul_inv]; push_cast; ring
  have h2 : ∫ x in (k : ℝ)..(k : ℝ) + 1, ((c - x : ℝ) : ℂ) * g c = 0 := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, hc,
      integral_center_unit]
    simp
  have h3 : ∫ x in (k : ℝ)..(k : ℝ) + 1, ((c - x : ℝ) : ℂ) * g x
      = ∫ x in (k : ℝ)..(k : ℝ) + 1, ((c - x : ℝ) : ℂ) * (g x - g c) := by
    have := intervalIntegral.integral_sub hI1 hI2
    simp only [mul_sub]
    rw [this, h2, sub_zero]
  rw [h1, h3]
  have hM : 0 ≤ ‖s + 1‖ * (k : ℝ) ^ (-s.re - 2) := by positivity
  calc ‖∫ x in (k : ℝ)..(k : ℝ) + 1, ((c - x : ℝ) : ℂ) * (g x - g c)‖
      ≤ ∫ x in (k : ℝ)..(k : ℝ) + 1, (‖s + 1‖ * (k : ℝ) ^ (-s.re - 2)) * (x - c) ^ 2 := by
        apply intervalIntegral.norm_integral_le_of_norm_le hle
        · apply Filter.Eventually.of_forall
          intro x hx
          have hxI : x ∈ Icc (k : ℝ) ((k : ℝ) + 1) := ⟨hx.1.le, hx.2⟩
          have hcI : c ∈ Icc (k : ℝ) ((k : ℝ) + 1) := ⟨by rw [hc]; linarith, by rw [hc]; linarith⟩
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hL := cpow_neg_lipschitz_unit hs hk1 hcI hxI
          calc |c - x| * ‖g x - g c‖ ≤ |c - x| * (‖s + 1‖ * (k : ℝ) ^ (-s.re - 2) * |x - c|) :=
                mul_le_mul_of_nonneg_left hL (abs_nonneg _)
            _ = (‖s + 1‖ * (k : ℝ) ^ (-s.re - 2)) * (x - c) ^ 2 := by
                rw [abs_sub_comm c x, ← sq_abs (x - c)]; ring
        · exact (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).intervalIntegrable _ _
    _ = ‖s + 1‖ * (k : ℝ) ^ (-s.re - 2) / 12 := by
        rw [intervalIntegral.integral_const_mul, hc, integral_sq_unit]; ring

theorem rpow_sum_le_integral_bound {N : ℝ} (hN : 1 ≤ N) {σ : ℝ} (hσ : 0 < σ) (K : ℕ) :
    ∑ i ∈ Finset.range K, (N + i) ^ (-σ - 2) ≤ N ^ (-σ - 2) + N ^ (-σ - 1) / (σ + 1) := by
  have hN0 : 0 < N := by linarith
  have hstep : ∑ i ∈ Finset.range K, (N + i) ^ (-σ - 2) ≤
      ∑ i ∈ Finset.range (K + 1), (N + i) ^ (-σ - 2) := by
    rw [Finset.sum_range_succ]
    have : 0 ≤ (N + K) ^ (-σ - 2) := Real.rpow_nonneg (by positivity) _
    linarith
  rw [Finset.sum_range_succ'] at hstep
  simp only [Nat.cast_zero, add_zero] at hstep
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ - 2)) (Icc N (N + K)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hsum := hanti.sum_le_integral
  have hint : ∫ x in N..N + K, x ^ (-σ - 2) = (N ^ (-σ - 1) - (N + K) ^ (-σ - 1)) / (σ + 1) := by
    rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
    · have h1 : -σ - 2 + 1 = -σ - 1 := by ring
      rw [h1]
      have h2 : (-σ - 1) = -(σ + 1) := by ring
      rw [h2, div_neg, ← neg_div]; ring_nf
    · rw [Set.uIcc_of_le (by have : (0:ℝ) ≤ K := Nat.cast_nonneg K; linarith)]
      intro h; linarith [h.1]
  have hpos : 0 ≤ (N + K) ^ (-σ - 1) / (σ + 1) := by
    apply div_nonneg (Real.rpow_nonneg (by positivity) _); linarith
  have hsum' : ∑ i ∈ Finset.range K, (N + ((i + 1 : ℕ) : ℝ)) ^ (-σ - 2) ≤
      N ^ (-σ - 1) / (σ + 1) := by
    calc _ ≤ ∫ x in N..N + K, x ^ (-σ - 2) := hsum
      _ = (N ^ (-σ - 1) - (N + K) ^ (-σ - 1)) / (σ + 1) := hint
      _ ≤ N ^ (-σ - 1) / (σ + 1) := by rw [sub_div]; linarith
  have hcast : ∀ i : ℕ, (N + ((i + 1 : ℕ) : ℝ)) = N + ((i : ℝ) + 1) := fun i => by push_cast; ring
  simp only [hcast] at hsum'
  have : ∑ i ∈ Finset.range K, (N + ((i + 1 : ℕ) : ℝ)) ^ (-σ - 2)
      = ∑ i ∈ Finset.range K, (N + (↑i + 1)) ^ (-σ - 2) := by simp only [hcast]
  push_cast at hstep
  linarith

theorem fine_tail_integral_bound {s : ℂ} (hs : 0 < s.re) (N : ℕ) (hN : 1 ≤ N) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      ‖s + 1‖ / 12 * ((N : ℝ) ^ (-s.re - 2) + (N : ℝ) ^ (-s.re - 1) / (s.re + 1)) := by
  set F : ℝ → ℂ := fun x => (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) with hF
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hFi : IntegrableOn F (Ioi (N : ℝ)) := by
    have := integrableOn_of_Zeta0_fun (N := N) (s := s) (by omega) hs
    convert this using 1
    funext x; simp only [hF, div_eq_mul_inv, cpow_neg]
  have hlim := intervalIntegral_tendsto_integral_Ioi (N : ℝ) hFi
    (b := fun K : ℕ => (N : ℝ) + K) (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  refine le_of_tendsto' hlim.norm (fun K => ?_)
  have hint : ∀ k < K, IntervalIntegrable F volume ((N : ℝ) + k) ((N : ℝ) + (k + 1 : ℕ)) := by
    intro k _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)]
    exact hFi.mono_set (fun x hx => by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      exact (show (N : ℝ) < x by linarith [hx.1]))
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (N : ℝ) + k) hint
  simp only [Nat.cast_zero, add_zero] at hsplit
  rw [← hsplit]
  calc ‖∑ k ∈ Finset.range K, ∫ x in (N : ℝ) + k..(N : ℝ) + (k + 1 : ℕ), F x‖
      ≤ ∑ k ∈ Finset.range K, ‖∫ x in (N : ℝ) + k..(N : ℝ) + (k + 1 : ℕ), F x‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range K, ‖s + 1‖ * ((N : ℝ) + k) ^ (-s.re - 2) / 12 := by
        apply Finset.sum_le_sum; intro k _
        have := unit_piece_bound hs (N + k) (by omega)
        simp only [hF]
        push_cast at this ⊢
        simpa [add_assoc] using this
    _ = ‖s + 1‖ / 12 * ∑ k ∈ Finset.range K, ((N : ℝ) + k) ^ (-s.re - 2) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ ‖s + 1‖ / 12 * ((N : ℝ) ^ (-s.re - 2) + (N : ℝ) ^ (-s.re - 1) / (s.re + 1)) :=
        mul_le_mul_of_nonneg_left (rpow_sum_le_integral_bound hN1 hs K) (by positivity)

/-- **Borne fine d'Euler–Maclaurin** : `‖ζ(s) − main_N(s)‖ ≤ ‖s‖·‖s+1‖/12·(N^{−σ−2} + N^{−σ−1}/(σ+1))`. -/
theorem zeta_sub_eulerMaclaurinMain_le_fine (N : ℕ) (hN : 1 ≤ N) {σ t : ℝ} (hσ : 0 < σ)
    (hs : (σ : ℂ) + t * I ≠ 1) :
    ‖riemannZeta ((σ : ℂ) + t * I) - eulerMaclaurinMain N ((σ : ℂ) + t * I)‖ ≤
      ‖(σ : ℂ) + t * I‖ * ‖(σ : ℂ) + t * I + 1‖ / 12 *
        ((N : ℝ) ^ (-σ - 2) + (N : ℝ) ^ (-σ - 1) / (σ + 1)) := by
  rw [← Zeta0EqZeta (N := N) (by omega) (by simp [hσ]) hs]
  have h : riemannZeta0 N ((σ : ℂ) + t * I) - eulerMaclaurinMain N ((σ : ℂ) + t * I) =
      ((σ : ℂ) + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ : ℂ) + t * I) + 1) := by
    unfold riemannZeta0 eulerMaclaurinMain; ring
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  have hb := fine_tail_integral_bound (s := (σ : ℂ) + t * I) (by rw [hre]; exact hσ) N hN
  rw [hre] at hb
  rw [h, norm_mul, mul_div_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by simpa [mul_div_assoc'] using hb) (norm_nonneg _)


/-- Non-annulation certifiée par la borne fine : si la partie principale dépasse l'erreur fine, `ζ(σ + it) ≠ 0`. -/
theorem zeta_ne_zero_of_eulerMaclaurinMain_fine (N : ℕ) (hN : 1 ≤ N) {σ t : ℝ} (hσ : 0 < σ)
    (hs : (σ : ℂ) + t * I ≠ 1)
    (hgt : ‖(σ : ℂ) + t * I‖ * ‖(σ : ℂ) + t * I + 1‖ / 12 *
        ((N : ℝ) ^ (-σ - 2) + (N : ℝ) ^ (-σ - 1) / (σ + 1)) < ‖eulerMaclaurinMain N ((σ : ℂ) + t * I)‖) :
    riemannZeta ((σ : ℂ) + t * I) ≠ 0 := by
  intro h0
  have h := zeta_sub_eulerMaclaurinMain_le_fine N hN hσ hs
  rw [h0, zero_sub, norm_neg] at h
  linarith

#print axioms zeta_sub_eulerMaclaurinMain_le_fine
#print axioms zeta_ne_zero_of_eulerMaclaurinMain_fine

end RHV6Fresh
