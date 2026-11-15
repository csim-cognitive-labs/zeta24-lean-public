/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.LocalWindowTransmission
import RHV6Fresh.Terminal.OnCrossReadings

/-!
# Compensation sur une fenêtre grammaticale authentique (auteur, 2026-10-11)

Tentative de l'auteur : sur une fenêtre d'événements premiers authentiques, une même lecture finie
`L_λ(f) = Σ_r λ_r f(x_r)` et une même borne `B` avec `|L_λ(Q)| ≤ B` et `|L_λ(Y − F)| > B`, où `Y` est le retrait de
l'historique (`historyRemoved`), `F` le groupe d'arrivée (`groupSignal`, fibre complète, multiplicités) et `Q` le complément
entier (`followingSum`, tous les membres suivants).

* §1 fenêtre : `x_r = p_{n₀+r}` (premiers authentiques), poids grammaticaux = écarts premiers, coefficients accordés en
  phase sur une hauteur `T` : `λ_r = c_r·x_r^{−iT}` (dépendance en `T` explicite et symbolique).
* §2 VÉRIFICATION DE COMPOSITION (aucune avancée sur les estimations) : `L(Y − F) = L(Q)` exactement
  (`window_same_quantity`) ; les deux inégalités ensemble sont contradictoires (`separation_contradiction`) : elles portent
  sur le même nombre, chacune doit donc venir d'une expression différente.
* §3 développement DIRECT du retrait par les poids premiers exacts : `L(Y) = Σ_{n<N} Λ(n)·Φ_λ(n) − L(fond) − L(P_H)`, avec le
  filtre `Φ_λ(n) = Σ_{r : n < x_r} λ_r (1 − n/x_r)` (`historyRemoved_filtered_primes`) ; aucune borne substituée.
* §4 signal du groupe sur la FIBRE COMPLÈTE : `L(F) = Σ_σ w_σ·Σ_r λ_r x_r^σ`, `w_σ = −m_σ/(σ(σ+1))` (coefficient propre de
  chaque membre, multiplicité comprise) (`groupSignal_eq_tsum_fiber`), découpé en moitié supérieure et moitié conjuguée.
* §5 filtre accordé : sur un passage consécutif, tout membre de la fibre a la hauteur `T_l` ; avec `λ_r = c_r x_r^{−iT_l}`,
  chaque membre supérieur donne `w_σ·Σ_r c_r x_r^{β_σ}` (phases de rotation alignées, coefficients propres conservés) et
  `Re w_σ > 0` dès `β(β+1) < T²` : AUCUNE annulation dans la moitié supérieure, minoration par n'importe quel membre
  (`upper_fiber_minoration`). La moitié conjuguée est la somme oscillante `Σ_σ w_σ Σ_r c_r x_r^{β_σ} x_r^{−2iT_l}`
  (`lower_term_eq`), non contrôlée.
* §6 composition : `‖Y‖ + marge + ‖moitié conjuguée‖ < Re w_l·Σ c_r x_r^{β_l}` ⟹ `False` (`matched_window_closes`) ;
  condition nécessaire avec la marge triangulaire : `budget(T_l) < ‖w_l‖` (`matched_separation_requires`).

Tout est démontré (axiomes standard). Les deux estimations (majoration non triangulaire du complément filtré, minoration de
la somme filtrée signée au-delà de la moitié conjuguée et du retrait) ne sont PAS démontrées. La séparation de §6 est une
CONDITION SUFFISANTE NON DÉMONTRÉE ; elle ne constitue pas une solution acquise (ordre correctif de l'auteur, 2026-10-11).
Composition généralisée, minoration sur la paire arrivée + miroir, fenêtre du passage : `GrammarWindowEstimate.lean`.
-/

namespace RHV6Fresh

open RHV3Lean Complex

/-! ## 1. Fenêtre d'événements premiers et coefficients -/

/-- Fenêtre des événements premiers authentiques `p_{n₀}, …, p_{n₀+m−1}`. -/
noncomputable def primeWindow (n₀ m : ℕ) : Fin m → ℝ := fun r => (fnPrimeAtRank (n₀ + r) : ℝ)

theorem primeWindow_gt_one (n₀ m : ℕ) : ∀ r, 1 < primeWindow n₀ m r := fun r => by
  unfold primeWindow; exact_mod_cast (thm_primeAtRank_isPrime (n₀ + r)).one_lt

/-- Poids grammaticaux : l'écart premier `g_{n₀+r} = p_{n₀+r+1} − p_{n₀+r}` de chaque événement. -/
noncomputable def gapWeights (n₀ m : ℕ) : Fin m → ℝ :=
  fun r => (fnPrimeAtRank (n₀ + r + 1) : ℝ) - fnPrimeAtRank (n₀ + r)

theorem gapWeights_pos (n₀ m : ℕ) : ∀ r, 0 < gapWeights n₀ m r := fun r => by
  unfold gapWeights
  have := thm_primeAtRank_strictMono (Nat.lt_succ_self (n₀ + r))
  rw [sub_pos]; exact_mod_cast this

/-- Coefficients accordés en phase sur la hauteur `T` : `λ_r = c_r·x_r^{−iT}`. -/
noncomputable def phaseMatched (T : ℝ) {m : ℕ} (c x : Fin m → ℝ) : Fin m → ℂ :=
  fun r => (c r : ℂ) * (x r : ℂ) ^ (-(T : ℂ) * I)

theorem phaseMatched_norm (T : ℝ) {m : ℕ} (c x : Fin m → ℝ) (hx : ∀ r, 0 < x r) (r : Fin m) :
    ‖phaseMatched T c x r‖ = |c r| := by
  unfold phaseMatched
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hx r)]
  simp

/-! ## 2. Identité et lemme de contradiction (vérification de composition) -/

/-- **Même nombre** : `L(Y − F) = L(Q)` exactement. -/
theorem window_same_quantity (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    historyRemoved H x lam - groupSignal H H' x lam = ∑ r, lam r * followingSum H' (x r) := by
  rw [window_exact_split H H' x lam hx]; ring

/-- **Lemme de contradiction** : une majoration de `L(Q)` et une minoration de `L(Y − F)` par la même borne sont
incompatibles. Vérifie la composition ; ne démontre aucune des deux estimations. -/
theorem separation_contradiction (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) {B : ℝ}
    (hQ : ‖∑ r, lam r * followingSum H' (x r)‖ ≤ B)
    (hYF : B < ‖historyRemoved H x lam - groupSignal H H' x lam‖) : False := by
  rw [window_same_quantity H H' x lam hx] at hYF; linarith

/-! ## 3. Développement direct du retrait par les poids premiers exacts -/

/-- Filtre premier de la lecture : `Φ_λ(n) = Σ_{r : n < ⌈x_r⌉} λ_r (1 − n/x_r)`. -/
noncomputable def primeFilter {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (n : ℕ) : ℂ :=
  ∑ r, if n < ⌈x r⌉₊ then lam r * (1 - (n : ℂ) / (x r : ℂ)) else 0

/-- **Somme de von Mangoldt filtrée** : `Σ_r λ_r Σ_{n<x_r} Λ(n)(1 − n/x_r) = Σ_{n<N} Λ(n) Φ_λ(n)`. -/
theorem filtered_vonMangoldt {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (N : ℕ) (hN : ∀ r, ⌈x r⌉₊ ≤ N) :
    ∑ r, lam r * smoothedVonMangoldtSum (x r) =
      ∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n : ℂ) * primeFilter x lam n := by
  unfold smoothedVonMangoldtSum primeFilter
  have h : ∀ r, lam r * ∑ n ∈ Finset.range ⌈x r⌉₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) * (1 - (n : ℂ) / (x r : ℂ)) =
      ∑ n ∈ Finset.range N, (if n < ⌈x r⌉₊ then
        (ArithmeticFunction.vonMangoldt n : ℂ) * (lam r * (1 - (n : ℂ) / (x r : ℂ))) else 0) := by
    intro r
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.mul_sum]
    have hf : (Finset.range N).filter (fun n => n < ⌈x r⌉₊) = Finset.range ⌈x r⌉₊ := by
      ext n; simp only [Finset.mem_filter, Finset.mem_range]; have := hN r; omega
    rw [hf]; exact Finset.sum_congr rfl fun n _ => by ring
  rw [Finset.sum_congr rfl fun r _ => h r, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

/-- **Retrait développé par les poids premiers exacts** : `L(Y) = Σ_{n<N} Λ(n)Φ_λ(n) − L(fond) − L(P_H)`. -/
theorem historyRemoved_filtered_primes (H : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (N : ℕ)
    (hN : ∀ r, ⌈x r⌉₊ ≤ N) :
    historyRemoved H x lam =
      ∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n : ℂ) * primeFilter x lam n
        - ∑ r, lam r * smoothedZeroBackground (x r) - ∑ r, lam r * precedingSum H (x r) := by
  rw [historyRemoved_prime_events, ← filtered_vonMangoldt x lam N hN]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- Instance : sur la fenêtre premières `p_{n₀}, …`, la coupure `N = p_{n₀+m}` contient tous les événements. -/
theorem primeWindow_ceil_le (n₀ m : ℕ) : ∀ r, ⌈primeWindow n₀ m r⌉₊ ≤ fnPrimeAtRank (n₀ + m) := fun r => by
  unfold primeWindow
  rw [Nat.ceil_natCast]
  exact (thm_primeAtRank_strictMono (by omega : n₀ + (r : ℕ) < n₀ + m)).le

/-! ## 4. Signal du groupe sur la fibre complète -/

theorem fiber_term_summable (H H' : ℝ) {x : ℝ} (hx : 1 < x) :
    Summable fun σ : ExplicitIndex => fiberWeight H H' σ * (x : ℂ) ^ (σ : ℂ) := by
  have hx0 : 0 < x := lt_trans one_pos hx
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun σ => ?_)
    ((fiberWeight_norm_summable H H').mul_right x))
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc x ^ (σ : ℂ).re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (explicitIndex_re_le_one σ)
    _ = x := Real.rpow_one x

/-- Terme filtré d'un membre de la fibre : `w_σ·Σ_r λ_r x_r^σ` (coefficient propre, multiplicité comprise). -/
noncomputable def fiberFiltered (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (σ : ExplicitIndex) : ℂ :=
  fiberWeight H H' σ * ∑ r, lam r * (x r : ℂ) ^ (σ : ℂ)

theorem fiberFiltered_eq_sum (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (σ : ExplicitIndex) :
    fiberFiltered H H' x lam σ = ∑ r, lam r * (fiberWeight H H' σ * (x r : ℂ) ^ (σ : ℂ)) := by
  unfold fiberFiltered; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring

theorem fiberFiltered_summable (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    Summable (fiberFiltered H H' x lam) := by
  have h : Summable fun σ : ExplicitIndex => ∑ r, lam r * (fiberWeight H H' σ * (x r : ℂ) ^ (σ : ℂ)) :=
    summable_sum fun r _ => (fiber_term_summable H H' (hx r)).mul_left (lam r)
  exact h.congr fun σ => (fiberFiltered_eq_sum H H' x lam σ).symm

/-- **Signal du groupe = série sur la fibre complète** : `L(F) = Σ_σ w_σ·Σ_r λ_r x_r^σ`. -/
theorem groupSignal_eq_tsum_fiber (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    groupSignal H H' x lam = ∑' σ, fiberFiltered H H' x lam σ := by
  unfold groupSignal
  simp_rw [fiberFiltered_eq_sum]
  rw [Summable.tsum_finsetSum fun r _ => (fiber_term_summable H H' (hx r)).mul_left (lam r)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [nextFiberSum_eq_tsum H H' (hx r), ← tsum_mul_left]

/-- Moitié supérieure (`Im σ > 0`) et moitié conjuguée (`Im σ ≤ 0`) de la fibre filtrée. -/
noncomputable def upperFiltered (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (σ : ExplicitIndex) : ℂ :=
  if 0 < (σ : ℂ).im then fiberFiltered H H' x lam σ else 0

noncomputable def lowerFiltered (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (σ : ExplicitIndex) : ℂ :=
  if 0 < (σ : ℂ).im then 0 else fiberFiltered H H' x lam σ

theorem upperFiltered_summable (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    Summable (upperFiltered H H' x lam) :=
  Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun σ => by unfold upperFiltered; split_ifs <;> simp)
    (fiberFiltered_summable H H' x lam hx).norm)

theorem lowerFiltered_summable (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    Summable (lowerFiltered H H' x lam) :=
  Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun σ => by unfold lowerFiltered; split_ifs <;> simp)
    (fiberFiltered_summable H H' x lam hx).norm)

/-- **Découpage exact** : `L(F) = moitié supérieure + moitié conjuguée`. -/
theorem groupSignal_split (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    groupSignal H H' x lam = ∑' σ, upperFiltered H H' x lam σ + ∑' σ, lowerFiltered H H' x lam σ := by
  rw [groupSignal_eq_tsum_fiber H H' x lam hx,
    ← (upperFiltered_summable H H' x lam hx).tsum_add (lowerFiltered_summable H H' x lam hx)]
  refine tsum_congr fun σ => ?_
  unfold upperFiltered lowerFiltered; split_ifs <;> simp

/-! ## 5. Filtre accordé en phase sur la fibre d'un passage consécutif -/

/-- `c·x^{−iT}·x^σ = c·x^{σ − iT}`. -/
theorem phaseMatched_cpow {x : ℝ} (hx : 0 < x) (T c : ℝ) (σ : ℂ) :
    (c : ℂ) * (x : ℂ) ^ (-(T : ℂ) * I) * (x : ℂ) ^ σ = (c : ℂ) * (x : ℂ) ^ (σ - (T : ℂ) * I) := by
  rw [mul_assoc, ← Complex.cpow_add _ _ (by exact_mod_cast hx.ne')]
  congr 2; ring

/-- **Membre supérieur de hauteur `T`** : la rotation est retirée, il reste `c·x^{β_σ}` réel. -/
theorem upper_aligned {x : ℝ} (hx : 0 < x) {T : ℝ} (c : ℝ) {σ : ℂ} (hσ : σ.im = T) :
    (c : ℂ) * (x : ℂ) ^ (-(T : ℂ) * I) * (x : ℂ) ^ σ = ((c * x ^ σ.re : ℝ) : ℂ) := by
  rw [phaseMatched_cpow hx,
    show σ - (T : ℂ) * I = ((σ.re : ℝ) : ℂ) by apply Complex.ext <;> simp [hσ],
    ← Complex.ofReal_cpow hx.le]
  push_cast; ring

/-- **Membre conjugué de hauteur `−T`** : il reste `c·x^{β_σ}·x^{−2iT}` (oscillation de fréquence `2T`). -/
theorem lower_oscillating {x : ℝ} (hx : 0 < x) {T : ℝ} (c : ℝ) {σ : ℂ} (hσ : σ.im = -T) :
    (c : ℂ) * (x : ℂ) ^ (-(T : ℂ) * I) * (x : ℂ) ^ σ =
      ((c * x ^ σ.re : ℝ) : ℂ) * (x : ℂ) ^ (-(2 * T : ℂ) * I) := by
  rw [phaseMatched_cpow hx,
    show σ - (T : ℂ) * I = ((σ.re : ℝ) : ℂ) + (-(2 * T : ℂ) * I) by apply Complex.ext <;> simp [hσ]; ring,
    Complex.cpow_add _ _ (by exact_mod_cast hx.ne'), ← Complex.ofReal_cpow hx.le]
  push_cast; ring

/-- **Coefficient propre d'un membre supérieur** : `Re(−m/(σ(σ+1))) ≥ 0` dès `β(β+1) < T²`. -/
theorem upper_weight_re_nonneg {σ : ℂ} (hT : σ.re * (σ.re + 1) < σ.im ^ 2) (m : ℕ) :
    0 ≤ (-(m : ℂ) / (σ * (σ + 1))).re := by
  have hre : (σ * (σ + 1)).re = σ.re * (σ.re + 1) - σ.im ^ 2 := by
    simp [Complex.mul_re]; ring
  have hns : 0 ≤ Complex.normSq (σ * (σ + 1)) := Complex.normSq_nonneg _
  rw [Complex.div_re]
  simp only [Complex.neg_re, Complex.natCast_re, Complex.neg_im, Complex.natCast_im, neg_zero, zero_mul,
    zero_div, add_zero, hre]
  apply div_nonneg _ hns
  have : σ.re * (σ.re + 1) - σ.im ^ 2 < 0 := by linarith
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- Poids de fibre non nul ⟹ hauteur dans la fibre. -/
theorem fiberWeight_ne_zero_mem {H H' : ℝ} (hHH' : H ≤ H') {σ : ExplicitIndex} (h : fiberWeight H H' σ ≠ 0) :
    H < |(σ : ℂ).im| ∧ |(σ : ℂ).im| ≤ H' := by
  unfold fiberWeight precedingWeight at h
  by_cases h1 : H' < |(σ : ℂ).im|
  · exact (h (by rw [if_pos h1, if_pos (lt_of_le_of_lt hHH' h1), sub_self])).elim
  by_cases h2 : H < |(σ : ℂ).im|
  · exact ⟨h2, not_lt.mp h1⟩
  · exact (h (by rw [if_neg h1, if_neg h2, sub_self])).elim

/-- Dans la fibre, le poids est le coefficient propre `−m_σ/(σ(σ+1))`. -/
theorem fiberWeight_of_mem {H H' : ℝ} {σ : ExplicitIndex} (h1 : H < |(σ : ℂ).im|) (h2 : |(σ : ℂ).im| ≤ H') :
    fiberWeight H H' σ = -(zetaZeroMultiplicity (σ : ℂ) : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1)) := by
  unfold fiberWeight precedingWeight
  rw [if_neg (not_lt.mpr h2), if_pos h1, sub_zero]

/-- **Membre supérieur de la fibre sous le filtre accordé** : `w_σ·Σ_r c_r x_r^{β_σ}`. -/
theorem upper_term_eq {H H' : ℝ} (hHH' : H ≤ H')
    (hFib : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' → |(σ : ℂ).im| = H')
    {m : ℕ} (c x : Fin m → ℝ) (hx : ∀ r, 1 < x r) (σ : ExplicitIndex) (hσ : 0 < (σ : ℂ).im) :
    upperFiltered H H' x (phaseMatched H' c x) σ =
      fiberWeight H H' σ * ((∑ r, c r * x r ^ (σ : ℂ).re : ℝ) : ℂ) := by
  unfold upperFiltered fiberFiltered
  rw [if_pos hσ]
  by_cases h0 : fiberWeight H H' σ = 0
  · rw [h0, zero_mul, zero_mul]
  obtain ⟨h1, h2⟩ := fiberWeight_ne_zero_mem hHH' h0
  have hIm : (σ : ℂ).im = H' := by rw [← hFib σ h1 h2, abs_of_pos hσ]
  congr 1
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold phaseMatched
  rw [upper_aligned (lt_trans one_pos (hx r)) (c r) hIm]; push_cast; ring

/-- **Membre conjugué de la fibre sous le filtre accordé** : `w_σ·Σ_r c_r x_r^{β_σ} x_r^{−2iT}`. -/
theorem lower_term_eq {H H' : ℝ} (hHH' : H ≤ H')
    (hFib : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' → |(σ : ℂ).im| = H')
    {m : ℕ} (c x : Fin m → ℝ) (hx : ∀ r, 1 < x r) (σ : ExplicitIndex) (hσ : (σ : ℂ).im ≤ 0) :
    lowerFiltered H H' x (phaseMatched H' c x) σ =
      fiberWeight H H' σ * ∑ r, ((c r * x r ^ (σ : ℂ).re : ℝ) : ℂ) * (x r : ℂ) ^ (-(2 * H' : ℂ) * I) := by
  unfold lowerFiltered fiberFiltered
  rw [if_neg (not_lt.mpr hσ)]
  by_cases h0 : fiberWeight H H' σ = 0
  · rw [h0, zero_mul, zero_mul]
  obtain ⟨h1, h2⟩ := fiberWeight_ne_zero_mem hHH' h0
  have hIm : (σ : ℂ).im = -H' := by
    have := hFib σ h1 h2; rw [abs_of_nonpos hσ] at this; linarith
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold phaseMatched
  rw [lower_oscillating (lt_trans one_pos (hx r)) (c r) hIm]

/-- **Minoration de la moitié supérieure, phases traitées** : sous le filtre accordé (`c_r ≥ 0`), chaque membre supérieur
de la fibre contribue `Re w_σ·Σ_r c_r x_r^{β_σ} ≥ 0` (aucune annulation, fibre complète, multiplicités) ; la partie réelle
de la moitié supérieure est donc au moins celle de n'importe quel membre. -/
theorem upper_fiber_minoration {H H' : ℝ} (hHH' : H ≤ H')
    (hFib : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' → |(σ : ℂ).im| = H')
    (hT : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' →
      (σ : ℂ).re * ((σ : ℂ).re + 1) < (σ : ℂ).im ^ 2)
    {m : ℕ} (c x : Fin m → ℝ) (hc : ∀ r, 0 ≤ c r) (hx : ∀ r, 1 < x r)
    (σ₀ : ExplicitIndex) (h0 : 0 < (σ₀ : ℂ).im) (h1 : H < |(σ₀ : ℂ).im|) (h2 : |(σ₀ : ℂ).im| ≤ H') :
    (-(zetaZeroMultiplicity (σ₀ : ℂ) : ℂ) / ((σ₀ : ℂ) * ((σ₀ : ℂ) + 1))).re * ∑ r, c r * x r ^ (σ₀ : ℂ).re ≤
      (∑' σ, upperFiltered H H' x (phaseMatched H' c x) σ).re := by
  have hs := upperFiltered_summable H H' x (phaseMatched H' c x) hx
  rw [Complex.re_tsum hs]
  have hnn : ∀ σ, 0 ≤ (upperFiltered H H' x (phaseMatched H' c x) σ).re := by
    intro σ
    by_cases hσ : 0 < (σ : ℂ).im
    · rw [upper_term_eq hHH' hFib c x hx σ hσ, Complex.re_mul_ofReal]
      by_cases h0' : fiberWeight H H' σ = 0
      · rw [h0', Complex.zero_re, zero_mul]
      obtain ⟨a1, a2⟩ := fiberWeight_ne_zero_mem hHH' h0'
      rw [fiberWeight_of_mem a1 a2]
      exact mul_nonneg (upper_weight_re_nonneg (hT σ a1 a2) _)
        (Finset.sum_nonneg fun r _ => mul_nonneg (hc r) (Real.rpow_nonneg (by linarith [hx r]) _))
    · unfold upperFiltered; rw [if_neg hσ, Complex.zero_re]
  have hsr : Summable fun σ => (upperFiltered H H' x (phaseMatched H' c x) σ).re := Complex.reCLM.summable hs
  have key := hsr.le_tsum σ₀ (fun σ _ => hnn σ)
  rw [upper_term_eq hHH' hFib c x hx σ₀ h0, fiberWeight_of_mem h1 h2, Complex.re_mul_ofReal] at key
  exact key

/-! ## 6. Composition et condition nécessaire -/

/-- **Composition** : si le retrait, la marge du complément et la moitié conjuguée restent sous la minoration de la moitié
supérieure par un membre `σ₀` de la fibre, contradiction. L'antécédent `hsep` est une condition suffisante NON démontrée ;
la marge triangulaire n'en est qu'un cas (forme générale : `window_closes_of_bounds`). -/
theorem matched_window_closes {H H' : ℝ} (hHH' : H ≤ H')
    (hFib : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' → |(σ : ℂ).im| = H')
    (hT : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' →
      (σ : ℂ).re * ((σ : ℂ).re + 1) < (σ : ℂ).im ^ 2)
    {m : ℕ} (c x : Fin m → ℝ) (hc : ∀ r, 0 ≤ c r) (hx : ∀ r, 1 < x r)
    (σ₀ : ExplicitIndex) (h0 : 0 < (σ₀ : ℂ).im) (h1 : H < |(σ₀ : ℂ).im|) (h2 : |(σ₀ : ℂ).im| ≤ H')
    (hsep : ‖historyRemoved H x (phaseMatched H' c x)‖ + windowMargin H' x (phaseMatched H' c x)
        + ‖∑' σ, lowerFiltered H H' x (phaseMatched H' c x) σ‖ <
      (-(zetaZeroMultiplicity (σ₀ : ℂ) : ℂ) / ((σ₀ : ℂ) * ((σ₀ : ℂ) + 1))).re * ∑ r, c r * x r ^ (σ₀ : ℂ).re) :
    False := by
  have hU := upper_fiber_minoration hHH' hFib hT c x hc hx σ₀ h0 h1 h2
  have hsplit := congrArg Complex.re (groupSignal_split H H' x (phaseMatched H' c x) hx)
  rw [Complex.add_re] at hsplit
  have a := Complex.re_le_norm (groupSignal H H' x (phaseMatched H' c x))
  have b := neg_le_of_abs_le (Complex.abs_re_le_norm (∑' σ, lowerFiltered H H' x (phaseMatched H' c x) σ))
  have hG : (-(zetaZeroMultiplicity (σ₀ : ℂ) : ℂ) / ((σ₀ : ℂ) * ((σ₀ : ℂ) + 1))).re * ∑ r, c r * x r ^ (σ₀ : ℂ).re
      - ‖∑' σ, lowerFiltered H H' x (phaseMatched H' c x) σ‖ ≤ ‖groupSignal H H' x (phaseMatched H' c x)‖ := by
    linarith
  exact local_transmission_closes H H' x _ hx hG le_rfl (by linarith)

/-- La marge du filtre accordé est `budget(H')·Σ_r c_r x_r`. -/
theorem phaseMatched_margin (H' : ℝ) {m : ℕ} (c x : Fin m → ℝ) (hc : ∀ r, 0 ≤ c r) (hx : ∀ r, 1 < x r) :
    windowMargin H' x (phaseMatched H' c x) = followingBudget H' * ∑ r, c r * x r := by
  unfold windowMargin
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [phaseMatched_norm H' c x (fun r => lt_trans one_pos (hx r)), abs_of_nonneg (hc r)]

/-- **Condition nécessaire avec la marge triangulaire** : la séparation du filtre accordé exige
`budget(H') < ‖w_{σ₀}‖` (dès que `Σ c_r x_r > 0`). La marge triangulaire du complément porte l'exposant `1` ; une
amélioration doit venir d'un contrôle de la somme oscillante complète du complément filtré. -/
theorem matched_separation_requires {H H' : ℝ} {m : ℕ} (c x : Fin m → ℝ) (hc : ∀ r, 0 ≤ c r)
    (hx : ∀ r, 1 < x r) (hS : 0 < ∑ r, c r * x r) (σ₀ : ExplicitIndex)
    (hsep : ‖historyRemoved H x (phaseMatched H' c x)‖ + windowMargin H' x (phaseMatched H' c x)
        + ‖∑' σ, lowerFiltered H H' x (phaseMatched H' c x) σ‖ <
      (-(zetaZeroMultiplicity (σ₀ : ℂ) : ℂ) / ((σ₀ : ℂ) * ((σ₀ : ℂ) + 1))).re * ∑ r, c r * x r ^ (σ₀ : ℂ).re) :
    followingBudget H' < ‖-(zetaZeroMultiplicity (σ₀ : ℂ) : ℂ) / ((σ₀ : ℂ) * ((σ₀ : ℂ) + 1))‖ := by
  rw [phaseMatched_margin H' c x hc hx] at hsep
  have hpow : ∑ r, c r * x r ^ (σ₀ : ℂ).re ≤ ∑ r, c r * x r := Finset.sum_le_sum fun r _ =>
    mul_le_mul_of_nonneg_left (by
      calc x r ^ (σ₀ : ℂ).re ≤ x r ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (hx r).le (explicitIndex_re_le_one σ₀)
        _ = x r := Real.rpow_one _) (hc r)
  have hpos0 : 0 ≤ ∑ r, c r * x r ^ (σ₀ : ℂ).re :=
    Finset.sum_nonneg fun r _ => mul_nonneg (hc r) (Real.rpow_nonneg (by linarith [hx r]) _)
  have hw := Complex.re_le_norm (-(zetaZeroMultiplicity (σ₀ : ℂ) : ℂ) / ((σ₀ : ℂ) * ((σ₀ : ℂ) + 1)))
  have hmul : (-(zetaZeroMultiplicity (σ₀ : ℂ) : ℂ) / ((σ₀ : ℂ) * ((σ₀ : ℂ) + 1))).re * ∑ r, c r * x r ^ (σ₀ : ℂ).re ≤
      ‖-(zetaZeroMultiplicity (σ₀ : ℂ) : ℂ) / ((σ₀ : ℂ) * ((σ₀ : ℂ) + 1))‖ * ∑ r, c r * x r := by
    calc _ ≤ ‖-(zetaZeroMultiplicity (σ₀ : ℂ) : ℂ) / ((σ₀ : ℂ) * ((σ₀ : ℂ) + 1))‖ * ∑ r, c r * x r ^ (σ₀ : ℂ).re :=
          mul_le_mul_of_nonneg_right hw hpos0
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
  have h1 := norm_nonneg (historyRemoved H x (phaseMatched H' c x))
  have h2 := norm_nonneg (∑' σ, lowerFiltered H H' x (phaseMatched H' c x) σ)
  exact lt_of_mul_lt_mul_right (by linarith) hS.le

#print axioms window_same_quantity
#print axioms separation_contradiction
#print axioms historyRemoved_filtered_primes
#print axioms groupSignal_eq_tsum_fiber
#print axioms groupSignal_split
#print axioms upper_fiber_minoration
#print axioms lower_term_eq
#print axioms matched_window_closes
#print axioms matched_separation_requires

end RHV6Fresh
