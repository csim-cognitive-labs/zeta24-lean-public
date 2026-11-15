/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.BreakMechanismOnLine

/-!
# La suite des amplitudes de paiement d'une Tour de la ligne aux rencontres successives
(E448, §19.70, 2026-11-08)

Module isolé (non ajouté à `RHV6Fresh.lean`). Ordre de l'auteur (R-LIGNE) : maîtriser le mécanisme de
cassure depuis la ligne (`β = 1/2`) avant toute déduction sur les OFF ; aucun énoncé ici ne parle d'un zéro
hors ligne, aucune contradiction n'est cherchée, aucune obligation n'est proposée. Point de départ : E447
(`line_break_amplitude_exact`) : la cassure `log q` au premier `q` est payée avec l'amplitude du dernier
contact, `√q·e^{−π f(q)/(2T)}/‖(1/2,T)‖`.
Question : d'un point au suivant, comment cette amplitude évolue-t-elle, et par quoi la suite est-elle déterminée ?

* L1 `cellFraction_step`, `cellFraction_step_eq_fract_sum`, `cellFraction_step_gap`, `displacement_add_fraction_eq` :
  **orbite de la fraction de cellule** — `f(y) = fract(f(x) + T·log(y/x)/π)` ; d'un premier au suivant, la suite des
  fractions est une orbite de translations par `T·log(p_{n+1}/p_n)/π` modulo un ; le déplacement de cellules plus la
  variation de fraction vaut exactement `T·log(y/x)/π`.
* L2 `line_abs_value_pos`, `line_abs_value_succ`, `line_abs_value_add_nat`, `line_abs_value_sub` : sur la ligne,
  `|v_{k+1}| = e^{π/(2T)}·|v_k|`, donc `|v_l| = e^{π(l−k)/(2T)}·|v_k|`.
* L3 `line_break_amplitude_ratio_cells`, `line_break_amplitude_ratio_exact` : **le rapport des amplitudes de paiement**
  entre deux points vaut `e^{π·(déplacement de cellules)/(2T)}` et aussi `√(y/x)·e^{−π(f(y)−f(x))/(2T)}`.
* L4 `line_break_amplitude_mono`, `line_break_amplitude_eq_iff_same_cell`, `line_break_amplitude_step_of_new_cell` :
  l'amplitude de paiement ne décroît jamais ; elle est constante **si et seulement si** les deux points partagent une
  cellule ; sinon elle est multipliée par au moins `e^{π/(2T)}`.
* L5 `line_break_amplitude_ratio_bounds` : le rapport est strictement entre `√(y/x)·e^{−π/(2T)}` et `√(y/x)·e^{π/(2T)}`.
* L6 `line_break_amplitude_telescope`, `line_break_amplitude_series`, `line_break_price_mono` : sur une série de
  rencontres le produit des rapports est `e^{π·(cellules franchies)/(2T)}` ; sur les premiers de rang `n` et `n+J` ;
  le prix `|v|·log q` ne décroît pas non plus.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune hypothèse, aucune somme de Tours, aucun objet spectral.
-/
namespace RHV6Fresh

open Real RHV3Lean Finset

/-! ## L1. L'orbite de la fraction de cellule -/

theorem cellFraction_step (β T : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    cellFraction β T y = Int.fract (cellFraction β T x + T * Real.log (y / x) / Real.pi) := by
  unfold cellFraction
  have hs : stagePosition β T y = stagePosition β T x + T * Real.log (y / x) / Real.pi := by
    have := stagePosition_sub β T x y hx hy; linarith
  have h : stagePosition β T x + T * Real.log (y / x) / Real.pi =
      (⌊stagePosition β T x⌋ : ℝ) + (Int.fract (stagePosition β T x) + T * Real.log (y / x) / Real.pi) := by
    rw [← add_assoc, Int.floor_add_fract]
  rw [hs, h, Int.fract_intCast_add]

theorem cellFraction_step_eq_fract_sum (β T : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    cellFraction β T y =
      Int.fract (cellFraction β T x + Int.fract (T * Real.log (y / x) / Real.pi)) := by
  rw [cellFraction_step β T hx hy]
  have hd := Int.floor_add_fract (T * Real.log (y / x) / Real.pi)
  have h : cellFraction β T x + T * Real.log (y / x) / Real.pi =
      (⌊T * Real.log (y / x) / Real.pi⌋ : ℝ) +
        (cellFraction β T x + Int.fract (T * Real.log (y / x) / Real.pi)) := by linarith
  rw [h, Int.fract_intCast_add]

theorem cellFraction_step_gap (β T : ℝ) (I : PrimeGapInterval) :
    cellFraction β T I.upper =
      Int.fract (cellFraction β T I.lower + T * Real.log (I.upper / I.lower) / Real.pi) :=
  cellFraction_step β T (by linarith [I.one_lt_lower]) (by linarith [I.one_lt_upper])

theorem displacement_add_fraction_eq (β T : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ((lastContactBefore β T y - lastContactBefore β T x : ℤ) : ℝ) +
        (cellFraction β T y - cellFraction β T x) = T * Real.log (y / x) / Real.pi := by
  have h1 := stagePosition_eq_last_add_fraction β T x
  have h2 := stagePosition_eq_last_add_fraction β T y
  have h3 := stagePosition_sub β T x y hx hy
  push_cast
  linarith

/-! ## L2. Le pas d'amplitude par cellule sur la ligne -/

theorem line_abs_value_pos {T : ℝ} (hT : 0 < T) (k : ℤ) :
    0 < |contactRealValue (1 / 2) T k| := by
  have h := line_contactRealValue_sq hT k
  have hpos : 0 < contactRealValue (1 / 2) T k ^ 2 := by
    rw [h]
    exact div_pos (contactAt_pos _ _ _) (pow_pos (norm_mk_pos (by norm_num)) 2)
  apply abs_pos.mpr
  intro h0
  rw [h0] at hpos
  simp at hpos

theorem line_abs_value_succ {T : ℝ} (hT : 0 < T) (k : ℤ) :
    |contactRealValue (1 / 2) T (k + 1)| =
      Real.exp (Real.pi / (2 * T)) * |contactRealValue (1 / 2) T k| := by
  rw [contactRealValue_succ hT.ne', abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
  have e : (1 / 2 : ℝ) * Real.pi / T = Real.pi / (2 * T) := by ring
  rw [e]

theorem line_abs_value_add_nat {T : ℝ} (hT : 0 < T) (k : ℤ) (m : ℕ) :
    |contactRealValue (1 / 2) T (k + m)| =
      Real.exp (Real.pi / (2 * T)) ^ m * |contactRealValue (1 / 2) T k| := by
  rw [contactRealValue_add_nat hT.ne', abs_mul, abs_pow, abs_neg, abs_of_pos (Real.exp_pos _)]
  have e : (1 / 2 : ℝ) * Real.pi / T = Real.pi / (2 * T) := by ring
  rw [e]

theorem line_abs_value_sub {T : ℝ} (hT : 0 < T) {k l : ℤ} (hkl : k ≤ l) :
    |contactRealValue (1 / 2) T l| =
      Real.exp (Real.pi * ((l - k : ℤ) : ℝ) / (2 * T)) * |contactRealValue (1 / 2) T k| := by
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hkl)
  have hl : l = k + (m : ℤ) := by omega
  subst hl
  rw [line_abs_value_add_nat hT, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-! ## L3. Le rapport des amplitudes de paiement : deux écritures -/

theorem line_break_amplitude_ratio_cells {T : ℝ} (hT : 0 < T) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T y)| =
      Real.exp (Real.pi * ((lastContactBefore (1 / 2) T y - lastContactBefore (1 / 2) T x : ℤ) : ℝ) / (2 * T))
        * |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x)| :=
  line_abs_value_sub hT (lastContactBefore_mono hT hx hxy)

theorem line_break_amplitude_ratio_exact {T : ℝ} (hT : 0 < T) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T y)| =
      (y / x) ^ (1 / 2 : ℝ) *
        Real.exp (-(Real.pi * (cellFraction (1 / 2) T y - cellFraction (1 / 2) T x) / (2 * T))) *
        |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x)| := by
  have he : Real.exp (-(Real.pi * (cellFraction (1 / 2) T y - cellFraction (1 / 2) T x) / (2 * T))) *
      Real.exp (-(Real.pi * cellFraction (1 / 2) T x / (2 * T))) =
        Real.exp (-(Real.pi * cellFraction (1 / 2) T y / (2 * T))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [line_break_amplitude_exact hT hy, line_break_amplitude_exact hT hx, Real.div_rpow hy.le hx.le, ← he]
  have hn := norm_mk_pos (β := 1 / 2) (T := T) (by norm_num)
  have hxp : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  field_simp

/-! ## L4. Monotonie de l'amplitude de paiement ; constance exactement dans une même cellule -/

theorem line_break_amplitude_mono {T : ℝ} (hT : 0 < T) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x)| ≤
      |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T y)| := by
  rw [line_break_amplitude_ratio_cells hT hx hxy]
  have hΔ : (0 : ℝ) ≤ ((lastContactBefore (1 / 2) T y - lastContactBefore (1 / 2) T x : ℤ) : ℝ) := by
    exact_mod_cast sub_nonneg.mpr (lastContactBefore_mono hT hx hxy)
  have h1 : 1 ≤ Real.exp (Real.pi * ((lastContactBefore (1 / 2) T y - lastContactBefore (1 / 2) T x : ℤ) : ℝ)
      / (2 * T)) := Real.one_le_exp (by positivity)
  exact le_mul_of_one_le_left (abs_nonneg _) h1

theorem line_break_amplitude_eq_iff_same_cell {T : ℝ} (hT : 0 < T) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x)| =
        |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T y)| ↔
      lastContactBefore (1 / 2) T x = lastContactBefore (1 / 2) T y := by
  constructor
  · intro h
    have hpos := line_abs_value_pos hT (lastContactBefore (1 / 2) T x)
    rw [line_break_amplitude_ratio_cells hT hx hxy] at h
    have he : Real.exp (Real.pi * ((lastContactBefore (1 / 2) T y - lastContactBefore (1 / 2) T x : ℤ) : ℝ)
        / (2 * T)) = 1 := by
      have h' : Real.exp (Real.pi * ((lastContactBefore (1 / 2) T y - lastContactBefore (1 / 2) T x : ℤ) : ℝ)
          / (2 * T)) * |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x)| =
            1 * |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x)| := by rw [one_mul]; exact h.symm
      exact mul_right_cancel₀ hpos.ne' h'
    rw [Real.exp_eq_one_iff] at he
    have hΔ : ((lastContactBefore (1 / 2) T y - lastContactBefore (1 / 2) T x : ℤ) : ℝ) = 0 := by
      have h2T : (2 * T : ℝ) ≠ 0 := by positivity
      rcases div_eq_zero_iff.mp he with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h Real.pi_ne_zero
        · exact h
      · exact absurd h h2T
    have : (lastContactBefore (1 / 2) T y - lastContactBefore (1 / 2) T x : ℤ) = 0 := by exact_mod_cast hΔ
    omega
  · intro h; rw [h]

theorem line_break_amplitude_step_of_new_cell {T : ℝ} (hT : 0 < T) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hlt : lastContactBefore (1 / 2) T x < lastContactBefore (1 / 2) T y) :
    Real.exp (Real.pi / (2 * T)) * |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x)| ≤
      |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T y)| := by
  rw [line_break_amplitude_ratio_cells hT hx hxy]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply Real.exp_le_exp.mpr
  have h1 : (1 : ℝ) ≤ ((lastContactBefore (1 / 2) T y - lastContactBefore (1 / 2) T x : ℤ) : ℝ) := by
    exact_mod_cast (by omega : (1 : ℤ) ≤ lastContactBefore (1 / 2) T y - lastContactBefore (1 / 2) T x)
  rw [div_le_div_iff_of_pos_right (by positivity)]
  nlinarith [Real.pi_pos]

/-! ## L5. Encadrement du rapport entre deux points -/

theorem line_break_amplitude_ratio_bounds {T : ℝ} (hT : 0 < T) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y / x) ^ (1 / 2 : ℝ) * Real.exp (-(Real.pi / (2 * T))) *
        |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x)| <
        |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T y)| ∧
      |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T y)| <
        (y / x) ^ (1 / 2 : ℝ) * Real.exp (Real.pi / (2 * T)) *
          |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x)| := by
  rw [line_break_amplitude_ratio_exact hT hx hy]
  have hpos := line_abs_value_pos hT (lastContactBefore (1 / 2) T x)
  have hr : 0 < (y / x) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (div_pos hy hx) _
  have hfx0 := cellFraction_nonneg (1 / 2) T x
  have hfx1 := cellFraction_lt_one (1 / 2) T x
  have hfy0 := cellFraction_nonneg (1 / 2) T y
  have hfy1 := cellFraction_lt_one (1 / 2) T y
  have hpi := Real.pi_pos
  constructor
  · apply mul_lt_mul_of_pos_right _ hpos
    apply mul_lt_mul_of_pos_left _ hr
    apply Real.exp_lt_exp.mpr
    rw [neg_lt_neg_iff, div_lt_div_iff_of_pos_right (by positivity)]
    nlinarith
  · apply mul_lt_mul_of_pos_right _ hpos
    apply mul_lt_mul_of_pos_left _ hr
    apply Real.exp_lt_exp.mpr
    rw [← neg_div, div_lt_div_iff_of_pos_right (by positivity)]
    nlinarith

/-! ## L6. Télescopage sur une série de rencontres ; le prix ne décroît pas -/

theorem line_break_amplitude_telescope (T : ℝ) (p : ℕ → ℝ) (n J : ℕ) :
    ∏ j ∈ range J, Real.exp (Real.pi *
        ((lastContactBefore (1 / 2) T (p (n + j + 1)) - lastContactBefore (1 / 2) T (p (n + j)) : ℤ) : ℝ)
        / (2 * T)) =
      Real.exp (Real.pi * ((lastContactBefore (1 / 2) T (p (n + J)) - lastContactBefore (1 / 2) T (p n) : ℤ) : ℝ)
        / (2 * T)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.prod_range_succ, ih, ← Real.exp_add]
    congr 1
    have e : n + (J + 1) = n + J + 1 := by ring
    rw [e]
    push_cast
    ring

theorem line_break_amplitude_series {T : ℝ} (hT : 0 < T) (n J : ℕ) :
    |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T (fnPrimeAtRank (n + J) : ℝ))| =
      Real.exp (Real.pi * ((lastContactBefore (1 / 2) T (fnPrimeAtRank (n + J) : ℝ)
          - lastContactBefore (1 / 2) T (fnPrimeAtRank n : ℝ) : ℤ) : ℝ) / (2 * T))
        * |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T (fnPrimeAtRank n : ℝ))| := by
  have hmono : StrictMono fnPrimeAtRank := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hp : (0 : ℝ) < fnPrimeAtRank n := by exact_mod_cast (thm_primeAtRank_isPrime n).pos
  have hle : (fnPrimeAtRank n : ℝ) ≤ fnPrimeAtRank (n + J) := by
    exact_mod_cast hmono.monotone (Nat.le_add_right n J)
  exact line_break_amplitude_ratio_cells hT hp hle

theorem line_break_price_mono {T : ℝ} (hT : 0 < T) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x)| * Real.log x ≤
      |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T y)| * Real.log y :=
  mul_le_mul (line_break_amplitude_mono hT (by linarith) hxy) (Real.log_le_log (by linarith) hxy)
    (Real.log_nonneg hx) (abs_nonneg _)

#print axioms cellFraction_step
#print axioms cellFraction_step_eq_fract_sum
#print axioms cellFraction_step_gap
#print axioms displacement_add_fraction_eq
#print axioms line_abs_value_pos
#print axioms line_abs_value_succ
#print axioms line_abs_value_add_nat
#print axioms line_abs_value_sub
#print axioms line_break_amplitude_ratio_cells
#print axioms line_break_amplitude_ratio_exact
#print axioms line_break_amplitude_mono
#print axioms line_break_amplitude_eq_iff_same_cell
#print axioms line_break_amplitude_step_of_new_cell
#print axioms line_break_amplitude_ratio_bounds
#print axioms line_break_amplitude_telescope
#print axioms line_break_amplitude_series
#print axioms line_break_price_mono

end RHV6Fresh
