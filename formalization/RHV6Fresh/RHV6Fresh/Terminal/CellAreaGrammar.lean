/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ArithmeticBudgetSeparation
import RHV6Fresh.Terminal.BreakMechanismOnLine

/-!
# RHV6Fresh — Terminal/CellAreaGrammar : grammaire des aires entre contacts consécutifs (E473, §19.106)
(2026-11-13 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse, aucun axiome, aucun `sorry`)

Stratégie (règle R-Ψ). Cible : écrire l'aire de la demande d'une cellule d'une Tour avec les seuls premiers qu'elle franchit et la
demande au contact d'entrée, puis ÉLIMINER cette demande (seule mémoire de tous les premiers antérieurs) par une récurrence entre
deux cellules consécutives. Ce qui reste est local : les poids des deux cellules pesés par leur distance aux contacts.
Objet cumulé : le budget arithmétique d'E472, réécrit par cette récurrence (première aire, dernière aire, somme alternée des termes
locaux). Pourquoi le ponctuel ne suffit pas : inchangé ; deux cellules consécutives sont la plus petite unité où une relation entre
aires existe. Signature d'un hors-ligne : inchangée (E472) ; la grammaire en change la lecture (G6). Suite dans les deux issues :
mesurer sur les premiers réels les termes locaux et la transmission sous changement de signe (phase B).

* G1 `cellArea`, `cellExitWeight`, `cellEntryWeight`, `cellDescentArea`, `cellArea_eq_descent_add_exit`, `exit_add_entry`,
  `cellExitWeight_nonneg`, `cellEntryWeight_nonneg`, `cellExitWeight_le`, `cellEntryWeight_le`, `exitDeviation`, `entryDeviation`,
  `exitDeviation_eq`, `entryDeviation_eq`, `deviation_add`.
* G2 `rawDemand_next_contact`, `cellLength_next` (`cellLength_add_nat` réutilisé d'E441), `cellArea_next`, `localGrammarTerm`, `localGrammarTerm_eq`,
  `cellArea_next_eq_local`, `localGrammarTerm_ge`, `localGrammarTerm_le`, `localGrammarTerm_of_no_weight`.
* G3 `budget_recurrence`, `arithmeticAlternatingBudget_eq_cellAreas`.
* G4 `abs_sub_mul_ge_of_mul_nonpos`, `cellArea_sign_change_transfer`, `budget_le_of_alternating`.
* G5 `cellArea_eventually_le_sq`, `sum_sq_cellLength_le`, `budget_unconditional_scale` (PNT porté : échelle `x_N^2`).
* G6 `budget_le_of_local_bounds`, `sum_contact_rpow_le`, `budget_line_scale_of_local` (clôtures conditionnelles, antécédents explicites).
Portée : identités et bornes exactes, valables sur la ligne comme hors ligne ; aucun théorème compilé n'exclut un hors-ligne.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction Finset Filter Topology

/-! ## G1 : l'aire d'une cellule, écrite avec ses seuls premiers et la demande au contact d'entrée -/

/-- Aire de la demande brute sur la cellule `k` de la Tour `(β, T)`. -/
noncomputable def cellArea (β T : ℝ) (k : ℤ) : ℝ := demandArea (contactAt β T k) (contactAt β T (k + 1))

/-- Poids des entiers franchis par la cellule, pesés par leur distance au contact de sortie. -/
noncomputable def cellExitWeight (β T : ℝ) (k : ℤ) : ℝ :=
  ∑ n ∈ Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 1)⌋₊, Λ n * (contactAt β T (k + 1) - n)

/-- Poids des entiers franchis par la cellule, pesés par leur distance au contact d'entrée. -/
noncomputable def cellEntryWeight (β T : ℝ) (k : ℤ) : ℝ :=
  ∑ n ∈ Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 1)⌋₊, Λ n * ((n : ℝ) - contactAt β T k)

/-- Part de descente de l'aire : demande au contact d'entrée × longueur − demi-carré de la longueur. -/
noncomputable def cellDescentArea (β T : ℝ) (k : ℤ) : ℝ :=
  rawDemand (contactAt β T k) * cellLength β T k - cellLength β T k ^ 2 / 2

theorem cellArea_eq_descent_add_exit (β T : ℝ) (k : ℤ) :
    cellArea β T k = cellDescentArea β T k + cellExitWeight β T k := by
  unfold cellArea demandArea cellDescentArea cellExitWeight cellLength
  ring

theorem exit_add_entry (β T : ℝ) (k : ℤ) :
    cellExitWeight β T k + cellEntryWeight β T k = cellWeight β T k * cellLength β T k := by
  unfold cellExitWeight cellEntryWeight cellWeight cellLength
  rw [← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem cellExitWeight_nonneg (β T : ℝ) (k : ℤ) : 0 ≤ cellExitWeight β T k := by
  unfold cellExitWeight
  refine Finset.sum_nonneg fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  have h1 : (n : ℝ) ≤ ⌊contactAt β T (k + 1)⌋₊ := by exact_mod_cast hn.2
  have h2 : (⌊contactAt β T (k + 1)⌋₊ : ℝ) ≤ contactAt β T (k + 1) := Nat.floor_le (contactAt_pos β T _).le
  exact mul_nonneg vonMangoldt_nonneg (by linarith)

theorem cellEntryWeight_nonneg (β T : ℝ) (k : ℤ) : 0 ≤ cellEntryWeight β T k := by
  unfold cellEntryWeight
  refine Finset.sum_nonneg fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  have h1 : (⌊contactAt β T k⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
  have h2 : contactAt β T k < ⌊contactAt β T k⌋₊ + 1 := Nat.lt_floor_add_one _
  exact mul_nonneg vonMangoldt_nonneg (by linarith)

theorem cellExitWeight_le (β T : ℝ) (k : ℤ) : cellExitWeight β T k ≤ cellWeight β T k * cellLength β T k := by
  have h1 := exit_add_entry β T k
  have h2 := cellEntryWeight_nonneg β T k
  linarith

theorem cellEntryWeight_le (β T : ℝ) (k : ℤ) : cellEntryWeight β T k ≤ cellWeight β T k * cellLength β T k := by
  have h1 := exit_add_entry β T k
  have h2 := cellExitWeight_nonneg β T k
  linarith

/-- Déviation de sortie : poids pesés par la distance à la sortie, moins la mesure de Lebesgue correspondante. -/
noncomputable def exitDeviation (β T : ℝ) (k : ℤ) : ℝ := cellExitWeight β T k - cellLength β T k ^ 2 / 2

/-- Déviation d'entrée : poids pesés par la distance à l'entrée, moins la mesure de Lebesgue correspondante. -/
noncomputable def entryDeviation (β T : ℝ) (k : ℤ) : ℝ := cellEntryWeight β T k - cellLength β T k ^ 2 / 2

/-- La déviation de sortie est l'aire moins (demande au contact d'entrée × longueur). -/
theorem exitDeviation_eq (β T : ℝ) (k : ℤ) :
    exitDeviation β T k = cellArea β T k - rawDemand (contactAt β T k) * cellLength β T k := by
  unfold exitDeviation
  rw [cellArea_eq_descent_add_exit]
  unfold cellDescentArea
  ring

/-! ## G2 : la grammaire locale entre deux cellules consécutives -/

theorem rawDemand_next_contact {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    rawDemand (contactAt β T (k + 1)) = rawDemand (contactAt β T k) + cellWeight β T k - cellLength β T k := by
  have h := cellDemand_eq (β := β) hT k
  unfold cellDemand at h
  linarith

/-- La déviation d'entrée est (demande au contact de sortie × longueur) moins l'aire. -/
theorem entryDeviation_eq {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    entryDeviation β T k = rawDemand (contactAt β T (k + 1)) * cellLength β T k - cellArea β T k := by
  unfold entryDeviation
  have h1 := exit_add_entry β T k
  have h2 := cellArea_eq_descent_add_exit β T k
  unfold cellDescentArea at h2
  rw [rawDemand_next_contact hT k]
  linear_combination h1 + h2

theorem deviation_add (β T : ℝ) (k : ℤ) :
    exitDeviation β T k + entryDeviation β T k = cellLength β T k * (cellWeight β T k - cellLength β T k) := by
  unfold exitDeviation entryDeviation
  have h := exit_add_entry β T k
  linear_combination h

theorem cellLength_next {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    cellLength β T (k + 1) = Real.exp (π / T) * cellLength β T k := by
  rw [cellLength_eq hT, cellLength_eq hT]
  have h := contactAt_ratio (β := β) hT.ne' k
  rw [div_eq_iff (contactAt_pos β T _).ne'] at h
  rw [h]
  ring

/-- **Grammaire locale.** `a_{k+1} = e^{π/T} a_k + P_{k+1} + e^{π/T} Q_k − e^{π/T}(1 + e^{π/T}) ℓ_k²/2` : la demande au contact
(mémoire de tous les premiers antérieurs) est éliminée ; ne restent que les poids des deux cellules et leurs longueurs. -/
theorem cellArea_next {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    cellArea β T (k + 1) = Real.exp (π / T) * cellArea β T k + cellExitWeight β T (k + 1) +
      Real.exp (π / T) * cellEntryWeight β T k -
      Real.exp (π / T) * (1 + Real.exp (π / T)) * cellLength β T k ^ 2 / 2 := by
  have hPQ := exit_add_entry β T k
  have hD := rawDemand_next_contact (β := β) hT k
  have hL := cellLength_next (β := β) hT k
  rw [cellArea_eq_descent_add_exit, cellArea_eq_descent_add_exit]
  unfold cellDescentArea
  rw [hL, hD]
  linear_combination (-Real.exp (π / T)) * hPQ

/-- Terme local de la grammaire : `L_k = ε_{k+1} + e^{π/T} η_k`. -/
noncomputable def localGrammarTerm (β T : ℝ) (k : ℤ) : ℝ :=
  exitDeviation β T (k + 1) + Real.exp (π / T) * entryDeviation β T k

theorem localGrammarTerm_eq {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    localGrammarTerm β T k = cellExitWeight β T (k + 1) + Real.exp (π / T) * cellEntryWeight β T k -
      Real.exp (π / T) * (1 + Real.exp (π / T)) * cellLength β T k ^ 2 / 2 := by
  unfold localGrammarTerm exitDeviation entryDeviation
  rw [cellLength_next hT k]
  ring

theorem cellArea_next_eq_local {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    cellArea β T (k + 1) - Real.exp (π / T) * cellArea β T k = localGrammarTerm β T k := by
  rw [localGrammarTerm_eq hT k, cellArea_next hT k]
  ring

/-- Contrôle des signes, borne basse : le terme local ne descend jamais sous la part de Lebesgue. -/
theorem localGrammarTerm_ge {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    -(Real.exp (π / T) * (1 + Real.exp (π / T)) * cellLength β T k ^ 2 / 2) ≤ localGrammarTerm β T k := by
  rw [localGrammarTerm_eq hT k]
  have h1 := cellExitWeight_nonneg β T (k + 1)
  have h2 := cellEntryWeight_nonneg β T k
  have h3 : 0 ≤ Real.exp (π / T) * cellEntryWeight β T k := mul_nonneg (Real.exp_pos _).le h2
  linarith

/-- Contrôle des signes, borne haute : le terme local est majoré par les poids des deux cellules fois leurs longueurs. -/
theorem localGrammarTerm_le {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    localGrammarTerm β T k ≤ cellWeight β T (k + 1) * cellLength β T (k + 1) +
      Real.exp (π / T) * (cellWeight β T k * cellLength β T k) -
      Real.exp (π / T) * (1 + Real.exp (π / T)) * cellLength β T k ^ 2 / 2 := by
  rw [localGrammarTerm_eq hT k]
  have h1 := cellExitWeight_le β T (k + 1)
  have h2 := cellEntryWeight_le β T k
  have h3 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (π / T)).le
  linarith

/-- Sans aucun poids dans les deux cellules, le terme local est la pure part de Lebesgue, strictement négative. -/
theorem localGrammarTerm_of_no_weight {β T : ℝ} (hT : 0 < T) (k : ℤ)
    (h1 : ∀ n ∈ Ioc ⌊contactAt β T (k + 1)⌋₊ ⌊contactAt β T (k + 1 + 1)⌋₊, Λ n = 0)
    (h2 : ∀ n ∈ Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 1)⌋₊, Λ n = 0) :
    localGrammarTerm β T k = -(Real.exp (π / T) * (1 + Real.exp (π / T)) * cellLength β T k ^ 2 / 2) := by
  rw [localGrammarTerm_eq hT k]
  have hP : cellExitWeight β T (k + 1) = 0 := by
    unfold cellExitWeight
    exact Finset.sum_eq_zero fun n hn => by rw [h1 n hn, zero_mul]
  have hQ : cellEntryWeight β T k = 0 := by
    unfold cellEntryWeight
    exact Finset.sum_eq_zero fun n hn => by rw [h2 n hn, zero_mul]
  rw [hP, hQ]
  ring

/-! ## G3 : la récurrence du budget alterné -/

/-- **Récurrence du budget.** `(1 + e^{π/T}) A_{N+1} = a_{k₀} + (−1)^N e^{π/T} a_{k₀+N} − Σ_{n<N} (−1)^n L_{k₀+n}`. -/
theorem budget_recurrence {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (N : ℕ) :
    (1 + Real.exp (π / T)) * ∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * cellArea β T (k₀ + n) =
      cellArea β T k₀ + (-1 : ℝ) ^ N * Real.exp (π / T) * cellArea β T (k₀ + N) -
        ∑ n ∈ range N, (-1 : ℝ) ^ n * localGrammarTerm β T (k₀ + n) := by
  induction N with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Finset.sum_range_zero, pow_zero, Nat.cast_zero, add_zero, one_mul,
      sub_zero]
    ring
  | succ N ih =>
    have hloc := cellArea_next_eq_local (β := β) hT (k₀ + N)
    have hc : k₀ + ((N + 1 : ℕ) : ℤ) = k₀ + N + 1 := by push_cast; ring
    rw [Finset.sum_range_succ _ N, Finset.sum_range_succ _ (N + 1), hc]
    linear_combination ih + (-(-1 : ℝ) ^ N) * hloc

/-- Pont avec E472 : le budget arithmétique alterné parti d'un contact est la somme alternée des aires de cellule de la Tour. -/
theorem arithmeticAlternatingBudget_eq_cellAreas (β T : ℝ) (k₀ : ℤ) (N : ℕ) :
    arithmeticAlternatingBudget T (contactAt β T k₀) N =
      ∑ n ∈ range N, (-1 : ℝ) ^ n * cellArea β T (k₀ + n) := by
  unfold arithmeticAlternatingBudget cellArea
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 : contactAt β T (k₀ + n + 1) = contactAt β T k₀ * Real.exp (π / T) ^ n * Real.exp (π / T) := by
    have h := contactAt_add_nat_eq (β := β) (T := T) k₀ (n + 1)
    push_cast at h
    rw [← add_assoc] at h
    rw [h, pow_succ, mul_assoc]
  rw [h1, contactAt_add_nat_eq]

/-! ## G4 : contrôle des signes, transmission du local au budget -/

theorem abs_sub_mul_ge_of_mul_nonpos {a b g : ℝ} (hg : 0 ≤ g) (h : a * b ≤ 0) :
    |b| + g * |a| ≤ |b - g * a| := by
  have hnn : 0 ≤ |b| + g * |a| := by positivity
  rw [← abs_of_nonneg hnn, ← sq_le_sq]
  have h1 : |a| * |b| = -(a * b) := by rw [← abs_mul, abs_of_nonpos h]
  have h2 := sq_abs a
  have h3 := sq_abs b
  have key : (|b| + g * |a|) ^ 2 = (b - g * a) ^ 2 := by
    linear_combination (2 * g) * h1 + g ^ 2 * h2 + h3
  exact key.le

/-- **Transmission.** Si deux aires consécutives sont de signes opposés, chacune est bornée par le terme local :
`|a_{k+1}| + e^{π/T}|a_k| ≤ |L_k|`. -/
theorem cellArea_sign_change_transfer {β T : ℝ} (hT : 0 < T) (k : ℤ)
    (h : cellArea β T k * cellArea β T (k + 1) ≤ 0) :
    |cellArea β T (k + 1)| + Real.exp (π / T) * |cellArea β T k| ≤ |localGrammarTerm β T k| := by
  rw [← cellArea_next_eq_local hT k]
  exact abs_sub_mul_ge_of_mul_nonpos (Real.exp_pos _).le h

/-- Sous alternance de signe sur une fenêtre, le budget est majoré par la première aire plus la somme des termes locaux. -/
theorem budget_le_of_alternating {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (N : ℕ)
    (h : ∀ n < N, cellArea β T (k₀ + n) * cellArea β T (k₀ + n + 1) ≤ 0) :
    |∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * cellArea β T (k₀ + n)| ≤
      |cellArea β T k₀| + ∑ n ∈ range N, |localGrammarTerm β T (k₀ + n)| := by
  have h1 : |∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * cellArea β T (k₀ + n)| ≤
      ∑ n ∈ range (N + 1), |cellArea β T (k₀ + n)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have h2 : ∑ n ∈ range (N + 1), |cellArea β T (k₀ + n)| =
      ∑ n ∈ range N, |cellArea β T (k₀ + n + 1)| + |cellArea β T k₀| := by
    rw [Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [show k₀ + ((n + 1 : ℕ) : ℤ) = k₀ + n + 1 by push_cast; ring]
    · simp
  have h3 : ∀ n ∈ range N, |cellArea β T (k₀ + n + 1)| ≤ |localGrammarTerm β T (k₀ + n)| := by
    intro n hn
    rw [Finset.mem_range] at hn
    have ht := cellArea_sign_change_transfer hT (k₀ + n) (h n hn)
    have hg : 0 ≤ Real.exp (π / T) * |cellArea β T (k₀ + n)| := by positivity
    linarith
  calc _ ≤ ∑ n ∈ range (N + 1), |cellArea β T (k₀ + n)| := h1
    _ = _ := h2
    _ ≤ ∑ n ∈ range N, |localGrammarTerm β T (k₀ + n)| + |cellArea β T k₀| :=
        add_le_add (Finset.sum_le_sum h3) le_rfl
    _ = _ := add_comm _ _

/-! ## G5 : l'échelle inconditionnelle compilée (PNT porté) est `x_N^2` -/

theorem cellArea_eventually_le_sq {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, |cellArea β T (k₀ + i)| ≤ (1 / 2 + ε) * cellLength β T (k₀ + i) ^ 2 := by
  have hD : Tendsto (fun i : ℕ => rawDemand (contactAt β T (k₀ + i)) / cellLength β T (k₀ + i)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun i : ℕ => rawDemand (contactAt β T (k₀ + i)) / contactAt β T (k₀ + i)) atTop (𝓝 0) :=
      rawDemand_div_tendsto_zero.comp (contactAt_tendsto_atTop hT k₀)
    have h := h0.div_const (Real.exp (π / T) - 1)
    rw [zero_div] at h
    refine h.congr fun i => ?_
    rw [cellLength_eq hT, div_div]
  have hW := cellWeight_div_cellLength_tendsto_one (β := β) hT k₀
  have h1 := hD.eventually_mem (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))
  have h2 := hW.eventually_mem (Metric.ball_mem_nhds (1 : ℝ) (half_pos hε))
  filter_upwards [h1, h2] with i hi1 hi2
  beta_reduce at hi1 hi2
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hi1
  rw [Metric.mem_ball, Real.dist_eq] at hi2
  have hℓ : 0 < cellLength β T (k₀ + i) := cellLength_pos hT _
  rw [abs_div, abs_of_pos hℓ, div_lt_iff₀ hℓ] at hi1
  obtain ⟨hDlo, hDhi⟩ := abs_lt.mp hi1
  have hWhi : cellWeight β T (k₀ + i) / cellLength β T (k₀ + i) - 1 < ε / 2 := (abs_lt.mp hi2).2
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hℓ] at hWhi
  have hDu : rawDemand (contactAt β T (k₀ + i)) * cellLength β T (k₀ + i) ≤ ε / 2 * cellLength β T (k₀ + i) ^ 2 := by
    nlinarith
  have hDl : -(ε / 2 * cellLength β T (k₀ + i) ^ 2) ≤ rawDemand (contactAt β T (k₀ + i)) * cellLength β T (k₀ + i) := by
    nlinarith
  have hWl : cellWeight β T (k₀ + i) * cellLength β T (k₀ + i) ≤ (ε / 2 + 1) * cellLength β T (k₀ + i) ^ 2 := by
    nlinarith
  have hPW := cellExitWeight_le β T (k₀ + i)
  have hP0 := cellExitWeight_nonneg β T (k₀ + i)
  have ha := cellArea_eq_descent_add_exit β T (k₀ + i)
  unfold cellDescentArea at ha
  rw [abs_le]
  constructor <;> linarith

theorem sum_sq_cellLength_le {β T : ℝ} (hT : 0 < T) (k : ℤ) (N : ℕ) :
    ∑ n ∈ range (N + 1), cellLength β T (k + n) ^ 2 ≤
      Real.exp (π / T) ^ 2 / (Real.exp (π / T) ^ 2 - 1) * cellLength β T (k + N) ^ 2 := by
  have hg : 1 < Real.exp (π / T) := Real.one_lt_exp_iff.mpr (by positivity)
  have hg2 : 1 < Real.exp (π / T) ^ 2 := by nlinarith
  have hpos : 0 < Real.exp (π / T) ^ 2 - 1 := by linarith
  have hterm : ∀ n ∈ range (N + 1),
      cellLength β T (k + n) ^ 2 = cellLength β T k ^ 2 * (Real.exp (π / T) ^ 2) ^ n := by
    intro n _
    rw [cellLength_add_nat hT]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, geom_sum_eq hg2.ne' (N + 1), cellLength_add_nat hT,
    mul_div_assoc', div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ hpos.le
  have hsq := sq_nonneg (cellLength β T k)
  have hid : cellLength β T k ^ 2 * ((Real.exp (π / T) ^ 2) ^ (N + 1) - 1) =
      Real.exp (π / T) ^ 2 * (cellLength β T k * Real.exp (π / T) ^ N) ^ 2 - cellLength β T k ^ 2 := by ring
  rw [hid]
  linarith

/-- **Échelle inconditionnelle du budget** : à partir d'un rang, pour toute fenêtre, le budget alterné est majoré par
`(1/2 + ε) e^{2π/T}/(e^{2π/T} − 1)` fois le carré de la dernière longueur de cellule : échelle `x_N^2` (PNT porté). -/
theorem budget_unconditional_scale {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ N : ℕ,
      |∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * cellArea β T (k₀ + i + n)| ≤
        (1 / 2 + ε) * (Real.exp (π / T) ^ 2 / (Real.exp (π / T) ^ 2 - 1)) * cellLength β T (k₀ + i + N) ^ 2 := by
  obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.mp (cellArea_eventually_le_sq (β := β) hT k₀ hε)
  refine ⟨i₀, fun i hi N => ?_⟩
  have h1 : |∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * cellArea β T (k₀ + i + n)| ≤
      ∑ n ∈ range (N + 1), (1 / 2 + ε) * cellLength β T (k₀ + i + n) ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hb := hi₀ (i + n) (by omega)
    push_cast at hb
    rwa [← add_assoc] at hb
  rw [← Finset.mul_sum] at h1
  have h2 := sum_sq_cellLength_le (β := β) hT (k₀ + i) N
  have hε' : 0 ≤ 1 / 2 + ε := by linarith
  calc _ ≤ _ := h1
    _ ≤ (1 / 2 + ε) * (Real.exp (π / T) ^ 2 / (Real.exp (π / T) ^ 2 - 1) * cellLength β T (k₀ + i + N) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 hε'
    _ = _ := by ring

/-! ## G6 : clôtures conditionnelles (antécédents explicites, rien d'admis) -/

/-- Dès que chaque terme local est borné par `b n`, le budget est borné par la première aire, la dernière aire et `Σ b`. -/
theorem budget_le_of_local_bounds {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (N : ℕ) (b : ℕ → ℝ)
    (hloc : ∀ n < N, |localGrammarTerm β T (k₀ + n)| ≤ b n) :
    (1 + Real.exp (π / T)) * |∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * cellArea β T (k₀ + n)| ≤
      |cellArea β T k₀| + Real.exp (π / T) * |cellArea β T (k₀ + N)| + ∑ n ∈ range N, b n := by
  have hg : 0 < 1 + Real.exp (π / T) := by positivity
  rw [← abs_of_pos hg, ← abs_mul, budget_recurrence hT k₀ N]
  have hS : |∑ n ∈ range N, (-1 : ℝ) ^ n * localGrammarTerm β T (k₀ + n)| ≤ ∑ n ∈ range N, b n := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hloc n (Finset.mem_range.mp hn)
  have hN : |(-1 : ℝ) ^ N * Real.exp (π / T) * cellArea β T (k₀ + N)| =
      Real.exp (π / T) * |cellArea β T (k₀ + N)| := by
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (Real.exp_pos _)]
  calc |cellArea β T k₀ + (-1 : ℝ) ^ N * Real.exp (π / T) * cellArea β T (k₀ + N) -
        ∑ n ∈ range N, (-1 : ℝ) ^ n * localGrammarTerm β T (k₀ + n)|
      ≤ |cellArea β T k₀ + (-1 : ℝ) ^ N * Real.exp (π / T) * cellArea β T (k₀ + N)| +
        |∑ n ∈ range N, (-1 : ℝ) ^ n * localGrammarTerm β T (k₀ + n)| := abs_sub _ _
    _ ≤ |cellArea β T k₀| + |(-1 : ℝ) ^ N * Real.exp (π / T) * cellArea β T (k₀ + N)| +
        ∑ n ∈ range N, b n := add_le_add (abs_add_le _ _) hS
    _ = _ := by rw [hN]

theorem sum_contact_rpow_le {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (N : ℕ) :
    ∑ n ∈ range N, contactAt β T (k₀ + n) ^ ((3 : ℝ) / 2) ≤
      contactAt β T (k₀ + N) ^ ((3 : ℝ) / 2) / (Real.exp (π / T) ^ ((3 : ℝ) / 2) - 1) := by
  have hg : 1 < Real.exp (π / T) := Real.one_lt_exp_iff.mpr (by positivity)
  have hr : 1 < Real.exp (π / T) ^ ((3 : ℝ) / 2) := Real.one_lt_rpow hg (by norm_num)
  have hr0 : 0 < Real.exp (π / T) ^ ((3 : ℝ) / 2) - 1 := by linarith
  have hx0 : 0 ≤ contactAt β T k₀ := (contactAt_pos β T k₀).le
  have hterm : ∀ n : ℕ, contactAt β T (k₀ + n) ^ ((3 : ℝ) / 2) =
      contactAt β T k₀ ^ ((3 : ℝ) / 2) * (Real.exp (π / T) ^ ((3 : ℝ) / 2)) ^ n := by
    intro n
    rw [contactAt_add_nat_eq, Real.mul_rpow hx0 (pow_nonneg (Real.exp_pos _).le n),
      ← Real.rpow_natCast (Real.exp (π / T)) n, ← Real.rpow_mul (Real.exp_pos _).le,
      mul_comm (n : ℝ) ((3 : ℝ) / 2), Real.rpow_mul (Real.exp_pos _).le, Real.rpow_natCast]
  rw [Finset.sum_congr rfl (fun n _ => hterm n), ← Finset.mul_sum, geom_sum_eq hr.ne' N, hterm N, mul_div_assoc']
  refine div_le_div_of_nonneg_right ?_ hr0.le
  have hx := Real.rpow_nonneg hx0 ((3 : ℝ) / 2)
  have hid : contactAt β T k₀ ^ ((3 : ℝ) / 2) * ((Real.exp (π / T) ^ ((3 : ℝ) / 2)) ^ N - 1) =
      contactAt β T k₀ ^ ((3 : ℝ) / 2) * (Real.exp (π / T) ^ ((3 : ℝ) / 2)) ^ N -
        contactAt β T k₀ ^ ((3 : ℝ) / 2) := by ring
  rw [hid]
  linarith

/-- **Clôture conditionnelle à l'échelle de la ligne.** Si les termes locaux, la première et la dernière aire sont à l'échelle
`C · C_k^{3/2}`, le budget l'est, avec la constante explicite `C (1 + e^{π/T} + 1/(e^{3π/(2T)} − 1))/(1 + e^{π/T})`.
Les antécédents sont des hypothèses du théorème, jamais admises ailleurs. -/
theorem budget_line_scale_of_local {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (N : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hloc : ∀ n < N, |localGrammarTerm β T (k₀ + n)| ≤ C * contactAt β T (k₀ + n) ^ ((3 : ℝ) / 2))
    (h0 : |cellArea β T k₀| ≤ C * contactAt β T k₀ ^ ((3 : ℝ) / 2))
    (hlast : |cellArea β T (k₀ + N)| ≤ C * contactAt β T (k₀ + N) ^ ((3 : ℝ) / 2)) :
    (1 + Real.exp (π / T)) * |∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * cellArea β T (k₀ + n)| ≤
      C * (1 + Real.exp (π / T) + 1 / (Real.exp (π / T) ^ ((3 : ℝ) / 2) - 1)) *
        contactAt β T (k₀ + N) ^ ((3 : ℝ) / 2) := by
  have h1 := budget_le_of_local_bounds hT k₀ N (fun n => C * contactAt β T (k₀ + n) ^ ((3 : ℝ) / 2)) hloc
  have hsum := sum_contact_rpow_le (β := β) hT k₀ N
  have hmono : contactAt β T k₀ ^ ((3 : ℝ) / 2) ≤ contactAt β T (k₀ + N) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (contactAt_pos β T k₀).le (contactAt_mono hT (by omega)) (by norm_num)
  have hg : 0 < Real.exp (π / T) := Real.exp_pos _
  rw [← Finset.mul_sum] at h1
  have h2 : C * ∑ n ∈ range N, contactAt β T (k₀ + n) ^ ((3 : ℝ) / 2) ≤
      C * (contactAt β T (k₀ + N) ^ ((3 : ℝ) / 2) / (Real.exp (π / T) ^ ((3 : ℝ) / 2) - 1)) :=
    mul_le_mul_of_nonneg_left hsum hC
  have h3 : C * contactAt β T k₀ ^ ((3 : ℝ) / 2) ≤ C * contactAt β T (k₀ + N) ^ ((3 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_left hmono hC
  have h4 : Real.exp (π / T) * |cellArea β T (k₀ + N)| ≤
      Real.exp (π / T) * (C * contactAt β T (k₀ + N) ^ ((3 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hlast hg.le
  have hkey : C * (1 + Real.exp (π / T) + 1 / (Real.exp (π / T) ^ ((3 : ℝ) / 2) - 1)) *
      contactAt β T (k₀ + N) ^ ((3 : ℝ) / 2) =
      C * contactAt β T (k₀ + N) ^ ((3 : ℝ) / 2) + Real.exp (π / T) * (C * contactAt β T (k₀ + N) ^ ((3 : ℝ) / 2)) +
        C * (contactAt β T (k₀ + N) ^ ((3 : ℝ) / 2) / (Real.exp (π / T) ^ ((3 : ℝ) / 2) - 1)) := by ring
  linarith [h1, h0, h2, h3, h4, hkey]

#print axioms cellArea_eq_descent_add_exit
#print axioms exit_add_entry
#print axioms exitDeviation_eq
#print axioms entryDeviation_eq
#print axioms deviation_add
#print axioms cellArea_next
#print axioms cellArea_next_eq_local
#print axioms localGrammarTerm_ge
#print axioms localGrammarTerm_le
#print axioms localGrammarTerm_of_no_weight
#print axioms budget_recurrence
#print axioms arithmeticAlternatingBudget_eq_cellAreas
#print axioms cellArea_sign_change_transfer
#print axioms budget_le_of_alternating
#print axioms cellArea_eventually_le_sq
#print axioms budget_unconditional_scale
#print axioms budget_le_of_local_bounds
#print axioms budget_line_scale_of_local

end RHV6Fresh
