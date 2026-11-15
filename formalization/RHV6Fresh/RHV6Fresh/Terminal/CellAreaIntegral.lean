/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CellAreaGrammar

/-!
# RHV6Fresh — Terminal/CellAreaIntegral : l'aire est l'intégrale de la demande ; le budget contrôlé par son suprémum (E474, §19.107)
(2026-11-13 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse, aucun axiome, aucun `sorry`)

Stratégie (règle R-Ψ). Cible : écrire `demandArea a b` comme l'intégrale de `rawDemand` sur `[a, b]` (sommation d'Abel de Mathlib,
`sum_mul_eq_sub_sub_integral_mul`), puis en tirer les bornes locales : une aire de cellule par le suprémum de la demande sur la
cellule, une déviation de sortie par la variation INTÉRIEURE de la demande, un terme local par le suprémum sur deux cellules, et le
budget alterné d'une fenêtre par le suprémum de la demande sur la fenêtre, avec constante explicite et sans aucune alternance.
Objet cumulé : `budget_le_of_demand_bound`. Pourquoi le ponctuel ne suffit pas : inchangé. Signature d'un hors-ligne : inchangée.
Suite dans les deux issues : l'antécédent « demande à l'échelle √x·(log x)² sur la fenêtre » est de force RH (R-RH : ce n'est ni une
objection ni un frein ; seul son admission comme prémisse est interdite) ; on ne le présente pas comme une obligation nouvelle.

* I1 `integral_psi_eq`, `rawDemand_intervalIntegrable`, `demandArea_eq_integral`, `demandArea_sub_eq_integral`.
* I2 `abs_demandArea_le_of_bound`, `abs_demandArea_sub_le_of_variation`.
* I3 `cellArea_eq_integral`, `abs_cellArea_le_of_bound`, `exitDeviation_eq_integral`, `abs_exitDeviation_le_of_variation`,
  `abs_localGrammarTerm_le_of_demand_bound`.
* I4 `sum_cellLength_eq`, `budget_le_of_demand_bound`, `budget_le_of_demand_bound'`.
Portée : identités et bornes exactes, valables sur la ligne comme hors ligne ; aucun théorème compilé n'exclut un hors-ligne.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction Finset MeasureTheory intervalIntegral

/-! ## I1 : l'aire de la demande est une intégrale -/

/-- Sommation d'Abel : `∫_a^b ψ = ψ(a)(b − a) + Σ_{a<n≤b} Λ(n)(b − n)`. -/
theorem integral_psi_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, Chebyshev.psi t = Chebyshev.psi a * (b - a) + ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, Λ n * (b - n) := by
  have hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun t : ℝ => b - t) t :=
    fun t _ => (differentiableAt_const _).sub differentiableAt_id
  have hderiv : deriv (fun t : ℝ => b - t) = fun _ => (-1 : ℝ) := by
    funext t
    rw [deriv_const_sub, deriv_id'']
  have hint : IntegrableOn (deriv fun t : ℝ => b - t) (Set.Icc a b) := by
    rw [hderiv]
    exact continuous_const.integrableOn_Icc
  have h := sum_mul_eq_sub_sub_integral_mul (c := fun n => Λ n) ha hab hdiff hint
  simp_rw [hderiv, ← Chebyshev.psi_eq_sum_Icc] at h
  have h2 : ∫ t in Set.Ioc a b, (-1 : ℝ) * Chebyshev.psi t = -∫ t in Set.Ioc a b, Chebyshev.psi t := by
    rw [MeasureTheory.integral_const_mul]
    ring
  have hsum : ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, Λ n * (b - n) = ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (b - k) * Λ k :=
    Finset.sum_congr rfl fun n _ => mul_comm _ _
  rw [intervalIntegral.integral_of_le hab, hsum, h, h2]
  ring

theorem rawDemand_intervalIntegrable (a b : ℝ) : IntervalIntegrable rawDemand volume a b := by
  have hpsi : IntervalIntegrable Chebyshev.psi volume a b :=
    (Chebyshev.psi_mono.monotoneOn _).intervalIntegrable
  have hid : IntervalIntegrable (fun t : ℝ => t) volume a b := continuous_id.intervalIntegrable _ _
  exact hpsi.sub hid

/-- **L'aire de la demande est l'intégrale de la demande brute.** -/
theorem demandArea_eq_integral {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    demandArea a b = ∫ t in a..b, rawDemand t := by
  have hpsi : IntervalIntegrable Chebyshev.psi volume a b :=
    (Chebyshev.psi_mono.monotoneOn _).intervalIntegrable
  have hid : IntervalIntegrable (fun t : ℝ => t) volume a b := continuous_id.intervalIntegrable _ _
  unfold rawDemand
  rw [intervalIntegral.integral_sub hpsi hid, integral_psi_eq ha hab, integral_id]
  unfold demandArea rawDemand
  ring

/-- L'aire moins (demande au bord gauche × longueur) est l'intégrale de la variation intérieure de la demande. -/
theorem demandArea_sub_eq_integral {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    demandArea a b - rawDemand a * (b - a) = ∫ t in a..b, (rawDemand t - rawDemand a) := by
  rw [intervalIntegral.integral_sub (rawDemand_intervalIntegrable a b) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, demandArea_eq_integral ha hab]
  ring

/-! ## I2 : bornes par le suprémum -/

theorem abs_demandArea_le_of_bound {a b M : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hM : ∀ t ∈ Set.Ioc a b, |rawDemand t| ≤ M) : |demandArea a b| ≤ M * (b - a) := by
  rw [demandArea_eq_integral ha hab]
  have hb : ∀ t ∈ Set.uIoc a b, ‖rawDemand t‖ ≤ M := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    rw [Real.norm_eq_abs]
    exact hM t ht
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h

theorem abs_demandArea_sub_le_of_variation {a b V : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hV : ∀ t ∈ Set.Ioc a b, |rawDemand t - rawDemand a| ≤ V) :
    |demandArea a b - rawDemand a * (b - a)| ≤ V * (b - a) := by
  rw [demandArea_sub_eq_integral ha hab]
  have hb : ∀ t ∈ Set.uIoc a b, ‖rawDemand t - rawDemand a‖ ≤ V := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    rw [Real.norm_eq_abs]
    exact hV t ht
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h

/-! ## I3 : sur les cellules d'une Tour -/

theorem cellArea_eq_integral {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    cellArea β T k = ∫ t in contactAt β T k..contactAt β T (k + 1), rawDemand t := by
  unfold cellArea
  exact demandArea_eq_integral (contactAt_pos β T k).le (contactAt_mono hT (by omega))

theorem abs_cellArea_le_of_bound {β T M : ℝ} (hT : 0 < T) (k : ℤ)
    (hM : ∀ t ∈ Set.Ioc (contactAt β T k) (contactAt β T (k + 1)), |rawDemand t| ≤ M) :
    |cellArea β T k| ≤ M * cellLength β T k := by
  unfold cellArea cellLength
  exact abs_demandArea_le_of_bound (contactAt_pos β T k).le (contactAt_mono hT (by omega)) hM

/-- **H4.** La déviation de sortie est l'intégrale, sur la cellule, de la variation de la demande depuis le contact d'entrée. -/
theorem exitDeviation_eq_integral {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    exitDeviation β T k =
      ∫ t in contactAt β T k..contactAt β T (k + 1), (rawDemand t - rawDemand (contactAt β T k)) := by
  rw [exitDeviation_eq]
  unfold cellArea cellLength
  exact demandArea_sub_eq_integral (contactAt_pos β T k).le (contactAt_mono hT (by omega))

theorem abs_exitDeviation_le_of_variation {β T V : ℝ} (hT : 0 < T) (k : ℤ)
    (hV : ∀ t ∈ Set.Ioc (contactAt β T k) (contactAt β T (k + 1)),
      |rawDemand t - rawDemand (contactAt β T k)| ≤ V) :
    |exitDeviation β T k| ≤ V * cellLength β T k := by
  rw [exitDeviation_eq]
  unfold cellArea cellLength
  exact abs_demandArea_sub_le_of_variation (contactAt_pos β T k).le (contactAt_mono hT (by omega)) hV

/-- **H3, explication compilée.** `|L_k| ≤ 2 e^{π/T} ℓ_k M` dès que `|rawDemand| ≤ M` sur les deux cellules `(C_k, C_{k+2}]`. -/
theorem abs_localGrammarTerm_le_of_demand_bound {β T M : ℝ} (hT : 0 < T) (k : ℤ)
    (hM : ∀ t ∈ Set.Ioc (contactAt β T k) (contactAt β T (k + 2)), |rawDemand t| ≤ M) :
    |localGrammarTerm β T k| ≤ 2 * Real.exp (π / T) * cellLength β T k * M := by
  have hg : 0 < Real.exp (π / T) := Real.exp_pos _
  have hk2 : (k + 1 + 1 : ℤ) = k + 2 := by ring
  have h01 : contactAt β T k ≤ contactAt β T (k + 1) := contactAt_mono hT (by omega)
  have h12 : contactAt β T (k + 1) ≤ contactAt β T (k + 2) := contactAt_mono hT (by omega)
  have hA : |cellArea β T k| ≤ M * cellLength β T k :=
    abs_cellArea_le_of_bound hT k fun t ht => hM t (Set.Ioc_subset_Ioc_right h12 ht)
  have hB : |cellArea β T (k + 1)| ≤ M * cellLength β T (k + 1) := by
    refine abs_cellArea_le_of_bound hT (k + 1) fun t ht => hM t ?_
    rw [hk2] at ht
    exact Set.Ioc_subset_Ioc_left h01 ht
  rw [cellLength_next hT k] at hB
  rw [← cellArea_next_eq_local hT k]
  calc |cellArea β T (k + 1) - Real.exp (π / T) * cellArea β T k|
      ≤ |cellArea β T (k + 1)| + |Real.exp (π / T) * cellArea β T k| := abs_sub _ _
    _ = |cellArea β T (k + 1)| + Real.exp (π / T) * |cellArea β T k| := by
        rw [abs_mul, abs_of_pos hg]
    _ ≤ M * (Real.exp (π / T) * cellLength β T k) + Real.exp (π / T) * (M * cellLength β T k) :=
        add_le_add hB (mul_le_mul_of_nonneg_left hA hg.le)
    _ = 2 * Real.exp (π / T) * cellLength β T k * M := by ring

/-! ## I4 : le budget d'une fenêtre contrôlé par le suprémum de la demande -/

theorem sum_cellLength_eq {β T : ℝ} (k₀ : ℤ) (N : ℕ) :
    ∑ n ∈ range N, cellLength β T (k₀ + n) = contactAt β T (k₀ + N) - contactAt β T k₀ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    unfold cellLength
    rw [show (k₀ + ((N + 1 : ℕ) : ℤ)) = k₀ + N + 1 by push_cast; ring]
    ring

/-- **Clôture conditionnelle par la demande.** Si `|rawDemand| ≤ M` sur la fenêtre `(C_{k₀}, C_{k₀+N+1}]`, le budget alterné de la
fenêtre est borné par `M` fois une longueur explicite : première cellule, dernière cellule pesée par `e^{π/T}`, et deux fois
`e^{π/T}` fois la longueur de la fenêtre. Aucune alternance n'est utilisée. -/
theorem budget_le_of_demand_bound {β T M : ℝ} (hT : 0 < T) (k₀ : ℤ) (N : ℕ) (hM0 : 0 ≤ M)
    (hM : ∀ t ∈ Set.Ioc (contactAt β T k₀) (contactAt β T (k₀ + N + 1)), |rawDemand t| ≤ M) :
    (1 + Real.exp (π / T)) * |∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * cellArea β T (k₀ + n)| ≤
      M * (cellLength β T k₀ + Real.exp (π / T) * cellLength β T (k₀ + N) +
        2 * Real.exp (π / T) * (contactAt β T (k₀ + N) - contactAt β T k₀)) := by
  have hg : 0 < Real.exp (π / T) := Real.exp_pos _
  have hloc : ∀ n < N, |localGrammarTerm β T (k₀ + n)| ≤ 2 * Real.exp (π / T) * cellLength β T (k₀ + n) * M := by
    intro n hn
    refine abs_localGrammarTerm_le_of_demand_bound hT (k₀ + n) fun t ht => hM t ?_
    exact Set.Ioc_subset_Ioc (contactAt_mono hT (by omega)) (contactAt_mono hT (by omega)) ht
  have h := budget_le_of_local_bounds hT k₀ N (fun n => 2 * Real.exp (π / T) * cellLength β T (k₀ + n) * M) hloc
  beta_reduce at h
  have h0 : |cellArea β T k₀| ≤ M * cellLength β T k₀ :=
    abs_cellArea_le_of_bound hT k₀ fun t ht => hM t (Set.Ioc_subset_Ioc_right (contactAt_mono hT (by omega)) ht)
  have hN : |cellArea β T (k₀ + N)| ≤ M * cellLength β T (k₀ + N) :=
    abs_cellArea_le_of_bound hT (k₀ + N) fun t ht =>
      hM t (Set.Ioc_subset_Ioc_left (contactAt_mono hT (by omega)) ht)
  have hsum : ∑ n ∈ range N, 2 * Real.exp (π / T) * cellLength β T (k₀ + n) * M =
      2 * Real.exp (π / T) * M * (contactAt β T (k₀ + N) - contactAt β T k₀) := by
    rw [← sum_cellLength_eq (β := β) (T := T) k₀ N, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hsum] at h
  have hN' : Real.exp (π / T) * |cellArea β T (k₀ + N)| ≤ Real.exp (π / T) * (M * cellLength β T (k₀ + N)) :=
    mul_le_mul_of_nonneg_left hN hg.le
  calc (1 + Real.exp (π / T)) * |∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * cellArea β T (k₀ + n)|
      ≤ |cellArea β T k₀| + Real.exp (π / T) * |cellArea β T (k₀ + N)| +
        2 * Real.exp (π / T) * M * (contactAt β T (k₀ + N) - contactAt β T k₀) := h
    _ ≤ M * cellLength β T k₀ + Real.exp (π / T) * (M * cellLength β T (k₀ + N)) +
        2 * Real.exp (π / T) * M * (contactAt β T (k₀ + N) - contactAt β T k₀) := by linarith
    _ = _ := by ring

/-- Forme courte : le budget à l'échelle `x_N` est contrôlé par `(1 + e^{π/T})² M`. -/
theorem budget_le_of_demand_bound' {β T M : ℝ} (hT : 0 < T) (k₀ : ℤ) (N : ℕ) (hM0 : 0 ≤ M)
    (hM : ∀ t ∈ Set.Ioc (contactAt β T k₀) (contactAt β T (k₀ + N + 1)), |rawDemand t| ≤ M) :
    (1 + Real.exp (π / T)) * |∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * cellArea β T (k₀ + n)| ≤
      M * (1 + Real.exp (π / T)) ^ 2 * contactAt β T (k₀ + N) := by
  have h := budget_le_of_demand_bound hT k₀ N hM0 hM
  have hg1 : 1 < Real.exp (π / T) := Real.one_lt_exp_iff.mpr (by positivity)
  have hmono : contactAt β T k₀ ≤ contactAt β T (k₀ + N) := contactAt_mono hT (by omega)
  have hpos : 0 < contactAt β T k₀ := contactAt_pos β T k₀
  have hl0 : cellLength β T k₀ = contactAt β T k₀ * (Real.exp (π / T) - 1) := cellLength_eq hT k₀
  have hlN : cellLength β T (k₀ + N) = contactAt β T (k₀ + N) * (Real.exp (π / T) - 1) := cellLength_eq hT _
  have hlen : cellLength β T k₀ + Real.exp (π / T) * cellLength β T (k₀ + N) +
      2 * Real.exp (π / T) * (contactAt β T (k₀ + N) - contactAt β T k₀) ≤
      (1 + Real.exp (π / T)) ^ 2 * contactAt β T (k₀ + N) := by
    rw [hl0, hlN]
    have hg : 0 < Real.exp (π / T) := Real.exp_pos _
    nlinarith [hpos, hmono, hg1, mul_pos hpos hg, mul_pos (hpos.trans_le hmono) hg]
  calc (1 + Real.exp (π / T)) * |∑ n ∈ range (N + 1), (-1 : ℝ) ^ n * cellArea β T (k₀ + n)| ≤ _ := h
    _ ≤ M * ((1 + Real.exp (π / T)) ^ 2 * contactAt β T (k₀ + N)) := mul_le_mul_of_nonneg_left hlen hM0
    _ = _ := by ring

#print axioms RHV6Fresh.integral_psi_eq
#print axioms RHV6Fresh.rawDemand_intervalIntegrable
#print axioms RHV6Fresh.demandArea_eq_integral
#print axioms RHV6Fresh.demandArea_sub_eq_integral
#print axioms RHV6Fresh.abs_demandArea_le_of_bound
#print axioms RHV6Fresh.abs_demandArea_sub_le_of_variation
#print axioms RHV6Fresh.cellArea_eq_integral
#print axioms RHV6Fresh.abs_cellArea_le_of_bound
#print axioms RHV6Fresh.exitDeviation_eq_integral
#print axioms RHV6Fresh.abs_exitDeviation_le_of_variation
#print axioms RHV6Fresh.abs_localGrammarTerm_le_of_demand_bound
#print axioms RHV6Fresh.sum_cellLength_eq
#print axioms RHV6Fresh.budget_le_of_demand_bound
#print axioms RHV6Fresh.budget_le_of_demand_bound'

end RHV6Fresh
