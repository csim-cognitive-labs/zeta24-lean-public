/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PairBreakAtPrime
import Mathlib.NumberTheory.PrimeCounting

/-!
# RHV6Fresh — Terminal/PairAsymmetryOverPrimes : l'asymétrie de la paire intégrée sur les premiers (Ψ3, E469, §19.103)
(plan Ψ, 2026-11-13 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse, aucun axiome, aucun `sorry`)

Stratégie (règle R-Ψ). Cible (H17 R3' en série) : les termes du zéro et du miroir ont le même poids cumulé sur la série des premiers.
Objet cumulé : somme, sur les premiers jusqu'à N, du logarithme du rapport des modules des deux puissances `p^{1−β}` et `p^β`.
Pourquoi le ponctuel échoue : en un premier, le rapport est `p^{1−2β}` (E450 `pair_break_ratio`) : une identité, vraie pour tout β.
Signature d'un hors-ligne : le cumul vaut `(1 − 2β)` fois la fonction de Tchebychev `θ(N)`, non borné ; par premier, la part est la
fraction `|1 − 2β| ≤ 1` du poids `log p` (fractionnel). Suite : côté premiers par Ψ2 (les autres hauteurs doivent payer la paire sur
TOUS les premiers).

* A1 `pairAsymmetryAt`, `pairAsymmetryAt_eq`, `pairAsymmetryAt_eq_neg_log_ratio_power` (lien à E450), `abs_pairAsymmetryAt_le`.
* A2 `primeSet`, `chebyshevTheta`, `cumulativeAsymmetry`, `cumulativeAsymmetry_eq`.
* A3 `cumulativeAsymmetry_eq_zero_iff` : nulle ⟺ ligne (dès que 2 ≤ N).
* A4 `chebyshevTheta_ge`, `chebyshevTheta_unbounded` (nombre infini de premiers, via `Nat.tendsto_primeCounting'`).
* A5 `cumulativeAsymmetry_unbounded_of_lt_half`, `cumulativeAsymmetry_unbounded_below_of_half_lt`.
Portée : identités et équivalences exactes ; la dérive cumulée lit la position radiale ; rien n'exclut seul un zéro hors ligne.
-/

namespace RHV6Fresh

open Real Finset

/-! ## A1 : asymétrie en un premier -/

noncomputable def pairAsymmetryAt (β : ℝ) (p : ℕ) : ℝ :=
  Real.log ((p : ℝ) ^ (1 - β)) - Real.log ((p : ℝ) ^ β)

theorem pairAsymmetryAt_eq {β : ℝ} {p : ℕ} (hp : 0 < p) : pairAsymmetryAt β p = (1 - 2 * β) * Real.log p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  unfold pairAsymmetryAt
  rw [Real.log_rpow hp', Real.log_rpow hp']
  ring

theorem pairAsymmetryAt_eq_neg_log_ratio_power {β : ℝ} {p : ℕ} (hp : 0 < p) :
    pairAsymmetryAt β p = -Real.log ((p : ℝ) ^ (2 * β - 1)) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [pairAsymmetryAt_eq hp, Real.log_rpow hp']
  ring

theorem abs_pairAsymmetryAt_le {β : ℝ} {p : ℕ} (hp : 0 < p) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    |pairAsymmetryAt β p| ≤ Real.log p := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  rw [pairAsymmetryAt_eq hp, abs_mul, abs_of_nonneg (Real.log_nonneg hp')]
  have : |1 - 2 * β| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  exact mul_le_of_le_one_left (Real.log_nonneg hp') this

/-! ## A2 : cumul sur les premiers -/

noncomputable def primeSet (N : ℕ) : Finset ℕ := (range (N + 1)).filter Nat.Prime

noncomputable def chebyshevTheta (N : ℕ) : ℝ := ∑ p ∈ primeSet N, Real.log p

noncomputable def cumulativeAsymmetry (β : ℝ) (N : ℕ) : ℝ := ∑ p ∈ primeSet N, pairAsymmetryAt β p

theorem mem_primeSet {N p : ℕ} : p ∈ primeSet N ↔ p ≤ N ∧ p.Prime := by
  unfold primeSet
  rw [mem_filter, mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

theorem cumulativeAsymmetry_eq (β : ℝ) (N : ℕ) : cumulativeAsymmetry β N = (1 - 2 * β) * chebyshevTheta N := by
  unfold cumulativeAsymmetry chebyshevTheta
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact pairAsymmetryAt_eq (mem_primeSet.mp hp).2.pos

/-! ## A3 : nulle ⟺ ligne -/

theorem chebyshevTheta_pos {N : ℕ} (hN : 2 ≤ N) : 0 < chebyshevTheta N := by
  unfold chebyshevTheta
  have h2 : 2 ∈ primeSet N := mem_primeSet.mpr ⟨hN, Nat.prime_two⟩
  have hnn : ∀ p ∈ primeSet N, 0 ≤ Real.log (p : ℝ) := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (mem_primeSet.mp hp).2.one_lt.le)
  have hle := single_le_sum hnn h2
  have hpos : 0 < Real.log ((2 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  linarith

theorem cumulativeAsymmetry_eq_zero_iff {β : ℝ} {N : ℕ} (hN : 2 ≤ N) : cumulativeAsymmetry β N = 0 ↔ β = 1 / 2 := by
  rw [cumulativeAsymmetry_eq, mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · linarith
    · exact absurd h (chebyshevTheta_pos hN).ne'
  · intro h
    left
    rw [h]
    ring

/-! ## A4 : la fonction de Tchebychev n'est pas bornée -/

theorem primeSet_card (N : ℕ) : (primeSet N).card = Nat.primeCounting N := by
  unfold primeSet
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

theorem chebyshevTheta_ge (N : ℕ) : (Nat.primeCounting N : ℝ) * Real.log 2 ≤ chebyshevTheta N := by
  unfold chebyshevTheta
  rw [← primeSet_card, ← nsmul_eq_mul]
  apply card_nsmul_le_sum
  intro p hp
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primeSet.mp hp).2.two_le
  exact Real.log_le_log (by norm_num) h2

theorem primeCounting_unbounded (M : ℕ) : ∃ N : ℕ, M < Nat.primeCounting N := by
  obtain ⟨i, hi⟩ := (Filter.tendsto_atTop_atTop.mp Nat.tendsto_primeCounting') (M + 1)
  refine ⟨i, ?_⟩
  have := hi (i + 1) (by omega)
  rw [Nat.primeCounting]
  omega

theorem chebyshevTheta_unbounded (M : ℝ) : ∃ N : ℕ, M < chebyshevTheta N := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_gt (M / Real.log 2)
  obtain ⟨N, hN⟩ := primeCounting_unbounded m
  refine ⟨N, lt_of_lt_of_le ?_ (chebyshevTheta_ge N)⟩
  have h1 : M < m * Real.log 2 := by rwa [div_lt_iff₀ hl] at hm
  have h2 : (m : ℝ) < Nat.primeCounting N := by exact_mod_cast hN
  nlinarith

/-! ## A5 : la dérive cumulée de la paire n'est pas bornée hors ligne -/

theorem cumulativeAsymmetry_unbounded_of_lt_half {β : ℝ} (hβ : β < 1 / 2) (M : ℝ) :
    ∃ N : ℕ, M < cumulativeAsymmetry β N := by
  have hc : 0 < 1 - 2 * β := by linarith
  obtain ⟨N, hN⟩ := chebyshevTheta_unbounded (M / (1 - 2 * β))
  refine ⟨N, ?_⟩
  rw [cumulativeAsymmetry_eq]
  rwa [div_lt_iff₀' hc] at hN

theorem cumulativeAsymmetry_unbounded_below_of_half_lt {β : ℝ} (hβ : 1 / 2 < β) (M : ℝ) :
    ∃ N : ℕ, cumulativeAsymmetry β N < -M := by
  have hc : 0 < 2 * β - 1 := by linarith
  obtain ⟨N, hN⟩ := chebyshevTheta_unbounded (M / (2 * β - 1))
  refine ⟨N, ?_⟩
  rw [cumulativeAsymmetry_eq]
  rw [div_lt_iff₀' hc] at hN
  linarith

#print axioms pairAsymmetryAt_eq
#print axioms cumulativeAsymmetry_eq
#print axioms cumulativeAsymmetry_eq_zero_iff
#print axioms chebyshevTheta_unbounded
#print axioms cumulativeAsymmetry_unbounded_of_lt_half
#print axioms cumulativeAsymmetry_unbounded_below_of_half_lt

end RHV6Fresh
