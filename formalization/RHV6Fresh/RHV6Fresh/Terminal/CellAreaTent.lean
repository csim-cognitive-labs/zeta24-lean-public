/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CellAreaGrammar

/-!
# RHV6Fresh — Terminal/CellAreaTent : le terme local comme discrépance contre une tente, et sa mémoire un (E474, §19.107)
(2026-11-13 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse, aucun axiome, aucun `sorry`)

Stratégie (règle R-Ψ). Cible : donner au terme local `L_k` d'E473 (`a_{k+1} − e^{π/T} a_k = L_k`) sa forme arithmétique EXACTE :
la somme des premiers des deux cellules consécutives contre un noyau chapeau continu, moins l'intégrale de ce chapeau (H1), et sa
forme à mémoire un : différence de deux déviations de sortie consécutives plus la variation de la demande sur la cellule (H2).
Objet cumulé : la somme alternée des termes locaux, réécrite sur les déviations de sortie et les variations de demande.
Pourquoi le ponctuel ne suffit pas : inchangé. Signature d'un hors-ligne : inchangée (E472). Suite dans les deux issues : le
module `CellAreaIntegral` écrit l'aire comme intégrale de la demande et borne le budget par le suprémum de la demande.

* H1 `tentKernel`, `contactAt_succ`, `contactAt_two`, `tentKernel_nonneg`, `tentKernel_le`, `tentKernel_peak`,
  `localGrammarTerm_eq_tent_sum`.
* H2 `localGrammarTerm_eq_memory_one`, `alternating_local_eq_exit_form`.
Portée : identités exactes, valables sur la ligne comme hors ligne ; aucun théorème compilé n'exclut un hors-ligne.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction Finset

/-! ## H1 : le noyau chapeau de deux cellules consécutives -/

/-- Noyau chapeau de la cellule double `(C_k, C_{k+2}]` : pente `e^{π/T}` de `C_k` à `C_{k+1}`, pente `−1` de `C_{k+1}` à `C_{k+2}`,
sommet en `C_{k+1}` de hauteur `ℓ_{k+1}`. -/
noncomputable def tentKernel (β T : ℝ) (k : ℤ) (t : ℝ) : ℝ :=
  min (Real.exp (π / T) * (t - contactAt β T k)) (contactAt β T (k + 2) - t)

theorem contactAt_succ {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    contactAt β T (k + 1) = Real.exp (π / T) * contactAt β T k := by
  have h := contactAt_ratio (β := β) hT.ne' k
  rw [div_eq_iff (contactAt_pos β T _).ne'] at h
  rw [h]

theorem contactAt_two {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    contactAt β T (k + 2) = Real.exp (π / T) * (Real.exp (π / T) * contactAt β T k) := by
  have h := contactAt_succ (β := β) hT (k + 1)
  rw [show (k + 1 + 1 : ℤ) = k + 2 by ring, contactAt_succ hT k] at h
  exact h

/-- Sur `(C_k, C_{k+1}]`, le chapeau est la branche montante. -/
theorem tentKernel_eq_left {β T : ℝ} (hT : 0 < T) (k : ℤ) {t : ℝ} (ht : t ≤ contactAt β T (k + 1)) :
    tentKernel β T k t = Real.exp (π / T) * (t - contactAt β T k) := by
  unfold tentKernel
  have hg : 0 < Real.exp (π / T) := Real.exp_pos _
  rw [contactAt_succ hT k] at ht
  rw [contactAt_two hT k]
  refine min_eq_left ?_
  have := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 1 + Real.exp (π / T))
  nlinarith

/-- Sur `[C_{k+1}, C_{k+2}]`, le chapeau est la branche descendante. -/
theorem tentKernel_eq_right {β T : ℝ} (hT : 0 < T) (k : ℤ) {t : ℝ} (ht : contactAt β T (k + 1) ≤ t) :
    tentKernel β T k t = contactAt β T (k + 2) - t := by
  unfold tentKernel
  have hg : 0 < Real.exp (π / T) := Real.exp_pos _
  rw [contactAt_succ hT k] at ht
  rw [contactAt_two hT k]
  refine min_eq_right ?_
  have := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 1 + Real.exp (π / T))
  nlinarith

theorem tentKernel_nonneg {β T : ℝ} (k : ℤ) {t : ℝ} (h1 : contactAt β T k ≤ t) (h2 : t ≤ contactAt β T (k + 2)) :
    0 ≤ tentKernel β T k t := by
  unfold tentKernel
  refine le_min ?_ ?_
  · exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr h1)
  · exact sub_nonneg.mpr h2

/-- Le chapeau culmine en `C_{k+1}` à la hauteur `ℓ_{k+1}`. -/
theorem tentKernel_peak {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    tentKernel β T k (contactAt β T (k + 1)) = cellLength β T (k + 1) := by
  rw [tentKernel_eq_right hT k le_rfl]
  unfold cellLength
  rw [show (k + 1 + 1 : ℤ) = k + 2 by ring]

/-- Le chapeau ne dépasse jamais sa hauteur `ℓ_{k+1}`. -/
theorem tentKernel_le {β T : ℝ} (hT : 0 < T) (k : ℤ) (t : ℝ) :
    tentKernel β T k t ≤ cellLength β T (k + 1) := by
  have hg : 0 < Real.exp (π / T) := Real.exp_pos _
  have hl : cellLength β T (k + 1) = contactAt β T (k + 2) - contactAt β T (k + 1) := by
    unfold cellLength
    rw [show (k + 1 + 1 : ℤ) = k + 2 by ring]
  rcases le_total t (contactAt β T (k + 1)) with ht | ht
  · rw [tentKernel_eq_left hT k ht, hl, contactAt_two hT k, contactAt_succ hT k]
    rw [contactAt_succ hT k] at ht
    nlinarith [mul_le_mul_of_nonneg_left ht hg.le]
  · rw [tentKernel_eq_right hT k ht, hl]
    linarith

/-- **H1, identité de la tente.** Le terme local est la somme des premiers des deux cellules contre le chapeau, moins l'intégrale
du chapeau `e^{π/T}(1 + e^{π/T}) ℓ_k²/2`. -/
theorem localGrammarTerm_eq_tent_sum {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    localGrammarTerm β T k =
      ∑ n ∈ Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 2)⌋₊, Λ n * tentKernel β T k n -
        Real.exp (π / T) * (1 + Real.exp (π / T)) * cellLength β T k ^ 2 / 2 := by
  rw [localGrammarTerm_eq hT k]
  have hk2 : (k + 1 + 1 : ℤ) = k + 2 := by ring
  have h01 : ⌊contactAt β T k⌋₊ ≤ ⌊contactAt β T (k + 1)⌋₊ := Nat.floor_mono (contactAt_mono hT (by omega))
  have h12 : ⌊contactAt β T (k + 1)⌋₊ ≤ ⌊contactAt β T (k + 2)⌋₊ := Nat.floor_mono (contactAt_mono hT (by omega))
  have hsplit := Finset.sum_Ioc_consecutive (fun n => Λ n * tentKernel β T k n) h01 h12
  rw [← hsplit]
  have hleft : ∑ n ∈ Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 1)⌋₊, Λ n * tentKernel β T k n =
      Real.exp (π / T) * cellEntryWeight β T k := by
    unfold cellEntryWeight
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : (n : ℝ) ≤ contactAt β T (k + 1) :=
      (Nat.le_floor_iff (contactAt_pos β T _).le).mp (Finset.mem_Ioc.mp hn).2
    rw [tentKernel_eq_left hT k hn']
    ring
  have hright : ∑ n ∈ Ioc ⌊contactAt β T (k + 1)⌋₊ ⌊contactAt β T (k + 2)⌋₊, Λ n * tentKernel β T k n =
      cellExitWeight β T (k + 1) := by
    unfold cellExitWeight
    rw [hk2]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : contactAt β T (k + 1) ≤ (n : ℝ) :=
      ((Nat.floor_lt (contactAt_pos β T _).le).mp (Finset.mem_Ioc.mp hn).1).le
    rw [tentKernel_eq_right hT k hn']
  rw [hleft, hright]
  ring

/-! ## H2 : la mémoire un du terme local -/

/-- **H2, mémoire un.** `L_k = ε_{k+1} − e^{π/T} ε_k + e^{π/T} ℓ_k (D(C_{k+1}) − D(C_k))` : le terme local est la différence de deux
déviations de sortie consécutives plus la variation de la demande sur la cellule `k` (poids des premiers franchis moins longueur). -/
theorem localGrammarTerm_eq_memory_one {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    localGrammarTerm β T k = exitDeviation β T (k + 1) - Real.exp (π / T) * exitDeviation β T k +
      Real.exp (π / T) * cellLength β T k * (rawDemand (contactAt β T (k + 1)) - rawDemand (contactAt β T k)) := by
  unfold localGrammarTerm
  have h1 := deviation_add β T k
  have h2 := rawDemand_next_contact (β := β) hT k
  linear_combination Real.exp (π / T) * h1 - Real.exp (π / T) * cellLength β T k * h2

/-- **Somme alternée des termes locaux, forme de sortie.** Toute la somme alternée se lit sur les déviations de sortie (premiers
INTÉRIEURS à chaque cellule) et sur les variations de demande pondérées par la longueur, à deux bords près. -/
theorem alternating_local_eq_exit_form {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (N : ℕ) :
    ∑ n ∈ range N, (-1 : ℝ) ^ n * localGrammarTerm β T (k₀ + n) =
      -(1 + Real.exp (π / T)) * ∑ n ∈ range N, (-1 : ℝ) ^ n * exitDeviation β T (k₀ + n) +
        exitDeviation β T k₀ - (-1 : ℝ) ^ N * exitDeviation β T (k₀ + N) +
        Real.exp (π / T) * ∑ n ∈ range N, (-1 : ℝ) ^ n * cellLength β T (k₀ + n) *
          (rawDemand (contactAt β T (k₀ + n + 1)) - rawDemand (contactAt β T (k₀ + n))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hc : (k₀ + ((N + 1 : ℕ) : ℤ)) = k₀ + N + 1 := by push_cast; ring
    simp only [Finset.sum_range_succ, hc]
    rw [ih, localGrammarTerm_eq_memory_one hT (k₀ + N), pow_succ (-1 : ℝ) N]
    ring

#print axioms RHV6Fresh.contactAt_succ
#print axioms RHV6Fresh.contactAt_two
#print axioms RHV6Fresh.tentKernel_eq_left
#print axioms RHV6Fresh.tentKernel_eq_right
#print axioms RHV6Fresh.tentKernel_nonneg
#print axioms RHV6Fresh.tentKernel_peak
#print axioms RHV6Fresh.tentKernel_le
#print axioms RHV6Fresh.localGrammarTerm_eq_tent_sum
#print axioms RHV6Fresh.localGrammarTerm_eq_memory_one
#print axioms RHV6Fresh.alternating_local_eq_exit_form

end RHV6Fresh
