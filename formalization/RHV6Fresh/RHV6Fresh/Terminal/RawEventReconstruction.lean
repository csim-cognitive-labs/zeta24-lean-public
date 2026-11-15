/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ContactSpectralLimit

/-!
# RHV6Fresh — reconstruction des événements arithmétiques depuis le canal spectral
(mission, 2026-11-03, module D)

L'objet reconstruit est SPECTRAL dans sa définition : `spectralPrimitive x = fond(x) + canal des
zéros(x)` (`backgroundPrimitive + zeroChannelPrimitive`, corpus), jamais un alias de `ψ`. Puis :

* `reconstructedPsi N = spectralPrimitive (N+1) − spectralPrimitive N` ;
  **`reconstructedPsi_eq_psi`** (`N ≥ 2`) : `= ψ(N)`, par la formule explicite lissée compilée
  (`smoothedZeroPrimitive_nat_difference`). Théorème analytique inconditionnel.
* `reconstructedVonMangoldt N = reconstructedPsi N − reconstructedPsi (N−1)` ;
  **`reconstructedVonMangoldt_eq`** (`N ≥ 3`) : `= Λ(N)`.
* `reconstructedRawEvent N : reconstructedVonMangoldt N ≠ 0` ⟺ `IsRawEvent N` (`Λ(N) ≠ 0`).
* **L'opérateur arithmétique supplémentaire** qui sépare les premiers des puissances de premiers :
  `reconstructedPrimeEvent N : reconstructedVonMangoldt N = log N`.
  `vonMangoldt_eq_log_iff` (`N ≥ 2`) : `Λ(N) = log N ⟺ N premier` (une puissance `p^k`, `k ≥ 2`,
  porte `log p < log N`). D'où **`reconstructedPrimeEvent_iff`** : `⟺ N premier` (`N ≥ 3`).
* **`reconstructedPsi_eq_limit_contact_accumulation`** : `reconstructedPsi N` est la limite,
  quand la hauteur de troncature tend vers l'infini, du fond plus les accumulations par contacts
  du canal intégré (chaque Tour sur ses propres contacts, bords compris) ; de même pour `Λ`
  (`reconstructedVonMangoldt_eq_limit_contact_accumulation`).

Non-circularité : aucune définition ne mentionne `Chebyshev.psi`, `Λ`, ni un premier ; ceux-ci
n'apparaissent que dans les ÉNONCÉS des théorèmes d'égalité (validation).
Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean ArithmeticFunction Filter Topology

/-! ## 1. La primitive spectrale et `ψ` reconstruit -/

/-- **La primitive spectrale** : fond compilé + canal des zéros non triviaux. Définie du seul côté
spectral. -/
noncomputable def spectralPrimitive (x : ℝ) : ℂ := backgroundPrimitive x + zeroChannelPrimitive x

theorem spectralPrimitive_eq {x : ℝ} (hx : 1 < x) : spectralPrimitive x = smoothedZeroPrimitive x :=
  (smoothedZeroPrimitive_eq_background_add_zeros hx).symm

/-- **`ψ` reconstruit** : le pas de la primitive spectrale entre `N` et `N + 1`. -/
noncomputable def reconstructedPsi (N : ℕ) : ℂ := stepAt spectralPrimitive N

/-- **`ψ̂ = ψ`** pour `N ≥ 2` (formule explicite lissée compilée). -/
theorem reconstructedPsi_eq_psi {N : ℕ} (hN : 2 ≤ N) :
    reconstructedPsi N = (Chebyshev.psi (N : ℝ) : ℂ) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN2 : (1 : ℝ) < (N : ℝ) + 1 := by linarith
  unfold reconstructedPsi stepAt
  rw [spectralPrimitive_eq hN1, spectralPrimitive_eq hN2]
  exact smoothedZeroPrimitive_nat_difference hN

/-! ## 2. Les poids reconstruits et les événements -/

/-- **`Λ̂(N)`** : différence de deux pas consécutifs de la primitive spectrale. -/
noncomputable def reconstructedVonMangoldt (N : ℕ) : ℂ :=
  reconstructedPsi N - reconstructedPsi (N - 1)

/-- **`Λ̂ = Λ`** pour `N ≥ 3`. -/
theorem reconstructedVonMangoldt_eq {N : ℕ} (hN : 3 ≤ N) :
    reconstructedVonMangoldt N = ((Λ N : ℝ) : ℂ) := by
  unfold reconstructedVonMangoldt
  rw [reconstructedPsi_eq_psi (by omega), reconstructedPsi_eq_psi (by omega : 2 ≤ N - 1)]
  rw [← Complex.ofReal_sub, ← thm_weightFromPsi_chebyshev (by omega : 1 ≤ N)]
  unfold fnWeightFromPsi
  congr 2
  push_cast [Nat.cast_sub (by omega : 1 ≤ N)]
  rfl

/-- Un événement brut reconstruit : poids reconstruit non nul. -/
def reconstructedRawEvent (N : ℕ) : Prop := reconstructedVonMangoldt N ≠ 0

theorem reconstructedRawEvent_iff {N : ℕ} (hN : 3 ≤ N) :
    reconstructedRawEvent N ↔ IsRawEvent N := by
  unfold reconstructedRawEvent IsRawEvent
  rw [reconstructedVonMangoldt_eq hN]
  simp

/-- **L'opérateur arithmétique supplémentaire** : `Λ(N) = log N ⟺ N premier` (`N ≥ 2`). Une
puissance `p^k`, `k ≥ 2`, porte `Λ = log p < log N`. -/
theorem vonMangoldt_eq_log_iff {N : ℕ} (hN : 2 ≤ N) : Λ N = Real.log N ↔ N.Prime := by
  constructor
  · intro h
    have hpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    have hne : Λ N ≠ 0 := by rw [h]; exact hpos.ne'
    have hpp : IsPrimePow N := by
      by_contra hc
      exact hne (vonMangoldt_eq_zero_iff.mpr hc)
    rw [vonMangoldt_apply, if_pos hpp] at h
    have hmin : (N.minFac : ℝ) = N := by
      apply Real.log_injOn_pos _ _ h
      · exact Set.mem_Ioi.mpr (by exact_mod_cast (Nat.minFac_pos N))
      · exact Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < N))
    exact Nat.prime_def_minFac.mpr ⟨hN, by exact_mod_cast hmin⟩
  · intro hp
    exact vonMangoldt_apply_prime hp

/-- **L'événement premier reconstruit** : le poids reconstruit vaut `log N` (fonction analytique
de `N`, aucune donnée arithmétique). -/
def reconstructedPrimeEvent (N : ℕ) : Prop := reconstructedVonMangoldt N = ((Real.log N : ℝ) : ℂ)

/-- **`N` est un événement premier reconstruit ⟺ `N` est premier** (`N ≥ 3`). -/
theorem reconstructedPrimeEvent_iff {N : ℕ} (hN : 3 ≤ N) : reconstructedPrimeEvent N ↔ N.Prime := by
  unfold reconstructedPrimeEvent
  rw [reconstructedVonMangoldt_eq hN, Complex.ofReal_inj]
  exact vonMangoldt_eq_log_iff (by omega)

/-! ## 3. Le pont avec l'accumulation par contacts -/

/-- Le pas tronqué : fond plus accumulations par contacts tronquées, pondérées par `N + 1` et `N`
(convention de primitive `x · Σ`). L'accumulation de `1` à `y` donne `Σ_ρ F_ρ(y) − Σ_ρ F_ρ(1)`. -/
noncomputable def truncatedStep (H : ℝ) (k₀ : ExplicitIndex → ℤ) (n : ExplicitIndex → ℕ)
    (N : ℕ) : ℂ :=
  stepAt backgroundPrimitive N +
    ((((N : ℝ) + 1 : ℝ) : ℂ) * (truncatedAccumulation H integratedTowerTerm k₀ n 1 ((N : ℝ) + 1) +
        ∑ ρ ∈ lowFrequencies H, integratedTowerTerm ρ 1) -
      ((N : ℝ) : ℂ) * (truncatedAccumulation H integratedTowerTerm k₀ n 1 (N : ℝ) +
        ∑ ρ ∈ lowFrequencies H, integratedTowerTerm ρ 1))

theorem truncatedStep_eq (H : ℝ) (k₀ : ExplicitIndex → ℤ) (n : ExplicitIndex → ℕ) (N : ℕ) :
    truncatedStep H k₀ n N = stepAt backgroundPrimitive N +
      ((((N : ℝ) + 1 : ℝ) : ℂ) * ∑ ρ ∈ lowFrequencies H, integratedTowerTerm ρ ((N : ℝ) + 1) -
        ((N : ℝ) : ℂ) * ∑ ρ ∈ lowFrequencies H, integratedTowerTerm ρ (N : ℝ)) := by
  unfold truncatedStep
  rw [truncatedAccumulation_eq, truncatedAccumulation_eq, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  ring

/-- **`ψ̂(N)` est la limite des accumulations par contacts tronquées** (canal intégré, `N ≥ 2`). -/
theorem reconstructedPsi_eq_limit_contact_accumulation (k₀ : ExplicitIndex → ℤ)
    (n : ExplicitIndex → ℕ) {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun H : ℝ => truncatedStep H k₀ n N) atTop (𝓝 (reconstructedPsi N)) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN2 : (1 : ℝ) < (N : ℝ) + 1 := by linarith
  have h1 := (integrated_contact_limit_eq_spectral hN2).const_mul ((((N : ℝ) + 1 : ℝ) : ℂ))
  have h2 := (integrated_contact_limit_eq_spectral hN1).const_mul (((N : ℝ) : ℂ))
  have h := (h1.sub h2).const_add (stepAt backgroundPrimitive N)
  have hlim : stepAt backgroundPrimitive N +
      ((((N : ℝ) + 1 : ℝ) : ℂ) * ∑' ρ : ExplicitIndex, integratedTowerTerm ρ ((N : ℝ) + 1) -
        ((N : ℝ) : ℂ) * ∑' ρ : ExplicitIndex, integratedTowerTerm ρ (N : ℝ)) =
      reconstructedPsi N := by
    unfold reconstructedPsi spectralPrimitive stepAt zeroChannelPrimitive
    simp only [integratedTowerTerm_eq_residue]
    ring
  rw [hlim] at h
  refine h.congr (fun H => ?_)
  rw [truncatedStep_eq]

/-- **`Λ̂(N)` est la limite des accumulations par contacts tronquées** (`N ≥ 3`). -/
theorem reconstructedVonMangoldt_eq_limit_contact_accumulation (k₀ : ExplicitIndex → ℤ)
    (n : ExplicitIndex → ℕ) {N : ℕ} (hN : 3 ≤ N) :
    Tendsto (fun H : ℝ => truncatedStep H k₀ n N - truncatedStep H k₀ n (N - 1)) atTop
      (𝓝 (reconstructedVonMangoldt N)) :=
  (reconstructedPsi_eq_limit_contact_accumulation k₀ n (by omega : 2 ≤ N)).sub
    (reconstructedPsi_eq_limit_contact_accumulation k₀ n (by omega : 2 ≤ N - 1))

#print axioms reconstructedPsi_eq_psi
#print axioms reconstructedPrimeEvent_iff
#print axioms reconstructedVonMangoldt_eq_limit_contact_accumulation

end RHV6Fresh
