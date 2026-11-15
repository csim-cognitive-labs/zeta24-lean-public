/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PrimeGapReconstruction

/-!
# RHV6Fresh — composition terminale de l'accumulation par contacts (mission, 2026-11-03, phase 11)

Compose les cinq modules A–E avec le corpus E405/E406 (`RawMeetingRemainder`, `RawSpectralChannel`).

**Chaîne compilée (inconditionnelle)** :
contacts → accumulation signée → variation spectrale finie → limite par hauteur (canal intégré)
→ `ψ` → `Λ` → événements premiers → écarts premiers.
`contact_chain_arithmetic` : les pas tronqués par contacts tendent vers `ψ(N)` ;
`psiRemainder_eq_reconstructed`, `psiRemainder_limit_contact_accumulation` : le reste brut d'E405
`ψ(N) − N` est la limite des accumulations par contacts tronquées moins `N`.

**Cible OFF (niveau 7) — ce qui est compilé et ce qui ne l'est pas** :
* `riemannHypothesis_of_contact_accumulation_bound` : SI la limite des accumulations par contacts
  moins `N` est bornée par `C·E^{1/2+ε}` aux deux côtés de chaque événement brut, ALORS RH. C'est
  `riemannHypothesis_of_psiRemainder_at_events` (E405) réécrit sur l'objet reconstruit.
* `off_member_forces_contact_excess` : tout membre OFF (`Re ρ > θ`) force un événement brut où la
  limite des accumulations moins `E` dépasse `C·E^θ` (E405, réécrit).
* La borne elle-même N'EST PAS démontrée ici : l'accumulation par contacts est une identité
  télescopique (`contact_accumulation_partition_independent`) et n'apporte aucune information
  au-delà de la formule explicite. La prémisse `∀ ε, ∃ C, …` est équivalente à RH
  (`riemannHypothesis_iff_remainder_growth_all_eps`, corpus) : elle n'est jamais posée.

Aucun `sorry`, aucun axiome, aucune prémisse posée vraie.
-/

namespace RHV6Fresh

open RHV3Lean ArithmeticFunction Filter Topology

/-- **La chaîne arithmétique** : les pas tronqués par contacts tendent vers `ψ(N)` (`N ≥ 2`). -/
theorem contact_chain_arithmetic (k₀ : ExplicitIndex → ℤ) (n : ExplicitIndex → ℕ) {N : ℕ}
    (hN : 2 ≤ N) :
    Tendsto (fun H : ℝ => truncatedStep H k₀ n N) atTop (𝓝 (Chebyshev.psi (N : ℝ) : ℂ)) := by
  rw [← reconstructedPsi_eq_psi hN]
  exact reconstructedPsi_eq_limit_contact_accumulation k₀ n hN

/-- Le reste brut d'E405 est `ψ̂(N) − N` (`N ≥ 2`). -/
theorem psiRemainder_eq_reconstructed {N : ℕ} (hN : 2 ≤ N) :
    ((psiRemainder N : ℝ) : ℂ) = reconstructedPsi N - N := by
  unfold psiRemainder
  rw [massA_eq_psi, reconstructedPsi_eq_psi hN]
  push_cast
  ring

/-- **Le reste brut aux rencontres est la limite des accumulations par contacts moins `N`.** -/
theorem psiRemainder_limit_contact_accumulation (k₀ : ExplicitIndex → ℤ) (n : ExplicitIndex → ℕ)
    {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun H : ℝ => truncatedStep H k₀ n N - N) atTop
      (𝓝 ((psiRemainder N : ℝ) : ℂ)) := by
  rw [psiRemainder_eq_reconstructed hN]
  exact (reconstructedPsi_eq_limit_contact_accumulation k₀ n hN).sub_const _

/-- **Niveau 7, forme conditionnelle** : si l'objet reconstruit par accumulation, moins `E`, est
borné par `C·E^{1/2+ε}` aux deux côtés de chaque événement brut, alors RH. La prémisse est
équivalente à RH (corpus) et n'est pas démontrée. -/
theorem riemannHypothesis_of_contact_accumulation_bound
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℕ, IsRawEvent E → 3 ≤ E →
      ‖reconstructedPsi E - E‖ ≤ C * (E : ℝ) ^ (1 / 2 + ε) ∧
        ‖reconstructedPsi (E - 1) - ((E - 1 : ℕ) : ℂ)‖ ≤ C * (E : ℝ) ^ (1 / 2 + ε)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_psiRemainder_at_events
  intro ε hε
  obtain ⟨C, hC, hE⟩ := h ε hε
  -- l'événement `E = 2` est absorbé par une constante plus grande
  refine ⟨max C (|psiRemainder 2| + |psiRemainder 1|), by positivity, fun E hEv => ?_⟩
  have hE2 : 2 ≤ E := by
    by_contra hlt
    push Not at hlt
    interval_cases E <;> exact hEv (by simp)
  have hE1 : (1 : ℝ) ≤ E := by exact_mod_cast (by omega : 1 ≤ E)
  have hpow : (1 : ℝ) ≤ (E : ℝ) ^ (1 / 2 + ε) := Real.one_le_rpow hE1 (by linarith)
  have hKnn : 0 ≤ max C (|psiRemainder 2| + |psiRemainder 1|) := by positivity
  rcases Nat.lt_or_ge E 3 with h3 | h3
  · have hE : E = 2 := by omega
    subst hE
    have hK : |psiRemainder 2| + |psiRemainder 1| ≤
        max C (|psiRemainder 2| + |psiRemainder 1|) * ((2 : ℕ) : ℝ) ^ (1 / 2 + ε) :=
      (le_max_right _ _).trans (le_mul_of_one_le_right hKnn hpow)
    constructor
    · linarith [abs_nonneg (psiRemainder 1)]
    · change |psiRemainder 1| ≤ _
      linarith [abs_nonneg (psiRemainder 2)]
  · obtain ⟨h1, h2⟩ := hE E hEv h3
    rw [← psiRemainder_eq_reconstructed (by omega)] at h1
    rw [← psiRemainder_eq_reconstructed (by omega : 2 ≤ E - 1)] at h2
    simp only [Complex.norm_real, Real.norm_eq_abs] at h1 h2
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
      h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩

/-- **Niveau 7, lecture OFF** : un membre OFF (`Re ρ > θ ≥ 0`) force un événement brut où la
limite des accumulations par contacts moins `E` dépasse `C·E^θ` d'un côté ou de l'autre (E405,
réécrit sur l'objet reconstruit). Cela ne contredit rien tant que la borne n'est pas démontrée. -/
theorem off_member_forces_contact_excess {θ : ℝ} (hθ : 0 ≤ θ) (ρ : ExplicitIndex)
    (hρ : θ < (ρ : ℂ).re) (C : ℝ) :
    ∃ E : ℕ, IsRawEvent E ∧
      (C * (E : ℝ) ^ θ < |psiRemainder E| ∨ C * (E : ℝ) ^ θ < |psiRemainder (E - 1)|) ∧
      (2 ≤ E → ((psiRemainder E : ℝ) : ℂ) = reconstructedPsi E - E) :=
  let ⟨E, hE, hx⟩ := off_member_forces_raw_excess_at_event hθ ρ hρ C
  ⟨E, hE, hx, fun h2 => psiRemainder_eq_reconstructed h2⟩

#print axioms contact_chain_arithmetic
#print axioms riemannHypothesis_of_contact_accumulation_bound
#print axioms off_member_forces_contact_excess

end RHV6Fresh
