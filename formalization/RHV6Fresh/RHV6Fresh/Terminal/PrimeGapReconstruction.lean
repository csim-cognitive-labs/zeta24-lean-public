/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RawEventReconstruction

/-!
# RHV6Fresh — reconstruction des écarts premiers depuis les événements reconstruits
(mission, 2026-11-03, module E)

Les premiers reconstruits sont énumérés par `Nat.nth` sur le prédicat SPECTRAL
`ReconstructedPrimeAbove N := 3 ≤ N ∧ reconstructedPrimeEvent N` (aucun premier réel n'entre dans
la définition). Les écarts reconstruits sont leurs différences consécutives.

* `reconstructedPrimeAbove_eq_primeAbove` : les deux prédicats coïncident (module D).
* **`reconstructedPrimeAtRank_eq_primeAtRank`**, **`reconstructedPrimeGap_eq_actualGap`**,
  **`reconstructedGapSequence_eq`** : premiers, écarts et suite des écarts reconstruits coïncident
  avec les vrais, rang par rang.
* `reconstructedPrimeSuccession` : la suite reconstruite est strictement croissante (infinité des
  premiers).
* **`contact_accumulation_reconstructs_prime_gaps`** : composition finale — chaque écart reconstruit
  est le vrai écart, et chaque événement premier reconstruit est lu dans la limite des accumulations
  par contacts tronquées.

Seuil : `3 ≤ N` parce que `reconstructedVonMangoldt N` lit `reconstructedPsi (N − 1)` qui exige
`N − 1 ≥ 2` ; le premier `2` n'est pas dans la fenêtre reconstruite (limite de domaine de la formule
compilée, déclarée).

Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean ArithmeticFunction Filter Topology

/-- Le prédicat spectral des premiers reconstruits dans la fenêtre `N ≥ 3`. -/
def ReconstructedPrimeAbove (N : ℕ) : Prop := 3 ≤ N ∧ reconstructedPrimeEvent N

/-- Le prédicat arithmétique de validation. -/
def PrimeAbove (N : ℕ) : Prop := 3 ≤ N ∧ N.Prime

theorem reconstructedPrimeAbove_eq_primeAbove : ReconstructedPrimeAbove = PrimeAbove := by
  funext N
  unfold ReconstructedPrimeAbove PrimeAbove
  apply propext
  constructor
  · rintro ⟨h3, h⟩; exact ⟨h3, (reconstructedPrimeEvent_iff h3).mp h⟩
  · rintro ⟨h3, h⟩; exact ⟨h3, (reconstructedPrimeEvent_iff h3).mpr h⟩

/-- **Le premier reconstruit de rang `k`** (rang `0` = premier premier `≥ 3`). -/
noncomputable def reconstructedPrimeAtRank (k : ℕ) : ℕ := Nat.nth ReconstructedPrimeAbove k

/-- Le vrai premier de rang `k` dans la même fenêtre. -/
noncomputable def primeAtRankAbove (k : ℕ) : ℕ := Nat.nth PrimeAbove k

theorem reconstructedPrimeAtRank_eq_primeAtRank (k : ℕ) :
    reconstructedPrimeAtRank k = primeAtRankAbove k := by
  unfold reconstructedPrimeAtRank primeAtRankAbove
  rw [reconstructedPrimeAbove_eq_primeAbove]

/-- **L'écart reconstruit de rang `k`**. -/
noncomputable def reconstructedPrimeGap (k : ℕ) : ℕ :=
  reconstructedPrimeAtRank (k + 1) - reconstructedPrimeAtRank k

/-- Le vrai écart de rang `k`. -/
noncomputable def actualPrimeGap (k : ℕ) : ℕ := primeAtRankAbove (k + 1) - primeAtRankAbove k

theorem reconstructedPrimeGap_eq_actualGap (k : ℕ) :
    reconstructedPrimeGap k = actualPrimeGap k := by
  unfold reconstructedPrimeGap actualPrimeGap
  rw [reconstructedPrimeAtRank_eq_primeAtRank, reconstructedPrimeAtRank_eq_primeAtRank]

/-- La suite des écarts reconstruits. -/
noncomputable def reconstructedGapSequence : ℕ → ℕ := reconstructedPrimeGap

theorem reconstructedGapSequence_eq : reconstructedGapSequence = actualPrimeGap :=
  funext reconstructedPrimeGap_eq_actualGap

/-- Les premiers `≥ 3` sont en nombre infini. -/
theorem primeAbove_infinite : (Set.ofPred PrimeAbove).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (max B 3 + 1)
  have : p ∈ Set.ofPred PrimeAbove := ⟨by omega, hpp⟩
  have := hB this
  omega

/-- **Succession** : la suite reconstruite est strictement croissante. -/
theorem reconstructedPrimeSuccession : StrictMono reconstructedPrimeAtRank := by
  unfold reconstructedPrimeAtRank
  rw [reconstructedPrimeAbove_eq_primeAbove]
  exact Nat.nth_strictMono primeAbove_infinite

/-- Chaque écart reconstruit est strictement positif. -/
theorem reconstructedPrimeGap_pos (k : ℕ) : 0 < reconstructedPrimeGap k := by
  unfold reconstructedPrimeGap
  have := reconstructedPrimeSuccession (Nat.lt_succ_self k)
  simp only [Nat.succ_eq_add_one] at this
  omega

/-- **Composition finale** : les écarts reconstruits sont les vrais écarts, et chaque premier
reconstruit est un entier `N ≥ 3` dont le poids reconstruit — limite des accumulations par contacts
tronquées — vaut `log N`. -/
theorem contact_accumulation_reconstructs_prime_gaps (k₀ : ExplicitIndex → ℤ)
    (n : ExplicitIndex → ℕ) :
    (∀ k, reconstructedPrimeGap k = actualPrimeGap k) ∧
      (∀ N, ReconstructedPrimeAbove N →
        Tendsto (fun H : ℝ => truncatedStep H k₀ n N - truncatedStep H k₀ n (N - 1)) atTop
          (𝓝 ((Real.log N : ℝ) : ℂ))) := by
  refine ⟨reconstructedPrimeGap_eq_actualGap, fun N hN => ?_⟩
  have h := reconstructedVonMangoldt_eq_limit_contact_accumulation k₀ n hN.1
  rwa [hN.2] at h

#print axioms reconstructedPrimeGap_eq_actualGap
#print axioms contact_accumulation_reconstructs_prime_gaps

end RHV6Fresh
