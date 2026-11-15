/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.CountingRigidity
import Mathlib.NumberTheory.Chebyshev

/-!
# RHV3Lean — reconstruction explicite Λ → ψ → J → π

Cette couche arithmétique lit un bord déjà produit. Elle ne définit aucun
contact. Les différences premières de `ψ` et de `J` rendent `Λ`; le critère
exact `Λ(n) = log n` rend la primalité, puis `π`, les rangs et C3.

    TRACE_ID              : RHV3-O10-VON-MANGOLDT-CHEBYSHEV
    SEMANTIC_OBJECT       : O10, reconstruction de l'unique histoire première
    SEMANTIC_STATEMENT    : Lambda produit psi puis J ; les sauts de J
                            caractérisent les premiers et reconstruisent pi
                            sur les deux bords de la même cellule fournie
    MATHEMATICAL_STATEMENT: Δpsi(n)=Λ(n), ΔJ(n)log(n)=Λ(n),
                            PrimeFromJ(n) ↔ Nat.Prime n et pi_J=pi
    MATHEMATICAL_PARENT   : O2 axe algébrique ; O6 histoire première ;
                            O10 CountingRigidity
    PROOF_STRATEGY        : différences de sommes finies, caractérisation de
                            von Mangoldt sur les puissances premières, puis
                            extensionalité du comptage fini
    REQUIRED_LEMMAS       : Finset.sum_range_succ,
                            vonMangoldt_apply_prime,
                            vonMangoldt_eq_zero_iff,
                            Nat.count_eq_card_filter_range
    WHY_EACH_LEMMA_EXISTS : le premier calcule les sauts ; les deux suivants
                            récupèrent exactement la primalité ; le dernier
                            identifie le cardinal reconstruit à pi
    LEAN_DEFINITION       : rVonMangoldtWeight, rChebyshevPsiNat,
                            rChebyshevJNat, PPrimeFromJ,
                            nPrimeCountingFromJ
    LEAN_THEOREM          : thm_psiJump_eq_vonMangoldt,
                            thm_jJump_mul_log_eq_vonMangoldt,
                            thm_primeFromJ_iff,
                            thm_primeCountingFromJ_eq_primeCounting,
                            thm_vonMangoldtChebyshev_reads_same_interval
    SAME_MEMBER_CHECK     : sans objet ; cette couche reçoit une cellule
    SAME_PASSAGE_CHECK    : sans objet ; aucun passage n'est construit ici
    SAME_MIDDLE_CHECK     : sans objet à ce niveau
    SAME_HISTORY_CHECK    : thm_primeCountingFromJ_eq_primeCounting identifie
                            la reconstruction à l'unique Nat.primeCounting
    FORBIDDEN_PREMISES    : contact choisi par un premier, cardinal positif,
                            succession C3 de deux membres, hypothèse RH
    NEXT_CONSUMER         : C3 et occurrence lus sur cette même cellule
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED
-/

namespace RHV3Lean

open ArithmeticFunction

/-- Poids de von Mangoldt canonique de Mathlib, exposé dans l'API RHV3. -/
noncomputable def rVonMangoldtWeight (n : ℕ) : ℝ := Λ n

/-- Somme de Chebyshev `ψ` à borne naturelle inclusive. -/
noncomputable def rChebyshevPsiNat (nBound : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (nBound + 1), rVonMangoldtWeight n

/-- Fonction `J` à borne naturelle inclusive, écrite depuis `Λ`. -/
noncomputable def rChebyshevJNat (nBound : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (nBound + 1),
    if 2 ≤ n then rVonMangoldtWeight n / Real.log (n : ℝ) else 0

/-- Première différence d'un canal cumulatif. -/
noncomputable def rCumulativeJump (F : ℕ → ℝ) (n : ℕ) : ℝ :=
  F n - F (n - 1)

theorem thm_psiJump_eq_vonMangoldt {n : ℕ} (hn : 1 ≤ n) :
    rCumulativeJump rChebyshevPsiNat n = rVonMangoldtWeight n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold rCumulativeJump rChebyshevPsiNat
  simp only [Nat.add_sub_cancel]
  rw [Finset.sum_range_succ]
  ring

theorem thm_jJump_mul_log_eq_vonMangoldt {n : ℕ} (hn : 2 ≤ n) :
    rCumulativeJump rChebyshevJNat n * Real.log (n : ℝ) = rVonMangoldtWeight n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmTwo : 2 ≤ m + 1 := by omega
  have hLog : Real.log ((m + 1 : ℕ) : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m + 1 by omega)))
  unfold rCumulativeJump rChebyshevJNat
  simp only [Nat.add_sub_cancel]
  rw [Finset.sum_range_succ]
  simp only [if_pos hmTwo]
  field_simp
  ring

/-- Primalité reconstruite depuis les sauts de `J`. -/
def PPrimeFromJ (J : ℕ → ℝ) (n : ℕ) : Prop :=
  2 ≤ n ∧ rCumulativeJump J n * Real.log (n : ℝ) = Real.log (n : ℝ)

theorem thm_prime_iff_vonMangoldt_eq_log (n : ℕ) :
    Nat.Prime n ↔ 2 ≤ n ∧ rVonMangoldtWeight n = Real.log (n : ℝ) := by
  unfold rVonMangoldtWeight
  constructor
  · intro hp
    exact ⟨hp.two_le, vonMangoldt_apply_prime hp⟩
  · rintro ⟨hTwo, hWeight⟩
    have hLogPos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hTwo.trans_lt' one_lt_two)
    by_cases hPP : IsPrimePow n
    · obtain ⟨p, k, hpPrime, hkPos, hpk⟩ := hPP
      have hpNat : Nat.Prime p := Nat.prime_iff.mpr hpPrime
      have hkNe : k ≠ 0 := hkPos.ne'
      have hLambda : Λ n = Real.log (p : ℝ) := by
        rw [← hpk, vonMangoldt_apply_pow hkNe, vonMangoldt_apply_prime hpNat]
      have hLogN : Real.log (n : ℝ) = (k : ℝ) * Real.log (p : ℝ) := by
        rw [← hpk]
        push_cast
        rw [Real.log_pow]
      have hLogPPos : 0 < Real.log (p : ℝ) :=
        Real.log_pos (by exact_mod_cast hpNat.one_lt)
      have hkOne : (k : ℝ) = 1 := by
        rw [hLambda, hLogN] at hWeight
        nlinarith
      have : k = 1 := by exact_mod_cast hkOne
      subst this
      rw [pow_one] at hpk
      exact hpk ▸ hpNat
    · rw [vonMangoldt_eq_zero_iff.mpr hPP] at hWeight
      linarith

theorem thm_primeFromJ_iff (n : ℕ) :
    PPrimeFromJ rChebyshevJNat n ↔ Nat.Prime n := by
  unfold PPrimeFromJ
  rw [thm_prime_iff_vonMangoldt_eq_log n]
  constructor
  · rintro ⟨hTwo, hEq⟩
    exact ⟨hTwo, by rwa [thm_jJump_mul_log_eq_vonMangoldt hTwo] at hEq⟩
  · rintro ⟨hTwo, hEq⟩
    exact ⟨hTwo, by rwa [thm_jJump_mul_log_eq_vonMangoldt hTwo]⟩

/-- `π` reconstruit depuis `J`, à borne inclusive. -/
noncomputable def nPrimeCountingFromJ (J : ℕ → ℝ) (nBound : ℕ) : ℕ :=
  letI := Classical.dec
  ((Finset.range (nBound + 1)).filter (PPrimeFromJ J)).card

theorem thm_primeCountingFromJ_eq_primeCounting :
    nPrimeCountingFromJ rChebyshevJNat = Nat.primeCounting := by
  funext nBound
  unfold nPrimeCountingFromJ
  simp_rw [thm_primeFromJ_iff]
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

/-- Le rang `π(x)` utilisé par O10 est exactement celui reconstruit depuis
`Λ → ψ → J`; le bord reste celui de la cellule fournie. -/
theorem thm_edgePrimeRank_eq_primeCountingFromJ (rPoint : ℝ) :
    nEdgePrimeRank rPoint =
      nPrimeCountingFromJ rChebyshevJNat ⌊rPoint⌋₊ := by
  rw [thm_primeCountingFromJ_eq_primeCounting]
  unfold nEdgePrimeRank Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]

/-- Reconstruction explicite sur le même intervalle `(C-,C+]`: les deux rangs
issus de `J` donnent le cardinal, puis C3 dans l'unique histoire première. -/
theorem thm_vonMangoldtChebyshev_reads_same_interval (I : TAlgebraicInterval) :
    nCellFoundCount I =
        nPrimeCountingFromJ rChebyshevJNat ⌊I.rRightEndpoint⌋₊ -
          nPrimeCountingFromJ rChebyshevJNat ⌊I.rLeftEndpoint⌋₊ ∧
      nCellCentralPrime I = fnPrimeAtRank (nCellCentralRank I - 1) := by
  constructor
  · rw [thm_cellFoundCount_eq_edgeRankDifference,
      nCellRightEdgeRank, nCellLeftEdgeRank,
      thm_edgePrimeRank_eq_primeCountingFromJ,
      thm_edgePrimeRank_eq_primeCountingFromJ]
  · rfl

end RHV3Lean
