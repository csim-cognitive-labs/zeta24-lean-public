/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ExactDisplacementAndThreshold
import RHV6Fresh.Terminal.ContinuousProgression

/-!
# RHV6Fresh — Terminal/GapsAboveThreshold : les écarts au-dessus du seuil, par les contacts et leurs signes seuls
(E443, §19.61–19.62, 2026-11-07 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse,
aucun axiome, aucun `sorry`, aucune position radiale, aucune famille de Tours, aucune théorie spectrale ;
seuls théorèmes arithmétiques importés : Bertrand (corpus) et la borne de Tchebychev `ψ − θ ≤ 2√x log x` (Mathlib))

## A1–A3. Bertrand sur l'écart et sur les contacts
* `upper_le_two_lower`, `gap_le_lower` ; `wholeCellCount_lt_log_two` : moins de `T log 2/π` cellules entières
  dans tout écart ; `meetingCell_displacement_lt` : le déplacement de la cellule de rencontre entre deux écarts
  consécutifs est `< T log 2/π + 1`.

## A4–A5. Un écart sans contact ; la pente d'un écart entier
* `gap_in_cell_of_no_contact` : un écart sans contact tient dans la cellule (signée) de sa rencontre ;
* `gap_primes_singleton`, `gap_demand_variation` : **la pente d'un écart entier = `log p_{n+1}` + poids non
  premiers − longueur de l'écart**, sans aucune hypothèse de contact.

## A6–A7. Le poids non premier borné ; le second seuil
* `cellNonPrimeWeight_le_psi_sub_theta`, `cellNonPrimeWeight_le_sqrt` : poids non premier d'une cellule
  `≤ 2√C_{k+1} log C_{k+1}` ;
* `contact_succ_meeting_le`, `meeting_falls_above_second_threshold` : **si `log p + 2√(p r) log(p r) < p(1 − 1/r)`,
  la cellule de rencontre descend** — condition en `p` et `T` seuls : au-delà du second seuil `x**`, toute cellule
  de rencontre descend.

Rien ici ne parle de la position radiale ni d'aucune somme de Tours.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction Finset

/-! ## A1. Bertrand sur l'écart -/

theorem upper_le_two_lower (I : PrimeGapInterval) : I.upper ≤ 2 * I.lower := by
  unfold PrimeGapInterval.upper PrimeGapInterval.lower
  have := primeSuccessor_le_two_mul I.rank
  unfold fnPrimeSuccessor at this
  exact_mod_cast this

theorem gap_le_lower (I : PrimeGapInterval) : I.upper - I.lower ≤ I.lower := by
  linarith [upper_le_two_lower I]

/-! ## A2–A3. Moins de `T log 2/π` cellules par écart ; déplacement borné -/

theorem log_ratio_le_log_two (I : PrimeGapInterval) : Real.log (I.upper / I.lower) ≤ Real.log 2 := by
  have hl : 0 < I.lower := by linarith [I.one_lt_lower]
  have hu : 0 < I.upper := by linarith [I.one_lt_upper]
  apply Real.log_le_log (div_pos hu hl)
  rw [div_le_iff₀ hl]
  exact upper_le_two_lower I

theorem wholeCellCount_lt_log_two {β T : ℝ} (hT : 0 < T) {I : PrimeGapInterval} (h : GapHasContact β T I) :
    ((wholeCellCount β T I : ℕ) : ℝ) < T * Real.log 2 / Real.pi := by
  have hb := wholeCellCount_bounds h
  rw [abs_lt] at hb
  have hlog := log_ratio_le_log_two I
  have : T * Real.log (I.upper / I.lower) / Real.pi ≤ T * Real.log 2 / Real.pi := by
    apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    exact mul_le_mul_of_nonneg_left hlog hT.le
  linarith [hb.2]

theorem meetingCell_displacement_lt {β T : ℝ} (hT : 0 < T) {I J : PrimeGapInterval} (hIJ : J.rank = I.rank + 1) :
    ((meetingCell β T J - meetingCell β T I : ℤ) : ℝ) < T * Real.log 2 / Real.pi + 1 := by
  unfold meetingCell
  have hb := lastContact_difference_bounds β T (p := I.upper) (q := J.upper)
    (by linarith [I.one_lt_upper]) (by linarith [J.one_lt_upper])
  rw [abs_lt] at hb
  have hlog : Real.log (J.upper / I.upper) ≤ Real.log 2 := by
    have := log_ratio_le_log_two J
    rw [consecutive_lower_eq_upper hIJ] at this
    exact this
  have : T * Real.log (J.upper / I.upper) / Real.pi ≤ T * Real.log 2 / Real.pi := by
    apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    exact mul_le_mul_of_nonneg_left hlog hT.le
  linarith [hb.2]

/-! ## A4. Un écart sans contact tient dans la cellule de sa rencontre -/

theorem gap_in_cell_of_no_contact {β T : ℝ} (hT : 0 < T) {I : PrimeGapInterval} (h : ¬ GapHasContact β T I) :
    contactAt β T (meetingCell β T I) ≤ I.lower ∧ I.upper < contactAt β T (meetingCell β T I + 1) := by
  unfold GapHasContact at h
  have hmono : lastContactBefore β T I.lower ≤ lastContactBefore β T I.upper :=
    lastContactBefore_mono hT (by linarith [I.one_lt_lower]) I.lower_lt_upper.le
  have heq : lastContactBefore β T I.upper = lastContactBefore β T I.lower := by omega
  unfold meetingCell
  rw [heq]
  exact ⟨lastContact_le hT (by linarith [I.one_lt_lower]), by
    rw [← heq]; exact lt_contact_succ hT (by linarith [I.one_lt_upper])⟩

/-! ## A5. La pente d'un écart entier, sans aucune hypothèse de contact -/

theorem gap_primes_singleton (I : PrimeGapInterval) :
    (Ioc (fnPrimeAtRank I.rank) (fnPrimeAtRank (I.rank + 1))).filter (fun n => Nat.Prime n) =
      {fnPrimeAtRank (I.rank + 1)} := by
  have hlt : fnPrimeAtRank I.rank < fnPrimeAtRank (I.rank + 1) := thm_primeAtRank_strictMono (by omega)
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hlt, le_rfl⟩, thm_primeAtRank_isPrime _⟩
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hq
    obtain ⟨⟨hq1, hq2⟩, hqp⟩ := hq
    rcases lt_or_eq_of_le hq2 with hq2 | hq2
    · exact absurd (thm_noPrimeStrictlyBetweenSuccessivePrimes I.rank hqp hq1
        (by unfold fnPrimeSuccessor; omega)) id
    · exact hq2

theorem gap_demand_variation (I : PrimeGapInterval) :
    rawDemand I.upper - rawDemand I.lower =
      Real.log (fnPrimeAtRank (I.rank + 1)) +
        ∑ n ∈ (Ioc (fnPrimeAtRank I.rank) (fnPrimeAtRank (I.rank + 1))).filter (fun n => ¬ Nat.Prime n), Λ n -
        (I.upper - I.lower) := by
  rw [rawDemand_variation I.lower_lt_upper.le]
  unfold PrimeGapInterval.upper PrimeGapInterval.lower
  rw [Nat.floor_natCast, Nat.floor_natCast, ← Finset.sum_filter_add_sum_filter_not _ (fun n => Nat.Prime n),
    gap_primes_singleton, Finset.sum_singleton, vonMangoldt_apply_prime (thm_primeAtRank_isPrime _)]

/-! ## A6. Le poids non premier d'une cellule, borné par Tchebychev -/

theorem cellNonPrimeWeight_le_psi_sub_theta (β T : ℝ) (k : ℤ) :
    cellNonPrimeWeight β T k ≤ Chebyshev.psi (contactAt β T (k + 1)) - Chebyshev.theta (contactAt β T (k + 1)) := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  unfold cellNonPrimeWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Finset.filter_subset_filter
    exact Finset.Ioc_subset_Ioc_left (Nat.zero_le _)
  · intro _ _ _; exact vonMangoldt_nonneg

theorem cellNonPrimeWeight_le_sqrt {β T : ℝ} (k : ℤ) (h1 : 1 ≤ contactAt β T (k + 1)) :
    cellNonPrimeWeight β T k ≤ 2 * Real.sqrt (contactAt β T (k + 1)) * Real.log (contactAt β T (k + 1)) :=
  (cellNonPrimeWeight_le_psi_sub_theta β T k).trans (Chebyshev.psi_sub_theta_le h1)

/-! ## A7. Le second seuil : au-delà, toute cellule de rencontre descend -/

theorem contact_succ_meeting_le {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) :
    contactAt β T (meetingCell β T I + 1) ≤ I.upper * Real.exp (Real.pi / T) := by
  have h := contactAt_ratio (β := β) hT.ne' (meetingCell β T I)
  have hpos := contactAt_pos β T (meetingCell β T I)
  have hup : contactAt β T (meetingCell β T I) ≤ I.upper := lastContact_le hT (by linarith [I.one_lt_upper])
  rw [div_eq_iff hpos.ne'] at h
  rw [h, mul_comm]
  exact mul_le_mul_of_nonneg_right hup (Real.exp_pos _).le

theorem meeting_falls_above_second_threshold {β T : ℝ} (hT : 0 < T) {I J : PrimeGapInterval}
    (hIJ : J.rank = I.rank + 1) (hI : GapHasContact β T I) (hJ : GapHasContact β T J)
    (hltI : contactAt β T (meetingCell β T I) < I.upper)
    (hltJ : contactAt β T (meetingCell β T J) < J.upper)
    (hfar : Real.log (fnPrimeAtRank (I.rank + 1)) +
        2 * Real.sqrt (I.upper * Real.exp (Real.pi / T)) * Real.log (I.upper * Real.exp (Real.pi / T)) <
      I.upper * (1 - Real.exp (-(Real.pi / T)))) :
    cellDemand β T (meetingCell β T I) < 0 := by
  apply meeting_falls_of_length_dominates hT hIJ hI hJ hltI hltJ
  have hC1 : 1 ≤ contactAt β T (meetingCell β T I + 1) := by
    have := lt_contact_succ (β := β) hT (by linarith [I.one_lt_upper] : (0:ℝ) < I.upper)
    unfold meetingCell; linarith [I.one_lt_upper]
  have hle := contact_succ_meeting_le (β := β) hT I
  have hnp := cellNonPrimeWeight_le_sqrt (β := β) (T := T) (meetingCell β T I) hC1
  have hsq : Real.sqrt (contactAt β T (meetingCell β T I + 1)) ≤ Real.sqrt (I.upper * Real.exp (Real.pi / T)) :=
    Real.sqrt_le_sqrt hle
  have hlog : Real.log (contactAt β T (meetingCell β T I + 1)) ≤ Real.log (I.upper * Real.exp (Real.pi / T)) :=
    Real.log_le_log (by linarith) hle
  have h0s : 0 ≤ Real.sqrt (contactAt β T (meetingCell β T I + 1)) := Real.sqrt_nonneg _
  have h0l : 0 ≤ Real.log (contactAt β T (meetingCell β T I + 1)) := Real.log_nonneg hC1
  have hprod : 2 * Real.sqrt (contactAt β T (meetingCell β T I + 1)) * Real.log (contactAt β T (meetingCell β T I + 1)) ≤
      2 * Real.sqrt (I.upper * Real.exp (Real.pi / T)) * Real.log (I.upper * Real.exp (Real.pi / T)) := by
    have := mul_le_mul hsq hlog h0l (Real.sqrt_nonneg _)
    linarith
  linarith

#print axioms upper_le_two_lower
#print axioms gap_le_lower
#print axioms log_ratio_le_log_two
#print axioms wholeCellCount_lt_log_two
#print axioms meetingCell_displacement_lt
#print axioms gap_in_cell_of_no_contact
#print axioms gap_primes_singleton
#print axioms gap_demand_variation
#print axioms cellNonPrimeWeight_le_psi_sub_theta
#print axioms cellNonPrimeWeight_le_sqrt
#print axioms contact_succ_meeting_le
#print axioms meeting_falls_above_second_threshold

end RHV6Fresh
