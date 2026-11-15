/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MeetingCellSigns

/-!
# RHV6Fresh — Terminal/SignedCellBalance : le bilan signé des cellules le long de la série
(E440, §19.57–19.59, 2026-11-07 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse,
aucun axiome, aucun `sorry`, aucune position radiale, aucune famille de Tours, aucune somme de
contributions, aucune théorie spectrale)

Objets : UNE Tour, SES cellules (signe `(−1)^k`), la pente de la demande brute sur chaque cellule, la série.

## B1–B2. Pente, longueur, poids d'une cellule
* `cellDemand_eq` : pente d'une cellule = poids des entiers franchis − longueur ;
* `cellLength_pos`, `cellLength_mono` : longueurs strictement positives et croissantes avec l'indice.

## B3. Les cellules intérieures à un écart descendent
* `inner_cell_demand_le` : poids non premiers seulement ; `cellDemand_neg_of_no_weight` : sans poids,
  descente pure strictement négative.

## B4–B5. La somme signée des pentes : la descente s'annule à une cellule près
* `signedCellSum_eq` : somme signée des pentes = somme signée des poids − somme signée des longueurs ;
* `signed_lengths_bounded`, `signedCellSum_near_signed_weights` : **la somme signée des longueurs est bornée par
  la dernière cellule ; la somme signée des pentes est, à une cellule près, la somme signée des poids.**

## B6–B7. Poids premier et non premier ; la cellule de rencontre
* `cellWeight_eq_prime_add_nonprime`, `cellPrimeWeight_inner_eq_zero`, `cellPrimeWeight_meeting`,
  `meeting_cellDemand` : poids premier nul sur toute cellule intérieure, égal à `log p_{n+1}` sur la cellule de
  rencontre ; `meeting_cell_demand_nonneg_of_short` : la cellule de rencontre monte dès qu'elle est plus courte
  que le poids de la rencontre.

Rien ici ne parle de la position radiale ni d'aucune somme de Tours.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction Finset

/-! ## B1–B2. Pente, longueur et poids d'une cellule -/

/-- Longueur linéaire de la cellule `k` : `C_{k+1} − C_k`. -/
noncomputable def cellLength (β T : ℝ) (k : ℤ) : ℝ := contactAt β T (k + 1) - contactAt β T k

/-- Poids des entiers franchis par la cellule `k`. -/
noncomputable def cellWeight (β T : ℝ) (k : ℤ) : ℝ :=
  ∑ n ∈ Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 1)⌋₊, Λ n

/-- Pente de la demande brute sur la cellule `k`. -/
noncomputable def cellDemand (β T : ℝ) (k : ℤ) : ℝ :=
  rawDemand (contactAt β T (k + 1)) - rawDemand (contactAt β T k)

theorem cellDemand_eq {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    cellDemand β T k = cellWeight β T k - cellLength β T k := by
  unfold cellDemand cellWeight cellLength
  exact rawDemand_variation (contactAt_mono hT (by omega))

theorem cellLength_eq {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    cellLength β T k = contactAt β T k * (Real.exp (Real.pi / T) - 1) :=
  cell_linear_length hT.ne' k

theorem cellLength_pos {β T : ℝ} (hT : 0 < T) (k : ℤ) : 0 < cellLength β T k := by
  rw [cellLength_eq hT]
  have h1 : 1 < Real.exp (Real.pi / T) := Real.one_lt_exp_iff.mpr (by positivity)
  have := contactAt_pos β T k
  nlinarith

theorem cellLength_mono {β T : ℝ} (hT : 0 < T) {k l : ℤ} (hkl : k ≤ l) :
    cellLength β T k ≤ cellLength β T l := by
  rw [cellLength_eq hT, cellLength_eq hT]
  have h1 : 1 ≤ Real.exp (Real.pi / T) := Real.one_le_exp (by positivity)
  exact mul_le_mul_of_nonneg_right (contactAt_mono hT hkl) (by linarith)

theorem cellWeight_nonneg (β T : ℝ) (k : ℤ) : 0 ≤ cellWeight β T k :=
  Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)

/-! ## B3. Les cellules intérieures à un écart descendent -/

theorem inner_cell_demand_le {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) {k : ℤ}
    (hk : I.lower ≤ contactAt β T k) (hk' : contactAt β T (k + 1) < I.upper) :
    cellDemand β T k =
      ∑ n ∈ (Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 1)⌋₊).filter (fun n => ¬ Nat.Prime n), Λ n -
        cellLength β T k :=
  inner_cell_variation hT I hk hk'

theorem cellDemand_eq_neg_length_of_no_weight {β T : ℝ} (hT : 0 < T) {k : ℤ}
    (h : ∀ n ∈ Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 1)⌋₊, Λ n = 0) :
    cellDemand β T k = -cellLength β T k := by
  rw [cellDemand_eq hT]
  unfold cellWeight
  rw [Finset.sum_eq_zero h]
  ring

theorem cellDemand_neg_of_no_weight {β T : ℝ} (hT : 0 < T) {k : ℤ}
    (h : ∀ n ∈ Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 1)⌋₊, Λ n = 0) :
    cellDemand β T k < 0 := by
  rw [cellDemand_eq_neg_length_of_no_weight hT h]
  linarith [cellLength_pos (β := β) hT k]

/-! ## B4–B5. La somme signée des pentes : la descente s'annule à une cellule près -/

/-- Somme signée des pentes de `m+1` cellules consécutives à partir de `k₀`. -/
noncomputable def signedCellSum (β T : ℝ) (k₀ : ℤ) (m : ℕ) : ℝ :=
  ∑ j ∈ range (m + 1), (-1 : ℝ) ^ j * cellDemand β T (k₀ + j)

theorem signedCellSum_eq {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (m : ℕ) :
    signedCellSum β T k₀ m =
      ∑ j ∈ range (m + 1), (-1 : ℝ) ^ j * cellWeight β T (k₀ + j) -
        ∑ j ∈ range (m + 1), (-1 : ℝ) ^ j * cellLength β T (k₀ + j) := by
  unfold signedCellSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [cellDemand_eq hT]
  ring

theorem signed_lengths_bounded {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (m : ℕ) :
    |∑ j ∈ range (m + 1), (-1 : ℝ) ^ j * cellLength β T (k₀ + j)| ≤ cellLength β T (k₀ + m) :=
  signed_cells_bounded_by_last hT k₀ m

/-- **La somme signée des pentes est, à une cellule près, la somme signée des poids.** -/
theorem signedCellSum_near_signed_weights {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (m : ℕ) :
    |signedCellSum β T k₀ m - ∑ j ∈ range (m + 1), (-1 : ℝ) ^ j * cellWeight β T (k₀ + j)| ≤
      cellLength β T (k₀ + m) := by
  rw [signedCellSum_eq hT]
  have := signed_lengths_bounded (β := β) hT k₀ m
  rwa [sub_sub_cancel_left, abs_neg]

/-! ## B6. Poids premier et poids non premier d'une cellule -/

noncomputable def cellPrimeWeight (β T : ℝ) (k : ℤ) : ℝ :=
  ∑ n ∈ (Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 1)⌋₊).filter (fun n => Nat.Prime n), Λ n

noncomputable def cellNonPrimeWeight (β T : ℝ) (k : ℤ) : ℝ :=
  ∑ n ∈ (Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 1)⌋₊).filter (fun n => ¬ Nat.Prime n), Λ n

theorem cellWeight_eq_prime_add_nonprime (β T : ℝ) (k : ℤ) :
    cellWeight β T k = cellPrimeWeight β T k + cellNonPrimeWeight β T k := by
  unfold cellWeight cellPrimeWeight cellNonPrimeWeight
  rw [Finset.sum_filter_add_sum_filter_not]

theorem cellPrimeWeight_inner_eq_zero {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) {k : ℤ}
    (hk : I.lower ≤ contactAt β T k) (hk' : contactAt β T (k + 1) < I.upper) :
    cellPrimeWeight β T k = 0 := by
  unfold cellPrimeWeight
  rw [Finset.filter_false_of_mem, Finset.sum_empty]
  exact no_prime_crossed_inside_gap I hk (contactAt_mono hT (by omega)) hk'

theorem cellPrimeWeight_meeting {β T : ℝ} (hT : 0 < T) {I J : PrimeGapInterval} (hIJ : J.rank = I.rank + 1)
    (hI : GapHasContact β T I) (hJ : GapHasContact β T J)
    (hltI : contactAt β T (meetingCell β T I) < I.upper)
    (hltJ : contactAt β T (meetingCell β T J) < J.upper) :
    cellPrimeWeight β T (meetingCell β T I) = Real.log (fnPrimeAtRank (I.rank + 1)) := by
  unfold cellPrimeWeight
  rw [meeting_cell_primes hT hIJ hI hJ hltI hltJ, Finset.sum_singleton,
    vonMangoldt_apply_prime (thm_primeAtRank_isPrime _)]

/-- Pente de la cellule de rencontre : poids premier de la rencontre + poids non premiers − longueur. -/
theorem meeting_cellDemand {β T : ℝ} (hT : 0 < T) {I J : PrimeGapInterval} (hIJ : J.rank = I.rank + 1)
    (hI : GapHasContact β T I) (hJ : GapHasContact β T J)
    (hltI : contactAt β T (meetingCell β T I) < I.upper)
    (hltJ : contactAt β T (meetingCell β T J) < J.upper) :
    cellDemand β T (meetingCell β T I) =
      Real.log (fnPrimeAtRank (I.rank + 1)) + cellNonPrimeWeight β T (meetingCell β T I) -
        cellLength β T (meetingCell β T I) := by
  rw [cellDemand_eq hT, cellWeight_eq_prime_add_nonprime, cellPrimeWeight_meeting hT hIJ hI hJ hltI hltJ]

/-! ## B7. La cellule de rencontre monte dès qu'elle est plus courte que le poids de la rencontre -/

theorem meeting_cell_demand_nonneg_of_short {β T : ℝ} (hT : 0 < T) {I J : PrimeGapInterval}
    (hIJ : J.rank = I.rank + 1) (hI : GapHasContact β T I) (hJ : GapHasContact β T J)
    (hltI : contactAt β T (meetingCell β T I) < I.upper)
    (hltJ : contactAt β T (meetingCell β T J) < J.upper)
    (hshort : cellLength β T (meetingCell β T I) ≤ Real.log (fnPrimeAtRank (I.rank + 1))) :
    0 ≤ cellDemand β T (meetingCell β T I) := by
  rw [meeting_cellDemand hT hIJ hI hJ hltI hltJ]
  have : 0 ≤ cellNonPrimeWeight β T (meetingCell β T I) :=
    Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
  linarith


#print axioms cellDemand_eq
#print axioms cellLength_pos
#print axioms cellLength_mono
#print axioms inner_cell_demand_le
#print axioms cellDemand_eq_neg_length_of_no_weight
#print axioms cellDemand_neg_of_no_weight
#print axioms signedCellSum_eq
#print axioms signed_lengths_bounded
#print axioms signedCellSum_near_signed_weights
#print axioms cellWeight_eq_prime_add_nonprime
#print axioms cellPrimeWeight_inner_eq_zero
#print axioms cellPrimeWeight_meeting
#print axioms meeting_cellDemand
#print axioms meeting_cell_demand_nonneg_of_short

end RHV6Fresh
