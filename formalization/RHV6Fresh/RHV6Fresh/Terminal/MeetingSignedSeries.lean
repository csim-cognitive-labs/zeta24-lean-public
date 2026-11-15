/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.SignedCellBalance

/-!
# RHV6Fresh — Terminal/MeetingSignedSeries : le bilan signé des rencontres le long de la série
(E441, §19.59–19.60, 2026-11-07 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse,
aucun axiome, aucun `sorry`, aucune position radiale, aucune famille de Tours, aucune somme de
contributions, aucune théorie spectrale)

Objets : UNE Tour, SES cellules (signe `(−1)^k`), les cellules de rencontre d'une série d'écarts, la pente
de la demande brute sur chaque cellule.

## M1–M2. Décalage des cellules de rencontre, somme signée des rencontres
* `meetingOffset`, `meetingOffset_succ`, `meetingOffset_lt_succ` : le décalage de la cellule de rencontre de
  ⟨n+j⟩ par rapport à celle de ⟨n⟩ avance du nombre de contacts franchis ; strictement si l'écart a un contact ;
* `meetingSignedSum` : `Σ_{j<J} (−1)^{décalage_j} · log p_{n+j+1}`.

## M3. Le poids premier signé des cellules de la série est EXACTEMENT la somme signée des rencontres
* `signedPrimeSum_eq_meetings` (chaque écart a un contact, aucune rencontre n'est un contact).

## M4–M5. Le bilan signé et la forme close de la descente signée
* `series_signed_balance` : pentes signées = poids premiers signés + poids non premiers signés − longueurs signées ;
* `signedLengthSum_closed_form`, `signedLengthSum_first_last` : **la descente signée vaut exactement
  `(première cellule − (−1)^{M+1}·r·dernière cellule)/(1 + r)`, `r = e^{π/T}`.**

## M6–M7. Ce que la croissance des longueurs impose à la borne : les rencontres extrêmes et la fréquence
* `cellLength_lt_of_lt_meeting`, `meeting_mul_lt_cellLength` : toute cellule avant la rencontre `p` est plus
  courte que `p·(r − 1)`, toute cellule à partir de la cellule de rencontre est plus longue que `p·(1 − 1/r)` ;
* `series_balance_near_meetings` : **|pentes signées − somme signée des rencontres − poids non premiers signés|
  < `p_{n+J+1}·(r − 1)`.**

Rien ici ne parle de la position radiale ni d'aucune somme de Tours.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction Finset

/-! ## M1. Décalage des cellules de rencontre et somme signée des rencontres -/

noncomputable def meetingOffset (β T : ℝ) (n j : ℕ) : ℕ :=
  (meetingCell β T ⟨n + j⟩ - meetingCell β T ⟨n⟩).toNat

theorem meetingOffset_zero (β T : ℝ) (n : ℕ) : meetingOffset β T n 0 = 0 := by
  simp [meetingOffset]

theorem meetingOffset_eq {β T : ℝ} (hT : 0 < T) (n j : ℕ) :
    ((meetingOffset β T n j : ℕ) : ℤ) = meetingCell β T ⟨n + j⟩ - meetingCell β T ⟨n⟩ := by
  unfold meetingOffset
  have := meetingCell_mono_rank (β := β) hT n j
  rw [Int.toNat_of_nonneg (by omega)]

theorem meetingOffset_succ {β T : ℝ} (hT : 0 < T) (n j : ℕ) (h : GapHasContact β T ⟨n + j + 1⟩) :
    meetingOffset β T n (j + 1) = meetingOffset β T n j + wholeCellCount β T ⟨n + j + 1⟩ + 1 := by
  have hs := meetingCell_step (β := β) (T := T) (I := ⟨n + j⟩) (J := ⟨n + j + 1⟩) rfl h
  have h1 := meetingOffset_eq (β := β) hT n j
  have h2 := meetingOffset_eq (β := β) hT n (j + 1)
  rw [← Nat.add_assoc] at h2
  omega

theorem meetingOffset_lt_succ {β T : ℝ} (hT : 0 < T) (n j : ℕ) (h : GapHasContact β T ⟨n + j + 1⟩) :
    meetingOffset β T n j < meetingOffset β T n (j + 1) := by
  rw [meetingOffset_succ hT n j h]; omega

/-- Somme signée des rencontres : `Σ_{j<J} (−1)^{décalage_j} · log p_{n+j+1}`. -/
noncomputable def meetingSignedSum (β T : ℝ) (n J : ℕ) : ℝ :=
  ∑ j ∈ range J, (-1 : ℝ) ^ (meetingOffset β T n j) * Real.log (fnPrimeAtRank (n + j + 1))

noncomputable def signedPrimeSum (β T : ℝ) (k₀ : ℤ) (M : ℕ) : ℝ :=
  ∑ i ∈ range M, (-1 : ℝ) ^ i * cellPrimeWeight β T (k₀ + i)

noncomputable def signedNonPrimeSum (β T : ℝ) (k₀ : ℤ) (M : ℕ) : ℝ :=
  ∑ i ∈ range M, (-1 : ℝ) ^ i * cellNonPrimeWeight β T (k₀ + i)

noncomputable def signedLengthSum (β T : ℝ) (k₀ : ℤ) (M : ℕ) : ℝ :=
  ∑ i ∈ range M, (-1 : ℝ) ^ i * cellLength β T (k₀ + i)

/-! ## M3. Le poids premier signé des cellules de la série est exactement la somme signée des rencontres -/

theorem signedPrimeSum_eq_meetings {β T : ℝ} (hT : 0 < T) (n J : ℕ)
    (hc : ∀ j ≤ J, GapHasContact β T ⟨n + j⟩)
    (hlt : ∀ j ≤ J, contactAt β T (meetingCell β T ⟨n + j⟩) < (⟨n + j⟩ : PrimeGapInterval).upper) :
    signedPrimeSum β T (meetingCell β T ⟨n⟩) (meetingOffset β T n J) = meetingSignedSum β T n J := by
  induction J with
  | zero => simp [signedPrimeSum, meetingSignedSum, meetingOffset_zero]
  | succ J ih =>
    have hcJ : ∀ j ≤ J, GapHasContact β T ⟨n + j⟩ := fun j hj => hc j (by omega)
    have hltJ : ∀ j ≤ J, contactAt β T (meetingCell β T ⟨n + j⟩) < (⟨n + j⟩ : PrimeGapInterval).upper :=
      fun j hj => hlt j (by omega)
    have ih' := ih hcJ hltJ
    have hJ1 : GapHasContact β T ⟨n + J + 1⟩ := by
      have := hc (J + 1) le_rfl; rwa [← Nat.add_assoc] at this
    have hlt1 : contactAt β T (meetingCell β T ⟨n + J + 1⟩) < (⟨n + J + 1⟩ : PrimeGapInterval).upper := by
      have := hlt (J + 1) le_rfl; rwa [← Nat.add_assoc] at this
    have hoff := meetingOffset_lt_succ hT n J hJ1
    set k₀ := meetingCell β T ⟨n⟩ with hk₀
    set a := meetingOffset β T n J with ha
    set b := meetingOffset β T n (J + 1) with hb
    have hka : (k₀ : ℤ) + a = meetingCell β T ⟨n + J⟩ := by
      have := meetingOffset_eq (β := β) hT n J; omega
    have hkb : (k₀ : ℤ) + b = meetingCell β T ⟨n + J + 1⟩ := by
      have := meetingOffset_eq (β := β) hT n (J + 1); rw [← Nat.add_assoc] at this; omega
    unfold signedPrimeSum meetingSignedSum
    rw [← Finset.sum_range_add_sum_Ico _ hoff.le, Finset.sum_range_succ,
      Finset.sum_eq_sum_Ico_succ_bot hoff]
    unfold signedPrimeSum meetingSignedSum at ih'
    rw [ih', hka]
    have hmeet : cellPrimeWeight β T (meetingCell β T ⟨n + J⟩) = Real.log (fnPrimeAtRank (n + J + 1)) :=
      cellPrimeWeight_meeting hT (I := ⟨n + J⟩) (J := ⟨n + J + 1⟩) rfl (hc J (by omega)) hJ1
        (hlt J (by omega)) hlt1
    rw [hmeet]
    have htail : ∑ i ∈ Ico (a + 1) b, (-1 : ℝ) ^ i * cellPrimeWeight β T (k₀ + i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hz : cellPrimeWeight β T (k₀ + i) = 0 := by
        apply cellPrimeWeight_inner_eq_zero hT ⟨n + J + 1⟩
        · -- lower = p_{n+J+1} = upper of ⟨n+J⟩ < C_{m+1} ≤ C_{k₀+i}
          have hup := lt_contact_succ (β := β) hT
            (by linarith [(⟨n + J⟩ : PrimeGapInterval).one_lt_upper] : (0 : ℝ) < (⟨n + J⟩ : PrimeGapInterval).upper)
          have hmono := contactAt_mono (β := β) hT (k := meetingCell β T ⟨n + J⟩ + 1) (l := k₀ + i) (by omega)
          have hlow : (⟨n + J + 1⟩ : PrimeGapInterval).lower = (⟨n + J⟩ : PrimeGapInterval).upper := rfl
          rw [hlow]
          unfold meetingCell at hmono
          linarith
        · have hmono := contactAt_mono (β := β) hT (k := k₀ + i + 1) (l := meetingCell β T ⟨n + J + 1⟩) (by omega)
          linarith
      rw [hz, mul_zero]
    rw [htail]
    ring

/-! ## M4. Le bilan signé de la série -/

theorem series_signed_balance {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (m : ℕ) :
    signedCellSum β T k₀ m =
      signedPrimeSum β T k₀ (m + 1) + signedNonPrimeSum β T k₀ (m + 1) - signedLengthSum β T k₀ (m + 1) := by
  unfold signedCellSum signedPrimeSum signedNonPrimeSum signedLengthSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [cellDemand_eq hT, cellWeight_eq_prime_add_nonprime]
  ring

/-! ## M5. Forme close de la descente signée -/

theorem contactAt_add_nat_eq {β T : ℝ} (k₀ : ℤ) (i : ℕ) :
    contactAt β T (k₀ + i) = contactAt β T k₀ * Real.exp (Real.pi / T) ^ i := by
  rw [contactAt_eq, contactAt_eq, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem cellLength_add_nat {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (i : ℕ) :
    cellLength β T (k₀ + i) = cellLength β T k₀ * Real.exp (Real.pi / T) ^ i := by
  rw [cellLength_eq hT, cellLength_eq hT, contactAt_add_nat_eq]
  ring

theorem signedLengthSum_closed_form {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (M : ℕ) :
    signedLengthSum β T k₀ M =
      cellLength β T k₀ * (1 - (-Real.exp (Real.pi / T)) ^ M) / (1 + Real.exp (Real.pi / T)) := by
  unfold signedLengthSum
  set r := Real.exp (Real.pi / T) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hne : -r ≠ 1 := by linarith
  have hsum : ∑ i ∈ range M, (-1 : ℝ) ^ i * cellLength β T (k₀ + i) =
      cellLength β T k₀ * ∑ i ∈ range M, (-r) ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [cellLength_add_nat hT, neg_pow]
    ring
  rw [hsum, geom_sum_eq hne]
  have h1 : (1 + r) ≠ 0 := by linarith
  have h2 : (-r - 1) ≠ 0 := by linarith
  field_simp
  ring

/-- La descente signée vaut exactement `(première cellule − (−1)^{M+1}·r·dernière cellule)/(1 + r)`. -/
theorem signedLengthSum_first_last {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (M : ℕ) :
    signedLengthSum β T k₀ (M + 1) =
      (cellLength β T k₀ - (-1 : ℝ) ^ (M + 1) * Real.exp (Real.pi / T) * cellLength β T (k₀ + M)) /
        (1 + Real.exp (Real.pi / T)) := by
  rw [signedLengthSum_closed_form hT, cellLength_add_nat hT, neg_pow, pow_succ]
  ring

/-! ## M6. Les cellules de la série encadrées par les rencontres extrêmes et la fréquence -/

theorem cellLength_lt_of_lt_meeting {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) {k : ℤ}
    (hk : k < meetingCell β T I) :
    cellLength β T k < I.upper * (Real.exp (Real.pi / T) - 1) := by
  rw [cellLength_eq hT]
  have h1 : 1 < Real.exp (Real.pi / T) := Real.one_lt_exp_iff.mpr (by positivity)
  have hCk : contactAt β T k < contactAt β T (k + 1) := by
    have := cellLength_pos (β := β) hT k; unfold cellLength at this; linarith
  have hle : contactAt β T (k + 1) ≤ contactAt β T (meetingCell β T I) := contactAt_mono hT (by omega)
  have hup : contactAt β T (meetingCell β T I) ≤ I.upper :=
    lastContact_le hT (by linarith [I.one_lt_upper])
  have := contactAt_pos β T k
  nlinarith

theorem contactAt_eq_succ_mul {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    contactAt β T k = contactAt β T (k + 1) * Real.exp (-(Real.pi / T)) := by
  rw [contactAt_eq, contactAt_eq, ← Real.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem cellLength_eq_succ {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    cellLength β T k = contactAt β T (k + 1) * (1 - Real.exp (-(Real.pi / T))) := by
  unfold cellLength
  rw [contactAt_eq_succ_mul hT k]
  ring

theorem meeting_mul_lt_cellLength {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) {k : ℤ}
    (hk : meetingCell β T I ≤ k) :
    I.upper * (1 - Real.exp (-(Real.pi / T))) < cellLength β T k := by
  rw [cellLength_eq_succ hT]
  have h1 : Real.exp (-(Real.pi / T)) < 1 := by
    rw [Real.exp_lt_one_iff]; have := Real.pi_pos; have := div_pos this hT; linarith
  have hup : I.upper < contactAt β T (meetingCell β T I + 1) :=
    lt_contact_succ hT (by linarith [I.one_lt_upper])
  have hle : contactAt β T (meetingCell β T I + 1) ≤ contactAt β T (k + 1) := contactAt_mono hT (by omega)
  nlinarith

/-! ## M7. Le bilan signé de la série est, à moins d'une cellule de la dernière rencontre près, la somme signée des rencontres plus les poids non premiers signés -/

theorem series_balance_near_meetings {β T : ℝ} (hT : 0 < T) (n J m : ℕ)
    (hc : ∀ j ≤ J, GapHasContact β T ⟨n + j⟩)
    (hlt : ∀ j ≤ J, contactAt β T (meetingCell β T ⟨n + j⟩) < (⟨n + j⟩ : PrimeGapInterval).upper)
    (hM : meetingOffset β T n J = m + 1) :
    |signedCellSum β T (meetingCell β T ⟨n⟩) m - meetingSignedSum β T n J -
        signedNonPrimeSum β T (meetingCell β T ⟨n⟩) (m + 1)| <
      (⟨n + J⟩ : PrimeGapInterval).upper * (Real.exp (Real.pi / T) - 1) := by
  rw [series_signed_balance hT, ← hM, signedPrimeSum_eq_meetings hT n J hc hlt, hM]
  have hb : |signedLengthSum β T (meetingCell β T ⟨n⟩) (m + 1)| ≤
      cellLength β T (meetingCell β T ⟨n⟩ + m) :=
    signed_lengths_bounded hT _ m
  have hlast : cellLength β T (meetingCell β T ⟨n⟩ + m) <
      (⟨n + J⟩ : PrimeGapInterval).upper * (Real.exp (Real.pi / T) - 1) := by
    apply cellLength_lt_of_lt_meeting hT
    have := meetingOffset_eq (β := β) hT n J
    omega
  have e : meetingSignedSum β T n J + signedNonPrimeSum β T (meetingCell β T ⟨n⟩) (m + 1) -
      signedLengthSum β T (meetingCell β T ⟨n⟩) (m + 1) - meetingSignedSum β T n J -
      signedNonPrimeSum β T (meetingCell β T ⟨n⟩) (m + 1) =
      -signedLengthSum β T (meetingCell β T ⟨n⟩) (m + 1) := by ring
  rw [e, abs_neg]
  linarith

#print axioms meetingOffset_eq
#print axioms meetingOffset_succ
#print axioms meetingOffset_lt_succ
#print axioms signedPrimeSum_eq_meetings
#print axioms series_signed_balance
#print axioms contactAt_add_nat_eq
#print axioms cellLength_add_nat
#print axioms signedLengthSum_closed_form
#print axioms signedLengthSum_first_last
#print axioms cellLength_lt_of_lt_meeting
#print axioms cellLength_eq_succ
#print axioms meeting_mul_lt_cellLength
#print axioms series_balance_near_meetings

end RHV6Fresh
