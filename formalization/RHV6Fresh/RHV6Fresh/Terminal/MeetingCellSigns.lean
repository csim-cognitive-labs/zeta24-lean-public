/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GapSlopeByContacts

/-!
# RHV6Fresh — Terminal/MeetingCellSigns : le signe de la cellule qui contient la rencontre, le long
d'une série d'écarts
(E439, §19.56–19.57, 2026-11-07 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse,
aucun axiome, aucun `sorry`, aucune position radiale, aucune famille de Tours, aucune somme de
contributions, aucune théorie spectrale)

Objets : UNE Tour, SES contacts (signe `(−1)^k`), la cellule qui contient chaque rencontre
(`meetingCell β T I = lastContactBefore β T I.upper`), la série des écarts, la demande brute lue comme pente.

## S1. Le signe porté par un contact
* `cellSign k = (−1)^k`, `contactRealValue_eq_sign_mul` : la valeur au contact est son signe fois une
  quantité positive ; `contactRealValue_sign_shift` : le contact `m` rangs plus loin a le signe fois `(−1)^m`.

## S2–S3. La cellule de rencontre se transmet et se déplace
* `meetingCell_eq_next_lower` : la cellule de la rencontre de l'écart `n` est la cellule qui ouvre l'écart `n+1` ;
* `lastContactBefore_mono`, `meetingCell_step` : si l'écart `n+1` contient un contact, l'indice avance de
  (cellules entières + 1) ; `meetingCell_eq_of_no_contact` : sinon les deux rencontres partagent la cellule.

## S4. Le signe d'une rencontre à la suivante
* `meeting_sign_step` : le signe de la cellule de rencontre change selon la parité de (cellules entières + 1)
  de l'écart franchi ; `meeting_sign_same_of_no_contact` : même signe sans contact.

## S5. Le long d'une série
* `meetingCell_telescope`, `meetingCell_mono_rank`, `meeting_sign_series` : le signe de la cellule de
  rencontre au rang `n+J` est celui du rang `n` fois la parité du déplacement total ;
* `meetingCell_series_read_by_frequency` : ce déplacement est lu, à moins d'une unité près, par la fréquence
  fois le logarithme du rapport des deux rencontres.

## S6. Ce que les restes partiels imposent à la pente de la cellule de rencontre
* `inner_cell_variation` : une cellule entière strictement intérieure à un écart est une descente pure
  (poids non premiers seulement) ;
* `meeting_cell_primes` : la cellule de rencontre (reste final de l'écart + reste initial du suivant) franchit
  exactement UN premier, la rencontre ;
* `meeting_cell_demand`, `meeting_cell_demand_ge` : sa pente est `log p_{n+1}` + poids non premiers − sa
  longueur.

Rien ici ne parle de la position radiale ni d'aucune somme de Tours.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction Finset

/-! ## S1. Le signe porté par un contact -/

/-- Signe de la cellule ouverte par le contact `k` : `(−1)^k`. -/
noncomputable def cellSign (k : ℤ) : ℝ := (-1 : ℝ) ^ k

theorem contactRealValue_eq_sign_mul (β T : ℝ) (k : ℤ) :
    contactRealValue β T k = cellSign k * (contactAt β T k ^ β / ‖(⟨β, T⟩ : ℂ)‖) := by
  unfold contactRealValue cellSign
  ring

theorem contactRealValue_sign_shift {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (k : ℤ) (m : ℕ) :
    0 < (-1 : ℝ) ^ m * contactRealValue β T (k + m) * contactRealValue β T k := by
  rw [contactRealValue_add_nat hT.ne']
  set v := contactRealValue β T k
  set E := Real.exp (β * Real.pi / T)
  rw [neg_pow E m]
  have sq : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by rw [← mul_pow]; norm_num
  have hv : 0 < v * v := mul_self_pos.mpr (contactRealValue_ne_zero hβ _)
  have hE : 0 < E ^ m := pow_pos (Real.exp_pos _) m
  calc (0:ℝ) < ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) * (E ^ m * (v * v)) := by rw [sq, one_mul]; positivity
    _ = (-1 : ℝ) ^ m * ((-1 : ℝ) ^ m * E ^ m * v) * v := by ring

/-! ## S2–S3. La cellule de rencontre et son déplacement d'un écart au suivant -/

/-- Indice de la cellule qui contient la rencontre `p_{n+1}` de l'écart `I`. -/
noncomputable def meetingCell (β T : ℝ) (I : PrimeGapInterval) : ℤ :=
  lastContactBefore β T I.upper

theorem meetingCell_eq_next_lower (β T : ℝ) {I J : PrimeGapInterval} (hIJ : J.rank = I.rank + 1) :
    meetingCell β T I = lastContactBefore β T J.lower := by
  unfold meetingCell
  rw [consecutive_lower_eq_upper hIJ]

theorem lastContactBefore_mono {β T : ℝ} (hT : 0 < T) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    lastContactBefore β T x ≤ lastContactBefore β T y := by
  unfold lastContactBefore
  apply Int.floor_le_floor
  unfold stagePosition
  have := Real.log_le_log hx hxy
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  nlinarith

theorem meetingCell_step {β T : ℝ} {I J : PrimeGapInterval} (hIJ : J.rank = I.rank + 1)
    (h : GapHasContact β T J) :
    meetingCell β T J = meetingCell β T I + ((wholeCellCount β T J + 1 : ℕ) : ℤ) := by
  have hk := firstContact_add_count h
  unfold firstContactAfterLower at hk
  rw [consecutive_lower_eq_upper hIJ] at hk
  unfold meetingCell
  push_cast
  omega

theorem meetingCell_eq_of_no_contact {β T : ℝ} (hT : 0 < T) {I J : PrimeGapInterval}
    (hIJ : J.rank = I.rank + 1) (h : ¬ GapHasContact β T J) :
    meetingCell β T J = meetingCell β T I := by
  unfold GapHasContact at h
  rw [consecutive_lower_eq_upper hIJ] at h
  have hmono : lastContactBefore β T I.upper ≤ lastContactBefore β T J.upper :=
    lastContactBefore_mono hT (by linarith [I.one_lt_upper])
      (by rw [← consecutive_lower_eq_upper hIJ]; exact (J.lower_lt_upper).le)
  unfold meetingCell
  omega

/-! ## S4. Le signe de la cellule de rencontre d'un écart au suivant -/

theorem meeting_sign_step {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) {I J : PrimeGapInterval}
    (hIJ : J.rank = I.rank + 1) (h : GapHasContact β T J) :
    0 < (-1 : ℝ) ^ (wholeCellCount β T J + 1) *
      contactRealValue β T (meetingCell β T J) * contactRealValue β T (meetingCell β T I) := by
  rw [meetingCell_step hIJ h]
  exact contactRealValue_sign_shift hβ hT _ _

theorem meeting_sign_same_of_no_contact {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) {I J : PrimeGapInterval}
    (hIJ : J.rank = I.rank + 1) (h : ¬ GapHasContact β T J) :
    0 < contactRealValue β T (meetingCell β T J) * contactRealValue β T (meetingCell β T I) := by
  rw [meetingCell_eq_of_no_contact hT hIJ h]
  exact mul_self_pos.mpr (contactRealValue_ne_zero hβ _)

/-! ## S5. Le long d'une série : télescopage, parité du déplacement, lecture par la fréquence -/

theorem meetingCell_telescope (β T : ℝ) (n J : ℕ) :
    ∑ j ∈ range J, (meetingCell β T ⟨n + j + 1⟩ - meetingCell β T ⟨n + j⟩) =
      meetingCell β T ⟨n + J⟩ - meetingCell β T ⟨n⟩ := by
  have := Finset.sum_range_sub (fun j => meetingCell β T ⟨n + j⟩) J
  simpa [Nat.add_assoc] using this

theorem meetingCell_mono_rank {β T : ℝ} (hT : 0 < T) (n J : ℕ) :
    meetingCell β T ⟨n⟩ ≤ meetingCell β T ⟨n + J⟩ := by
  unfold meetingCell
  apply lastContactBefore_mono hT (by linarith [(⟨n⟩ : PrimeGapInterval).one_lt_upper])
  unfold PrimeGapInterval.upper
  exact_mod_cast thm_primeAtRank_strictMono.monotone (by omega : n + 1 ≤ n + J + 1)

theorem meeting_sign_series {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (n J : ℕ) :
    0 < (-1 : ℝ) ^ (meetingCell β T ⟨n + J⟩ - meetingCell β T ⟨n⟩).toNat *
      contactRealValue β T (meetingCell β T ⟨n + J⟩) * contactRealValue β T (meetingCell β T ⟨n⟩) := by
  have hm := meetingCell_mono_rank (β := β) hT n J
  generalize hmdef : (meetingCell β T ⟨n + J⟩ - meetingCell β T ⟨n⟩).toNat = m
  have hk : meetingCell β T ⟨n + J⟩ = meetingCell β T ⟨n⟩ + (m : ℤ) := by
    rw [← hmdef, Int.toNat_of_nonneg (by omega)]; ring
  rw [hk]
  exact contactRealValue_sign_shift hβ hT _ _

theorem meetingCell_series_read_by_frequency (β T : ℝ) (n J : ℕ) :
    |((meetingCell β T ⟨n + J⟩ - meetingCell β T ⟨n⟩ : ℤ) : ℝ) -
        T * Real.log ((⟨n + J⟩ : PrimeGapInterval).upper / (⟨n⟩ : PrimeGapInterval).upper) / Real.pi| < 1 :=
  lastContact_difference_bounds β T (by linarith [(⟨n⟩ : PrimeGapInterval).one_lt_upper])
    (by linarith [(⟨n + J⟩ : PrimeGapInterval).one_lt_upper])

/-! ## S6. Ce que les restes partiels imposent à la pente de la cellule de rencontre -/

/-- Une cellule entière strictement intérieure à un écart est une descente pure (poids non premiers seulement). -/
theorem inner_cell_variation {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) {k : ℤ}
    (hk : I.lower ≤ contactAt β T k) (hk' : contactAt β T (k + 1) < I.upper) :
    rawDemand (contactAt β T (k + 1)) - rawDemand (contactAt β T k) =
      ∑ n ∈ (Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 1)⌋₊).filter (fun n => ¬ Nat.Prime n), Λ n -
        (contactAt β T (k + 1) - contactAt β T k) :=
  inner_piece_variation I hk (contactAt_mono hT (by omega)) hk'

/-- Les premiers franchis par la cellule de rencontre : exactement `{p_{n+1}}`. -/
theorem meeting_cell_primes {β T : ℝ} (hT : 0 < T) {I J : PrimeGapInterval} (hIJ : J.rank = I.rank + 1)
    (hI : GapHasContact β T I) (hJ : GapHasContact β T J)
    (hltI : contactAt β T (meetingCell β T I) < I.upper)
    (hltJ : contactAt β T (meetingCell β T J) < J.upper) :
    (Ioc ⌊contactAt β T (meetingCell β T I)⌋₊ ⌊contactAt β T (meetingCell β T I + 1)⌋₊).filter
        (fun n => Nat.Prime n) = {fnPrimeAtRank (I.rank + 1)} := by
  set k := meetingCell β T I with hkdef
  set p := fnPrimeAtRank (I.rank + 1) with hp
  have hup : I.upper = (p : ℝ) := rfl
  have hCk0 : 0 ≤ contactAt β T k := (contactAt_pos β T k).le
  have hCk1 : (0:ℝ) ≤ contactAt β T (k + 1) := (contactAt_pos β T _).le
  -- p_n ≤ C_k (l'écart I contient un contact)
  have hlowI : I.lower ≤ contactAt β T k := by
    have hl := lt_contact_succ (β := β) hT (by linarith [I.one_lt_lower] : 0 < I.lower)
    unfold GapHasContact at hI
    exact hl.le.trans (contactAt_mono hT (by unfold meetingCell at hkdef; omega))
  -- p < C_{k+1}
  have hpC : (p : ℝ) < contactAt β T (k + 1) := by
    rw [← hup]; exact lt_contact_succ hT (by linarith [I.one_lt_upper])
  -- C_{k+1} < p_{n+2} (l'écart J contient un contact strictement avant sa rencontre)
  have hC1J : contactAt β T (k + 1) < J.upper := by
    have h1 : k + 1 ≤ meetingCell β T J := by
      unfold GapHasContact at hJ
      rw [consecutive_lower_eq_upper hIJ] at hJ
      unfold meetingCell at hkdef ⊢; omega
    exact (contactAt_mono hT h1).trans_lt hltJ
  have hJup : J.upper = (fnPrimeAtRank (I.rank + 1 + 1) : ℝ) := by
    unfold PrimeGapInterval.upper; rw [hIJ]
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, thm_primeAtRank_isPrime _⟩
    · exact (Nat.floor_lt hCk0).mpr (by rw [← hup]; exact hltI)
    · exact Nat.le_floor hpC.le
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hq
    obtain ⟨⟨hq1, hq2⟩, hqp⟩ := hq
    have hlow : fnPrimeAtRank I.rank ≤ ⌊contactAt β T k⌋₊ := Nat.le_floor hlowI
    have hq2' : (q : ℝ) < fnPrimeAtRank (I.rank + 1 + 1) := by
      have h1 : (q : ℝ) ≤ (⌊contactAt β T (k + 1)⌋₊ : ℝ) := by exact_mod_cast hq2
      have h2 := Nat.floor_le hCk1
      rw [hJup] at hC1J
      linarith
    have hq2'' : q < fnPrimeAtRank (I.rank + 1 + 1) := by exact_mod_cast hq2'
    rcases lt_trichotomy q p with hlt | heq | hgt
    · exact absurd (thm_noPrimeStrictlyBetweenSuccessivePrimes I.rank hqp (by omega)
        (by unfold fnPrimeSuccessor; omega)) id
    · exact heq
    · exact absurd (thm_noPrimeStrictlyBetweenSuccessivePrimes (I.rank + 1) hqp (by omega)
        (by unfold fnPrimeSuccessor; omega)) id

/-- **La cellule de rencontre porte exactement un poids premier** : sa pente est `log p_{n+1}` + poids non premiers −
sa longueur. -/
theorem meeting_cell_demand {β T : ℝ} (hT : 0 < T) {I J : PrimeGapInterval} (hIJ : J.rank = I.rank + 1)
    (hI : GapHasContact β T I) (hJ : GapHasContact β T J)
    (hltI : contactAt β T (meetingCell β T I) < I.upper)
    (hltJ : contactAt β T (meetingCell β T J) < J.upper) :
    rawDemand (contactAt β T (meetingCell β T I + 1)) - rawDemand (contactAt β T (meetingCell β T I)) =
      Real.log (fnPrimeAtRank (I.rank + 1)) +
        ∑ n ∈ (Ioc ⌊contactAt β T (meetingCell β T I)⌋₊ ⌊contactAt β T (meetingCell β T I + 1)⌋₊).filter
          (fun n => ¬ Nat.Prime n), Λ n -
        (contactAt β T (meetingCell β T I + 1) - contactAt β T (meetingCell β T I)) := by
  rw [rawDemand_variation (contactAt_mono hT (by omega)),
    ← Finset.sum_filter_add_sum_filter_not _ (fun n => Nat.Prime n),
    meeting_cell_primes hT hIJ hI hJ hltI hltJ, Finset.sum_singleton,
    vonMangoldt_apply_prime (thm_primeAtRank_isPrime _)]

theorem meeting_cell_demand_ge {β T : ℝ} (hT : 0 < T) {I J : PrimeGapInterval} (hIJ : J.rank = I.rank + 1)
    (hI : GapHasContact β T I) (hJ : GapHasContact β T J)
    (hltI : contactAt β T (meetingCell β T I) < I.upper)
    (hltJ : contactAt β T (meetingCell β T J) < J.upper) :
    Real.log (fnPrimeAtRank (I.rank + 1)) -
        (contactAt β T (meetingCell β T I + 1) - contactAt β T (meetingCell β T I)) ≤
      rawDemand (contactAt β T (meetingCell β T I + 1)) - rawDemand (contactAt β T (meetingCell β T I)) := by
  rw [meeting_cell_demand hT hIJ hI hJ hltI hltJ]
  have := Finset.sum_nonneg (fun n _ => (vonMangoldt_nonneg : 0 ≤ Λ n))
    (s := (Ioc ⌊contactAt β T (meetingCell β T I)⌋₊ ⌊contactAt β T (meetingCell β T I + 1)⌋₊).filter
      (fun n => ¬ Nat.Prime n))
  linarith


#print axioms contactRealValue_eq_sign_mul
#print axioms contactRealValue_sign_shift
#print axioms meetingCell_eq_next_lower
#print axioms lastContactBefore_mono
#print axioms meetingCell_step
#print axioms meetingCell_eq_of_no_contact
#print axioms meeting_sign_step
#print axioms meeting_sign_same_of_no_contact
#print axioms meetingCell_telescope
#print axioms meetingCell_mono_rank
#print axioms meeting_sign_series
#print axioms meetingCell_series_read_by_frequency
#print axioms inner_cell_variation
#print axioms meeting_cell_primes
#print axioms meeting_cell_demand
#print axioms meeting_cell_demand_ge

end RHV6Fresh
