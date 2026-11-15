/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GapsAboveThreshold
import RHV6Fresh.Terminal.ContactRealValue

/-!
# Le bilan signé porté par la fréquence ET l'amplitude : les contacts lisent la position radiale (E444, 2026-11-07)

Module isolé (non ajouté à `RHV6Fresh.lean`). Correction de l'auteur §19.63 : les contacts retrouvent la position
radiale par les formules tangentielles (`inversion_radial`, `radial_of_contact_tangent`,
`radial_of_contact_value_ratio`, `radial_from_amplitude_step`) ; une Tour a une fréquence `T` ET une amplitude ;
l'intervalle sur l'axe réel est défini par les deux. Ce module reprend le bilan signé de la série (§19.60–19.62)
avec les deux variables : chaque cellule pèse par la valeur réelle de la Tour à son contact
`contactRealValue β T k = (−1)^k · C_k^β / ‖ρ‖` (signe ET amplitude), et non par son signe seul.

* B1 `stagePosition_sub_radial`, `towerPhase_lt_of_radial_lt`, `stagePosition_lt_of_radial_lt` : à `T` et `x`
  fixés la position de cellule croît strictement avec `β` ; le signe de la cellule d'un réel dépend de `β`.
* B2 `radial_of_stagePosition`, `radial_of_cellFraction` : `β = T / tan(T log x − π (cellule + fraction))`.
* B3 `cellLength_ratio`, `height_of_cellLength_ratio`, `radial_of_value_and_length_ratios` :
  `T = π / log(L_{k+1}/L_k)`, `β = log(|v_{k+1}|/|v_k|) / log(L_{k+1}/L_k)` : l'intervalle rend les deux.
* B4 `valueLengthSum`, `valueLengthSum_closed_form` : descente pondérée par l'amplitude, raison `−e^{(β+1)π/T}`.
* B5 `valueCellSum`, `valueCellSum_eq_signed` : bilan pondéré = valeur initiale × somme signée à poids `e^{βπ/T}`.
* B6 `valuePrimeSum`, `valuePrimeSum_eq_primes_in_block`, `amplitudeMeetingSum`, `valuePrimeSum_eq_meetings` :
  le poids premier pondéré d'un bloc (plusieurs rencontres par cellule) et d'une série de rencontres est la somme
  des rencontres pesées par la valeur de leur cellule.
* B7 `meeting_value_step`, `meeting_value_ratio_sign`, `radial_of_meeting_values`, `meetingOffset_lt_bertrand` :
  entre deux rencontres le rapport des valeurs est `(−e^{βπ/T})^Δ`, `Δ` = déplacement ; le signe change selon la
  parité de `Δ`, l'amplitude lit `β` ; `Δ < T log 2/π + 1` (Bertrand).

Une seule Tour, ses contacts, ses valeurs, ses cellules, les écarts et la demande brute ; aucune somme de Tours.
Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/
namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction Finset

/-! ## B1. Le signe de la cellule d'un réel lit la position radiale -/

theorem stagePosition_sub_radial (β β' T x : ℝ) :
    stagePosition β T x - stagePosition β' T x = (towerPhase β' T - towerPhase β T) / Real.pi := by
  unfold stagePosition towerPhase
  ring

theorem towerPhase_lt_of_radial_lt {β β' T : ℝ} (hT : 0 < T) (hβ : 0 < β) (hββ' : β < β') :
    towerPhase β' T < towerPhase β T := by
  unfold towerPhase
  rw [Real.arctan_lt_arctan_iff]
  exact div_lt_div_of_pos_left hT hβ hββ'

theorem stagePosition_lt_of_radial_lt {β β' T : ℝ} (hT : 0 < T) (hβ : 0 < β) (hββ' : β < β') (x : ℝ) :
    stagePosition β T x < stagePosition β' T x := by
  have h := towerPhase_lt_of_radial_lt hT hβ hββ'
  have : stagePosition β' T x - stagePosition β T x = (towerPhase β T - towerPhase β' T) / Real.pi :=
    stagePosition_sub_radial β' β T x
  have hpos : 0 < (towerPhase β T - towerPhase β' T) / Real.pi := div_pos (by linarith) Real.pi_pos
  linarith

/-! ## B2. La fraction de cellule lit la position radiale -/

theorem radial_of_stagePosition {β T : ℝ} (hβ : 0 < β) (hT : T ≠ 0) (x : ℝ) :
    β = T / Real.tan (T * Real.log x - Real.pi * stagePosition β T x) := by
  have h : T * Real.log x - Real.pi * stagePosition β T x = Real.arctan (T / β) := by
    unfold stagePosition
    field_simp
    ring
  rw [h, Real.tan_arctan]
  field_simp

theorem radial_of_cellFraction {β T : ℝ} (hβ : 0 < β) (hT : T ≠ 0) (x : ℝ) :
    β = T / Real.tan (T * Real.log x - Real.pi * (lastContactBefore β T x + cellFraction β T x)) := by
  have h : (lastContactBefore β T x : ℝ) + cellFraction β T x = stagePosition β T x := by
    unfold lastContactBefore cellFraction
    exact Int.floor_add_fract _
  rw [h]
  exact radial_of_stagePosition hβ hT x

/-! ## B3. L'intervalle est défini par la fréquence ET l'amplitude -/

theorem cellLength_ratio {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    cellLength β T (k + 1) / cellLength β T k = Real.exp (Real.pi / T) := by
  rw [cellLength_eq hT, cellLength_eq hT, mul_div_mul_right _ _ (by
    have := Real.one_lt_exp_iff.mpr (by positivity : 0 < Real.pi / T); linarith),
    contactAt_ratio hT.ne']

theorem height_of_cellLength_ratio {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    T = Real.pi / Real.log (cellLength β T (k + 1) / cellLength β T k) := by
  rw [cellLength_ratio hT, Real.log_exp]
  field_simp

theorem radial_of_value_and_length_ratios {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (k : ℤ) :
    β = Real.log (|contactRealValue β T (k + 1)| / |contactRealValue β T k|) /
      Real.log (cellLength β T (k + 1) / cellLength β T k) := by
  rw [cellLength_ratio hT, abs_contactRealValue_ratio hβ hT.ne', Real.log_exp, Real.log_exp]
  field_simp

/-! ## B4. Le bilan des longueurs pondéré par l'amplitude -/

/-- `contactRealValue_add_nat` (GapSlopeByContacts) : `v_{k+i} = (−e^{βπ/T})^i · v_k`. -/

noncomputable def valueLengthSum (β T : ℝ) (k₀ : ℤ) (M : ℕ) : ℝ :=
  ∑ i ∈ range M, contactRealValue β T (k₀ + i) * cellLength β T (k₀ + i)

theorem valueLengthSum_closed_form {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (M : ℕ) :
    valueLengthSum β T k₀ M =
      contactRealValue β T k₀ * cellLength β T k₀ *
        (1 - (-Real.exp ((β + 1) * Real.pi / T)) ^ M) / (1 + Real.exp ((β + 1) * Real.pi / T)) := by
  unfold valueLengthSum
  set r := Real.exp ((β + 1) * Real.pi / T) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hne : -r ≠ 1 := by linarith
  have hsplit : r = Real.exp (β * Real.pi / T) * Real.exp (Real.pi / T) := by
    rw [hr, ← Real.exp_add]; congr 1; ring
  have hsum : ∑ i ∈ range M, contactRealValue β T (k₀ + i) * cellLength β T (k₀ + i) =
      contactRealValue β T k₀ * cellLength β T k₀ * ∑ i ∈ range M, (-r) ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [cellLength_add_nat hT, contactRealValue_add_nat hT.ne', hsplit, ← neg_mul, mul_pow]
    ring
  rw [hsum, geom_sum_eq hne]
  have h1 : (1 + r) ≠ 0 := by linarith
  have h2 : (-r - 1) ≠ 0 := by linarith
  field_simp
  ring

/-! ## B5. Le bilan des pentes pondéré par l'amplitude -/

noncomputable def valueCellSum (β T : ℝ) (k₀ : ℤ) (m : ℕ) : ℝ :=
  ∑ j ∈ range (m + 1), contactRealValue β T (k₀ + j) * cellDemand β T (k₀ + j)

theorem valueCellSum_eq_signed {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (m : ℕ) :
    valueCellSum β T k₀ m =
      contactRealValue β T k₀ *
        ∑ j ∈ range (m + 1), (-1 : ℝ) ^ j * Real.exp (β * Real.pi / T) ^ j * cellDemand β T (k₀ + j) := by
  unfold valueCellSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [contactRealValue_add_nat hT.ne', neg_pow]
  ring

/-! ## B6. Le poids premier pondéré d'un bloc : chaque rencontre pèse par la valeur de sa cellule -/

noncomputable def valuePrimeSum (β T : ℝ) (k₀ : ℤ) (M : ℕ) : ℝ :=
  ∑ i ∈ range M, contactRealValue β T (k₀ + i) * cellPrimeWeight β T (k₀ + i)

theorem valuePrimeSum_eq_primes_in_block {β T : ℝ} (hT : 0 < T) (a : ℤ) (M : ℕ)
    (hnc : ∀ (k : ℤ) (q : ℕ), (q : ℝ) ≠ contactAt β T k) :
    valuePrimeSum β T a M =
      ∑ q ∈ (Ioc ⌊contactAt β T a⌋₊ ⌊contactAt β T (a + M)⌋₊).filter (fun q => Nat.Prime q),
        contactRealValue β T (lastContactBefore β T q) * Real.log q := by
  induction M with
  | zero => simp [valuePrimeSum]
  | succ M ih =>
    unfold valuePrimeSum at ih ⊢
    rw [Finset.sum_range_succ, ih, Finset.sum_filter, Finset.sum_filter]
    have hmono : ⌊contactAt β T a⌋₊ ≤ ⌊contactAt β T (a + M)⌋₊ :=
      Nat.floor_mono (contactAt_mono hT (by omega))
    have hmono' : ⌊contactAt β T (a + M)⌋₊ ≤ ⌊contactAt β T (a + (M + 1 : ℕ))⌋₊ :=
      Nat.floor_mono (contactAt_mono hT (by push_cast; omega))
    rw [← Finset.sum_Ioc_consecutive _ hmono hmono']
    congr 1
    unfold cellPrimeWeight
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr (by push_cast; ring_nf)
    intro q hq
    have hcell : lastContactBefore β T q = a + M := by
      apply lastContactBefore_of_mem_cell hT (k := a + M) _ (hnc _ _)
      have e : (a + (M + 1 : ℕ) : ℤ) = a + M + 1 := by push_cast; ring
      rw [← e]; exact hq
    rw [hcell]
    split_ifs with hp
    · rw [vonMangoldt_apply_prime hp]
    · simp

noncomputable def amplitudeMeetingSum (β T : ℝ) (n J : ℕ) : ℝ :=
  ∑ j ∈ range J, contactRealValue β T (meetingCell β T ⟨n + j⟩) * Real.log (fnPrimeAtRank (n + j + 1))

theorem valuePrimeSum_eq_meetings {β T : ℝ} (hT : 0 < T) (n J : ℕ)
    (hc : ∀ j ≤ J, GapHasContact β T ⟨n + j⟩)
    (hlt : ∀ j ≤ J, contactAt β T (meetingCell β T ⟨n + j⟩) < (⟨n + j⟩ : PrimeGapInterval).upper) :
    valuePrimeSum β T (meetingCell β T ⟨n⟩) (meetingOffset β T n J) = amplitudeMeetingSum β T n J := by
  induction J with
  | zero => simp [valuePrimeSum, amplitudeMeetingSum, meetingOffset_zero]
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
    unfold valuePrimeSum amplitudeMeetingSum
    rw [← Finset.sum_range_add_sum_Ico _ hoff.le, Finset.sum_range_succ,
      Finset.sum_eq_sum_Ico_succ_bot hoff]
    unfold valuePrimeSum amplitudeMeetingSum at ih'
    rw [ih', hka]
    have hmeet : cellPrimeWeight β T (meetingCell β T ⟨n + J⟩) = Real.log (fnPrimeAtRank (n + J + 1)) :=
      cellPrimeWeight_meeting hT (I := ⟨n + J⟩) (J := ⟨n + J + 1⟩) rfl (hc J (by omega)) hJ1
        (hlt J (by omega)) hlt1
    rw [hmeet]
    have htail : ∑ i ∈ Ico (a + 1) b, contactRealValue β T (k₀ + i) * cellPrimeWeight β T (k₀ + i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hz : cellPrimeWeight β T (k₀ + i) = 0 := by
        apply cellPrimeWeight_inner_eq_zero hT ⟨n + J + 1⟩
        · have hup := lt_contact_succ (β := β) hT
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

/-! ## B7. Entre deux rencontres : rapport des valeurs, changements de signe bornés par Bertrand -/

theorem meeting_value_step {β T : ℝ} (hT : 0 < T) (n j : ℕ) :
    contactRealValue β T (meetingCell β T ⟨n + j⟩) =
      contactRealValue β T (meetingCell β T ⟨n⟩) * (-Real.exp (β * Real.pi / T)) ^ (meetingOffset β T n j) := by
  have h : meetingCell β T ⟨n + j⟩ = meetingCell β T ⟨n⟩ + (meetingOffset β T n j : ℤ) := by
    have := meetingOffset_eq (β := β) hT n j; omega
  rw [h, contactRealValue_add_nat hT.ne']
  ring

theorem meeting_value_ratio_sign {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (n j : ℕ) :
    contactRealValue β T (meetingCell β T ⟨n + j⟩) / contactRealValue β T (meetingCell β T ⟨n⟩) =
      (-1 : ℝ) ^ (meetingOffset β T n j) * Real.exp (β * Real.pi / T) ^ (meetingOffset β T n j) := by
  rw [meeting_value_step hT, neg_pow, mul_div_cancel_left₀ _ (contactRealValue_ne_zero hβ _)]

theorem radial_of_meeting_values {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (n j : ℕ) (hj : 0 < meetingOffset β T n j) :
    β = T * Real.log (|contactRealValue β T (meetingCell β T ⟨n + j⟩)| /
      |contactRealValue β T (meetingCell β T ⟨n⟩)|) / (meetingOffset β T n j * Real.pi) := by
  rw [← abs_div, meeting_value_ratio_sign hβ hT, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (pow_pos (Real.exp_pos _) _), ← Real.exp_nat_mul, Real.log_exp]
  have : (meetingOffset β T n j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  field_simp

theorem meetingOffset_lt_bertrand {β T : ℝ} (hT : 0 < T) (n : ℕ) :
    ((meetingOffset β T n 1 : ℕ) : ℝ) < T * Real.log 2 / Real.pi + 1 := by
  have h := meetingCell_displacement_lt (β := β) hT (I := ⟨n⟩) (J := ⟨n + 1⟩) rfl
  have e := meetingOffset_eq (β := β) hT n 1
  have : ((meetingOffset β T n 1 : ℕ) : ℝ) = ((meetingCell β T ⟨n + 1⟩ - meetingCell β T ⟨n⟩ : ℤ) : ℝ) := by
    rw [← e]; push_cast; ring
  rw [this]; exact h

#print axioms RHV6Fresh.stagePosition_lt_of_radial_lt
#print axioms RHV6Fresh.radial_of_cellFraction
#print axioms RHV6Fresh.radial_of_value_and_length_ratios
#print axioms RHV6Fresh.valueLengthSum_closed_form
#print axioms RHV6Fresh.valueCellSum_eq_signed
#print axioms RHV6Fresh.valuePrimeSum_eq_primes_in_block
#print axioms RHV6Fresh.valuePrimeSum_eq_meetings
#print axioms RHV6Fresh.radial_of_meeting_values
#print axioms RHV6Fresh.meetingOffset_lt_bertrand

end RHV6Fresh
