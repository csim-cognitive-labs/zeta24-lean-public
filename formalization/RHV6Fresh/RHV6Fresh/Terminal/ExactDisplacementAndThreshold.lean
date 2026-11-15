/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MeetingSignedSeries

/-!
# RHV6Fresh — Terminal/ExactDisplacementAndThreshold : les règles d'E441 compilées
(E442, §19.60–19.61, 2026-11-07 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse,
aucun axiome, aucun `sorry`, aucune position radiale, aucune famille de Tours, aucune théorie spectrale)

Objets : UNE Tour, SES contacts et cellules, la fraction de cellule, les rencontres, la demande brute.

## D1–D2. Le déplacement exact du dernier contact (règle R1 d'E441)
* `floor_add_sub_floor` ; `displacement_rule`, `meetingCell_displacement_rule` : **d'une rencontre à la suivante,
  la cellule avance de `⌊T log(p'/p)/π⌋`, plus un si la fraction de cellule à `p` ajoutée à la partie
  fractionnaire atteint un** — la fréquence lit à une unité près, la fraction de cellule rend exact.

## D3–D5. La cellule d'un entier ; le poids premier signé d'un bloc sans hypothèse de contact par écart
* `stagePosition_contact`, `lastContactBefore_contact`, `lastContactBefore_of_mem_cell` ;
* `signedPrimeSum_eq_primes_in_block` : **le poids premier signé d'un bloc de cellules est la somme, sur les
  premiers du bloc, de `(−1)^{cellule(q) − a}·log q`** (les rencontres qui partagent une cellule portent le même
  signe ; hypothèse ponctuelle : aucun contact n'est un entier).

## D6–D7. Le seuil de montée des cellules de rencontre (règle R4 d'E441)
* `cellLength_meeting_le`, `meeting_rises_of_weight_dominates` : si `p(r − 1) ≤ log p`, la cellule de rencontre
  monte ; `meeting_falls_of_length_dominates` : si `log p` + poids non premiers `< p(1 − 1/r)`, elle descend ;
* `weight_dominates_below_threshold` : sous un point `x` où `x(r − 1) ≤ log x` (et au-dessus de `1/(r − 1)`), le
  poids domine la cellule : **le seuil `x*` défini par `x*(r − 1) = log x*` sépare les deux régimes**.

Rien ici ne parle de la position radiale ni d'aucune somme de Tours.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction Finset

/-! ## D1. Arithmétique des parties entières -/

theorem floor_add_sub_floor (a d : ℝ) :
    ⌊a + d⌋ - ⌊a⌋ = ⌊d⌋ + (if 1 ≤ Int.fract a + Int.fract d then 1 else 0) := by
  have ha := Int.floor_add_fract a
  have hd := Int.floor_add_fract d
  have h0a := Int.fract_nonneg a
  have h0d := Int.fract_nonneg d
  have h1a := Int.fract_lt_one a
  have h1d := Int.fract_lt_one d
  split_ifs with h
  · have : ⌊a + d⌋ = ⌊a⌋ + ⌊d⌋ + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    omega
  · rw [not_le] at h
    have : ⌊a + d⌋ = ⌊a⌋ + ⌊d⌋ := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    omega

/-! ## D2. Le déplacement exact du dernier contact, lu par la fréquence ET la fraction de cellule -/

theorem displacement_rule (β T : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    lastContactBefore β T y - lastContactBefore β T x =
      ⌊T * Real.log (y / x) / Real.pi⌋ +
        (if 1 ≤ cellFraction β T x + Int.fract (T * Real.log (y / x) / Real.pi) then 1 else 0) := by
  unfold lastContactBefore cellFraction
  have hs : stagePosition β T y = stagePosition β T x + T * Real.log (y / x) / Real.pi := by
    have := stagePosition_sub β T x y hx hy; linarith
  rw [hs]
  exact floor_add_sub_floor _ _

theorem meetingCell_displacement_rule (β T : ℝ) {I J : PrimeGapInterval} (hIJ : J.rank = I.rank + 1) :
    meetingCell β T J - meetingCell β T I =
      ⌊T * Real.log (J.upper / I.upper) / Real.pi⌋ +
        (if 1 ≤ cellFraction β T I.upper + Int.fract (T * Real.log (J.upper / I.upper) / Real.pi) then 1
          else 0) := by
  unfold meetingCell
  have _ := hIJ
  exact displacement_rule β T (by linarith [I.one_lt_upper]) (by linarith [J.one_lt_upper])

/-! ## D3–D4. La position d'étage d'un contact est son indice ; la cellule d'un entier -/

theorem stagePosition_contact {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    stagePosition β T (contactAt β T k) = k := by
  rw [contactAt_eq]
  unfold stagePosition towerPhase
  rw [Real.log_exp]
  field_simp
  ring

theorem lastContactBefore_contact {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    lastContactBefore β T (contactAt β T k) = k := by
  unfold lastContactBefore
  rw [stagePosition_contact hT, Int.floor_intCast]

theorem stagePosition_mono {β T : ℝ} (hT : 0 < T) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    stagePosition β T x ≤ stagePosition β T y := by
  unfold stagePosition
  have := Real.log_le_log hx hxy
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  nlinarith

theorem stagePosition_strictMono {β T : ℝ} (hT : 0 < T) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    stagePosition β T x < stagePosition β T y := by
  unfold stagePosition
  have := Real.log_lt_log hx hxy
  apply div_lt_div_of_pos_right _ Real.pi_pos
  nlinarith

theorem lastContactBefore_of_mem_cell {β T : ℝ} (hT : 0 < T) {k : ℤ} {q : ℕ}
    (hq : q ∈ Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 1)⌋₊) (hnc : (q : ℝ) ≠ contactAt β T (k + 1)) :
    lastContactBefore β T q = k := by
  rw [Finset.mem_Ioc] at hq
  obtain ⟨h1, h2⟩ := hq
  have hlo : contactAt β T k < q := (Nat.floor_lt (contactAt_pos β T k).le).mp h1
  have hhi : (q : ℝ) ≤ contactAt β T (k + 1) := (Nat.le_floor_iff (contactAt_pos β T _).le).mp h2
  have hhi' : (q : ℝ) < contactAt β T (k + 1) := lt_of_le_of_ne hhi hnc
  unfold lastContactBefore
  rw [Int.floor_eq_iff]
  constructor
  · have := stagePosition_mono (β := β) hT (contactAt_pos β T k) hlo.le
    rw [stagePosition_contact hT] at this; exact this
  · have hq0 : (0 : ℝ) < q := lt_trans (contactAt_pos β T k) hlo
    have := stagePosition_strictMono (β := β) hT hq0 hhi'
    rw [stagePosition_contact hT] at this; push_cast at this ⊢; exact this

/-! ## D5. Le poids premier signé d'un bloc de cellules, sans hypothèse de contact par écart -/

theorem signedPrimeSum_eq_primes_in_block {β T : ℝ} (hT : 0 < T) (a : ℤ) (M : ℕ)
    (hnc : ∀ (k : ℤ) (q : ℕ), (q : ℝ) ≠ contactAt β T k) :
    signedPrimeSum β T a M =
      ∑ q ∈ (Ioc ⌊contactAt β T a⌋₊ ⌊contactAt β T (a + M)⌋₊).filter (fun q => Nat.Prime q),
        (-1 : ℝ) ^ (lastContactBefore β T q - a) * Real.log q := by
  induction M with
  | zero => simp [signedPrimeSum]
  | succ M ih =>
    unfold signedPrimeSum at ih ⊢
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
      have e : (a + (M : ℤ) - a) = (M : ℤ) := by ring
      rw [e, zpow_natCast]
    · simp

/-! ## D6. Les deux sûre-zones du seuil de montée -/

theorem cellLength_meeting_le {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) :
    cellLength β T (meetingCell β T I) ≤ I.upper * (Real.exp (Real.pi / T) - 1) := by
  rw [cellLength_eq hT]
  have h1 : 1 ≤ Real.exp (Real.pi / T) := Real.one_le_exp (by positivity)
  have hup : contactAt β T (meetingCell β T I) ≤ I.upper :=
    lastContact_le hT (by linarith [I.one_lt_upper])
  exact mul_le_mul_of_nonneg_right hup (by linarith)

theorem meeting_rises_of_weight_dominates {β T : ℝ} (hT : 0 < T) {I J : PrimeGapInterval}
    (hIJ : J.rank = I.rank + 1) (hI : GapHasContact β T I) (hJ : GapHasContact β T J)
    (hltI : contactAt β T (meetingCell β T I) < I.upper)
    (hltJ : contactAt β T (meetingCell β T J) < J.upper)
    (hw : I.upper * (Real.exp (Real.pi / T) - 1) ≤ Real.log (fnPrimeAtRank (I.rank + 1))) :
    0 ≤ cellDemand β T (meetingCell β T I) :=
  meeting_cell_demand_nonneg_of_short hT hIJ hI hJ hltI hltJ
    ((cellLength_meeting_le hT I).trans hw)

theorem meeting_falls_of_length_dominates {β T : ℝ} (hT : 0 < T) {I J : PrimeGapInterval}
    (hIJ : J.rank = I.rank + 1) (hI : GapHasContact β T I) (hJ : GapHasContact β T J)
    (hltI : contactAt β T (meetingCell β T I) < I.upper)
    (hltJ : contactAt β T (meetingCell β T J) < J.upper)
    (hl : Real.log (fnPrimeAtRank (I.rank + 1)) + cellNonPrimeWeight β T (meetingCell β T I) <
      I.upper * (1 - Real.exp (-(Real.pi / T)))) :
    cellDemand β T (meetingCell β T I) < 0 := by
  rw [meeting_cellDemand hT hIJ hI hJ hltI hltJ]
  have := meeting_mul_lt_cellLength hT I (k := meetingCell β T I) le_rfl
  linarith

/-! ## D7. Sous le seuil, le poids domine la cellule -/

theorem weight_dominates_below_threshold {r x p : ℝ} (hr : 1 < r)
    (hx : x * (r - 1) ≤ Real.log x) (hp1 : 1 / (r - 1) ≤ p) (hpx : p ≤ x) :
    p * (r - 1) ≤ Real.log p := by
  have hr1 : 0 < r - 1 := by linarith
  have hp : 0 < p := lt_of_lt_of_le (by positivity) hp1
  have hx0 : 0 < x := lt_of_lt_of_le hp hpx
  have hlog : Real.log (x / p) ≤ x / p - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hx0.ne' hp.ne'] at hlog
  have hdiv : 1 / (r - 1) * (r - 1) = 1 := by field_simp
  have hinv : 1 / p ≤ r - 1 := by
    rw [div_le_iff₀ hp]; nlinarith
  have hxp : x / p - 1 = (x - p) / p := by field_simp
  have hbound : (x - p) / p ≤ (x - p) * (r - 1) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hinv (by linarith)
  nlinarith

#print axioms floor_add_sub_floor
#print axioms displacement_rule
#print axioms meetingCell_displacement_rule
#print axioms stagePosition_contact
#print axioms lastContactBefore_contact
#print axioms stagePosition_mono
#print axioms stagePosition_strictMono
#print axioms lastContactBefore_of_mem_cell
#print axioms signedPrimeSum_eq_primes_in_block
#print axioms cellLength_meeting_le
#print axioms meeting_rises_of_weight_dominates
#print axioms meeting_falls_of_length_dominates
#print axioms weight_dominates_below_threshold

end RHV6Fresh
