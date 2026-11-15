/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MirrorStrip
import RHV6Fresh.Terminal.MeetingCellSigns


/-!
# RHV6Fresh — Terminal/CarrierLocalReading : hypothèses locales H-a et H-b, classées contre RH
(E459, plan Φ étape Φ3, §19.80, §19.83, §19.88, 2026-11-09 ; module isolé, NON importé par `RHV6Fresh.lean` ;
aucune hypothèse, aucun axiome, aucun `sorry`)

Forme paramétrique `SameReadingAt β T n` : le rang `n` n'est pas dans la bande de la Tour `(β, T)`.

* Dictionnaire : `sameReadingAt_iff` ; `meetingCell_eq_towerWord`, `same_meetingCell_iff` : la cellule de rencontre d'un écart est
  le mot au rang suivant.
* H-a, rubrique (ii), contre-modèle au niveau des Tours : `towerWord_stable_near` (hors contact exact, le mot est localement
  constant en la position radiale), `sameReading_window` (fenêtre ouverte de même lecture autour de la ligne sur tout ensemble fini
  de rangs sans contact exact), `exists_offLine_sameReading_on_finset` (une Tour du côté bas, hors ligne, a la même lecture).
* H-a, branche dégénérée : `mem_mirrorStrip_of_prime_on_line_contact` ; classement exact `sameReadingAt_forces_line_iff` : la même
  lecture au rang `n` force la ligne à la hauteur `T` si et seulement si le premier de rang `n` est exactement sur un contact de
  la ligne de hauteur `T`. Branche LOGIQUE : il n'est jamais affirmé qu'un premier est sur un contact (§19.51).
* H-b : `sameReading_beyond_iff` (sur les Tours, même lecture à partir d'un rang ⟺ ligne).
* Sur les zéros vrais : `sameReadingAtRank_of_riemannHypothesis` (RH ⟹ H-a ; réciproque OUVERTE) ;
  `sameReadingBeyond_iff_riemannHypothesis`, `sameMeetingCells_iff_riemannHypothesis` (H-b ⟺ RH : reformulation, JAMAIS posée).

Portée : aucune des propositions nommées n'est posée ; le poids n'intervient dans aucune exigence de ce module (critère d'arrêt du
plan Φ non atteint) ; aucune contradiction n'est tirée ; aucune densité n'est affirmée ; aucune théorie spectrale.
-/

namespace RHV6Fresh

open Real Filter Topology RHV3Lean

/-! ## 1. Forme paramétrique : même lecture au rang `n` -/

def SameReadingAt (β T : ℝ) (n : ℕ) : Prop := n ∉ mirrorStrip β T

theorem sameReadingAt_iff (β T : ℝ) (n : ℕ) :
    SameReadingAt β T n ↔ towerWord (1 - β) T n = towerWord β T n := not_not

theorem meetingCell_eq_towerWord (β T : ℝ) (I : PrimeGapInterval) :
    meetingCell β T I = towerWord β T (I.rank + 1) := rfl

theorem same_meetingCell_iff (β T : ℝ) (I : PrimeGapInterval) :
    meetingCell (1 - β) T I = meetingCell β T I ↔ SameReadingAt β T (I.rank + 1) :=
  (sameReadingAt_iff β T (I.rank + 1)).symm

/-! ## 2. Fenêtre de même lecture autour de la ligne (contre-modèle au niveau des Tours) -/

theorem floor_stable_of_continuous_not_int {f : ℝ → ℝ} {β : ℝ} (hc : ContinuousAt f β)
    (hni : Int.fract (f β) ≠ 0) : ∃ δ > 0, ∀ b, |b - β| < δ → ⌊f b⌋ = ⌊f β⌋ := by
  have h1 : (⌊f β⌋ : ℝ) < f β := by
    have h2 : 0 < Int.fract (f β) := lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hni)
    have h3 := Int.floor_add_fract (f β)
    linarith
  have h2 : f β < ⌊f β⌋ + 1 := Int.lt_floor_add_one _
  have hev : ∀ᶠ b in 𝓝 β, f b ∈ Set.Ioo (⌊f β⌋ : ℝ) (⌊f β⌋ + 1) := hc.eventually (Ioo_mem_nhds h1 h2)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun b hb => ?_⟩
  have hm := hball (y := b) (by rw [Real.dist_eq]; exact hb)
  rw [Int.floor_eq_iff]
  exact ⟨hm.1.le, hm.2⟩

theorem towerWord_stable_near {β T : ℝ} (hβ : 0 < β) (n : ℕ)
    (hni : cellFraction β T (fnPrimeAtRank n : ℝ) ≠ 0) :
    ∃ δ > 0, ∀ b, |b - β| < δ → towerWord b T n = towerWord β T n :=
  floor_stable_of_continuous_not_int (continuousAt_stagePosition_radial hβ T _) hni

theorem sameReading_window {T : ℝ} (S : Finset ℕ)
    (hS : ∀ n ∈ S, cellFraction (1 / 2) T (fnPrimeAtRank n : ℝ) ≠ 0) :
    ∃ δ > 0, ∀ β, |β - 1 / 2| < δ → ∀ n ∈ S, SameReadingAt β T n := by
  have hev : ∀ n ∈ S, ∀ᶠ b in 𝓝 (1 / 2 : ℝ), towerWord b T n = towerWord (1 / 2) T n := by
    intro n hn
    obtain ⟨δ, hδ, h⟩ := towerWord_stable_near (by norm_num : (0 : ℝ) < 1 / 2) n (hS n hn)
    rw [Metric.eventually_nhds_iff]
    exact ⟨δ, hδ, fun b hd => h b (by rwa [Real.dist_eq] at hd)⟩
  rw [← Filter.eventually_all_finset, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, h⟩ := hev
  refine ⟨δ, hδ, fun β hβ n hn => ?_⟩
  rw [sameReadingAt_iff]
  have h1 : towerWord β T n = towerWord (1 / 2) T n := h (y := β) (by rw [Real.dist_eq]; exact hβ) n hn
  have h2 : towerWord (1 - β) T n = towerWord (1 / 2) T n := by
    refine h (y := 1 - β) ?_ n hn
    rw [Real.dist_eq]
    have e : (1 - β) - 1 / 2 = -(β - 1 / 2) := by ring
    rw [e, abs_neg]
    exact hβ
  rw [h1, h2]

theorem exists_offLine_sameReading_on_finset {T : ℝ} (S : Finset ℕ)
    (hS : ∀ n ∈ S, cellFraction (1 / 2) T (fnPrimeAtRank n : ℝ) ≠ 0) :
    ∃ β, 0 < β ∧ β < 1 / 2 ∧ ∀ n ∈ S, SameReadingAt β T n := by
  obtain ⟨δ, hδ, h⟩ := sameReading_window S hS
  have h0 : 0 < min δ (1 / 2 : ℝ) := lt_min hδ (by norm_num)
  have hl := min_le_left δ (1 / 2 : ℝ)
  have hr := min_le_right δ (1 / 2 : ℝ)
  refine ⟨1 / 2 - min δ (1 / 2) / 2, by linarith, by linarith, ?_⟩
  apply h
  rw [abs_lt]
  constructor <;> linarith

/-! ## 3. Branche dégénérée : le premier exactement sur un contact de la ligne -/

theorem mem_mirrorStrip_of_prime_on_line_contact {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T)
    (hne : β ≠ 1 / 2) (n : ℕ) (h0 : cellFraction (1 / 2) T (fnPrimeAtRank n : ℝ) = 0) :
    n ∈ mirrorStrip β T := by
  have hk : stagePosition (1 / 2) T (fnPrimeAtRank n : ℝ) =
      (lastContactBefore (1 / 2) T (fnPrimeAtRank n : ℝ) : ℝ) := by
    have h := stagePosition_eq_last_add_fraction (1 / 2) T (fnPrimeAtRank n : ℝ)
    rw [h0, add_zero] at h
    exact h
  show towerWord (1 - β) T n ≠ towerWord β T n
  rcases lt_or_gt_of_ne hne with hlow | hhigh
  · have a := stagePosition_lt_of_radial_lt hT hβ hlow (fnPrimeAtRank n : ℝ)
    have b := stagePosition_lt_of_radial_lt hT (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith : (1 / 2 : ℝ) < 1 - β) (fnPrimeAtRank n : ℝ)
    rw [hk] at a b
    have a' : towerWord β T n < lastContactBefore (1 / 2) T (fnPrimeAtRank n : ℝ) := Int.floor_lt.mpr a
    have b' : lastContactBefore (1 / 2) T (fnPrimeAtRank n : ℝ) ≤ towerWord (1 - β) T n :=
      Int.le_floor.mpr b.le
    intro heq
    omega
  · have a := stagePosition_lt_of_radial_lt hT (by linarith : (0 : ℝ) < 1 - β)
      (by linarith : 1 - β < 1 / 2) (fnPrimeAtRank n : ℝ)
    have b := stagePosition_lt_of_radial_lt hT (by norm_num : (0 : ℝ) < 1 / 2) hhigh (fnPrimeAtRank n : ℝ)
    rw [hk] at a b
    have a' : towerWord (1 - β) T n < lastContactBefore (1 / 2) T (fnPrimeAtRank n : ℝ) :=
      Int.floor_lt.mpr a
    have b' : lastContactBefore (1 / 2) T (fnPrimeAtRank n : ℝ) ≤ towerWord β T n := Int.le_floor.mpr b.le
    intro heq
    omega

/-! ## 4. Classement exact de H-a au niveau des Tours -/

theorem sameReadingAt_forces_line_iff {T : ℝ} (hT : 0 < T) (n : ℕ) :
    (∀ β, 0 < β → β < 1 → SameReadingAt β T n → β = 1 / 2) ↔
      cellFraction (1 / 2) T (fnPrimeAtRank n : ℝ) = 0 := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨β, h0, h1, h2⟩ := exists_offLine_sameReading_on_finset (T := T) {n}
      (by intro m hm; rw [Finset.mem_singleton] at hm; rw [hm]; exact hne)
    have := h β h0 (by linarith) (h2 n (Finset.mem_singleton_self n))
    linarith
  · intro h0 β hβ hβ1 hs
    by_contra hne
    exact hs (mem_mirrorStrip_of_prime_on_line_contact hβ hβ1 hT hne n h0)

/-! ## 5. H-b sur toutes les rencontres à partir d'un rang : équivalente à la ligne -/

theorem sameReading_beyond_iff {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) (N : ℕ) :
    (∀ n, N ≤ n → SameReadingAt β T n) ↔ β = 1 / 2 := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨n, hn, hd⟩ := pair_words_differ_beyond hβ hβ1 hT hne N
    exact h n hn hd
  · intro h n _ hn
    rw [(mirrorStrip_eq_empty_iff hβ hβ1 hT).mpr h] at hn
    exact (Set.mem_empty_iff_false n).mp hn

/-! ## 6. Sur les zéros vrais -/

def SameReadingAtRankOnCarriers (n : ℕ) : Prop := ∀ z : TrueZero, n ∉ zeroStrip z

def SameReadingBeyondOnCarriers (N : ℕ) : Prop := ∀ z : TrueZero, ∀ n, N ≤ n → n ∉ zeroStrip z

def SameMeetingCellsOnCarriers : Prop := ∀ z : TrueZero, ∀ I : PrimeGapInterval,
  meetingCell (1 - rZeroRadialPosition z.1) (rZeroHeight z.1) I =
    meetingCell (rZeroRadialPosition z.1) (rZeroHeight z.1) I

theorem sameReadingAtRank_of_riemannHypothesis (hRH : RiemannHypothesis) (n : ℕ) :
    SameReadingAtRankOnCarriers n := by
  intro z
  rw [stripEmptyOnCarriers_iff_riemannHypothesis.mpr hRH z]
  exact Set.notMem_empty n

theorem sameReadingBeyond_iff_riemannHypothesis (N : ℕ) :
    SameReadingBeyondOnCarriers N ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply thm_riemannHypothesis_of_allUpperOnCriticalLine
    intro z
    exact (sameReading_beyond_iff (zero_radial_pos z) (zero_radial_lt_one z) (zero_height_pos z) N).mp (h z)
  · intro hRH z n _
    rw [stripEmptyOnCarriers_iff_riemannHypothesis.mpr hRH z]
    exact Set.notMem_empty n

theorem sameMeetingCells_iff_riemannHypothesis : SameMeetingCellsOnCarriers ↔ RiemannHypothesis := by
  rw [← sameReadingBeyond_iff_riemannHypothesis 1]
  constructor
  · intro h z n hn hmem
    have e : n - 1 + 1 = n := by omega
    have h' : towerWord (1 - rZeroRadialPosition z.1) (rZeroHeight z.1) (n - 1 + 1) =
        towerWord (rZeroRadialPosition z.1) (rZeroHeight z.1) (n - 1 + 1) := h z ⟨n - 1⟩
    rw [e] at h'
    exact hmem h'
  · intro h z I
    exact not_not.mp (h z (I.rank + 1) (by omega))

#print axioms same_meetingCell_iff
#print axioms towerWord_stable_near
#print axioms sameReading_window
#print axioms exists_offLine_sameReading_on_finset
#print axioms mem_mirrorStrip_of_prime_on_line_contact
#print axioms sameReadingAt_forces_line_iff
#print axioms sameReading_beyond_iff
#print axioms sameReadingAtRank_of_riemannHypothesis
#print axioms sameReadingBeyond_iff_riemannHypothesis
#print axioms sameMeetingCells_iff_riemannHypothesis

end RHV6Fresh
