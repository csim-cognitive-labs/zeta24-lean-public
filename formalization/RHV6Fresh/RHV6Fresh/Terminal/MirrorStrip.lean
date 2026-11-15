/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CarrierSelection
import RHV6Fresh.Terminal.SameHeightContactShift
import RHV6Fresh.Terminal.ArrivalFiberHypotheses


/-!
# RHV6Fresh — Terminal/MirrorStrip : géométrie exacte de la bande miroir
(E458, plan Φ étape Φ2, §19.80, §19.86, §19.87, 2026-11-09 ; module isolé, NON importé par `RHV6Fresh.lean` ;
aucune hypothèse, aucun axiome, aucun `sorry`)

La bande d'une Tour `(β, T)` est l'ensemble des RANGS de premiers où le mot du miroir `(1 − β, T)` diffère du mot de la Tour.

* B0 `mirrorStrip_abs_eq_one`, `towerWord_le_mirror`, `mirrorStrip_word_succ` : sur la bande l'écart des deux mots vaut exactement un ;
  du côté bas, le mot du miroir vaut le mot de la Tour plus un.
* B1 `mirrorStrip_eq_empty_iff` : bande vide ⟺ ligne. B2 `mirrorStrip_infinite_iff` : bande infinie ⟺ hors ligne.
  B3 `mirrorStrip_empty_or_infinite`, `mirrorStrip_not_nonempty_finite` : jamais non vide et finie.
* B4 `mem_mirrorStrip_iff_between_contacts` : du côté bas, un rang est dans la bande si et seulement si son premier est dans
  l'intervalle, fermé à gauche et ouvert à droite, qui va du contact d'un indice du miroir au contact de MÊME indice de la Tour ;
  `mirror_contact_before_within_half_cell` : ces deux contacts ne sont jamais confondus (le miroir strictement avant), et leur
  rapport est strictement inférieur à une demi-cellule. L'énoncé place un premier ENTRE deux contacts ; il n'affirme jamais
  qu'un contact est un premier (§19.51).
* B5 `zeroStrip_eq_empty_of_fiberCount_lt_two`, `two_le_fiberCount_of_zeroStrip_nonempty` : seul point de contact entre le poids
  et la bande (audit E460) : poids de fibre sous deux ⟹ bande vide ; bande non vide ⟹ poids de fibre au moins deux.
* B6 `stripEmptyOnCarriers_iff_riemannHypothesis`, `stripFiniteOnCarriers_iff_riemannHypothesis` : reformulations, JAMAIS posées
  (la seconde est l'hypothèse H-c du plan, classée équivalente).

Portée : toute Tour hors ligne, porteuse ou non, a la même bande ; la géométrie de la bande ne porte pas la sélection des porteurs.
AUCUNE densité de la bande n'est affirmée : seule l'infinitude est compilée. Aucune contradiction n'est tirée ; aucune théorie
spectrale.
-/

namespace RHV6Fresh

open Real RHV3Lean

/-! ## 1. La bande -/

def mirrorStrip (β T : ℝ) : Set ℕ := {n | towerWord (1 - β) T n ≠ towerWord β T n}

def zeroStrip (z : TrueZero) : Set ℕ := mirrorStrip (rZeroRadialPosition z.1) (rZeroHeight z.1)

/-! ## 2. B0 : orientation -/

theorem mirrorStrip_abs_eq_one {β T : ℝ} {n : ℕ} (hn : n ∈ mirrorStrip β T) :
    |towerWord (1 - β) T n - towerWord β T n| = 1 := by
  have key : ∀ d : ℤ, |d| ≤ 1 → d ≠ 0 → |d| = 1 := by
    intro d hd h0
    obtain ⟨h1, h2⟩ := abs_le.mp hd
    have : d = 1 ∨ d = -1 := by omega
    rcases this with rfl | rfl <;> simp
  exact key _ (mirror_word_difference_le_one β T _) (sub_ne_zero.mpr hn)

theorem towerWord_le_mirror {β T : ℝ} (hβ : 0 < β) (hlow : β ≤ 1 / 2) (hT : 0 < T) (n : ℕ) :
    towerWord β T n ≤ towerWord (1 - β) T n := by
  unfold towerWord lastContactBefore
  apply Int.floor_le_floor
  rcases eq_or_lt_of_le hlow with h | h
  · have h' : 1 - β = β := by linarith
    rw [h']
  · exact (stagePosition_lt_of_radial_lt hT hβ (by linarith) _).le

theorem mirrorStrip_word_succ {β T : ℝ} (hβ : 0 < β) (hlow : β < 1 / 2) (hT : 0 < T) {n : ℕ}
    (hn : n ∈ mirrorStrip β T) : towerWord (1 - β) T n = towerWord β T n + 1 := by
  have h1 := towerWord_le_mirror hβ hlow.le hT n
  have h2 := mirrorStrip_abs_eq_one hn
  rw [abs_of_nonneg (sub_nonneg.mpr h1)] at h2
  omega

/-! ## 3. B1–B3 : vide ⟺ ligne ; infinie ⟺ hors ligne ; jamais non vide et finie -/

theorem mirrorStrip_eq_empty_iff {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) :
    mirrorStrip β T = ∅ ↔ β = 1 / 2 := by
  rw [← pair_words_eq_iff hβ hβ1 hT, Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h n; exact not_not.mp (h n)
  · intro h n hn; exact hn (h n)

theorem mirrorStrip_infinite_iff {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) :
    (mirrorStrip β T).Infinite ↔ β ≠ 1 / 2 := by
  constructor
  · intro hinf hβ2
    rw [(mirrorStrip_eq_empty_iff hβ hβ1 hT).mpr hβ2] at hinf
    exact hinf Set.finite_empty
  · intro hne
    rw [Set.infinite_iff_exists_gt]
    intro a
    obtain ⟨n, hn, hd⟩ := pair_words_differ_beyond hβ hβ1 hT hne (a + 1)
    exact ⟨n, hd, by omega⟩

theorem mirrorStrip_empty_or_infinite {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) :
    mirrorStrip β T = ∅ ∨ (mirrorStrip β T).Infinite := by
  by_cases h : β = 1 / 2
  · exact Or.inl ((mirrorStrip_eq_empty_iff hβ hβ1 hT).mpr h)
  · exact Or.inr ((mirrorStrip_infinite_iff hβ hβ1 hT).mpr h)

theorem mirrorStrip_not_nonempty_finite {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) :
    ¬ ((mirrorStrip β T).Nonempty ∧ (mirrorStrip β T).Finite) := by
  rintro ⟨hne, hfin⟩
  rcases mirrorStrip_empty_or_infinite hβ hβ1 hT with h | h
  · rw [h] at hne; exact Set.not_nonempty_empty hne
  · exact h hfin

/-! ## 4. B4 : un premier de bande est entre deux contacts de même indice -/

theorem windingContact_le_iff_stage {β T q : ℝ} (hT : 0 < T) (hq : 0 < q) (x : ℝ) :
    windingContact β T x ≤ q ↔ x ≤ stagePosition β T q := by
  unfold windingContact stagePosition
  rw [← Real.exp_log hq, Real.exp_le_exp, Real.exp_log hq, div_le_iff₀ hT, le_div_iff₀ Real.pi_pos]
  constructor <;> intro h <;> linarith

theorem mem_mirrorStrip_iff_between_contacts {β T : ℝ} (hβ : 0 < β) (hlow : β < 1 / 2) (hT : 0 < T) (n : ℕ) :
    n ∈ mirrorStrip β T ↔ ∃ k : ℤ, windingContact (1 - β) T k ≤ (fnPrimeAtRank n : ℝ) ∧
      (fnPrimeAtRank n : ℝ) < windingContact β T k := by
  have hq : (0 : ℝ) < (fnPrimeAtRank n : ℝ) := by linarith [one_lt_primeAtRank_real n]
  constructor
  · intro hn
    have hs := mirrorStrip_word_succ hβ hlow hT hn
    refine ⟨towerWord (1 - β) T n, ?_, ?_⟩
    · rw [windingContact_le_iff_stage hT hq]
      exact Int.floor_le _
    · rw [← not_le, windingContact_le_iff_stage hT hq, not_le, hs]
      push_cast
      exact Int.lt_floor_add_one _
  · rintro ⟨k, h1, h2⟩
    rw [windingContact_le_iff_stage hT hq] at h1
    rw [← not_le, windingContact_le_iff_stage hT hq, not_le] at h2
    have a : k ≤ towerWord (1 - β) T n := Int.le_floor.mpr h1
    have b : towerWord β T n < k := Int.floor_lt.mpr h2
    show towerWord (1 - β) T n ≠ towerWord β T n
    intro heq
    omega

theorem mirror_contact_before_within_half_cell {β T : ℝ} (hβ : 0 < β) (hlow : β < 1 / 2) (hT : 0 < T) (k : ℤ) :
    windingContact (1 - β) T k < windingContact β T k ∧
      windingContact β T k < Real.exp (Real.pi / (2 * T)) * windingContact (1 - β) T k :=
  ⟨windingContact_lt_of_radial_lt hβ (by linarith) hT,
    (same_height_shift_within_half_cell hβ (by linarith) hT k).2⟩

/-! ## 5. B5 : poids de fibre et bande -/

theorem zeroStrip_eq_empty_of_fiberCount_lt_two (z : TrueZero)
    (h : fiberCountWithMultiplicity (rZeroHeight z.1) < 2) : zeroStrip z = ∅ := by
  have h1 : ¬ rZeroRadialPosition z.1 < 1 / 2 := fun hlow => by
    have := two_le_fiberCount_of_low z hlow
    omega
  have h2 : ¬ rZeroRadialPosition (mirrorMember z).1 < 1 / 2 := fun hlow => by
    have := two_le_fiberCount_of_low (mirrorMember z) hlow
    rw [mirrorMember_ordinate] at this
    omega
  rw [mirrorMember_radial] at h2
  have hhalf : rZeroRadialPosition z.1 = 1 / 2 := by linarith [not_lt.mp h1, not_lt.mp h2]
  exact (mirrorStrip_eq_empty_iff (zero_radial_pos z) (zero_radial_lt_one z) (zero_height_pos z)).mpr hhalf

theorem two_le_fiberCount_of_zeroStrip_nonempty (z : TrueZero) (h : (zeroStrip z).Nonempty) :
    2 ≤ fiberCountWithMultiplicity (rZeroHeight z.1) := by
  by_contra hlt
  rw [zeroStrip_eq_empty_of_fiberCount_lt_two z (by omega)] at h
  exact Set.not_nonempty_empty h

/-! ## 6. B6 : reformulations (jamais posées) -/

def StripEmptyOnCarriers : Prop := ∀ z : TrueZero, zeroStrip z = ∅

def StripFiniteOnCarriers : Prop := ∀ z : TrueZero, (zeroStrip z).Finite

theorem zeroStrip_eq_empty_iff (z : TrueZero) : zeroStrip z = ∅ ↔ rZeroRadialPosition z.1 = 1 / 2 :=
  mirrorStrip_eq_empty_iff (zero_radial_pos z) (zero_radial_lt_one z) (zero_height_pos z)

theorem stripEmptyOnCarriers_iff_riemannHypothesis : StripEmptyOnCarriers ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply thm_riemannHypothesis_of_allUpperOnCriticalLine
    intro z
    exact (zeroStrip_eq_empty_iff z).mp (h z)
  · intro hRH z
    exact (zeroStrip_eq_empty_iff z).mpr (thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1)

theorem stripFiniteOnCarriers_iff_stripEmpty : StripFiniteOnCarriers ↔ StripEmptyOnCarriers := by
  constructor
  · intro h z
    rcases mirrorStrip_empty_or_infinite (zero_radial_pos z) (zero_radial_lt_one z) (zero_height_pos z) with he | hi
    · exact he
    · exact absurd (h z) hi
  · intro h z
    rw [h z]
    exact Set.finite_empty

theorem stripFiniteOnCarriers_iff_riemannHypothesis : StripFiniteOnCarriers ↔ RiemannHypothesis :=
  stripFiniteOnCarriers_iff_stripEmpty.trans stripEmptyOnCarriers_iff_riemannHypothesis

#print axioms mirrorStrip_word_succ
#print axioms mirrorStrip_eq_empty_iff
#print axioms mirrorStrip_infinite_iff
#print axioms mirrorStrip_not_nonempty_finite
#print axioms mem_mirrorStrip_iff_between_contacts
#print axioms mirror_contact_before_within_half_cell
#print axioms zeroStrip_eq_empty_of_fiberCount_lt_two
#print axioms two_le_fiberCount_of_zeroStrip_nonempty
#print axioms stripEmptyOnCarriers_iff_riemannHypothesis
#print axioms stripFiniteOnCarriers_iff_riemannHypothesis

end RHV6Fresh
