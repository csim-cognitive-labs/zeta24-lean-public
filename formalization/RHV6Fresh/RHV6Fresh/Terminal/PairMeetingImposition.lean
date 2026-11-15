/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PairBreakOfZero

/-!
# RHV6Fresh — Terminal/PairMeetingImposition : ce que la rencontre exacte impose aux deux termes de même poids au
même premier (E452, §19.74, K2b, 2026-11-08 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse,
aucun axiome, aucun `sorry`)

Paire `(β, T)`, `(1−β, T)` au premier partagé `x`. E450 a compilé « deux mots décalés d'au plus une cellule » ; ce
module écrit la relation EXACTE entre les deux mots, puis ce qui en découle pour les deux valeurs au même premier.
Deux termes seulement ; aucune somme de Tours ; aucune comparaison avec `log q`, `ψ` ou une cellule.

## 1. Le décalage de mot du miroir
* `mirrorWordShift β T x := ⌊f_β(x) + mirrorPhaseShift β T / π⌋` ; `mirror_lastContactBefore` : `k_{1−β} = k_β + s` ;
  `abs_mirrorWordShift_le_one`, `mirrorWordShift_trichotomy` : `s ∈ {−1, 0, 1}`.
## 2. La fenêtre de même mot, fixée par `β`
* `pair_same_word_iff` : même mot ⟺ `−δ/π ≤ f_β(x) < 1 − δ/π` ; `line_mirrorWordShift_eq_zero` : sur la ligne, `s = 0`.
## 3. Les signes des deux valeurs
* `pair_value_tower_eq`, `pair_value_mirror_eq` : `v = σ|v|`, `v* = σ(−1)^s|v*|`, `σ = (−1)^{k_β}` ;
  `pair_value_product` : `v·v* = (−1)^s |v||v*|` ; `pair_same_sign_iff` : même signe ⟺ `s = 0`.
## 4. La valeur de la paire au premier partagé
* `pair_value_sum_abs` : `|v + v*| = | |v| + (−1)^s |v*| |` ; `pair_value_sum_of_same_word` (somme des amplitudes),
  `pair_value_sum_of_shifted_word` (différence) ; `pair_value_sum_ge` : `|v| − |v*| ≤ |v + v*|`.
## 5. Confrontée à la séparation (E450 L6) : la paire ne se compense jamais elle-même
* `pair_value_no_cancellation` (`β > 1/2`) : `∀ᶠ x, |v|/2 < |v + v*|` ; `pair_meeting_no_cancellation` : à toute
  rencontre au-delà d'un rang.
## 6. La ligne : `line_pair_value_sum` : `v + v* = 2v`.
## 7. Au paramètre d'un zéro vrai (E451)
* `zero_pair_value_no_cancellation` ; `zero_weighted_pair_value_abs` : `|m v + m* v*| = m|v + v*|` ;
  `zero_weighted_pair_value_ge` : le poids commun `m ≥ 1` ne fait qu'amplifier.

Portée : la FORME de la paire à tout premier partagé tardif (un membre domine, signe relatif dicté par la fenêtre) ;
aucune contradiction n'est tirée (§19.74.2).
-/

namespace RHV6Fresh

open Real Filter Topology RHV3Lean


noncomputable def mirrorWordShift (β T x : ℝ) : ℤ :=
  ⌊cellFraction β T x + mirrorPhaseShift β T / Real.pi⌋

theorem mirror_stagePosition_eq (β T x : ℝ) :
    stagePosition (1 - β) T x =
      ((lastContactBefore β T x : ℤ) : ℝ) + (cellFraction β T x + mirrorPhaseShift β T / Real.pi) := by
  have h := mirror_stagePosition_difference β T x
  unfold lastContactBefore cellFraction
  rw [← add_assoc, Int.floor_add_fract]
  rw [neg_div] at h
  linarith

theorem mirror_lastContactBefore (β T x : ℝ) :
    lastContactBefore (1 - β) T x = lastContactBefore β T x + mirrorWordShift β T x := by
  change ⌊stagePosition (1 - β) T x⌋ = lastContactBefore β T x + ⌊cellFraction β T x + mirrorPhaseShift β T / Real.pi⌋
  rw [mirror_stagePosition_eq, Int.floor_intCast_add]

theorem abs_mirrorWordShift_le_one (β T x : ℝ) : |mirrorWordShift β T x| ≤ 1 := by
  have h := mirror_word_difference_le_one β T x
  rw [mirror_lastContactBefore] at h
  simpa using h

theorem mirrorWordShift_trichotomy (β T x : ℝ) :
    mirrorWordShift β T x = -1 ∨ mirrorWordShift β T x = 0 ∨ mirrorWordShift β T x = 1 := by
  have h := abs_mirrorWordShift_le_one β T x
  rw [abs_le] at h
  omega

theorem pair_same_word_iff (β T x : ℝ) :
    lastContactBefore (1 - β) T x = lastContactBefore β T x ↔
      -(mirrorPhaseShift β T / Real.pi) ≤ cellFraction β T x ∧
        cellFraction β T x < 1 - mirrorPhaseShift β T / Real.pi := by
  rw [mirror_lastContactBefore]
  constructor
  · intro h
    have hs : mirrorWordShift β T x = 0 := by omega
    unfold mirrorWordShift at hs
    have := Int.floor_eq_zero_iff.mp hs
    rw [Set.mem_Ico] at this
    constructor <;> linarith [this.1, this.2]
  · intro h
    have hs : mirrorWordShift β T x = 0 := by
      unfold mirrorWordShift
      rw [Int.floor_eq_zero_iff, Set.mem_Ico]
      constructor <;> linarith [h.1, h.2]
    omega

theorem line_mirrorWordShift_eq_zero {T : ℝ} (hT : 0 < T) (x : ℝ) :
    mirrorWordShift (1 / 2) T x = 0 := by
  unfold mirrorWordShift
  rw [(mirrorPhaseShift_eq_zero_iff (by norm_num) (by norm_num) hT).mpr rfl, zero_div, add_zero,
    Int.floor_eq_zero_iff, Set.mem_Ico]
  exact ⟨cellFraction_nonneg _ _ _, cellFraction_lt_one _ _ _⟩

theorem pair_value_tower_eq {β T : ℝ} (hβ : 0 < β) (x : ℝ) :
    contactRealValue β T (lastContactBefore β T x) =
      (-1 : ℝ) ^ lastContactBefore β T x * |contactRealValue β T (lastContactBefore β T x)| := by
  rw [abs_contactRealValue hβ]
  conv_lhs => rw [contactRealValue]
  ring

theorem pair_value_mirror_eq {β T : ℝ} (hβ1 : β < 1) (x : ℝ) :
    contactRealValue (1 - β) T (lastContactBefore (1 - β) T x) =
      (-1 : ℝ) ^ lastContactBefore β T x * (-1 : ℝ) ^ mirrorWordShift β T x *
        |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| := by
  have hk : (-1 : ℝ) ^ lastContactBefore (1 - β) T x =
      (-1 : ℝ) ^ lastContactBefore β T x * (-1 : ℝ) ^ mirrorWordShift β T x := by
    rw [mirror_lastContactBefore, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  rw [abs_contactRealValue (by linarith : 0 < 1 - β)]
  conv_lhs => rw [contactRealValue, hk]
  ring

theorem abs_sign_sum (k s : ℤ) (a b : ℝ) :
    |(-1 : ℝ) ^ k * a + (-1 : ℝ) ^ k * (-1 : ℝ) ^ s * b| = |a + (-1 : ℝ) ^ s * b| := by
  rw [show (-1 : ℝ) ^ k * a + (-1 : ℝ) ^ k * (-1 : ℝ) ^ s * b =
      (-1 : ℝ) ^ k * (a + (-1 : ℝ) ^ s * b) by ring,
    abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]

theorem pair_value_sum_abs {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (x : ℝ) :
    |contactRealValue β T (lastContactBefore β T x) +
        contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| =
      abs (|contactRealValue β T (lastContactBefore β T x)| +
        (-1 : ℝ) ^ mirrorWordShift β T x *
          |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)|) := by
  conv_lhs => rw [pair_value_tower_eq hβ x, pair_value_mirror_eq hβ1 x]
  exact abs_sign_sum _ _ _ _

theorem pair_value_sum_of_same_word {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (x : ℝ)
    (h : mirrorWordShift β T x = 0) :
    |contactRealValue β T (lastContactBefore β T x) +
        contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| =
      |contactRealValue β T (lastContactBefore β T x)| +
        |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| := by
  rw [pair_value_sum_abs hβ hβ1 x, h, zpow_zero, one_mul]
  exact abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))

theorem pair_value_sum_of_shifted_word {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (x : ℝ)
    (h : mirrorWordShift β T x ≠ 0) :
    |contactRealValue β T (lastContactBefore β T x) +
        contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| =
      abs (|contactRealValue β T (lastContactBefore β T x)| -
        |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)|) := by
  rw [pair_value_sum_abs hβ hβ1 x]
  have hodd : Odd (mirrorWordShift β T x) := by
    rcases mirrorWordShift_trichotomy β T x with h1 | h1 | h1
    · rw [h1]; exact ⟨-1, by norm_num⟩
    · exact absurd h1 h
    · rw [h1]; exact odd_one
  rw [hodd.neg_one_zpow]
  congr 1
  ring

theorem pair_value_product {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (x : ℝ) :
    contactRealValue β T (lastContactBefore β T x) *
        contactRealValue (1 - β) T (lastContactBefore (1 - β) T x) =
      (-1 : ℝ) ^ mirrorWordShift β T x *
        (|contactRealValue β T (lastContactBefore β T x)| *
          |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)|) := by
  conv_lhs => rw [pair_value_tower_eq hβ x, pair_value_mirror_eq hβ1 x]
  have hk : (-1 : ℝ) ^ lastContactBefore β T x * (-1 : ℝ) ^ lastContactBefore β T x = 1 := by
    rw [← mul_zpow]; norm_num
  linear_combination (|contactRealValue β T (lastContactBefore β T x)| *
    (-1 : ℝ) ^ mirrorWordShift β T x *
    |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)|) * hk

theorem neg_one_zpow_neg_one' : (-1 : ℝ) ^ (-1 : ℤ) = -1 := by
  rw [zpow_neg_one, inv_neg_one]

theorem pair_same_sign_iff {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (x : ℝ) :
    0 < contactRealValue β T (lastContactBefore β T x) *
        contactRealValue (1 - β) T (lastContactBefore (1 - β) T x) ↔
      mirrorWordShift β T x = 0 := by
  rw [pair_value_product hβ hβ1 x]
  have ha : 0 < |contactRealValue β T (lastContactBefore β T x)| :=
    abs_pos.mpr (contactRealValue_ne_zero hβ _)
  have hb : 0 < |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| :=
    abs_pos.mpr (contactRealValue_ne_zero (by linarith) _)
  have hab := mul_pos ha hb
  rcases mirrorWordShift_trichotomy β T x with h | h | h <;> rw [h]
  · rw [neg_one_zpow_neg_one']
    constructor
    · intro h0; linarith
    · intro h0; exact absurd h0 (by norm_num)
  · rw [zpow_zero, one_mul]
    exact ⟨fun _ => rfl, fun _ => hab⟩
  · rw [zpow_one]
    constructor
    · intro h0; linarith
    · intro h0; exact absurd h0 (by norm_num)

theorem pair_value_sum_ge {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (x : ℝ) :
    |contactRealValue β T (lastContactBefore β T x)| -
        |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| ≤
      |contactRealValue β T (lastContactBefore β T x) +
        contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| := by
  rw [pair_value_sum_abs hβ hβ1 x]
  have hb := abs_nonneg (contactRealValue (1 - β) T (lastContactBefore (1 - β) T x))
  rcases mirrorWordShift_trichotomy β T x with h | h | h <;> rw [h]
  · rw [neg_one_zpow_neg_one']
    have := le_abs_self (|contactRealValue β T (lastContactBefore β T x)| +
      -1 * |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)|)
    linarith
  · rw [zpow_zero]
    have := le_abs_self (|contactRealValue β T (lastContactBefore β T x)| +
      1 * |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)|)
    linarith
  · rw [zpow_one]
    have := le_abs_self (|contactRealValue β T (lastContactBefore β T x)| +
      -1 * |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)|)
    linarith

theorem pair_value_no_cancellation {β T : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) (hT : 0 < T) :
    ∀ᶠ x : ℝ in atTop,
      |contactRealValue β T (lastContactBefore β T x)| / 2 <
        |contactRealValue β T (lastContactBefore β T x) +
          contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| := by
  have hβ0 : 0 < β := by linarith
  filter_upwards [pair_break_ratio_unbounded hβ hβ1 hT 2] with x hx
  have hb : 0 < |contactRealValue (1 - β) T (lastContactBefore (1 - β) T x)| :=
    abs_pos.mpr (contactRealValue_ne_zero (by linarith) _)
  rw [lt_div_iff₀ hb] at hx
  have := pair_value_sum_ge (T := T) hβ0 hβ1 x
  linarith

theorem pair_meeting_no_cancellation {β T : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) (hT : 0 < T) :
    ∃ N : ℝ, ∀ I : PrimeGapInterval, N ≤ I.upper →
      |contactRealValue β T (meetingCell β T I)| / 2 <
        |contactRealValue β T (meetingCell β T I) +
          contactRealValue (1 - β) T (meetingCell (1 - β) T I)| := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (pair_value_no_cancellation hβ hβ1 hT)
  exact ⟨N, fun I hI => hN _ hI⟩

theorem line_pair_value_sum (T x : ℝ) :
    contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x) +
        contactRealValue (1 - 1 / 2) T (lastContactBefore (1 - 1 / 2) T x) =
      2 * contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x) := by
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  ring

theorem zero_pair_value_no_cancellation (z : TrueZero) (hβ : 1 / 2 < rZeroRadialPosition z.1) :
    ∀ᶠ x : ℝ in atTop,
      |contactRealValue (rZeroRadialPosition z.1) (rZeroHeight z.1)
          (lastContactBefore (rZeroRadialPosition z.1) (rZeroHeight z.1) x)| / 2 <
        |contactRealValue (rZeroRadialPosition z.1) (rZeroHeight z.1)
            (lastContactBefore (rZeroRadialPosition z.1) (rZeroHeight z.1) x) +
          contactRealValue (rZeroRadialPosition (mirrorMember z).1) (rZeroHeight (mirrorMember z).1)
            (lastContactBefore (rZeroRadialPosition (mirrorMember z).1)
              (rZeroHeight (mirrorMember z).1) x)| := by
  rw [mirrorMember_radial, mirrorMember_ordinate]
  exact pair_value_no_cancellation hβ (zero_radial_lt_one z) (zero_height_pos z)

theorem zero_weighted_pair_value_abs (z : TrueZero) (x : ℝ) :
    |(zeroMult (zeroPoint z) : ℝ) *
        contactRealValue (rZeroRadialPosition z.1) (rZeroHeight z.1)
          (lastContactBefore (rZeroRadialPosition z.1) (rZeroHeight z.1) x) +
      (zeroMult (zeroPoint (mirrorMember z)) : ℝ) *
        contactRealValue (rZeroRadialPosition (mirrorMember z).1) (rZeroHeight (mirrorMember z).1)
          (lastContactBefore (rZeroRadialPosition (mirrorMember z).1)
            (rZeroHeight (mirrorMember z).1) x)| =
      (zeroMult (zeroPoint z) : ℝ) *
        |contactRealValue (rZeroRadialPosition z.1) (rZeroHeight z.1)
            (lastContactBefore (rZeroRadialPosition z.1) (rZeroHeight z.1) x) +
          contactRealValue (rZeroRadialPosition (mirrorMember z).1) (rZeroHeight (mirrorMember z).1)
            (lastContactBefore (rZeroRadialPosition (mirrorMember z).1)
              (rZeroHeight (mirrorMember z).1) x)| := by
  rw [zeroMult_mirrorMember, ← mul_add, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]

theorem zero_weighted_pair_value_ge (z : TrueZero) (x : ℝ) :
    |contactRealValue (rZeroRadialPosition z.1) (rZeroHeight z.1)
          (lastContactBefore (rZeroRadialPosition z.1) (rZeroHeight z.1) x) +
        contactRealValue (rZeroRadialPosition (mirrorMember z).1) (rZeroHeight (mirrorMember z).1)
          (lastContactBefore (rZeroRadialPosition (mirrorMember z).1)
            (rZeroHeight (mirrorMember z).1) x)| ≤
      |(zeroMult (zeroPoint z) : ℝ) *
          contactRealValue (rZeroRadialPosition z.1) (rZeroHeight z.1)
            (lastContactBefore (rZeroRadialPosition z.1) (rZeroHeight z.1) x) +
        (zeroMult (zeroPoint (mirrorMember z)) : ℝ) *
          contactRealValue (rZeroRadialPosition (mirrorMember z).1) (rZeroHeight (mirrorMember z).1)
            (lastContactBefore (rZeroRadialPosition (mirrorMember z).1)
              (rZeroHeight (mirrorMember z).1) x)| := by
  rw [zero_weighted_pair_value_abs]
  have h1 : (1 : ℝ) ≤ zeroMult (zeroPoint z) := by exact_mod_cast one_le_zeroMult_zeroPoint z
  exact le_mul_of_one_le_left (abs_nonneg _) h1

#print axioms mirror_lastContactBefore
#print axioms pair_same_word_iff
#print axioms pair_same_sign_iff
#print axioms pair_value_sum_abs
#print axioms pair_value_sum_ge
#print axioms pair_value_no_cancellation
#print axioms pair_meeting_no_cancellation
#print axioms zero_pair_value_no_cancellation
#print axioms zero_weighted_pair_value_ge

end RHV6Fresh
