/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PairMeetingImposition
import RHV6Fresh.Terminal.ContactsFromGapsInversion

/-!
# RHV6Fresh — Terminal/PairWordInversion : l'inversion d'E449 appliquée au mot du miroir (E453, §19.75, K3,
2026-11-08 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse, aucun axiome, aucun `sorry`)

Question K3 (§19.74) : E449 a compilé que le mot des écarts détermine la Tour ; la paire exige deux mots qui diffèrent
exactement sur la fenêtre de K2b. Que rend l'inversion d'E449 appliquée au mot du miroir ?

## 1. L'inversion du miroir (E449 L1, L3 appliqués à `(1−β, T)`)
* `mirror_tower_of_two_contacts` : deux contacts du miroir rendent `T` et `1−β` par la formule tangentielle ;
  `mirror_word_slope_tendsto` : `k*(p_n)/log p_n → T/π` ; `word_slope_bracket` : encadrement déterministe
  `|k/log x − T/π| ≤ (|φ|+π)/(π log x)` pour tout mot.
## 2. Unicité : `mirror_word_determines_mirror` — toute Tour ayant le mot du miroir est le miroir.
## 3. Le mot du miroir est FONCTION du mot de la Tour
* `pair_of_same_word`, `mirror_word_of_same_word` : deux Tours de même mot ont la même paire et des miroirs de même mot.
  La seconde donnée n'est pas une donnée nouvelle : les écarts la portent déjà par le mot de la Tour.
## 4. `pair_words_eq_iff` : les deux mots coïncident sur tous les premiers ⟺ `β = 1/2`.
## 5. `cellFraction_primes_small_and_near_one_from`, `pair_words_differ_beyond`, `pair_words_differ_beyond_iff` :
  hors ligne, les deux mots diffèrent au-delà de tout rang (cause : E449 L4, la fraction approche 0 et 1 au-delà de tout
  rang ; fenêtre de K2b de largeur `|δ|/π ∈ (0,1)`) ; et réciproquement.
## 6. Au paramètre d'un zéro vrai et de son miroir (E451) : `zero_pair_words_eq_iff`, `zero_pair_words_differ_beyond`.
## 7. L'arrivée est au plus à un demi (rectification de l'auteur, 2026-11-08, §19.76)
* La plage `β ∈ (0,1)` des sections 1–6 est plus large que l'objet de la route : le membre d'ENTRÉE d'une hauteur nouvelle
  vérifie `β ≤ 1/2` par l'ordre seul (`passage_entry_radial_le_half`, RaccordDetector, sans hypothèse), et le régime démarre
  à ON (`first_passage_no_shared_frequency`, MeetingPoint). Le cas `β > 1/2` n'est donc jamais une arrivée : c'est le miroir
  d'une arrivée basse. `low_pair_words_differ_beyond`, `low_pair_words_differ_beyond_iff` (sous un demi, `β < 1` superflu) ;
  `arrival_radial_le_half` ; `arrival_pair_words_differ_beyond_iff` : pour l'arrivée, mots distincts au-delà de tout rang ⟺
  `β < 1/2` ; `arrival_pair_words_dichotomy` : ou bien ligne et mots identiques partout, ou bien arrivée basse et mots
  distincts au-delà de tout rang. Aucun troisième cas.

Réponse de K3 (consignée d'avance en §19.75.2 et compilée ici) : l'inversion rend `(1−β, T)` exactement ; deux Tours
lisibles ; le mot du miroir n'exige aucune donnée nouvelle ; AUCUNE contradiction. Aucun taux de divergence n'est compilé.
-/
namespace RHV6Fresh

open Real Filter Topology RHV3Lean

/-! ## L1. L'inversion d'E449 appliquée au miroir -/

theorem mirror_tower_of_two_contacts {β T : ℝ} (hβ1 : β < 1) (hT : 0 < T) (k : ℤ) :
    T = Real.pi / Real.log (contactAt (1 - β) T (k + 1) / contactAt (1 - β) T k) ∧
      1 - β = T / Real.tan (T * Real.log (contactAt (1 - β) T k) - k * Real.pi) :=
  tower_of_two_contacts (by linarith) hT k

theorem mirror_word_slope_tendsto (β : ℝ) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => (lastContactBefore (1 - β) T (fnPrimeAtRank n : ℝ) : ℝ) / Real.log (fnPrimeAtRank n : ℝ))
      atTop (𝓝 (T / Real.pi)) :=
  word_slope_tendsto (1 - β) hT

theorem word_slope_bracket (β T : ℝ) {x : ℝ} (hx : 1 < x) :
    |(lastContactBefore β T x : ℝ) / Real.log x - T / Real.pi| ≤ (|towerPhase β T| + Real.pi) / (Real.pi * Real.log x) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hpi := Real.pi_pos
  have h := phase_eq_word_sub_fraction β T x
  have hf0 := cellFraction_nonneg β T x
  have hf1 := cellFraction_lt_one β T x
  have hk : (lastContactBefore β T x : ℝ) = (T * Real.log x - towerPhase β T) / Real.pi - cellFraction β T x := by
    field_simp; linarith
  have key : (lastContactBefore β T x : ℝ) / Real.log x - T / Real.pi
      = -(towerPhase β T + Real.pi * cellFraction β T x) / (Real.pi * Real.log x) := by
    rw [hk]; field_simp; ring
  rw [key, abs_div, abs_of_pos (mul_pos hpi hl), abs_neg]
  apply div_le_div_of_nonneg_right _ (mul_pos hpi hl).le
  calc |towerPhase β T + Real.pi * cellFraction β T x|
      ≤ |towerPhase β T| + |Real.pi * cellFraction β T x| := abs_add_le _ _
    _ ≤ |towerPhase β T| + Real.pi := by
        rw [abs_mul, abs_of_pos hpi, abs_of_nonneg hf0]
        nlinarith

/-! ## L2. Toute Tour ayant le mot du miroir est le miroir -/

theorem mirror_word_determines_mirror {β β' T T' : ℝ} (hβ1 : β < 1) (hβ' : 0 < β') (hT : 0 < T) (hT' : 0 < T')
    (hw : ∀ n : ℕ, lastContactBefore (1 - β) T (fnPrimeAtRank n : ℝ) = lastContactBefore β' T' (fnPrimeAtRank n : ℝ)) :
    T = T' ∧ 1 - β = β' :=
  tower_eq_of_same_word (by linarith) hβ' hT hT' hw

/-! ## L3. Le mot du miroir est fonction du mot de la Tour -/

theorem pair_of_same_word {β β' T T' : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (hT : 0 < T) (hT' : 0 < T')
    (hw : ∀ n : ℕ, lastContactBefore β T (fnPrimeAtRank n : ℝ) = lastContactBefore β' T' (fnPrimeAtRank n : ℝ)) :
    T = T' ∧ β = β' ∧ 1 - β = 1 - β' := by
  obtain ⟨h1, h2⟩ := tower_eq_of_same_word hβ hβ' hT hT' hw
  exact ⟨h1, h2, by rw [h2]⟩

theorem mirror_word_of_same_word {β β' T T' : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (hT : 0 < T) (hT' : 0 < T')
    (hw : ∀ n : ℕ, lastContactBefore β T (fnPrimeAtRank n : ℝ) = lastContactBefore β' T' (fnPrimeAtRank n : ℝ)) :
    ∀ n : ℕ, lastContactBefore (1 - β) T (fnPrimeAtRank n : ℝ) = lastContactBefore (1 - β') T' (fnPrimeAtRank n : ℝ) := by
  obtain ⟨h1, h2⟩ := tower_eq_of_same_word hβ hβ' hT hT' hw
  subst h1; subst h2
  intro n; rfl

/-! ## L4. Les deux mots coïncident sur tous les premiers ⟺ ligne -/

theorem pair_words_eq_iff {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) :
    (∀ n : ℕ, lastContactBefore (1 - β) T (fnPrimeAtRank n : ℝ) = lastContactBefore β T (fnPrimeAtRank n : ℝ)) ↔
      β = 1 / 2 := by
  constructor
  · intro hw
    have := (tower_eq_of_same_word (by linarith) hβ hT hT hw).2
    linarith
  · intro h
    subst h
    intro n
    rw [mirror_lastContactBefore, line_mirrorWordShift_eq_zero hT, add_zero]

/-! ## L5. Hors ligne, les deux mots diffèrent au-delà de tout rang -/

theorem cellFraction_primes_small_and_near_one_from (β : ℝ) {T : ℝ} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (N : ℕ) :
    ∃ n, N ≤ n ∧ cellFraction β T (fnPrimeAtRank (n + 1) : ℝ) < ε ∧ 1 - ε < cellFraction β T (fnPrimeAtRank n : ℝ) := by
  have hu : Tendsto (fun n : ℕ => stagePosition β T (fnPrimeAtRank (n + N) : ℝ)) atTop atTop :=
    (stagePosition_primes_tendsto_atTop β hT).comp (tendsto_add_atTop_nat N)
  have hstep : Tendsto (fun n : ℕ => stagePosition β T (fnPrimeAtRank (n + 1 + N) : ℝ) -
      stagePosition β T (fnPrimeAtRank (n + N) : ℝ)) atTop (𝓝 0) := by
    have := (stagePosition_primes_step_tendsto_zero β T).comp (tendsto_add_atTop_nat N)
    refine this.congr (fun n => ?_)
    simp only [Function.comp]
    rw [Nat.add_right_comm]
  obtain ⟨n, h1, h2⟩ := fract_small_and_near_one_of_steps hu hstep hε hε1
  refine ⟨n + N, by omega, ?_, h2⟩
  unfold cellFraction
  rw [Nat.add_right_comm]
  exact h1

theorem pair_words_differ_beyond {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) (hne : β ≠ 1 / 2) (N : ℕ) :
    ∃ n, N ≤ n ∧ lastContactBefore (1 - β) T (fnPrimeAtRank n : ℝ) ≠ lastContactBefore β T (fnPrimeAtRank n : ℝ) := by
  have hδ : mirrorPhaseShift β T ≠ 0 := fun h => hne ((mirrorPhaseShift_eq_zero_iff hβ hβ1 hT).mp h)
  have hpi := Real.pi_pos
  have hε : 0 < |mirrorPhaseShift β T| / Real.pi := div_pos (abs_pos.mpr hδ) hpi
  have hε1 : |mirrorPhaseShift β T| / Real.pi < 1 := by
    rw [div_lt_one hpi]; exact abs_mirrorPhaseShift_lt_pi β T
  obtain ⟨n, hn, h1, h2⟩ := cellFraction_primes_small_and_near_one_from β hT hε hε1 N
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · refine ⟨n + 1, by omega, ?_⟩
    rw [abs_of_neg hneg] at h1
    intro heq
    have := ((pair_same_word_iff β T _).mp heq).1
    rw [neg_div] at h1
    linarith
  · refine ⟨n, hn, ?_⟩
    rw [abs_of_pos hpos] at h2
    intro heq
    have := ((pair_same_word_iff β T _).mp heq).2
    linarith

theorem pair_words_differ_beyond_iff {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) :
    (∀ N : ℕ, ∃ n, N ≤ n ∧
      lastContactBefore (1 - β) T (fnPrimeAtRank n : ℝ) ≠ lastContactBefore β T (fnPrimeAtRank n : ℝ)) ↔ β ≠ 1 / 2 := by
  constructor
  · intro h hβ2
    obtain ⟨n, -, hn⟩ := h 0
    exact hn ((pair_words_eq_iff hβ hβ1 hT).mpr hβ2 n)
  · exact pair_words_differ_beyond hβ hβ1 hT

/-! ## L6. Au paramètre d'un zéro vrai et de son miroir (E451) -/

theorem zero_pair_words_eq_iff (z : TrueZero) :
    (∀ n : ℕ, lastContactBefore (rZeroRadialPosition (mirrorMember z).1) (rZeroHeight (mirrorMember z).1) (fnPrimeAtRank n : ℝ) =
        lastContactBefore (rZeroRadialPosition z.1) (rZeroHeight z.1) (fnPrimeAtRank n : ℝ)) ↔
      rZeroRadialPosition z.1 = 1 / 2 := by
  rw [mirrorMember_radial, mirrorMember_ordinate]
  exact pair_words_eq_iff (zero_radial_pos z) (zero_radial_lt_one z) (zero_height_pos z)

theorem zero_pair_words_differ_beyond (z : TrueZero) (hne : rZeroRadialPosition z.1 ≠ 1 / 2) (N : ℕ) :
    ∃ n, N ≤ n ∧
      lastContactBefore (rZeroRadialPosition (mirrorMember z).1) (rZeroHeight (mirrorMember z).1) (fnPrimeAtRank n : ℝ) ≠
        lastContactBefore (rZeroRadialPosition z.1) (rZeroHeight z.1) (fnPrimeAtRank n : ℝ) := by
  rw [mirrorMember_radial, mirrorMember_ordinate]
  exact pair_words_differ_beyond (zero_radial_pos z) (zero_radial_lt_one z) (zero_height_pos z) hne N

/-! ## L7. L'arrivée est au plus à un demi (§19.76) : la plage utile est `β ≤ 1/2` -/

theorem low_pair_words_differ_beyond {β T : ℝ} (hβ : 0 < β) (hlow : β < 1 / 2) (hT : 0 < T) (N : ℕ) :
    ∃ n, N ≤ n ∧ lastContactBefore (1 - β) T (fnPrimeAtRank n : ℝ) ≠ lastContactBefore β T (fnPrimeAtRank n : ℝ) :=
  pair_words_differ_beyond hβ (by linarith) hT (ne_of_lt hlow) N

theorem low_pair_words_differ_beyond_iff {β T : ℝ} (hβ : 0 < β) (hle : β ≤ 1 / 2) (hT : 0 < T) :
    (∀ N : ℕ, ∃ n, N ≤ n ∧
      lastContactBefore (1 - β) T (fnPrimeAtRank n : ℝ) ≠ lastContactBefore β T (fnPrimeAtRank n : ℝ)) ↔ β < 1 / 2 := by
  rw [pair_words_differ_beyond_iff hβ (by linarith) hT]
  exact ⟨fun h => lt_of_le_of_ne hle h, ne_of_lt⟩

/-- Le membre d'entrée d'une hauteur nouvelle est au plus à un demi : ordre seul (`passage_entry_radial_le_half`). -/
theorem arrival_radial_le_half (p : TZeroPassage) (l : TrueZero) (hl : l.1 = p.zLaterMember)
    (hT : rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember) :
    rZeroRadialPosition l.1 ≤ 1 / 2 := by
  rw [hl]; exact passage_entry_radial_le_half p hT

theorem arrival_pair_words_differ_beyond_iff (p : TZeroPassage) (l : TrueZero) (hl : l.1 = p.zLaterMember)
    (hT : rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember) :
    (∀ N : ℕ, ∃ n, N ≤ n ∧
      lastContactBefore (rZeroRadialPosition (mirrorMember l).1) (rZeroHeight (mirrorMember l).1) (fnPrimeAtRank n : ℝ) ≠
        lastContactBefore (rZeroRadialPosition l.1) (rZeroHeight l.1) (fnPrimeAtRank n : ℝ)) ↔
      rZeroRadialPosition l.1 < 1 / 2 := by
  have hle := arrival_radial_le_half p l hl hT
  constructor
  · intro h
    by_contra hge
    push Not at hge
    obtain ⟨n, -, hn⟩ := h 0
    exact hn ((zero_pair_words_eq_iff l).mpr (le_antisymm hle hge) n)
  · intro hlow N
    exact zero_pair_words_differ_beyond l (ne_of_lt hlow) N

/-- **Dichotomie de l'arrivée** : ligne et mots identiques partout, ou arrivée basse et mots distincts au-delà de tout
rang. Le cas `β > 1/2` n'existe pas pour une arrivée. -/
theorem arrival_pair_words_dichotomy (p : TZeroPassage) (l : TrueZero) (hl : l.1 = p.zLaterMember)
    (hT : rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember) :
    (rZeroRadialPosition l.1 = 1 / 2 ∧ ∀ n : ℕ,
      lastContactBefore (rZeroRadialPosition (mirrorMember l).1) (rZeroHeight (mirrorMember l).1) (fnPrimeAtRank n : ℝ) =
        lastContactBefore (rZeroRadialPosition l.1) (rZeroHeight l.1) (fnPrimeAtRank n : ℝ)) ∨
    (rZeroRadialPosition l.1 < 1 / 2 ∧ ∀ N : ℕ, ∃ n, N ≤ n ∧
      lastContactBefore (rZeroRadialPosition (mirrorMember l).1) (rZeroHeight (mirrorMember l).1) (fnPrimeAtRank n : ℝ) ≠
        lastContactBefore (rZeroRadialPosition l.1) (rZeroHeight l.1) (fnPrimeAtRank n : ℝ)) := by
  rcases lt_or_eq_of_le (arrival_radial_le_half p l hl hT) with hlow | heq
  · exact Or.inr ⟨hlow, (arrival_pair_words_differ_beyond_iff p l hl hT).mpr hlow⟩
  · exact Or.inl ⟨heq, (zero_pair_words_eq_iff l).mpr heq⟩

#print axioms mirror_tower_of_two_contacts
#print axioms mirror_word_slope_tendsto
#print axioms word_slope_bracket
#print axioms mirror_word_determines_mirror
#print axioms pair_of_same_word
#print axioms mirror_word_of_same_word
#print axioms pair_words_eq_iff
#print axioms cellFraction_primes_small_and_near_one_from
#print axioms pair_words_differ_beyond
#print axioms pair_words_differ_beyond_iff
#print axioms zero_pair_words_eq_iff
#print axioms zero_pair_words_differ_beyond
#print axioms low_pair_words_differ_beyond
#print axioms low_pair_words_differ_beyond_iff
#print axioms arrival_radial_le_half
#print axioms arrival_pair_words_differ_beyond_iff
#print axioms arrival_pair_words_dichotomy

end RHV6Fresh
