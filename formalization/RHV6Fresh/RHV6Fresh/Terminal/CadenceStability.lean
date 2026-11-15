/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GrammarDrift
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# La cadence est une stabilité (module isolé, non importé par la chaîne)

Demande de l'auteur (2026-10-29) : la cadence imposée par la grammaire aux rencontres est une
stabilité ; l'écrire en Lean. Trois faits compilés la constituent :

1. **Loi affine de l'état.** Aux rencontres, le logarithme de l'amplitude relative d'un membre est
   une fonction affine du logarithme du premier suivant, de pente la position radiale moins un demi
   (`log_relativeAmplitude_meeting`). La suite des amplitudes relatives aux rencontres est constante
   si et seulement si le membre est sur la ligne (`meeting_sequence_const_iff_onLine`) ; sous la
   ligne elle est strictement décroissante à toute rencontre, au-dessus strictement croissante
   (`meeting_sequence_strictAnti_of_low`, `meeting_sequence_strictMono_of_high`) : jamais de pause,
   jamais de retour.
2. **La cadence ne s'arrête jamais.** Les changements d'état entre rencontres consécutives se
   produisent au-delà de tout rang (`cadence_never_stops`, par le théorème de Dirichlet modulo six,
   Mathlib) : la transition obligatoire entre deux alternances obligées se répète sans fin.
3. **Chaque paire de changements consécutifs paie un minimum fixe.** Deux changements d'état
   consécutifs, quels que soient les maintiens entre eux, avancent d'au moins six
   (`two_changes_advance_ge_six`, par l'alternance à travers les maintiens), donc un membre sous la
   ligne perd entre eux au moins le facteur grammatical, strictement sous un
   (`cadence_drift_low_le`), et un membre au-dessus gagne au moins l'inverse
   (`cadence_drift_high_ge`).

La stabilité, en un théorème (`off_line_cadence_stability`) : pour un membre sous la ligne, la suite
de ses amplitudes relatives aux rencontres décroît strictement, les changements d'état ne cessent
jamais, et chaque paire de changements consécutifs la fait baisser d'au moins le facteur grammatical.
Sur la ligne, la même cadence laisse l'amplitude relative invariante : c'est le seul régime stable
sous la cadence, et c'est le régime ON.

Aucun axiome, aucun `sorry`.
-/

namespace RHV6Fresh

open Complex RHV3Lean

/-! ## 1. Loi affine et monotonie de la suite aux rencontres -/

theorem meetingPoint_strictMono {n m : ℕ} (h : n < m) : meetingPoint ⟨n⟩ < meetingPoint ⟨m⟩ := by
  unfold meetingPoint PrimeGapInterval.upper
  exact_mod_cast thm_primeAtRank_strictMono (show n + 1 < m + 1 by omega)

/-- **Loi affine de l'état aux rencontres** : logarithme de l'amplitude relative = logarithme du
poids + (position − un demi) × logarithme du premier suivant. -/
theorem log_relativeAmplitude_meeting (w : TrueZero) (n : ℕ) :
    Real.log (relativeAmplitude w (meetingPoint ⟨n⟩)) =
      Real.log ((zetaZeroMultiplicity (zeroPoint w) : ℝ) / (‖zeroPoint w‖ * ‖zeroPoint w + 1‖)) +
        (rZeroRadialPosition w.1 - 1 / 2) * Real.log (meetingPoint ⟨n⟩) := by
  have hx := meetingPoint_pos ⟨n⟩
  rw [relativeAmplitude_eq w hx, Real.log_mul
    (div_pos (memberMultiplicity_pos w) (memberDenominator_pos w)).ne'
    (Real.rpow_pos_of_pos hx _).ne', Real.log_rpow hx]

/-- **Suite constante aux rencontres si et seulement si sur la ligne.** -/
theorem meeting_sequence_const_iff_onLine (w : TrueZero) :
    (∀ n : ℕ, relativeAmplitude w (meetingPoint ⟨n + 1⟩) = relativeAmplitude w (meetingPoint ⟨n⟩)) ↔
      rZeroRadialPosition w.1 = 1 / 2 := by
  have hpos : ∀ n : ℕ, 0 < relativeAmplitude w (meetingPoint ⟨n⟩) := fun n => by
    rw [relativeAmplitude_eq w (meetingPoint_pos _)]
    exact mul_pos (div_pos (memberMultiplicity_pos w) (memberDenominator_pos w))
      (Real.rpow_pos_of_pos (meetingPoint_pos _) _)
  constructor
  · intro h
    rw [← meeting_drift_eq_one_iff w 0, div_eq_one_iff_eq (hpos 0).ne']
    exact h 0
  · intro h n
    have := (meeting_drift_eq_one_iff w n).mpr h
    rwa [div_eq_one_iff_eq (hpos n).ne'] at this

/-- **Sous la ligne, la suite aux rencontres décroît strictement**, à toute rencontre. -/
theorem meeting_sequence_strictAnti_of_low (w : TrueZero) (hlow : rZeroRadialPosition w.1 < 1 / 2) :
    StrictAnti (fun n : ℕ => relativeAmplitude w (meetingPoint ⟨n⟩)) := fun n m h =>
  relativeAmplitude_strictAnti_of_low w hlow (meetingPoint_pos ⟨n⟩) (meetingPoint_strictMono h)

/-- **Au-dessus de la ligne, la suite aux rencontres croît strictement**, à toute rencontre. -/
theorem meeting_sequence_strictMono_of_high (w : TrueZero) (hhigh : 1 / 2 < rZeroRadialPosition w.1) :
    StrictMono (fun n : ℕ => relativeAmplitude w (meetingPoint ⟨n⟩)) := fun n m h =>
  relativeAmplitude_strictMono_of_high w hhigh (meetingPoint_pos ⟨n⟩) (meetingPoint_strictMono h)

/-! ## 2. La cadence ne s'arrête jamais (Dirichlet modulo six) -/

/-- Toute rencontre de rang au moins deux dépasse trois, et le bon état modulo six s'ensuit. -/
theorem primeAtRank_goodMod6 {n : ℕ} (hn : 2 ≤ n) : GoodMod6 (fnPrimeAtRank n) :=
  prime_goodMod6 _ (thm_primeAtRank_isPrime n) (primeAtRank_gt_three hn)

/-- Sans changement d'état entre les rangs `n` et `m`, l'état est le même. -/
theorem state_const_of_maintains {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m)
    (h : ∀ k, n ≤ k → k < m → gapClass6 (fnPrimeAtRank k) (fnPrimeAtRank (k + 1)) = 0) :
    state6 (fnPrimeAtRank n) = state6 (fnPrimeAtRank m) := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    have hk := h m hm (by omega)
    rw [ih (fun k hk1 hk2 => h k hk1 (by omega))]
    exact (gapClass6_eq_zero_iff (primeAtRank_goodMod6 (by omega)) (primeAtRank_goodMod6 (by omega))
      (thm_primeAtRank_strictMono (show m < m + 1 by omega)).le).mp hk

/-- Tout premier est une rencontre : il a un rang. -/
theorem exists_rank_of_prime {q : ℕ} (hq : q.Prime) : ∃ r : ℕ, fnPrimeAtRank r = q :=
  ⟨Nat.count Nat.Prime q, Nat.nth_count hq⟩

/-- Un premier d'état opposé existe au-delà de tout seuil (Dirichlet modulo six, Mathlib). -/
theorem exists_prime_gt_of_state (b : Bool) (N : ℕ) :
    ∃ q : ℕ, N < q ∧ q.Prime ∧ state6 q = b := by
  cases b with
  | true =>
    obtain ⟨q, hq, hqp, hmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := 6) (a := 1) isUnit_one N
    refine ⟨q, hq, hqp, ?_⟩
    have h1 : ((q : ℕ) : ZMod 6) = ((1 : ℕ) : ZMod 6) := by rw [hmod]; simp
    have := (ZMod.natCast_eq_natCast_iff' q 1 6).mp h1
    unfold state6
    simp [this]
  | false =>
    have hu : IsUnit (5 : ZMod 6) := ⟨⟨5, 5, by decide, by decide⟩, rfl⟩
    obtain ⟨q, hq, hqp, hmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := 6) hu N
    refine ⟨q, hq, hqp, ?_⟩
    have h5 : ((q : ℕ) : ZMod 6) = ((5 : ℕ) : ZMod 6) := by rw [hmod]; simp
    have := (ZMod.natCast_eq_natCast_iff' q 5 6).mp h5
    unfold state6
    simp [this]

/-- **La cadence ne s'arrête jamais** : au-delà de tout rang, un changement d'état entre deux
rencontres consécutives. -/
theorem cadence_never_stops (n₀ : ℕ) :
    ∃ n : ℕ, n₀ ≤ n ∧ gapClass6 (fnPrimeAtRank n) (fnPrimeAtRank (n + 1)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set N := max n₀ 2 with hN
  have hN2 : 2 ≤ N := le_max_right _ _
  obtain ⟨q, hq, hqp, hqs⟩ := exists_prime_gt_of_state (!state6 (fnPrimeAtRank N)) (fnPrimeAtRank N)
  obtain ⟨r, hr⟩ := exists_rank_of_prime hqp
  have hNr : N ≤ r := by
    by_contra h
    have := thm_primeAtRank_strictMono (show r < N by omega)
    omega
  have hconst := state_const_of_maintains hN2 hNr
    (fun k hk _ => hcon k (le_trans (le_max_left _ _) hk))
  rw [hr] at hconst
  rw [← hconst] at hqs
  cases state6 (fnPrimeAtRank N) <;> simp at hqs

/-! ## 3. Deux changements consécutifs, à travers les maintiens, avancent d'au moins six -/

/-- Alternance à travers les maintiens : deux changements séparés par des maintiens avancent
ensemble d'au moins six (leurs classes sont opposées, deux et quatre). -/
theorem two_changes_sum_ge_six {p q r s : ℕ} (hp : GoodMod6 p) (hq : GoodMod6 q) (hr : GoodMod6 r)
    (hs : GoodMod6 s) (hpq : p ≤ q) (hrs : r ≤ s) (hqr : state6 q = state6 r)
    (h1 : gapClass6 p q ≠ 0) (h2 : gapClass6 r s ≠ 0) : 6 ≤ (q - p) + (s - r) := by
  unfold GoodMod6 at hp hq hr hs
  unfold gapClass6 at h1 h2
  unfold state6 at hqr
  simp only [decide_eq_decide] at hqr
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rcases hr with hr | hr <;>
    rcases hs with hs | hs <;> omega

/-- **Deux changements d'état consécutifs** (ranks `n < m`, maintiens entre eux) : la rencontre
suivant le second dépasse la rencontre précédant le premier d'au moins six. -/
theorem two_changes_advance_ge_six {n m : ℕ} (hn : 2 ≤ n) (hnm : n < m)
    (h1 : gapClass6 (fnPrimeAtRank n) (fnPrimeAtRank (n + 1)) ≠ 0)
    (h2 : gapClass6 (fnPrimeAtRank m) (fnPrimeAtRank (m + 1)) ≠ 0)
    (hmid : ∀ k, n < k → k < m → gapClass6 (fnPrimeAtRank k) (fnPrimeAtRank (k + 1)) = 0) :
    fnPrimeAtRank n + 6 ≤ fnPrimeAtRank (m + 1) := by
  have hstate : state6 (fnPrimeAtRank (n + 1)) = state6 (fnPrimeAtRank m) :=
    state_const_of_maintains (by omega) (by omega) (fun k hk1 hk2 => hmid k (by omega) hk2)
  have hsum := two_changes_sum_ge_six (primeAtRank_goodMod6 hn) (primeAtRank_goodMod6 (by omega))
    (primeAtRank_goodMod6 (by omega)) (primeAtRank_goodMod6 (by omega))
    (thm_primeAtRank_strictMono (show n < n + 1 by omega)).le
    (thm_primeAtRank_strictMono (show m < m + 1 by omega)).le hstate h1 h2
  have hmono : fnPrimeAtRank (n + 1) ≤ fnPrimeAtRank m :=
    (StrictMono.monotone thm_primeAtRank_strictMono) (show n + 1 ≤ m by omega)
  have h01 := (thm_primeAtRank_strictMono (show n < n + 1 by omega)).le
  have h23 := (thm_primeAtRank_strictMono (show m < m + 1 by omega)).le
  omega

/-- Puissance d'exposant non positif : antitone en la base. -/
theorem rpow_antitone_of_nonpos {x y z : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) :
    y ^ z ≤ x ^ z := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  calc y ^ z = (y⁻¹) ^ (-z) := by rw [Real.inv_rpow hy.le, ← Real.rpow_neg hy.le, neg_neg]
    _ ≤ (x⁻¹) ^ (-z) := Real.rpow_le_rpow (by positivity) (inv_anti₀ hx hxy) (by linarith)
    _ = x ^ z := by rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, neg_neg]

/-- **Sous la ligne, chaque paire de changements consécutifs fait perdre au moins le facteur
grammatical** : de la rencontre précédant le premier changement (rang `n`, rencontre `⟨n − 1⟩`
écrite `⟨n'⟩` avec `n = n' + 1`) à la rencontre du second (`⟨m⟩`). -/
theorem cadence_drift_low_le (w : TrueZero) (hlow : rZeroRadialPosition w.1 ≤ 1 / 2) {n' m : ℕ}
    (hn : 2 ≤ n' + 1) (hnm : n' + 1 < m)
    (h1 : gapClass6 (fnPrimeAtRank (n' + 1)) (fnPrimeAtRank (n' + 2)) ≠ 0)
    (h2 : gapClass6 (fnPrimeAtRank m) (fnPrimeAtRank (m + 1)) ≠ 0)
    (hmid : ∀ k, n' + 1 < k → k < m → gapClass6 (fnPrimeAtRank k) (fnPrimeAtRank (k + 1)) = 0) :
    relativeAmplitude w (meetingPoint ⟨m⟩) ≤
      (1 + 6 / (fnPrimeAtRank (n' + 1) : ℝ)) ^ (rZeroRadialPosition w.1 - 1 / 2) *
        relativeAmplitude w (meetingPoint ⟨n'⟩) := by
  have hpos : 0 < relativeAmplitude w (meetingPoint ⟨n'⟩) := by
    rw [relativeAmplitude_eq w (meetingPoint_pos _)]
    exact mul_pos (div_pos (memberMultiplicity_pos w) (memberDenominator_pos w))
      (Real.rpow_pos_of_pos (meetingPoint_pos _) _)
  have hd := relativeAmplitude_ratio w (meetingPoint_pos ⟨n'⟩) (meetingPoint_pos ⟨m⟩)
  rw [div_eq_iff hpos.ne'] at hd
  rw [hd]
  refine mul_le_mul_of_nonneg_right ?_ hpos.le
  have hadv := two_changes_advance_ge_six hn hnm h1 h2 hmid
  have hp0 : (0 : ℝ) < fnPrimeAtRank (n' + 1) := by
    exact_mod_cast (lt_trans (by norm_num) (primeAtRank_gt_three hn))
  have hbase : 1 + 6 / (fnPrimeAtRank (n' + 1) : ℝ) ≤ meetingPoint ⟨m⟩ / meetingPoint ⟨n'⟩ := by
    change 1 + 6 / (fnPrimeAtRank (n' + 1) : ℝ) ≤
      (fnPrimeAtRank (m + 1) : ℝ) / (fnPrimeAtRank (n' + 1) : ℝ)
    rw [le_div_iff₀ hp0, add_mul, div_mul_cancel₀ _ hp0.ne', one_mul]
    exact_mod_cast hadv
  exact rpow_antitone_of_nonpos (by positivity) hbase (by linarith)

/-- **Au-dessus de la ligne, chaque paire de changements consécutifs fait gagner au moins l'inverse
du facteur grammatical.** -/
theorem cadence_drift_high_ge (w : TrueZero) (hhigh : 1 / 2 ≤ rZeroRadialPosition w.1) {n' m : ℕ}
    (hn : 2 ≤ n' + 1) (hnm : n' + 1 < m)
    (h1 : gapClass6 (fnPrimeAtRank (n' + 1)) (fnPrimeAtRank (n' + 2)) ≠ 0)
    (h2 : gapClass6 (fnPrimeAtRank m) (fnPrimeAtRank (m + 1)) ≠ 0)
    (hmid : ∀ k, n' + 1 < k → k < m → gapClass6 (fnPrimeAtRank k) (fnPrimeAtRank (k + 1)) = 0) :
    (1 + 6 / (fnPrimeAtRank (n' + 1) : ℝ)) ^ (rZeroRadialPosition w.1 - 1 / 2) *
        relativeAmplitude w (meetingPoint ⟨n'⟩) ≤
      relativeAmplitude w (meetingPoint ⟨m⟩) := by
  have hpos : 0 < relativeAmplitude w (meetingPoint ⟨n'⟩) := by
    rw [relativeAmplitude_eq w (meetingPoint_pos _)]
    exact mul_pos (div_pos (memberMultiplicity_pos w) (memberDenominator_pos w))
      (Real.rpow_pos_of_pos (meetingPoint_pos _) _)
  have hd := relativeAmplitude_ratio w (meetingPoint_pos ⟨n'⟩) (meetingPoint_pos ⟨m⟩)
  rw [div_eq_iff hpos.ne'] at hd
  rw [hd]
  refine mul_le_mul_of_nonneg_right ?_ hpos.le
  have hadv := two_changes_advance_ge_six hn hnm h1 h2 hmid
  have hp0 : (0 : ℝ) < fnPrimeAtRank (n' + 1) := by
    exact_mod_cast (lt_trans (by norm_num) (primeAtRank_gt_three hn))
  have hbase : 1 + 6 / (fnPrimeAtRank (n' + 1) : ℝ) ≤ meetingPoint ⟨m⟩ / meetingPoint ⟨n'⟩ := by
    change 1 + 6 / (fnPrimeAtRank (n' + 1) : ℝ) ≤
      (fnPrimeAtRank (m + 1) : ℝ) / (fnPrimeAtRank (n' + 1) : ℝ)
    rw [le_div_iff₀ hp0, add_mul, div_mul_cancel₀ _ hp0.ne', one_mul]
    exact_mod_cast hadv
  exact Real.rpow_le_rpow (by positivity) hbase (by linarith)

/-! ## 4. La stabilité, en un théorème -/

/-- **La cadence est une stabilité.** Pour un membre sous la ligne : (i) la suite de ses amplitudes
relatives aux rencontres décroît strictement ; (ii) les changements d'état ne cessent jamais ;
(iii) chaque paire de changements consécutifs la fait baisser d'au moins le facteur grammatical,
strictement sous un. -/
theorem off_line_cadence_stability (w : TrueZero) (hlow : rZeroRadialPosition w.1 < 1 / 2) :
    StrictAnti (fun n : ℕ => relativeAmplitude w (meetingPoint ⟨n⟩)) ∧
    (∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧ gapClass6 (fnPrimeAtRank n) (fnPrimeAtRank (n + 1)) ≠ 0) ∧
    (∀ {n' m : ℕ}, 2 ≤ n' + 1 → n' + 1 < m →
      gapClass6 (fnPrimeAtRank (n' + 1)) (fnPrimeAtRank (n' + 2)) ≠ 0 →
      gapClass6 (fnPrimeAtRank m) (fnPrimeAtRank (m + 1)) ≠ 0 →
      (∀ k, n' + 1 < k → k < m → gapClass6 (fnPrimeAtRank k) (fnPrimeAtRank (k + 1)) = 0) →
      relativeAmplitude w (meetingPoint ⟨m⟩) ≤
        (1 + 6 / (fnPrimeAtRank (n' + 1) : ℝ)) ^ (rZeroRadialPosition w.1 - 1 / 2) *
          relativeAmplitude w (meetingPoint ⟨n'⟩) ∧
      (1 + 6 / (fnPrimeAtRank (n' + 1) : ℝ)) ^ (rZeroRadialPosition w.1 - 1 / 2) < 1) :=
  ⟨meeting_sequence_strictAnti_of_low w hlow, cadence_never_stops,
    fun hn hnm h1 h2 hmid => ⟨cadence_drift_low_le w hlow.le hn hnm h1 h2 hmid,
      grammar_factor_lt_one w hlow _⟩⟩

/-- **Sur la ligne, la cadence laisse l'état invariant** : c'est le régime stable. -/
theorem on_line_invariant_under_cadence (w : TrueZero) (hon : rZeroRadialPosition w.1 = 1 / 2) :
    ∀ n m : ℕ, relativeAmplitude w (meetingPoint ⟨n⟩) = relativeAmplitude w (meetingPoint ⟨m⟩) :=
  fun n m => (constantRelativeAmplitude_iff_onLine w).mpr hon ⟨n⟩ ⟨m⟩

end RHV6Fresh
