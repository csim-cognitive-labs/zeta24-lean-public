/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GrammarDwellDecomposition
import RHV6Fresh.Terminal.GrammarWeightedG4
import RHV6Fresh.Terminal.FirstGainPremise
import RHV6Fresh.Terminal.GrammarKinematics
import RHV6Fresh.Terminal.ReadingArithmetic
import RHV6Fresh.Terminal.LocalPrimeGapSynchronization

/-!
# Compositions vérifiées pour le modèle de contraintes (2026-10-26)

Les états, rangs et poids sont identiques dans chaque composition. Aucun résultat
ne suppose une stabilité ON globale ni la conclusion terminale. Ces lemmes relient
des contraintes ; ils ne constituent pas encore la contradiction terminale.
-/

namespace RHV6Fresh.ConstraintCorrelation

open RHV3Lean

/-- États premiers de la même fenêtre, avant toute lecture géométrique. -/
noncomputable def primeStates (a : ℕ) (i : ℕ) : Bool :=
  state6 (fnPrimeAtRank (a + i))

/-- Poids G4 sur cette même fenêtre, dont l'extrémité est fixée par le rang. -/
noncomputable def primeMass (a n : ℕ) (i : ℕ) : ℝ :=
  AstraGrammarG4.massWeight (fnPrimeAtRank (a + n)) (fnPrimeAtRank (a + i))

/-- Composition des deux stabilités : le défaut séjour/caractère est exactement
le canal orienté, borné par la variation des MÊMES poids. -/
theorem dwell_character_variation (n : ℕ) (s : ℕ → Bool) (w : ℕ → ℝ) :
    |(G11 n s w - G55 n s w) -
      ∑ i ∈ Finset.range n, (if s i then (1 : ℝ) else -1) * w i| ≤
    (|w 0| + |w (n - 1)| +
      ∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i|) / 2 := by
  rw [← weighted_character_channel, weighted_dwell_balance,
    sub_sub_cancel_left, abs_neg]
  exact weighted_orientation_abs_le n s w

/-- G4 instancié sur les vrais premiers et les quatre canaux de transition.
L'ordre des premiers décharge les hypothèses de monotonie du théorème abstrait. -/
theorem prime_orientation_mass_bound (a n : ℕ) (hn : 1 ≤ n) :
    |G15 n (primeStates a) (primeMass a n) -
      G51 n (primeStates a) (primeMass a n)| ≤
    (fnPrimeAtRank (a + n) : ℝ) * Real.log (fnPrimeAtRank (a + n)) := by
  rw [weighted_orientation_eq_abel]
  apply AstraGrammarG4.weighted_orientation_log_mul_sub_bound hn
    (fun i => if primeStates a i then (1 : ℝ) else -1)
    (by intro i; split <;> norm_num)
    (fun i => (fnPrimeAtRank (a + i) : ℝ))
  · intro i _
    exact_mod_cast (thm_primeAtRank_isPrime (a + i)).one_lt.le
  · intro i hi
    exact_mod_cast thm_primeAtRank_strictMono.monotone (Nat.add_le_add_left hi.le a)
  · intro i _
    exact_mod_cast thm_primeAtRank_strictMono (by omega : a + i < a + (i + 1))

/-- Les séjours et le caractère ne sont pas deux budgets indépendants : leur
différence est contrôlée par G4, sur la fenêtre première fixée. -/
theorem prime_dwell_character_mass_bound (a n : ℕ) (hn : 1 ≤ n) :
    |(G11 n (primeStates a) (primeMass a n) -
      G55 n (primeStates a) (primeMass a n)) -
      ∑ i ∈ Finset.range n,
        (if primeStates a i then (1 : ℝ) else -1) * primeMass a n i| ≤
    (fnPrimeAtRank (a + n) : ℝ) * Real.log (fnPrimeAtRank (a + n)) := by
  rw [← weighted_character_channel, weighted_dwell_balance,
    sub_sub_cancel_left, abs_neg]
  exact prime_orientation_mass_bound a n hn

/-- Le même rang authentique relie magnitude/classe, registre de passage et
déplacement radial. Aucune part du registre n'est supprimée. -/
theorem passage_magnitude_radial_ledger (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    let e : TrueZero := ⟨p.zEarlierMember, hE⟩
    let l : TrueZero := ⟨p.zLaterMember, hL⟩
    let r := nZeroSourceIndex e.1
    occurrencePosition l - occurrencePosition e =
      heightShift e l + rZeroHeight e.1 *
        Real.log (1 + (6 * (gapMagnitude r : ℝ) + (eventClass r : ℝ)) /
          (fnPrimeAtRank r : ℝ)) +
      (rZeroHeight e.1 * Real.log (radialFactor e) -
        rZeroHeight l.1 * Real.log (radialFactor l)) := by
  dsimp only
  rw [passage_ledger_radial _ _
    (expectedMinimumPrime_eq_laterOccurrence p hE hL).symm,
    primeGapLogRatio_eq_log_one_add]

/-- Le certificat d'écart déplace la cellule de l'occurrence vers une cellule
ultérieure. Il ne permet pas de les identifier dans une contradiction. -/
theorem occurrence_expected_cells_separated (z : TrueZero)
    (hgap : Real.pi ≤ rZeroHeight z.1 *
      Real.log ((expectedMinimumPrime z : ℝ) / (occurrence z : ℝ))) :
    pivotCoordinate z (occurrence z) < pivotCoordinate z (expectedMinimumPrime z) := by
  exact coordinate_lt_of_gap_ge_pi z
    (by exact_mod_cast (occurrence_prime z).pos)
    (by exact_mod_cast (expectedMinimumPrime_prime z).pos) hgap

/-- La séparation géométrique et la synchronisation spectrale portent ici sur
le MÊME rang premier. La conclusion préserve la somme infinie entière. -/
theorem cell_separation_with_exact_synchronization (z : TrueZero)
    (hgap : Real.pi ≤ rZeroHeight z.1 *
      Real.log ((expectedMinimumPrime z : ℝ) / (occurrence z : ℝ))) :
    pivotCoordinate z (occurrence z) < pivotCoordinate z (expectedMinimumPrime z) ∧
    localArithmeticTarget ⟨nZeroSourceIndex z.1⟩ =
      ∑' ρ : ExplicitIndex, smoothedLocalContribution ρ ⟨nZeroSourceIndex z.1⟩ :=
  ⟨occurrence_expected_cells_separated z hgap, localSynchronization _⟩

/-- Le transport des états grammaticaux vers une chaîne utilise son théorème
de rang : il ne réindexe pas librement les premiers. -/
theorem chain_states_match {m : ℕ} (c : ZeroChain m) (j : ℕ) (hj : j ≤ m) :
    primeStates (nZeroSourceIndex (c.member 0).1) j =
      state6 (occurrence (c.member j)) := by
  unfold primeStates
  rw [c.occurrence_eq j hj]

/-- Même contrôle de variation appliqué aux contributions lissées d'un vrai
zéro, sur les mêmes écarts que les états premiers. Aucune borne uniforme
de variation n'est introduite. -/
theorem spectral_dwell_character_variation (z : TrueZero) (a n : ℕ) :
    let s := primeStates a
    let w := fun i => (smoothedLocalContribution (memberIndex z) ⟨a + i⟩).re
    |(G11 n s w - G55 n s w) -
      ∑ i ∈ Finset.range n, (if s i then (1 : ℝ) else -1) * w i| ≤
      (|w 0| + |w (n - 1)| +
        ∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i|) / 2 :=
  dwell_character_variation n (primeStates a) _

/-! ## Raccord géométrique strict du pivot

Le pivot authentique est `⌈x⌉ - 1`, donc sa borne supérieure est strictement
en dessous de la cellule complète suivante. Cette stricte inégalité reste vraie
au cas frontière `x ∈ ℤ` : le contact supérieur vaut alors exactement `q`,
mais `q < q * exp (π/T)`. -/

theorem pivot_upper_contact_lt_exp_width (z : TrueZero) {q : ℝ} (hq : 0 < q) :
    (pivotPair z q).lastRayContact <
      q * Real.exp (Real.pi / rZeroHeight z.1) := by
  rw [pivotPair_lastRayContact]
  have hT : 0 < rZeroHeight z.1 := z.2
  have hπ : 0 < Real.pi := Real.pi_pos
  have hceil : (⌈towerPosition z q⌉ : ℝ) < towerPosition z q + 1 :=
    Int.ceil_lt_add_one _
  have hres :
      ((pivotCoordinate z q + 1 : ℤ) : ℝ) < towerPosition z q + 1 := by
    unfold pivotCoordinate
    push_cast
    simpa using hceil
  have hres' :
      (((pivotCoordinate z q + 1 : ℤ) : ℝ) - 1) <
        (rZeroHeight z.1 * Real.log q - (towerMotionOf z).phase) / Real.pi := by
    unfold towerPosition at hres
    linarith
  have hres'' :
      (((pivotCoordinate z q + 1 : ℤ) : ℝ) - 1) * Real.pi <
        rZeroHeight z.1 * Real.log q - (towerMotionOf z).phase := by
    exact (lt_div_iff₀ Real.pi_pos).mp hres'
  have hlog :
      ((towerMotionOf z).phase + ((pivotCoordinate z q + 1 : ℤ) : ℝ) * Real.pi) /
          rZeroHeight z.1 <
        Real.log q + Real.pi / rZeroHeight z.1 := by
    apply (div_lt_iff₀ hT).2
    calc
      (towerMotionOf z).phase + ((pivotCoordinate z q + 1 : ℤ) : ℝ) * Real.pi <
          rZeroHeight z.1 * Real.log q + Real.pi := by
        nlinarith [hres'']
      _ = (Real.log q + Real.pi / rZeroHeight z.1) * rZeroHeight z.1 := by
        field_simp
  calc
    Real.exp (((towerMotionOf z).phase + ((pivotCoordinate z q + 1 : ℤ) : ℝ) * Real.pi) /
        rZeroHeight z.1) < Real.exp (Real.log q + Real.pi / rZeroHeight z.1) :=
      Real.exp_lt_exp.mpr hlog
    _ = q * Real.exp (Real.pi / rZeroHeight z.1) := by
      rw [Real.exp_add, Real.exp_log hq]

theorem pivot_upper_below_expected_of_exp_margin (z : TrueZero)
    {s p : ℝ} (hs : 0 < s) (hmargin : s * Real.exp (Real.pi / rZeroHeight z.1) ≤ p)
    : (pivotPair z s).lastRayContact < p := by
  have hstrict := pivot_upper_contact_lt_exp_width z hs
  exact lt_of_lt_of_le hstrict hmargin

/-! La borne est lue sur la cellule du même ancrage `s`, sans introduire un
transport tacite vers la cellule de `p`. -/

/-- Borne grossière de largeur, conservée pour compatibilité. Malgré son nom
historique, ce résultat ne calcule pas la phase résiduelle. -/
theorem pivot_phase_residual_threshold (z : TrueZero) {s p : ℝ}
    (hs : 0 < s) (hp : 0 < p)
    (hcell : p ≤ (pivotPair z s).lastRayContact) :
    Real.log (p / s) ≤ Real.pi / rZeroHeight z.1 := by
  have hupper := pivot_upper_contact_lt_exp_width z hs
  have hpos : 0 < (pivotPair z s).lastRayContact :=
    contactPlusAt_positive z (pivotCoordinate z s)
  have hratio : p / s ≤ Real.exp (Real.pi / rZeroHeight z.1) := by
    apply le_of_lt
    calc
      p / s ≤ (pivotPair z s).lastRayContact / s :=
        (div_le_div_of_nonneg_right hcell hs.le)
      _ < (s * Real.exp (Real.pi / rZeroHeight z.1)) / s := by
        exact div_lt_div_of_pos_right hupper hs
      _ = Real.exp (Real.pi / rZeroHeight z.1) := by field_simp
  have hratio' : 0 < p / s := by positivity
  have hlogmono := Real.strictMonoOn_log.monotoneOn
    (show p / s ∈ Set.Ioi (0 : ℝ) from hratio')
    (show Real.exp (Real.pi / rZeroHeight z.1) ∈ Set.Ioi (0 : ℝ) from Real.exp_pos _)
    hratio
  simpa [Real.log_exp] using hlogmono

/-- Distance logarithmique exacte jusqu'au contact supérieur sélectionné.
La position entière donne zéro ; la largeur entière n'est jamais atteinte. -/
noncomputable def pivotResidual (z : TrueZero) (s : ℝ) : ℝ :=
  ((⌈towerPosition z s⌉ : ℝ) - towerPosition z s) *
    (Real.pi / rZeroHeight z.1)

theorem pivot_log_contact_ratio (z : TrueZero) {s : ℝ} (hs : 0 < s) :
    Real.log ((pivotPair z s).lastRayContact / s) = pivotResidual z s := by
  have hpos : 0 < (pivotPair z s).lastRayContact := contactPlusAt_positive z _
  rw [Real.log_div (ne_of_gt hpos) (ne_of_gt hs),
    pivotPair_lastRayContact, Real.log_exp]
  unfold pivotResidual pivotCoordinate towerPosition
  push_cast
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  field_simp [hT, Real.pi_ne_zero]
  ring

/-- Lecture du même événement sur la même cellule : seuil exact, dans les
deux sens. Ce théorème ne produit pas l'obligation de lecture. -/
theorem pivot_reading_iff_residual (z : TrueZero) {s p : ℝ}
    (hs : 0 < s) (hp : 0 < p) :
    p ≤ (pivotPair z s).lastRayContact ↔
      Real.log (p / s) ≤ pivotResidual z s := by
  have hpos : 0 < (pivotPair z s).lastRayContact := contactPlusAt_positive z _
  rw [← pivot_log_contact_ratio z hs]
  rw [Real.log_le_log_iff (div_pos hp hs) (div_pos hpos hs)]
  exact (div_le_div_iff_of_pos_right hs).symm

/-- Un certificat strict sur la phase résiduelle exclut effectivement la
lecture, sans changer l'ancrage, le membre ou l'événement. -/
theorem pivot_reading_excluded_of_residual_gap (z : TrueZero) {s p : ℝ}
    (hs : 0 < s) (hp : 0 < p)
    (hgap : pivotResidual z s < Real.log (p / s)) :
    ¬ p ≤ (pivotPair z s).lastRayContact := by
  intro hread
  exact (not_le_of_gt hgap) ((pivot_reading_iff_residual z hs hp).mp hread)

theorem pivotResidual_bounds (z : TrueZero) (s : ℝ) :
    0 ≤ pivotResidual z s ∧ pivotResidual z s < Real.pi / rZeroHeight z.1 := by
  have hw : 0 < Real.pi / rZeroHeight z.1 := div_pos Real.pi_pos z.2
  unfold pivotResidual
  constructor
  · exact mul_nonneg (sub_nonneg.mpr (Int.le_ceil _)) hw.le
  · have hd : (⌈towerPosition z s⌉ : ℝ) - towerPosition z s < 1 := by
      linarith [Int.ceil_lt_add_one (towerPosition z s)]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hd hw

/-- Raccord exact avec le plancher de Gemini, y compris la frontière. -/
theorem pivot_gemini_boundary (z : TrueZero) (s : ℝ) :
    (towerPosition z s ∈ Set.range (Int.cast : ℤ → ℝ) →
      pivotCoordinate z s = ⌊towerPosition z s⌋ - 1 ∧ pivotResidual z s = 0) ∧
    (towerPosition z s ∉ Set.range (Int.cast : ℤ → ℝ) →
      pivotCoordinate z s = ⌊towerPosition z s⌋) := by
  constructor
  · rintro ⟨k, hk⟩
    simp [pivotCoordinate, pivotResidual, ← hk]
  · intro h
    unfold pivotCoordinate
    rw [(Int.ceil_eq_floor_add_one_iff_notMem _).mpr h]
    omega

/-- Raccord de l'exclusion au véritable passage : l'événement exclu est
l'occurrence suivante, par l'égalité prouvée du minimum attendu. -/
theorem passage_reading_excluded_of_residual_gap (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember)
    (hgap : pivotResidual ⟨p.zEarlierMember, hE⟩ (occurrence ⟨p.zEarlierMember, hE⟩) <
      Real.log ((expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) /
        (occurrence ⟨p.zEarlierMember, hE⟩ : ℝ))) :
    ¬ (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) ≤
      (pivotPair ⟨p.zEarlierMember, hE⟩ (occurrence ⟨p.zEarlierMember, hE⟩)).lastRayContact := by
  rw [← expectedMinimumPrime_eq_laterOccurrence p hE hL]
  exact pivot_reading_excluded_of_residual_gap _
    (by exact_mod_cast (occurrence_prime ⟨p.zEarlierMember, hE⟩).pos)
    (by exact_mod_cast (expectedMinimumPrime_prime ⟨p.zEarlierMember, hE⟩).pos) hgap

/-- Les classes et magnitudes du rang authentique alimentent le seuil exact.
La comparaison stricte reste une obligation : la décomposition de l'écart
seule ne la démontre pas. -/
theorem expected_reading_excluded_of_magnitude_gap (z : TrueZero)
    (hgap : pivotResidual z (occurrence z) <
      Real.log (1 + (6 * (gapMagnitude (nZeroSourceIndex z.1) : ℝ) +
        (eventClass (nZeroSourceIndex z.1) : ℝ)) /
        (fnPrimeAtRank (nZeroSourceIndex z.1) : ℝ))) :
    ¬ (expectedMinimumPrime z : ℝ) ≤ (pivotPair z (occurrence z)).lastRayContact := by
  apply pivot_reading_excluded_of_residual_gap z
    (by exact_mod_cast (occurrence_prime z).pos)
    (by exact_mod_cast (expectedMinimumPrime_prime z).pos)
  have heq : Real.log ((expectedMinimumPrime z : ℝ) / (occurrence z : ℝ)) =
      rPrimeGapLogRatio (nZeroSourceIndex z.1) := by
    rw [occurrence_eq_canonicalAnchor]
    rfl
  rw [heq, primeGapLogRatio_eq_log_one_add]
  exact hgap

#print axioms pivot_upper_contact_lt_exp_width
#print axioms pivot_upper_below_expected_of_exp_margin
#print axioms pivot_phase_residual_threshold
#print axioms pivot_log_contact_ratio
#print axioms pivot_reading_iff_residual
#print axioms pivot_reading_excluded_of_residual_gap
#print axioms pivotResidual_bounds
#print axioms pivot_gemini_boundary
#print axioms passage_reading_excluded_of_residual_gap
#print axioms expected_reading_excluded_of_magnitude_gap

#print axioms dwell_character_variation
#print axioms prime_orientation_mass_bound
#print axioms prime_dwell_character_mass_bound
#print axioms passage_magnitude_radial_ledger
#print axioms occurrence_expected_cells_separated
#print axioms cell_separation_with_exact_synchronization
#print axioms chain_states_match
#print axioms spectral_dwell_character_variation

end RHV6Fresh.ConstraintCorrelation
