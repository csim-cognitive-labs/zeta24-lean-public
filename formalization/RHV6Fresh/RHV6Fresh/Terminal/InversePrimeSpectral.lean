/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CountingFieldArchitecture
import RHV6Fresh.Terminal.CanonicalEnumeration

/-!
# Démarche inverse : des impulsions premières au signal normalisé (E334 ; auteur, 2026-10-18)

Ordre imposé par l'auteur : premiers ⟶ impulsions de comptage ⟶ signal collectif ⟶ décomposition spectrale ⟶ fréquences,
amplitudes, contacts, `(β, T)`. Ce module écrit les objets arithmétiques et la normalisation EXACTE ; il ne contient aucun zéro
dans les énoncés du §1–§3.

* §1 Impulsions. Le comptage à gauche `J₋(t) = Σ_{n<t} Λ(n)/log n` (égal à `J₀` hors des entiers, ensemble négligeable) a pour
  dérivée distributionnelle la mesure atomique `Σ_n w(n) δ_n` : pour toute fonction test `φ` de classe `C¹` sur `[a, b]`,
  nulle aux bords, `∫_a^b J₋ φ' = −Σ_{a<n<b} w(n) φ(n)` (`counting_distributional_derivative`). Les impulsions ne sont jamais
  remplacées par la dérivée ordinaire, nulle entre les événements.
* §2 Transport en `u = log x` et normalisation. CORRECTION de la prescription : le facteur est `−u e^{−u/2}/2` (et non
  `e^{+u/2}`). Une impulsion en `n` de poids `w(n)` devient, normalisée, `Λ(n)/√n` (`normalized_atom_weight`) ; la densité du
  fond `e^u/u du` devient `e^{u/2}/2` (`normalized_background_density`) ; la densité de comptage d'un zéro, transportée et
  normalisée, est EXACTEMENT `e^{(β−1/2)u} cos(T u)` (`normalized_mode_density`). Le signal normalisé est donc une mesure
  (atomes `Λ(n)/√n` moins une densité lisse), non une fonction ; sa représentation spectrale `Σ e^{(β−1/2)u} cos(T u)` est une
  égalité au sens des fonctions test, jamais ponctuelle.
* §3 Amplitude intrinsèque. `|e^{(β−1/2)u}|` est constante en `u` ⟺ `β = 1/2` (`individualAmplitudeRigidity_iff`) ; pour tous
  les vrais zéros ⟺ RH (`individualAmplitudeRigidity_all_iff`). C'est le DERNIER maillon, une caractérisation : le maillon
  précédent, « contraintes arithmétiques ⟹ rigidité », n'est pas démontré et n'est l'hypothèse d'aucune fermeture.

Régularité (portée exacte) : `J₀ − F` est lisse sur chaque intervalle ouvert sans puissance de premier et saute de `w(n)` en
chaque `n` ; toute somme finie de contributions est lisse (`countingSum_hasDerivAt`) ; la normalisation transporte des atomes,
pas une fonction partout non dérivable. Aucun énoncé « nulle part dérivable » n'est vrai de `J₀ − F` (il est dérivable hors
d'un ensemble dénombrable) ; aucun autre objet n'est ici identifié qui le serait.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## §1 Impulsions arithmétiques et dérivée distributionnelle du comptage -/

/-- Comptage à gauche `J₋(t) = Σ_{n < t} w(n)`. -/
noncomputable def countingJLeft (t : ℝ) : ℝ := ∑ n ∈ Finset.range ⌈t⌉₊, countingWeight n

/-- Sur `t ≤ N`, le comptage à gauche est la somme finie des marches `w(n)·1_{n<t}`, `n < N`. -/
theorem countingJLeft_eq_steps {N : ℕ} {t : ℝ} (htN : t ≤ N) :
    countingJLeft t = ∑ n ∈ Finset.range N, countingWeight n * (if (n : ℝ) < t then 1 else 0) := by
  unfold countingJLeft
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_range, Finset.mem_filter]
  constructor
  · intro h
    have h1 : (n : ℝ) < t := Nat.lt_ceil.mp h
    exact ⟨lt_of_lt_of_le h (Nat.ceil_le.mpr htN), h1⟩
  · rintro ⟨_, h⟩; exact Nat.lt_ceil.mpr h

/-- Intégrale d'une marche contre la dérivée d'une fonction test nulle aux bords :
`∫_a^b 1_{c<t} φ'(t) dt = −φ(c)` si `a < c < b`, `0` sinon. -/
theorem step_test_integral {φ φ' : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hφ : ∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t) (hφ' : ContinuousOn φ' (Set.Icc a b))
    (ha : φ a = 0) (hb : φ b = 0) :
    ∫ t in a..b, (if c < t then 1 else 0) * φ' t = -(if a < c ∧ c < b then φ c else 0) := by
  have hI : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hFTC : ∀ {x y : ℝ}, a ≤ x → x ≤ y → y ≤ b → ∫ t in x..y, φ' t = φ y - φ x := by
    intro x y hax hxy hyb
    have hsub : Set.uIcc x y ⊆ Set.Icc a b := by
      rw [Set.uIcc_of_le hxy]; exact Set.Icc_subset_Icc hax hyb
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hφ t (hsub ht))
      ((hφ'.mono hsub).intervalIntegrable)
  by_cases hca : c ≤ a
  · have h1 : ∫ t in a..b, (if c < t then 1 else 0) * φ' t = ∫ t in a..b, φ' t := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
      rw [Set.uIoc_of_le hab] at ht
      rw [if_pos (lt_of_le_of_lt hca ht.1), one_mul]
    rw [h1, hFTC le_rfl hab le_rfl, ha, hb, if_neg (fun h => absurd h.1 (not_lt.mpr hca))]
    ring
  by_cases hcb : b ≤ c
  · have h1 : ∫ t in a..b, (if c < t then 1 else 0) * φ' t = ∫ t in a..b, (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
      rw [Set.uIoc_of_le hab] at ht
      rw [if_neg (not_lt.mpr (le_trans ht.2 hcb)), zero_mul]
    rw [h1, intervalIntegral.integral_zero, if_neg (fun h => absurd h.2 (not_lt.mpr hcb))]
    ring
  push Not at hca hcb
  have hφ'int : ∀ {x y : ℝ}, a ≤ x → x ≤ y → y ≤ b → IntervalIntegrable φ' MeasureTheory.volume x y := by
    intro x y hax hxy hyb
    have hsub : Set.uIcc x y ⊆ Set.Icc a b := by
      rw [Set.uIcc_of_le hxy]; exact Set.Icc_subset_Icc hax hyb
    exact (hφ'.mono hsub).intervalIntegrable
  have hL : ∫ t in a..c, (if c < t then 1 else 0) * φ' t = ∫ t in a..c, (0 : ℝ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le hca.le] at ht
    rw [if_neg (not_lt.mpr ht.2), zero_mul]
  have hR : ∫ t in c..b, (if c < t then 1 else 0) * φ' t = ∫ t in c..b, φ' t := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le hcb.le] at ht
    rw [if_pos ht.1, one_mul]
  have hiL : IntervalIntegrable (fun t => (if c < t then (1 : ℝ) else 0) * φ' t) MeasureTheory.volume a c := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hca.le]
    exact (MeasureTheory.integrableOn_zero).congr_fun
      (fun t ht => by rw [if_neg (not_lt.mpr ht.2), zero_mul]) measurableSet_Ioc
  have hiR : IntervalIntegrable (fun t => (if c < t then (1 : ℝ) else 0) * φ' t) MeasureTheory.volume c b := by
    have h := hφ'int hca.le hcb.le le_rfl
    rw [intervalIntegrable_iff, Set.uIoc_of_le hcb.le] at h ⊢
    exact h.congr_fun (fun t ht => by rw [if_pos ht.1, one_mul]) measurableSet_Ioc
  rw [← intervalIntegral.integral_add_adjacent_intervals hiL hiR, hL, hR, intervalIntegral.integral_zero,
    hFTC hca.le hcb.le le_rfl, hb, if_pos ⟨hca, hcb⟩]
  ring

/-- **Dérivée distributionnelle du comptage** : pour toute fonction test `φ` de classe `C¹` sur `[a, b]`, nulle en `a` et en
`b`, avec `b ≤ N`, `∫_a^b J₋(t) φ'(t) dt = −Σ_{n<N, a<n<b} w(n) φ(n)`, c'est-à-dire `DJ = Σ_n w(n) δ_n` sur `]a, b[`. -/
theorem counting_distributional_derivative {φ φ' : ℝ → ℝ} {a b : ℝ} {N : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    (hφ : ∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t) (hφ' : ContinuousOn φ' (Set.Icc a b))
    (ha : φ a = 0) (hb : φ b = 0) :
    ∫ t in a..b, countingJLeft t * φ' t =
      -∑ n ∈ Finset.range N, countingWeight n * (if a < (n : ℝ) ∧ (n : ℝ) < b then φ n else 0) := by
  have hI : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hcongr : ∫ t in a..b, countingJLeft t * φ' t =
      ∫ t in a..b, ∑ n ∈ Finset.range N, countingWeight n * ((if (n : ℝ) < t then 1 else 0) * φ' t) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le hab] at ht
    rw [countingJLeft_eq_steps (le_trans ht.2 hbN), Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hint : ∀ n ∈ Finset.range N, IntervalIntegrable
      (fun t => countingWeight n * ((if (n : ℝ) < t then (1 : ℝ) else 0) * φ' t)) MeasureTheory.volume a b := by
    intro n _
    refine IntervalIntegrable.const_mul ?_ _
    have h := (hI ▸ hφ').intervalIntegrable (μ := MeasureTheory.volume)
    rw [intervalIntegrable_iff, Set.uIoc_of_le hab] at h ⊢
    refine (h.indicator (measurableSet_Ioi (a := (n : ℝ)))).congr_fun (fun t _ => ?_) measurableSet_Ioc
    by_cases hn : (n : ℝ) < t
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hn), if_pos hn, one_mul]
    · rw [Set.indicator_of_notMem (fun h' => hn (Set.mem_Ioi.mp h')), if_neg hn, zero_mul]
  rw [hcongr, intervalIntegral.integral_finsetSum hint, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_const_mul, step_test_integral hab hφ hφ' ha hb]
  ring

/-! ## §2 Transport en `u = log x` et normalisation `−u e^{−u/2}/2` -/

/-- Une impulsion en `n ≥ 2` de poids `w(n)`, transportée en `u = log n` et normalisée par `u e^{−u/2}`, a pour poids
`Λ(n)/√n`. -/
theorem normalized_atom_weight {n : ℕ} (hn : 2 ≤ n) :
    Real.log n * Real.exp (-(Real.log n) / 2) * countingWeight n =
      ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  have hs : Real.exp (-(Real.log n) / 2) = 1 / Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0, neg_div, Real.exp_neg, one_div]
    congr 2; ring
  unfold countingWeight
  rw [hs]
  field_simp

/-- La densité du fond `dF = dx/log x` (terme principal) devient `e^u/u du` en `u = log x` ; normalisée par `u e^{−u/2}/2`,
elle vaut `e^{u/2}/2`. -/
theorem normalized_background_density {u : ℝ} (hu : 0 < u) :
    u * Real.exp (-u / 2) / 2 * (Real.exp u / u) = Real.exp (u / 2) / 2 := by
  have h : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by rw [← Real.exp_add]; congr 1; ring
  field_simp
  rw [← h]; ring_nf

/-- **Normalisation exacte d'un mode** : la densité de comptage d'un vrai zéro, transportée en `u = log x` (facteur `e^u`
du changement de variable) et multipliée par `−u e^{−u/2}/2`, est EXACTEMENT `e^{(β−1/2)u} cos(T u)`, pour `u > 0`. -/
theorem normalized_mode_density (z : TrueZero) {u : ℝ} (hu : 0 < u) :
    -(u * Real.exp (-u / 2) / 2) * (countingModulationDensity z (Real.exp u) * Real.exp u) =
      Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * u) * Real.cos (rZeroHeight z.1 * u) := by
  have hx : 1 < Real.exp u := by simpa using Real.exp_lt_exp.mpr hu
  rw [countingDensity_eq_weightedMode z hx, Real.log_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos u),
    Real.log_exp]
  have hu0 : u ≠ 0 := hu.ne'
  have h3 : Real.exp (-(u / 2)) * Real.exp u = Real.exp (u / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (u * (1 / 2)) = Real.exp (u / 2) := by congr 1; ring
  rw [h2]
  have he : Real.exp (u / 2) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  rw [mul_right_comm, h3]

/-- Le mode normalisé a pour module `e^{(β−1/2)u}` : seule place de la position radiale. -/
theorem normalized_mode_abs_le (z : TrueZero) {u : ℝ} (hu : 0 < u) :
    |-(u * Real.exp (-u / 2) / 2) * (countingModulationDensity z (Real.exp u) * Real.exp u)| ≤
      Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * u) := by
  rw [normalized_mode_density z hu, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

/-! ## §3 Amplitude intrinsèque : le dernier maillon (caractérisation) -/

/-- Rigidité d'amplitude individuelle d'un vrai zéro : le module du mode normalisé ne dépend pas de `u > 0`. -/
def IndividualAmplitudeRigidity (z : TrueZero) : Prop :=
  ∀ u₁ u₂ : ℝ, 0 < u₁ → 0 < u₂ →
    Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * u₁) = Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * u₂)

/-- **Dernier maillon** : amplitude intrinsèque constante ⟺ `β = 1/2` (caractérisation, aucune loi). -/
theorem individualAmplitudeRigidity_iff (z : TrueZero) :
    IndividualAmplitudeRigidity z ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro h
    have h12 := h 1 2 one_pos two_pos
    rw [Real.exp_eq_exp] at h12
    linarith
  · intro h u₁ u₂ _ _
    rw [h, sub_self, zero_mul, zero_mul]

/-- Pour tous les vrais zéros, la rigidité d'amplitude individuelle ⟺ RH : la démontrer depuis l'arithmétique, c'est
démontrer RH. Elle n'est l'hypothèse d'aucune fermeture du dépôt. -/
theorem individualAmplitudeRigidity_all_iff :
    (∀ z : TrueZero, IndividualAmplitudeRigidity z) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_all_canonical_onLine fun n _ =>
      (individualAmplitudeRigidity_iff _).mp (h _)
  · intro hRH z
    exact (individualAmplitudeRigidity_iff z).mpr (thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1)

end RHV6Fresh

#print axioms RHV6Fresh.counting_distributional_derivative
#print axioms RHV6Fresh.normalized_atom_weight
#print axioms RHV6Fresh.normalized_background_density
#print axioms RHV6Fresh.normalized_mode_density
#print axioms RHV6Fresh.individualAmplitudeRigidity_all_iff
