/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.OscillationResultant

/-!
# Architecture du champ de comptage : fréquences, amplitudes, contacts, écarts (E332, E333 ; auteur, 2026-10-18)

E332 a montré que les contributions des zéros s'additionnent sur les MÊMES intervalles premiers, dans un seul
champ de comptage autour du fond `F`, et que seule la limite spectrale porte les sauts. Ce module écrit les objets
correspondants et leurs conversions exactes ; il ne contient aucune hypothèse de position radiale.

* §1 Fréquences : la phase `T log x` a pour dérivée `T/x` ; fréquence algébrique locale `T/(2πx)`, période locale
  `2πx/T` (inverses) ; un tour exact couvre `[x, x e^{2π/T}]`, de longueur algébrique `x(e^{2π/T} − 1) ≥ 2πx/T` ;
  nombre de demi-tours d'un zéro sur un écart `[a, b]` : `(T/π) log(b/a)`.
* §2 Trois niveaux d'amplitude : mode unité (module 1), mode pondéré (module `e^{(β−1/2)u}`), densité de comptage
  `b'(x) = −2/(√x log x) · e^{(β−1/2) log x} cos(T log x)` ; enveloppe démontrée `|b'(x)| ≤ 2x^{β−1}/log x`. Les
  trois niveaux diffèrent par des facteurs explicites ; aucune identification n'est permise sans eux.
* §3 Taxonomie des contacts d'un zéro (familles DISJOINTES dès `β > 0`) :
  (C) contacts de Tour `C_k = exp((φ + kπ)/T)` : la contribution brute `c = −2 Re(x^ρ/ρ)` touche son enveloppe
  (`pairContribution_at_contact`, déjà compilé), la densité de comptage n'y est JAMAIS nulle ;
  (D) `D_k = exp((π/2 + kπ)/T)` : zéros de la densité de comptage = extrema de `b` et de `c` ;
  (Z) zéros de la contribution brute `Tu = φ + π/2 + kπ` ; décalages exacts `log Z_k − log C_k = π/(2T)`.
  Les zéros de `b` lui-même (contact de la courbe individuelle `F + b` avec `F`) n'ont pas de forme close dans
  le dépôt (`Ei` absent de Mathlib) ; les événements premiers ne sont dans aucune de ces familles (§4).
* §4 Champ collectif sur un écart : l'incrément d'une somme finie sur `[a, b]` est la somme des variations de
  TOUTES ses contributions sur ce même intervalle ; complément `E = ΔC − ΔS`, passage de `N` à `N + 1`,
  télescopage ; une somme finie est continue, donc le complément porte TOUT saut de la correction ; minoration
  démontrée de la largeur d'une montée par la borne de la densité (Lipschitz).
* §5 Le canal `J₀` au demi-saut, défini depuis `Λ` : sur un écart de premiers `p < q`,
  `ΔJ₀ = 1 + Σ_{p<n<q} Λ(n)/log n`, `= 1` sans puissance de premier intérieure ; correction `D = ΔJ₀ − ΔF`.
* §6 Limite collective : `CountingExplicitFormula` NOMME l'énoncé « les sommes successives tendent vers `J₀ − F` en
  tout `x > 1` » (formule explicite du canal `J`, NON démontrée dans le dépôt, obligation de transport) ; sous lui,
  le complément de chaque écart tend vers 0. Hypothèse d'aucune fermeture.

Portée : identités et bornes vraies pour toute famille et toute position radiale ; aucun énoncé ne fixe `β`.
-/

namespace RHV6Fresh

open RHV3Lean Filter Topology

/-! ## §1 Fréquence logarithmique et fréquence algébrique -/

/-- La phase `T log x` a pour dérivée `T/x` : fréquence intrinsèque `T` en `u = log x`, fréquence algébrique
`T/(2πx)` en `x`. -/
theorem logPhase_hasDerivAt (T : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => T * Real.log y) (T / x) x := by
  have h := (Real.hasDerivAt_log hx.ne').const_mul T
  simpa [div_eq_mul_inv] using h

/-- Fréquence algébrique locale `f(x) = T/(2πx)`. -/
noncomputable def localFrequency (T x : ℝ) : ℝ := T / (2 * Real.pi * x)

/-- Période algébrique locale `λ(x) = 2πx/T`. -/
noncomputable def localPeriod (T x : ℝ) : ℝ := 2 * Real.pi * x / T

theorem localFrequency_mul_localPeriod {T x : ℝ} (hT : T ≠ 0) (hx : x ≠ 0) :
    localFrequency T x * localPeriod T x = 1 := by
  unfold localFrequency localPeriod
  field_simp

/-- Un tour exact de phase : de `x` à `x e^{2π/T}` la phase avance de `2π`, à toute abscisse. -/
theorem logPhase_full_turn {T x : ℝ} (hT : T ≠ 0) (hx : 0 < x) :
    T * Real.log (x * Real.exp (2 * Real.pi / T)) = T * Real.log x + 2 * Real.pi := by
  rw [Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp, mul_add, mul_div_cancel₀ _ hT]

/-- La longueur algébrique d'un tour, `x(e^{2π/T} − 1)`, est au moins la période locale `2πx/T`
(et lui est équivalente quand `x/T` est fixé et `T → ∞`). -/
theorem turn_length_ge_localPeriod {T x : ℝ} (hx : 0 < x) :
    localPeriod T x ≤ x * Real.exp (2 * Real.pi / T) - x := by
  unfold localPeriod
  have h := Real.add_one_le_exp (2 * Real.pi / T)
  have : 2 * Real.pi * x / T = x * (2 * Real.pi / T) := by ring
  rw [this]
  nlinarith

/-- Nombre de demi-tours d'un zéro de hauteur `T` sur un intervalle `[a, b]` : `(T/π) log(b/a)` ; il ne dépend
que de la hauteur et des bornes, jamais de la position radiale. -/
noncomputable def halfTurnsOnGap (T a b : ℝ) : ℝ := T * Real.log (b / a) / Real.pi

theorem halfTurnsOnGap_eq_phase_advance {T a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    halfTurnsOnGap T a b * Real.pi = T * Real.log b - T * Real.log a := by
  unfold halfTurnsOnGap
  rw [Real.log_div hb.ne' ha.ne', div_mul_cancel₀ _ Real.pi_pos.ne']
  ring

/-! ## §2 Trois niveaux d'amplitude et leurs conversions -/

/-- Niveau 1 : le mode unité `e^{iTu}` est de module 1. -/
theorem unitMode_norm (T u : ℝ) : ‖Complex.exp (((T * u : ℝ) : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Niveau 3 exprimé par le niveau 2 : la densité de comptage d'un zéro est
`b'(x) = −2/(√x log x) · e^{(β−1/2) log x} cos(T log x)`. Le facteur `−2/(√x log x)` est la conversion exacte
entre le mode pondéré et la densité. -/
theorem countingDensity_eq_weightedMode (z : TrueZero) {x : ℝ} (hx : 1 < x) :
    countingModulationDensity z x =
      -2 / (Real.sqrt x * Real.log x) *
        (Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * Real.log x) *
          Real.cos (rZeroHeight z.1 * Real.log x)) := by
  have h := counting_density_sum_eq {z} hx
  simpa [Finset.sum_singleton, weightedResultant_re] using h

/-- Enveloppe démontrée de la densité de comptage : `|b'(x)| ≤ 2x^{β−1}/log x`, toute position radiale. -/
theorem countingDensity_abs_le (z : TrueZero) {x : ℝ} (hx : 1 < x) :
    |countingModulationDensity z x| ≤ 2 * x ^ (rZeroRadialPosition z.1 - 1) / Real.log x := by
  have hx0 : 0 < x := lt_trans one_pos hx
  have hl : 0 < Real.log x := Real.log_pos hx
  have hp : 0 < x ^ (rZeroRadialPosition z.1 - 1) := Real.rpow_pos_of_pos hx0 _
  unfold countingModulationDensity
  rw [abs_div, abs_of_pos hl, abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos hp]
  apply div_le_div_of_nonneg_right _ hl.le
  have := Real.abs_cos_le_one (rZeroHeight z.1 * Real.log x)
  nlinarith

/-- Le rapport des niveaux 2 et 3 : à `x` fixé, l'enveloppe de densité vaut `2/(√x log x)` fois le module du
mode pondéré. -/
theorem densityEnvelope_eq_weightedModule (z : TrueZero) {x : ℝ} (hx : 1 < x) :
    2 * x ^ (rZeroRadialPosition z.1 - 1) / Real.log x =
      2 / (Real.sqrt x * Real.log x) * Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * Real.log x) := by
  rw [rpow_sub_one_eq_exp_div_sqrt (lt_trans one_pos hx)]
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr (lt_trans one_pos hx)).ne'
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp

/-- Densité collective d'une famille finie : `|Σ b_z'(x)| ≤ Σ 2x^{β_z−1}/log x` (sur la ligne, `2·card s/(√x log x)`) ;
avec `rise_width_ge`, toute montée d'une somme finie est d'autant plus large que la famille est petite. -/
theorem collectiveDensity_abs_le (s : Finset TrueZero) {x : ℝ} (hx : 1 < x) :
    |∑ z ∈ s, countingModulationDensity z x| ≤
      ∑ z ∈ s, 2 * x ^ (rZeroRadialPosition z.1 - 1) / Real.log x :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => countingDensity_abs_le z hx)

/-! ## §3 Taxonomie des contacts d'un zéro -/

/-- (Z) Zéro de la contribution brute : `exp((φ + π/2 + kπ)/T)`, `φ = arctan(T/β)`. -/
noncomputable def rawSignalZero (z : TrueZero) (k : ℤ) : ℝ :=
  Real.exp ((Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) + Real.pi / 2 + (k : ℝ) * Real.pi) /
    rZeroHeight z.1)

/-- (D) En `D_k`, la densité de comptage s'annule : `D_k` est un extremum de `b` (et de `c`). -/
theorem countingDensity_at_extremum (z : TrueZero) (k : ℤ) :
    countingModulationDensity z (modulationExtremum z k) = 0 := by
  have hT : 0 < rZeroHeight z.1 := z.2
  unfold countingModulationDensity modulationExtremum
  rw [Real.log_exp, mul_div_cancel₀ _ hT.ne', add_comm, Real.cos_add_pi_div_two, Real.sin_int_mul_pi]
  simp

/-- (Z) En `Z_k`, la contribution brute s'annule. -/
theorem pairContribution_at_rawSignalZero (z : TrueZero) (k : ℤ) :
    pairContribution z (rawSignalZero z k) = 0 := by
  have hT : 0 < rZeroHeight z.1 := z.2
  unfold rawSignalZero
  rw [pairContribution_eq (Real.exp_pos _), Real.log_exp, mul_div_cancel₀ _ hT.ne']
  have : Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) + Real.pi / 2 + (k : ℝ) * Real.pi -
      Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) = (k : ℝ) * Real.pi + Real.pi / 2 := by ring
  rw [this, Real.cos_add_pi_div_two, Real.sin_int_mul_pi]
  simp

/-- Décalage exact entre zéro de la contribution brute et contact de Tour : `log Z_k − log C_k = π/(2T)`. -/
theorem rawSignalZero_contact_offset (z : TrueZero) (k : ℤ) :
    Real.log (rawSignalZero z k) - Real.log (contactMinusAt z k) = Real.pi / (2 * rZeroHeight z.1) := by
  have hT : 0 < rZeroHeight z.1 := z.2
  unfold rawSignalZero
  rw [contactMinusAt_eq_exp, Real.log_exp, Real.log_exp]
  field_simp
  ring

/-- (C) Au contact de Tour, la densité de comptage n'est jamais nulle (dès `C_k > 1`) : un contact de Tour n'est
ni un extremum de `b` ni un extremum de `c`. -/
theorem countingDensity_at_contact_ne_zero (z : TrueZero) (k : ℤ) (hC : 1 < contactMinusAt z k) :
    countingModulationDensity z (contactMinusAt z k) ≠ 0 := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hC0 : 0 < contactMinusAt z k := contactMinusAt_positive z k
  have hl : Real.log (contactMinusAt z k) ≠ 0 := (Real.log_pos hC).ne'
  have hp : contactMinusAt z k ^ (rZeroRadialPosition z.1 - 1) ≠ 0 := (Real.rpow_pos_of_pos hC0 _).ne'
  have hlog : rZeroHeight z.1 * Real.log (contactMinusAt z k) =
      Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) + (k : ℝ) * Real.pi := by
    rw [contactMinusAt_eq_exp, Real.log_exp, mul_div_cancel₀ _ hT.ne']
  have hcos : Real.cos (rZeroHeight z.1 * Real.log (contactMinusAt z k)) ≠ 0 := by
    rw [hlog, Real.cos_add_int_mul_pi]
    have hpos : 0 < Real.cos (Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1)) :=
      Real.cos_arctan_pos _
    have h1 : ((-1 : ℝ) ^ k) ≠ 0 := zpow_ne_zero _ (by norm_num)
    exact mul_ne_zero h1 hpos.ne'
  unfold countingModulationDensity
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp) hcos) hl

/-- Les trois familles d'un même zéro sont deux à deux disjointes à indice égal : `C_k < D_k < Z_k`
(`D_k − C_k` : `arctan(β/T)/T ∈ ]0, π/(2T)[`, `Z_k − C_k` : `π/(2T)`, en échelle logarithmique). -/
theorem contact_families_ordered (z : TrueZero) (k : ℤ) :
    contactMinusAt z k < modulationExtremum z k ∧ modulationExtremum z k < rawSignalZero z k := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hpos : 0 < Real.arctan (rZeroRadialPosition z.1 / rZeroHeight z.1) :=
    Real.arctan_pos.mpr (div_pos hβ hT)
  have hlt : Real.arctan (rZeroRadialPosition z.1 / rZeroHeight z.1) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have h1 := extremum_contact_offset z k
  have h2 := rawSignalZero_contact_offset z k
  have hD := Real.exp_pos ((Real.pi / 2 + (k : ℝ) * Real.pi) / rZeroHeight z.1)
  have hC := contactMinusAt_positive z k
  have hZ := Real.exp_pos ((Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) + Real.pi / 2 +
    (k : ℝ) * Real.pi) / rZeroHeight z.1)
  constructor
  · rw [← Real.log_lt_log_iff hC (by unfold modulationExtremum; exact hD)]
    have : 0 < Real.arctan (rZeroRadialPosition z.1 / rZeroHeight z.1) / rZeroHeight z.1 := div_pos hpos hT
    linarith
  · rw [← Real.log_lt_log_iff (by unfold modulationExtremum; exact hD) (by unfold rawSignalZero; exact hZ)]
    have : Real.arctan (rZeroRadialPosition z.1 / rZeroHeight z.1) / rZeroHeight z.1 <
        Real.pi / (2 * rZeroHeight z.1) := by
      rw [div_lt_div_iff₀ hT (by positivity)]; nlinarith
    linarith

/-! ## §4 Champ collectif sur un écart -/

/-- Incrément d'une somme finie de contributions sur `[a, b]`. -/
noncomputable def gapSumIncrement (s : Finset TrueZero) (F : TrueZero → ℂ → ℂ) (a b : ℝ) : ℝ :=
  countingSum s F b - countingSum s F a

/-- Complément de troncature sur `[a, b]` pour une correction `C` : `E = ΔC − ΔS`. -/
noncomputable def gapComplement (C : ℝ → ℝ) (s : Finset TrueZero) (F : TrueZero → ℂ → ℂ) (a b : ℝ) : ℝ :=
  (C b - C a) - gapSumIncrement s F a b

/-- **Tous les zéros contribuent au même écart** : l'incrément d'une somme finie sur `[a, b]` est la somme des
variations de chacune de ses contributions SUR CE MÊME intervalle, chacune intégrale de sa densité. -/
theorem gapSumIncrement_eq_sum_cells (s : Finset TrueZero) {F : TrueZero → ℂ → ℂ} {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b)
    (hF : ∀ z ∈ s, ∀ t ∈ Set.Icc a b, HasDerivAt (F z)
      (Complex.exp (zeroPoint z * (Real.log t : ℂ)) / (zeroPoint z * (Real.log t : ℂ)))
      (zeroPoint z * (Real.log t : ℂ))) :
    gapSumIncrement s F a b = ∑ z ∈ s, cellModulation z a b := by
  have hI : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  unfold gapSumIncrement countingSum cellModulation
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => -2 * (F z (zeroPoint z * (Real.log y : ℂ))).re)
      (countingModulationDensity z t) t := by
    intro t ht
    rw [hI] at ht
    exact counting_pair_hasDerivAt z (lt_of_lt_of_le ha ht.1) (hF z hz t ht)
  have hint : IntervalIntegrable (countingModulationDensity z) MeasureTheory.volume a b :=
    (hI ▸ countingModulationDensity_continuousOn z ha (b := b)).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

/-- Passage de `N` à `N + 1` sur un écart : ajouter un zéro retire exactement sa variation sur cet écart. -/
theorem gapComplement_insert [DecidableEq TrueZero] {s : Finset TrueZero} {z : TrueZero} (hz : z ∉ s)
    (C : ℝ → ℝ) (F : TrueZero → ℂ → ℂ) (a b : ℝ) :
    gapComplement C (insert z s) F a b =
      gapComplement C s F a b -
        (-2 * (F z (zeroPoint z * (Real.log b : ℂ))).re - -2 * (F z (zeroPoint z * (Real.log a : ℂ))).re) := by
  unfold gapComplement gapSumIncrement
  rw [countingSum_insert hz, countingSum_insert hz]
  ring

/-- Télescopage : les compléments de deux écarts consécutifs s'ajoutent. -/
theorem gapComplement_add (C : ℝ → ℝ) (s : Finset TrueZero) (F : TrueZero → ℂ → ℂ) (a b c : ℝ) :
    gapComplement C s F a b + gapComplement C s F b c = gapComplement C s F a c := by
  unfold gapComplement gapSumIncrement; ring

/-- Une somme finie de contributions est continue en tout `x > 1`. -/
theorem countingSum_continuousAt (s : Finset TrueZero) {F : TrueZero → ℂ → ℂ} {x : ℝ} (hx : 1 < x)
    (hF : ∀ z ∈ s, HasDerivAt (F z)
      (Complex.exp (zeroPoint z * (Real.log x : ℂ)) / (zeroPoint z * (Real.log x : ℂ)))
      (zeroPoint z * (Real.log x : ℂ))) :
    ContinuousAt (countingSum s F) x :=
  (countingSum_hasDerivAt s hx hF).continuousAt

/-- **Aucune somme finie ne porte un saut** : si la correction `C` n'est pas continue en `p > 1`, le complément
`C − S_s` ne l'est pas non plus, pour toute famille finie `s`. Le saut est porté par la limite seule. -/
theorem complement_discontinuous_of_jump (s : Finset TrueZero) {F : TrueZero → ℂ → ℂ} {C : ℝ → ℝ} {p : ℝ}
    (hp : 1 < p)
    (hF : ∀ z ∈ s, HasDerivAt (F z)
      (Complex.exp (zeroPoint z * (Real.log p : ℂ)) / (zeroPoint z * (Real.log p : ℂ)))
      (zeroPoint z * (Real.log p : ℂ)))
    (hC : ¬ ContinuousAt C p) :
    ¬ ContinuousAt (fun x => C x - countingSum s F x) p := by
  intro h
  apply hC
  have h2 := h.add (countingSum_continuousAt s hp hF)
  have heq : ((fun x => C x - countingSum s F x) + countingSum s F) = C := by
    funext x; simp
  rwa [heq] at h2

/-- **Largeur minimale d'une montée** (Lipschitz) : si la densité collective est bornée par `M` sur `[a, b]`, la
somme finie y varie d'au plus `M(b − a)` ; reproduire une montée `δ` exige `b − a ≥ δ/M`. -/
theorem gapSumIncrement_abs_le (s : Finset TrueZero) {F : TrueZero → ℂ → ℂ} {a b M : ℝ}
    (ha : 1 < a) (hab : a ≤ b)
    (hF : ∀ z ∈ s, ∀ t ∈ Set.Icc a b, HasDerivAt (F z)
      (Complex.exp (zeroPoint z * (Real.log t : ℂ)) / (zeroPoint z * (Real.log t : ℂ)))
      (zeroPoint z * (Real.log t : ℂ)))
    (hM : ∀ t ∈ Set.Icc a b, |∑ z ∈ s, countingModulationDensity z t| ≤ M) :
    |gapSumIncrement s F a b| ≤ M * (b - a) := by
  have hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt (countingSum s F) (∑ z ∈ s, countingModulationDensity z t) t := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    rw [counting_density_sum_eq s ht1]
    exact countingSum_hasDerivAt s ht1 fun z hz => hF z hz t ht
  have hcont : ContinuousOn (countingSum s F) (Set.Icc a b) := fun t ht =>
    (hderiv t ht).continuousAt.continuousWithinAt
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := countingSum s F)
    (f' := fun t => ∑ z ∈ s, countingModulationDensity z t) (C := M)
    (fun t ht => (hderiv t ht).hasDerivWithinAt)
    (fun t ht => by rw [Real.norm_eq_abs]; exact hM t (Set.Ico_subset_Icc_self ht)) b
    ⟨hab, le_refl b⟩
  unfold gapSumIncrement
  simpa [Real.norm_eq_abs] using h

theorem rise_width_ge (s : Finset TrueZero) {F : TrueZero → ℂ → ℂ} {a b M δ : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hMpos : 0 < M)
    (hF : ∀ z ∈ s, ∀ t ∈ Set.Icc a b, HasDerivAt (F z)
      (Complex.exp (zeroPoint z * (Real.log t : ℂ)) / (zeroPoint z * (Real.log t : ℂ)))
      (zeroPoint z * (Real.log t : ℂ)))
    (hM : ∀ t ∈ Set.Icc a b, |∑ z ∈ s, countingModulationDensity z t| ≤ M)
    (hrise : δ ≤ |gapSumIncrement s F a b|) :
    δ / M ≤ b - a := by
  rw [div_le_iff₀ hMpos]
  have := gapSumIncrement_abs_le s ha hab hF hM
  nlinarith

/-! ## §5 Le canal `J₀` au demi-saut, depuis `Λ` -/

/-- Poids de comptage `w(n) = Λ(n)/log n` (`1/k` en `n = p^k`, `0` hors des puissances de premiers). -/
noncomputable def countingWeight (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.log n

/-- `J₀(x) = Σ_{n ≤ x} w(n) − w(x)/2` si `x` est entier, valeur au demi-saut. -/
noncomputable def countingJHalf (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.range (⌊x⌋₊ + 1), countingWeight n) -
    (if (⌊x⌋₊ : ℝ) = x then countingWeight ⌊x⌋₊ / 2 else 0)

theorem countingJHalf_natCast (m : ℕ) :
    countingJHalf m = (∑ n ∈ Finset.range (m + 1), countingWeight n) - countingWeight m / 2 := by
  unfold countingJHalf
  rw [Nat.floor_natCast]
  simp

theorem countingWeight_prime {p : ℕ} (hp : p.Prime) : countingWeight p = 1 := by
  unfold countingWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  have : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  field_simp

theorem countingWeight_nonneg (n : ℕ) : 0 ≤ countingWeight n := by
  unfold countingWeight
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg n)

/-- **Saut de `J₀` sur un intervalle d'entiers** : `J₀(q) − J₀(p) = (w(p) + w(q))/2 + Σ_{p<n<q} w(n)`. -/
theorem countingJHalf_gap {p q : ℕ} (hpq : p < q) :
    countingJHalf q - countingJHalf p =
      (countingWeight p + countingWeight q) / 2 + ∑ n ∈ Finset.Ico (p + 1) q, countingWeight n := by
  rw [countingJHalf_natCast, countingJHalf_natCast, Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (p + 1)) (by omega : p + 1 ≤ q + 1),
    Finset.sum_Ico_succ_top (by omega : p + 1 ≤ q)]
  ring

/-- Sur un écart de premiers `p < q` : `ΔJ₀ = 1 + Σ_{p<n<q} w(n)` (puissances de premiers intérieures). -/
theorem countingJHalf_prime_gap {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    countingJHalf q - countingJHalf p = 1 + ∑ n ∈ Finset.Ico (p + 1) q, countingWeight n := by
  rw [countingJHalf_gap hpq, countingWeight_prime hp, countingWeight_prime hq]
  ring

/-- Sans puissance de premier intérieure, l'écart de premiers porte exactement une unité de `J₀`. -/
theorem countingJHalf_prime_gap_eq_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hnone : ∀ n ∈ Finset.Ico (p + 1) q, ¬ IsPrimePow n) :
    countingJHalf q - countingJHalf p = 1 := by
  rw [countingJHalf_prime_gap hp hq hpq]
  have : ∑ n ∈ Finset.Ico (p + 1) q, countingWeight n = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    unfold countingWeight
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (hnone n hn), zero_div]
  rw [this, add_zero]

/-- Correction de comptage d'un écart pour un fond `F` : `D = Δ(J₀ − F)`. Elle n'est pas la longueur `q − p`. -/
noncomputable def gapCountingCorrection (F : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (countingJHalf b - F b) - (countingJHalf a - F a)

theorem gapCountingCorrection_prime_gap (F : ℝ → ℝ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    gapCountingCorrection F p q =
      1 + (∑ n ∈ Finset.Ico (p + 1) q, countingWeight n) - (F q - F p) := by
  unfold gapCountingCorrection
  have := countingJHalf_prime_gap hp hq hpq
  linarith

/-! ## §6 Limite collective (énoncé nommé, non démontré) -/

/-- **Formule explicite du canal `J`, comme énoncé nommé** : pour une suite croissante de familles finies `S N`
et des primitives `Fz`, les sommes successives tendent vers `J₀ − F` en tout `x > 1`. NON DÉMONTRÉ dans le dépôt
(obligation de transport) ; hypothèse d'aucune fermeture. -/
def CountingExplicitFormula (F : ℝ → ℝ) (S : ℕ → Finset TrueZero) (Fz : TrueZero → ℂ → ℂ) : Prop :=
  ∀ x : ℝ, 1 < x → Tendsto (fun N => countingSum (S N) Fz x) atTop (𝓝 (countingJHalf x - F x))

/-- Sous la formule explicite nommée, le complément de chaque écart tend vers 0 (CONDITIONNEL). -/
theorem gapComplement_tendsto_zero {F : ℝ → ℝ} {S : ℕ → Finset TrueZero} {Fz : TrueZero → ℂ → ℂ}
    (hEF : CountingExplicitFormula F S Fz) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    Tendsto (fun N => gapComplement (fun x => countingJHalf x - F x) (S N) Fz a b) atTop (𝓝 0) := by
  have h := ((tendsto_const_nhds (x := (countingJHalf b - F b) - (countingJHalf a - F a))).sub
    ((hEF b hb).sub (hEF a ha)))
  have h0 : (countingJHalf b - F b) - (countingJHalf a - F a) -
      ((countingJHalf b - F b) - (countingJHalf a - F a)) = 0 := by ring
  rw [h0] at h
  refine h.congr fun N => ?_
  unfold gapComplement gapSumIncrement
  ring

end RHV6Fresh

#print axioms RHV6Fresh.turn_length_ge_localPeriod
#print axioms RHV6Fresh.countingDensity_eq_weightedMode
#print axioms RHV6Fresh.contact_families_ordered
#print axioms RHV6Fresh.countingDensity_at_contact_ne_zero
#print axioms RHV6Fresh.gapSumIncrement_eq_sum_cells
#print axioms RHV6Fresh.complement_discontinuous_of_jump
#print axioms RHV6Fresh.rise_width_ge
#print axioms RHV6Fresh.collectiveDensity_abs_le
#print axioms RHV6Fresh.countingJHalf_prime_gap
#print axioms RHV6Fresh.gapComplement_tendsto_zero
