/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GapSynchronization
import RHV6Fresh.Terminal.AmplitudeStableSynchronization
import RHV6Fresh.Terminal.BackgroundModulation
import RHV6Fresh.Terminal.AuthenticPassageProfile

/-!
# RHV6Fresh — synchronisation locale des contributions des zéros sur chaque écart premier (C126, E264–E300, 2026-10-14)

Objet (mission E264–E300) : les écarts premiers `I_n = [p_n, p_{n+1}]` sont les unités de contrôle ; chaque zéro contribue
individuellement et la reconstruction est locale et additive. Ce module formalise les faits INDÉPENDANTS de RH, puis situe
la contrainte C126 par rapport au but `:399` (`radial_conservation_anchored`), sans le modifier.

Variable `t = log x`.

1. **Écart premier** `PrimeGapInterval` : rang `n`, bornes `p_n < p_{n+1}`, bornes logarithmiques `0 < a < b`.
2. **Contribution locale, canal de comptage** : `countingGapTerm ρ a b = ∫_a^b e^{ρt}/t dt` (`= ∫ x^{ρ−1}/log x dx`,
   soit `li(e^{bρ}) − li(e^{aρ})` ; `Ei` est absent de Mathlib, la forme intégrale est la définition) ; contribution
   signée regroupée avec le conjugué `zeroLocalContribution ρ I = −2 Re countingGapTerm ρ I.a I.b`. Faits : concaténation
   (télescopage, `countingGapTerm_add`), borne d'enveloppe (`countingGapTerm_norm_le`), dérivée exacte par rapport à la
   borne supérieure = densité (`countingGapTerm_hasDerivAt`), signe marginal = cosinus de la phase, indépendant de `β`
   (`marginal_contribution_re`), **facteur hyperbolique** d'une paire miroir `e^{(ρ₀−d)t} + e^{(ρ₀+d)t} − 2e^{ρ₀t} =
   2(cosh(dt) − 1)e^{ρ₀t}` (`mirror_pair_density`, `countingGapTerm_mirror_pair`).
3. **Décomposition locale exacte, canal lissé** (seul canal dont la formule explicite est compilée ; la reconstruction
   du canal de COMPTAGE `ΔJ₀ = Δli + Σ C_j + R` de l'énoncé de l'auteur n'est PAS formalisée : `zeroLocalContribution`
   n'entre dans aucune identité de reconstruction, audit E301) : contribution locale
   `smoothedLocalContribution ρ I = (−m_ρ/(ρ+1))·gapTerm ρ I.a I.b`, cible `localArithmeticTarget I = R(p_{n+1}) − R(p_n)`,
   résidu de troncature `localReconstructionResidual s I`. **Synchronisation locale** (`localSynchronization`) : la cible
   est la somme sur TOUS les vrais zéros ; le résidu d'une troncature finie est la queue infinie (`localResidual_eq_tail`) ;
   une décomposition à résidu défini par différence est une tautologie (`finite_truncation_tautology`).
4. **Rigidité des contributions locales** (`local_contribution_rigidity`) : si deux points donnent les mêmes contributions
   locales sur tous les écarts `[a, b]`, `b > a`, ils sont égaux. Elle vaut pour TOUTE partie réelle : elle identifie
   `(β, T)`, elle ne contraint pas `β` (`rigidity_identifies_any_radial`).
5. **Rapport au but `:399`** : la lecture ON des contributions locales (`LocalOnScale`) équivaut à `β = 1/2`
   (`localOnScale_iff`) ; départ ON + lecture ON de l'arrivée ⟹ `radialFactor = 1` (`localOnScale_closes`) ; quantifiée sur
   les passages d'historique ON ⟺ RH sous l'ancre (`local_on_law_iff_riemannHypothesis`). La chaîne « progression
   verticale ⟹ contributions locales ⟹ synchronisation exacte ⟹ rigidité ⟹ `β = 1/2` » a ses trois premiers maillons
   démontrés pour toute `β` ; le quatrième est une caractérisation du but, non une dérivation.
-/

namespace RHV6Fresh

open RHV3Lean Complex MeasureTheory intervalIntegral

/-! ## 1. Écart premier -/

/-- Écart premier de rang `n` : `[p_n, p_{n+1}]`. -/
structure PrimeGapInterval where
  rank : ℕ

namespace PrimeGapInterval

/-- Borne inférieure `p_n`. -/
noncomputable def lower (I : PrimeGapInterval) : ℝ := fnPrimeAtRank I.rank
/-- Borne supérieure `p_{n+1}`. -/
noncomputable def upper (I : PrimeGapInterval) : ℝ := fnPrimeAtRank (I.rank + 1)
/-- Borne logarithmique inférieure `a = log p_n`. -/
noncomputable def a (I : PrimeGapInterval) : ℝ := Real.log I.lower
/-- Borne logarithmique supérieure `b = log p_{n+1}`. -/
noncomputable def b (I : PrimeGapInterval) : ℝ := Real.log I.upper

theorem one_lt_lower (I : PrimeGapInterval) : 1 < I.lower := by
  unfold lower; exact_mod_cast (thm_primeAtRank_isPrime I.rank).one_lt

theorem one_lt_upper (I : PrimeGapInterval) : 1 < I.upper := by
  unfold upper; exact_mod_cast (thm_primeAtRank_isPrime (I.rank + 1)).one_lt

theorem lower_lt_upper (I : PrimeGapInterval) : I.lower < I.upper := by
  unfold lower upper; exact_mod_cast thm_primeAtRank_strictMono (Nat.lt_succ_self I.rank)

theorem a_pos (I : PrimeGapInterval) : 0 < I.a := Real.log_pos I.one_lt_lower

theorem a_lt_b (I : PrimeGapInterval) : I.a < I.b :=
  Real.log_lt_log (by linarith [I.one_lt_lower]) I.lower_lt_upper

end PrimeGapInterval

/-! ## 2. Contribution locale d'un point au canal de comptage -/

/-- Densité du canal de comptage en variable logarithmique : `e^{ρt}/t` (soit `x^{ρ−1}/log x` en `x = e^t`). -/
noncomputable def countingDensity (ρ : ℂ) (t : ℝ) : ℂ := Complex.exp (ρ * t) / t

/-- Contribution locale exacte d'un point `ρ` à l'écart logarithmique `[a, b]` dans le canal de comptage :
`∫_a^b e^{ρt}/t dt = li(e^{bρ}) − li(e^{aρ})`. -/
noncomputable def countingGapTerm (ρ : ℂ) (a b : ℝ) : ℂ := ∫ t in a..b, countingDensity ρ t

/-- Contribution signée réelle du point `ρ` (regroupé avec son conjugué) à l'écart premier `I`. -/
noncomputable def zeroLocalContribution (ρ : ℂ) (I : PrimeGapInterval) : ℝ :=
  -2 * (countingGapTerm ρ I.a I.b).re

theorem countingDensity_continuousOn (ρ : ℂ) : ContinuousOn (countingDensity ρ) {t : ℝ | t ≠ 0} := by
  unfold countingDensity
  apply ContinuousOn.div
  · exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn
  · exact Complex.continuous_ofReal.continuousOn
  · intro t ht; exact_mod_cast ht

theorem countingDensity_intervalIntegrable (ρ : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (countingDensity ρ) volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine (countingDensity_continuousOn ρ).mono ?_
  intro t ht
  rcases Set.mem_uIcc.mp ht with h | h <;> show _ ≠ _ <;> linarith [h.1]

/-- **Concaténation (télescopage)** : la contribution à deux écarts adjacents est la contribution à leur réunion. -/
theorem countingGapTerm_add (ρ : ℂ) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    countingGapTerm ρ a b + countingGapTerm ρ b c = countingGapTerm ρ a c :=
  integral_add_adjacent_intervals (countingDensity_intervalIntegrable ρ ha hb)
    (countingDensity_intervalIntegrable ρ hb hc)

/-- Module de la densité : `e^{βt}/t`. -/
theorem countingDensity_norm (ρ : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖countingDensity ρ t‖ = Real.exp (ρ.re * t) / t := by
  unfold countingDensity
  rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  congr 2
  simp [Complex.mul_re]

/-- **Borne d'enveloppe** : `‖∫_a^b e^{ρt}/t‖ ≤ (b − a)·e^{β b}/a` pour `0 < a ≤ b`, `0 ≤ β`. -/
theorem countingGapTerm_norm_le (ρ : ℂ) (hρ : 0 ≤ ρ.re) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖countingGapTerm ρ a b‖ ≤ Real.exp (ρ.re * b) / a * (b - a) := by
  have h : ∀ t ∈ Set.uIoc a b, ‖countingDensity ρ t‖ ≤ Real.exp (ρ.re * b) / a := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    have ht0 : 0 < t := lt_trans ha ht.1
    rw [countingDensity_norm ρ ht0]
    apply div_le_div₀ (Real.exp_pos _).le _ ha ht.1.le
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hρ)
  have := norm_integral_le_of_norm_le_const h
  rwa [abs_of_nonneg (by linarith)] at this

/-- **Dérivée exacte par rapport à la borne supérieure** : la contribution locale varie comme la densité `e^{ρb}/b`. -/
theorem countingGapTerm_hasDerivAt (ρ : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun u => countingGapTerm ρ a u) (countingDensity ρ b) b := by
  have hopen : IsOpen {t : ℝ | t ≠ 0} := isOpen_ne
  have hb' : b ∈ {t : ℝ | t ≠ 0} := ne_of_gt hb
  exact integral_hasDerivAt_right (countingDensity_intervalIntegrable ρ ha hb)
    (ContinuousOn.stronglyMeasurableAtFilter hopen (countingDensity_continuousOn ρ) b hb')
    ((countingDensity_continuousOn ρ).continuousAt (hopen.mem_nhds hb'))

/-- **Signe marginal** : la partie réelle de la densité est `e^{βt} cos(Tt)/t` : le signe de la contribution marginale à une
borne est celui du cosinus de la phase `T·log p`, quelle que soit la partie réelle. -/
theorem marginal_contribution_re (ρ : ℂ) (t : ℝ) :
    (countingDensity ρ t).re = Real.exp (ρ.re * t) * Real.cos (ρ.im * t) / t := by
  unfold countingDensity
  have hre : (Complex.exp (ρ * t)).re = Real.exp (ρ.re * t) * Real.cos (ρ.im * t) := by
    rw [Complex.exp_re]; simp [Complex.mul_re, Complex.mul_im]
  rw [Complex.div_ofReal_re, hre]

/-! ### Paire miroir : le facteur hyperbolique -/

/-- **Facteur hyperbolique** : `e^{(ρ₀−d)t} + e^{(ρ₀+d)t} − 2e^{ρ₀t} = 2(cosh(dt) − 1)·e^{ρ₀t}`, `d` réel. -/
theorem mirror_pair_density (ρ₀ : ℂ) (d t : ℝ) :
    Complex.exp ((ρ₀ - d) * t) + Complex.exp ((ρ₀ + d) * t) - 2 * Complex.exp (ρ₀ * t) =
      2 * (Complex.cosh (d * t) - 1) * Complex.exp (ρ₀ * t) := by
  have h1 : Complex.exp ((ρ₀ - d) * t) = Complex.exp (-(d * t)) * Complex.exp (ρ₀ * t) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h2 : Complex.exp ((ρ₀ + d) * t) = Complex.exp (d * t) * Complex.exp (ρ₀ * t) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [h1, h2, mul_sub, Complex.two_cosh]; ring

/-- **Paire miroir sur un écart** : `C_{ρ₀−d} + C_{ρ₀+d} − 2C_{ρ₀} = ∫_a^b 2(cosh(dt) − 1) e^{ρ₀t}/t dt`. Le défaut d'une
paire hypothétique par rapport au point ON de même hauteur est positif à l'ordre `d²` ; il est non nul dès `d ≠ 0`. -/
theorem countingGapTerm_mirror_pair (ρ₀ : ℂ) (d : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    countingGapTerm (ρ₀ - d) a b + countingGapTerm (ρ₀ + d) a b - 2 * countingGapTerm ρ₀ a b =
      ∫ t in a..b, 2 * (Complex.cosh (d * t) - 1) * Complex.exp (ρ₀ * t) / t := by
  unfold countingGapTerm
  rw [← intervalIntegral.integral_const_mul, ← integral_add (countingDensity_intervalIntegrable _ ha hb)
    (countingDensity_intervalIntegrable _ ha hb),
    ← integral_sub ((countingDensity_intervalIntegrable _ ha hb).add (countingDensity_intervalIntegrable _ ha hb))
      ((countingDensity_intervalIntegrable ρ₀ ha hb).const_mul 2)]
  congr 1; funext t
  unfold countingDensity
  rw [← mirror_pair_density]; ring

/-! ### Forme réelle de la contribution (formule de l'auteur) et zéros de la densité -/

/-- Densité locale réelle de l'auteur : `D_ρ(t) = −2 e^{βt} cos(Tt)/t` (soit `−2 x^{β−1} cos(T log x)/log x` en `x = e^t`). -/
noncomputable def realCountingDensity (ρ : ℂ) (t : ℝ) : ℝ :=
  -2 * (Real.exp (ρ.re * t) * Real.cos (ρ.im * t) / t)

theorem realCountingDensity_eq (ρ : ℂ) (t : ℝ) :
    realCountingDensity ρ t = -2 * (countingDensity ρ t).re := by
  rw [realCountingDensity, marginal_contribution_re]

/-- **Formule exacte de l'auteur** : `C_ρ(a, b) = −2 ∫_a^b e^{βt} cos(Tt)/t dt` (variable `t = log x` :
`−2 ∫ x^{β−1} cos(T log x)/log x dx`). La contribution signée est l'intégrale de la densité réelle, aucune oscillation à
amplitude fixe ne s'y substitue. -/
theorem zeroLocalContribution_eq_real_integral (ρ : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    -2 * (countingGapTerm ρ a b).re = ∫ t in a..b, realCountingDensity ρ t := by
  have h := Complex.reCLM.intervalIntegral_comp_comm (countingDensity_intervalIntegrable ρ ha hb)
  simp only [Complex.reCLM_apply] at h
  unfold countingGapTerm
  rw [← h, ← intervalIntegral.integral_const_mul]
  congr 1; funext t; rw [realCountingDensity_eq]

/-- Contribution partielle `C_ρ(a, x)` depuis le début de l'écart : sa dérivée en `x` est la densité réelle `D_ρ(x)`. -/
theorem partialContribution_hasDerivAt (ρ : ℂ) {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (fun u => -2 * (countingGapTerm ρ a u).re) (realCountingDensity ρ x) x := by
  have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (countingGapTerm_hasDerivAt ρ ha hx)).const_mul (-2)
  simpa [realCountingDensity_eq] using h

/-- Point de changement de signe de la densité, d'indice `k` : `x_k = exp((π/2 + kπ)/T)` (en logarithme `(π/2 + kπ)/T`). -/
noncomputable def densitySignChangeLog (T : ℝ) (k : ℤ) : ℝ := (Real.pi / 2 + k * Real.pi) / T

/-- **Changements de signe de la densité** : pour `t > 0`, `D_ρ(t) = 0 ⟺ cos(Tt) = 0 ⟺ ∃ k, t = (π/2 + kπ)/T`. Ils ne
dépendent que de la hauteur `T`, jamais de `β`. -/
theorem realCountingDensity_eq_zero_iff (ρ : ℂ) (hT : ρ.im ≠ 0) {t : ℝ} (ht : 0 < t) :
    realCountingDensity ρ t = 0 ↔ ∃ k : ℤ, t = densitySignChangeLog ρ.im k := by
  unfold realCountingDensity densitySignChangeLog
  have hexp : Real.exp (ρ.re * t) ≠ 0 := (Real.exp_pos _).ne'
  constructor
  · intro h
    have hcos : Real.cos (ρ.im * t) = 0 := by
      rcases mul_eq_zero.mp h with h0 | h0
      · norm_num at h0
      · rcases div_eq_zero_iff.mp h0 with h1 | h1
        · rcases mul_eq_zero.mp h1 with h2 | h2
          · exact absurd h2 hexp
          · exact h2
        · exact absurd h1 ht.ne'
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hcos
    refine ⟨k, ?_⟩
    rw [eq_div_iff hT]
    linear_combination hk
  · rintro ⟨k, hk⟩
    have hcos : Real.cos (ρ.im * t) = 0 := by
      rw [Real.cos_eq_zero_iff]
      refine ⟨k, ?_⟩
      rw [hk]; field_simp; ring
    rw [hcos]; simp

/-- Les changements de signe de la densité sont communs à tous les points de même hauteur (`ρ₀`, `ρ₀ ± d`). -/
theorem densitySignChange_beta_independent (ρ ρ' : ℂ) (hT : ρ.im = ρ'.im) (hT0 : ρ.im ≠ 0) {t : ℝ} (ht : 0 < t) :
    realCountingDensity ρ t = 0 ↔ realCountingDensity ρ' t = 0 := by
  rw [realCountingDensity_eq_zero_iff ρ hT0 ht, realCountingDensity_eq_zero_iff ρ' (hT ▸ hT0) ht, hT]

/-- **Trois familles de points distinctes** : le contact de phase `C_k = exp((arctan(T/β) + kπ)/T)` d'un vrai zéro et le
changement de signe de sa densité `x_k = exp((π/2 + kπ)/T)` diffèrent de `log(C_k/x_k) = −arctan(β/T)/T < 0` : le contact de
phase précède strictement le zéro de la densité, d'un décalage qui lit `β`. -/
theorem contact_vs_densitySignChange (z : TrueZero) (k : ℤ) :
    Real.log (contactMinusAt z k) - densitySignChangeLog (rZeroHeight z.1) k =
      -(Real.arctan (rZeroRadialPosition z.1 / rZeroHeight z.1) / rZeroHeight z.1) := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  rw [contactMinusAt_eq_exp, Real.log_exp]
  unfold densitySignChangeLog
  have hinv : rZeroHeight z.1 / rZeroRadialPosition z.1 = (rZeroRadialPosition z.1 / rZeroHeight z.1)⁻¹ :=
    (inv_div _ _).symm
  rw [hinv, Real.arctan_inv_of_pos (div_pos hβ hT)]
  field_simp
  ring

/-! ## 3. Décomposition locale exacte (canal lissé, formule explicite compilée) -/

/-- Contribution locale lissée du vrai zéro `ρ` à l'écart premier `I` : `(−m_ρ/(ρ+1))·∫_a^b e^{ρt} dt`. -/
noncomputable def smoothedLocalContribution (ρ : ExplicitIndex) (I : PrimeGapInterval) : ℂ :=
  (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) + 1)) * gapTerm ρ I.a I.b

/-- Cible arithmétique locale : incrément du reste lissé des premiers sur l'écart (aucun zéro dans sa définition). -/
noncomputable def localArithmeticTarget (I : PrimeGapInterval) : ℂ :=
  smoothedRemainder I.upper - smoothedRemainder I.lower

/-- Résidu de reconstruction après troncature à une famille FINIE `s` de vrais zéros. -/
noncomputable def localReconstructionResidual (s : Finset ExplicitIndex) (I : PrimeGapInterval) : ℂ :=
  localArithmeticTarget I - ∑ ρ ∈ s, smoothedLocalContribution ρ I

/-- Chaque contribution locale lissée est l'incrément du terme de résidu du zéro entre les deux bornes. -/
theorem smoothedLocalContribution_eq (ρ : ExplicitIndex) (I : PrimeGapInterval) :
    smoothedLocalContribution ρ I =
      nontrivialZeroResidueTerm I.upper ρ - nontrivialZeroResidueTerm I.lower ρ := by
  unfold smoothedLocalContribution PrimeGapInterval.a PrimeGapInterval.b
  exact (residueTerm_gap_eq ρ (by linarith [I.one_lt_lower]) (by linarith [I.one_lt_upper])).symm

/-- La famille des contributions locales lissées est sommable (convergence absolue de la formule explicite lissée). -/
theorem smoothedLocalContribution_summable (I : PrimeGapInterval) :
    Summable (fun ρ : ExplicitIndex => smoothedLocalContribution ρ I) := by
  have h := (nontrivial_zero_residue_series_summable I.one_lt_upper).sub
    (nontrivial_zero_residue_series_summable I.one_lt_lower)
  exact h.congr fun ρ => (smoothedLocalContribution_eq ρ I).symm

/-- **C126, synchronisation locale (canal lissé)** : pour CHAQUE écart premier, l'incrément du reste des premiers est la
somme, sur TOUS les vrais zéros, de leurs contributions locales exactes. Aucune hypothèse sur les positions radiales. -/
theorem localSynchronization (I : PrimeGapInterval) :
    localArithmeticTarget I = ∑' ρ : ExplicitIndex, smoothedLocalContribution ρ I :=
  prime_gap_synchronization I.rank

/-- **Le résidu d'une troncature finie est la queue infinie** : la somme finie ne remplace jamais la formule explicite
sans son terme de reste, et ce reste est la somme des zéros omis. -/
theorem localResidual_eq_tail (s : Finset ExplicitIndex) (I : PrimeGapInterval) :
    localReconstructionResidual s I =
      ∑' ρ : ((s : Set ExplicitIndex)ᶜ : Set ExplicitIndex), smoothedLocalContribution ρ.1 I := by
  unfold localReconstructionResidual
  rw [localSynchronization I, ← (smoothedLocalContribution_summable I).sum_add_tsum_compl (s := s)]
  ring

/-- Le résidu est nul exactement quand la queue est nulle (le reste de troncature n'est pas une contradiction). -/
theorem localResidual_eq_zero_iff (s : Finset ExplicitIndex) (I : PrimeGapInterval) :
    localReconstructionResidual s I = 0 ↔
      ∑' ρ : ((s : Set ExplicitIndex)ᶜ : Set ExplicitIndex), smoothedLocalContribution ρ.1 I = 0 := by
  rw [localResidual_eq_tail]

/-- **Tautologie de la décomposition finie** : pour TOUTE cible `c` et TOUTE famille finie `f`, poser le résidu par
différence rend la décomposition vraie. Sans le théorème de queue, une « décomposition locale » n'a aucun contenu. -/
theorem finite_truncation_tautology {ι : Type*} (s : Finset ι) (f : ι → ℂ) (c : ℂ) :
    c = ∑ j ∈ s, f j + (c - ∑ j ∈ s, f j) := by ring

/-- Linéarité : la contribution locale d'une famille finie est l'intégrale de sa superposition (réutilisation). -/
theorem smoothedLocalContribution_finset_sum (s : Finset ExplicitIndex) (I : PrimeGapInterval) :
    ∑ ρ ∈ s, smoothedLocalContribution ρ I =
      ∫ t in I.a..I.b, ∑ ρ ∈ s, (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) + 1)) * Complex.exp ((ρ : ℂ) * t) :=
  gap_sum_linear s _ _ I.a I.b

/-- Télescopage de la cible sur une fenêtre d'écarts consécutifs : aucune compensation entre écarts n'est masquée. -/
theorem localArithmeticTarget_window (n m : ℕ) :
    ∑ k ∈ Finset.range m, localArithmeticTarget ⟨n + k⟩ =
      smoothedRemainder (fnPrimeAtRank (n + m)) - smoothedRemainder (fnPrimeAtRank n) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    unfold localArithmeticTarget PrimeGapInterval.upper PrimeGapInterval.lower
    simp only [Nat.add_succ]
    ring

/-! ## 4. Rigidité des contributions locales -/

/-- Lemme : si `e^{ρb} = e^{ρ'b}` pour tout `b > a`, alors `ρ = ρ'`. -/
theorem exp_eq_on_ray_imp_eq {ρ ρ' : ℂ} {a : ℝ}
    (h : ∀ b : ℝ, a < b → Complex.exp (ρ * b) = Complex.exp (ρ' * b)) : ρ = ρ' := by
  set b₀ : ℝ := a + 1 with hb₀
  have hb₀a : a < b₀ := by linarith
  have hg : ∀ b : ℝ, a < b → Complex.exp ((ρ - ρ') * b) = 1 := by
    intro b hb
    have hne : Complex.exp (ρ' * b) ≠ 0 := Complex.exp_ne_zero _
    rw [sub_mul, Complex.exp_sub, h b hb, div_self hne]
  have hD : HasDerivAt (fun b : ℝ => Complex.exp ((ρ - ρ') * b))
      (Complex.exp ((ρ - ρ') * b₀) * (ρ - ρ')) b₀ := by
    have h1 : HasDerivAt (fun b : ℝ => ((ρ - ρ') * (b : ℂ))) (ρ - ρ') b₀ := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := b₀)).const_mul (ρ - ρ'))
    exact h1.cexp
  have hconst : HasDerivAt (fun b : ℝ => Complex.exp ((ρ - ρ') * b)) 0 b₀ := by
    have h1 : HasDerivAt (fun _ : ℝ => (1 : ℂ)) 0 b₀ := hasDerivAt_const _ _
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hb₀a] with b hb
    exact hg b hb
  have := hconst.unique hD
  have hne : Complex.exp ((ρ - ρ') * b₀) ≠ 0 := Complex.exp_ne_zero _
  have h0 : ρ - ρ' = 0 := by
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hne
    · exact h
  exact sub_eq_zero.mp h0

/-- **Rigidité des contributions locales** : deux points qui donnent la même contribution locale sur tous les intervalles
`[a, b]`, pour TOUTE borne réelle `b > a > 0`, sont égaux. Les contributions locales d'un point isolé identifient `(β, T)`.
Portée (audit E301) : l'hypothèse porte sur un continu de bornes, pas sur les seuls écarts premiers `[log p_n, log p_{n+1}]` ;
l'identifiabilité depuis les seuls écarts premiers n'est pas démontrée ici. -/
theorem local_contribution_rigidity {ρ ρ' : ℂ} {a : ℝ} (ha : 0 < a)
    (h : ∀ b : ℝ, a < b → countingGapTerm ρ a b = countingGapTerm ρ' a b) : ρ = ρ' := by
  apply exp_eq_on_ray_imp_eq (a := a)
  intro b hb
  have hb0 : 0 < b := lt_trans ha hb
  have hD := countingGapTerm_hasDerivAt ρ ha hb0
  have hD' := countingGapTerm_hasDerivAt ρ' ha hb0
  have hD'' : HasDerivAt (fun u => countingGapTerm ρ a u) (countingDensity ρ' b) b := by
    refine hD'.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hb] with u hu
    exact h u hu
  have heq := hD''.unique hD
  unfold countingDensity at heq
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  exact (div_left_inj' hb').mp heq.symm

/-- **La rigidité identifie toute position radiale** (elle n'est pas « aveugle à `β` » : la contribution dépend explicitement
de `β`, voir §4bis) : elle identifie tout point, hors ligne compris ; en particulier le point `1/4 + iT` est identifié par ses
contributions aussi sûrement que `1/2 + iT`. Identifier n'est pas contraindre. -/
theorem rigidity_identifies_any_radial (T : ℝ) {a : ℝ} (ha : 0 < a) :
    (∀ ρ' : ℂ, (∀ b : ℝ, a < b → countingGapTerm (1 / 4 + T * I) a b = countingGapTerm ρ' a b) →
      ρ' = 1 / 4 + T * I) ∧
    (∀ ρ' : ℂ, (∀ b : ℝ, a < b → countingGapTerm (1 / 2 + T * I) a b = countingGapTerm ρ' a b) →
      ρ' = 1 / 2 + T * I) :=
  ⟨fun _ h => (local_contribution_rigidity ha h).symm, fun _ h => (local_contribution_rigidity ha h).symm⟩

/-- Rigidité pour le canal lissé par écart (même preuve : la dérivée de `gapTerm` est la densité `e^{ρb}`). -/
theorem gapTerm_rigidity {ρ ρ' : ℂ} {a : ℝ}
    (h : ∀ b : ℝ, a < b → gapTerm ρ a b = gapTerm ρ' a b) : ρ = ρ' := by
  apply exp_eq_on_ray_imp_eq (a := a)
  intro b hb
  have hcont : ∀ σ : ℂ, Continuous fun t : ℝ => Complex.exp (σ * t) := fun σ => by fun_prop
  have hD : HasDerivAt (fun u => gapTerm ρ a u) (Complex.exp (ρ * b)) b :=
    integral_hasDerivAt_right ((hcont ρ).intervalIntegrable _ _)
      ((hcont ρ).stronglyMeasurableAtFilter _ _) (hcont ρ).continuousAt
  have hD' : HasDerivAt (fun u => gapTerm ρ' a u) (Complex.exp (ρ' * b)) b :=
    integral_hasDerivAt_right ((hcont ρ').intervalIntegrable _ _)
      ((hcont ρ').stronglyMeasurableAtFilter _ _) (hcont ρ').continuousAt
  have hD'' : HasDerivAt (fun u => gapTerm ρ a u) (Complex.exp (ρ' * b)) b := by
    refine hD'.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hb] with u hu
    exact h u hu
  exact (hD''.unique hD).symm


/-! ## 4bis. Sensibilité radiale : la contribution locale VOIT `β` (audit prioritaire de l'auteur, 2026-10-14)

Inventaire de la dépendance à `β` dans ce module : les points de changement de signe de la densité
(`realCountingDensity_eq_zero_iff`, `densitySignChange_beta_independent`) ne dépendent que de `T` ; la valeur de la densité
(`realCountingDensity`, `countingDensity_norm`), la contribution intégrée (`countingGapTerm`, `zeroLocalContribution`) et l'enveloppe
(`countingGapTerm_norm_le`) en dépendent explicitement. `localSynchronization` et `local_contribution_rigidity` VALENT pour toute
`β` (la dépendance est dans les termes, pas effacée). Ce qui suit formalise la dérivée radiale, l'injectivité en `β` de la densité
(théorème A de l'auteur) et l'inversion à deux points. -/

/-- Dérivée radiale de la densité du canal de comptage : `∂_β [e^{(β+iT)t}/t] = e^{(β+iT)t}` (`t ≠ 0`). -/
theorem countingDensity_radial_hasDerivAt (T : ℝ) (β : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun β : ℝ => countingDensity (β + T * I) t) (Complex.exp ((β + T * I) * t)) β := by
  have h1 : HasDerivAt (fun β : ℝ => ((β : ℂ) + T * I) * t) (t : ℂ) β := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := β)).add_const ((T : ℂ) * I)).mul_const (t : ℂ)
    simpa using this
  have h2 := (h1.cexp).div_const (t : ℂ)
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  unfold countingDensity
  exact h2.congr_deriv (by rw [mul_div_assoc, div_self ht', mul_one])

/-- **Sensibilité radiale de la contribution locale** : `∂_β C_{β,T}(a,b) = ∫_a^b e^{(β+iT)t} dt = gapTerm (β+iT) a b`
(dérivation sous l'intégrale, bornes `0 < a, b`). -/
theorem countingGapTerm_radial_hasDerivAt (T : ℝ) (β₀ : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun β : ℝ => countingGapTerm (β + T * I) a b) (gapTerm (β₀ + T * I) a b) β₀ := by
  have hpos : ∀ t ∈ Set.uIoc a b, 0 < t := by
    intro t ht
    rcases Set.mem_uIoc.mp ht with h | h <;> linarith [h.1]
  set M : ℝ := max a b with hM
  have hbound : ∀ t ∈ Set.uIoc a b, ∀ β ∈ Metric.ball β₀ 1,
      ‖Complex.exp ((β + T * I) * t)‖ ≤ Real.exp ((|β₀| + 1) * M) := by
    intro t ht β hβ
    have htpos := hpos t ht
    have htM : t ≤ M := by
      rcases Set.mem_uIoc.mp ht with h | h
      · exact le_trans h.2 (le_max_right _ _)
      · exact le_trans h.2 (le_max_left _ _)
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : ((β + T * I : ℂ) * t).re = β * t := by simp [Complex.mul_re]
    rw [hre]
    have hβabs : |β| ≤ |β₀| + 1 := by
      have := Metric.mem_ball.mp hβ
      rw [Real.dist_eq] at this
      calc |β| = |β₀ + (β - β₀)| := by ring_nf
        _ ≤ |β₀| + |β - β₀| := abs_add_le _ _
        _ ≤ |β₀| + 1 := by linarith
    calc β * t ≤ |β| * t := mul_le_mul_of_nonneg_right (le_abs_self β) htpos.le
      _ ≤ (|β₀| + 1) * t := mul_le_mul_of_nonneg_right hβabs htpos.le
      _ ≤ (|β₀| + 1) * M := mul_le_mul_of_nonneg_left htM (by positivity)
  have hcontF : ∀ β : ℝ, ContinuousOn (fun t : ℝ => countingDensity (β + T * I) t) (Set.uIoc a b) :=
    fun β => (countingDensity_continuousOn _).mono (fun t ht => ne_of_gt (hpos t ht))
  have hcontF' : ContinuousOn (fun t : ℝ => Complex.exp ((β₀ + T * I) * t)) (Set.uIoc a b) :=
    (by fun_prop : Continuous fun t : ℝ => Complex.exp ((β₀ + T * I) * t)).continuousOn
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (E := ℂ) (x₀ := β₀)
    (F := fun (β : ℝ) (t : ℝ) => countingDensity (β + T * I) t)
    (F' := fun (β : ℝ) (t : ℝ) => Complex.exp ((β + T * I) * t))
    (bound := fun _ => Real.exp ((|β₀| + 1) * M)) (μ := volume) (a := a) (b := b)
    (Metric.ball_mem_nhds β₀ one_pos)
    (Filter.Eventually.of_forall fun (β : ℝ) => (hcontF β).aestronglyMeasurable measurableSet_uIoc)
    (countingDensity_intervalIntegrable _ ha hb)
    (hcontF'.aestronglyMeasurable measurableSet_uIoc)
    (Filter.Eventually.of_forall fun t ht (β : ℝ) hβ => hbound t ht β hβ)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun t ht (β : ℝ) _ => countingDensity_radial_hasDerivAt T β (ne_of_gt (hpos t ht)))
  exact h.2

/-- **Forme fermée de l'auteur** : `∂_β[−2 Re C_{β,T}(a,b)] = −2 Re[(e^{bρ} − e^{aρ})/ρ]`, `ρ = β₀ + iT ≠ 0`
(en `x = e^t` : `−2 Re[(b^ρ − a^ρ)/ρ]`). Elle n'est pas identiquement nulle : sa dérivée en `b` est `−2 e^{β₀b} cos(Tb)`. -/
theorem zeroLocalContribution_radial_derivative (T : ℝ) (β₀ : ℝ) (hρ : (β₀ : ℂ) + T * I ≠ 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun β : ℝ => -2 * (countingGapTerm (β + T * I) a b).re)
      (-2 * ((Complex.exp ((β₀ + T * I) * b) - Complex.exp ((β₀ + T * I) * a)) / (β₀ + T * I)).re) β₀ := by
  have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt β₀
    (countingGapTerm_radial_hasDerivAt T β₀ ha hb)).const_mul (-2)
  rw [gapTerm_eq hρ] at h
  simpa using h

/-- La sensibilité radiale n'est pas identiquement nulle : `Re e^{ρb} = e^{βb} cos(Tb)`, non nul dès que `cos(Tb) ≠ 0`
(des annulations oscillatoires sur un écart particulier restent possibles). -/
theorem radial_sensitivity_density_ne_zero (β T b : ℝ) (hc : Real.cos (T * b) ≠ 0) :
    (Complex.exp ((β + T * I) * b)).re ≠ 0 := by
  rw [Complex.exp_re]
  have h1 : ((β + T * I : ℂ) * b).re = β * b := by simp [Complex.mul_re]
  have h2 : ((β + T * I : ℂ) * b).im = T * b := by simp [Complex.mul_im]
  rw [h1, h2]
  exact mul_ne_zero (Real.exp_pos _).ne' hc

/-- Sur tout intervalle ouvert, le cosinus `cos(T·)` ne s'annule pas partout. -/
theorem exists_cos_ne_zero_in_Ioo (T : ℝ) {u v : ℝ} (huv : u < v) :
    ∃ t ∈ Set.Ioo u v, Real.cos (T * t) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set t₀ : ℝ := (u + v) / 2 with ht₀
  have ht₀mem : t₀ ∈ Set.Ioo u v := ⟨by rw [ht₀]; linarith, by rw [ht₀]; linarith⟩
  have hD : HasDerivAt (fun t : ℝ => Real.cos (T * t)) (-Real.sin (T * t₀) * T) t₀ := by
    have := (hasDerivAt_id t₀).const_mul T
    simpa using this.cos
  have hconst : HasDerivAt (fun t : ℝ => Real.cos (T * t)) 0 t₀ := by
    refine (hasDerivAt_const t₀ (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht₀mem.1 ht₀mem.2] with t ht
    exact hcon t ht
  have hzero := hconst.unique hD
  have hcos := hcon t₀ ht₀mem
  have hsin : Real.sin (T * t₀) * T = 0 := by linarith
  have hpyth := Real.sin_sq_add_cos_sq (T * t₀)
  rcases mul_eq_zero.mp hsin with hs | hT
  · rw [hs, hcos] at hpyth; norm_num at hpyth
  · rw [hT, zero_mul, Real.cos_zero] at hcos; exact one_ne_zero hcos

/-- **Théorème A (identifiabilité radiale individuelle)** : à hauteur `T` fixée, deux positions radiales qui donnent la même
densité individuelle sur un intervalle ouvert `]u, v[`, `0 < u`, sont égales. -/
theorem density_radial_injective {β₁ β₂ T : ℝ} {u v : ℝ} (hu : 0 < u) (huv : u < v)
    (h : ∀ t ∈ Set.Ioo u v, realCountingDensity (β₁ + T * I) t = realCountingDensity (β₂ + T * I) t) :
    β₁ = β₂ := by
  obtain ⟨t, ht, hc⟩ := exists_cos_ne_zero_in_Ioo T huv
  have htpos : 0 < t := lt_trans hu ht.1
  have := h t ht
  unfold realCountingDensity at this
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.add_im, Complex.mul_im] at this
  have hsimp : ∀ β : ℝ, -2 * (Real.exp ((β + (T * 0 - 0 * 1)) * t) * Real.cos ((0 + (T * 1 + 0 * 0)) * t) / t) =
      -2 * (Real.exp (β * t) * Real.cos (T * t) / t) := fun β => by ring_nf
  rw [hsimp, hsimp] at this
  have hexp : Real.exp (β₁ * t) = Real.exp (β₂ * t) := by
    have h2 : Real.exp (β₁ * t) * Real.cos (T * t) / t = Real.exp (β₂ * t) * Real.cos (T * t) / t :=
      mul_left_cancel₀ (by norm_num : (-2 : ℝ) ≠ 0) this
    have h3 : Real.exp (β₁ * t) * Real.cos (T * t) = Real.exp (β₂ * t) * Real.cos (T * t) :=
      (div_left_inj' htpos.ne').mp h2
    exact mul_right_cancel₀ hc h3
  have := Real.exp_injective hexp
  exact mul_right_cancel₀ htpos.ne' this

/-- **Inversion exacte à deux points** (formule de l'auteur, variable `t = log x` : `e^{βt} dt = x^{β−1} dx`, d'où l'exposant
`β` ici et `β − 1` en `x`) : à `T` connu, deux abscisses `t₁ ≠ t₂ > 0` où `cos ≠ 0` restituent `β` depuis la densité isolée. -/
theorem radial_inversion_two_points (β T : ℝ) {t₁ t₂ : ℝ} (h1 : 0 < t₁) (h2 : 0 < t₂) (hne : t₁ ≠ t₂)
    (hc1 : Real.cos (T * t₁) ≠ 0) (hc2 : Real.cos (T * t₂) ≠ 0) :
    β = Real.log |(realCountingDensity (β + T * I) t₂ * t₂ / Real.cos (T * t₂)) /
          (realCountingDensity (β + T * I) t₁ * t₁ / Real.cos (T * t₁))| / (t₂ - t₁) := by
  have hval : ∀ t : ℝ, 0 < t → Real.cos (T * t) ≠ 0 →
      realCountingDensity (β + T * I) t * t / Real.cos (T * t) = -2 * Real.exp (β * t) := by
    intro t ht hc
    unfold realCountingDensity
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.mul_im]
    field_simp
    ring_nf
  rw [hval t₁ h1 hc1, hval t₂ h2 hc2]
  have hpos1 := Real.exp_pos (β * t₁)
  have hpos2 := Real.exp_pos (β * t₂)
  have hratio : (-2 * Real.exp (β * t₂)) / (-2 * Real.exp (β * t₁)) = Real.exp (β * (t₂ - t₁)) := by
    rw [mul_sub, Real.exp_sub]; field_simp
  rw [hratio, abs_of_pos (Real.exp_pos _), Real.log_exp]
  have hne' : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  field_simp

/-! ## 5. Rapport au but `:399` : lecture ON des contributions locales -/

/-- **Lecture ON des contributions locales** d'un vrai zéro : sa densité exacte a, en toute abscisse logarithmique `t > 0`,
l'amplitude de l'échelle de la ligne `e^{t/2}`. -/
def LocalOnScale (z : TrueZero) : Prop :=
  ∀ t : ℝ, 0 < t → ‖Complex.exp ((z.1.1 : ℂ) * t)‖ = Real.exp (t / 2)

/-- La lecture ON des contributions locales ⟺ `β = 1/2` (une seule abscisse suffit dans un sens). -/
theorem localOnScale_iff (z : TrueZero) : LocalOnScale z ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  have hnorm : ∀ t : ℝ, ‖Complex.exp ((z.1.1 : ℂ) * t)‖ = Real.exp (rZeroRadialPosition z.1 * t) := by
    intro t
    rw [Complex.norm_exp, rZeroRadialPosition_eq_re]
    congr 1; simp [Complex.mul_re]
  constructor
  · intro h
    have h1 := h 1 one_pos
    rw [hnorm] at h1
    have := Real.exp_injective h1
    linarith
  · intro h t _
    rw [hnorm, h]; ring_nf

/-- **Fermeture du but `:399` sous la lecture ON** de l'arrivée : c'est le but écrit sur les contributions locales. -/
theorem localOnScale_closes (p : TZeroPassage) (hL : 0 < rZeroHeight p.zLaterMember)
    (h : LocalOnScale ⟨p.zLaterMember, hL⟩) : radialFactor ⟨p.zLaterMember, hL⟩ = 1 :=
  (radialFactor_eq_one_iff ⟨p.zLaterMember, hL⟩).mpr ((localOnScale_iff _).mp h)

/-- **La loi « lecture ON de l'arrivée sur tout passage d'historique ON » équivaut à RH** sous l'ancre : C126 sous sa
forme fermante n'est pas plus faible que RH. -/
theorem local_on_law_iff_riemannHypothesis (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    (∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ hL : 0 < rZeroHeight p.zLaterMember, LocalOnScale ⟨p.zLaterMember, hL⟩) ↔ RiemannHypothesis := by
  constructor
  · intro h
    refine riemannHypothesis_of_anchor_and_history_conservation h₁ ?_
    intro p hE hV hOn hHist
    have hL : 0 < rZeroHeight p.zLaterMember := lt_of_lt_of_le hE (passage_height_le p)
    rw [hOn]
    exact (localOnScale_iff ⟨p.zLaterMember, hL⟩).mp (h p hE hV hOn hHist hL)
  · intro hRH p hE hV hOn hHist hL
    refine (localOnScale_iff ⟨p.zLaterMember, hL⟩).mpr ?_
    have := history_conservation_of_conservation (conservation_of_riemannHypothesis hRH) p hE hV hOn hHist
    rw [this, hOn]

/-- **Ce que C126 démontre pour toute position radiale** : sur tout passage, la synchronisation locale tient sur chaque
écart et la contribution du membre atteint y est identifiée par ses contributions ; ni l'une ni l'autre ne mentionne la
partie réelle de l'arrivée. Le troisième composant est la trichotomie de `ℝ` (`lt_trichotomy`) : il n'a aucun contenu
propre (audit E301). -/
theorem c126_holds_any_radial (p : TZeroPassage) (I : PrimeGapInterval) :
    localArithmeticTarget I = ∑' ρ : ExplicitIndex, smoothedLocalContribution ρ I ∧
      (∀ ρ' : ℂ, (∀ b : ℝ, I.a < b → countingGapTerm (p.zLaterMember.1 : ℂ) I.a b = countingGapTerm ρ' I.a b) →
        ρ' = (p.zLaterMember.1 : ℂ)) ∧
      (rZeroRadialPosition p.zLaterMember < 1 / 2 ∨ rZeroRadialPosition p.zLaterMember = 1 / 2 ∨
        1 / 2 < rZeroRadialPosition p.zLaterMember) :=
  ⟨localSynchronization I, fun _ h => (local_contribution_rigidity I.a_pos h).symm, lt_trichotomy _ _⟩

#print axioms localSynchronization
#print axioms localResidual_eq_tail
#print axioms countingGapTerm_mirror_pair
#print axioms countingGapTerm_hasDerivAt
#print axioms local_contribution_rigidity
#print axioms gapTerm_rigidity
#print axioms localOnScale_closes
#print axioms local_on_law_iff_riemannHypothesis
#print axioms zeroLocalContribution_eq_real_integral
#print axioms realCountingDensity_eq_zero_iff
#print axioms contact_vs_densitySignChange
#print axioms countingGapTerm_radial_hasDerivAt
#print axioms zeroLocalContribution_radial_derivative
#print axioms density_radial_injective
#print axioms radial_inversion_two_points

end RHV6Fresh
