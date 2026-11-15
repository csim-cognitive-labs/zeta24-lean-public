/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.SamplingFromLogGaps
import Mathlib.NumberTheory.Chebyshev

/-!
# De l'asymptotique de Tchebychev aux écarts logarithmiques : l'interface exacte avec le théorème des
# nombres premiers (module isolé)

Suite de l'exécution du maître §16.7 (solution 2) et réponse à la première « décision » du §17.6, que
l'auteur a tranchée le 2026-10-29 : « tes questions ne sont pas des choix, avance ».

**Le fait.** L'hypothèse nommée `LogGapsVanish` (les écarts logarithmiques entre premiers consécutifs
tendent vers zéro) n'est pas dans Mathlib. Elle est une conséquence du théorème des nombres premiers,
dont la formalisation Lean 4 existe hors Mathlib (projet PrimeNumberTheoremAnd, théorème
`chebyshev_asymptotic : θ ~[atTop] id`, où `θ` est la fonction de Tchebychev `Chebyshev.theta` de
Mathlib). Ce projet est épinglé sur une chaîne d'outils et une révision de Mathlib différentes des
nôtres (vérifié le 2026-10-29 : `v4.35.0` contre `v4.33.0-rc2`) ; l'importer comme dépendance
demanderait une reconstruction de Mathlib, hors de toute course bornée.

**Ce que fait ce module.** Il réduit l'écart à une substitution d'une ligne : il nomme l'hypothèse
`ChebyshevAsymptotic` sous la forme EXACTE du théorème externe (le quotient `θ x / x` tend vers un), et
démontre, avec Mathlib seul, qu'elle entraîne `LogGapsVanish`. Le jour où la dépendance est importée,
`chebyshevAsymptotic_of_isEquivalent` reçoit `chebyshev_asymptotic` et tout le chemin des zéros devient
inconditionnel en cette hypothèse.

**La preuve, en mots.** Entre deux premiers consécutifs il n'y a aucun premier, donc la fonction `θ`
(somme des logarithmes des premiers) est constante sur l'écart (`theta_eq_of_mem_gap`, par la propriété
caractéristique de l'énumération `Nat.nth`). Si une infinité d'écarts dépassaient une fraction fixe du
premier, `θ` resterait constante sur un intervalle `[p, (1 + ε/2) p]` avec `θ(p)/p` proche de un :
contradiction avec `θ(y)/y` proche de un en `y = (1 + ε/2) p`. Donc le rapport de deux premiers
consécutifs tend vers un (`ratio_tendsto_one_of_chebyshevAsymptotic`), et son logarithme vers zéro.

Composition : `ChebyshevAsymptotic ∧ DemandBoundedAtMeetings ∧ SummitAttained ⟹ RH`. Aucun axiome,
aucun `sorry`, aucune hypothèse posée comme démontrée. La chaîne est intacte.
-/

namespace RHV6Fresh

open Complex RHV3Lean Filter Topology

/-! ## 1. L'hypothèse nommée, sous la forme exacte du théorème externe -/

/-- **Asymptotique de Tchebychev (hypothèse nommée, jamais posée)** : `θ(x)/x` tend vers un. C'est le
théorème `chebyshev_asymptotic` (`θ ~[atTop] id`) du projet PrimeNumberTheoremAnd, écrit comme limite du
quotient. -/
def ChebyshevAsymptotic : Prop :=
  Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)

/-- La forme « équivalence asymptotique » du théorème externe donne l'hypothèse nommée. -/
theorem chebyshevAsymptotic_of_isEquivalent
    (h : Asymptotics.IsEquivalent atTop Chebyshev.theta id) : ChebyshevAsymptotic := by
  have hz : ∀ᶠ x : ℝ in atTop, (id x : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact ne_of_gt hx
  exact (Asymptotics.isEquivalent_iff_tendsto_one hz).mp h

/-! ## 2. `θ` est constante sur un écart premier -/

/-- Sur `[p_n, p_{n+1}[`, aucun premier n'est ajouté : `θ` y vaut `θ(p_n)`. -/
theorem theta_eq_of_mem_gap (n : ℕ) {y : ℝ} (hy : (fnPrimeAtRank n : ℝ) ≤ y)
    (hy' : y < fnPrimeAtRank (n + 1)) :
    Chebyshev.theta y = Chebyshev.theta (fnPrimeAtRank n : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE, Nat.floor_natCast]
  have hy0 : (0 : ℝ) ≤ y := le_trans (Nat.cast_nonneg _) hy
  congr 1
  ext p
  simp only [Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, hprime⟩
    refine ⟨?_, hprime⟩
    have h1 : (p : ℝ) ≤ y := (Nat.le_floor_iff hy0).mp hp
    have h2 : (p : ℝ) < fnPrimeAtRank (n + 1) := lt_of_le_of_lt h1 hy'
    have h3 : p < Nat.nth Nat.Prime (n + 1) := by exact_mod_cast h2
    exact Nat.le_nth_of_lt_nth_succ h3 hprime
  · rintro ⟨hp, hprime⟩
    refine ⟨Nat.le_floor ?_, hprime⟩
    have h1 : (p : ℝ) ≤ fnPrimeAtRank n := by exact_mod_cast hp
    linarith

/-! ## 3. Le rapport de deux premiers consécutifs tend vers un -/

/-- **Théorème** : sous l'asymptotique de Tchebychev, `p_{n+1} / p_n` tend vers un. -/
theorem ratio_tendsto_one_of_chebyshevAsymptotic (h : ChebyshevAsymptotic) :
    Tendsto (fun n : ℕ => (fnPrimeAtRank (n + 1) : ℝ) / fnPrimeAtRank n) atTop (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    refine Eventually.of_forall fun n => ?_
    have hp : (0 : ℝ) < fnPrimeAtRank n := by exact_mod_cast thm_primeAtRank_pos n
    have hlt : (fnPrimeAtRank n : ℝ) < fnPrimeAtRank (n + 1) := by
      exact_mod_cast thm_primeAtRank_strictMono (Nat.lt_succ_self n)
    exact ha.trans ((one_lt_div hp).mpr hlt)
  · intro a ha
    obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (a - 1) 1 := ⟨_, rfl⟩
    have hε0 : 0 < ε := by rw [hεdef]; exact lt_min (by linarith) one_pos
    have hε1 : ε ≤ 1 := by rw [hεdef]; exact min_le_right _ _
    have hεa : ε ≤ a - 1 := by rw [hεdef]; exact min_le_left _ _
    have hη0 : 0 < ε / 8 := by positivity
    obtain ⟨X, hX⟩ := eventually_atTop.mp
      (h.eventually (Ioo_mem_nhds (by linarith : 1 - ε / 8 < 1) (by linarith : 1 < 1 + ε / 8)))
    refine eventually_atTop.mpr ⟨⌈X⌉₊, fun n hn => ?_⟩
    have hp : (0 : ℝ) < fnPrimeAtRank n := by exact_mod_cast thm_primeAtRank_pos n
    have hpX : X ≤ fnPrimeAtRank n := by
      have h1 : (n : ℝ) ≤ fnPrimeAtRank n := by exact_mod_cast thm_primeAtRank_strictMono.id_le n
      have h2 : X ≤ ⌈X⌉₊ := Nat.le_ceil X
      have h3 : ((⌈X⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    by_contra hcon
    push Not at hcon
    have hratio : (1 + ε) * fnPrimeAtRank n ≤ fnPrimeAtRank (n + 1) := by
      have h1 : a * fnPrimeAtRank n ≤ fnPrimeAtRank (n + 1) := (le_div_iff₀ hp).mp hcon
      have h2 : (1 + ε) * fnPrimeAtRank n ≤ a * fnPrimeAtRank n :=
        mul_le_mul_of_nonneg_right (by linarith) hp.le
      linarith
    obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = (1 + ε / 2) * fnPrimeAtRank n := ⟨_, rfl⟩
    have hy1 : (fnPrimeAtRank n : ℝ) ≤ y := by rw [hydef]; nlinarith
    have hy2 : y < fnPrimeAtRank (n + 1) := by rw [hydef]; nlinarith
    have hy0 : 0 < y := lt_of_lt_of_le hp hy1
    have hθ := theta_eq_of_mem_gap n hy1 hy2
    obtain ⟨_, hA2⟩ := hX _ hpX
    obtain ⟨hB1, _⟩ := hX y (le_trans hpX hy1)
    rw [hθ] at hB1
    have h1 : Chebyshev.theta (fnPrimeAtRank n : ℝ) < (1 + ε / 8) * fnPrimeAtRank n :=
      (div_lt_iff₀ hp).mp hA2
    have h2 : (1 - ε / 8) * y < Chebyshev.theta (fnPrimeAtRank n : ℝ) := (lt_div_iff₀ hy0).mp hB1
    rw [hydef] at h2
    have key : 0 ≤ (fnPrimeAtRank n : ℝ) * ε * (4 - ε) :=
      mul_nonneg (mul_nonneg hp.le hε0.le) (by linarith)
    have h3 : (1 + ε / 8) * (fnPrimeAtRank n : ℝ) ≤ (1 - ε / 8) * ((1 + ε / 2) * fnPrimeAtRank n) := by
      nlinarith [key]
    linarith

/-! ## 4. Les écarts logarithmiques tendent vers zéro -/

/-- **Théorème** : l'asymptotique de Tchebychev entraîne l'hypothèse nommée de `SamplingFromLogGaps`. -/
theorem logGapsVanish_of_chebyshevAsymptotic (h : ChebyshevAsymptotic) : LogGapsVanish := by
  unfold LogGapsVanish
  have hr := (ratio_tendsto_one_of_chebyshevAsymptotic h).log one_ne_zero
  rw [Real.log_one] at hr
  refine hr.congr' (Eventually.of_forall fun n => ?_)
  have hp : (0 : ℝ) < fnPrimeAtRank n := by exact_mod_cast thm_primeAtRank_pos n
  have hq : (0 : ℝ) < fnPrimeAtRank (n + 1) := by exact_mod_cast thm_primeAtRank_pos (n + 1)
  exact Real.log_div hq.ne' hp.ne'

/-! ## 5. Composition : le chemin des zéros, sous l'interface exacte -/

/-- Sous l'asymptotique de Tchebychev, les rencontres échantillonnent les fréquences. -/
theorem meetingsSampleFrequencies_of_chebyshev (h : ChebyshevAsymptotic) :
    MeetingsSampleFrequencies :=
  meetingsSampleFrequencies_of_logGaps (logGapsVanish_of_chebyshevAsymptotic h)

/-- **Chemin des zéros** : asymptotique de Tchebychev, demande bornée aux rencontres et sommet atteint
donnent RH. -/
theorem riemannHypothesis_of_chebyshev_summit (h : ChebyshevAsymptotic)
    (hdem : DemandBoundedAtMeetings) (hsum : SummitAttained) : RiemannHypothesis :=
  riemannHypothesis_of_logGaps_summit (logGapsVanish_of_chebyshevAsymptotic h) hdem hsum

/-- La prémisse unique de la chaîne, sous les mêmes hypothèses nommées. -/
theorem expectedFrequencyRises_of_chebyshev_summit (h : ChebyshevAsymptotic)
    (hdem : DemandBoundedAtMeetings) (hsum : SummitAttained) : ExpectedFrequencyRises :=
  expectedFrequencyRises_iff_riemannHypothesis.mpr (riemannHypothesis_of_chebyshev_summit h hdem hsum)

/-- Sous l'asymptotique de Tchebychev et la demande bornée aux rencontres, un zéro à droite n'est jamais
en nombre fini. -/
theorem infinite_right_of_chebyshev (h : ChebyshevAsymptotic) (hdem : DemandBoundedAtMeetings)
    (hex : ∃ ρ : ExplicitIndex, 1 / 2 < (ρ : ℂ).re) :
    Set.Infinite {ρ : ExplicitIndex | 1 / 2 < (ρ : ℂ).re} :=
  infinite_right_of_logGaps (logGapsVanish_of_chebyshevAsymptotic h) hdem hex

end RHV6Fresh
