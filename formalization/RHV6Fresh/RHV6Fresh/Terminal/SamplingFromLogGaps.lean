/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.SummitAttained
import RHV6Fresh.Terminal.MeetingsBridge
import RHV6Fresh.Terminal.FiniteRadialRigidity

/-!
# L'échantillonnage dérivé (module isolé, non importé par la chaîne)

Solution 2 du maître §16.7 (validée par l'auteur le 2026-10-29). Objet : dériver l'hypothèse nommée
d'échantillonnage (`MeetingsSampleFrequencies`, `MeetingSampling.lean`) de faits compilés et d'une seule
hypothèse nommée sur les premiers.

**Correction au maître §16.7, dite avant d'écrire** : le maître parlait d'« équirépartition des logarithmes
des premiers ». Ce n'est pas le bon énoncé : les logarithmes des premiers ne sont pas équirépartis modulo un
(pas plus que ceux des entiers). Ce qui sert est plus faible et plus précis : le polynôme de fréquences ne
tend pas vers zéro en variable continue (compilé : `trig_poly_not_tendsto_zero`, `FiniteRadialRigidity.lean`),
il est lipschitzien (compilé ici), et les écarts LOGARITHMIQUES entre premiers consécutifs tendent vers zéro
(`LogGapsVanish`, hypothèse nommée : le rapport de deux premiers consécutifs tend vers un ; force du théorème
des nombres premiers, absent de Mathlib ; Bertrand ne donne que « au plus log 2 »).

Ce qui est compilé :

1. le polynôme de fréquences d'une famille est un polynôme trigonométrique en `log x`
   (`topPolynomial_eq_trigPoly`), à fréquences distinctes sur une famille de même position radiale
   (`frequencies_injective`) et à coefficients non nuls (`memberCoefficient_ne_zero`) ;
2. il ne tend pas vers zéro : à toute borne de la variable, un point au-delà où il dépasse un seuil fixe
   (`exists_large_beyond`) ;
3. il est lipschitzien en la variable (`trigPoly_lipschitz`) ;
4. sous `LogGapsVanish`, toute fenêtre de longueur fixe assez loin contient une rencontre
   (`exists_meeting_in_window`) ;
5. donc **l'échantillonnage est dérivé** (`meetingsSampleFrequencies_of_logGaps`).

Conséquence, en composant avec les modules précédents : sous `LogGapsVanish`, l'hypothèse de clôture et le
sommet atteint donnent RH (`riemannHypothesis_of_logGaps_summit`). Aucun axiome, aucun `sorry`.
-/

namespace RHV6Fresh

open Complex RHV3Lean Filter Topology FiniteRadialRigidity

/-! ## 1. Le polynôme de fréquences est un polynôme trigonométrique en `log x` -/

/-- Coefficients d'une famille, indexés par la famille. -/
noncomputable def familyCoefficients (A : Finset ExplicitIndex) : A → ℂ :=
  fun σ => memberCoefficient σ

/-- Fréquences d'une famille, indexées par la famille : les parties imaginaires. -/
noncomputable def familyFrequencies (A : Finset ExplicitIndex) : A → ℝ :=
  fun σ => ((σ : ExplicitIndex) : ℂ).im

open Classical in
/-- Le polynôme trigonométrique d'une famille, en la variable `u = log x`. -/
noncomputable def familyTrigPoly (A : Finset ExplicitIndex) (u : ℝ) : ℂ :=
  trigPoly (familyCoefficients A) (familyFrequencies A) u

open Classical in
/-- Constante de Lipschitz d'une famille. -/
noncomputable def familyLipschitz (A : Finset ExplicitIndex) : ℝ :=
  ∑ j : A, ‖familyCoefficients A j‖ * |familyFrequencies A j|

/-- Le polynôme de fréquences, lu en `u = log x`, est le polynôme trigonométrique de la famille. -/
theorem topPolynomial_eq_trigPoly (A : Finset ExplicitIndex) (x : ℝ) :
    topPolynomial A x = familyTrigPoly A (Real.log x) := by
  unfold topPolynomial familyTrigPoly trigPoly familyCoefficients familyFrequencies
  rw [← Finset.sum_coe_sort A]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 2
  ring

/-- Sur une famille de même position radiale, les fréquences sont distinctes. -/
theorem frequencies_injective (A : Finset ExplicitIndex) (b : ℝ) (hAb : ∀ σ ∈ A, (σ : ℂ).re = b) :
    Function.Injective (familyFrequencies A) := by
  intro σ τ h
  apply Subtype.ext
  apply Subtype.ext
  apply Complex.ext
  · rw [hAb σ σ.2, hAb τ τ.2]
  · exact h

/-- Le coefficient d'un indice n'est jamais nul. -/
theorem memberCoefficient_ne_zero (σ : ExplicitIndex) : memberCoefficient σ ≠ 0 := by
  unfold memberCoefficient
  refine mul_ne_zero (div_ne_zero ?_ ?_) (Complex.exp_ne_zero _)
  · have := zetaZeroMultiplicity_pos σ.property.1
    exact neg_ne_zero.mpr (by exact_mod_cast this.ne')
  · exact_mod_cast (indexDenominator_pos σ).ne'

/-! ## 2. Il ne tend pas vers zéro et il est lipschitzien -/

open Classical in
/-- À toute borne, un point au-delà où le polynôme de fréquences dépasse un seuil fixe. -/
theorem exists_large_beyond (A : Finset ExplicitIndex) (b : ℝ) (hA : A.Nonempty)
    (hAb : ∀ σ ∈ A, (σ : ℂ).re = b) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ U : ℝ, ∃ u : ℝ, U ≤ u ∧
      ε ≤ ‖familyTrigPoly A u‖ := by
  obtain ⟨σ₀, hσ₀⟩ := hA
  have hnot := trig_poly_not_tendsto_zero (familyCoefficients A)
    (frequencies_injective A b hAb) ⟨⟨σ₀, hσ₀⟩, memberCoefficient_ne_zero σ₀⟩
  rw [Metric.tendsto_atTop] at hnot
  push Not at hnot
  obtain ⟨ε, hε, h⟩ := hnot
  refine ⟨ε, hε, fun U => ?_⟩
  obtain ⟨u, hu, hd⟩ := h U
  refine ⟨u, hu, ?_⟩
  rw [dist_zero_right] at hd
  exact hd

/-- Constante de Lipschitz du polynôme : somme des modules des coefficients fois les fréquences. -/
noncomputable def lipschitzConstant {ι : Type*} [Fintype ι] (c : ι → ℂ) (T : ι → ℝ) : ℝ :=
  ∑ j, ‖c j‖ * |T j|

/-- **Le polynôme trigonométrique est lipschitzien.** -/
theorem trigPoly_lipschitz {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ) (T : ι → ℝ)
    (u v : ℝ) : ‖trigPoly c T u - trigPoly c T v‖ ≤ lipschitzConstant c T * |u - v| := by
  unfold trigPoly lipschitzConstant
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hsplit : c j * Complex.exp (I * ((T j : ℂ) * u)) - c j * Complex.exp (I * ((T j : ℂ) * v)) =
      c j * Complex.exp (I * ((T j * v : ℝ) : ℂ)) *
        (Complex.exp (I * ((T j * (u - v) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, mul_assoc, ← Complex.exp_add]
    congr 2
    · push_cast; ring
    · push_cast; ring
  rw [hsplit, norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  calc ‖c j‖ * ‖Complex.exp (I * ((T j * (u - v) : ℝ) : ℂ)) - 1‖
      ≤ ‖c j‖ * ‖T j * (u - v)‖ :=
        mul_le_mul_of_nonneg_left Real.norm_exp_I_mul_ofReal_sub_one_le (norm_nonneg _)
    _ = ‖c j‖ * |T j| * |u - v| := by rw [Real.norm_eq_abs, abs_mul, mul_assoc]

/-- Le polynôme d'une famille est lipschitzien, de constante `familyLipschitz`. -/
theorem familyTrigPoly_lipschitz (A : Finset ExplicitIndex) (u v : ℝ) :
    ‖familyTrigPoly A u - familyTrigPoly A v‖ ≤ familyLipschitz A * |u - v| := by
  unfold familyTrigPoly familyLipschitz
  exact trigPoly_lipschitz _ _ u v

theorem familyLipschitz_nonneg (A : Finset ExplicitIndex) : 0 ≤ familyLipschitz A := by
  unfold familyLipschitz
  exact Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)

/-! ## 3. Les écarts logarithmiques tendent vers zéro : hypothèse nommée -/

/-- **Hypothèse nommée (jamais posée)** : les écarts logarithmiques entre premiers consécutifs tendent vers
zéro, c'est-à-dire le rapport de deux premiers consécutifs tend vers un. Vrai par le théorème des nombres
premiers ; absent de Mathlib. -/
def LogGapsVanish : Prop :=
  Tendsto (fun n : ℕ => Real.log (fnPrimeAtRank (n + 1)) - Real.log (fnPrimeAtRank n)) atTop (𝓝 0)

/-- Sous l'hypothèse nommée : tout point `u` assez loin a une rencontre dans `]u, u + η]`, de rang au-delà
de tout rang donné. -/
theorem exists_meeting_in_window (h : LogGapsVanish) {η : ℝ} (hη : 0 < η) (n₀ : ℕ) :
    ∃ U : ℝ, ∀ u : ℝ, U ≤ u → ∃ k : ℕ, n₀ ≤ k ∧
      u < Real.log (meetingPoint ⟨k⟩) ∧ Real.log (meetingPoint ⟨k⟩) ≤ u + η := by
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (h.eventually (Iio_mem_nhds hη))
  refine ⟨Real.log (fnPrimeAtRank (max n₀ n₁ + 1)), fun u hu => ?_⟩
  have hp0 : (0 : ℝ) < fnPrimeAtRank 0 := by exact_mod_cast (thm_primeAtRank_isPrime 0).pos
  have hpm : (0 : ℝ) < fnPrimeAtRank (max n₀ n₁ + 1) := by
    exact_mod_cast (thm_primeAtRank_isPrime _).pos
  have hx0 : (fnPrimeAtRank 0 : ℝ) ≤ Real.exp u := by
    have h1 : (fnPrimeAtRank 0 : ℝ) ≤ fnPrimeAtRank (max n₀ n₁ + 1) := by
      exact_mod_cast thm_primeAtRank_strictMono.monotone (Nat.zero_le _)
    calc (fnPrimeAtRank 0 : ℝ) ≤ fnPrimeAtRank (max n₀ n₁ + 1) := h1
      _ = Real.exp (Real.log (fnPrimeAtRank (max n₀ n₁ + 1))) := (Real.exp_log hpm).symm
      _ ≤ Real.exp u := Real.exp_le_exp.mpr hu
  obtain ⟨k, hk1, hk2⟩ := exists_rank_le_lt hx0
  -- `k` est au-delà de `max n₀ n₁`
  have hkge : max n₀ n₁ + 1 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : fnPrimeAtRank (k + 1) ≤ fnPrimeAtRank (max n₀ n₁ + 1) :=
      thm_primeAtRank_strictMono.monotone (by omega)
    have h' : (fnPrimeAtRank (k + 1) : ℝ) ≤ fnPrimeAtRank (max n₀ n₁ + 1) := by exact_mod_cast this
    have h'' : (fnPrimeAtRank (max n₀ n₁ + 1) : ℝ) ≤ Real.exp u := by
      calc (fnPrimeAtRank (max n₀ n₁ + 1) : ℝ)
          = Real.exp (Real.log (fnPrimeAtRank (max n₀ n₁ + 1))) := (Real.exp_log hpm).symm
        _ ≤ Real.exp u := Real.exp_le_exp.mpr hu
    linarith
  have hpk : (0 : ℝ) < fnPrimeAtRank k := by exact_mod_cast (thm_primeAtRank_isPrime k).pos
  have hpk1 : (0 : ℝ) < fnPrimeAtRank (k + 1) := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  refine ⟨k, by omega, ?_, ?_⟩
  · change u < Real.log (fnPrimeAtRank (k + 1) : ℝ)
    rw [← Real.log_exp u]
    exact Real.log_lt_log (Real.exp_pos u) hk2
  · change Real.log (fnPrimeAtRank (k + 1) : ℝ) ≤ u + η
    have hgap := hn₁ k (by omega)
    have hlk : Real.log (fnPrimeAtRank k : ℝ) ≤ u := by
      rw [← Real.log_exp u]
      exact Real.log_le_log hpk hk1
    linarith

/-! ## 4. L'échantillonnage est dérivé -/

/-- **Théorème** : sous la seule hypothèse nommée `LogGapsVanish`, les rencontres échantillonnent les
fréquences : pour toute famille finie non vide de même position radiale, le polynôme de fréquences dépasse
un seuil fixe en des rencontres de rang arbitrairement grand. -/
theorem meetingsSampleFrequencies_of_logGaps (h : LogGapsVanish) : MeetingsSampleFrequencies := by
  intro A b hA hAb
  obtain ⟨ε, hε, hbig⟩ := exists_large_beyond A b hA hAb
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = familyLipschitz A + 1 := ⟨_, rfl⟩
  have hL0 := familyLipschitz_nonneg A
  have hM0 : 0 < M := by linarith
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / (2 * M) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  refine ⟨ε / 2, by positivity, fun n₀ => ?_⟩
  obtain ⟨U, hU⟩ := exists_meeting_in_window h hη0 n₀
  obtain ⟨u, hu, hPu⟩ := hbig U
  obtain ⟨k, hk, hk1, hk2⟩ := hU u hu
  refine ⟨k, hk, ?_⟩
  rw [topPolynomial_eq_trigPoly]
  have hlip := familyTrigPoly_lipschitz A (Real.log (meetingPoint ⟨k⟩)) u
  have habs : |Real.log (meetingPoint ⟨k⟩) - u| ≤ η := by
    rw [abs_of_pos (by linarith)]
    linarith
  have hMη : M * η = ε / 2 := by
    rw [hη, mul_div_assoc', mul_comm M ε, mul_div_mul_right ε 2 hM0.ne']
  have hL : familyLipschitz A * |Real.log (meetingPoint ⟨k⟩) - u| ≤ ε / 2 := by
    calc familyLipschitz A * |Real.log (meetingPoint ⟨k⟩) - u|
        ≤ M * η := mul_le_mul (by linarith) habs (abs_nonneg _) hM0.le
      _ = ε / 2 := hMη
  have htri := norm_sub_norm_le (familyTrigPoly A u) (familyTrigPoly A (Real.log (meetingPoint ⟨k⟩)))
  rw [norm_sub_rev] at htri
  linarith

/-! ## 5. Composition : ce qui ferme sous les hypothèses nommées -/

/-- Sous `LogGapsVanish`, l'hypothèse de clôture et le sommet atteint donnent RH. -/
theorem riemannHypothesis_of_logGaps_summit (h : LogGapsVanish) (hdem : DemandBoundedAtMeetings)
    (hsum : SummitAttained) : RiemannHypothesis :=
  riemannHypothesis_of_summitAttained (meetingsSampleFrequencies_of_logGaps h) hdem hsum

/-- Sous `LogGapsVanish`, un zéro à droite n'est jamais en nombre fini, sous demande bornée. -/
theorem infinite_right_of_logGaps (h : LogGapsVanish) (hdem : DemandBoundedAtMeetings)
    (hex : ∃ ρ : ExplicitIndex, 1 / 2 < (ρ : ℂ).re) :
    Set.Infinite {ρ : ExplicitIndex | 1 / 2 < (ρ : ℂ).re} :=
  infinite_right_of_sampling (meetingsSampleFrequencies_of_logGaps h) hdem hex

end RHV6Fresh
