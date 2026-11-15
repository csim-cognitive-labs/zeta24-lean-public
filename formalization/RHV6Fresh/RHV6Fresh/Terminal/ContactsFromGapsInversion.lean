/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.BreakAmplitudeSequence

/-!
# Le chemin inverse : des écarts premiers aux contacts, puis au zéro par la formule tangentielle
(E449, §19.71, 2026-11-08)

Module isolé (non ajouté à `RHV6Fresh.lean`). Priorité de l'auteur du 2026-11-08 : reconstituer les contacts
depuis les écarts premiers avec les règles établies, retrouver `(β, T)` par la formule tangentielle. Le **mot**
d'une Tour sur les premiers est la suite des cellules `k(p_n) = lastContactBefore β T p_n` (combien de contacts
chaque écart contient). Une Tour à la fois, aucun objet spectral, aucune contradiction cherchée.

* L1 `phase_of_contact`, `log_contact_ratio`, `frequency_of_two_contacts`, `beta_of_phase`,
  `tower_of_two_contacts` : **formule tangentielle** — `T = π/log(C_{k+1}/C_k)`, `φ = T·log C_k − kπ`,
  `β = T/tan φ` : deux contacts consécutifs rendent la Tour exactement.
* L2 `stagePosition_mul_pi`, `phase_eq_word_sub_fraction`, `phase_bracket` : en tout point,
  `φ = T·log x − π(k(x) + f(x))` ; le mot seul encadre la phase dans une fenêtre de largeur `π`.
* L3 `lastContactBefore_div_log_tendsto`, `primes_tendsto_atTop`, `word_slope_tendsto` : **la fréquence
  d'abord** — `k(x)/log x → T/π`, en particulier le long des premiers.
* L4 `fract_small_and_near_one_of_steps`, `stagePosition_primes_tendsto_atTop`,
  `stagePosition_primes_step_tendsto_zero`, `cellFraction_primes_small_and_near_one` : **la cause** — les pas de
  l'orbite `T·log(p_{n+1}/p_n)/π` tendent vers `0` (`logGapsVanish_holds`, PNT porté) et la position d'étage est
  non bornée ; à chaque franchissement d'un entier la fraction est `< ε` juste après et `> 1 − ε` juste avant.
* L5 `frequency_eq_of_same_word`, `le_of_forall_lt_add_pi_mul`, `phase_le_of_same_word_same_frequency`,
  `phase_eq_of_same_word`, `beta_eq_of_phase_eq`, `tower_eq_of_same_word` : **le mot détermine la Tour** —
  deux Tours (`β, β' > 0`) de même mot sur tous les premiers ont même fréquence, même phase, donc même `β`.

Ce que ce module ne dit pas (consigné d'avance, H6) : tout vaut pour TOUTE Tour `(β, T)`, zéro ou non ; le chemin
inverse rend la Tour dont on a le mot, il ne dit pas pourquoi ce mot est celui d'un zéro.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune hypothèse, aucune somme de Tours, aucun objet spectral.
-/
namespace RHV6Fresh

open Real RHV3Lean Finset Filter Topology

/-! ## L1. La formule tangentielle : inversion exacte depuis deux contacts -/

theorem phase_of_contact {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    towerPhase β T = T * Real.log (contactAt β T k) - k * Real.pi := by
  rw [contactAt_eq, Real.log_exp]
  unfold towerPhase
  field_simp
  ring

theorem log_contact_ratio {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    Real.log (contactAt β T (k + 1) / contactAt β T k) = Real.pi / T := by
  rw [Real.log_div (contactAt_pos _ _ _).ne' (contactAt_pos _ _ _).ne', contactAt_eq, contactAt_eq,
    Real.log_exp, Real.log_exp]
  field_simp
  push_cast
  ring

theorem frequency_of_two_contacts {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    T = Real.pi / Real.log (contactAt β T (k + 1) / contactAt β T k) := by
  rw [log_contact_ratio hT k]
  field_simp

theorem beta_of_phase {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) :
    β = T / Real.tan (towerPhase β T) := by
  unfold towerPhase
  rw [Real.tan_arctan]
  field_simp

theorem tower_of_two_contacts {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (k : ℤ) :
    T = Real.pi / Real.log (contactAt β T (k + 1) / contactAt β T k) ∧
      β = T / Real.tan (T * Real.log (contactAt β T k) - k * Real.pi) := by
  refine ⟨frequency_of_two_contacts hT k, ?_⟩
  rw [← phase_of_contact hT k]
  exact beta_of_phase hβ hT

/-! ## L2. Chaque point encadre la phase ; identité exacte phase = mot + fraction -/

theorem stagePosition_mul_pi (β T x : ℝ) :
    stagePosition β T x * Real.pi = T * Real.log x - towerPhase β T := by
  unfold stagePosition towerPhase
  field_simp

theorem phase_eq_word_sub_fraction (β T x : ℝ) :
    towerPhase β T = T * Real.log x - Real.pi * (lastContactBefore β T x + cellFraction β T x) := by
  have h := stagePosition_mul_pi β T x
  rw [stagePosition_eq_last_add_fraction] at h
  linarith

theorem phase_bracket (β T x : ℝ) :
    T * Real.log x - Real.pi * (lastContactBefore β T x + 1) < towerPhase β T ∧
      towerPhase β T ≤ T * Real.log x - Real.pi * lastContactBefore β T x := by
  have hpi := Real.pi_pos
  have hs := stagePosition_mul_pi β T x
  have h1 := mul_le_mul_of_nonneg_right (Int.floor_le (stagePosition β T x)) hpi.le
  have h2 := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (stagePosition β T x)) hpi
  unfold lastContactBefore
  constructor <;> nlinarith

/-! ## L3. La fréquence d'abord : la pente du mot -/

theorem lastContactBefore_div_log_tendsto (β : ℝ) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun x : ℝ => (lastContactBefore β T x : ℝ) / Real.log x) atTop (𝓝 (T / Real.pi)) := by
  have hinv : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have h1 : Tendsto (fun x : ℝ => T / Real.pi - towerPhase β T / Real.pi * (Real.log x)⁻¹) atTop
      (𝓝 (T / Real.pi)) := by
    have := (tendsto_const_nhds (x := T / Real.pi)).sub (hinv.const_mul (towerPhase β T / Real.pi))
    simpa using this
  have h2 : Tendsto (fun x : ℝ => cellFraction β T x * (Real.log x)⁻¹) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hinv
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hl : 0 < (Real.log x)⁻¹ := inv_pos.mpr (Real.log_pos hx)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cellFraction_nonneg _ _ _), abs_of_pos hl]
    exact mul_le_of_le_one_left hl.le (cellFraction_lt_one _ _ _).le
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hpi := Real.pi_ne_zero
  have hk : (lastContactBefore β T x : ℝ) = stagePosition β T x - cellFraction β T x := by
    linarith [stagePosition_eq_last_add_fraction β T x]
  have hs : stagePosition β T x = (T * Real.log x - towerPhase β T) / Real.pi := by
    have := stagePosition_mul_pi β T x
    field_simp
    linarith
  rw [hk, hs]
  field_simp

theorem primes_tendsto_atTop : Tendsto (fun n : ℕ => (fnPrimeAtRank n : ℝ)) atTop atTop := by
  have hmono : StrictMono fnPrimeAtRank := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  exact tendsto_natCast_atTop_atTop.comp hmono.tendsto_atTop

theorem word_slope_tendsto (β : ℝ) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => (lastContactBefore β T (fnPrimeAtRank n : ℝ) : ℝ) / Real.log (fnPrimeAtRank n : ℝ))
      atTop (𝓝 (T / Real.pi)) :=
  (lastContactBefore_div_log_tendsto β hT).comp primes_tendsto_atTop

/-! ## L4. La cause : pas évanescents et position non bornée ⇒ la fraction approche 0 et 1 -/

theorem fract_small_and_near_one_of_steps {u : ℕ → ℝ} (hu : Tendsto u atTop atTop)
    (hstep : Tendsto (fun n => u (n + 1) - u n) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ n, Int.fract (u (n + 1)) < ε ∧ 1 - ε < Int.fract (u n) := by
  classical
  have hev : ∀ᶠ n in atTop, |u (n + 1) - u n| < ε := by
    have := (Metric.tendsto_nhds.mp hstep) ε hε
    filter_upwards [this] with n hn
    simpa [Real.dist_eq] using hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  set m : ℤ := ⌊u N⌋ + 1 with hm
  have hmN : u N < m := by rw [hm]; push_cast; exact Int.lt_floor_add_one _
  have hex : ∃ n, N ≤ n ∧ (m : ℝ) ≤ u n := by
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hu.eventually_ge_atTop (m : ℝ))
    exact ⟨max N n₀, le_max_left _ _, hn₀ _ (le_max_right _ _)⟩
  obtain ⟨n, hn, hmin⟩ : ∃ n, (N ≤ n ∧ (m : ℝ) ≤ u n) ∧ ∀ n' < n, ¬ (N ≤ n' ∧ (m : ℝ) ≤ u n') :=
    ⟨Nat.find hex, Nat.find_spec hex, fun n' h => Nat.find_min hex h⟩
  have hnN : N < n := by
    rcases hn.1.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hn; linarith [hn.2]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hn'N : N ≤ n' := by omega
  have hlt : u n' < m := by
    by_contra h
    push Not at h
    exact hmin n' (Nat.lt_succ_self n') ⟨hn'N, h⟩
  have hstepn := hN n' hn'N
  rw [abs_lt] at hstepn
  refine ⟨n', ?_, ?_⟩
  · have hfl : ⌊u (n' + 1)⌋ = m := by
      rw [Int.floor_eq_iff]
      exact ⟨hn.2, by push_cast; linarith⟩
    rw [← Int.self_sub_floor, hfl]
    linarith [hn.2]
  · have hfl : ⌊u n'⌋ = m - 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith [hn.2]
    rw [← Int.self_sub_floor, hfl]
    push_cast
    linarith [hn.2]

theorem stagePosition_primes_tendsto_atTop (β : ℝ) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => stagePosition β T (fnPrimeAtRank n : ℝ)) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log (fnPrimeAtRank n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp primes_tendsto_atTop
  have h1 := (hlog.const_mul_atTop hT)
  have h2 := tendsto_atTop_add_const_right atTop (-(Real.arctan (T / β))) h1
  have h3 := h2.atTop_div_const Real.pi_pos
  refine h3.congr (fun n => ?_)
  unfold stagePosition
  ring

theorem stagePosition_primes_step_tendsto_zero (β : ℝ) (T : ℝ) :
    Tendsto (fun n : ℕ => stagePosition β T (fnPrimeAtRank (n + 1) : ℝ) - stagePosition β T (fnPrimeAtRank n : ℝ))
      atTop (𝓝 0) := by
  have := logGapsVanish_holds.const_mul (T / Real.pi)
  rw [mul_zero] at this
  refine this.congr (fun n => ?_)
  unfold stagePosition
  ring

theorem cellFraction_primes_small_and_near_one (β : ℝ) {T : ℝ} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ n, cellFraction β T (fnPrimeAtRank (n + 1) : ℝ) < ε ∧ 1 - ε < cellFraction β T (fnPrimeAtRank n : ℝ) :=
  fract_small_and_near_one_of_steps (stagePosition_primes_tendsto_atTop β hT)
    (stagePosition_primes_step_tendsto_zero β T) hε hε1

/-! ## L5. Le mot détermine la Tour : fréquence, puis phase, puis β -/

theorem frequency_eq_of_same_word {β β' T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (hw : ∀ n : ℕ, lastContactBefore β T (fnPrimeAtRank n : ℝ) = lastContactBefore β' T' (fnPrimeAtRank n : ℝ)) :
    T = T' := by
  have h1 := word_slope_tendsto β hT
  have h2 := word_slope_tendsto β' hT'
  have h2' : Tendsto (fun n : ℕ => (lastContactBefore β T (fnPrimeAtRank n : ℝ) : ℝ) / Real.log (fnPrimeAtRank n : ℝ))
      atTop (𝓝 (T' / Real.pi)) := by
    refine h2.congr (fun n => ?_)
    rw [hw n]
  have := tendsto_nhds_unique h1 h2'
  have hpi := Real.pi_pos
  field_simp at this
  linarith

theorem le_of_forall_lt_add_pi_mul {a b : ℝ} (h : ∀ ε : ℝ, 0 < ε → ε < 1 → a < b + Real.pi * ε) : a ≤ b := by
  by_contra hab
  push Not at hab
  set δ := (a - b) / Real.pi with hδdef
  have hδ : 0 < δ := div_pos (by linarith) Real.pi_pos
  have hε := h (min (δ / 2) (1 / 2)) (lt_min (by positivity) (by norm_num))
    (by linarith [min_le_right (δ / 2) (1 / 2)])
  have h1 : Real.pi * min (δ / 2) (1 / 2) ≤ Real.pi * (δ / 2) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) Real.pi_pos.le
  have h2 : Real.pi * (δ / 2) = (a - b) / 2 := by
    rw [hδdef]; field_simp
  linarith

theorem phase_le_of_same_word_same_frequency {β β' T : ℝ} (hT : 0 < T)
    (hw : ∀ n : ℕ, lastContactBefore β T (fnPrimeAtRank n : ℝ) = lastContactBefore β' T (fnPrimeAtRank n : ℝ)) :
    towerPhase β' T ≤ towerPhase β T := by
  apply le_of_forall_lt_add_pi_mul
  intro ε hε hε1
  obtain ⟨n, hn, -⟩ := cellFraction_primes_small_and_near_one β hT hε hε1
  have h1 := phase_eq_word_sub_fraction β T (fnPrimeAtRank (n + 1) : ℝ)
  have h2 := (phase_bracket β' T (fnPrimeAtRank (n + 1) : ℝ)).2
  rw [← hw (n + 1)] at h2
  have hpi := Real.pi_pos
  nlinarith

theorem phase_eq_of_same_word {β β' T : ℝ} (hT : 0 < T)
    (hw : ∀ n : ℕ, lastContactBefore β T (fnPrimeAtRank n : ℝ) = lastContactBefore β' T (fnPrimeAtRank n : ℝ)) :
    towerPhase β T = towerPhase β' T :=
  le_antisymm (phase_le_of_same_word_same_frequency hT (fun n => (hw n).symm))
    (phase_le_of_same_word_same_frequency hT hw)

theorem beta_eq_of_phase_eq {β β' T : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (hT : 0 < T)
    (h : towerPhase β T = towerPhase β' T) : β = β' := by
  unfold towerPhase at h
  have h2 := Real.arctan_injective h
  field_simp at h2
  nlinarith

theorem tower_eq_of_same_word {β β' T T' : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (hT : 0 < T) (hT' : 0 < T')
    (hw : ∀ n : ℕ, lastContactBefore β T (fnPrimeAtRank n : ℝ) = lastContactBefore β' T' (fnPrimeAtRank n : ℝ)) :
    T = T' ∧ β = β' := by
  have hTT := frequency_eq_of_same_word hT hT' hw
  subst hTT
  exact ⟨rfl, beta_eq_of_phase_eq hβ hβ' hT (phase_eq_of_same_word hT hw)⟩

#print axioms phase_of_contact
#print axioms log_contact_ratio
#print axioms frequency_of_two_contacts
#print axioms beta_of_phase
#print axioms tower_of_two_contacts
#print axioms stagePosition_mul_pi
#print axioms phase_eq_word_sub_fraction
#print axioms phase_bracket
#print axioms lastContactBefore_div_log_tendsto
#print axioms primes_tendsto_atTop
#print axioms word_slope_tendsto
#print axioms fract_small_and_near_one_of_steps
#print axioms stagePosition_primes_tendsto_atTop
#print axioms stagePosition_primes_step_tendsto_zero
#print axioms cellFraction_primes_small_and_near_one
#print axioms frequency_eq_of_same_word
#print axioms le_of_forall_lt_add_pi_mul
#print axioms phase_le_of_same_word_same_frequency
#print axioms phase_eq_of_same_word
#print axioms beta_eq_of_phase_eq
#print axioms tower_eq_of_same_word

end RHV6Fresh
