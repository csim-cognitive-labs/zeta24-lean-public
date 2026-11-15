/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GrammarKinematics
import RHV6Fresh.Terminal.ExactAxisReading
import RHV6Fresh.Terminal.CompensationRigidity

/-!
# RHV6Fresh — la grammaire première comme suite de sollicitations : mots, canaux, dette miroir (E157, auteur, 2026-10-03)

Proposition de l'auteur : la grammaire ne fixe pas la position radiale, mais elle fixe la succession structurée des
sollicitations auxquelles la position radiale répond. Entrée grammaticale exacte d'un événement : la magnitude
`a = g / 6` et la transition d'état (A = `6k − 1`, B = `6k + 1`), de classe `r = g % 6`.

* **Attentes exactes à deux pas** (§1) : deux changements d'état consécutifs avancent exactement de
  `6(a_n + a_{n+1} + 1)` (`alternating_two_step_gap`), ce qui précise le plancher compilé `p_{n+2} ≥ p_n + 6` ;
  retour à l'état de départ ⟺ l'avance à deux pas est multiple de `6` (`state_return_iff_two_step_mod6`).
* **Verrou des canaux AB et BA** (§2) : sur toute fenêtre de transitions, le nombre de passages A → B moins le nombre de
  passages B → A ne dépend que des états des deux extrémités (`ab_ba_channel_lock`), donc vaut `−1`, `0` ou `1`
  (`ab_ba_channel_lock_abs_le_one`), en particulier sur la suite des premiers (`prime_ab_ba_channel_lock`).
* **Dette miroir sur un mot** (§3) : sur tout mot de la grammaire, l'écart des réponses énergétiques des deux membres
  d'une paire miroir de profondeur `d` est `4d` fois le logarithme du rapport des extrémités
  (`mirror_word_energy_debt`) ; sur deux changements consécutifs il vaut `4d·log(1 + 6(a_n + a_{n+1} + 1)/p_n)`
  (`alternating_two_step_mirror_debt`), strictement positif ⟺ `d ≠ 0` sur un pas croissant (`mirror_word_debt_pos_iff`).

Borne : ce sont des identités ; la dette d'un mot est fixée par ses extrémités (télescopage, la structure interne du
mot n'y entre pas), elle est proportionnelle à la profondeur et tend vers `0` avec elle ; la grammaire est une fonction
des positions des premiers seules, identique dans tout monde de même support (témoin `ζ(s−δ)ζ(s+δ)`, signes
cohérents) ; elle ne fixe pas l'exposant du reste. Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Real RHV3Lean Finset

/-! ## 1. Attentes exactes à deux pas -/

/-- **Deux changements d'état consécutifs** : l'avance à deux pas vaut exactement `6(a_n + a_{n+1} + 1)`. -/
theorem alternating_two_step_gap {p q r : ℕ} (hp : GoodMod6 p) (hq : GoodMod6 q) (hr : GoodMod6 r)
    (hpq : p ≤ q) (hqr : q ≤ r) (h1 : gapClass6 p q ≠ 0) (h2 : gapClass6 q r ≠ 0) :
    r - p = 6 * ((q - p) / 6 + (r - q) / 6 + 1) := by
  unfold GoodMod6 at hp hq hr
  unfold gapClass6 at h1 h2
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rcases hr with hr | hr <;> omega

/-- **Retour à l'état de départ** ⟺ l'avance à deux pas (ou sur toute fenêtre) est multiple de `6`. -/
theorem state_return_iff_two_step_mod6 {p r : ℕ} (hp : GoodMod6 p) (hr : GoodMod6 r) (hpr : p ≤ r) :
    state6 r = state6 p ↔ (r - p) % 6 = 0 := by
  unfold GoodMod6 at hp hr
  unfold state6
  rcases hp with hp | hp <;> rcases hr with hr | hr <;> simp [hp, hr] <;> omega

/-! ## 2. Verrou des canaux AB et BA -/

/-- Indicatrice entière d'un état `B`. -/
def stateIndicator (b : Bool) : ℤ := if b then 1 else 0

/-- Passage A → B (classe `2`) moins passage B → A (classe `4`) sur une transition. -/
def abMinusBa (b b' : Bool) : ℤ := (if b = false ∧ b' = true then 1 else 0) - (if b = true ∧ b' = false then 1 else 0)

theorem abMinusBa_eq (b b' : Bool) : abMinusBa b b' = stateIndicator b' - stateIndicator b := by
  cases b <;> cases b' <;> rfl

/-- **Verrou des canaux** : sur toute fenêtre, (nombre de A → B) − (nombre de B → A) ne dépend que des états des deux
extrémités. -/
theorem ab_ba_channel_lock (s : ℕ → Bool) (m : ℕ) :
    ∑ i ∈ range m, abMinusBa (s i) (s (i + 1)) = stateIndicator (s m) - stateIndicator (s 0) := by
  simp_rw [abMinusBa_eq]
  exact Finset.sum_range_sub (fun i => stateIndicator (s i)) m

/-- **Les effectifs des canaux AB et BA diffèrent d'au plus une unité sur toute fenêtre.** -/
theorem ab_ba_channel_lock_abs_le_one (s : ℕ → Bool) (m : ℕ) :
    |∑ i ∈ range m, abMinusBa (s i) (s (i + 1))| ≤ 1 := by
  rw [ab_ba_channel_lock]
  unfold stateIndicator
  split_ifs <;> simp

/-- **Sur la suite des premiers**, à partir de tout rang. -/
theorem prime_ab_ba_channel_lock (n₀ m : ℕ) :
    |∑ i ∈ range m, abMinusBa (state6 (fnPrimeAtRank (n₀ + i))) (state6 (fnPrimeAtRank (n₀ + (i + 1))))| ≤ 1 :=
  ab_ba_channel_lock_abs_le_one (fun i => state6 (fnPrimeAtRank (n₀ + i))) m

/-! ## 3. Dette miroir sur un mot de la grammaire -/

/-- **Dette miroir sur un mot** : écart des réponses énergétiques `2β·g` des membres `1/2 + d` et `1/2 − d`, sommé sur
le mot, `= 4d·log(q_m/q_0)` ; la structure interne du mot n'y entre pas. -/
theorem mirror_word_energy_debt (d : ℝ) (q : ℕ → ℝ) (m : ℕ) (h0 : 0 < q 0) (hm : 0 < q m) :
    ∑ i ∈ range m, (2 * (1 / 2 + d) - 2 * (1 / 2 - d)) * (Real.log (q (i + 1)) - Real.log (q i)) =
      4 * d * Real.log (q m / q 0) := by
  rw [chain_reading_telescopes, Real.log_div hm.ne' h0.ne']
  ring

/-- **Sur deux changements d'état consécutifs**, la dette miroir vaut `4d·log(1 + 6(a_n + a_{n+1} + 1)/p_n)`. -/
theorem alternating_two_step_mirror_debt (d : ℝ) {p q r : ℕ} (hp : GoodMod6 p) (hq : GoodMod6 q)
    (hr : GoodMod6 r) (hp0 : 0 < p) (hpq : p ≤ q) (hqr : q ≤ r) (h1 : gapClass6 p q ≠ 0)
    (h2 : gapClass6 q r ≠ 0) :
    4 * d * Real.log ((r : ℝ) / p) =
      4 * d * Real.log (1 + 6 * (((q - p) / 6 + (r - q) / 6 + 1 : ℕ) : ℝ) / p) := by
  have h := alternating_two_step_gap hp hq hr hpq hqr h1 h2
  have hpr : p ≤ r := hpq.trans hqr
  have hc : (r : ℝ) = p + 6 * (((q - p) / 6 + (r - q) / 6 + 1 : ℕ) : ℝ) := by
    generalize (q - p) / 6 + (r - q) / 6 + 1 = k at h ⊢
    have : r = p + 6 * k := by omega
    rw [this]; push_cast; ring
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
  congr 2
  rw [hc]; field_simp

/-- **La dette d'un pas croissant est non nulle ⟺ la profondeur est non nulle.** -/
theorem mirror_word_debt_pos_iff (d : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    4 * d * Real.log (b / a) ≠ 0 ↔ d ≠ 0 := by
  have hl : 0 < Real.log (b / a) := Real.log_pos ((one_lt_div ha).2 hab)
  constructor
  · intro h hd; exact h (by rw [hd]; ring)
  · intro hd; exact mul_ne_zero (mul_ne_zero (by norm_num) hd) hl.ne'

end RHV6Fresh
