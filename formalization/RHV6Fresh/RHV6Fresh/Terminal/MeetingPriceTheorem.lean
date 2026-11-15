/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.AmplitudeSignedBalance

/-!
# Le Théorème du Prix au point de rencontre : partie compilable (E445, §19.65, 2026-11-07)

Module isolé (non ajouté à `RHV6Fresh.lean`). Plan de l'auteur (§19.65) : le facteur `x^{β−1/2}` est l'écart radial
d'amplitude entre une Tour OFF et une Tour ON ; les contacts l'identifient ; au point de rencontre l'amplitude est
imposée par le zéro ; le prix doit être confronté au budget fini de la constellation. Ici, ce qui se compile sans
hypothèse : une Tour `(β, T)`, sa paire `(1−β, T)` en amplitudes réelles, ses contacts, ses valeurs, ses cellules.

* P1 `offPrice β x = cosh((β − 1/2) log x)` ; `x^β + x^{1−β} = 2 x^{1/2} · offPrice β x` (`pair_amplitude_eq_price`) :
  le prix exact de la paire contre deux Tours ON de même fréquence.
* P2 `offPrice_ge_one`, `offPrice_ge_quadratic`, `offPrice_unbounded` : prix `≥ 1 + ((β−1/2) log x)²/2`, non borné
  dès que `β ≠ 1/2`.
* P3 `offPrice_of_meeting_values` : le prix est identifié par deux valeurs aux rencontres (`radial_of_meeting_values`).
* P4 `meeting_value_bounds` : `p^β e^{−βπ/T}/‖ρ‖ < |v_{rencontre}| ≤ p^β/‖ρ‖` : l'amplitude à la cellule de
  rencontre est imposée par `(β, T)` à un facteur `e^{βπ/T}` près.
* P5 `valueCellSum_abs_le` (réponse à la question §19.64) : si toutes les pentes de cellule sont bornées par `D`,
  `|valueCellSum| ≤ |v_dernière| · D · q/(q−1)`, `q = e^{βπ/T}` : le bilan pondéré est une quantité de dernière cellule.
* P6 `price_beats_budget` : `K log x < x^r` pour `x` assez grand (`r > 0`) : le prix d'une paire OFF bat le budget
  `log p` d'une rencontre.

Les trois tentatives de fermeture (confrontation au budget collectif) sont dans
`experiments/E445_MeetingPrice/attempts/` avec la sortie exacte du compilateur ; aucune n'est ici.
Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/
namespace RHV6Fresh

open Real RHV3Lean Finset Filter

/-! ## P1. Le prix exact de la paire contre deux Tours ON -/

/-- Prix radial d'une paire `(β, 1−β)` au point `x` : `cosh((β − 1/2) log x)`. -/
noncomputable def offPrice (β x : ℝ) : ℝ := Real.cosh ((β - 1 / 2) * Real.log x)

theorem pair_amplitude_eq_price {β x : ℝ} (hx : 0 < x) :
    x ^ β + x ^ (1 - β) = 2 * x ^ (1 / 2 : ℝ) * offPrice β x := by
  unfold offPrice
  rw [Real.cosh_eq, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx]
  have e1 : Real.log x * β = Real.log x * (1 / 2) + (β - 1 / 2) * Real.log x := by ring
  have e2 : Real.log x * (1 - β) = Real.log x * (1 / 2) + -((β - 1 / 2) * Real.log x) := by ring
  rw [e1, e2, Real.exp_add, Real.exp_add]
  ring

/-! ## P2. Le prix vaut au moins un, et n'est pas borné dès que `β ≠ 1/2` -/

theorem offPrice_ge_one (β x : ℝ) : 1 ≤ offPrice β x := Real.one_le_cosh _

theorem offPrice_ge_quadratic (β x : ℝ) :
    1 + ((β - 1 / 2) * Real.log x) ^ 2 / 2 ≤ offPrice β x := by
  have := two_cosh_sub_one_ge_sq (β - 1 / 2) (Real.log x)
  unfold offPrice
  linarith

theorem offPrice_unbounded {β : ℝ} (hβ : β ≠ 1 / 2) (K : ℝ) : ∃ x : ℝ, 1 < x ∧ K < offPrice β x := by
  have hd : 0 < |β - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hβ)
  refine ⟨Real.exp ((2 * |K| + 1) / |β - 1 / 2|), ?_, ?_⟩
  · rw [Real.one_lt_exp_iff]; positivity
  · have h := offPrice_ge_quadratic β (Real.exp ((2 * |K| + 1) / |β - 1 / 2|))
    rw [Real.log_exp] at h
    have hsq : ((β - 1 / 2) * ((2 * |K| + 1) / |β - 1 / 2|)) ^ 2 = (2 * |K| + 1) ^ 2 := by
      rw [mul_pow, div_pow, ← sq_abs (β - 1 / 2)]
      field_simp
      rw [div_self (abs_ne_zero.mpr (by intro h; apply hβ; linarith))]
    rw [hsq] at h
    have := le_abs_self K
    nlinarith [abs_nonneg K]

/-! ## P3. Le prix est identifié par les valeurs aux rencontres -/

theorem offPrice_of_meeting_values {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (n j : ℕ)
    (hj : 0 < meetingOffset β T n j) (x : ℝ) :
    offPrice β x = Real.cosh ((T * Real.log (|contactRealValue β T (meetingCell β T ⟨n + j⟩)| /
      |contactRealValue β T (meetingCell β T ⟨n⟩)|) / (meetingOffset β T n j * Real.pi) - 1 / 2) * Real.log x) := by
  unfold offPrice
  rw [← radial_of_meeting_values hβ hT n j hj]

/-! ## P4. L'amplitude à la cellule de rencontre est imposée par le zéro -/

theorem meeting_value_bounds {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (I : PrimeGapInterval) :
    I.upper ^ β * Real.exp (-(β * Real.pi / T)) / ‖(⟨β, T⟩ : ℂ)‖ <
        |contactRealValue β T (meetingCell β T I)| ∧
      |contactRealValue β T (meetingCell β T I)| ≤ I.upper ^ β / ‖(⟨β, T⟩ : ℂ)‖ := by
  have hu : 0 < I.upper := by linarith [I.one_lt_upper]
  have hle := lastContact_le (β := β) hT hu
  have hlt := lt_contact_succ (β := β) hT hu
  rw [abs_contactRealValue hβ]
  have hn := norm_mk_pos (T := T) hβ
  unfold meetingCell
  constructor
  · apply div_lt_div_of_pos_right _ hn
    have hC : contactAt β T (lastContactBefore β T I.upper + 1) =
        contactAt β T (lastContactBefore β T I.upper) * Real.exp (Real.pi / T) := by
      have := contactAt_ratio (β := β) hT.ne' (lastContactBefore β T I.upper)
      rw [div_eq_iff (contactAt_pos β T _).ne'] at this
      rw [this, mul_comm]
    rw [hC] at hlt
    have hpos := contactAt_pos β T (lastContactBefore β T I.upper)
    have h1 : I.upper * Real.exp (-(Real.pi / T)) < contactAt β T (lastContactBefore β T I.upper) := by
      rw [Real.exp_neg]
      have he := Real.exp_pos (Real.pi / T)
      rw [mul_inv_lt_iff₀ he]; linarith
    have h2 := Real.rpow_lt_rpow (by positivity) h1 hβ
    rw [Real.mul_rpow hu.le (Real.exp_pos _).le, ← Real.exp_mul] at h2
    have e : -(Real.pi / T) * β = -(β * Real.pi / T) := by ring
    rw [e] at h2
    exact h2
  · apply div_le_div_of_nonneg_right _ hn.le
    exact Real.rpow_le_rpow (contactAt_pos β T _).le hle hβ.le

/-! ## P5. Réponse à la question §19.64 : le bilan pondéré est borné par sa dernière cellule -/

theorem contactRealValue_abs_add_nat {β T : ℝ} (hT : T ≠ 0) (k₀ : ℤ) (i : ℕ) :
    |contactRealValue β T (k₀ + i)| = |contactRealValue β T k₀| * Real.exp (β * Real.pi / T) ^ i := by
  rw [contactRealValue_add_nat hT, abs_mul, abs_pow, abs_neg, abs_of_pos (Real.exp_pos _), mul_comm]

theorem valueCellSum_abs_le {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (k₀ : ℤ) (m : ℕ) {D : ℝ}
    (hD : ∀ j ∈ range (m + 1), |cellDemand β T (k₀ + j)| ≤ D) :
    |valueCellSum β T k₀ m| ≤
      |contactRealValue β T (k₀ + m)| * D *
        (Real.exp (β * Real.pi / T) / (Real.exp (β * Real.pi / T) - 1)) := by
  set q := Real.exp (β * Real.pi / T) with hq
  have hq1 : 1 < q := Real.one_lt_exp_iff.mpr (by positivity)
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD 0 (by simp))
  unfold valueCellSum
  calc |∑ j ∈ range (m + 1), contactRealValue β T (k₀ + j) * cellDemand β T (k₀ + j)|
      ≤ ∑ j ∈ range (m + 1), |contactRealValue β T (k₀ + j) * cellDemand β T (k₀ + j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (m + 1), |contactRealValue β T k₀| * q ^ j * D := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, contactRealValue_abs_add_nat hT.ne']
        exact mul_le_mul_of_nonneg_left (hD j hj) (by positivity)
    _ = |contactRealValue β T k₀| * D * ∑ j ∈ range (m + 1), q ^ j := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    _ = |contactRealValue β T k₀| * D * ((q ^ (m + 1) - 1) / (q - 1)) := by
        rw [geom_sum_eq hq1.ne']
    _ ≤ |contactRealValue β T k₀| * D * (q ^ (m + 1) / (q - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_right _ (by linarith)
        linarith
    _ = |contactRealValue β T (k₀ + m)| * D * (q / (q - 1)) := by
        rw [contactRealValue_abs_add_nat hT.ne', pow_succ, ← hq]
        field_simp

/-! ## P6. Le prix bat le budget d'une rencontre -/

theorem price_beats_budget {r : ℝ} (hr : 0 < r) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, K * Real.log x < x ^ r := by
  have hc : 0 < 1 / (|K| + 1) := by positivity
  have h := (isLittleO_log_rpow_atTop hr).def hc
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hxr : 0 < x ^ r := Real.rpow_pos_of_pos (by linarith) r
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1), abs_of_pos hxr] at hx
  have hK : K * Real.log x ≤ |K| * Real.log x :=
    mul_le_mul_of_nonneg_right (le_abs_self K) (Real.log_nonneg hx1)
  have h2 : |K| * Real.log x ≤ |K| * (1 / (|K| + 1) * x ^ r) :=
    mul_le_mul_of_nonneg_left hx (abs_nonneg K)
  have h3 : |K| * (1 / (|K| + 1) * x ^ r) < x ^ r := by
    have : |K| * (1 / (|K| + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]; linarith
    nlinarith
  linarith

#print axioms RHV6Fresh.pair_amplitude_eq_price
#print axioms RHV6Fresh.offPrice_unbounded
#print axioms RHV6Fresh.offPrice_of_meeting_values
#print axioms RHV6Fresh.meeting_value_bounds
#print axioms RHV6Fresh.valueCellSum_abs_le
#print axioms RHV6Fresh.price_beats_budget

end RHV6Fresh
