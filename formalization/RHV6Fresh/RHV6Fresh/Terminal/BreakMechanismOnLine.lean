/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MeetingRegimeFinite

/-!
# Le mécanisme de cassure sur la ligne critique, écrit avec les contacts (E447, §19.69, 2026-11-07)

Module isolé (non ajouté à `RHV6Fresh.lean`). Ordre de l'auteur (R-LIGNE) : maîtriser le mécanisme de cassure depuis
la ligne (`β = 1/2`) avant toute déduction sur les OFF ; aucun énoncé ici ne parle d'un zéro hors ligne, aucune
contradiction n'est cherchée. Objets : une Tour, ses contacts `C_k`, ses cellules, ses valeurs réelles `v_k` aux
contacts ; la demande brute `rawDemand = ψ − id`, ses pentes de cellule ; les premiers et leurs poids.

* L1 `demandAtContact`, `cellDemand_eq_demandAtContact`, `cellDemand_telescope` : la demande brute AUX CONTACTS ;
  la somme des pentes d'un bloc est la différence des demandes aux deux contacts extrêmes.
* L2 `valueCellSum_abel` (toute `β`), `valueCellSum_abel_signed` : **bilan d'Abel** — la somme pondérée des pentes
  d'un bloc vaut `v_M R(C_M) − v_0 R(C_0) + (1 + e^{βπ/T}) Σ v_i R(C_{i+1})` : le budget collectif pondéré se lit sur
  la demande brute aux contacts, avec la règle signée `v_{k+1} = −e^{βπ/T} v_k`.
* L3 `line_contactRealValue_sq`, `line_value_sq_succ`, `line_value_sq_ratio_eq_length_ratio` : sur la ligne,
  `v_k² = C_k / ‖(1/2,T)‖²`, `v_{k+1}² = e^{π/T} v_k²`, et le rapport des carrés est le rapport des abscisses.
* L4 `contact_of_fraction`, `line_break_amplitude_exact`, `line_break_amplitude_bounds`, `line_break_price_bounds` :
  **attribution exacte de la cassure** — au point `x`, le dernier contact vaut `C_k = x·e^{−π f/T}` (`f` fraction de
  cellule), et sur la ligne `|v_k| = √x · e^{−π f/(2T)} / ‖(1/2,T)‖`, donc strictement entre `√x·e^{−π/(2T)}` et `√x`
  (sur la norme) ; la cassure `log q` au premier `q` est payée avec cette amplitude.
* L5 `rawDemand_prime_from_contact`, `break_then_descent` : du contact au premier `q`, la demande brute varie des
  poids franchis moins la descente `q − C_k` ; si `q` est le seul poids franchi, c'est `log q − (q − C_k)` :
  montée d'un coup, descente linéaire.
* L6 `rawDemand_div_tendsto_zero`, `demandAtContact_div_tendsto_zero`, `line_weighted_demand_at_contact_small` :
  `R(x)/x → 0` (PNT porté, `WeakPNT''`), donc `R(C_k)/C_k → 0` le long de toute Tour, et sur la ligne
  `|v_k R(C_k)| / C_k^{3/2} → 0`.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune hypothèse, aucune somme de Tours, aucun objet spectral.
-/
namespace RHV6Fresh

open Real RHV3Lean Finset Filter Topology Asymptotics ArithmeticFunction

/-! ## L1. La demande brute aux contacts ; télescopage des pentes -/

noncomputable def demandAtContact (β T : ℝ) (k : ℤ) : ℝ := rawDemand (contactAt β T k)

theorem cellDemand_eq_demandAtContact (β T : ℝ) (k : ℤ) :
    cellDemand β T k = demandAtContact β T (k + 1) - demandAtContact β T k := rfl

theorem cellDemand_telescope (β T : ℝ) (k₀ : ℤ) (M : ℕ) :
    ∑ i ∈ range M, cellDemand β T (k₀ + i) = demandAtContact β T (k₀ + M) - demandAtContact β T k₀ := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, cellDemand_eq_demandAtContact]
    have e : (k₀ + ((M + 1 : ℕ) : ℤ)) = k₀ + M + 1 := by push_cast; ring
    rw [e]; ring

/-! ## L2. Bilan d'Abel du budget pondéré -/

theorem valueCellSum_abel (β T : ℝ) (k₀ : ℤ) (M : ℕ) :
    ∑ i ∈ range M, contactRealValue β T (k₀ + i) * cellDemand β T (k₀ + i) =
      contactRealValue β T (k₀ + M) * demandAtContact β T (k₀ + M)
        - contactRealValue β T k₀ * demandAtContact β T k₀
        - ∑ i ∈ range M, (contactRealValue β T (k₀ + i + 1) - contactRealValue β T (k₀ + i))
            * demandAtContact β T (k₀ + i + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, cellDemand_eq_demandAtContact]
    have e : (k₀ + ((M + 1 : ℕ) : ℤ)) = k₀ + M + 1 := by push_cast; ring
    rw [e]; ring

theorem valueCellSum_abel_signed {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (M : ℕ) :
    ∑ i ∈ range M, contactRealValue β T (k₀ + i) * cellDemand β T (k₀ + i) =
      contactRealValue β T (k₀ + M) * demandAtContact β T (k₀ + M)
        - contactRealValue β T k₀ * demandAtContact β T k₀
        + (1 + Real.exp (β * Real.pi / T)) *
            ∑ i ∈ range M, contactRealValue β T (k₀ + i) * demandAtContact β T (k₀ + i + 1) := by
  rw [valueCellSum_abel, Finset.mul_sum]
  have hterm : ∀ i ∈ range M,
      (contactRealValue β T (k₀ + i + 1) - contactRealValue β T (k₀ + i)) * demandAtContact β T (k₀ + i + 1)
        = -((1 + Real.exp (β * Real.pi / T)) *
            (contactRealValue β T (k₀ + i) * demandAtContact β T (k₀ + i + 1))) := by
    intro i _
    rw [contactRealValue_succ hT.ne']
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
  ring

/-! ## L3. La règle du carré sur la ligne -/

theorem line_contactRealValue_sq {T : ℝ} (_hT : 0 < T) (k : ℤ) :
    contactRealValue (1 / 2) T k ^ 2 = contactAt (1 / 2) T k / ‖(⟨1 / 2, T⟩ : ℂ)‖ ^ 2 := by
  unfold contactRealValue
  have h1 : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [← sq_abs, abs_neg_one_zpow]; norm_num
  have h2 : (contactAt (1 / 2) T k ^ (1 / 2 : ℝ)) ^ 2 = contactAt (1 / 2) T k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (contactAt_pos _ _ _).le]; norm_num
  rw [div_pow, mul_pow, h1, h2, one_mul]

theorem line_value_sq_succ {T : ℝ} (hT : 0 < T) (k : ℤ) :
    contactRealValue (1 / 2) T (k + 1) ^ 2 = Real.exp (Real.pi / T) * contactRealValue (1 / 2) T k ^ 2 := by
  rw [contactRealValue_succ hT.ne', mul_pow, neg_sq, ← Real.exp_nat_mul]
  congr 2; push_cast; ring

theorem line_value_sq_ratio_eq_length_ratio {T : ℝ} (hT : 0 < T) (k : ℤ) :
    contactRealValue (1 / 2) T (k + 1) ^ 2 * contactAt (1 / 2) T k =
      contactRealValue (1 / 2) T k ^ 2 * contactAt (1 / 2) T (k + 1) := by
  rw [line_contactRealValue_sq hT, line_contactRealValue_sq hT]
  ring

/-! ## L4. Attribution exacte de la cassure à l'amplitude du dernier contact -/

theorem contact_of_fraction {β T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    contactAt β T (lastContactBefore β T x) = x * Real.exp (-(Real.pi * cellFraction β T x / T)) := by
  have h := log_div_lastContact (β := β) hT hx
  have hc := contactAt_pos β T (lastContactBefore β T x)
  have hdiv : x / contactAt β T (lastContactBefore β T x) = Real.exp (Real.pi * cellFraction β T x / T) := by
    rw [← h, Real.exp_log (div_pos hx hc)]
  rw [Real.exp_neg, ← hdiv]
  field_simp

theorem line_break_amplitude_exact {T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x)| =
      x ^ (1 / 2 : ℝ) * Real.exp (-(Real.pi * cellFraction (1 / 2) T x / (2 * T))) / ‖(⟨1 / 2, T⟩ : ℂ)‖ := by
  unfold contactRealValue
  have hn := norm_mk_pos (β := 1 / 2) (T := T) (by norm_num)
  rw [abs_div, abs_mul, abs_neg_one_zpow, one_mul, abs_of_pos hn,
    abs_of_nonneg (Real.rpow_nonneg (contactAt_pos _ _ _).le _), contact_of_fraction hT hx,
    Real.mul_rpow hx.le (Real.exp_pos _).le, ← Real.exp_mul]
  congr 3
  ring

theorem line_break_amplitude_bounds {T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    x ^ (1 / 2 : ℝ) * Real.exp (-(Real.pi / (2 * T))) / ‖(⟨1 / 2, T⟩ : ℂ)‖ <
        |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x)| ∧
      |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T x)| ≤ x ^ (1 / 2 : ℝ) / ‖(⟨1 / 2, T⟩ : ℂ)‖ := by
  rw [line_break_amplitude_exact hT hx]
  have hn := norm_mk_pos (β := 1 / 2) (T := T) (by norm_num)
  have hxp : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  have hf0 := cellFraction_nonneg (1 / 2) T x
  have hf1 := cellFraction_lt_one (1 / 2) T x
  have hpi := Real.pi_pos
  constructor
  · apply div_lt_div_of_pos_right _ hn
    apply mul_lt_mul_of_pos_left _ hxp
    apply Real.exp_lt_exp.mpr
    rw [neg_lt_neg_iff, div_lt_div_iff_of_pos_right (by positivity)]
    nlinarith
  · apply div_le_div_of_nonneg_right _ hn.le
    calc x ^ (1 / 2 : ℝ) * Real.exp (-(Real.pi * cellFraction (1 / 2) T x / (2 * T)))
        ≤ x ^ (1 / 2 : ℝ) * 1 := by
          apply mul_le_mul_of_nonneg_left _ hxp.le
          apply Real.exp_le_one_iff.mpr
          rw [neg_nonpos]; positivity
      _ = x ^ (1 / 2 : ℝ) := mul_one _

theorem line_break_price_bounds {T : ℝ} (hT : 0 < T) {q : ℕ} (hq : q.Prime) :
    (q : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-(Real.pi / (2 * T))) / ‖(⟨1 / 2, T⟩ : ℂ)‖ * Real.log q <
        |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T q) * Real.log q| ∧
      |contactRealValue (1 / 2) T (lastContactBefore (1 / 2) T q) * Real.log q| ≤
        (q : ℝ) ^ (1 / 2 : ℝ) / ‖(⟨1 / 2, T⟩ : ℂ)‖ * Real.log q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  obtain ⟨h1, h2⟩ := line_break_amplitude_bounds hT hq0
  rw [abs_mul, abs_of_pos hlog]
  exact ⟨mul_lt_mul_of_pos_right h1 hlog, mul_le_mul_of_nonneg_right h2 hlog.le⟩

/-! ## L5. Cassure puis descente -/

theorem rawDemand_prime_from_contact {β T : ℝ} (k : ℤ) {q : ℕ} (hq : contactAt β T k ≤ q) :
    rawDemand q - demandAtContact β T k =
      ∑ n ∈ Ioc ⌊contactAt β T k⌋₊ q, Λ n - ((q : ℝ) - contactAt β T k) := by
  unfold demandAtContact
  rw [rawDemand_variation hq, Nat.floor_natCast]

theorem break_then_descent {β T : ℝ} (k : ℤ) {q : ℕ} (hq : contactAt β T k < q) (hp : q.Prime)
    (hsolo : ∀ n ∈ Ioc ⌊contactAt β T k⌋₊ q, n ≠ q → Λ n = 0) :
    rawDemand q - demandAtContact β T k = Real.log q - ((q : ℝ) - contactAt β T k) := by
  rw [rawDemand_prime_from_contact k hq.le, Finset.sum_eq_single q hsolo, vonMangoldt_apply_prime hp]
  intro habs
  exfalso; apply habs
  rw [Finset.mem_Ioc]
  exact ⟨(Nat.floor_lt (contactAt_pos β T k).le).mpr hq, le_rfl⟩

/-! ## L6. Taille de la demande brute aux contacts (PNT porté) -/

theorem rawDemand_div_tendsto_zero : Tendsto (fun x : ℝ => rawDemand x / x) atTop (𝓝 0) := by
  have hpsi : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
    have hz : ∀ᶠ x : ℝ in atTop, x ≠ 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx using hx.ne'
    exact (isEquivalent_iff_tendsto_one hz).mp WeakPNT''
  have h := hpsi.sub_const 1
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold rawDemand
  field_simp

theorem demandAtContact_div_tendsto_zero {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) :
    Tendsto (fun i : ℕ => demandAtContact β T (k₀ + i) / contactAt β T (k₀ + i)) atTop (𝓝 0) :=
  rawDemand_div_tendsto_zero.comp (contactAt_tendsto_atTop hT k₀)

theorem line_weighted_demand_at_contact_small {T : ℝ} (hT : 0 < T) (k₀ : ℤ) :
    Tendsto (fun i : ℕ => contactRealValue (1 / 2) T (k₀ + i) * demandAtContact (1 / 2) T (k₀ + i) /
      (contactAt (1 / 2) T (k₀ + i) ^ (1 / 2 : ℝ) * contactAt (1 / 2) T (k₀ + i))) atTop (𝓝 0) := by
  have hn := norm_mk_pos (β := 1 / 2) (T := T) (by norm_num)
  have h := (demandAtContact_div_tendsto_zero (β := 1 / 2) hT k₀).const_mul (1 / ‖(⟨1 / 2, T⟩ : ℂ)‖)
  rw [mul_zero] at h
  rw [tendsto_zero_iff_abs_tendsto_zero] at h ⊢
  refine h.congr (fun i => ?_)
  simp only [Function.comp_apply]
  have hc := contactAt_pos (1 / 2) T (k₀ + i)
  have hr := Real.rpow_pos_of_pos hc (1 / 2 : ℝ)
  have hv : |contactRealValue (1 / 2) T (k₀ + i)| = contactAt (1 / 2) T (k₀ + i) ^ (1 / 2 : ℝ) / ‖(⟨1 / 2, T⟩ : ℂ)‖ := by
    unfold contactRealValue
    rw [abs_div, abs_mul, abs_neg_one_zpow, one_mul, abs_of_pos hn, abs_of_pos hr]
  rw [abs_mul, abs_div, abs_one, abs_of_pos hn, abs_div, abs_of_pos hc, abs_div, abs_mul, hv,
    abs_mul, abs_of_pos hr, abs_of_pos hc]
  field_simp

#print axioms RHV6Fresh.cellDemand_telescope
#print axioms RHV6Fresh.valueCellSum_abel_signed
#print axioms RHV6Fresh.line_contactRealValue_sq
#print axioms RHV6Fresh.line_break_amplitude_exact
#print axioms RHV6Fresh.line_break_price_bounds
#print axioms RHV6Fresh.break_then_descent
#print axioms RHV6Fresh.line_weighted_demand_at_contact_small

end RHV6Fresh
