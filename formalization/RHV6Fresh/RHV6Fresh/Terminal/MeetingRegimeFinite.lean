/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MeetingPriceTheorem
import RHV6Fresh.Terminal.LogGapsTheorem

/-!
# Le régime « une rencontre par cellule » est fini ; le budget exact d'une cellule est sa longueur (E446, §19.68, 2026-11-07)

Module isolé (non ajouté à `RHV6Fresh.lean`). Cause racine du constat d'E445 (le prix bat le budget d'une rencontre,
jamais le budget cumulé) : tous les énoncés « la cellule de rencontre franchit exactement un premier » supposent que
deux écarts consécutifs contiennent chacun un contact. Cette hypothèse force `π/T ≤ log p_{n+2} − log p_n`, ce que le
théorème porté `logGapsVanish_holds` (PNT) interdit au-delà d'un rang fini. Au-delà, le budget exact d'une cellule est
`ψ(C_{k+1}) − ψ(C_k)`, équivalent à sa longueur (`WeakPNT''`), et le pas de toute Tour `0 < β < 1` sur sa cellule lui est
négligeable.

* F1 `meeting_cell_within_two_gaps` : la cellule de rencontre est dans `]p_n, p_{n+2}]` ;
* F2 `log_ratio_ge_cell_of_meeting` : `π/T ≤ log p_{n+2} − log p_n` ;
* F3 `two_consecutive_contacts_finite` : il existe `N` au-delà duquel deux écarts consécutifs n'ont jamais chacun un contact ;
* F4 `meeting_series_rank_bounded`, `meeting_break_rank_bounded` : les hypothèses de `valuePrimeSum_eq_meetings` et de
  `cellPrimeWeight_meeting` ne sont satisfaites qu'à rang borné ;
* F5 `cellWeight_eq_psi_diff`, `contactAt_tendsto_atTop`, `cellWeight_div_cellLength_tendsto_one` ;
* F6 `cellDemand_div_cellLength_tendsto_zero` : la variation de la demande brute sur une cellule est `o(cellule)` ;
* F7 `tower_step_div_cellLength_tendsto_zero` : pas d'une Tour sur sa cellule / longueur → 0, pour tout `0 < β < 1` ;
* F8 `price_beats_budget_on_line` : P6 vaut aussi sur la ligne (`β = 1/2`) ;
* F9 `valueNonPrimeSum`, `valuePrimeSum_balance` : budget pondéré des premiers d'un bloc = demande pondérée − poids non
  premiers pondérés + longueurs pondérées.

Une Tour, ses contacts, ses cellules, ses valeurs ; les premiers et `rawDemand` ; aucune somme de Tours, aucun objet
spectral. Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/
namespace RHV6Fresh

open Real RHV3Lean Finset Filter Topology Asymptotics

/-! ## F1–F2. Deux écarts consécutifs à contact enferment une cellule entière -/

theorem meeting_cell_within_two_gaps {β T : ℝ} (hT : 0 < T) {I J : PrimeGapInterval} (hIJ : J.rank = I.rank + 1)
    (hI : GapHasContact β T I) (hJ : GapHasContact β T J) :
    I.lower < contactAt β T (meetingCell β T I) ∧ contactAt β T (meetingCell β T I + 1) ≤ J.upper := by
  have hlow : J.lower = I.upper := by
    unfold PrimeGapInterval.lower PrimeGapInterval.upper
    rw [hIJ]
  unfold GapHasContact at hI hJ
  rw [hlow] at hJ
  unfold meetingCell
  constructor
  · have h1 := lt_contact_succ (β := β) hT (by linarith [I.one_lt_lower] : (0 : ℝ) < I.lower)
    have h2 := contactAt_mono (β := β) hT (k := lastContactBefore β T I.lower + 1)
      (l := lastContactBefore β T I.upper) (by omega)
    linarith
  · have h1 := lastContact_le (β := β) hT (by linarith [J.one_lt_upper] : (0 : ℝ) < J.upper)
    have h2 := contactAt_mono (β := β) hT (k := lastContactBefore β T I.upper + 1)
      (l := lastContactBefore β T J.upper) (by omega)
    linarith

theorem log_ratio_ge_cell_of_meeting {β T : ℝ} (hT : 0 < T) {I J : PrimeGapInterval} (hIJ : J.rank = I.rank + 1)
    (hI : GapHasContact β T I) (hJ : GapHasContact β T J) :
    Real.pi / T ≤ Real.log J.upper - Real.log I.lower := by
  obtain ⟨h1, h2⟩ := meeting_cell_within_two_gaps hT hIJ hI hJ
  have hr := contactAt_ratio (β := β) hT.ne' (meetingCell β T I)
  have hpos := contactAt_pos β T (meetingCell β T I)
  have hpos' := contactAt_pos β T (meetingCell β T I + 1)
  have hl : 0 < I.lower := by linarith [I.one_lt_lower]
  have hu : 0 < J.upper := by linarith [J.one_lt_upper]
  have hle : Real.exp (Real.pi / T) ≤ J.upper / I.lower := by
    rw [← hr, div_le_div_iff₀ hpos hl]
    calc contactAt β T (meetingCell β T I + 1) * I.lower
        ≤ contactAt β T (meetingCell β T I + 1) * contactAt β T (meetingCell β T I) :=
          mul_le_mul_of_nonneg_left h1.le hpos'.le
      _ ≤ J.upper * contactAt β T (meetingCell β T I) := mul_le_mul_of_nonneg_right h2 hpos.le
  have := Real.log_le_log (Real.exp_pos _) hle
  rwa [Real.log_exp, Real.log_div hu.ne' hl.ne'] at this

/-! ## F3–F4. Le régime à une rencontre par cellule est fini -/

theorem two_consecutive_contacts_finite {β T : ℝ} (hT : 0 < T) :
    ∃ N : ℕ, ∀ n, N ≤ n → ¬ (GapHasContact β T ⟨n⟩ ∧ GapHasContact β T ⟨n + 1⟩) := by
  have hlog := logGapsVanish_holds
  unfold LogGapsVanish at hlog
  have hε : 0 < Real.pi / T / 2 := by positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlog) _ hε
  refine ⟨N, fun n hn ⟨hI, hJ⟩ => ?_⟩
  have h := log_ratio_ge_cell_of_meeting hT (I := ⟨n⟩) (J := ⟨n + 1⟩) rfl hI hJ
  have h1 := hN n hn
  have h2 := hN (n + 1) (by omega)
  rw [Real.dist_eq, sub_zero] at h1 h2
  have hu : (⟨n + 1⟩ : PrimeGapInterval).upper = (fnPrimeAtRank (n + 1 + 1) : ℝ) := rfl
  have hl : (⟨n⟩ : PrimeGapInterval).lower = (fnPrimeAtRank n : ℝ) := rfl
  rw [hu, hl] at h
  have := abs_lt.mp h1
  have := abs_lt.mp h2
  linarith

theorem meeting_series_rank_bounded {β T : ℝ} (hT : 0 < T) :
    ∃ N : ℕ, ∀ n J : ℕ, 1 ≤ J → (∀ j ≤ J, GapHasContact β T ⟨n + j⟩) → n < N := by
  obtain ⟨N, hN⟩ := two_consecutive_contacts_finite (β := β) hT
  refine ⟨N, fun n J hJ hc => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact hN n hlt ⟨by simpa using hc 0 (by omega), hc 1 hJ⟩

theorem meeting_break_rank_bounded {β T : ℝ} (hT : 0 < T) :
    ∃ N : ℕ, ∀ I J : PrimeGapInterval, J.rank = I.rank + 1 → GapHasContact β T I → GapHasContact β T J → I.rank < N := by
  obtain ⟨N, hN⟩ := two_consecutive_contacts_finite (β := β) hT
  refine ⟨N, fun I J hIJ hI hJ => ?_⟩
  obtain ⟨n⟩ := I
  obtain ⟨m⟩ := J
  simp only at hIJ
  subst hIJ
  by_contra hlt
  push_neg at hlt
  exact hN n hlt ⟨hI, hJ⟩

/-! ## F5–F6. Le budget exact d'une cellule est sa longueur, au premier ordre (PNT porté) -/

theorem cellWeight_eq_psi_diff {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    cellWeight β T k = Chebyshev.psi (contactAt β T (k + 1)) - Chebyshev.psi (contactAt β T k) := by
  have h := cellDemand_eq (β := β) hT k
  unfold cellDemand rawDemand cellLength at h
  linarith

theorem contactAt_tendsto_atTop {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) :
    Tendsto (fun i : ℕ => contactAt β T (k₀ + i)) atTop atTop := by
  have hr1 : 1 < Real.exp (Real.pi / T) := Real.one_lt_exp_iff.mpr (by positivity)
  have : (fun i : ℕ => contactAt β T (k₀ + i)) = fun i : ℕ => contactAt β T k₀ * Real.exp (Real.pi / T) ^ i := by
    funext i; exact contactAt_add_nat_eq k₀ i
  rw [this]
  exact Tendsto.const_mul_atTop (contactAt_pos β T k₀) (tendsto_pow_atTop_atTop_of_one_lt hr1)

theorem cellWeight_div_cellLength_tendsto_one {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) :
    Tendsto (fun i : ℕ => cellWeight β T (k₀ + i) / cellLength β T (k₀ + i)) atTop (𝓝 1) := by
  set r := Real.exp (Real.pi / T) with hr
  have hr1 : 1 < r := Real.one_lt_exp_iff.mpr (by positivity)
  have hr0 : 0 < r := by linarith
  have hu := contactAt_tendsto_atTop (β := β) hT k₀
  have hpsi : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
    have hz : ∀ᶠ x : ℝ in atTop, x ≠ 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx using hx.ne'
    exact (isEquivalent_iff_tendsto_one hz).mp WeakPNT''
  have ha : Tendsto (fun i : ℕ => Chebyshev.psi (contactAt β T (k₀ + i)) / contactAt β T (k₀ + i)) atTop (𝓝 1) :=
    hpsi.comp hu
  have hb : Tendsto (fun i : ℕ => Chebyshev.psi (contactAt β T (k₀ + i) * r) / (contactAt β T (k₀ + i) * r))
      atTop (𝓝 1) :=
    hpsi.comp (hu.atTop_mul_const hr0)
  have hlim : Tendsto (fun i : ℕ =>
      (r * (Chebyshev.psi (contactAt β T (k₀ + i) * r) / (contactAt β T (k₀ + i) * r)) -
        Chebyshev.psi (contactAt β T (k₀ + i)) / contactAt β T (k₀ + i)) / (r - 1)) atTop (𝓝 1) := by
    have := ((hb.const_mul r).sub ha).div_const (r - 1)
    rw [mul_one, div_self (by linarith : r - 1 ≠ 0)] at this
    exact this
  refine hlim.congr (fun i => ?_)
  have hC : contactAt β T (k₀ + i + 1) = contactAt β T (k₀ + i) * r := by
    have := contactAt_ratio (β := β) hT.ne' (k₀ + i)
    rw [div_eq_iff (contactAt_pos β T _).ne'] at this
    rw [this, ← hr, mul_comm]
  have hpos := contactAt_pos β T (k₀ + i)
  rw [cellWeight_eq_psi_diff hT, cellLength_eq hT, ← hr, hC]
  have h1 : r - 1 ≠ 0 := by linarith
  field_simp

theorem cellDemand_div_cellLength_tendsto_zero {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) :
    Tendsto (fun i : ℕ => cellDemand β T (k₀ + i) / cellLength β T (k₀ + i)) atTop (𝓝 0) := by
  have h := (cellWeight_div_cellLength_tendsto_one (β := β) hT k₀).sub_const 1
  rw [sub_self] at h
  refine h.congr (fun i => ?_)
  rw [cellDemand_eq hT, sub_div, div_self (cellLength_pos hT _).ne']

/-! ## F7. Le pas d'une Tour sur sa cellule est négligeable devant la longueur de la cellule -/

theorem tower_step_div_cellLength_tendsto_zero {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) (k₀ : ℤ) :
    Tendsto (fun i : ℕ => |contactRealValue β T (k₀ + i + 1) - contactRealValue β T (k₀ + i)| /
      cellLength β T (k₀ + i)) atTop (𝓝 0) := by
  set r := Real.exp (Real.pi / T) with hr
  set q := Real.exp (β * Real.pi / T) with hq
  have hr1 : 1 < r := Real.one_lt_exp_iff.mpr (by positivity)
  have hq0 : 0 < q := Real.exp_pos _
  have hn := norm_mk_pos (T := T) hβ
  have hu := contactAt_tendsto_atTop (β := β) hT k₀
  have hpow : Tendsto (fun i : ℕ => contactAt β T (k₀ + i) ^ (-(1 - β))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp hu
  have hlim := hpow.const_mul ((1 + q) / (‖(⟨β, T⟩ : ℂ)‖ * (r - 1)))
  rw [mul_zero] at hlim
  refine hlim.congr (fun i => ?_)
  rw [contactRealValue_succ hT.ne', ← hq, cellLength_eq hT, ← hr]
  have h1 : |-q * contactRealValue β T (k₀ + i) - contactRealValue β T (k₀ + i)| =
      (1 + q) * |contactRealValue β T (k₀ + i)| := by
    rw [show -q * contactRealValue β T (k₀ + i) - contactRealValue β T (k₀ + i) =
      -((1 + q) * contactRealValue β T (k₀ + i)) by ring, abs_neg, abs_mul, abs_of_pos (by linarith)]
  rw [h1, abs_contactRealValue hβ]
  have hC := contactAt_pos β T (k₀ + i)
  rw [show -(1 - β) = β - 1 by ring, Real.rpow_sub_one hC.ne']
  have h2 : r - 1 ≠ 0 := by linarith
  field_simp

/-! ## F8. P6 n'est pas discriminant : il vaut aussi sur la ligne -/

theorem price_beats_budget_on_line (K : ℝ) : ∀ᶠ x : ℝ in atTop, K * Real.log x < x ^ (1 / 2 : ℝ) :=
  price_beats_budget (by norm_num) K

/-! ## F9. Le budget collectif pondéré d'un bloc, en objets autorisés -/

noncomputable def valueNonPrimeSum (β T : ℝ) (k₀ : ℤ) (M : ℕ) : ℝ :=
  ∑ i ∈ range M, contactRealValue β T (k₀ + i) * cellNonPrimeWeight β T (k₀ + i)

theorem valuePrimeSum_balance {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (M : ℕ) :
    valuePrimeSum β T k₀ M =
      (∑ i ∈ range M, contactRealValue β T (k₀ + i) * cellDemand β T (k₀ + i)) -
        valueNonPrimeSum β T k₀ M + valueLengthSum β T k₀ M := by
  unfold valuePrimeSum valueNonPrimeSum valueLengthSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [cellDemand_eq hT, cellWeight_eq_prime_add_nonprime]
  ring

#print axioms RHV6Fresh.log_ratio_ge_cell_of_meeting
#print axioms RHV6Fresh.two_consecutive_contacts_finite
#print axioms RHV6Fresh.meeting_break_rank_bounded
#print axioms RHV6Fresh.cellWeight_div_cellLength_tendsto_one
#print axioms RHV6Fresh.cellDemand_div_cellLength_tendsto_zero
#print axioms RHV6Fresh.tower_step_div_cellLength_tendsto_zero
#print axioms RHV6Fresh.valuePrimeSum_balance

end RHV6Fresh
