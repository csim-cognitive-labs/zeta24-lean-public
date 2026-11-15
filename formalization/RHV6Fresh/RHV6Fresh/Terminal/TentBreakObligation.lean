/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CellAreaTent
import RHV6Fresh.Terminal.PairBreakAtPrime

/-!
# RHV6Fresh — Terminal/TentBreakObligation : la tente lit la cassure ; l'obligation du poids du premier partagé (E476, §19.110)
(2026-11-14 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse, aucun axiome, aucun `sorry`)

Stratégie (règle R-Ψ). Ordre de l'auteur : combiner la tente (E474) et la cassure au premier (E447/E450). La cassure de la demande en un
premier `x` entre dans le terme local `L_k` avec le poids `Λ(x)·tente_k(x)` ; la Tour paie en `x` l'amplitude `x^β e^{−βπf/T}/‖ρ‖`. Les deux
dépendent de la même fraction de cellule `f` : le poids de la cassure dans la grammaire des aires est une fonction de l'amplitude payée
(H2), le poids alterné est une dent de scie nulle au point neutre de la cellule (H3), et le miroir ne donne jamais au même premier le
poids que lui donne la Tour, sauf sur la ligne (H4). Aucune contradiction n'est posée ; contacts ≠ premiers (§19.51) : `x` est un
réel quelconque, sa fraction de cellule est sa position relative aux contacts.
-/

namespace RHV6Fresh

open Real ArithmeticFunction Finset

/-- Poids de tente de la cassure en `x` : la tente de la cellule qui contient `x`, évaluée en `x` (branche montante). -/
noncomputable def breakTentWeight (β T x : ℝ) : ℝ := tentKernel β T (lastContactBefore β T x) x

/-- **H1.** `w = e^{π/T}·x·(1 − e^{−πf/T})`. -/
theorem breakTentWeight_eq {β T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    breakTentWeight β T x =
      Real.exp (π / T) * x * (1 - Real.exp (-(π * cellFraction β T x / T))) := by
  unfold breakTentWeight
  have hle : x ≤ contactAt β T (lastContactBefore β T x + 1) := (lt_contact_succ hT hx).le
  rw [tentKernel_eq_left hT _ hle, contact_of_fraction hT hx]
  ring

/-- **H1, tente précédente.** Dans la tente de la cellule précédente, `x` est sur la branche descendante :
`tente_{k−1}(x) = x(e^{π/T}e^{−πf/T} − 1)`. -/
theorem breakTentWeight_prev_eq {β T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    tentKernel β T (lastContactBefore β T x - 1) x =
      x * (Real.exp (π / T) * Real.exp (-(π * cellFraction β T x / T)) - 1) := by
  have hge : contactAt β T (lastContactBefore β T x - 1 + 1) ≤ x := by
    rw [show lastContactBefore β T x - 1 + 1 = lastContactBefore β T x by ring]
    exact lastContact_le hT hx
  rw [tentKernel_eq_right hT _ hge,
    show lastContactBefore β T x - 1 + 2 = lastContactBefore β T x + 1 by ring,
    contactAt_succ hT, contact_of_fraction hT hx]
  ring

theorem breakTentWeight_nonneg {β T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) : 0 ≤ breakTentWeight β T x := by
  rw [breakTentWeight_eq hT hx]
  have h1 : Real.exp (-(π * cellFraction β T x / T)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := cellFraction_nonneg β T x
    have := Real.pi_pos
    have : 0 ≤ π * cellFraction β T x / T := by positivity
    linarith
  have h2 : 0 ≤ Real.exp (π / T) * x := by positivity
  nlinarith

/-- **H2, la cassure lit la tente.** L'amplitude payée au dernier contact avant `x` est une fonction du poids de tente de `x` :
`|v| = x^β (1 − w/(e^{π/T}x))^β / ‖ρ‖`. -/
theorem break_amplitude_reads_tent {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    |contactRealValue β T (lastContactBefore β T x)| =
      x ^ β * (1 - breakTentWeight β T x / (Real.exp (π / T) * x)) ^ β / ‖(⟨β, T⟩ : ℂ)‖ := by
  rw [break_amplitude_exact hβ hT hx, breakTentWeight_eq hT hx]
  have hg : Real.exp (π / T) * x ≠ 0 := by positivity
  have h1 : 1 - Real.exp (π / T) * x * (1 - Real.exp (-(π * cellFraction β T x / T))) / (Real.exp (π / T) * x) =
      Real.exp (-(π * cellFraction β T x / T)) := by
    field_simp
    ring
  have h2 : Real.exp (-(β * π * cellFraction β T x / T)) = Real.exp (-(π * cellFraction β T x / T)) ^ β := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [h1, h2]

/-- Division du terme local : le poids de la cassure en un entier `q` de la double cellule, et le reste. -/
theorem localGrammarTerm_break_split {β T : ℝ} (hT : 0 < T) (k : ℤ) {q : ℕ}
    (hq : q ∈ Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 2)⌋₊) :
    localGrammarTerm β T k =
      Λ q * tentKernel β T k q +
        ∑ n ∈ (Ioc ⌊contactAt β T k⌋₊ ⌊contactAt β T (k + 2)⌋₊).erase q, Λ n * tentKernel β T k n -
        Real.exp (π / T) * (1 + Real.exp (π / T)) * cellLength β T k ^ 2 / 2 := by
  rw [localGrammarTerm_eq_tent_sum hT k, ← Finset.add_sum_erase _ _ hq]

/-- **H3, dent de scie.** Différence des deux tentes qui contiennent `x` : `(1 + e^{π/T})x − 2C_{k+1}`. -/
theorem tent_difference_eq_sawtooth {β T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    breakTentWeight β T x - tentKernel β T (lastContactBefore β T x - 1) x =
      (1 + Real.exp (π / T)) * x - 2 * contactAt β T (lastContactBefore β T x + 1) := by
  rw [breakTentWeight_eq hT hx, breakTentWeight_prev_eq hT hx, contactAt_succ hT, contact_of_fraction hT hx]
  ring

/-- **H3, poids alterné.** Dans la somme alternée, la cassure en `x` (cellule de rang `j` dans la fenêtre) pèse
`(−1)^j·((1+e^{π/T})x − 2C_{k+1})`. -/
theorem alternating_break_weight {β T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) (j : ℕ) :
    (-1 : ℝ) ^ (j + 1) * tentKernel β T (lastContactBefore β T x - 1) x + (-1 : ℝ) ^ j * breakTentWeight β T x =
      (-1 : ℝ) ^ j * ((1 + Real.exp (π / T)) * x - 2 * contactAt β T (lastContactBefore β T x + 1)) := by
  rw [← tent_difference_eq_sawtooth hT hx, pow_succ]
  ring

/-- **H3, signe.** Le poids alterné est positif ⟺ `x` est au-delà du point neutre : `2e^{π/T}e^{−πf/T} < 1 + e^{π/T}`. -/
theorem sawtooth_pos_iff {β T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    0 < (1 + Real.exp (π / T)) * x - 2 * contactAt β T (lastContactBefore β T x + 1) ↔
      2 * Real.exp (π / T) * Real.exp (-(π * cellFraction β T x / T)) < 1 + Real.exp (π / T) := by
  rw [contactAt_succ hT, contact_of_fraction hT hx]
  have h : (1 + Real.exp (π / T)) * x - 2 * (Real.exp (π / T) * (x * Real.exp (-(π * cellFraction β T x / T)))) =
      x * ((1 + Real.exp (π / T)) - 2 * Real.exp (π / T) * Real.exp (-(π * cellFraction β T x / T))) := by ring
  rw [h, mul_pos_iff_of_pos_left hx, sub_pos]

/-- **H4, obligation de la paire.** Le miroir donne au même `x` le même poids de tente que la Tour si et seulement si `β = 1/2`. -/
theorem pair_breakTentWeight_eq_iff {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    breakTentWeight (1 - β) T x = breakTentWeight β T x ↔ β = 1 / 2 := by
  rw [breakTentWeight_eq hT hx, breakTentWeight_eq hT hx]
  have hg : 0 < Real.exp (π / T) * x := by positivity
  constructor
  · intro h
    have h1 : 1 - Real.exp (-(π * cellFraction (1 - β) T x / T)) = 1 - Real.exp (-(π * cellFraction β T x / T)) :=
      mul_left_cancel₀ hg.ne' h
    have h1' : Real.exp (-(π * cellFraction (1 - β) T x / T)) = Real.exp (-(π * cellFraction β T x / T)) := by
      linarith
    have h3 : π * cellFraction (1 - β) T x / T = π * cellFraction β T x / T := by
      linarith [Real.exp_injective h1']
    rw [div_left_inj' hT.ne', mul_right_inj' Real.pi_pos.ne'] at h3
    have h4 : Int.fract (cellFraction β T x + mirrorPhaseShift β T / π) = Int.fract (cellFraction β T x) := by
      have hf : Int.fract (cellFraction β T x) = cellFraction β T x := by
        unfold cellFraction
        exact Int.fract_fract _
      rw [hf, ← mirror_cellFraction]
      exact h3
    obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp h4
    have hz' : (z : ℝ) = mirrorPhaseShift β T / π := by linarith
    have habs : |(z : ℝ)| < 1 := by
      rw [hz', abs_div, abs_of_pos Real.pi_pos, div_lt_one Real.pi_pos]
      exact abs_mirrorPhaseShift_lt_pi β T
    have hz0 : z = 0 := by
      have : |z| < 1 := by exact_mod_cast habs
      exact Int.abs_lt_one_iff.mp this
    have hδ : mirrorPhaseShift β T = 0 := by
      rw [hz0, Int.cast_zero] at hz'
      rcases div_eq_zero_iff.mp hz'.symm with h | h
      · exact h
      · exact absurd h Real.pi_pos.ne'
    exact (mirrorPhaseShift_eq_zero_iff hβ hβ1 hT).mp hδ
  · rintro rfl
    norm_num

/-- **H4, forme de la différence.** `w(1−β) − w(β) = e^{π/T} x (e^{−πf_β/T} − e^{−πf_{1−β}/T})`. -/
theorem pair_breakTentWeight_sub {β T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    breakTentWeight (1 - β) T x - breakTentWeight β T x =
      Real.exp (π / T) * x *
        (Real.exp (-(π * cellFraction β T x / T)) - Real.exp (-(π * cellFraction (1 - β) T x / T))) := by
  rw [breakTentWeight_eq hT hx, breakTentWeight_eq hT hx]
  ring

#print axioms RHV6Fresh.breakTentWeight_eq
#print axioms RHV6Fresh.breakTentWeight_prev_eq
#print axioms RHV6Fresh.breakTentWeight_nonneg
#print axioms RHV6Fresh.break_amplitude_reads_tent
#print axioms RHV6Fresh.localGrammarTerm_break_split
#print axioms RHV6Fresh.tent_difference_eq_sawtooth
#print axioms RHV6Fresh.alternating_break_weight
#print axioms RHV6Fresh.sawtooth_pos_iff
#print axioms RHV6Fresh.pair_breakTentWeight_eq_iff
#print axioms RHV6Fresh.pair_breakTentWeight_sub

end RHV6Fresh
