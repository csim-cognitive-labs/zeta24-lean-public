/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ExactAxisReading
import RHV6Fresh.Terminal.InverseReading
import RHV6Fresh.Terminal.SpectralUniqueness

/-!
# RHV6Fresh — demande exacte d'une marche, réponse collective, diagonale et croisés, dette (E137bis, auteur, 2026-10-03)

Flèche consolidée de l'auteur (E103 + E137 + E154 + E155) : écart exact `g = 6a + r` → demande exacte de la marche
(poids du premier atteint moins l'avance du fond) → réponse collective de toutes les Tours → diagonale (énergies
individuelles) et croisés (renforcements et compensations) → dette d'un membre hors ligne.

* **Demande d'une marche pure** (§1) : entre deux premiers consécutifs sans puissance de premier intercalée, la
  somme des poids est le poids du premier atteint (`pure_step_weight_sum`) ; la demande est ce poids moins l'avance
  du fond (`pure_step_demand`), et l'écart s'y lit par sa magnitude et sa classe (`pure_step_demand_magnitude`).
  La réponse collective est forcée : `remainderBetween_eq_spectral`, `complementBetween_forced` (déjà compilés).
* **Diagonale et croisés** (§2) : pour toute famille finie de contributions, le carré de la réponse est la
  diagonale plus les croisés, les croisés étant la somme hors diagonale (`stepCross_eq_offDiagonal`) ; une fois la
  réponse fixée par la demande, les croisés valent demande² − diagonale (`stepCross_forced_by_demand`), négatifs
  ⟺ la diagonale dépasse le carré de la demande (`stepCross_neg_iff`) ; des contributions de même signe ne se
  compensent pas (`stepCross_nonneg_of_aligned`) ; changer les signes ne change pas la diagonale
  (`stepDiagonal_sign_invariant`) : la diagonale ne voit pas les compensations.
* **La dette ne se cache pas sur toute l'histoire** (§3) : un membre hors ligne garde son poids dans toute
  représentation spectrale du même reste exact (aucune réorganisation des autres membres ne l'efface), et il force
  l'exposant du reste au-dessus de `1/2` (`off_debt_visible_in_exponent`, `compensation_closure_verdict`).

Borne : la rigidité de compensation est l'unicité de la représentation spectrale ; elle dit qu'un hors-ligne laisse
une dette visible dans l'exposant du reste, elle ne dit pas que l'exposant du reste de zêta vaut `1/2`
(`riemannHypothesis_iff_remainderExponent_eq_half`). Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction

/-! ## 1. La demande exacte d'une marche pure -/

/-- **Marche pure** : sans puissance de premier entre `p` et `q`, les poids de `]p, q]` se réduisent au poids de `q`. -/
theorem pure_step_weight_sum {p q : ℕ} (hpq : p < q) (hq : q.Prime)
    (hpure : ∀ n ∈ Finset.Ioo p q, Λ n = 0) :
    ∑ n ∈ Finset.Ioc p q, Λ n = Real.log q := by
  rw [← Finset.Ioo_insert_right hpq, Finset.sum_insert (by simp), Finset.sum_eq_zero hpure, add_zero,
    vonMangoldt_apply_prime hq]

/-- **Demande exacte d'une marche pure** : le poids du premier atteint moins l'avance du fond. -/
theorem pure_step_demand {p q : ℕ} (hpq : p < q) (hq : q.Prime)
    (hpure : ∀ n ∈ Finset.Ioo p q, Λ n = 0) :
    remainderBetween p q =
      ((Real.log q : ℝ) : ℂ) - (stepAt backgroundPrimitive q - stepAt backgroundPrimitive p) := by
  rw [remainderBetween_arithmetic hpq.le, pure_step_weight_sum hpq hq hpure]

/-- **L'écart y entre par sa magnitude et sa classe** : `g = 6a + r`, et la demande est le poids du premier atteint
moins `6a + r`, moins l'écart entre l'avance du fond et l'écart. -/
theorem pure_step_demand_magnitude {p q : ℕ} (hpq : p < q) (hq : q.Prime)
    (hpure : ∀ n ∈ Finset.Ioo p q, Λ n = 0) :
    remainderBetween p q =
      ((Real.log q : ℝ) : ℂ) - ((6 * ((q - p) / 6) + (q - p) % 6 : ℕ) : ℂ) -
        ((stepAt backgroundPrimitive q - stepAt backgroundPrimitive p) - ((q : ℂ) - p)) := by
  rw [pure_step_demand hpq hq hpure, Nat.div_add_mod, Nat.cast_sub hpq.le]
  ring

/-! ## 2. Diagonale et croisés de la réponse collective -/

section Split

variable {ι : Type*}

/-- **Diagonale d'une marche** : la somme des énergies individuelles des contributions. -/
def stepDiagonal (s : Finset ι) (c : ι → ℝ) : ℝ := ∑ i ∈ s, c i ^ 2

/-- **Croisés d'une marche** : carré de la réponse moins la diagonale (renforcements et compensations). -/
def stepCross (s : Finset ι) (c : ι → ℝ) : ℝ := (∑ i ∈ s, c i) ^ 2 - stepDiagonal s c

/-- **Les croisés sont la somme hors diagonale** des produits de deux contributions distinctes. -/
theorem stepCross_eq_offDiagonal [DecidableEq ι] (s : Finset ι) (c : ι → ℝ) :
    stepCross s c = ∑ i ∈ s, ∑ j ∈ s.erase i, c i * c j := by
  unfold stepCross stepDiagonal
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.add_sum_erase s (fun j => c i * c j) hi]
  ring

/-- **Carré de la réponse = diagonale + croisés.** -/
theorem response_sq_eq_diagonal_add_cross (s : Finset ι) (c : ι → ℝ) :
    (∑ i ∈ s, c i) ^ 2 = stepDiagonal s c + stepCross s c := by
  unfold stepCross
  ring

/-- **Croisés forcés par la demande** : si la réponse vaut la demande, les croisés valent demande² − diagonale. -/
theorem stepCross_forced_by_demand (s : Finset ι) (c : ι → ℝ) {S : ℝ} (h : ∑ i ∈ s, c i = S) :
    stepCross s c = S ^ 2 - stepDiagonal s c := by
  unfold stepCross
  rw [h]

/-- **Compensation nette** ⟺ la diagonale dépasse le carré de la demande. -/
theorem stepCross_neg_iff (s : Finset ι) (c : ι → ℝ) {S : ℝ} (h : ∑ i ∈ s, c i = S) :
    stepCross s c < 0 ↔ S ^ 2 < stepDiagonal s c := by
  rw [stepCross_forced_by_demand s c h]
  constructor <;> intro h' <;> linarith

/-- **Des contributions de même signe ne se compensent pas.** -/
theorem stepCross_nonneg_of_aligned [DecidableEq ι] (s : Finset ι) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) :
    0 ≤ stepCross s c := by
  rw [stepCross_eq_offDiagonal]
  exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
    mul_nonneg (hc i hi) (hc j (Finset.mem_of_mem_erase hj))

/-- **La diagonale ne voit pas les signes** : changer le signe de chaque contribution ne la change pas. -/
theorem stepDiagonal_sign_invariant (s : Finset ι) (c ε : ι → ℝ) (hε : ∀ i, |ε i| = 1) :
    stepDiagonal s (fun i => ε i * c i) = stepDiagonal s c := by
  unfold stepDiagonal
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← sq_abs (ε i), hε, one_pow, one_mul]

end Split

/-! ## 3. La dette d'un hors-ligne ne se cache pas sur toute l'histoire -/

/-- **La dette est visible dans l'exposant du reste** : un membre hors ligne force `θ* > 1/2`. -/
theorem off_debt_visible_in_exponent {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    1 / 2 < remainderExponent := by
  have h := mirror_pair_exponent_le_remainderExponent z
  have hne : rZeroRadialPosition z.1 ≠ 1 / 2 := hOff
  refine lt_of_lt_of_le ?_ h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  · exact lt_of_lt_of_le hgt (le_max_left _ _)

/-- **Verdict de la rigidité de compensation** : un membre hors ligne garde un poids non nul hors de la ligne dans
toute représentation spectrale du reste exact (aucune réorganisation des autres membres ne l'efface), et il force
l'exposant du reste au-dessus de `1/2`. -/
theorem compensation_closure_verdict {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    (∀ (ι : Type) (Rep : SpectralRepresentation ι), ∃ i, Rep.weight i ≠ 0 ∧ (Rep.point i).re ≠ 1 / 2) ∧
      1 / 2 < remainderExponent :=
  ⟨fun _ Rep => Rep.off_identity_not_erased hOff, off_debt_visible_in_exponent hOff⟩


end RHV6Fresh
