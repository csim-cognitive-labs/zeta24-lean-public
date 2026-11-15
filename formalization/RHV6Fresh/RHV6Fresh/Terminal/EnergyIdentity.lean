/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GeometricEnergyRaccord
import RHV6Fresh.Terminal.VerticalEnergyPush
import RHV6Fresh.Terminal.SuccessionInvariants

/-!
# `Terminal/EnergyIdentity.lean` — sélection géométrique du raccord, identité `log(A_l/A_e) = H − V`

Demande de l'auteur (2026-09-29) : sélectionner intrinsèquement la cellule du raccord, formaliser
séparément l'énergie verticale `V(e,l) = log‖ρ_l‖ − log‖ρ_e‖` et l'horizontale
`H(e,l,q) = (β_l − β_e) log q`, poser l'identité exacte `log(A_l/A_e) = H − V`.

Compilé ici, sans prémisse : (1) `geometry_selects_raccord_prime` ; (2) `log_amplitude_ratio_eq` ;
(3) `amplitude_le_iff_horizontal_le_vertical` ; (4) à même hauteur, `V` est bornée par `H` dès que
`q` dépasse un seuil explicite (`sameHeight_horizontal_dominates`).

NON compilé, et non compilable sans prémisse : « `V ≥ H` au raccord sélectionné ». C'est
`PVerticalDominatesAtRaccord` ci-dessous, impliquée par `PVerticalEnergyPush` (∀ q ≥ 1) ; sa
vérité sur un passage OFF n'est pas un théorème du code. Voir le verdict en fin de fichier.
-/

namespace RHV6Fresh
open RHV3Lean

/-- Énergie verticale : gain de norme de `ρ` de `e` à `l`. -/
noncomputable def verticalEnergy (e l : TrueZero) : ℝ :=
  Real.log ‖zeroPoint l‖ - Real.log ‖zeroPoint e‖

/-- Énergie horizontale : écart radial fois `log q`. -/
noncomputable def horizontalEnergy (e l : TrueZero) (q : ℝ) : ℝ :=
  (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * Real.log q

/-- **(1) La géométrie sélectionne le raccord.** La cellule `(C⁻,C⁺]` de la Tour de `e` sélectionnée
par `pivotCoordinate` porte `q₁ = p_min(e) = Occ(l)`, celle de la Tour de `l` porte `q₂ = p_min(l)`,
et toute coordonnée dont la cellule contient `q` est cette coordonnée (unicité) : aucun sélecteur
externe, `q` n'est lu que comme point à localiser. -/
theorem geometry_selects_raccord_prime (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    let e : TrueZero := ⟨p.zEarlierMember, hE⟩
    let l : TrueZero := ⟨p.zLaterMember, hL⟩
    occurrence l = expectedMinimumPrime e ∧
    (contactMinusAt e (pivotCoordinate e (expectedMinimumPrime e : ℝ)) < (expectedMinimumPrime e : ℝ) ∧
      (expectedMinimumPrime e : ℝ) ≤ contactPlusAt e (pivotCoordinate e (expectedMinimumPrime e : ℝ))) ∧
    (contactMinusAt l (pivotCoordinate l (expectedMinimumPrime l : ℝ)) < (expectedMinimumPrime l : ℝ) ∧
      (expectedMinimumPrime l : ℝ) ≤ contactPlusAt l (pivotCoordinate l (expectedMinimumPrime l : ℝ))) ∧
    (∀ k : ℤ, contactMinusAt e k < (expectedMinimumPrime e : ℝ) →
      (expectedMinimumPrime e : ℝ) ≤ contactPlusAt e k →
        k = pivotCoordinate e (expectedMinimumPrime e : ℝ)) := by
  intro e l
  refine ⟨(passage_raccords p hE hL).1, ?_, ?_, ?_⟩
  · exact prime_raccord_has_unique_tower_cell e (by exact_mod_cast expectedMinimumPrime_pos e)
  · exact prime_raccord_has_unique_tower_cell l (by exact_mod_cast expectedMinimumPrime_pos l)
  · intro k h1 h2
    exact pivotCoordinate_unique e (by exact_mod_cast expectedMinimumPrime_pos e) h1 h2

/-- **(2) L'identité exacte** : `log‖zeroTerm l q‖ − log‖zeroTerm e q‖ = H − V`. -/
theorem log_amplitude_ratio_eq (e l : TrueZero) {q : ℝ} (hq : 0 < q) :
    Real.log ‖zeroTerm l q‖ - Real.log ‖zeroTerm e q‖ =
      horizontalEnergy e l q - verticalEnergy e l := by
  have hl : 0 < ‖zeroPoint l‖ := norm_pos_iff.mpr (zeroPoint_ne_zero l)
  have he : 0 < ‖zeroPoint e‖ := norm_pos_iff.mpr (zeroPoint_ne_zero e)
  have hql : 0 < q ^ rZeroRadialPosition l.1 := Real.rpow_pos_of_pos hq _
  have hqe : 0 < q ^ rZeroRadialPosition e.1 := Real.rpow_pos_of_pos hq _
  rw [zeroTerm_norm hq, zeroTerm_norm hq, Real.log_div hql.ne' hl.ne',
    Real.log_div hqe.ne' he.ne', Real.log_rpow hq, Real.log_rpow hq]
  unfold horizontalEnergy verticalEnergy
  ring

/-- **(3) Le résidu P7 est exactement `H ≤ V`.** -/
theorem amplitude_le_iff_horizontal_le_vertical (e l : TrueZero) {q : ℝ} (hq : 0 < q) :
    ‖zeroTerm l q‖ ≤ ‖zeroTerm e q‖ ↔ horizontalEnergy e l q ≤ verticalEnergy e l := by
  have hl : 0 < ‖zeroTerm l q‖ := by
    rw [zeroTerm_norm hq]
    exact div_pos (Real.rpow_pos_of_pos hq _) (norm_pos_iff.mpr (zeroPoint_ne_zero l))
  have he : 0 < ‖zeroTerm e q‖ := by
    rw [zeroTerm_norm hq]
    exact div_pos (Real.rpow_pos_of_pos hq _) (norm_pos_iff.mpr (zeroPoint_ne_zero e))
  have h := log_amplitude_ratio_eq e l hq
  rw [← Real.log_le_log_iff hl he]
  constructor <;> intro h' <;> linarith

/-- **(4) À même hauteur, `V` ne compense pas `H > 0`** dès que `q` dépasse le seuil `exp(V/Δβ)` :
alors `A_l(q) > A_e(q)`, l'inégalité du résidu est fausse. -/
theorem sameHeight_horizontal_dominates (e l : TrueZero)
    (hβ : rZeroRadialPosition e.1 < rZeroRadialPosition l.1) {q : ℝ} (hq : 0 < q)
    (hthr : Real.exp (verticalEnergy e l / (rZeroRadialPosition l.1 - rZeroRadialPosition e.1)) < q) :
    ‖zeroTerm e q‖ < ‖zeroTerm l q‖ := by
  have hd : 0 < rZeroRadialPosition l.1 - rZeroRadialPosition e.1 := sub_pos.mpr hβ
  have h1 : verticalEnergy e l / (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) < Real.log q :=
    (Real.lt_log_iff_exp_lt hq).mpr hthr
  have h2 : verticalEnergy e l < horizontalEnergy e l q := by
    unfold horizontalEnergy
    have := (div_lt_iff₀ hd).mp h1
    linarith
  by_contra hn
  exact absurd ((amplitude_le_iff_horizontal_le_vertical e l hq).mp (not_lt.mp hn)) (not_le.mpr h2)

#print axioms geometry_selects_raccord_prime
#print axioms log_amplitude_ratio_eq
#print axioms amplitude_le_iff_horizontal_le_vertical
#print axioms sameHeight_horizontal_dominates
end RHV6Fresh
