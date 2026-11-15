/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FixedExponentField
import RHV6Fresh.Terminal.RemainderExponent
import RHV6Fresh.Terminal.NoRegimeChange

/-!
# RHV6Fresh — financement de l'évasion d'une Tour par le reste exact (auteur, 2026-10-03)

Route de l'auteur : fond déterministe → poids premiers exacts = impulsions → phases → reste = somme exacte des
écarts → amplitude = mesure de la possibilité d'évasion ; comparer l'excès radial nécessaire à l'évasion d'une
Tour à ce que le reste exact peut financer, sans supposer de borne critique.

* **§1 Le besoin** : une Tour d'exposant plus grand dépasse tout multiple du champ (`escape_exceeds_any_multiple`).
* **§2 Le financement est obligatoire** : toute borne `C·x^θ` du reste exact est un mur pour chaque Tour
  (`tower_captive_of_remainder_wall`) ; une Tour au-dessus de la ligne oblige le reste à dépasser tout `C·x^θ`,
  `θ < β` (`escape_must_be_financed`).
* **§3 Le disponible depuis les poids exacts** : positivité et Chebyshev donnent le mur `x¹`
  (`financing_ledger`) : le disponible démontré couvre le besoin, la comparaison ne ferme pas.
* **§4 Règle minimale (TDD)** : `RemainderCaptive z`, « la somme de toutes les Tours reste dans le champ d'une
  seule Tour et de son miroir ». Captive d'un seul côté : la Tour est au sommet (`captive_one_side_summit`) ;
  captive des deux côtés : la Tour est en ligne et l'hypothèse de Riemann suit
  (`remainderCaptive_onLine`, `riemannHypothesis_of_remainderCaptive`) ; équivalence
  (`remainderCaptive_iff_riemannHypothesis`) ; la prison de chaque Tour en découle (`prison_of_remainderCaptive`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Le besoin -/

/-- **Une Tour d'exposant plus grand dépasse tout multiple du champ.** -/
theorem escape_exceeds_any_multiple {z₁ w : TrueZero}
    (hgt : rZeroRadialPosition z₁.1 < rZeroRadialPosition w.1) {K : ℝ} (hK : 0 < K) :
    ∃ x : ℝ, 1 ≤ x ∧ K * firstField z₁ x < ‖zeroTerm w x‖ := by
  by_contra hno
  push Not at hno
  have := exponent_le_of_inside (β := rZeroRadialPosition w.1) (γ := rZeroRadialPosition z₁.1)
    (norm_zeroPoint_pos w) (div_pos (norm_zeroPoint_pos z₁) hK) (fun x hx => by
      have h := hno x hx
      unfold firstField at h
      rw [norm_zeroTerm_eq w (by linarith), norm_zeroTerm_eq z₁ (by linarith)] at h
      have e : x ^ rZeroRadialPosition z₁.1 / (‖zeroPoint z₁‖ / K) =
          K * (x ^ rZeroRadialPosition z₁.1 / ‖zeroPoint z₁‖) := by
        field_simp
      rw [e]; exact h)
  linarith

/-! ## 2. Le financement est obligatoire -/

/-- **Toute borne du reste exact est un mur pour chaque Tour.** -/
theorem tower_captive_of_remainder_wall {θ C : ℝ}
    (h : ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ θ) (w : TrueZero) {x : ℝ} (hx : 1 ≤ x) :
    ‖zeroTerm w x‖ ≤ x ^ θ / ‖zeroPoint w‖ := by
  rw [norm_zeroTerm_eq w (by linarith)]
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hx (radial_le_of_remainder_growth h w)) (norm_zeroPoint_pos w).le

/-- **L'évasion se paie dans le reste exact** : une Tour d'exposant `β` oblige le reste à dépasser toute borne
`C·x^θ` avec `θ < β`. -/
theorem escape_must_be_financed (w : TrueZero) {θ : ℝ} (hθ : θ < rZeroRadialPosition w.1) (C : ℝ) :
    ∃ x : ℝ, 1 < x ∧ C * x ^ θ < ‖smoothedRemainder x‖ := by
  by_contra hno
  push Not at hno
  have := radial_le_of_remainder_growth hno w
  linarith

/-! ## 3. Le disponible depuis les poids exacts -/

/-- **Registre du financement** : depuis la positivité des poids et Chebyshev, le reste exact est borné par
`C·x`, et tout exposant de Tour est `≤ 1`. Le disponible démontré couvre le besoin de toute Tour. -/
theorem financing_ledger :
    ∃ C : ℝ, (∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 : ℝ)) ∧
      ∀ w : TrueZero, rZeroRadialPosition w.1 ≤ 1 := by
  obtain ⟨C, hC⟩ := smoothedRemainder_linear_growth
  exact ⟨C, hC, fun w => radial_le_of_remainder_growth hC w⟩

/-! ## 4. Règle minimale -/

/-- **Le reste exact est captif de la Tour `z` et de son miroir** : une seule constante, la somme de toutes les
Tours ne dépasse ni l'amplitude de la Tour de `z` ni celle de la Tour de son miroir. -/
def RemainderCaptive (z : TrueZero) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 1 < x →
    ‖smoothedRemainder x‖ ≤ C * ‖zeroTerm z x‖ ∧ ‖smoothedRemainder x‖ ≤ C * ‖zeroTerm (mirrorMember z) x‖

/-- **Captif d'un seul côté** : si le reste exact ne dépasse pas la Tour de `z`, cette Tour est au sommet,
aucun exposant ne dépasse le sien, et il vaut au moins `1/2`. -/
theorem captive_one_side_summit {z : TrueZero} {C : ℝ}
    (h : ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * ‖zeroTerm z x‖) :
    (∀ w : TrueZero, rZeroRadialPosition w.1 ≤ rZeroRadialPosition z.1) ∧
      1 / 2 ≤ rZeroRadialPosition z.1 := by
  have hb : ∀ x : ℝ, 1 < x →
      ‖smoothedRemainder x‖ ≤ (C / ‖zeroPoint z‖) * x ^ rZeroRadialPosition z.1 := fun x hx => by
    have := h x hx
    rw [norm_zeroTerm_eq z (by linarith)] at this
    calc ‖smoothedRemainder x‖ ≤ C * (x ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖) := this
      _ = (C / ‖zeroPoint z‖) * x ^ rZeroRadialPosition z.1 := by ring
  have hall : ∀ w : TrueZero, rZeroRadialPosition w.1 ≤ rZeroRadialPosition z.1 :=
    fun w => radial_le_of_remainder_growth hb w
  refine ⟨hall, ?_⟩
  have := hall (mirrorMember z)
  rw [mirrorMember_radial] at this
  linarith

/-- **Captif des deux côtés : la Tour est en ligne.** -/
theorem remainderCaptive_onLine {z : TrueZero} (h : RemainderCaptive z) :
    rZeroRadialPosition z.1 = 1 / 2 := by
  obtain ⟨C, hC⟩ := h
  have h1 := (captive_one_side_summit fun x hx => (hC x hx).1).2
  have h2 := (captive_one_side_summit fun x hx => (hC x hx).2).2
  rw [mirrorMember_radial] at h2
  linarith

/-- **Règle minimale ⟹ hypothèse de Riemann.** -/
theorem riemannHypothesis_of_remainderCaptive {z : TrueZero} (h : RemainderCaptive z) :
    RiemannHypothesis := by
  have hz := remainderCaptive_onLine h
  obtain ⟨C, hC⟩ := h
  have hall := (captive_one_side_summit fun x hx => (hC x hx).1).1
  refine thm_riemannHypothesis_of_allUpperOnCriticalLine fun w => ?_
  have h1 := hall w
  have h2 := hall (mirrorMember w)
  rw [mirrorMember_radial] at h2
  linarith

/-- **La règle minimale équivaut à l'hypothèse de Riemann**, pour n'importe quelle Tour. -/
theorem remainderCaptive_iff_riemannHypothesis :
    (∃ z : TrueZero, RemainderCaptive z) ↔ RiemannHypothesis := by
  refine ⟨fun ⟨_, h⟩ => riemannHypothesis_of_remainderCaptive h, fun hRH => ?_⟩
  obtain ⟨z, -, -⟩ := exists_two_heights
  obtain ⟨C, hC⟩ := riemannHypothesis_iff_remainder_sqrt_growth.mp hRH
  have hz := thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1
  have hm := thm_zeroRadialPosition_half_of_riemannHypothesis hRH (mirrorMember z).1
  have bound : ∀ v : TrueZero, rZeroRadialPosition v.1 = 1 / 2 → ∀ x : ℝ, 1 < x →
      ‖smoothedRemainder x‖ ≤ (|C| * ‖zeroPoint v‖) * ‖zeroTerm v x‖ := by
    intro v hv x hx
    have hx0 : 0 < x := by linarith
    rw [norm_zeroTerm_eq v hx0, hv]
    have hp := norm_zeroPoint_pos v
    have e : |C| * ‖zeroPoint v‖ * (x ^ (1 / 2 : ℝ) / ‖zeroPoint v‖) = |C| * x ^ (1 / 2 : ℝ) := by
      field_simp
    rw [e]
    exact (hC x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx0.le _))
  refine ⟨z, |C| * (‖zeroPoint z‖ + ‖zeroPoint (mirrorMember z)‖), fun x hx => ⟨?_, ?_⟩⟩
  · refine (bound z hz x hx).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (zeroPoint (mirrorMember z))]) (abs_nonneg C)
  · refine (bound _ hm x hx).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (zeroPoint z)]) (abs_nonneg C)

/-- **La prison de chaque Tour découle de la règle minimale.** -/
theorem prison_of_remainderCaptive {z : TrueZero} (h : RemainderCaptive z) (p : TZeroPassage) :
    TowerPrisoner p :=
  prison_of_riemannHypothesis (riemannHypothesis_of_remainderCaptive h) p

#print axioms escape_exceeds_any_multiple
#print axioms tower_captive_of_remainder_wall
#print axioms escape_must_be_financed
#print axioms financing_ledger
#print axioms captive_one_side_summit
#print axioms remainderCaptive_onLine
#print axioms riemannHypothesis_of_remainderCaptive
#print axioms remainderCaptive_iff_riemannHypothesis
#print axioms prison_of_remainderCaptive

end RHV6Fresh
