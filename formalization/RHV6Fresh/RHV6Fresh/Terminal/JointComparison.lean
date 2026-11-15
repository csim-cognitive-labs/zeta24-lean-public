/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.StageCell

/-!
# Lecture conjointe de la fibre d'arrivée : majorations séparées et comparaison stricte (auteur, 2026-10-11)

Décomposition exacte (canal lissé, `expected_next_fiber`) : `Y := R − P_H = F + Q_{H'}`, avec `P_H` l'historique (fini),
`F` la fibre `]H, H']` (groupe d'arrivée, miroirs et multiplicités compris), `Q_{H'}` le complément infini. Sur une famille
finie d'abscisses `x_r > 1` et de poids `λ_r` :

* §1 majoration INDÉPENDANTE de la lecture conjointe de l'attendu `Σλ_r Y(x_r)`, sans passer par l'identité : reste par la
  borne démontrée d'exposant `1` (`smoothedRemainder_linear_growth`, constante `C` en paramètre), historique ON par
  `precedingBudget·√x` ;
* §2 majoration du complément entier, résidu compris : `‖Σλ_r Q(x_r)‖ ≤ budget(H')·M` dès que chaque profil de la queue
  vérifie `‖Σλ_r x_r^σ‖ ≤ M` (`tail_joint_functional_bound`, rappelé) ;
* §3 PLAFOND du signal de la fibre : `‖Σλ_r F(x_r)‖ ≤ fiberBudget·Σ|λ_r| x_r` (toute minoration démontrée du signal signé,
  phases et dénominateurs compris, est sous ce plafond) ;
* §4 fermeture : si le signal dépasse STRICTEMENT la majoration indépendante de l'attendu plus la compensation maximale du
  complément, la même reconstruction ne satisfait pas les deux bornes (`joint_comparison_closes`) ;
* §5 condition NÉCESSAIRE de cette comparaison avec la seule borne d'exposant `1` du reste : `C < fiberBudget`
  (`joint_comparison_requires`). Avec une majoration indépendante de la forme `C·x^θ`, la condition porte sur `θ` et sur la
  constante (§6, `joint_comparison_requires_exponent`).

Aucune prémisse : tout est démontré (axiomes standard). La minoration du signal signé n'est PAS démontrée ici.
-/

namespace RHV6Fresh

open RHV3Lean

/-- Masse totale des coefficients de la fibre `]H, H']`. -/
noncomputable def fiberBudget (H H' : ℝ) : ℝ := ∑' σ : ExplicitIndex, ‖fiberWeight H H' σ‖

theorem fiberBudget_nonneg (H H' : ℝ) : 0 ≤ fiberBudget H H' := tsum_nonneg fun _ => norm_nonneg _

/-- **Plafond ponctuel de la fibre** : `‖F(x)‖ ≤ fiberBudget·x` pour `x > 1` (par `Re σ ≤ 1`). -/
theorem nextFiberSum_norm_le (H H' : ℝ) {x : ℝ} (hx : 1 < x) :
    ‖nextFiberSum H H' x‖ ≤ fiberBudget H H' * x := by
  have hx0 : 0 < x := lt_trans one_pos hx
  have hterm : ∀ σ : ExplicitIndex, ‖fiberWeight H H' σ * (x : ℂ) ^ (σ : ℂ)‖ ≤ ‖fiberWeight H H' σ‖ * x := by
    intro σ
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc x ^ (σ : ℂ).re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (explicitIndex_re_le_one σ)
      _ = x := Real.rpow_one x
  have hdom : Summable fun σ : ExplicitIndex => ‖fiberWeight H H' σ‖ * x :=
    (fiberWeight_norm_summable H H').mul_right _
  have hs : Summable fun σ : ExplicitIndex => ‖fiberWeight H H' σ * (x : ℂ) ^ (σ : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hdom
  rw [nextFiberSum_eq_tsum H H' hx]
  calc ‖∑' σ : ExplicitIndex, fiberWeight H H' σ * (x : ℂ) ^ (σ : ℂ)‖
      ≤ ∑' σ : ExplicitIndex, ‖fiberWeight H H' σ * (x : ℂ) ^ (σ : ℂ)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' σ : ExplicitIndex, ‖fiberWeight H H' σ‖ * x := Summable.tsum_le_tsum hterm hs hdom
    _ = fiberBudget H H' * x := by unfold fiberBudget; exact tsum_mul_right

/-- **§3 Plafond conjoint du signal** : `‖Σ_r λ_r F(x_r)‖ ≤ fiberBudget·Σ_r |λ_r| x_r`. -/
theorem fiber_joint_le (H H' : ℝ) {n : ℕ} (x : Fin n → ℝ) (lam : Fin n → ℂ) (hx : ∀ r, 1 < x r) :
    ‖∑ r, lam r * nextFiberSum H H' (x r)‖ ≤ fiberBudget H H' * ∑ r, ‖lam r‖ * x r := by
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul]
  calc ‖lam r‖ * ‖nextFiberSum H H' (x r)‖ ≤ ‖lam r‖ * (fiberBudget H H' * x r) :=
        mul_le_mul_of_nonneg_left (nextFiberSum_norm_le H H' (hx r)) (norm_nonneg _)
    _ = fiberBudget H H' * (‖lam r‖ * x r) := by ring

/-- **§1 Majoration indépendante de l'attendu** sous un historique ON jusqu'à `H` et une borne `‖R(x)‖ ≤ C·x` :
`‖Σλ_r (R − P_H)(x_r)‖ ≤ Σ_r |λ_r| (C·x_r + B_H·√x_r)`. Elle ne passe pas par l'identité `Y = F + Q`. -/
theorem history_joint_bound {H C : ℝ} (hC : ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 : ℝ))
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ H → rZeroRadialPosition w.1 = 1 / 2)
    {n : ℕ} (x : Fin n → ℝ) (lam : Fin n → ℂ) (hx : ∀ r, 1 < x r) :
    ‖∑ r, lam r * (smoothedRemainder (x r) - precedingSum H (x r))‖ ≤
      ∑ r, ‖lam r‖ * (C * x r + precedingBudget H * x r ^ (1 / 2 : ℝ)) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 := hC (x r) (hx r)
  rw [Real.rpow_one] at h1
  exact (norm_sub_le _ _).trans (add_le_add h1 (precedingSum_le_budget_of_onLine hOn (hx r)))

/-- **§4 Fermeture par comparaison stricte** : si la lecture conjointe du signal de la fibre dépasse strictement la
majoration indépendante de l'attendu plus la majoration du complément entier (`budget(H')·M`), la
reconstruction exacte est contredite. -/
theorem joint_comparison_closes {H H' C : ℝ}
    (hC : ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 : ℝ))
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ H → rZeroRadialPosition w.1 = 1 / 2)
    (h : ∃ (n : ℕ) (x : Fin n → ℝ) (lam : Fin n → ℂ) (M : ℝ), (∀ r, 1 < x r) ∧
      (∀ σ : ExplicitIndex, H' < |(σ : ℂ).im| → ‖∑ r, lam r * (x r : ℂ) ^ (σ : ℂ)‖ ≤ M) ∧
      ∑ r, ‖lam r‖ * (C * x r + precedingBudget H * x r ^ (1 / 2 : ℝ)) + followingBudget H' * M <
        ‖∑ r, lam r * nextFiberSum H H' (x r)‖) : False := by
  obtain ⟨n, x, lam, M, hx, hM, hStrict⟩ := h
  have hQ := expected_next_fiber_joint H H' Finset.univ x lam (fun r _ => hx r) hM
  have hY := history_joint_bound hC hOn x lam hx
  have htri := norm_sub_norm_le (∑ r, lam r * (smoothedRemainder (x r) - precedingSum H (x r)))
    (∑ r, lam r * nextFiberSum H H' (x r))
  have htri' := norm_sub_le (∑ r, lam r * (smoothedRemainder (x r) - precedingSum H (x r)))
    (∑ r, lam r * nextFiberSum H H' (x r))
  have hsub : ‖∑ r, lam r * nextFiberSum H H' (x r)‖ ≤
      ‖∑ r, lam r * (smoothedRemainder (x r) - precedingSum H (x r))‖ +
        ‖∑ r, lam r * (smoothedRemainder (x r) - precedingSum H (x r))
          - ∑ r, lam r * nextFiberSum H H' (x r)‖ := by
    have := norm_sub_le (∑ r, lam r * (smoothedRemainder (x r) - precedingSum H (x r)))
      (∑ r, lam r * (smoothedRemainder (x r) - precedingSum H (x r)) - ∑ r, lam r * nextFiberSum H H' (x r))
    simpa using this
  linarith

/-- **§5 Condition nécessaire** de la comparaison stricte avec la borne d'exposant `1` du reste : la masse de la fibre
dépasse la constante `C` (`M ≥ 0`). Avec la seule borne de Chebyshev, la lecture conjointe ne ferme que si
`C < fiberBudget`. -/
theorem joint_comparison_requires {H H' C : ℝ} {n : ℕ} (x : Fin n → ℝ) (lam : Fin n → ℂ)
    (hx : ∀ r, 1 < x r) {M : ℝ} (hM0 : 0 ≤ M)
    (hStrict : ∑ r, ‖lam r‖ * (C * x r + precedingBudget H * x r ^ (1 / 2 : ℝ)) + followingBudget H' * M <
      ‖∑ r, lam r * nextFiberSum H H' (x r)‖) (hBnn : 0 ≤ precedingBudget H) :
    C < fiberBudget H H' := by
  have hcap := fiber_joint_le H H' x lam hx
  have hFb : 0 ≤ followingBudget H' * M :=
    mul_nonneg (tsum_nonneg fun _ => norm_nonneg _) hM0
  have hge : C * ∑ r, ‖lam r‖ * x r ≤ ∑ r, ‖lam r‖ * (C * x r + precedingBudget H * x r ^ (1 / 2 : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    have : 0 ≤ ‖lam r‖ * (precedingBudget H * x r ^ (1 / 2 : ℝ)) :=
      mul_nonneg (norm_nonneg _) (mul_nonneg hBnn (Real.rpow_nonneg (by linarith [hx r]) _))
    nlinarith
  have hS : 0 ≤ ∑ r, ‖lam r‖ * x r :=
    Finset.sum_nonneg fun r _ => mul_nonneg (norm_nonneg _) (by linarith [hx r])
  have hlt : C * ∑ r, ‖lam r‖ * x r < fiberBudget H H' * ∑ r, ‖lam r‖ * x r := by linarith
  rcases hS.lt_or_eq with hSpos | hS0
  · exact lt_of_mul_lt_mul_right hlt hSpos.le
  · rw [← hS0] at hlt; simp at hlt

/-- **§6 Forme à exposant** : si la majoration indépendante du reste est `‖R(x)‖ ≤ C·x^θ` et que la fibre a ses profils
d'exposant au plus `η` (`‖F(x)‖ ≤ K·x^η`), une comparaison stricte en un point `x > 1` exige `C·x^θ < K·x^η` : pour
`θ ≥ η` et `x ≥ 1`, elle exige `C < K`. -/
theorem joint_comparison_requires_exponent {C K θ η x : ℝ} (hx : 1 ≤ x) (hθη : η ≤ θ) (hC0 : 0 ≤ C)
    (h : C * x ^ θ < K * x ^ η) : C < K := by
  have hxθ : x ^ η ≤ x ^ θ := Real.rpow_le_rpow_of_exponent_le hx hθη
  have hpos : 0 < x ^ η := Real.rpow_pos_of_pos (by linarith) _
  by_contra hK
  push Not at hK
  have : K * x ^ η ≤ C * x ^ θ :=
    calc K * x ^ η ≤ C * x ^ η := mul_le_mul_of_nonneg_right hK hpos.le
      _ ≤ C * x ^ θ := mul_le_mul_of_nonneg_left hxθ hC0
  linarith

#print axioms fiber_joint_le
#print axioms history_joint_bound
#print axioms joint_comparison_closes
#print axioms joint_comparison_requires
#print axioms joint_comparison_requires_exponent

end RHV6Fresh
