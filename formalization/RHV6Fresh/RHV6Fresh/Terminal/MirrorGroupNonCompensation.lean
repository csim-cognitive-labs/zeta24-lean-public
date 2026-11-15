/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.StageCell
import RHV6Fresh.Terminal.RemainderExponent

/-!
# Le miroir du membre bas dans un groupe fini de suivants : non-compensation (auteur, 2026-10-11)

Directive de l'auteur : « la disqualification du zéro OFF `< 1/2` passe par son miroir ; c'est lui qui viole la règle de la
progression en hauteur, et sa contribution au reste le trahit ; la première enveloppe est fortement consommée ; établir un
reste à consommer par un groupe fini de zéros suivants et démontrer, sur ce groupe, la non-compensation de la contribution
erratique d'un zéro OFF ».

Canal lissé (seule représentation démontrée). Pour un historique `H` (le premier zéro et tous les membres ON sous le départ,
`P_H`, « première enveloppe consommée ») et une coupure finie `H'' ≥ T_l` :

* §1 le groupe `]H, H'']` est FINI (`group_finite`) ;
* §2 reste à consommer : `R − P_H = G_{H,H''} + Q_{H''}` (identité, `consumed_residual_split`) ;
* §3 NON-COMPENSATION dans le groupe : si `l` est bas (`β_l < 1/2`) et dans le groupe, son miroir (même hauteur,
  `β* = 1 − β_l > 1/2`) y est aussi ; aucune somme finie du groupe, avec tous ses autres membres, multiplicités et phases,
  n'est bornée par `C·x^θ` pour un `θ < 1 − β_l` (`mirror_group_not_compensated`, lecture du pôle) ;
* §4 fermeture : sous l'historique ON, une borne `C·x^θ`, `θ < 1 − β_l`, de `R − Q_{H''}` (reste des premiers moins la
  queue au-delà du groupe) contredit `β_l < 1/2` (`group_noncompensation_closes`) ;
* §5 portée : la borne DÉMONTRÉE de `R − Q_{H''}` est d'exposant `1` (`group_residual_linear`) ; `1 − β_l < 1`.

Tout est démontré (axiomes standard). La borne d'exposant `< 1 − β_l` de `R − Q_{H''}` n'est PAS démontrée.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Le groupe est fini -/

/-- Les points de hauteur absolue `≤ H''` sont en nombre fini. -/
theorem group_finite (H'' : ℝ) : {σ : ExplicitIndex | |(σ : ℂ).im| ≤ H''}.Finite := by
  refine (explicitIndex_locallyFinite (1 + H'')).subset fun σ hσ => ?_
  simp only [Set.mem_ofPred_eq] at hσ ⊢
  have hre := isNontrivialZetaZero_re_mem_Ioo σ.property
  calc ‖(σ : ℂ)‖ ≤ |(σ : ℂ).re| + |(σ : ℂ).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 + H'' := add_le_add (by rw [abs_of_pos hre.1]; exact hre.2.le) hσ

/-! ## 2. Le reste à consommer -/

/-- **Reste à consommer** après l'historique : `R − P_H = G_{H,H''} + Q_{H''}` (identité). -/
theorem consumed_residual_split (H H'' : ℝ) {x : ℝ} (hx : 1 < x) :
    smoothedRemainder x - precedingSum H x = nextFiberSum H H'' x + followingSum H'' x := by
  rw [expected_next_fiber H H'' hx]; ring

/-! ## 3. Non-compensation du miroir dans le groupe -/

/-- **Le miroir du membre bas est lu par le groupe.** Si `H < T_z ≤ H''` et `β_z < 1/2`, aucune borne `C·x^θ` avec
`θ < 1 − β_z` ne tient pour la somme du groupe `]H, H'']` : le miroir (`β* = 1 − β_z`, même hauteur) n'y est compensé
par aucun autre membre, quelles que soient leurs positions, multiplicités et phases. -/
theorem mirror_group_not_compensated {H H'' θ C : ℝ} (z : TrueZero) (hz : H < rZeroHeight z.1)
    (hz' : rZeroHeight z.1 ≤ H'') (hθ : θ < 1 - rZeroRadialPosition z.1) :
    ¬ ∀ x : ℝ, 1 < x → ‖nextFiberSum H H'' x‖ ≤ C * x ^ θ := by
  intro h
  have hT : 0 < rZeroHeight z.1 := z.2
  have hTm : rZeroHeight (mirrorMember z).1 = rZeroHeight z.1 := mirrorMember_ordinate z
  have h2 := nextFiber_growth_bounds_each h (memberIndex (mirrorMember z))
    (by change H < |rZeroHeight (mirrorMember z).1|; rw [hTm, abs_of_pos hT]; exact hz)
    (by change |rZeroHeight (mirrorMember z).1| ≤ H''; rw [hTm, abs_of_pos hT]; exact hz')
  rw [show ((memberIndex (mirrorMember z) : ExplicitIndex) : ℂ) = zeroPoint (mirrorMember z) from rfl,
    zeroPoint_re, mirrorMember_radial] at h2
  linarith

/-! ## 4. Fermeture par la non-compensation -/

/-- **Fermeture** : historique ON jusqu'à `H`, membre bas `z` de hauteur dans `]H, H'']`. Si le reste des premiers moins
la queue au-delà du groupe est borné par `C·x^θ` avec `θ < 1 − β_z`, contradiction. -/
theorem group_noncompensation_closes {H : ℝ}
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ H → rZeroRadialPosition w.1 = 1 / 2)
    (z : TrueZero) (hz : H < rZeroHeight z.1) (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (h : ∃ H'' θ C : ℝ, rZeroHeight z.1 ≤ H'' ∧ θ < 1 - rZeroRadialPosition z.1 ∧
      ∀ x : ℝ, 1 < x → ‖smoothedRemainder x - followingSum H'' x‖ ≤ C * x ^ θ) : False := by
  obtain ⟨H'', θ, C, hz', hθ, hC⟩ := h
  set θ' := max θ (1 / 2) with hθ'
  have hθ'lt : θ' < 1 - rZeroRadialPosition z.1 := max_lt hθ (by linarith)
  have hB : 0 ≤ precedingBudget H := tsum_nonneg fun _ => norm_nonneg _
  refine mirror_group_not_compensated (C := max C 0 + precedingBudget H) z hz hz' hθ'lt fun x hx => ?_
  have hx1 : 1 ≤ x := hx.le
  have hG : nextFiberSum H H'' x = (smoothedRemainder x - followingSum H'' x) - precedingSum H x := by
    rw [expected_next_fiber H H'' hx]; ring
  have e1 : x ^ θ ≤ x ^ θ' := Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)
  have e2 : x ^ (1 / 2 : ℝ) ≤ x ^ θ' := Real.rpow_le_rpow_of_exponent_le hx1 (le_max_right _ _)
  have hxθ : 0 ≤ x ^ θ := Real.rpow_nonneg (by linarith) _
  rw [hG, add_mul]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · calc ‖smoothedRemainder x - followingSum H'' x‖ ≤ C * x ^ θ := hC x hx
      _ ≤ max C 0 * x ^ θ := mul_le_mul_of_nonneg_right (le_max_left _ _) hxθ
      _ ≤ max C 0 * x ^ θ' := mul_le_mul_of_nonneg_left e1 (le_max_right _ _)
  · exact (precedingSum_le_budget_of_onLine hOn hx).trans (mul_le_mul_of_nonneg_left e2 hB)

/-! ## 5. Portée : ce qui est démontré sur le reste à consommer -/

/-- **Borne démontrée** de `R − Q_{H''}` : exposant `1`, constante `C_lin + budget(H'')` (aucune borne d'exposant `< 1`). -/
theorem group_residual_linear (H'' : ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x - followingSum H'' x‖ ≤ C * x ^ (1 : ℝ) := by
  obtain ⟨C, hC⟩ := smoothedRemainder_linear_growth
  refine ⟨C + followingBudget H'', fun x hx => ?_⟩
  rw [add_mul]
  refine (norm_sub_le _ _).trans (add_le_add (hC x hx) ?_)
  rw [Real.rpow_one]; exact followingSum_norm_le_budget_linear H'' hx

#print axioms group_finite
#print axioms consumed_residual_split
#print axioms mirror_group_not_compensated
#print axioms group_noncompensation_closes
#print axioms group_residual_linear

/-! ## 6. Lecture exacte du but affiché, et forme indépendante -/

/-- **Identité** : le reste moins la queue au-delà de `H''` est la somme FINIE des membres de hauteur `≤ H''`. Le but
« `R − Q_{H''}` sous `C·x^θ` » n'est donc pas une majoration indépendante : c'est la borne d'une somme finie de zéros qui
contient le miroir. -/
theorem remainder_sub_tail_eq_preceding (H'' : ℝ) {x : ℝ} (hx : 1 < x) :
    smoothedRemainder x - followingSum H'' x = precedingSum H'' x := by
  rw [remainder_eq_preceding_add_following H'' hx]; ring

/-- **Forme indépendante** (premiers seuls, aucun zéro) : une borne `C·x^θ` du reste lissé des premiers avec
`θ < 1 − β_z` est impossible : le miroir (`1 − β_z`) est lu par le reste entier. Sous `β_z < 1/2`, c'est la
contradiction cherchée. -/
theorem mirror_closes_of_remainder_growth (z : TrueZero)
    (h : ∃ θ C : ℝ, θ < 1 - rZeroRadialPosition z.1 ∧
      ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ θ) : False := by
  obtain ⟨θ, C, hθ, hC⟩ := h
  have hm := radial_le_of_remainder_growth hC (mirrorMember z)
  rw [mirrorMember_radial] at hm
  linarith

#print axioms remainder_sub_tail_eq_preceding
#print axioms mirror_closes_of_remainder_growth


/-! ## 6. Élaboration de la voie H5 (texte collé, 2026-10-19) : le triple `(H'', θ, C)`

La voie H5 demande, pour une première arrivée basse `l`, une hauteur `H''`, un exposant `θ < 1 − β_l` et une constante
`C` telles que `‖R − Q_{H''}‖ ≤ C·x^θ`. Élaboration compilée : (a) SOUS la hauteur d'arrivée (`H'' = T_e`, historique ON) le
triple EXISTE, à l'exposant `1/2` (part finie ON sous `budget·√x`) ; (b) AU NIVEAU ou AU-DESSUS de l'arrivée (`H'' ≥ T_l`,
ce qu'exige `group_noncompensation_closes`) le triple N'EXISTE JAMAIS sous `β_l < 1/2` : `R − Q_{H''} = P_{H''}` contient
le miroir. Ce qui sépare (a) de (b) est exactement la fibre `]T_e, H'']` qui contient `l` et `l*`
(`mirror_group_not_compensated`). La voie H5 n'est donc pas une voie de fermeture : son hypothèse est fausse dans le
contexte où elle fermerait, vraie là où elle ne ferme pas. -/

/-- (a) Le triple existe SOUS la hauteur d'arrivée : `H'' = H` (historique ON), `θ = 1/2`, `C = budget(H)`. -/
theorem h5_triple_below_arrival {H : ℝ}
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ H → rZeroRadialPosition w.1 = 1 / 2) :
    ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x - followingSum H x‖ ≤ C * x ^ (1 / 2 : ℝ) :=
  ⟨precedingBudget H, fun x hx => by
    rw [remainder_sub_tail_eq_preceding H hx]; exact precedingSum_le_budget_of_onLine hOn hx⟩

/-- (a') Sous la hauteur d'arrivée, l'exposant `1/2` est strictement sous l'exposant du miroir d'une arrivée basse :
le triple de H5 y est satisfait avec `θ = 1/2 < 1 − β_l`. Il ne ferme pas : `group_noncompensation_closes` exige
`T_l ≤ H''`. -/
theorem h5_triple_below_arrival_exponent {H : ℝ}
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ H → rZeroRadialPosition w.1 = 1 / 2)
    (z : TrueZero) (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    ∃ θ C : ℝ, θ < 1 - rZeroRadialPosition z.1 ∧
      ∀ x : ℝ, 1 < x → ‖smoothedRemainder x - followingSum H x‖ ≤ C * x ^ θ := by
  obtain ⟨C, hC⟩ := h5_triple_below_arrival hOn
  exact ⟨1 / 2, C, by linarith, hC⟩

/-- (b) Le triple n'existe JAMAIS au niveau ou au-dessus d'une arrivée basse (le groupe contient le miroir). -/
theorem h5_triple_impossible_above_arrival {H : ℝ}
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ H → rZeroRadialPosition w.1 = 1 / 2)
    (z : TrueZero) (hz : H < rZeroHeight z.1) (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    ¬ ∃ H'' θ C : ℝ, rZeroHeight z.1 ≤ H'' ∧ θ < 1 - rZeroRadialPosition z.1 ∧
      ∀ x : ℝ, 1 < x → ‖smoothedRemainder x - followingSum H'' x‖ ≤ C * x ^ θ :=
  fun h => group_noncompensation_closes hOn z hz hβ h

/-- (c) Ce qui sépare (a) de (b) : le passage de `H` à `H'' ≥ T_l` ajoute la fibre `]H, H'']`, et c'est cette fibre seule,
qui contient le miroir, qui n'admet aucune borne sous l'exposant du miroir. -/
theorem h5_gap_is_mirror_fiber {H H'' θ C : ℝ} (z : TrueZero) (hz : H < rZeroHeight z.1)
    (hz' : rZeroHeight z.1 ≤ H'') (hθ : θ < 1 - rZeroRadialPosition z.1) {x : ℝ} (hx : 1 < x) :
    (smoothedRemainder x - followingSum H'' x) - (smoothedRemainder x - followingSum H x) = nextFiberSum H H'' x ∧
    ¬ ∀ y : ℝ, 1 < y → ‖nextFiberSum H H'' y‖ ≤ C * y ^ θ :=
  ⟨by rw [expected_next_fiber H H'' hx, remainder_eq_preceding_add_following H hx]; ring,
   mirror_group_not_compensated z hz hz' hθ⟩

#print axioms h5_triple_below_arrival
#print axioms h5_triple_impossible_above_arrival
#print axioms h5_gap_is_mirror_fiber

end RHV6Fresh
