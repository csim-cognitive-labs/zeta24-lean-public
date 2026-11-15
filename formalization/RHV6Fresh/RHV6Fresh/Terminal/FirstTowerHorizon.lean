/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TowerHierarchy

/-!
# RHV6Fresh — ce que les seuls paramètres fixent : l'horizon de la première Tour (auteur, 2026-10-04)

Énoncé de l'auteur : « l'énergie de la première Tour ne peut pas être surpassée par les Tours suivantes
simplement du fait des valeurs de certains paramètres ; étudier la monotonie des énergies qui emprisonnent
les zéros et en font un tout cohérent ».

Les paramètres d'une Tour sont sa position radiale `β`, sa hauteur `T`, donc son support `‖ρ‖`. Aucun
autre objet n'entre dans ce fichier.

* **§1 La comparaison de deux Tours est une inégalité de paramètres** : en `x > 0`, la Tour de `w` ne
  dépasse pas celle de `z` ⟺ `x^{β_w − β_z}·‖ρ_z‖ ≤ ‖ρ_w‖` (`tower_le_iff_parameters`,
  `tower_surpasses_iff_parameters`).
* **§2 Prison par les paramètres** : `β_w ≤ β_z` et `‖ρ_z‖ ≤ ‖ρ_w‖` ⟹ `w` est dans le champ de `z` pour
  toujours (`inside_field_of_parameters`) ; sur la ligne, l'ordre des énergies est l'ordre des hauteurs, en
  tout point de l'axe des premiers (`onLine_energy_order_iff_height`).
* **§3 L'horizon garanti (borne uniforme, pire cas)** : la vraie position radiale de `w` est remplacée par la
  seule borne `β_w < 1` ; d'où : tant que `√x·‖ρ₁‖ ≤ ‖ρ_w‖`, a fortiori tant que `√x·‖ρ₁‖ ≤ T_w`, la Tour de `w`
  ne dépasse pas le champ du premier zéro en ligne (`tower_inside_below_horizon`, `tower_inside_of_height`).
  `(T_w/‖ρ₁‖)²` est une borne volontairement pessimiste, PAS l'horizon de la Tour : elle ignore sa vraie `β_w`.
* **§4 Un prisonnier à chaque hauteur** : au-dessus de la hauteur `‖ρ₁‖`, de tout membre et de son miroir,
  l'un au moins est dans le champ pour toujours (`mirror_pair_has_prisoner`) : c'est le membre bas
  (`lower_member_prisoner`).
* **§5 Le membre haut, horizon exact** : pour `β_w = 1/2 + δ`, rapport à la première Tour `x^δ·‖ρ₁‖/‖ρ_w‖`
  (`upper_member_ratio`) ; évasion ⟺ `x^δ > ‖ρ_w‖/‖ρ₁‖` (`upper_member_escapes_iff`) ; horizon exact
  `(‖ρ_w‖/‖ρ₁‖)^{1/δ}` (`upper_member_exact_horizon`), au moins l'horizon garanti (`uniform_horizon_le_exact`) ;
  un exposant `1/2 + δ` interdit toute borne globale du reste d'exposant `1/2 + η`, `η < δ`
  (`upper_member_gain_must_be_financed`, application directe de `escape_must_be_financed` : lecture asymptotique
  globale du reste, qui n'utilise ni raccord, ni Tour précédente, ni énergie locale).

Portée : ce fichier compare seulement les modules individuels des Tours ; il n'utilise ni les poids de von
Mangoldt, ni les phases, ni les premiers du raccord, ni le reste exact. Il établit jusqu'où la géométrie seule
va : le membre bas d'un miroir est emprisonné automatiquement ; toute la difficulté arithmétique est dans la
croissance `x^δ` du membre haut. Une Tour avec `T_w > T₁` et `β_w > 1/2` sort (§1, §5) : le verrou révélé ici
n'est pas « la Tour suivante ne peut pas prendre la hauteur de la précédente », c'est le membre haut du miroir.
Ce fichier compare chaque Tour à la première, jusqu'à l'infini : ce n'est pas l'objet local. `financing_ledger`
ne lit que la positivité et Chebyshev, sans phase ni raccord. La comparaison de deux Tours successives au premier
du raccord, coût de sortie contre disponible, est dans `Terminal/LocalRaccordCaptivity.lean`.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse `def P… : Prop`.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. La comparaison de deux Tours est une inégalité de paramètres -/

/-- **Comparaison de deux Tours en un point de l'axe des premiers** : inégalité entre positions radiales
et supports, rien d'autre. -/
theorem tower_le_iff_parameters (z w : TrueZero) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm w x‖ ≤ ‖zeroTerm z x‖ ↔
      x ^ (rZeroRadialPosition w.1 - rZeroRadialPosition z.1) * ‖zeroPoint z‖ ≤ ‖zeroPoint w‖ := by
  rw [norm_zeroTerm_eq w hx, norm_zeroTerm_eq z hx, Real.rpow_sub hx,
    div_le_div_iff₀ (norm_zeroPoint_pos w) (norm_zeroPoint_pos z)]
  have h3 := Real.rpow_pos_of_pos hx (rZeroRadialPosition z.1)
  rw [div_mul_eq_mul_div, div_le_iff₀ h3]
  constructor <;> intro h <;> linarith

/-- **Dépassement** : la Tour de `w` dépasse celle de `z` en `x` exactement quand l'inégalité de
paramètres est renversée. -/
theorem tower_surpasses_iff_parameters (z w : TrueZero) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm z x‖ < ‖zeroTerm w x‖ ↔
      ‖zeroPoint w‖ < x ^ (rZeroRadialPosition w.1 - rZeroRadialPosition z.1) * ‖zeroPoint z‖ := by
  rw [← not_le, ← not_le, tower_le_iff_parameters z w hx]

/-! ## 2. Prison par les paramètres -/

/-- **Prison par les seuls paramètres** : position radiale non supérieure et support non inférieur ⟹
dans le champ pour toujours. -/
theorem inside_field_of_parameters {z₁ w : TrueZero}
    (hβ : rZeroRadialPosition w.1 ≤ rZeroRadialPosition z₁.1)
    (hρ : ‖zeroPoint z₁‖ ≤ ‖zeroPoint w‖) : InsideField z₁ w := by
  intro x hx
  have hx0 : 0 < x := by linarith
  unfold firstField
  rw [tower_le_iff_parameters z₁ w hx0]
  have h1 : x ^ (rZeroRadialPosition w.1 - rZeroRadialPosition z₁.1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  nlinarith [norm_zeroPoint_pos z₁]

/-- **Sur la ligne, l'ordre des énergies est l'ordre des hauteurs**, en tout point de l'axe des premiers. -/
theorem onLine_energy_order_iff_height {z w : TrueZero} (hz : rZeroRadialPosition z.1 = 1 / 2)
    (hw : rZeroRadialPosition w.1 = 1 / 2) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm w x‖ < ‖zeroTerm z x‖ ↔ rZeroHeight z.1 < rZeroHeight w.1 := by
  have hβ : rZeroRadialPosition z.1 = rZeroRadialPosition w.1 := hz.trans hw.symm
  refine ⟨fun h => ?_, fun h => amplitude_lt_of_height_lt z w hβ h hx⟩
  by_contra hn
  rcases (not_lt.mp hn).lt_or_eq with h' | h'
  · exact lt_asymm h (amplitude_lt_of_height_lt w z hβ.symm h' hx)
  · have hn' := zeroPoint_norm_eq_of_eq w z hβ.symm h'
    rw [norm_zeroTerm_eq w hx, norm_zeroTerm_eq z hx, hβ, hn'] at h
    exact lt_irrefl _ h

/-! ## 3. L'horizon -/

/-- Le support d'un membre est au moins sa hauteur. -/
theorem height_le_zeroPoint_norm (w : TrueZero) : rZeroHeight w.1 ≤ ‖zeroPoint w‖ := by
  have h := zeroPoint_norm_sq w
  have hT : 0 < rZeroHeight w.1 := w.2
  refine not_lt.mp fun hlt => ?_
  nlinarith [norm_nonneg (zeroPoint w), sq_nonneg (rZeroRadialPosition w.1),
    mul_pos (sub_pos.mpr hlt) (add_pos_of_pos_of_nonneg hT (norm_nonneg (zeroPoint w)))]

/-- **Horizon garanti, borne uniforme** : la position radiale de `w` est remplacée par le pire cas `β_w < 1` ;
tant que `√x·‖ρ₁‖ ≤ ‖ρ_w‖`, la Tour de `w` ne dépasse pas le champ du zéro en ligne `z₁`. Ce n'est pas
l'horizon exact de `w` (voir `upper_member_exact_horizon`). -/
theorem tower_inside_below_horizon {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    {x : ℝ} (hx : 1 ≤ x) (hH : Real.sqrt x * ‖zeroPoint z₁‖ ≤ ‖zeroPoint w‖) :
    ‖zeroTerm w x‖ ≤ firstField z₁ x := by
  have hx0 : 0 < x := by linarith
  unfold firstField
  rw [tower_le_iff_parameters z₁ w hx0, h₁]
  have hb := thm_zeroRadialPosition_lt_one w.1
  have h1 : x ^ (rZeroRadialPosition w.1 - 1 / 2) ≤ x ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  rw [← Real.sqrt_eq_rpow] at h1
  nlinarith [norm_zeroPoint_pos z₁]

/-- **L'horizon garanti lu sur la hauteur seule** (plus faible encore : `T_w ≤ ‖ρ_w‖`) ; il croît comme le carré
de la hauteur. -/
theorem tower_inside_of_height {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    {x : ℝ} (hx : 1 ≤ x) (hH : Real.sqrt x * ‖zeroPoint z₁‖ ≤ rZeroHeight w.1) :
    ‖zeroTerm w x‖ ≤ firstField z₁ x :=
  tower_inside_below_horizon h₁ hx (hH.trans (height_le_zeroPoint_norm w))

/-! ## 4. Un prisonnier à chaque hauteur -/

/-- **De tout membre et de son miroir, l'un au moins est dans le champ pour toujours**, dès que la
hauteur atteint le support du zéro en ligne `z₁`. -/
theorem mirror_pair_has_prisoner {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hH : ‖zeroPoint z₁‖ ≤ rZeroHeight w.1) :
    InsideField z₁ w ∨ InsideField z₁ (mirrorMember w) := by
  rcases le_total (rZeroRadialPosition w.1) (1 / 2) with h | h
  · exact Or.inl (inside_field_of_parameters (by rw [h₁]; exact h)
      (hH.trans (height_le_zeroPoint_norm w)))
  · refine Or.inr (inside_field_of_parameters (by rw [h₁, mirrorMember_radial]; linarith) ?_)
    have hm := height_le_zeroPoint_norm (mirrorMember w)
    rw [mirrorMember_ordinate] at hm
    exact hH.trans hm

/-- **Le membre bas est prisonnier pour toujours**, par la géométrie seule. -/
theorem lower_member_prisoner {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hβ : rZeroRadialPosition w.1 ≤ 1 / 2) (hρ : ‖zeroPoint z₁‖ ≤ ‖zeroPoint w‖) : InsideField z₁ w :=
  inside_field_of_parameters (by rw [h₁]; exact hβ) hρ

/-! ## 5. Le membre haut : horizon exact -/

/-- **Rapport exact du membre haut au champ** : `x^δ·‖ρ₁‖/‖ρ_w‖`. -/
theorem upper_member_ratio {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2) {δ : ℝ}
    (hw : rZeroRadialPosition w.1 = 1 / 2 + δ) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm w x‖ / firstField z₁ x = x ^ δ * ‖zeroPoint z₁‖ / ‖zeroPoint w‖ := by
  unfold firstField
  rw [norm_zeroTerm_eq w hx, norm_zeroTerm_eq z₁ hx, hw, h₁, Real.rpow_add hx]
  have h1 := norm_zeroPoint_pos z₁
  have h2 := norm_zeroPoint_pos w
  have h3 := Real.rpow_pos_of_pos hx (1 / 2 : ℝ)
  field_simp

/-- **Évasion du membre haut** : exactement quand `x^δ > ‖ρ_w‖/‖ρ₁‖`. -/
theorem upper_member_escapes_iff {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2) {δ : ℝ}
    (hw : rZeroRadialPosition w.1 = 1 / 2 + δ) {x : ℝ} (hx : 0 < x) :
    firstField z₁ x < ‖zeroTerm w x‖ ↔ ‖zeroPoint w‖ / ‖zeroPoint z₁‖ < x ^ δ := by
  unfold firstField
  rw [tower_surpasses_iff_parameters z₁ w hx, hw, h₁, div_lt_iff₀ (norm_zeroPoint_pos z₁)]
  ring_nf

/-- **Horizon exact du membre haut** : dans le champ en `x` ⟺ `x ≤ (‖ρ_w‖/‖ρ₁‖)^{1/δ}`. -/
theorem upper_member_exact_horizon {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2) {δ : ℝ}
    (hδ : 0 < δ) (hw : rZeroRadialPosition w.1 = 1 / 2 + δ) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm w x‖ ≤ firstField z₁ x ↔ x ≤ (‖zeroPoint w‖ / ‖zeroPoint z₁‖) ^ (1 / δ) := by
  have hR : 0 ≤ ‖zeroPoint w‖ / ‖zeroPoint z₁‖ :=
    div_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [← not_lt, upper_member_escapes_iff h₁ hw hx, not_lt,
    ← Real.rpow_le_rpow_iff hx.le (Real.rpow_nonneg hR _) hδ, ← Real.rpow_mul hR,
    one_div_mul_cancel hδ.ne', Real.rpow_one]

/-- **L'horizon garanti est sous l'horizon exact** : `(‖ρ_w‖/‖ρ₁‖)² ≤ (‖ρ_w‖/‖ρ₁‖)^{1/δ}`. -/
theorem uniform_horizon_le_exact {z₁ w : TrueZero} {δ : ℝ} (hδ : 0 < δ)
    (hw : rZeroRadialPosition w.1 = 1 / 2 + δ) (hρ : ‖zeroPoint z₁‖ ≤ ‖zeroPoint w‖) :
    (‖zeroPoint w‖ / ‖zeroPoint z₁‖) ^ (2 : ℝ) ≤ (‖zeroPoint w‖ / ‖zeroPoint z₁‖) ^ (1 / δ) := by
  have hb := thm_zeroRadialPosition_lt_one w.1
  have h1 : 1 ≤ ‖zeroPoint w‖ / ‖zeroPoint z₁‖ := (one_le_div (norm_zeroPoint_pos z₁)).mpr hρ
  refine Real.rpow_le_rpow_of_exponent_le h1 ?_
  rw [le_div_iff₀ hδ]
  linarith

/-- **Lecture asymptotique globale, pas un budget au raccord** : un membre d'exposant `1/2 + δ` interdit toute
borne globale du reste d'exposant inférieur. L'énoncé ne compare pas l'énergie disponible à un raccord et le coût
de sortie ; il n'utilise ni raccord ni Tour précédente. Le reste dépasse tout `C·x^{1/2 + η}`,
`η < δ`. -/
theorem upper_member_gain_must_be_financed {w : TrueZero} {δ : ℝ}
    (hw : rZeroRadialPosition w.1 = 1 / 2 + δ) {η : ℝ} (hη : η < δ) (C : ℝ) :
    ∃ x : ℝ, 1 < x ∧ C * x ^ (1 / 2 + η) < ‖smoothedRemainder x‖ :=
  escape_must_be_financed w (by rw [hw]; linarith) C

#print axioms tower_le_iff_parameters
#print axioms tower_surpasses_iff_parameters
#print axioms inside_field_of_parameters
#print axioms onLine_energy_order_iff_height
#print axioms height_le_zeroPoint_norm
#print axioms tower_inside_below_horizon
#print axioms tower_inside_of_height
#print axioms mirror_pair_has_prisoner
#print axioms lower_member_prisoner
#print axioms upper_member_ratio
#print axioms upper_member_escapes_iff
#print axioms upper_member_exact_horizon
#print axioms uniform_horizon_le_exact
#print axioms upper_member_gain_must_be_financed

end RHV6Fresh
