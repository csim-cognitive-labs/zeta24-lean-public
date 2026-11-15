/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RayEnergy

/-!
# RHV6Fresh — P8 : les invariants d'une succession authentique, sans cible RH-équivalente (2026-09-28)

Correction de l'auteur sur P7 (acceptée intégralement) :
1. dans le cas horizontal de P7, `hinv` ne contredit le but qu'en `q > q₀`, pas au `q` courant ;
2. `PVerticalEnergyPush` est `↔ RH` : partir de `riemannHypothesis_of_verticalEnergyPush` biaise la
   sonde vers une cible circulaire, comme P6 (égalité imposée) devenu P7 (signe imposé) ;
3. la première branche de V4 (`T_e < T_l`) n'est PAS le mode vertical (`Δβ = 0`) : elle fusionne
   A (`ΔT > 0, Δβ = 0`) et B (`ΔT > 0, Δβ ≠ 0`) ; le mode vertical pur est A, le mode horizontal pur
   est C (`ΔT = 0, Δβ > 0`), B est mixte ;
4. « exclure B est RH » n'est pas démontré ; seule l'exclusion de C l'est (`noNullPassage`).

Ce fichier ne pose AUCUNE cible. Il part d'un passage authentique `p` et calcule ce qui est
disponible :

* **S1** la trichotomie A / B / C (théorème, depuis l'ordre lexicographique) ;
* **S2** `Δβ`, `ΔT ≥ 0`, `Δφ` ; la grille du LATER est celle du EARLIER translatée par `λ_C =
  exp(Δφ/T)` en C (même hauteur) ;
* **S3** le rapport énergétique `R_E(q) = E_l(q)/E_e(q) = q^{Δβ} · ‖ρ_e‖/‖ρ_l‖`, exact, tout passage ;
* **S4** `R_E` est CONSTANT en `q` ssi `Δβ = 0` (mode A : `R_E = ‖ρ_e‖/‖ρ_l‖ < 1`) ; si `Δβ > 0`,
  `R_E(q) → +∞` (tout `M` est dépassé au-delà d'un seuil) — la signature asymptotique de
  l'auteur, valable en B comme en C, indépendamment de `ΔT` ;
* **S5** les deux raccords `Occ(l) = p_min(e)` et `p_min(l) = p_{n_e+2}`, et la cellule unique de
  chaque Tour qui contient réellement chacun de ces deux premiers ;
* **S6** le paquet complet, habité pour tout passage (consistance : aucune contradiction n'est
  disponible à ce niveau).

Ce que ce fichier NE fait PAS : imposer `E_l ≤ E_e` (P7), imposer `E_l = E_e` (P6), ou toute
autre relation entre la signature énergétique et les raccords. La question ouverte, correctement
posée par l'auteur : existe-t-il une identité de raccord, imposée par la Tour et `M` et
indépendante de `β`, que les deux signatures de `Δβ` (géométrique dans les rayons, énergétique
sur l'axe) ne peuvent satisfaire simultanément ? Rien de compilé ne la fournit ni ne l'exclut.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## S1 — la trichotomie A / B / C -/

/-- **Trichotomie d'une succession** : A vertical pur, B mixte, C horizontal pur. -/
theorem passage_trichotomy_ABC (p : TZeroPassage) :
    (rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
        rZeroRadialPosition p.zEarlierMember = rZeroRadialPosition p.zLaterMember) ∨
      (rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
        rZeroRadialPosition p.zEarlierMember ≠ rZeroRadialPosition p.zLaterMember) ∨
      (rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember ∧
        rZeroRadialPosition p.zEarlierMember < rZeroRadialPosition p.zLaterMember) := by
  rcases (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mp p.precedes with hlt | ⟨heq, hr⟩
  · by_cases hβ : rZeroRadialPosition p.zEarlierMember = rZeroRadialPosition p.zLaterMember
    · exact Or.inl ⟨hlt, hβ⟩
    · exact Or.inr (Or.inl ⟨hlt, hβ⟩)
  · exact Or.inr (Or.inr ⟨heq, hr⟩)

/-! ## S2 — les trois déplacements et la translation de grille -/

/-- `ΔT ≥ 0` sur tout passage. -/
theorem passage_deltaT_nonneg (p : TZeroPassage) :
    0 ≤ rZeroHeight p.zLaterMember - rZeroHeight p.zEarlierMember :=
  sub_nonneg.mpr (passage_height_le p)

/-- **En mode C, la grille du LATER est la grille du EARLIER translatée rigidement par
`λ_C = exp(Δφ/T)`**, pour tout rayon `k`. -/
theorem passage_grid_translation_of_sameHeight (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hSame : rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember) (k : ℤ) :
    contactMinusAt ⟨p.zLaterMember, hL⟩ k =
      contactMinusAt ⟨p.zEarlierMember, hE⟩ k *
        Real.exp (((towerMotionOf ⟨p.zLaterMember, hL⟩).phase -
          (towerMotionOf ⟨p.zEarlierMember, hE⟩).phase) / rZeroHeight p.zEarlierMember) :=
  sameHeight_grid_rigid_translation ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hSame k

/-! ## S3 — le rapport énergétique exact -/

/-- Le rapport énergétique `R_E(q) = ‖zeroTerm l q‖ / ‖zeroTerm e q‖`. -/
noncomputable def energyRatio (e l : TrueZero) (q : ℝ) : ℝ :=
  ‖zeroTerm l q‖ / ‖zeroTerm e q‖

/-- **`R_E(q) = q^{Δβ} · ‖ρ_e‖ / ‖ρ_l‖`**, exact, pour tout couple et tout `q > 0`. -/
theorem energyRatio_eq (e l : TrueZero) {q : ℝ} (hq : 0 < q) :
    energyRatio e l q =
      q ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * (‖zeroPoint e‖ / ‖zeroPoint l‖) := by
  unfold energyRatio
  have hNe := zeroPoint_norm_pos e
  have hNl := zeroPoint_norm_pos l
  have hpe : 0 < q ^ rZeroRadialPosition e.1 := Real.rpow_pos_of_pos hq _
  rw [zeroTerm_norm hq, zeroTerm_norm hq, Real.rpow_sub hq]
  field_simp

/-! ## S4 — constance en `q` ssi `Δβ = 0` ; divergence si `Δβ > 0` -/

/-- **Mode A** (`Δβ = 0`) : le rapport énergétique est constant en `q`, égal à `‖ρ_e‖/‖ρ_l‖`. -/
theorem energyRatio_const_of_deltaBeta_zero (e l : TrueZero)
    (hβ : rZeroRadialPosition e.1 = rZeroRadialPosition l.1) {q : ℝ} (hq : 0 < q) :
    energyRatio e l q = ‖zeroPoint e‖ / ‖zeroPoint l‖ := by
  rw [energyRatio_eq e l hq, hβ, sub_self, Real.rpow_zero, one_mul]

/-- **Mode A avec `ΔT > 0`** : le rapport constant est `< 1` (l'énergie décroît, V1). -/
theorem energyRatio_lt_one_of_vertical (e l : TrueZero)
    (hβ : rZeroRadialPosition e.1 = rZeroRadialPosition l.1)
    (hT : rZeroHeight e.1 < rZeroHeight l.1) {q : ℝ} (hq : 0 < q) :
    energyRatio e l q < 1 := by
  rw [energyRatio_const_of_deltaBeta_zero e l hβ hq,
    div_lt_one (zeroPoint_norm_pos l)]
  exact zeroPoint_norm_lt_of_height_lt e l hβ hT

/-- **Le rapport énergétique est constant en `q` ssi `Δβ = 0`** (deux points `q = 2, 4`
suffisent). -/
theorem energyRatio_const_iff (e l : TrueZero) :
    (∀ q₁ q₂ : ℝ, 0 < q₁ → 0 < q₂ → energyRatio e l q₁ = energyRatio e l q₂) ↔
      rZeroRadialPosition e.1 = rZeroRadialPosition l.1 := by
  constructor
  · intro h
    have h24 := h 2 4 (by norm_num) (by norm_num)
    rw [energyRatio_eq e l (by norm_num), energyRatio_eq e l (by norm_num)] at h24
    have hN : 0 < ‖zeroPoint e‖ / ‖zeroPoint l‖ :=
      div_pos (zeroPoint_norm_pos e) (zeroPoint_norm_pos l)
    have h24' : (2 : ℝ) ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) =
        (4 : ℝ) ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) :=
      mul_right_cancel₀ hN.ne' h24
    have h4 : (4 : ℝ) ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) =
        (2 : ℝ) ^ (2 * (rZeroRadialPosition l.1 - rZeroRadialPosition e.1)) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num,
        ← Real.rpow_mul (by norm_num)]
    rw [h4] at h24'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : rZeroRadialPosition l.1 - rZeroRadialPosition e.1 <
          2 * (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) := by linarith
      exact absurd h24' (ne_of_lt ((Real.rpow_lt_rpow_left_iff (by norm_num)).mpr this))
    · have : 2 * (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) <
          rZeroRadialPosition l.1 - rZeroRadialPosition e.1 := by linarith
      exact absurd h24' (ne_of_gt ((Real.rpow_lt_rpow_left_iff (by norm_num)).mpr this))
  · intro hβ q₁ q₂ h1 h2
    rw [energyRatio_const_of_deltaBeta_zero e l hβ h1, energyRatio_const_of_deltaBeta_zero e l hβ h2]

/-- **Signature asymptotique** (`Δβ > 0`, quel que soit `ΔT`) : `R_E(q)` dépasse tout `M` au-delà
d'un seuil. -/
theorem energyRatio_unbounded_of_deltaBeta_pos (e l : TrueZero)
    (hβ : rZeroRadialPosition e.1 < rZeroRadialPosition l.1) (M : ℝ) :
    ∃ q₀ : ℝ, 1 ≤ q₀ ∧ ∀ q : ℝ, q₀ < q → M < energyRatio e l q := by
  set δ := rZeroRadialPosition l.1 - rZeroRadialPosition e.1 with hδdef
  have hδ : 0 < δ := sub_pos.mpr hβ
  set c := ‖zeroPoint e‖ / ‖zeroPoint l‖ with hcdef
  have hc : 0 < c := div_pos (zeroPoint_norm_pos e) (zeroPoint_norm_pos l)
  -- seuil : q₀ = max 1 ((max M 1 / c)^{1/δ})
  set M' := max M 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨max 1 ((M' / c) ^ (1 / δ)), le_max_left _ _, ?_⟩
  intro q hq
  have hq0 : 0 < q := lt_trans one_pos (lt_of_le_of_lt (le_max_left _ _) hq)
  have hqr : (M' / c) ^ (1 / δ) < q := lt_of_le_of_lt (le_max_right _ _) hq
  have hr : 0 < M' / c := div_pos hM'pos hc
  have hqδ : M' / c < q ^ δ := by
    have h1 : ((M' / c) ^ (1 / δ)) ^ δ < q ^ δ :=
      Real.rpow_lt_rpow (Real.rpow_nonneg hr.le _) hqr hδ
    rwa [← Real.rpow_mul hr.le, one_div_mul_cancel hδ.ne', Real.rpow_one] at h1
  rw [energyRatio_eq e l hq0]
  have : M' < q ^ δ * c := by
    have := (div_lt_iff₀ hc).mp hqδ
    linarith
  exact lt_of_le_of_lt (le_max_left M 1) this

/-! ## S5 — les deux raccords et les cellules qui les contiennent -/

/-- **Les deux raccords** : `Occ(l) = p_min(e) = p_{n_e+1}` et `p_min(l) = p_{n_e+2}`. -/
theorem passage_raccords (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
      occurrence ⟨p.zLaterMember, hL⟩ = fnPrimeAtRank (nZeroSourceIndex p.zEarlierMember + 1) ∧
      expectedMinimumPrime ⟨p.zLaterMember, hL⟩ =
        fnPrimeAtRank (nZeroSourceIndex p.zEarlierMember + 2) := by
  obtain ⟨hSucc, hOcc, _⟩ := passage_event_increment p hE hL
  refine ⟨hOcc, ?_, ?_⟩
  · rw [occurrence_eq_primeAtRank (⟨p.zLaterMember, hL⟩ : TrueZero)]
    exact congrArg fnPrimeAtRank hSucc
  · show fnPrimeAtRank (nZeroSourceIndex p.zLaterMember + 1) = _
    rw [hSucc]

/-! ## S6 — le paquet complet des invariants, habité pour tout passage -/

/-- **P8** : tout ce qui est calculable sur une succession authentique, sans cible. Le fait que
ce terme compile pour TOUT passage prouve que ces invariants sont consistants entre eux — aucune
contradiction n'est disponible à ce niveau, ON ou OFF. -/
theorem succession_invariants (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    -- trichotomie
    ((rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
        rZeroRadialPosition p.zEarlierMember = rZeroRadialPosition p.zLaterMember) ∨
      (rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
        rZeroRadialPosition p.zEarlierMember ≠ rZeroRadialPosition p.zLaterMember) ∨
      (rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember ∧
        rZeroRadialPosition p.zEarlierMember < rZeroRadialPosition p.zLaterMember)) ∧
    -- rapport énergétique exact
    (∀ q : ℝ, 0 < q → energyRatio ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ q =
      q ^ (rZeroRadialPosition p.zLaterMember - rZeroRadialPosition p.zEarlierMember) *
        (‖zeroPoint ⟨p.zEarlierMember, hE⟩‖ / ‖zeroPoint ⟨p.zLaterMember, hL⟩‖)) ∧
    -- constance ssi Δβ = 0
    ((∀ q₁ q₂ : ℝ, 0 < q₁ → 0 < q₂ →
        energyRatio ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ q₁ =
          energyRatio ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ q₂) ↔
      rZeroRadialPosition p.zEarlierMember = rZeroRadialPosition p.zLaterMember) ∧
    -- raccords
    (occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
      expectedMinimumPrime ⟨p.zLaterMember, hL⟩ =
        fnPrimeAtRank (nZeroSourceIndex p.zEarlierMember + 2)) ∧
    -- cellules contenant les deux raccords, sur les deux Tours
    (contactMinusAt ⟨p.zLaterMember, hL⟩
        (pivotCoordinate ⟨p.zLaterMember, hL⟩ (occurrence ⟨p.zLaterMember, hL⟩ : ℝ)) <
        (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) ∧
      (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) ≤ contactPlusAt ⟨p.zLaterMember, hL⟩
        (pivotCoordinate ⟨p.zLaterMember, hL⟩ (occurrence ⟨p.zLaterMember, hL⟩ : ℝ))) ∧
    (contactMinusAt ⟨p.zEarlierMember, hE⟩
        (pivotCoordinate ⟨p.zEarlierMember, hE⟩ (occurrence ⟨p.zLaterMember, hL⟩ : ℝ)) <
        (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) ∧
      (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) ≤ contactPlusAt ⟨p.zEarlierMember, hE⟩
        (pivotCoordinate ⟨p.zEarlierMember, hE⟩ (occurrence ⟨p.zLaterMember, hL⟩ : ℝ))) ∧
    -- énergie signée sur les rayons de chaque Tour
    (∀ k : ℤ, (zeroTerm ⟨p.zLaterMember, hL⟩ (contactMinusAt ⟨p.zLaterMember, hL⟩ k)).re =
      (-1 : ℝ) ^ k * (contactMinusAt ⟨p.zLaterMember, hL⟩ k) ^ rZeroRadialPosition p.zLaterMember /
        ‖zeroPoint ⟨p.zLaterMember, hL⟩‖) ∧
    -- excès
    0 ≤ interTowerExcess p hE hL := by
  obtain ⟨hOcc, _, hpmin⟩ := passage_raccords p hE hL
  refine ⟨passage_trichotomy_ABC p, fun q hq => energyRatio_eq _ _ hq, energyRatio_const_iff _ _,
    ⟨hOcc, hpmin⟩, ?_, ?_, fun k => ray_energy _ k, interTowerExcess_nonneg p hE hL⟩
  · exact prime_raccord_has_unique_tower_cell _ (by exact_mod_cast occurrence_pos _)
  · exact prime_raccord_has_unique_tower_cell _ (by exact_mod_cast occurrence_pos _)

#print axioms passage_trichotomy_ABC
#print axioms energyRatio_eq
#print axioms energyRatio_const_iff
#print axioms energyRatio_unbounded_of_deltaBeta_pos
#print axioms passage_raccords
#print axioms succession_invariants

end RHV6Fresh
