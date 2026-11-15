/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MirrorFrequency
import RHV6Fresh.Terminal.ReadingArithmetic

/-!
# RHV6Fresh — translation de phase (β) contre progression de Tour, à `T` fixé

Plan TDD (auteur, 2026-09-28) : `experiments/PLAN_TDD_TRANSLATION_PROGRESSION_20260928.md`, suite
directe de `Terminal/MirrorFrequency.lean` (commit `ebb7dca2`).

## 0. Résultat d'audit qui gouverne ce fichier

E111 (`experiments/e111_translation_vs_progression_published_output.md`) : sur les 300 zéros ON
réels d'Odlyzko, l'événement membre `Occ(z) → p_min(z)` tombe dans le MÊME anneau de la Tour propre
du zéro (`Prog = 0`) dans **88/300** cas. La prémisse (B) de l'auteur — « un événement grammatical
est une progression de Tour (≥ 1 anneau), jamais une translation » — exclurait donc des zéros SUR la
ligne : elle est RÉFUTÉE comme prémisse. Ce fichier ne la pose pas ; il compile les objets qui
permettent de le dire (translation, progression, décomposition du pivot) et la signature (D) de
l'auteur.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune hypothèse non déchargée.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. La translation miroir, valeur exacte et borne fine -/

/-- **La translation de phase miroir a une valeur exacte** : `φ_z − φ_{z*} =
arctan( T(1−2β) / (β(1−β) + T²) )`. Chaîne : `towerMotion_phase` sur `z` et son miroir
(`mirrorMember_phase`), `arctan a − arctan b = arctan a + arctan(−b) = arctan((a−b)/(1+ab))`
(`Real.arctan_neg`, `Real.arctan_add`), puis mise au même dénominateur de l'argument. -/
theorem mirror_phase_gap_eq_arctan (z : TrueZero) :
    (towerMotionOf z).phase - (towerMotionOf (mirrorMember z)).phase =
      Real.arctan (rZeroHeight z.1 * (1 - 2 * rZeroRadialPosition z.1) /
        (rZeroRadialPosition z.1 * (1 - rZeroRadialPosition z.1) + rZeroHeight z.1 ^ 2)) := by
  have hT : (0 : ℝ) < rZeroHeight z.1 := z.2
  have hβ0 : (0 : ℝ) < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hβ1 : (0 : ℝ) < 1 - rZeroRadialPosition z.1 := by
    have := mirrorMember_radial z
    have hβ0' : (0 : ℝ) < rZeroRadialPosition (mirrorMember z).1 :=
      thm_zeroRadialPosition_positive (mirrorMember z).1
    rw [this] at hβ0'
    linarith
  rw [towerMotion_phase, mirrorMember_phase]
  set β : ℝ := rZeroRadialPosition z.1 with hβdef
  set T : ℝ := rZeroHeight z.1 with hTdef
  have hxy : (T / β) * (-(T / (1 - β))) < 1 := by
    have hneg : (T / β) * (-(T / (1 - β))) < 0 := by
      have h1 : 0 < T / β := div_pos hT hβ0
      have h2 : 0 < T / (1 - β) := div_pos hT hβ1
      nlinarith
    linarith
  have hstep : Real.arctan (T / β) - Real.arctan (T / (1 - β)) =
      Real.arctan (T / β) + Real.arctan (-(T / (1 - β))) := by
    rw [Real.arctan_neg]; ring
  rw [hstep, Real.arctan_add hxy]
  congr 1
  have hβne : β ≠ 0 := hβ0.ne'
  have hβ1ne : (1 - β) ≠ 0 := hβ1.ne'
  have hden : β * (1 - β) + T ^ 2 ≠ 0 := by positivity
  field_simp [hβne, hβ1ne, hden]
  ring

/-- **La borne fine de la translation miroir**, sous `β < 1/2` : la translation de phase est
strictement positive et strictement sous `(1 − 2β)/T`. Positivité : réexposition de
`mirror_phase_lt`. Majoration : `y := arctan X` avec `X` l'argument de
`mirror_phase_gap_eq_arctan` ; `y < tan y = X` (`Real.lt_tan`, `Real.tan_arctan`) ; puis
`X < (1 − 2β)/T` car `β(1 − β) > 0`. -/
theorem mirror_phase_gap_lt {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    0 < (towerMotionOf z).phase - (towerMotionOf (mirrorMember z)).phase ∧
    (towerMotionOf z).phase - (towerMotionOf (mirrorMember z)).phase <
      (1 - 2 * rZeroRadialPosition z.1) / rZeroHeight z.1 := by
  have hT : (0 : ℝ) < rZeroHeight z.1 := z.2
  have hβ0 : (0 : ℝ) < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hβ1 : (0 : ℝ) < 1 - rZeroRadialPosition z.1 := by linarith
  refine ⟨sub_pos.mpr (mirror_phase_lt hβ), ?_⟩
  rw [mirror_phase_gap_eq_arctan]
  set β : ℝ := rZeroRadialPosition z.1 with hβdef
  set T : ℝ := rZeroHeight z.1 with hTdef
  set X : ℝ := T * (1 - 2 * β) / (β * (1 - β) + T ^ 2) with hXdef
  have hden : (0 : ℝ) < β * (1 - β) + T ^ 2 := by positivity
  have hX0 : 0 < X := by
    rw [hXdef]
    apply div_pos
    · nlinarith
    · exact hden
  have hy1 : (0 : ℝ) < Real.arctan X := Real.arctan_pos.mpr hX0
  have hy2 : Real.arctan X < Real.pi / 2 := Real.arctan_lt_pi_div_two X
  have hlt : Real.arctan X < Real.tan (Real.arctan X) := Real.lt_tan hy1 hy2
  rw [Real.tan_arctan] at hlt
  have hXbound : X < (1 - 2 * β) / T := by
    rw [hXdef, div_lt_div_iff₀ hden hT]
    have hββ : 0 < β * (1 - β) := by positivity
    nlinarith
  linarith

/-- **La translation miroir sous `1/(πT)` anneau** : l'écart de position dans la Tour entre le
membre miroir et `z`, à toute référence `q`, est strictement compris entre `0` et
`(1 − 2β)/(πT)`. Ceci remplace, en beaucoup plus fin, `towerPosition_shift_abs_lt_half`
(compilé, borne `1/2` sans `β`) : la translation n'est pas seulement sous un demi-anneau, elle est
sous `1/(πT)` anneau. E085 §A et E111 §A la mesurent. -/
theorem mirror_translation_lt {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) (q : ℝ) :
    0 < towerPosition (mirrorMember z) q - towerPosition z q ∧
    towerPosition (mirrorMember z) q - towerPosition z q <
      (1 - 2 * rZeroRadialPosition z.1) / (Real.pi * rZeroHeight z.1) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hgap := mirror_phase_gap_lt hβ
  rw [towerPosition_mirror_sub]
  refine ⟨div_pos hgap.1 hπ, ?_⟩
  have hstep := div_lt_div_of_pos_right hgap.2 hπ
  rwa [div_div, mul_comm (rZeroHeight z.1) Real.pi] at hstep

/-- **Corollaire** : la même translation est, plus grossièrement, sous `1/(πT)` anneau (car
`1 − 2β < 1`). -/
theorem mirror_translation_lt_inv_pi_height {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2) (q : ℝ) :
    towerPosition (mirrorMember z) q - towerPosition z q < 1 / (Real.pi * rZeroHeight z.1) := by
  have hβ0 : (0 : ℝ) < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hT : (0 : ℝ) < rZeroHeight z.1 := z.2
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h := (mirror_translation_lt hβ q).2
  have hlt1 : (1 - 2 * rZeroRadialPosition z.1) < 1 := by linarith
  have hpos : (0 : ℝ) < Real.pi * rZeroHeight z.1 := by positivity
  calc towerPosition (mirrorMember z) q - towerPosition z q
      < (1 - 2 * rZeroRadialPosition z.1) / (Real.pi * rZeroHeight z.1) := h
    _ < 1 / (Real.pi * rZeroHeight z.1) := by
        apply div_lt_div_of_pos_right hlt1 hpos

/-! ## 2. La progression, entier compilé -/

/-- Nombre de frontières d'anneau franchies, sur la grille propre de `w`, par l'arête première
`Occ(w) → p_min(w)`. -/
noncomputable def progression (w : TrueZero) : ℤ :=
  pivotCoordinate w (expectedMinimumPrime w : ℝ) - pivotCoordinate w (occurrence w : ℝ)

/-- La règle du pivot est monotone en la référence : deux réels positifs ordonnés donnent des
coordonnées ordonnées. -/
theorem pivotCoordinate_mono (w : TrueZero) {q₁ q₂ : ℝ} (h₁ : 0 < q₁) (h₁₂ : q₁ ≤ q₂) :
    pivotCoordinate w q₁ ≤ pivotCoordinate w q₂ := by
  unfold pivotCoordinate towerPosition
  have hlog : Real.log q₁ ≤ Real.log q₂ := Real.log_le_log h₁ h₁₂
  have hT : (0 : ℝ) < rZeroHeight w.1 := w.2
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hle : (rZeroHeight w.1 * Real.log q₁ - (towerMotionOf w).phase) / Real.pi ≤
      (rZeroHeight w.1 * Real.log q₂ - (towerMotionOf w).phase) / Real.pi := by
    apply div_le_div_of_nonneg_right _ hπ.le
    nlinarith
  have hceil := Int.ceil_mono hle
  omega

/-- **La progression est toujours non négative** : `Occ(w) < p_min(w)` (théorème,
`occurrence_lt_expectedMinimumPrime`) donne, par monotonie de la règle du pivot,
`pivotCoordinate w Occ(w) ≤ pivotCoordinate w p_min(w)`. -/
theorem progression_nonneg (w : TrueZero) : 0 ≤ progression w := by
  unfold progression
  have hocc : (0 : ℝ) < (occurrence w : ℝ) := by exact_mod_cast occurrence_pos w
  have hle : (occurrence w : ℝ) ≤ (expectedMinimumPrime w : ℝ) := by
    exact_mod_cast le_of_lt (occurrence_lt_expectedMinimumPrime w)
  have := pivotCoordinate_mono w hocc hle
  omega

/-- **C_lecture EST `progression (z*) ≥ 1` ; sa négation V EST `progression (z*) = 0`.**
E111 §B : `progression = 0` sur 88/300 zéros ON réels — ce n'est pas une signature OFF. -/
theorem secondTower_reads_iff_progression_pos (z : TrueZero) :
    (secondTowerOf z).properState.reaches (occurrence (mirrorMember z)) ↔
      0 < progression (mirrorMember z) := by
  rw [secondTower_reads_occurrence_iff_coordinate_lt]
  unfold progression
  omega

/-! ## 3. Décomposition du pivot sur la paire OFF consécutive -/

/-- **Décomposition du pivot du membre miroir, sous consécutivité stricte.** Le pas de coordonnée
entre les deux membres de la paire, `k(z*, p_min(z*)) − k(z, p_min(z))`, se décompose exactement en
la progression première `progression (z*)` plus un reste `δk ∈ {0, 1}` — porté ENTIÈREMENT par la
grille commune à même hauteur (`pivotCoordinate_mirror_mem`), jamais par `β`. -/
theorem mirror_pivot_decomposition_of_consecutive {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (hab : PZeroMembersConsecutive z.1 (mirrorMember z).1) :
    ∃ δk : ℤ, (δk = 0 ∨ δk = 1) ∧
      pivotCoordinate (mirrorMember z) (expectedMinimumPrime (mirrorMember z) : ℝ) =
        pivotCoordinate z (expectedMinimumPrime z : ℝ) + progression (mirrorMember z) + δk := by
  have hOcc : (occurrence (mirrorMember z) : ℝ) = (expectedMinimumPrime z : ℝ) := by
    exact_mod_cast (expectedMinimum_eq_mirror_occurrence_of_consecutive hab).symm
  have hcoord : pivotCoordinate (mirrorMember z) (occurrence (mirrorMember z) : ℝ) =
      pivotCoordinate (mirrorMember z) (expectedMinimumPrime z : ℝ) := by rw [hOcc]
  have hmem := pivotCoordinate_mirror_mem hβ (expectedMinimumPrime z : ℝ)
  refine ⟨pivotCoordinate (mirrorMember z) (expectedMinimumPrime z : ℝ) -
    pivotCoordinate z (expectedMinimumPrime z : ℝ), by omega, ?_⟩
  unfold progression
  rw [hcoord]
  ring

/-- **Corollaire** : sous consécutivité stricte, la coordonnée de pivot du membre miroir est au
moins celle de `z` — le pas de coordonnée n'est jamais négatif. -/
theorem mirror_pivot_mono_of_consecutive {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (hab : PZeroMembersConsecutive z.1 (mirrorMember z).1) :
    pivotCoordinate z (expectedMinimumPrime z : ℝ) ≤
      pivotCoordinate (mirrorMember z) (expectedMinimumPrime (mirrorMember z) : ℝ) := by
  obtain ⟨δk, hδk, heq⟩ := mirror_pivot_decomposition_of_consecutive hβ hab
  have hprog := progression_nonneg (mirrorMember z)
  omega

/-! ## 4. La signature (D) de l'auteur, sous consécutivité, côté bas -/

/-- **La signature (D) de l'auteur** : sous consécutivité stricte et `β < 1/2`, l'horloge des
membres avance d'exactement un cran, la hauteur est identique, l'horloge des hauteurs est
identique, la portée première coïncide sur tout rang, l'accroissement de phase coïncide sur tout
intervalle, la translation est strictement bornée par `1/(πT)` anneau, et la coordonnée de pivot du
membre miroir est au moins celle de `z`. Tout est déjà compilé : `mirror_sourceIndex_of_consecutive`,
`mirrorMember_ordinate`, `mirror_heightEventIndex_eq`, `mirror_span_eq`, `mirror_phase_increment_eq`,
`mirror_translation_lt`, `mirror_pivot_mono_of_consecutive`. La forme `hOff` s'obtient par
`off_lowerSide` (l'un des deux membres est côté bas) ; on garde `hβ` pour rester exact. -/
theorem off_consecutive_translation_signature {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (hab : PZeroMembersConsecutive z.1 (mirrorMember z).1) :
    nZeroSourceIndex (mirrorMember z).1 = nZeroSourceIndex z.1 + 1 ∧
    rZeroHeight (mirrorMember z).1 = rZeroHeight z.1 ∧
    nZeroHeightEventIndex (tZeroHeightEvent (mirrorMember z)) =
      nZeroHeightEventIndex (tZeroHeightEvent z) ∧
    (∀ n : ℕ, TowerPrimeGapSpan (mirrorMember z) n = TowerPrimeGapSpan z n) ∧
    (∀ q₁ q₂ : ℝ, Real.pi * towerPosition (mirrorMember z) q₂ -
        Real.pi * towerPosition (mirrorMember z) q₁ =
      Real.pi * towerPosition z q₂ - Real.pi * towerPosition z q₁) ∧
    (∀ q : ℝ, 0 < towerPosition (mirrorMember z) q - towerPosition z q ∧
      towerPosition (mirrorMember z) q - towerPosition z q <
        (1 - 2 * rZeroRadialPosition z.1) / (Real.pi * rZeroHeight z.1)) ∧
    pivotCoordinate z (expectedMinimumPrime z : ℝ) ≤
      pivotCoordinate (mirrorMember z) (expectedMinimumPrime (mirrorMember z) : ℝ) :=
  ⟨mirror_sourceIndex_of_consecutive hab, mirrorMember_ordinate z, mirror_heightEventIndex_eq z,
    mirror_span_eq z, fun q₁ q₂ => mirror_phase_increment_eq z q₁ q₂,
    fun q => mirror_translation_lt hβ q, mirror_pivot_mono_of_consecutive hβ hab⟩

/-!
## 5. Ce que ce fichier dit et ne dit pas

1. (B) « événement ⟹ progression ≥ 1 anneau » est RÉFUTÉE par E111 §B (88/300 ON à `Prog = 0`) :
   le même-anneau est un comportement normal des zéros ON, pas une signature OFF.
2. Une prémisse qui interdirait la « translation sous un anneau » interdit `T_E = T_L` (car
   `T_E = T_L ⟹ translation < 1/(πT)` est ici un théorème) : elle EST `PHeightProgression`
   (`Terminal/ReverseEngineeredClosure.lean`), équivalente à RH — pas plus petite.
3. Tout observable de la géométrie des anneaux à `T` fixé coïncide sur la paire miroir (ce fichier +
   `MirrorFrequency.lean` + `pivotCoordinate_sameHeight_shift_le_one`) : les seuls objets
   β-visibles restants sont `β`, l'étiquette `n`, et l'amplitude `‖zeroTerm‖ = q^β/‖ρ‖`
   (`zeroTerm_norm`).

Aucun `Prop` de prémisse n'est défini ici ; `RH_FOUND=FALSE`.
-/

#print axioms off_consecutive_translation_signature
#print axioms mirror_phase_gap_lt
#print axioms mirror_pivot_decomposition_of_consecutive

end RHV6Fresh
