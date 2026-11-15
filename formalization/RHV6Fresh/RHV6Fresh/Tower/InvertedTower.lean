/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Tower.ProperTower

/-!
# RHV6Fresh — la seconde orientation : contacts inversés (théorème de la réflexion `1 − ρ`)

Niveau GÉOMÉTRIE.  La seconde Tour de la paire est la Tour du zéro que l'équation fonctionnelle
produit, `1 − ρ = (1 − β, −T)`, conjugué du miroir supérieur : phase `−φ*`, pas `−π/T`, parcours dans
le sens opposé.  Ses rayons sont ceux du miroir supérieur parcourus à l'envers, et son anneau à sa
propre coordonnée `−(k+1)` a pour entrée `C*_{k+1}` (rayon du haut) et pour dernier rayon `C*_k`
(rayon du bas).  L'inversion des contacts est ce THÉORÈME (`Tower/ReflectedMotion.lean`,
`invertedPairAt_eq_reflected`), jamais une définition ni un énoncé ; ce module porte le type des
paires de la seconde orientation et ses lectures.

* `InvertedContactPair z` : la paire à deux lois de la seconde orientation.  L'**incidence d'entrée**
  est le rayon du haut, le **dernier rayon** est le rayon du bas ; même loi tangentielle (l'entrée est
  une incidence de la phase), même loi de rotation (le dernier rayon est un rayon de la même rotation).
  La cellule est le même anneau que dans l'orientation croissante, parcouru dans le sens opposé (`upright`).
* `invertedPairAt z k` : la valeur des formules à la coordonnée `k` dans la seconde orientation,
  entrée `C_{k+1}`, dernier rayon `C_k` (contrôle de formule, jamais un contact de la Tour par
  lui-même).
* `InvertedTower z` : le mouvement unique de `z` portant SON entrée et SON dernier rayon dans la
  seconde orientation ; `InvertedTower.properState` est l'unique état porté.

Les lectures (coordonnée d'entrée, nombre d'étages) et les inversions (`recovers_T`, `recovers_beta`)
sont les mêmes que dans `Tower/ProperTower.lean`, appliquées à l'entrée du haut.  Aucun premier,
aucun rang, aucun comptage n'entre ici.  Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **Paire à deux lois de la seconde orientation** : l'entrée est le rayon du haut, le dernier rayon
est le rayon du bas (« ce qu'on considérait C⁺ devient C⁻ et inversement »). -/
structure InvertedContactPair (z : TrueZero) where
  /-- `C⁻` : rayon de l'incidence d'entrée (le rayon du haut dans cette orientation). -/
  entryContact : ℝ
  /-- `C⁺` : dernier rayon du mouvement (le rayon du bas dans cette orientation). -/
  lastRayContact : ℝ
  entryContact_pos : 0 < entryContact
  lastRayContact_pos : 0 < lastRayContact
  /-- Ordre de la seconde orientation : le dernier rayon est sous l'entrée. -/
  ordered : lastRayContact < entryContact
  /-- Loi de rotation : le dernier rayon est un rayon de la même rotation. -/
  rotationLaw :
    Real.sin (rZeroHeight z.1 * (Real.log entryContact - Real.log lastRayContact)) = 0
  /-- Loi tangentielle : l'entrée est une incidence de la phase propre. -/
  tangentLaw :
    Real.sin (rZeroHeight z.1 * Real.log entryContact - rTowerPhase z) = 0

namespace InvertedContactPair

variable {z : TrueZero} (𝒯 : InvertedContactPair z)

/-! ## 1. Le même anneau, lu dans l'orientation croissante -/

/-- La cellule de la paire inversée, lue dans l'orientation croissante : rayon du bas, rayon du haut.
Le rayon du bas satisfait la loi tangentielle par les deux lois de la paire inversée. -/
noncomputable def upright : AnalyticContactPair z where
  entryContact := 𝒯.lastRayContact
  lastRayContact := 𝒯.entryContact
  entryContact_pos := 𝒯.lastRayContact_pos
  lastRayContact_pos := 𝒯.entryContact_pos
  ordered := 𝒯.ordered
  rotationLaw := 𝒯.rotationLaw
  tangentLaw := by
    obtain ⟨a, ha⟩ := Real.sin_eq_zero_iff.mp 𝒯.tangentLaw
    obtain ⟨b, hb⟩ := Real.sin_eq_zero_iff.mp 𝒯.rotationLaw
    exact Real.sin_eq_zero_iff.mpr ⟨a - b, by push_cast; linear_combination ha - hb⟩

theorem upright_entryContact : 𝒯.upright.entryContact = 𝒯.lastRayContact := rfl

theorem upright_lastRayContact : 𝒯.upright.lastRayContact = 𝒯.entryContact := rfl

/-! ## 2. Le diamètre logarithmique et les deux lectures -/

noncomputable def logDiameter : ℝ :=
  Real.log 𝒯.entryContact - Real.log 𝒯.lastRayContact

theorem logDiameter_positive : 0 < 𝒯.logDiameter := 𝒯.upright.logDiameter_positive

/-- Lecture du nombre d'étages : `m = T·(log C⁻ − log C⁺)/π` (entrée en haut). -/
noncomputable def stageReading : ℝ :=
  rTowerDensity z * 𝒯.logDiameter

theorem stageReading_isNat : ∃ m : ℕ, 0 < m ∧ 𝒯.stageReading = (m : ℝ) :=
  𝒯.upright.stageReading_isNat

/-- Le nombre d'étages, lu (jamais posé). -/
noncomputable def stageCount : ℕ := 𝒯.upright.stageCount

theorem stageCount_positive : 0 < 𝒯.stageCount := 𝒯.upright.stageCount_positive

theorem stageCount_cast : 𝒯.stageReading = (𝒯.stageCount : ℝ) := 𝒯.upright.stageCount_cast

/-- Lecture de la coordonnée d'entrée : `(T·log C⁻ − φ)/π`, sur l'entrée du haut. -/
noncomputable def entryReading : ℝ :=
  (rZeroHeight z.1 * Real.log 𝒯.entryContact - rTowerPhase z) / Real.pi

/-- La coordonnée d'entrée lue est un entier : c'est la loi tangentielle et rien d'autre. -/
theorem entryReading_isInt : ∃ k : ℤ, 𝒯.entryReading = (k : ℝ) := by
  obtain ⟨k, hRoot⟩ := Real.sin_eq_zero_iff.mp 𝒯.tangentLaw
  refine ⟨k, ?_⟩
  unfold entryReading
  rw [← hRoot]
  field_simp

/-- La coordonnée d'entrée, lue : celle du rayon du haut, soit la coordonnée du bas plus le nombre
d'étages. -/
noncomputable def entryCoordinate : ℤ :=
  𝒯.upright.entryCoordinate + 𝒯.upright.stageCount

/-! ## 3. Les deux inversions : l'état rend le zéro -/

/-- Inversion de la coordonnée `T` : `T = m·π/(log C⁻ − log C⁺)` avec `m` lu. -/
theorem recovers_T :
    rZeroHeight z.1 = 𝒯.stageReading * Real.pi / 𝒯.logDiameter :=
  𝒯.upright.recovers_T

/-- Inversion tangentielle : `β = T/tan(T·log C⁻)`, lue sur le seul contact d'entrée (le rayon du
haut) ; la périodicité de la tangente absorbe la coordonnée lue. -/
theorem recovers_beta :
    rZeroRadialPosition z.1 =
      rZeroHeight z.1 / Real.tan (rZeroHeight z.1 * Real.log 𝒯.entryContact) := by
  have hRadial : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  obtain ⟨k, hRoot⟩ := Real.sin_eq_zero_iff.mp 𝒯.tangentLaw
  have hPhase :
      rZeroHeight z.1 * Real.log 𝒯.entryContact = rTowerPhase z + (k : ℝ) * Real.pi := by
    linarith [hRoot]
  rw [hPhase, (Real.tan_periodic.int_mul k) (rTowerPhase z), rTowerPhase, Real.tan_arctan]
  unfold rTowerHeight rTowerRadialPosition
  field_simp

/-! ## 4. Les contacts sont des rayons de la Tour, aux coordonnées lues -/

theorem entryContact_eq_incidence :
    𝒯.entryContact = rTowerIncidence z 𝒯.entryCoordinate :=
  𝒯.upright.lastRayContact_eq_incidence

theorem lastRayContact_eq_incidence :
    𝒯.lastRayContact = rTowerIncidence z (𝒯.entryCoordinate - 𝒯.stageCount) := by
  have h := 𝒯.upright.entryContact_eq_incidence
  unfold entryCoordinate stageCount
  rw [show 𝒯.upright.entryCoordinate + (𝒯.upright.stageCount : ℤ) - (𝒯.upright.stageCount : ℤ) =
      𝒯.upright.entryCoordinate by ring]
  exact h

end InvertedContactPair

/-! ## 5. Valeurs des formules à une coordonnée dans la seconde orientation : contrôles de formule -/

/-- La valeur des formules à la coordonnée `k` dans la seconde orientation : entrée `C_{k+1}` (rayon
du haut), dernier rayon `C_k` (rayon du bas).  Même anneau que `analyticPairAt z k`, contacts inversés. -/
noncomputable def invertedPairAt (z : TrueZero) (k : ℤ) : InvertedContactPair z where
  entryContact := contactPlusAt z k
  lastRayContact := contactMinusAt z k
  entryContact_pos := contactPlusAt_positive z k
  lastRayContact_pos := contactMinusAt_positive z k
  ordered := contactAt_ordered z k
  rotationLaw := (analyticPairAt z k).rotationLaw
  tangentLaw := (analyticPairAt z (k + 1)).tangentLaw

theorem invertedPairAt_entryContact (z : TrueZero) (k : ℤ) :
    (invertedPairAt z k).entryContact = contactPlusAt z k := rfl

theorem invertedPairAt_lastRayContact (z : TrueZero) (k : ℤ) :
    (invertedPairAt z k).lastRayContact = contactMinusAt z k := rfl

/-- Le même anneau, lu dans l'orientation croissante, est `analyticPairAt z k`. -/
theorem invertedPairAt_upright (z : TrueZero) (k : ℤ) :
    (invertedPairAt z k).upright = analyticPairAt z k := rfl

/-! ## 6. La Tour propre complète dans la seconde orientation -/

/-- **La Tour propre complète de la seconde orientation** : le mouvement unique de `z` portant SON
entrée (rayon du haut) et SON dernier rayon (rayon du bas). -/
structure InvertedTower (z : TrueZero) extends TowerMotion z, InvertedContactPair z

namespace InvertedTower

variable {z : TrueZero} (𝒯 : InvertedTower z)

/-- L'unique état porté par le mouvement dans la seconde orientation. -/
def properState : InvertedContactPair z := 𝒯.toInvertedContactPair

theorem properState_entryContact : 𝒯.properState.entryContact = 𝒯.entryContact := rfl

theorem properState_lastRayContact : 𝒯.properState.lastRayContact = 𝒯.lastRayContact := rfl

end InvertedTower

end RHV6Fresh
