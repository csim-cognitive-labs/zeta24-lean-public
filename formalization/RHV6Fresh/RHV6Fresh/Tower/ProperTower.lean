/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Tower.Incidences

/-!
# RHV6Fresh — L1 : paires à deux lois, Tour propre complète et état porté

Transcription du maître mathématique RHV6 §5 (correction du 2026-09-22, §13) et
du maître Lean §5.1 corrigé (§22-A) :

* `AnalyticContactPair z` : **toute** paire (C⁻, C⁺) satisfaisant les deux lois
  exactes — loi tangentielle `sin (T·log C⁻ − φ) = 0` (l'entrée est une
  incidence de la phase) et loi de rotation `sin (T·(log C⁺ − log C⁻)) = 0`
  (le dernier rayon est un rayon de la même rotation).  C'est le type de
  **certification** des deux lois : la paire portée par la Tour les satisfait,
  et les valeurs des formules à une autre coordonnée (`analyticPairAt z k`,
  contrôles de formule) les satisfont aussi sans être des contacts de la Tour,
  qui n'en a que deux (sixième correction du 2026-09-22) ; ce type **n'est
  pas** l'état propre.
* `TrueTower z` : le mouvement unique de z (`TowerMotion z`, phase et rayons)
  portant SON incidence d'entrée et SON dernier rayon comme champs
  constitutifs ; `TrueTower.properState` est l'unique état porté.

La coordonnée d'entrée `k = (T·log C⁻ − φ)/π` et le nombre d'étages
`m = T·(log C⁺ − log C⁻)/π` sont **lus** sur une paire ; ils ne sont ni
cherchés, ni posés, ni exposés comme champs.  Aucun premier, rang, comptage,
seuil ou sélecteur n'entre ici.

La Tour portée d'un zéro (le mouvement `towerMotionOf z` muni de son entrée et de
son dernier rayon) est produite par la règle du pivot (`Direct/PivotCell.lean`,
`Direct/PairTowers.lean` : `firstTowerOf z`, `secondTowerOf z`) ; elle n'est ni définie
ici par une formule de k, ni remplacée par une hypothèse.

PORT (jamais import) de `RHV3Lean/Objects/TrueTowerState.lean` au commit
`87f84474` (2026-09-09, `TTrueHarmonicTowerState` à deux lois, `recoveredKappa`,
`recoveredSpan`, inversions, rigidité), représentation perdue au commit
`f8a880b4` (contacts consécutifs puis branche principale `k = 0`).  Les noms
historiques contenant « height » ne sont pas repris (mot interdit dans
l'implémentation) ; `rZeroHeight` reste le nom RHV3Lean de la coordonnée `T`.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **Paire à deux lois** : toute paire `(C⁻, C⁺)` de rayons de la Tour de `z`
satisfaisant la loi tangentielle et la loi de rotation : type de certification des
deux lois.  La Tour n'a que deux contacts avec l'axe algébrique ; une autre valeur
des formules est un contrôle de formule, jamais un contact de la Tour ; ce type n'est
jamais l'état propre par lui-même (maître Lean §22-A, §26). -/
structure AnalyticContactPair (z : TrueZero) where
  /-- `C⁻` : rayon de l'incidence d'entrée. -/
  entryContact : ℝ
  /-- `C⁺` : dernier rayon du mouvement. -/
  lastRayContact : ℝ
  entryContact_pos : 0 < entryContact
  lastRayContact_pos : 0 < lastRayContact
  ordered : entryContact < lastRayContact
  /-- Loi de rotation : le dernier rayon est un rayon de la même rotation. -/
  rotationLaw :
    Real.sin (rZeroHeight z.1 * (Real.log lastRayContact - Real.log entryContact)) = 0
  /-- Loi tangentielle : l'entrée est une incidence de la phase propre. -/
  tangentLaw :
    Real.sin (rZeroHeight z.1 * Real.log entryContact - rTowerPhase z) = 0

namespace AnalyticContactPair

variable {z : TrueZero} (𝒯 : AnalyticContactPair z)

/-! ## 1. Le diamètre logarithmique du mouvement -/

noncomputable def logDiameter : ℝ :=
  Real.log 𝒯.lastRayContact - Real.log 𝒯.entryContact

theorem logDiameter_positive : 0 < 𝒯.logDiameter := by
  have hLog : Real.log 𝒯.entryContact < Real.log 𝒯.lastRayContact :=
    Real.log_lt_log 𝒯.entryContact_pos 𝒯.ordered
  unfold logDiameter
  linarith

/-! ## 2. Les deux lectures : coordonnée d'entrée et nombre d'étages -/

/-- Lecture de la coordonnée d'entrée : `k = (T·log C⁻ − φ)/π`. -/
noncomputable def entryReading : ℝ :=
  (rZeroHeight z.1 * Real.log 𝒯.entryContact - rTowerPhase z) / Real.pi

/-- Lecture du nombre d'étages : `m = T·(log C⁺ − log C⁻)/π`. -/
noncomputable def stageReading : ℝ :=
  rTowerDensity z * 𝒯.logDiameter

/-- La coordonnée d'entrée lue est un entier : c'est la loi tangentielle et rien d'autre. -/
theorem entryReading_isInt : ∃ k : ℤ, 𝒯.entryReading = (k : ℝ) := by
  obtain ⟨k, hRoot⟩ := Real.sin_eq_zero_iff.mp 𝒯.tangentLaw
  refine ⟨k, ?_⟩
  unfold entryReading
  rw [← hRoot]
  field_simp

/-- Le nombre d'étages lu est un entier : c'est la loi de rotation et rien d'autre. -/
theorem stageReading_isInt : ∃ m : ℤ, 𝒯.stageReading = (m : ℝ) := by
  obtain ⟨m, hRoot⟩ := Real.sin_eq_zero_iff.mp 𝒯.rotationLaw
  refine ⟨m, ?_⟩
  have hPi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold stageReading rTowerDensity rTowerHeight logDiameter
  field_simp
  linarith [hRoot]

theorem stageReading_positive : 0 < 𝒯.stageReading :=
  mul_pos (thm_rTowerDensity_positive z) 𝒯.logDiameter_positive

/-- Le nombre d'étages lu est un naturel strictement positif. -/
theorem stageReading_isNat : ∃ m : ℕ, 0 < m ∧ 𝒯.stageReading = (m : ℝ) := by
  obtain ⟨n, hValue⟩ := 𝒯.stageReading_isInt
  have hPositive : (0 : ℝ) < (n : ℝ) := hValue ▸ 𝒯.stageReading_positive
  have hIntPositive : 0 < n := by exact_mod_cast hPositive
  refine ⟨n.toNat, by omega, ?_⟩
  rw [hValue]
  congr 1
  omega

/-- La coordonnée d'entrée, lue (jamais posée). -/
noncomputable def entryCoordinate : ℤ := 𝒯.entryReading_isInt.choose

theorem entryCoordinate_cast : 𝒯.entryReading = (𝒯.entryCoordinate : ℝ) :=
  𝒯.entryReading_isInt.choose_spec

/-- Le nombre d'étages, lu (jamais posé). -/
noncomputable def stageCount : ℕ := 𝒯.stageReading_isNat.choose

theorem stageCount_positive : 0 < 𝒯.stageCount :=
  𝒯.stageReading_isNat.choose_spec.1

theorem stageCount_cast : 𝒯.stageReading = (𝒯.stageCount : ℝ) :=
  𝒯.stageReading_isNat.choose_spec.2

/-! ## 3. Les deux inversions : l'état rend le zéro -/

/-- Inversion de la coordonnée `T` : `T = m·π/(log C⁺ − log C⁻)` avec `m` lu. -/
theorem recovers_T :
    rZeroHeight z.1 = 𝒯.stageReading * Real.pi / 𝒯.logDiameter := by
  have hDiameter : 𝒯.logDiameter ≠ 0 := ne_of_gt 𝒯.logDiameter_positive
  unfold stageReading rTowerDensity rTowerHeight
  field_simp

/-- Inversion tangentielle : `β = T/tan(T·log C⁻)`, lue sur le seul contact d'entrée ;
la périodicité de la tangente absorbe la coordonnée lue. -/
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
    𝒯.entryContact = rTowerIncidence z 𝒯.entryCoordinate := by
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  have hK :
      rZeroHeight z.1 * Real.log 𝒯.entryContact =
        rTowerPhase z + (𝒯.entryCoordinate : ℝ) * Real.pi := by
    have hCast := 𝒯.entryCoordinate_cast
    unfold entryReading at hCast
    field_simp at hCast
    linarith [hCast]
  unfold rTowerIncidence rTowerLogIncidence rTowerHeight
  rw [show (rTowerPhase z + (𝒯.entryCoordinate : ℝ) * Real.pi) / rZeroHeight z.1 =
      Real.log 𝒯.entryContact by rw [← hK]; field_simp]
  exact (Real.exp_log 𝒯.entryContact_pos).symm

theorem lastRayContact_eq_incidence :
    𝒯.lastRayContact = rTowerIncidence z (𝒯.entryCoordinate + 𝒯.stageCount) := by
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  have hK :
      rZeroHeight z.1 * Real.log 𝒯.entryContact =
        rTowerPhase z + (𝒯.entryCoordinate : ℝ) * Real.pi := by
    have hCast := 𝒯.entryCoordinate_cast
    unfold entryReading at hCast
    field_simp at hCast
    linarith [hCast]
  have hM :
      rZeroHeight z.1 * 𝒯.logDiameter = (𝒯.stageCount : ℝ) * Real.pi := by
    have hCast := 𝒯.stageCount_cast
    unfold stageReading rTowerDensity rTowerHeight at hCast
    field_simp at hCast
    linarith [hCast]
  have hSum :
      rZeroHeight z.1 * Real.log 𝒯.lastRayContact =
        rTowerPhase z + ((𝒯.entryCoordinate : ℝ) + (𝒯.stageCount : ℝ)) * Real.pi := by
    have hD : 𝒯.logDiameter = Real.log 𝒯.lastRayContact - Real.log 𝒯.entryContact := rfl
    rw [hD] at hM
    nlinarith [hK, hM]
  unfold rTowerIncidence rTowerLogIncidence rTowerHeight
  rw [show (rTowerPhase z + ((𝒯.entryCoordinate + (𝒯.stageCount : ℤ) : ℤ) : ℝ) * Real.pi) /
      rZeroHeight z.1 = Real.log 𝒯.lastRayContact by
    push_cast; rw [← hSum]; field_simp]
  exact (Real.exp_log 𝒯.lastRayContact_pos).symm

/-- Quand le mouvement compte un seul étage, ses deux contacts sont la paire
consécutive `(contactMinusAt z k, contactPlusAt z k)` à la coordonnée lue `k`. -/
theorem contacts_of_one_stage (hOne : 𝒯.stageCount = 1) :
    𝒯.entryContact = contactMinusAt z 𝒯.entryCoordinate ∧
      𝒯.lastRayContact = contactPlusAt z 𝒯.entryCoordinate := by
  refine ⟨𝒯.entryContact_eq_incidence, ?_⟩
  rw [𝒯.lastRayContact_eq_incidence, hOne]
  rfl

/-! ## 5. Rigidité : même état (contacts et étages), même zéro -/

/-- Même état propre ⇒ même zéro (maître mathématique §5.e) : l'état porte ses deux
contacts avec ses lectures ; l'inversion `(C⁻, C⁺, m) → (T, β)` rend les coordonnées
et `(T, β)` rend le zéro.  Les contacts d'un zéro lui sont propres et ne sont
partagés avec aucun autre zéro. -/
theorem same_state_same_zero
    {zLeft zRight : TrueZero}
    (𝒯L : AnalyticContactPair zLeft) (𝒯R : AnalyticContactPair zRight)
    (hStages : 𝒯L.stageCount = 𝒯R.stageCount)
    (hEntry : 𝒯L.entryContact = 𝒯R.entryContact)
    (hLast : 𝒯L.lastRayContact = 𝒯R.lastRayContact) :
    zLeft = zRight := by
  have hDiameter : 𝒯L.logDiameter = 𝒯R.logDiameter := by
    unfold logDiameter
    rw [hEntry, hLast]
  have hStagesReal : 𝒯L.stageReading = 𝒯R.stageReading := by
    rw [𝒯L.stageCount_cast, 𝒯R.stageCount_cast, hStages]
  have hSameT : rZeroHeight zLeft.1 = rZeroHeight zRight.1 := by
    rw [𝒯L.recovers_T, 𝒯R.recovers_T, hStagesReal, hDiameter]
  have hSameBeta : rZeroRadialPosition zLeft.1 = rZeroRadialPosition zRight.1 := by
    rw [𝒯L.recovers_beta, 𝒯R.recovers_beta, hSameT, hEntry]
  exact Subtype.ext (thm_zero_identity_of_sameSupport (Complex.ext hSameBeta hSameT))

end AnalyticContactPair

/-! ## 6. Valeurs des formules à une coordonnée : contrôles de formule

Contrôle de cohérence des formules (pas un producteur, jamais un `properState`,
jamais un contact de la Tour) : la valeur `(C_k, C_{k+1})` des formules
tangentielles satisfait les deux lois à toute coordonnée `k`.  La Tour n'a que
deux contacts avec l'axe algébrique (sixième correction du 2026-09-22) ; ces
valeurs ne sont pas des contacts, la paire `k = 0` n'a aucun privilège et n'est
jamais appelée état propre. -/

noncomputable def analyticPairAt (z : TrueZero) (k : ℤ) : AnalyticContactPair z where
  entryContact := contactMinusAt z k
  lastRayContact := contactPlusAt z k
  entryContact_pos := contactMinusAt_positive z k
  lastRayContact_pos := contactPlusAt_positive z k
  ordered := contactAt_ordered z k
  rotationLaw := by
    rw [contactAt_consecutive_logWidth]
    have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
    rw [show rZeroHeight z.1 * (Real.pi / rZeroHeight z.1) = Real.pi by field_simp]
    exact Real.sin_pi
  tangentLaw := by
    unfold contactMinusAt
    rw [(towerMotionOf z).incidence_eq, Real.log_exp, (towerMotionOf z).logIncidence_eq,
      towerMotion_phase]
    have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
    rw [show rZeroHeight z.1 *
        ((Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) + (k : ℝ) * Real.pi) /
          rZeroHeight z.1) - rTowerPhase z = (k : ℝ) * Real.pi by
      unfold rTowerPhase rTowerHeight rTowerRadialPosition; field_simp; ring]
    exact Real.sin_int_mul_pi k

theorem analyticPairAt_entryContact (z : TrueZero) (k : ℤ) :
    (analyticPairAt z k).entryContact = contactMinusAt z k := rfl

theorem analyticPairAt_lastRayContact (z : TrueZero) (k : ℤ) :
    (analyticPairAt z k).lastRayContact = contactPlusAt z k := rfl

/-! ## 7. Séparation dans la fibre par l'entrée (maître mathématique §5.e)

Deux zéros de même coordonnée `T` dont des paires à deux lois partagent le
contact d'entrée sont le même zéro : la loi tangentielle donne
`T·log C⁻ = φ + kπ` avec `0 < φ < π/2`, donc `k(z) = k(z')` et `φ(z) = φ(z')`,
puis `β(z) = β(z')`.  Dérivation sans hypothèse. -/

theorem entry_separates_in_fiber {zLeft zRight : TrueZero}
    (𝒯L : AnalyticContactPair zLeft) (𝒯R : AnalyticContactPair zRight)
    (hT : rZeroHeight zRight.1 = rZeroHeight zLeft.1)
    (hEntry : 𝒯R.entryContact = 𝒯L.entryContact) :
    zLeft = zRight := by
  obtain ⟨kL, hL⟩ := Real.sin_eq_zero_iff.mp 𝒯L.tangentLaw
  obtain ⟨kR, hR⟩ := Real.sin_eq_zero_iff.mp 𝒯R.tangentLaw
  rw [hT, hEntry] at hR
  have hPhaseDiff :
      ((kR - kL : ℤ) : ℝ) * Real.pi = rTowerPhase zLeft - rTowerPhase zRight := by
    push_cast
    linarith [hL, hR]
  have hLpos := thm_rTowerPhase_positive zLeft
  have hRpos := thm_rTowerPhase_positive zRight
  have hLlt := thm_rTowerPhase_lt_piDivTwo zLeft
  have hRlt := thm_rTowerPhase_lt_piDivTwo zRight
  have hPi := Real.pi_pos
  have hSameK : kR - kL = 0 := by
    rcases lt_trichotomy (kR - kL) 0 with hNeg | hZero | hPos
    · exfalso
      have hLe : ((kR - kL : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (Int.le_sub_one_iff.mpr hNeg)
      have : ((kR - kL : ℤ) : ℝ) * Real.pi ≤ -Real.pi := by nlinarith
      linarith
    · exact hZero
    · exfalso
      have hGe : (1 : ℝ) ≤ ((kR - kL : ℤ) : ℝ) := by exact_mod_cast hPos
      have : Real.pi ≤ ((kR - kL : ℤ) : ℝ) * Real.pi := by nlinarith
      linarith
  have hSamePhase : rTowerPhase zLeft = rTowerPhase zRight := by
    rw [hSameK] at hPhaseDiff
    push_cast at hPhaseDiff
    linarith
  have hRatio :
      rZeroHeight zLeft.1 / rZeroRadialPosition zLeft.1 =
        rZeroHeight zRight.1 / rZeroRadialPosition zRight.1 :=
    Real.arctan_strictMono.injective hSamePhase
  have hβL := thm_zeroRadialPosition_positive zLeft.1
  have hβR := thm_zeroRadialPosition_positive zRight.1
  have hTne : rZeroHeight zLeft.1 ≠ 0 := ne_of_gt zLeft.2
  have hSameBeta : rZeroRadialPosition zLeft.1 = rZeroRadialPosition zRight.1 := by
    rw [hT, div_eq_div_iff (ne_of_gt hβL) (ne_of_gt hβR)] at hRatio
    exact (mul_left_cancel₀ hTne hRatio).symm
  exact Subtype.ext (thm_zero_identity_of_sameSupport (Complex.ext hSameBeta hT.symm))

/-! ## 8. La Tour propre complète : le mouvement portant son état

Maître Lean §5.1 (corrigé §22-A) : la Tour d'un vrai zéro est son mouvement
(`TowerMotion z`) **avec** son incidence d'entrée et son dernier rayon, champs
constitutifs soumis aux deux lois.  `properState` est l'unique état porté.

La Tour portée — le mouvement `towerMotionOf z` muni de son entrée et de son
dernier rayon — est produite par la règle du pivot (`firstTowerOf z`, et dans la seconde
orientation `secondTowerOf z : InvertedTower`, `Tower/InvertedTower.lean`,
`Direct/PairTowers.lean`) ; elle n'est pas définie ici et aucune
formule de `k`, aucun sélecteur, aucune hypothèse ne la remplace. -/

/-- **La Tour propre complète** : le mouvement unique de `z` portant SON entrée et
SON dernier rayon. -/
structure TrueTower (z : TrueZero) extends TowerMotion z, AnalyticContactPair z

namespace TrueTower

variable {z : TrueZero} (𝒯 : TrueTower z)

/-- L'unique état porté par le mouvement. -/
def properState : AnalyticContactPair z := 𝒯.toAnalyticContactPair

theorem properState_entryContact : 𝒯.properState.entryContact = 𝒯.entryContact := rfl

theorem properState_lastRayContact : 𝒯.properState.lastRayContact = 𝒯.lastRayContact := rfl

/-- Le mouvement porté est celui des formules (les champs sont fixés par `z`). -/
theorem phase_eq_motion : 𝒯.phase = (towerMotionOf z).phase := by
  rw [𝒯.phase_eq, towerMotion_phase]

theorem incidence_eq_motion (k : ℤ) : 𝒯.incidence k = (towerMotionOf z).incidence k := by
  rw [𝒯.incidence_eq, 𝒯.logIncidence_eq, 𝒯.phase_eq, towerMotion_incidence, towerMotion_phase]

end TrueTower

end RHV6Fresh
