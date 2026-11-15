/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.CleanTerminal

/-!
# RHV6Fresh — le mouvement analytique d'un vrai zéro

Transcription du maître mathématique RHV6 §4 : la Tour d'un vrai zéro est un
mouvement géométrique unique, de phase `φ = atan(T/β)`, de vitesse `T`, dont
les rayons sont `C_k = exp((φ + kπ)/T)`.  Ce module porte ce mouvement seul
(phase, log-rayons, rayons), produit par les formules et par rien d'autre :
aucun premier, rang, minimum attendu, premier constaté ni proposition
terminale n'y entre.

L'état porté par le mouvement (incidence d'entrée, dernier rayon) est
représenté dans `Tower/ProperTower.lean` (`AnalyticContactPair`, `TrueTower`,
`TrueTower.properState`), conformément au maître Lean §5.1 et §22-A.
-/

namespace RHV6Fresh

open RHV3Lean

/-- Le mouvement analytique porté par un vrai zéro : phase et rayons. -/
structure TowerMotion (z : TrueZero) where
  phase : ℝ
  logIncidence : ℤ → ℝ
  incidence : ℤ → ℝ
  phase_eq :
    phase = Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1)
  logIncidence_eq : ∀ k : ℤ,
    logIncidence k = (phase + (k : ℝ) * Real.pi) / rZeroHeight z.1
  incidence_eq : ∀ k : ℤ, incidence k = Real.exp (logIncidence k)

/-- Le mouvement produit par les seules coordonnées de `z`. -/
noncomputable def towerMotionOf (z : TrueZero) : TowerMotion z where
  phase := rTowerPhase z
  logIncidence := rTowerLogIncidence z
  incidence := rTowerIncidence z
  phase_eq := rfl
  logIncidence_eq := fun _ => rfl
  incidence_eq := fun _ => rfl

theorem towerMotion_phase (z : TrueZero) :
    (towerMotionOf z).phase =
      Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) :=
  (towerMotionOf z).phase_eq

theorem towerMotion_incidence (z : TrueZero) (k : ℤ) :
    (towerMotionOf z).incidence k =
      Real.exp (((towerMotionOf z).phase + (k : ℝ) * Real.pi) /
        rZeroHeight z.1) := by
  rw [(towerMotionOf z).incidence_eq, (towerMotionOf z).logIncidence_eq]

theorem towerMotion_incidence_positive (z : TrueZero) (k : ℤ) :
    0 < (towerMotionOf z).incidence k := by
  rw [(towerMotionOf z).incidence_eq]
  exact Real.exp_pos _

theorem towerMotion_consecutive_width (z : TrueZero) (k : ℤ) :
    Real.log ((towerMotionOf z).incidence (k + 1)) -
        Real.log ((towerMotionOf z).incidence k) =
      Real.pi / rZeroHeight z.1 := by
  rw [(towerMotionOf z).incidence_eq, (towerMotionOf z).incidence_eq,
    Real.log_exp, Real.log_exp, (towerMotionOf z).logIncidence_eq,
    (towerMotionOf z).logIncidence_eq]
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  push_cast
  field_simp
  ring

theorem towerMotion_incidence_strictOrder
    (z : TrueZero) {k l : ℤ} (hkl : k < l) :
    (towerMotionOf z).incidence k < (towerMotionOf z).incidence l := by
  change rTowerIncidence z k < rTowerIncidence z l
  exact thm_rTowerIncidence_strictOrder z hkl

theorem towerMotion_ringJump_logWidth (z : TrueZero) (k₀ k₁ : ℤ) :
    (towerMotionOf z).logIncidence k₁ - (towerMotionOf z).logIncidence k₀ =
      (k₁ - k₀ : ℝ) * (Real.pi / rZeroHeight z.1) := by
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  rw [(towerMotionOf z).logIncidence_eq, (towerMotionOf z).logIncidence_eq]
  field_simp
  ring

end RHV6Fresh
