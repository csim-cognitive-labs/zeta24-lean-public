/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaZeroMultiplicity

/-!
# Tour 23-B — itération 3A : troncature par hauteur et réflexion fonctionnelle

Cette étape construit une troncature finie exacte des zéros dans la bande
`0 ≤ re ρ ≤ 1`, `|im ρ| ≤ T`, puis prouve la fermeture sous `ρ ↦ 1 - ρ`
pour les zéros strictement intérieurs. Elle ne revendique ni formule de
Perron, ni convergence infinie, ni conservation de multiplicité sous
symétrie, ni RH.

Dossier mathématique préalable :
`validation/p4_autoresearch_prime/rh_resolution_progression/`
`stage34_round23b_iteration3a_math_dossier.md`.
-/

open Set Filter Finset BigOperators
open scoped Topology

namespace RHV3Lean

/-- Zéros de ζ dans la bande fermée `0 ≤ re ≤ 1`, tronqués par hauteur.

Le filtre part du `Finset` radial de rayon `1 + |T|`. Pour `T ≥ 0`, cette
enveloppe est exacte, car `‖ρ‖ ≤ |re ρ| + |im ρ| ≤ 1 + T`. -/
noncomputable def criticalStripHeightZerosFinset (T : ℝ) : Finset ℂ := by
  classical
  exact (zetaZerosFinset (1 + |T|)).filter fun ρ ↦
    0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T

/-- Caractérisation brute, incluant explicitement l'enveloppe radiale. -/
@[simp] theorem mem_criticalStripHeightZerosFinset_raw {T : ℝ} {ρ : ℂ} :
    ρ ∈ criticalStripHeightZerosFinset T ↔
      ρ ∈ Metric.closedBall (0 : ℂ) (1 + |T|) ∧
      riemannZeta ρ = 0 ∧
      0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T := by
  classical
  simp [criticalStripHeightZerosFinset, mem_zetaZerosFinset, and_assoc]

/-- Pour `T ≥ 0`, le `Finset` radial filtré est exactement la troncature
par hauteur dans la bande critique fermée. -/
theorem mem_criticalStripHeightZerosFinset_iff {T : ℝ} (hT : 0 ≤ T) {ρ : ℂ} :
    ρ ∈ criticalStripHeightZerosFinset T ↔
      riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T := by
  constructor
  · intro hρ
    rcases mem_criticalStripHeightZerosFinset_raw.mp hρ with
      ⟨_, hzero, hre0, hre1, him⟩
    exact ⟨hzero, hre0, hre1, him⟩
  · rintro ⟨hzero, hre0, hre1, him⟩
    have hnorm : ‖ρ‖ ≤ 1 + |T| := by
      calc
        ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
        _ = ρ.re + |ρ.im| := by rw [abs_of_nonneg hre0]
        _ ≤ 1 + T := add_le_add hre1 him
        _ = 1 + |T| := by rw [abs_of_nonneg hT]
    have hball : ρ ∈ Metric.closedBall (0 : ℂ) (1 + |T|) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
    exact mem_criticalStripHeightZerosFinset_raw.mpr
      ⟨hball, hzero, hre0, hre1, him⟩

/-- Les troncatures exactes sont monotones en hauteur. -/
theorem criticalStripHeightZerosFinset_mono {T S : ℝ}
    (hT : 0 ≤ T) (hTS : T ≤ S) :
    criticalStripHeightZerosFinset T ⊆ criticalStripHeightZerosFinset S := by
  have hS : 0 ≤ S := hT.trans hTS
  intro ρ hρ
  rcases (mem_criticalStripHeightZerosFinset_iff hT).mp hρ with
    ⟨hzero, hre0, hre1, him⟩
  exact (mem_criticalStripHeightZerosFinset_iff hS).mpr
    ⟨hzero, hre0, hre1, him.trans hTS⟩

/-- Réflexion imposée par l'équation fonctionnelle. -/
def zetaReflect (ρ : ℂ) : ℂ := 1 - ρ

@[simp] theorem zetaReflect_re (ρ : ℂ) : (zetaReflect ρ).re = 1 - ρ.re := by
  simp [zetaReflect]

@[simp] theorem zetaReflect_im (ρ : ℂ) : (zetaReflect ρ).im = -ρ.im := by
  simp [zetaReflect]

@[simp] theorem zetaReflect_involutive (ρ : ℂ) : zetaReflect (zetaReflect ρ) = ρ := by
  simp [zetaReflect]

@[simp] theorem abs_zetaReflect_im (ρ : ℂ) : |(zetaReflect ρ).im| = |ρ.im| := by
  simp [zetaReflect]

/-- Un point de partie réelle strictement positive n'est aucun entier naturel
négatif, condition requise par `riemannZeta_one_sub`. -/
theorem ne_neg_nat_of_re_pos {ρ : ℂ} (hre : 0 < ρ.re) (n : ℕ) :
    ρ ≠ -(n : ℂ) := by
  intro h
  have hre_eq := congrArg Complex.re h
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  simp at hre_eq
  linarith

/-- La formule fonctionnelle transporte tout zéro de partie réelle positive
vers le zéro réfléchi `1 - ρ`. -/
theorem riemannZeta_zetaReflect_eq_zero {ρ : ℂ}
    (hzero : riemannZeta ρ = 0) (hre : 0 < ρ.re) :
    riemannZeta (zetaReflect ρ) = 0 := by
  have hne1 : ρ ≠ 1 := zetaZero_ne_one hzero
  rw [zetaReflect,
    riemannZeta_one_sub (s := ρ) (fun n ↦ ne_neg_nat_of_re_pos hre n) hne1,
    hzero]
  simp

/-- La réflexion conserve exactement la troncature de hauteur et la bande,
pour un zéro strictement intérieur. -/
theorem zetaReflect_mem_criticalStripHeightZerosFinset {T : ℝ} {ρ : ℂ}
    (hT : 0 ≤ T)
    (hρ : ρ ∈ criticalStripHeightZerosFinset T)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) :
    zetaReflect ρ ∈ criticalStripHeightZerosFinset T := by
  rcases (mem_criticalStripHeightZerosFinset_iff hT).mp hρ with
    ⟨hzero, _, _, him⟩
  apply (mem_criticalStripHeightZerosFinset_iff hT).mpr
  refine ⟨riemannZeta_zetaReflect_eq_zero hzero hre0, ?_, ?_, ?_⟩
  · simp [zetaReflect]
    linarith
  · simp [zetaReflect]
    linarith
  · simpa using him

/-- Somme spectrale finie par hauteur, pondérée par la multiplicité analytique
prouvée au Tour 23-B/2. -/
noncomputable def criticalStripHeightZeroSum (T : ℝ) (F : ℂ → ℂ) : ℂ :=
  ∑ ρ ∈ criticalStripHeightZerosFinset T,
    (zetaZeroMultiplicity ρ : ℂ) * F ρ

/-- Linéarité exacte de la somme spectrale finie par hauteur. -/
theorem criticalStripHeightZeroSum_add (T : ℝ) (F G : ℂ → ℂ) :
    criticalStripHeightZeroSum T (fun ρ ↦ F ρ + G ρ)
      = criticalStripHeightZeroSum T F + criticalStripHeightZeroSum T G := by
  unfold criticalStripHeightZeroSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

@[simp] theorem criticalStripHeightZeroSum_zero (T : ℝ) :
    criticalStripHeightZeroSum T (fun _ ↦ 0) = 0 := by
  simp [criticalStripHeightZeroSum]

end RHV3Lean

/-! ## Audit d'axiomes — Tour 23-B, itération 3A -/

#print axioms RHV3Lean.mem_criticalStripHeightZerosFinset_raw
#print axioms RHV3Lean.mem_criticalStripHeightZerosFinset_iff
#print axioms RHV3Lean.criticalStripHeightZerosFinset_mono
#print axioms RHV3Lean.ne_neg_nat_of_re_pos
#print axioms RHV3Lean.riemannZeta_zetaReflect_eq_zero
#print axioms RHV3Lean.zetaReflect_mem_criticalStripHeightZerosFinset
#print axioms RHV3Lean.criticalStripHeightZeroSum_add
#print axioms RHV3Lean.criticalStripHeightZeroSum_zero
