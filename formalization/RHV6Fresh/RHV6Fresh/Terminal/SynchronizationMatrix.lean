/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.LocalPrimeGapSynchronization
import RHV6Fresh.Terminal.ConstantAmplitudeNeed
import RHV6Fresh.Terminal.GeneratedFrequency

/-!
# La matrice de synchronisation : lignes = intervalles arithmétiques, colonnes = fréquences engendrées (E323, 2026-10-16)

Texte de l'auteur (2026-10-16) : « construire une matrice dont les lignes sont les intervalles arithmétiques et les colonnes les
composantes fréquentielles ; chaque cellule contient simultanément la phase, le nombre de rencontres, le déplacement de la
composante et sa variation d'amplitude sur l'intervalle ; la somme de chaque ligne doit reproduire exactement la variation
négative du fond et des corrections ; rechercher une contrainte de compatibilité globale : les mêmes paramètres `(T, β, φ)`
doivent satisfaire toutes les lignes, sans réajustement d'un intervalle au suivant ; déterminer si cette matrice possède une
rigidité suffisante pour interdire une variation d'amplitude, sans supposer cette interdiction. »

Ce module écrit la matrice sur le canal démontré (reste lissé des premiers `smoothedRemainder`, représentation exacte
`smoothedRemainder_eq_tsum_residueTerm`) ; le canal de comptage `J` de l'expérience E323 n'est pas formalisé.

* **Cellule** `matrixCell ρ a b` : incrément du signal du vrai zéro `ρ` sur la ligne `[a, b]` (`matrixCell_eq_gapTerm` : c'est
  `(−m/(ρ+1))·∫ x^{ρ−1} dx`, toute position radiale).
* **Identité de ligne** (`row_identity`) : sur toute ligne `1 < a < b`, la variation du reste des premiers est la somme de toutes
  les cellules de la ligne ; la ligne tronquée à une famille finie de colonnes laisse exactement la queue (`row_residual_eq_tail`).
  La matrice finie ne ferme aucune ligne : E323 mesure un résidu de ligne de 99,6 % avec vingt colonnes et 83 % avec les cinq
  mille premiers zéros publiés.
* **Continuité des colonnes** (`residueTerm_continuousOn`, `finite_columns_continuousOn`) : toute cellule, toute somme finie de
  cellules est continue en la borne ; aucun saut n'est porté par un nombre fini de colonnes (sur le canal de comptage, le saut
  `1/m` du comptage est porté par la limite seule, E323 M1).
* **Réajustement entre blocs** (`block_readjustment_log`) : pour une colonne, le réajustement d'amplitude (échelle de la ligne)
  exigé entre deux abscisses `x < y` vaut `(β − 1/2)·(log y − log x)` : identité, toute position radiale ; il s'inverse
  (`radial_from_two_blocks`) ; **aucun réajustement entre deux blocs quelconques ⟺ colonne sur la ligne**
  (`no_block_readjustment_iff`, c'est le besoin constant de `Terminal/ConstantAmplitudeNeed.lean`).
* **Portée** (`matrix_compatibility_law_iff_riemannHypothesis`) : la compatibilité globale demandée, « aucune colonne ne réajuste
  son amplitude d'un bloc au suivant », quantifiée sur toutes les colonnes, ⟺ RH. La rigidité suffisante que le texte cherche est
  donc exactement la loi à démontrer ; la matrice la formule, elle ne la fournit pas. Mesuré (E323, premiers seuls, `X = 10⁸`,
  vingt colonnes, cinq blocs de décade) : réajustement nul au bruit près à toutes les colonnes, pente nulle (contrôle de ligne
  identique), témoin `ζ(s−δ)ζ(s+δ)` refusé (pente `≈ δ`). Rien n'est dérivé ici au-delà des identités.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Cellules et identité de ligne (canal lissé, démontré) -/

/-- **Cellule de la matrice** : incrément du signal lissé du vrai zéro `ρ` sur la ligne `[a, b]`. -/
noncomputable def matrixCell (ρ : ExplicitIndex) (a b : ℝ) : ℂ :=
  nontrivialZeroResidueTerm b ρ - nontrivialZeroResidueTerm a ρ

/-- La cellule est la contribution exacte `(−m/(ρ+1))·∫_a^b x^{ρ−1} dx`, pour toute position radiale. -/
theorem matrixCell_eq_gapTerm (ρ : ExplicitIndex) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    matrixCell ρ a b =
      (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) + 1)) * gapTerm ρ (Real.log a) (Real.log b) :=
  residueTerm_gap_eq ρ ha hb

theorem matrixCell_summable {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    Summable (fun ρ : ExplicitIndex => matrixCell ρ a b) :=
  (nontrivial_zero_residue_series_summable hb).sub (nontrivial_zero_residue_series_summable ha)

/-- **Identité de ligne** : la variation du reste des premiers sur la ligne `[a, b]` est la somme de toutes les cellules de la
ligne (tous les vrais zéros, convergence absolue). -/
theorem row_identity {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    smoothedRemainder b - smoothedRemainder a = ∑' ρ : ExplicitIndex, matrixCell ρ a b := by
  rw [smoothedRemainder_eq_tsum_residueTerm hb, smoothedRemainder_eq_tsum_residueTerm ha,
    ← (nontrivial_zero_residue_series_summable hb).tsum_sub (nontrivial_zero_residue_series_summable ha)]
  rfl

/-- **La ligne tronquée laisse la queue** : la somme d'une famille finie de colonnes ne ferme jamais une ligne, le résidu est
la somme des colonnes omises. -/
theorem row_residual_eq_tail (s : Finset ExplicitIndex) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    smoothedRemainder b - smoothedRemainder a - ∑ ρ ∈ s, matrixCell ρ a b =
      ∑' ρ : ((s : Set ExplicitIndex)ᶜ : Set ExplicitIndex), matrixCell ρ.1 a b := by
  rw [row_identity ha hb, ← (matrixCell_summable ha hb).sum_add_tsum_compl (s := s)]
  ring

/-! ## 2. Continuité : aucune colonne, aucune somme finie de colonnes ne porte un saut -/

theorem residueTerm_continuousOn (ρ : ExplicitIndex) :
    ContinuousOn (fun x : ℝ => nontrivialZeroResidueTerm x ρ) (Set.Ioi 0) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  unfold nontrivialZeroResidueTerm Perron.f
  apply ContinuousAt.mul continuousAt_const
  apply ContinuousAt.div_const
  exact Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (ne_of_gt (Set.mem_Ioi.mp hx)))

/-- Toute somme finie de cellules est continue en la borne supérieure de la ligne. -/
theorem finite_columns_continuousOn (s : Finset ExplicitIndex) (a : ℝ) :
    ContinuousOn (fun b : ℝ => ∑ ρ ∈ s, matrixCell ρ a b) (Set.Ioi 0) := by
  unfold matrixCell
  apply continuousOn_finsetSum
  intro ρ _
  exact (residueTerm_continuousOn ρ).sub continuousOn_const

/-! ## 3. Réajustement d'une colonne entre deux blocs -/

/-- **Réajustement d'amplitude entre deux abscisses** : à l'échelle de la ligne, le logarithme du rapport des amplitudes d'une
colonne entre `x` et `y` vaut `(β − 1/2)·(log y − log x)`. Identité, toute position radiale. -/
theorem block_readjustment_log (z : TrueZero) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (pairAmplitude z y / pairAmplitude z x) =
      (rZeroRadialPosition z.1 - 1 / 2) * (Real.log y - Real.log x) := by
  rw [pairAmplitude_eq z hy, pairAmplitude_eq z hx]
  set e := rZeroRadialPosition z.1 - 1 / 2 with he
  have hs : 0 < Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) := by
    apply Real.sqrt_pos.mpr
    have := z.2
    positivity
  have hxe := Real.rpow_pos_of_pos hx e
  have hye := Real.rpow_pos_of_pos hy e
  have hq : 2 * y ^ e / Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) /
      (2 * x ^ e / Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2)) = y ^ e / x ^ e := by
    field_simp
  rw [hq, Real.log_div hye.ne' hxe.ne', Real.log_rpow hy, Real.log_rpow hx]
  ring

/-- **Inversion à deux blocs** : deux abscisses distinctes restituent la position radiale depuis le réajustement. -/
theorem radial_from_two_blocks (z : TrueZero) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    rZeroRadialPosition z.1 =
      1 / 2 + Real.log (pairAmplitude z y / pairAmplitude z x) / (Real.log y - Real.log x) := by
  rw [block_readjustment_log z hx hy]
  have hne : Real.log y - Real.log x ≠ 0 := by
    intro h
    exact hxy (Real.log_injOn_pos (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr hx) (sub_eq_zero.mp h)).symm
  field_simp
  ring

/-- **Aucun réajustement entre blocs ⟺ colonne sur la ligne** : la compatibilité globale d'une colonne (même amplitude à
l'échelle de la ligne sur tous les blocs `x, y ≥ 1`) caractérise la position radiale un demi. -/
theorem no_block_readjustment_iff (z : TrueZero) :
    (∀ x y : ℝ, 1 ≤ x → 1 ≤ y → Real.log (pairAmplitude z y / pairAmplitude z x) = 0) ↔
      rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro h
    have h12 := h 1 2 le_rfl (by norm_num)
    rw [block_readjustment_log z one_pos two_pos, Real.log_one, sub_zero] at h12
    rcases mul_eq_zero.mp h12 with h1 | h2
    · linarith
    · exact absurd h2 (Real.log_pos one_lt_two).ne'
  · intro h x y hx hy
    rw [block_readjustment_log z (by linarith) (by linarith), h]
    ring

/-! ## 4. Portée : la compatibilité globale sur toutes les colonnes a la force de RH -/

/-- **La rigidité cherchée est la loi à démontrer** : « aucune colonne ne réajuste son amplitude d'un bloc au suivant »,
quantifiée sur toutes les colonnes, ⟺ RH. -/
theorem matrix_compatibility_law_iff_riemannHypothesis :
    (∀ z : TrueZero, ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → Real.log (pairAmplitude z y / pairAmplitude z x) = 0) ↔
      RiemannHypothesis := by
  rw [← constantNeed_law_iff_riemannHypothesis]
  constructor
  · intro h z
    exact constantNeed_of_onLine z ((no_block_readjustment_iff z).mp (h z))
  · intro h z
    exact (no_block_readjustment_iff z).mpr (onLine_of_constantNeed z (h z))


/-- **La cellule de la matrice est l'entrée conjointe du §12 de `GeneratedFrequency`** : phase et enveloppe aux deux bornes
(fréquence, calage des rencontres lissées, amplitude), aucune duplication. -/
theorem matrixCell_eq_gap_entry (ρ : ExplicitIndex) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    matrixCell ρ a b =
      -((gapEnvelope ρ b : ℂ) * Complex.exp ((gapPhase ρ b : ℂ) * Complex.I)) +
        (gapEnvelope ρ a : ℂ) * Complex.exp ((gapPhase ρ a : ℂ) * Complex.I) :=
  gap_entry_joint ρ ha hb

#print axioms matrixCell_eq_gap_entry

end RHV6Fresh
