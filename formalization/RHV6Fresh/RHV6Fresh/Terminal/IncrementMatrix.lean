/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TransmissionIncrements
import RHV6Fresh.Terminal.WindowComparison

/-!
# Matrice collective des incréments et ses deux télescopages (auteur, 2026-10-11 ; E199)

Sur une suite de coupures `x_0 < … < x_K` (événements premiers, contacts) et une famille finie de contributions `g_i`
(historique consommé, membres du groupe, complément), la matrice `A_{i,r} = g_i(x_{r+1}) − g_i(x_r)` a deux sommes
marginales : par ligne, l'incrément de la contribution sur toute la fenêtre ; par colonne, l'incrément de la somme. Leur
composition est le même total. Instance : `R = P_H + fibre]H, H'] + Q_{H'}` (`transmission_increment_split`).

Indices de compensation : `|Σ_i A_{i,r}| ≤ Σ_i |A_{i,r}|` (colonne), `|Σ_r A_{i,r}| ≤ Σ_r |A_{i,r}|` (ligne), et la
chaîne `|ΔR_total| ≤ Σ_r |ΔR_r| ≤ Σ_r Σ_i |A_{i,r}|`. Ce sont des inégalités triangulaires : elles mesurent la
compensation, elles ne la bornent pas par en dessous. Aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean

/-- Matrice des incréments : contribution `i`, intervalle de coupure `r`. -/
def incrementMatrix {ι : Type*} (g : ι → ℝ → ℂ) (x : ℕ → ℝ) (i : ι) (r : ℕ) : ℂ :=
  g i (x (r + 1)) - g i (x r)

/-- **Télescopage par ligne** : `Σ_{r<K} A_{i,r} = g_i(x_K) − g_i(x_0)`. -/
theorem incrementMatrix_row_sum {ι : Type*} (g : ι → ℝ → ℂ) (x : ℕ → ℝ) (i : ι) (K : ℕ) :
    ∑ r ∈ Finset.range K, incrementMatrix g x i r = g i (x K) - g i (x 0) :=
  Finset.sum_range_sub (fun r => g i (x r)) K

/-- **Somme par colonne** : `Σ_i A_{i,r} = G(x_{r+1}) − G(x_r)`, `G = Σ_i g_i`. -/
theorem incrementMatrix_col_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ) (x : ℕ → ℝ) (r : ℕ) :
    ∑ i ∈ s, incrementMatrix g x i r = (∑ i ∈ s, g i (x (r + 1))) - ∑ i ∈ s, g i (x r) := by
  unfold incrementMatrix; rw [Finset.sum_sub_distrib]

/-- **Composition des deux télescopages** : le total de la matrice vaut l'incrément de la somme sur toute la fenêtre,
lu par lignes ou par colonnes. -/
theorem incrementMatrix_total {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ) (x : ℕ → ℝ) (K : ℕ) :
    ∑ r ∈ Finset.range K, ∑ i ∈ s, incrementMatrix g x i r =
        (∑ i ∈ s, g i (x K)) - ∑ i ∈ s, g i (x 0) ∧
      ∑ i ∈ s, ∑ r ∈ Finset.range K, incrementMatrix g x i r =
        (∑ i ∈ s, g i (x K)) - ∑ i ∈ s, g i (x 0) := by
  refine ⟨?_, ?_⟩
  · simp_rw [incrementMatrix_col_sum]
    exact Finset.sum_range_sub (fun r => ∑ i ∈ s, g i (x r)) K
  · simp_rw [incrementMatrix_row_sum]; rw [Finset.sum_sub_distrib]

/-- **Colonnes = incréments du reste** dès que la famille reconstruit le reste aux coupures. -/
theorem incrementMatrix_col_eq_remainder {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ) (x : ℕ → ℝ)
    (R : ℝ → ℂ) (hR : ∀ r, R (x r) = ∑ i ∈ s, g i (x r)) (r : ℕ) :
    ∑ i ∈ s, incrementMatrix g x i r = R (x (r + 1)) - R (x r) := by
  rw [incrementMatrix_col_sum, hR, hR]

/-- **Indices de compensation (inégalités triangulaires)** : colonne, ligne, et chaîne totale. -/
theorem incrementMatrix_compensation {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ) (x : ℕ → ℝ) (K : ℕ) :
    (∀ r, ‖∑ i ∈ s, incrementMatrix g x i r‖ ≤ ∑ i ∈ s, ‖incrementMatrix g x i r‖) ∧
    (∀ i, ‖∑ r ∈ Finset.range K, incrementMatrix g x i r‖ ≤ ∑ r ∈ Finset.range K, ‖incrementMatrix g x i r‖) ∧
    ‖(∑ i ∈ s, g i (x K)) - ∑ i ∈ s, g i (x 0)‖ ≤
      ∑ r ∈ Finset.range K, ‖∑ i ∈ s, incrementMatrix g x i r‖ ∧
    ∑ r ∈ Finset.range K, ‖∑ i ∈ s, incrementMatrix g x i r‖ ≤
      ∑ r ∈ Finset.range K, ∑ i ∈ s, ‖incrementMatrix g x i r‖ := by
  refine ⟨fun r => norm_sum_le _ _, fun i => norm_sum_le _ _, ?_, ?_⟩
  · rw [← (incrementMatrix_total s g x K).1]; exact norm_sum_le _ _
  · exact Finset.sum_le_sum fun r _ => norm_sum_le _ _

/-- Les trois lignes de la transmission `T_e → T_l` : historique consommé, groupe suivant, complément. -/
noncomputable def transmissionRows (He Hl : ℝ) : Fin 3 → ℝ → ℂ
  | 0 => precedingSum He
  | 1 => nextFiberSum He Hl
  | 2 => followingSum Hl

/-- **Instance de la transmission** : sur toute suite de coupures `> 1`, les colonnes de la matrice à trois lignes sont
exactement les incréments du reste lissé, et le total est `R(x_K) − R(x_0)`. -/
theorem transmission_matrix (He Hl : ℝ) (x : ℕ → ℝ) (hx : ∀ r, 1 < x r) (K : ℕ) :
    (∀ r, ∑ i, incrementMatrix (transmissionRows He Hl) x i r = smoothedRemainder (x (r + 1)) - smoothedRemainder (x r)) ∧
    ∑ r ∈ Finset.range K, ∑ i, incrementMatrix (transmissionRows He Hl) x i r =
      smoothedRemainder (x K) - smoothedRemainder (x 0) := by
  have hR : ∀ r, smoothedRemainder (x r) = ∑ i, transmissionRows He Hl i (x r) := by
    intro r
    rw [Fin.sum_univ_three, remainder_eq_preceding_add_following Hl (hx r)]
    simp only [transmissionRows, nextFiberSum]; ring
  refine ⟨fun r => incrementMatrix_col_eq_remainder _ _ x _ hR r, ?_⟩
  rw [(incrementMatrix_total Finset.univ _ x K).1, ← hR, ← hR]

end RHV6Fresh
