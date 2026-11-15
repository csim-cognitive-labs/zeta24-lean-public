/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.OneZeroOnePrime
import RHV6Fresh.Terminal.RegimeTower
import RHV6Fresh.Terminal.DiagonalPassage
import RHV6Fresh.Terminal.SuccessionInvariants

/-!
# RHV6Fresh — la Tour est une grille infinie : forme normale, régime de ligne, régime concurrent (auteur, 2026-10-01)

Audit d'impact de `OneZeroOnePrime` : la Tour est unique par zéro, mais ses cellules sont en nombre
infini et contiennent tous les premiers. Ce fichier écrit ce qui en résulte pour le régime.

* **Forme normale** (§1) : toute Tour est la Tour de ligne à sa hauteur, de pas `π/T`, translatée de
  `D/π` cellule, la même translation pour tout réel (`tower_grid_normal_form`).
* **Régime de ligne, caractérisé** (§2) : en ligne, la grille est une fonction de la hauteur seule ;
  deux membres en ligne ont la même grille ⟺ même hauteur (`onLine_grid_eq_iff_height_eq`).
* **Régime concurrent, détecté en tout point** (§3) : un membre hors ligne se lit en n'importe quel
  réel (`competing_regime_at_any_point`) ; un passage se découpe en part de pas (hauteur) et part de
  translation (`passage_grid_decomposition`) ; depuis l'état engagé, la part de translation est
  `D_l/π` (`engaged_passage_translation`).
* **Deux lectures sans point privilégié** (§4) : le transport `‖q^{ρ_l}/ρ_l‖/‖q^{ρ_e}/ρ_e‖` est le
  même en tout `q` ⟺ même position radiale (`energyRatio_flat_iff`) ; le module du terme d'Euler
  d'un entier `n > 1` au membre vaut `n^{−1/2}` ⟺ en ligne, quel que soit `n`
  (`local_euler_modulus_point_irrelevant`).

Borne : ce sont des caractérisations ; elles lisent la translation, elles ne l'interdisent pas.
Aucune prémisse, aucun `sorry`, aucun axiome.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Forme normale de toute Tour -/

/-- **Toute Tour = Tour de ligne à sa hauteur, translatée.** Contacts : contacts de ligne × facteur
radial unique ; pas `π/T` ; position de tout réel : position de ligne + `D/π`. -/
theorem tower_grid_normal_form (z : TrueZero) :
    (∀ k : ℤ, contactMinusAt z k = lineContact (rZeroHeight z.1) k * radialFactor z) ∧
      towerPitch z = Real.pi / rZeroHeight z.1 ∧
      ∀ q : ℝ, towerPosition z q = linePosition (rZeroHeight z.1) q + changeResidue z.1 / Real.pi :=
  ⟨contact_eq_line_mul_radial z, rfl, towerPosition_eq_line_add_residue z⟩

/-! ## 2. Le régime de ligne : une grille par hauteur -/

/-- En ligne, la position de tout réel est la position de ligne à la hauteur du membre. -/
theorem onLine_grid_height_only (z : TrueZero) (hz : rZeroRadialPosition z.1 = 1 / 2) (q : ℝ) :
    towerPosition z q = linePosition (rZeroHeight z.1) q :=
  (onLine_iff_no_grid_translation z).mp hz q

/-- **Deux membres en ligne ont la même grille ⟺ ils ont la même hauteur.** -/
theorem onLine_grid_eq_iff_height_eq (z w : TrueZero)
    (hz : rZeroRadialPosition z.1 = 1 / 2) (hw : rZeroRadialPosition w.1 = 1 / 2) :
    (∀ q : ℝ, towerPosition z q = towerPosition w q) ↔ rZeroHeight z.1 = rZeroHeight w.1 := by
  constructor
  · intro h
    have h1 := h 1
    have he := h (Real.exp 1)
    rw [onLine_grid_height_only z hz, onLine_grid_height_only w hw] at h1 he
    unfold linePosition at h1 he
    rw [Real.log_one] at h1
    rw [Real.log_exp] at he
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp at h1 he
    linarith
  · intro hT q
    rw [onLine_grid_height_only z hz, onLine_grid_height_only w hw, hT]

/-! ## 3. Le régime concurrent : une translation, lisible en tout point -/

/-- **Hors ligne ⟺ un réel quelconque n'est pas à sa position de ligne.** -/
theorem competing_regime_at_any_point (z : TrueZero) (q : ℝ) :
    rZeroRadialPosition z.1 ≠ 1 / 2 ↔
      towerPosition z q ≠ linePosition (rZeroHeight z.1) q :=
  not_congr (onLine_iff_entry_at_point z q)

/-- **Un passage = une part de pas (hauteur) + une part de translation (radiale).** -/
theorem passage_grid_decomposition (e l : TrueZero) (q : ℝ) :
    towerPosition l q - towerPosition e q =
      ((rZeroHeight l.1 - rZeroHeight e.1) * Real.log q -
          (linePhase (rZeroHeight l.1) - linePhase (rZeroHeight e.1))) / Real.pi +
        (changeResidue l.1 - changeResidue e.1) / Real.pi := by
  rw [towerPosition_eq_line_add_residue l q, towerPosition_eq_line_add_residue e q]
  unfold linePosition
  ring

/-- **Depuis l'état engagé, la part de translation d'un passage est `D_l/π`**, la même pour tout réel ;
elle est nulle ⟺ l'arrivée est en ligne. -/
theorem engaged_passage_translation (e l : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2) (q : ℝ) :
    towerPosition l q - towerPosition e q =
        ((rZeroHeight l.1 - rZeroHeight e.1) * Real.log q -
            (linePhase (rZeroHeight l.1) - linePhase (rZeroHeight e.1))) / Real.pi +
          changeResidue l.1 / Real.pi ∧
      (changeResidue l.1 / Real.pi = 0 ↔ rZeroRadialPosition l.1 = 1 / 2) := by
  have hDe : changeResidue e.1 = 0 := (changeResidue_eq_zero_iff e.1).mpr he
  refine ⟨by rw [passage_grid_decomposition e l q, hDe, sub_zero], ?_⟩
  rw [← changeResidue_eq_zero_iff l.1, div_eq_zero_iff]
  exact ⟨fun h => h.resolve_right Real.pi_pos.ne', Or.inl⟩

/-! ## 4. Deux lectures sans point privilégié -/

/-- **Le transport est le même en tout point ⟺ même position radiale.** -/
theorem energyRatio_flat_iff (e l : TrueZero) :
    (∀ q : ℝ, 0 < q → energyRatio e l q = energyRatio e l 1) ↔
      rZeroRadialPosition l.1 = rZeroRadialPosition e.1 := by
  have hc : 0 < ‖zeroPoint e‖ / ‖zeroPoint l‖ := div_pos (zeroPoint_norm_pos e) (zeroPoint_norm_pos l)
  constructor
  · intro h
    have h1 := h (Real.exp 1) (Real.exp_pos 1)
    rw [energyRatio_eq e l (Real.exp_pos 1), energyRatio_eq e l one_pos, Real.one_rpow, one_mul]
      at h1
    have h2 : Real.exp 1 ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) = 1 := by
      have := mul_right_cancel₀ hc.ne' (h1.trans (one_mul _).symm)
      exact this
    have h3 := congrArg Real.log h2
    rw [Real.log_rpow (Real.exp_pos 1), Real.log_exp, mul_one, Real.log_one] at h3
    linarith
  · intro hβ q hq
    rw [energyRatio_eq e l hq, energyRatio_eq e l one_pos, hβ, sub_self, Real.rpow_zero,
      Real.one_rpow]

/-- **Depuis l'état engagé : transport plat ⟺ arrivée en ligne.** -/
theorem engaged_transport_flat_iff_arrival_onLine (e l : TrueZero)
    (he : rZeroRadialPosition e.1 = 1 / 2) :
    (∀ q : ℝ, 0 < q → energyRatio e l q = energyRatio e l 1) ↔
      rZeroRadialPosition l.1 = 1 / 2 := by
  rw [energyRatio_flat_iff, he]

/-- **Le module du terme d'Euler d'un entier `n > 1` au membre vaut `n^{−1/2}` ⟺ en ligne**, quel que
soit `n` : le premier partagé n'y a aucun rôle propre. -/
theorem local_euler_modulus_point_irrelevant (z : TrueZero) (n : ℕ) (hn : 1 < n) :
    ‖(n : ℂ) ^ (-(zeroPoint z))‖ = (n : ℝ) ^ (-(1 / 2 : ℝ)) ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [local_euler_term_norm n (by omega) z]
  constructor
  · intro h
    have := rpow_exponent_injective hn1 h
    linarith
  · intro h
    rw [h]

#print axioms tower_grid_normal_form
#print axioms onLine_grid_height_only
#print axioms onLine_grid_eq_iff_height_eq
#print axioms competing_regime_at_any_point
#print axioms passage_grid_decomposition
#print axioms engaged_passage_translation
#print axioms energyRatio_flat_iff
#print axioms engaged_transport_flat_iff_arrival_onLine
#print axioms local_euler_modulus_point_irrelevant

end RHV6Fresh
