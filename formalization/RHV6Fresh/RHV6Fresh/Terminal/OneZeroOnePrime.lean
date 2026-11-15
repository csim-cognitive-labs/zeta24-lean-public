/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PointedPrimeComparison
import RHV6Fresh.Terminal.GeometricEnergyRaccord

/-!
# RHV6Fresh — « un zéro = un premier » : étiquette de rang, pas géométrie de la Tour (auteur, 2026-10-01)

Question de l'auteur : l'assertion « un zéro = un premier » semble fausse ; vérifier.

* **Ce que dit le code** (§1) : le premier attaché à un membre est le premier de rang « nombre de
  membres de la moitié supérieure strictement en dessous » (`occurrence_is_rank_label`) ; l'étiquette
  est injective (`expectedMinimumPrime_injective`). C'est un comptage, pas une lecture de la Tour.
* **Ce que fait la Tour** (§2) : tout premier, et plus généralement tout réel positif, a une cellule
  dans la Tour de tout membre (`every_prime_in_every_tower`) ; la Tour ne sélectionne aucun premier.
* **Le mouvement radial est une translation de toute la grille** (§3) : l'écart entre la position
  d'un réel dans la Tour et sa position dans la Tour de ligne à la même hauteur est le même pour tout
  réel (`tower_offset_rigid`) ; il est nul en un point quelconque ⟺ il est nul partout ⟺ le membre
  est en ligne (`onLine_iff_entry_at_point`, `onLine_iff_no_grid_translation`).
* **Conséquence pour la flèche** (§4) : la flèche de `EntryPositionArrow` ne dépend pas du premier
  partagé ; énoncée en n'importe quel point choisi par membre, elle est la même loi
  (`entry_arrow_point_irrelevant`), à savoir « la Tour d'arrivée n'est pas translatée ».

Borne : réécriture exacte ; le verrou est inchangé (l'absence de translation à l'arrivée n'est pas
dérivée). Aucune prémisse, aucun `sorry`, aucun axiome.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Le premier d'un membre est une étiquette de rang -/

/-- **Le premier attaché à un membre est le premier de rang « nombre de membres en dessous ».** -/
theorem occurrence_is_rank_label (z : TrueZero) :
    occurrence z = Nat.nth Nat.Prime (thm_upperZerosBelow_finite z.1).toFinset.card := by
  rw [occurrence_eq_primeAtRank]
  rfl

/-! ## 2. La Tour contient tous les premiers -/

/-- **Tout premier a sa cellule dans la Tour de tout membre.** -/
theorem every_prime_in_every_tower (z : TrueZero) (p : ℕ) (hp : Nat.Prime p) :
    contactMinusAt z (pivotCoordinate z (p : ℝ)) < (p : ℝ) ∧
      (p : ℝ) ≤ contactPlusAt z (pivotCoordinate z (p : ℝ)) :=
  prime_raccord_has_unique_tower_cell z (by exact_mod_cast hp.pos)

/-! ## 3. Le mouvement radial translate toute la grille -/

/-- **L'écart à la Tour de ligne est le même pour tout réel.** -/
theorem tower_offset_rigid (z : TrueZero) (q q' : ℝ) :
    towerPosition z q - linePosition (rZeroHeight z.1) q =
      towerPosition z q' - linePosition (rZeroHeight z.1) q' := by
  rw [towerPosition_eq_line_add_residue z q, towerPosition_eq_line_add_residue z q']
  ring

/-- **En ligne ⟺ un réel quelconque est à sa position de ligne.** -/
theorem onLine_iff_entry_at_point (z : TrueZero) (q : ℝ) :
    rZeroRadialPosition z.1 = 1 / 2 ↔
      towerPosition z q = linePosition (rZeroHeight z.1) q := by
  rw [towerPosition_eq_line_add_residue z q, ← changeResidue_eq_zero_iff z.1]
  constructor
  · intro h
    rw [h, zero_div, add_zero]
  · intro h
    have h0 : changeResidue z.1 / Real.pi = 0 := by linarith
    rcases div_eq_zero_iff.mp h0 with h1 | h1
    · exact h1
    · exact absurd h1 Real.pi_pos.ne'

/-- **En ligne ⟺ aucune translation de la grille.** -/
theorem onLine_iff_no_grid_translation (z : TrueZero) :
    rZeroRadialPosition z.1 = 1 / 2 ↔
      ∀ q : ℝ, towerPosition z q = linePosition (rZeroHeight z.1) q :=
  ⟨fun h q => (onLine_iff_entry_at_point z q).mp h,
    fun h => (onLine_iff_entry_at_point z 1).mpr (h 1)⟩

/-! ## 4. La flèche ne dépend pas du premier partagé -/

/-- **La flèche énoncée au premier partagé est la flèche énoncée en n'importe quel point.** -/
theorem entry_arrow_point_irrelevant (f : TrueZero → ℝ) :
    (∀ (p : TZeroPassage) (_hE : 0 < rZeroHeight p.zEarlierMember)
        (hL : 0 < rZeroHeight p.zLaterMember),
        rZeroRadialPosition p.zEarlierMember = 1 / 2 →
          towerPosition ⟨p.zLaterMember, hL⟩ (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) =
            linePosition (rZeroHeight p.zLaterMember) (occurrence ⟨p.zLaterMember, hL⟩ : ℝ)) ↔
      (∀ (p : TZeroPassage) (_hE : 0 < rZeroHeight p.zEarlierMember)
        (hL : 0 < rZeroHeight p.zLaterMember),
        rZeroRadialPosition p.zEarlierMember = 1 / 2 →
          towerPosition ⟨p.zLaterMember, hL⟩ (f ⟨p.zLaterMember, hL⟩) =
            linePosition (rZeroHeight p.zLaterMember) (f ⟨p.zLaterMember, hL⟩)) := by
  constructor
  · intro h p hE hL hOn
    exact (onLine_iff_entry_at_point _ _).mp
      ((onLine_iff_entry_at_point _ _).mpr (h p hE hL hOn))
  · intro h p hE hL hOn
    exact (onLine_iff_entry_at_point _ _).mp
      ((onLine_iff_entry_at_point _ _).mpr (h p hE hL hOn))

#print axioms occurrence_is_rank_label
#print axioms every_prime_in_every_tower
#print axioms tower_offset_rigid
#print axioms onLine_iff_entry_at_point
#print axioms onLine_iff_no_grid_translation
#print axioms entry_arrow_point_irrelevant

end RHV6Fresh
