/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.LocalReading
import RHV6Fresh.Terminal.ProgressionDirection

/-!
# RHV6Fresh — le raccord entre deux Tours consécutives (auteur, 2026-09-29)

Objet unique du programme : `TowerRaccord e l`. Il rassemble le premier partagé
`M = p_min(e) = Occ(l)`, la cellule de sortie de `e` qui contient `M`, la cellule d'entrée de `l`
qui contient `M`, l'encadrement énergétique de `M` dans chacune des deux cellules, et le transport
énergétique exact de `e` vers `l` en `M` :
`‖zeroTerm l M‖ / ‖zeroTerm e M‖ = M^{β_l − β_e} · ‖ρ_e‖ / ‖ρ_l‖`.

* **Existence et rigidité** (`towerRaccordOf`, `towerRaccord_eq`) : sur tout passage, le raccord
  existe et il est unique ; aucun champ n'est choisi.
* **Orientation** (`TowerRaccord.Oriented`) : `M^{β_l}/‖ρ_l‖ ≤ M^{β_e}/‖ρ_e‖`, c'est-à-dire
  transport `≤ 1`. Théorème en passage vertical (`towerRaccord_oriented_of_vertical`).
* **Passage horizontal** (`towerRaccord_reverses_of_sameHeight`) : le raccord existe avec tous ses
  champs et le transport est strictement `> 1`.
* **Sous RH** le raccord est orienté sur tout passage (`towerRaccord_oriented_of_riemannHypothesis`).
  L'orientation n'est plus une prémisse (décision de l'auteur, 2026-09-30) : la prémisse unique est
  `PNoRegimeChange` (`Terminal/NoRegimeChange.lean`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **Le raccord entre la Tour `e` et la Tour `l`** au premier partagé `M`. -/
structure TowerRaccord (e l : TrueZero) where
  /-- Le premier partagé. -/
  M : ℕ
  exit_eq : M = expectedMinimumPrime e
  entry_eq : M = occurrence l
  /-- La cellule de sortie de `e` : celle qui contient `M`. -/
  exitCell : ℤ
  exitCell_eq : exitCell = pivotCoordinate e M
  exitCell_contains : contactMinusAt e exitCell < M ∧ (M : ℝ) ≤ contactPlusAt e exitCell
  /-- La cellule d'entrée de `l` : celle qui contient `M`. -/
  entryCell : ℤ
  entryCell_eq : entryCell = pivotCoordinate l M
  entryCell_contains : contactMinusAt l entryCell < M ∧ (M : ℝ) ≤ contactPlusAt l entryCell
  /-- L'énergie de `M` dans la cellule de sortie est encadrée par les contacts de `e`. -/
  exitEnergy : ‖zeroTerm e (contactMinusAt e exitCell)‖ < ‖zeroTerm e M‖ ∧
    ‖zeroTerm e M‖ ≤ ‖zeroTerm e (contactPlusAt e exitCell)‖
  /-- L'énergie de `M` dans la cellule d'entrée est encadrée par les contacts de `l`. -/
  entryEnergy : ‖zeroTerm l (contactMinusAt l entryCell)‖ < ‖zeroTerm l M‖ ∧
    ‖zeroTerm l M‖ ≤ ‖zeroTerm l (contactPlusAt l entryCell)‖
  /-- Le transport énergétique de `e` vers `l` en `M`. -/
  transport : energyRatio e l M =
    (M : ℝ) ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * (‖zeroPoint e‖ / ‖zeroPoint l‖)

/-- **Rigidité** : deux raccords entre les mêmes Tours sont égaux (tous les champs sont fixés). -/
theorem towerRaccord_eq {e l : TrueZero} (R S : TowerRaccord e l) : R = S := by
  obtain ⟨M, hx, _, c, hc, _, d, hd, _, _, _, _⟩ := R
  obtain ⟨M', hx', _, c', hc', _, d', hd', _, _, _, _⟩ := S
  subst hx hx' hc hc' hd hd'
  rfl

/-- Construction du raccord à partir du premier partagé : il suffit que `p_min(e) = Occ(l)`. -/
noncomputable def towerRaccordOfShared (e l : TrueZero)
    (h : occurrence l = expectedMinimumPrime e) : TowerRaccord e l where
  M := expectedMinimumPrime e
  exit_eq := rfl
  entry_eq := h.symm
  exitCell := pivotCoordinate e (expectedMinimumPrime e)
  exitCell_eq := rfl
  exitCell_contains :=
    prime_raccord_has_unique_tower_cell e (by exact_mod_cast expectedMinimumPrime_pos e)
  entryCell := pivotCoordinate l (expectedMinimumPrime e)
  entryCell_eq := rfl
  entryCell_contains :=
    prime_raccord_has_unique_tower_cell l (by exact_mod_cast expectedMinimumPrime_pos e)
  exitEnergy := pivotCell_amplitude_brackets e (by exact_mod_cast expectedMinimumPrime_pos e)
  entryEnergy := pivotCell_amplitude_brackets l (by exact_mod_cast expectedMinimumPrime_pos e)
  transport := energyRatio_eq e l (by exact_mod_cast expectedMinimumPrime_pos e)

/-- **Existence** : sur tout passage, le raccord existe (`passage_direction_rigid` fournit le premier
partagé `Occ(l) = p_min(e)`). -/
noncomputable def towerRaccordOf (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    TowerRaccord ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ :=
  towerRaccordOfShared _ _ (passage_direction_rigid p hE hL).2.2.2.1

/-- **Orientation du raccord** : la Tour `l` ne lit pas plus d'énergie en `M` que la Tour `e`. -/
def TowerRaccord.Oriented {e l : TrueZero} (R : TowerRaccord e l) : Prop :=
  ‖zeroTerm l R.M‖ ≤ ‖zeroTerm e R.M‖

/-- L'orientation est exactement « transport `≤ 1` ». -/
theorem TowerRaccord.oriented_iff_transport_le_one {e l : TrueZero} (R : TowerRaccord e l) :
    R.Oriented ↔
      (R.M : ℝ) ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) *
        (‖zeroPoint e‖ / ‖zeroPoint l‖) ≤ 1 := by
  rw [← R.transport, TowerRaccord.Oriented, energyRatio]
  have hM : (0 : ℝ) < R.M := by rw [R.exit_eq]; exact_mod_cast expectedMinimumPrime_pos e
  have hpos : 0 < ‖zeroTerm e R.M‖ := by
    rw [zeroTerm_norm hM]
    exact div_pos (Real.rpow_pos_of_pos hM _) (zeroPoint_norm_pos e)
  rw [div_le_one hpos]

/-- **Passage vertical** (`β_e = β_l`, `T_e < T_l`) : le raccord est orienté. -/
theorem towerRaccord_oriented_of_vertical {e l : TrueZero} (R : TowerRaccord e l)
    (hβ : rZeroRadialPosition e.1 = rZeroRadialPosition l.1)
    (hT : rZeroHeight e.1 < rZeroHeight l.1) : R.Oriented := by
  have hM : (0 : ℝ) < R.M := by rw [R.exit_eq]; exact_mod_cast expectedMinimumPrime_pos e
  exact (amplitude_lt_of_height_lt e l hβ hT hM).le

/-- **Passage horizontal** (même hauteur `T ≥ 2`, `β_e < β_l`) : le raccord existe avec tous ses
champs, et le transport est strictement renversé. -/
theorem towerRaccord_reverses_of_sameHeight {e l : TrueZero} (R : TowerRaccord e l)
    (hT : rZeroHeight e.1 = rZeroHeight l.1) (hT2 : 2 ≤ rZeroHeight e.1)
    (hβ : rZeroRadialPosition e.1 < rZeroRadialPosition l.1) :
    ‖zeroTerm e R.M‖ < ‖zeroTerm l R.M‖ := by
  have h := (sameHeight_amplitude_inverts_at_raccords e l hT hT2 hβ).1
  rwa [← R.entry_eq] at h

/-- **RH ⟹ orientation** : sous RH tout passage est vertical (`β_e = β_l = 1/2`, `T_e < T_l`). -/
theorem towerRaccord_oriented_of_riemannHypothesis (hRH : RiemannHypothesis) (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    (towerRaccordOf p hE hL).Oriented :=
  towerRaccord_oriented_of_vertical (towerRaccordOf p hE hL)
    ((thm_zeroRadialPosition_half_of_riemannHypothesis hRH _).trans
      (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _).symm)
    (passage_height_lt_of_riemannHypothesis hRH p)

/-- **Pour tout zéro hors ligne de hauteur `≥ 2`**, il existe un passage dont le raccord est
construit avec tous ses champs et dont le transport est strictement renversé. -/
theorem off_towerRaccord_reverses {z : TrueZero} (hOff : PIsOffCriticalLine z.1)
    (hT2 : 2 ≤ rZeroHeight z.1) :
    ∃ p : TZeroPassage, ∃ hE : 0 < rZeroHeight p.zEarlierMember,
      ∃ hL : 0 < rZeroHeight p.zLaterMember,
        ¬ (towerRaccordOf p hE hL).Oriented := by
  obtain ⟨p, hE, hL, hHz, hSame, _, _, _⟩ := off_event_increment_without_height hOff
  have hHMR := nullPassage_horizontal p ((thm_zeroPassage_null_iff_sameHeight p).mpr hSame)
  refine ⟨p, hE, hL, not_le.mpr ?_⟩
  exact towerRaccord_reverses_of_sameHeight (towerRaccordOf p hE hL) hSame (hHz ▸ hT2) hHMR.2.1

#print axioms towerRaccord_eq
#print axioms towerRaccordOf
#print axioms towerRaccord_oriented_of_vertical
#print axioms towerRaccord_reverses_of_sameHeight
#print axioms off_towerRaccord_reverses
#print axioms towerRaccord_oriented_of_riemannHypothesis

end RHV6Fresh
