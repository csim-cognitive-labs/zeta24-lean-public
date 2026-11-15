/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MemberConstancySeries
import RHV6Fresh.Terminal.CollectiveSlopeOnPieces

/-!
# RHV6Fresh — Terminal/FiberAnnihilator : l'annulateur de fibre sur les cellules (Ψ2 = Φ9, E468, §19.102)
(plan Ψ, 2026-11-13 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse, aucun axiome, aucun `sorry`)

Stratégie (règle R-Ψ). Cible : écrire, sur les premiers seuls, ce que les AUTRES hauteurs déposent sur les cellules d'une Tour.
Objet cumulé : sur deux cellules consécutives d'une Tour, la combinaison des totaux (aires de demande, E465) à coefficient le facteur
de cellule élimine la Tour ; sur trois cellules, deux coefficients éliminent la paire Tour + miroir ; puis la suite de ces identités
le long des cellules. Pourquoi le ponctuel échoue : une aire seule contient toutes les Tours. Signature d'un hors-ligne : annulée
avec le coefficient de la LIGNE, une Tour hors ligne laisse un résidu `(f_β − f_{1/2}) × part`, non nul, qui croît comme la dérive de Ψ1.
Suite : la cible unique en série (les autres hauteurs ne peuvent pas fournir au cumul la dérive d'une paire) est désormais écrite.

* F1 `fiberCellTerm`, `fiberCellTerm_summable`, `fiberCellTotal`, `fiberCellTotal_eq_demandArea` (E465 S10 sur la cellule).
* F2 `annihilate_one_tower` : total(x e^{π/T}) − f_β total(x) = somme sur les AUTRES membres.
* F3 `pairAnnihilated`, `annihilate_pair`, `pairAnnihilated_zero_at_tower`, `pairAnnihilated_zero_at_mirror`.
* F4 `annihilate_one_tower_series` : les N identités de cellules consécutives, sommées.
* F5 `line_annihilator_residue`, `line_annihilator_residue_eq_zero_iff`, `line_annihilator_residue_iterate` : signature radiale.
Portée : identités exactes, ligne et hors ligne ; rien n'exclut seul un zéro hors ligne.
-/

namespace RHV6Fresh

open Real

/-! ## F1 : terme et total d'une cellule de pas `T` -/

noncomputable def fiberCellTerm {ι : Type*} (Rec : ArithmeticRecomposition ι) (T : ℝ) (i : ι) (y : ℝ) : ℂ :=
  Rec.weight i * (integratedKernel (y * Real.exp (π / T)) (Rec.point i) - integratedKernel y (Rec.point i))

noncomputable def fiberCellTotal {ι : Type*} (Rec : ArithmeticRecomposition ι) (T : ℝ) (y : ℝ) : ℂ :=
  ∑' i, fiberCellTerm Rec T i y

theorem one_lt_mul_exp_cell {T y : ℝ} (hT : 0 < T) (hy : 1 < y) : 1 < y * Real.exp (π / T) := by
  have h1 : 1 ≤ Real.exp (π / T) := Real.one_le_exp (div_pos Real.pi_pos hT).le
  exact lt_of_lt_of_le hy (le_mul_of_one_le_right (by linarith) h1)

theorem fiberCellTerm_summable {ι : Type*} (Rec : ArithmeticRecomposition ι) {T y : ℝ} (hT : 0 < T) (hy : 1 < y) :
    Summable fun i => fiberCellTerm Rec T i y := by
  have hye := one_lt_mul_exp_cell hT hy
  have h1 := (recomposition_term_summable Rec hye).mul_left ((y * Real.exp (π / T) : ℝ) : ℂ)
  have h2 := (recomposition_term_summable Rec hy).mul_left (y : ℂ)
  refine (h1.sub h2).congr ?_
  intro i
  simp only [fiberCellTerm, integratedKernel]
  push_cast
  ring

theorem fiberCellTerm_eq_towerCellShare {ι : Type*} (Rec : ArithmeticRecomposition ι) {β T : ℝ} {j : ι}
    (hj : Rec.point j = towerPoint β T) (y : ℝ) :
    fiberCellTerm Rec T j y = towerCellShare (Rec.weight j) β T y := by
  unfold fiberCellTerm towerCellShare
  rw [hj]

theorem fiberCellTotal_eq_demandArea {ι : Type*} (Rec : ArithmeticRecomposition ι) {T y : ℝ} (hT : 0 < T)
    (hy : 1 < y) :
    fiberCellTotal Rec T y =
      ((demandArea y (y * Real.exp (π / T)) : ℝ) : ℂ) -
        (((y * Real.exp (π / T) : ℝ) : ℂ) * residualBackground (y * Real.exp (π / T)) -
          (y : ℂ) * residualBackground y) := by
  unfold fiberCellTotal fiberCellTerm
  have h1 : 1 ≤ Real.exp (π / T) := Real.one_le_exp (div_pos Real.pi_pos hT).le
  exact collective_piece_slope_balance Rec hy (le_mul_of_one_le_right (by linarith) h1)

/-! ## F2 : annuler une Tour par deux cellules consécutives -/

theorem annihilate_one_tower {ι : Type*} [DecidableEq ι] (Rec : ArithmeticRecomposition ι) {β T x : ℝ}
    (hT : 0 < T) (hx : 1 < x) (j : ι) (hj : Rec.point j = towerPoint β T) :
    fiberCellTotal Rec T (x * Real.exp (π / T)) - cellFactor β T * fiberCellTotal Rec T x =
      ∑' i, if i = j then 0 else
        (fiberCellTerm Rec T i (x * Real.exp (π / T)) - cellFactor β T * fiberCellTerm Rec T i x) := by
  have hxe := one_lt_mul_exp_cell hT hx
  have h1 := fiberCellTerm_summable Rec hT hxe
  have h2 := (fiberCellTerm_summable Rec hT hx).mul_left (cellFactor β T)
  have hs := h1.sub h2
  have hj0 : fiberCellTerm Rec T j (x * Real.exp (π / T)) - cellFactor β T * fiberCellTerm Rec T j x = 0 := by
    rw [fiberCellTerm_eq_towerCellShare Rec hj, fiberCellTerm_eq_towerCellShare Rec hj,
      towerCellShare_next hT (by linarith) (Rec.weight j)]
    unfold cellFactor
    ring
  unfold fiberCellTotal
  rw [← tsum_mul_left, ← h1.tsum_sub h2, hs.tsum_eq_add_tsum_ite j, hj0, zero_add]

/-! ## F3 : annuler la paire Tour + miroir par trois cellules consécutives -/

noncomputable def pairAnnihilated {ι : Type*} (Rec : ArithmeticRecomposition ι) (β T : ℝ) (i : ι) (x : ℝ) : ℂ :=
  fiberCellTerm Rec T i (x * Real.exp (π / T) ^ 2) -
    (cellFactor β T + cellFactor (1 - β) T) * fiberCellTerm Rec T i (x * Real.exp (π / T)) +
    cellFactor β T * cellFactor (1 - β) T * fiberCellTerm Rec T i x

theorem annihilate_pair {ι : Type*} (Rec : ArithmeticRecomposition ι) {β T x : ℝ} (hT : 0 < T) (hx : 1 < x) :
    fiberCellTotal Rec T (x * Real.exp (π / T) ^ 2) -
        (cellFactor β T + cellFactor (1 - β) T) * fiberCellTotal Rec T (x * Real.exp (π / T)) +
        cellFactor β T * cellFactor (1 - β) T * fiberCellTotal Rec T x =
      ∑' i, pairAnnihilated Rec β T i x := by
  have hxe := one_lt_mul_exp_cell hT hx
  have hxe2 : 1 < x * Real.exp (π / T) ^ 2 := by
    have := one_lt_mul_exp_cell hT hxe
    rwa [mul_assoc, ← pow_two] at this
  have h0 := fiberCellTerm_summable Rec hT hxe2
  have h1 := (fiberCellTerm_summable Rec hT hxe).mul_left (cellFactor β T + cellFactor (1 - β) T)
  have h2 := (fiberCellTerm_summable Rec hT hx).mul_left (cellFactor β T * cellFactor (1 - β) T)
  unfold fiberCellTotal pairAnnihilated
  rw [← tsum_mul_left, ← tsum_mul_left, ← h0.tsum_sub h1, ← (h0.sub h1).tsum_add h2]

theorem towerCellShare_two_cells {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) :
    towerCellShare w β T (x * Real.exp (π / T) ^ 2) = cellFactor β T ^ 2 * towerCellShare w β T x :=
  towerCellShare_iterate hT hx w 2

theorem pairAnnihilated_zero_at_tower {ι : Type*} (Rec : ArithmeticRecomposition ι) {β T x : ℝ} (hT : 0 < T)
    (hx : 0 < x) {j : ι} (hj : Rec.point j = towerPoint β T) : pairAnnihilated Rec β T j x = 0 := by
  unfold pairAnnihilated
  rw [fiberCellTerm_eq_towerCellShare Rec hj, fiberCellTerm_eq_towerCellShare Rec hj,
    fiberCellTerm_eq_towerCellShare Rec hj, towerCellShare_two_cells hT hx, towerCellShare_next hT hx]
  unfold cellFactor
  ring

theorem pairAnnihilated_zero_at_mirror {ι : Type*} (Rec : ArithmeticRecomposition ι) {β T x : ℝ} (hT : 0 < T)
    (hx : 0 < x) {j' : ι} (hj' : Rec.point j' = towerPoint (1 - β) T) : pairAnnihilated Rec β T j' x = 0 := by
  unfold pairAnnihilated
  rw [fiberCellTerm_eq_towerCellShare Rec hj', fiberCellTerm_eq_towerCellShare Rec hj',
    fiberCellTerm_eq_towerCellShare Rec hj', towerCellShare_two_cells hT hx, towerCellShare_next hT hx]
  unfold cellFactor
  ring

/-! ## F4 : la série des identités annulées -/

theorem annihilate_one_tower_series {ι : Type*} [DecidableEq ι] (Rec : ArithmeticRecomposition ι) {β T x : ℝ}
    (hT : 0 < T) (hx : 1 < x) (j : ι) (hj : Rec.point j = towerPoint β T) (N : ℕ) :
    ∑ n ∈ Finset.range N, (fiberCellTotal Rec T (x * Real.exp (π / T) ^ n * Real.exp (π / T)) -
        cellFactor β T * fiberCellTotal Rec T (x * Real.exp (π / T) ^ n)) =
      ∑ n ∈ Finset.range N, ∑' i, if i = j then 0 else
        (fiberCellTerm Rec T i (x * Real.exp (π / T) ^ n * Real.exp (π / T)) -
          cellFactor β T * fiberCellTerm Rec T i (x * Real.exp (π / T) ^ n)) := by
  apply Finset.sum_congr rfl
  intro n _
  have hxn : 1 < x * Real.exp (π / T) ^ n :=
    lt_of_lt_of_le hx (le_mul_of_one_le_right (by linarith)
      (one_le_pow₀ (Real.one_le_exp (div_pos Real.pi_pos hT).le)))
  exact annihilate_one_tower Rec hT hxn j hj

/-! ## F5 : signature radiale de l'annulateur de la ligne -/

theorem line_annihilator_residue {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) :
    towerCellShare w β T (x * Real.exp (π / T)) - cellFactor (1 / 2) T * towerCellShare w β T x =
      (cellFactor β T - cellFactor (1 / 2) T) * towerCellShare w β T x := by
  rw [towerCellShare_next hT hx w]
  unfold cellFactor
  ring

theorem cellFactor_inj {β β' T : ℝ} (hT : 0 < T) (h : cellFactor β T = cellFactor β' T) : β = β' := by
  unfold cellFactor at h
  have h1 := neg_inj.mp h
  exact cell_ratio_reads_radial hT (Complex.ofReal_inj.mp h1)

theorem line_annihilator_residue_eq_zero_iff {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) {w : ℂ} (hw : w ≠ 0) :
    towerCellShare w β T (x * Real.exp (π / T)) - cellFactor (1 / 2) T * towerCellShare w β T x = 0 ↔
      β = 1 / 2 := by
  rw [line_annihilator_residue hT hx w, mul_eq_zero]
  have hs : towerCellShare w β T x ≠ 0 := (towerCellShare_ne_zero_iff hT hx w).mpr hw
  constructor
  · intro h
    rcases h with h | h
    · exact cellFactor_inj hT (sub_eq_zero.mp h)
    · exact absurd h hs
  · intro h
    left
    rw [h, sub_self]

theorem line_annihilator_residue_iterate {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) (n : ℕ) :
    towerCellShare w β T (x * Real.exp (π / T) ^ n * Real.exp (π / T)) -
        cellFactor (1 / 2) T * towerCellShare w β T (x * Real.exp (π / T) ^ n) =
      (cellFactor β T - cellFactor (1 / 2) T) * cellFactor β T ^ n * towerCellShare w β T x := by
  have hxn : 0 < x * Real.exp (π / T) ^ n := mul_pos hx (pow_pos (Real.exp_pos _) _)
  rw [line_annihilator_residue hT hxn w, towerCellShare_iterate hT hx w n]
  ring

#print axioms fiberCellTotal_eq_demandArea
#print axioms annihilate_one_tower
#print axioms annihilate_pair
#print axioms pairAnnihilated_zero_at_tower
#print axioms pairAnnihilated_zero_at_mirror
#print axioms annihilate_one_tower_series
#print axioms line_annihilator_residue_eq_zero_iff
#print axioms line_annihilator_residue_iterate

end RHV6Fresh
