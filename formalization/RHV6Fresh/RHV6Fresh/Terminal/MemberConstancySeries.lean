/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RecompositionOnCells

/-!
# RHV6Fresh — Terminal/MemberConstancySeries : la constance par membre comme loi de SÉRIE (Ψ1, E467, §19.101)
(plan Ψ, 2026-11-13 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse, aucun axiome, aucun `sorry`)

Stratégie (règle R-Ψ). Cible : la part relative d'une Tour réalisée reste bornée le long de la série de ses cellules.
Objet cumulé : la suite des parts `towerCellShare` sur les cellules consécutives, rapportée à l'échelle de la ligne `x^{3/2}`.
Pourquoi le ponctuel échoue : sur une cellule la part est non nulle pour toute Tour réalisée (E463) et rien de plus ; le facteur
d'une cellule à la suivante (E463 K4) n'avait jamais été COMPOSÉ. Signature d'un hors-ligne : croissance géométrique de la part
relative du miroir, raison `e^{π(β−1/2)/T}` par cellule, soit `A^{β−1/2}` sur une plage logarithmique de facteur `A`.
Suite dans les deux issues : côté premiers par l'annulateur de fibre (Ψ2, `FiberAnnihilator.lean`).

* C1 `cellFactor`, `towerCellShare_iterate` : produit des facteurs de cellule = forme close.
* C2 `relativeCellShare`, `relativeCellShare_next`, `relativeCellShare_iterate`, `relativeCellShare_log_range`.
* C3 `relativeCellShare_next_eq_iff` : constante d'une cellule à la suivante ⟺ sur la ligne.
* C4 `relativeCellShare_unbounded_of_half_lt` (miroir), `relativeCellShare_vanishes_of_lt_half` (membre bas).
* C5 `pairRelativeShare_unbounded_of_lt_half` : la paire (membre bas + miroir) n'est pas bornée au cumul.
* C6 `cell_ratio_fractional` : par cellule, l'écart à la ligne est entre `e^{−π/(2T)}` et `e^{π/(2T)}` (fractionnel).
* C7 `recomposition_carrier_relativeShare_pos` : dans toute recomposition, la part relative d'une porteuse est > 0 sur chaque cellule.
Portée : identités et équivalences exactes, ligne et hors ligne ; le cumul lit la position radiale ; rien n'exclut seul un zéro hors ligne.
-/

namespace RHV6Fresh

open Real

/-! ## C1 : facteur de cellule et forme close du produit -/

noncomputable def cellFactor (β T : ℝ) : ℂ := -(Real.exp (π / T * (1 + β)) : ℂ)

theorem towerCellShare_iterate {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) (n : ℕ) :
    towerCellShare w β T (x * Real.exp (π / T) ^ n) = cellFactor β T ^ n * towerCellShare w β T x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : 0 < x * Real.exp (π / T) ^ n := mul_pos hx (pow_pos (Real.exp_pos _) _)
    rw [pow_succ, ← mul_assoc, towerCellShare_next hT hxn w, ih, pow_succ]
    unfold cellFactor
    ring

/-! ## C2 : part relative à l'échelle de la ligne -/

noncomputable def relativeCellShare (w : ℂ) (β T x : ℝ) : ℝ :=
  ‖towerCellShare w β T x‖ / x ^ ((3 : ℝ) / 2)

theorem relativeCellShare_nonneg (w : ℂ) (β T x : ℝ) (hx : 0 < x) : 0 ≤ relativeCellShare w β T x :=
  div_nonneg (norm_nonneg _) (Real.rpow_nonneg hx.le _)

theorem relativeCellShare_pos {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) {w : ℂ} (hw : w ≠ 0) :
    0 < relativeCellShare w β T x :=
  div_pos (norm_pos_iff.mpr ((towerCellShare_ne_zero_iff hT hx w).mpr hw)) (Real.rpow_pos_of_pos hx _)

theorem relativeCellShare_next {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) :
    relativeCellShare w β T (x * Real.exp (π / T)) =
      Real.exp (π / T * (β - 1 / 2)) * relativeCellShare w β T x := by
  unfold relativeCellShare
  rw [towerCellShare_next hT hx w, norm_mul, norm_neg, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Real.mul_rpow hx.le (Real.exp_pos _).le, ← Real.exp_mul]
  have h1 : Real.exp (π / T * (1 + β)) =
      Real.exp (π / T * (β - 1 / 2)) * Real.exp (π / T * (3 / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1]
  have hx32 : 0 < x ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hx _
  have he : 0 < Real.exp (π / T * (3 / 2)) := Real.exp_pos _
  field_simp

theorem relativeCellShare_iterate {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) (n : ℕ) :
    relativeCellShare w β T (x * Real.exp (π / T) ^ n) =
      Real.exp (n * (π / T * (β - 1 / 2))) * relativeCellShare w β T x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : 0 < x * Real.exp (π / T) ^ n := mul_pos hx (pow_pos (Real.exp_pos _) _)
    have hcast : (((n + 1 : ℕ) : ℝ) * (π / T * (β - 1 / 2))) =
        π / T * (β - 1 / 2) + n * (π / T * (β - 1 / 2)) := by push_cast; ring
    rw [pow_succ, ← mul_assoc, relativeCellShare_next hT hxn w, ih, hcast, Real.exp_add]
    ring

/-- Sur une plage logarithmique de facteur `A = e^{nπ/T}` (n cellules), la part relative est multipliée par `A^{β−1/2}`. -/
theorem relativeCellShare_log_range {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) (n : ℕ) :
    relativeCellShare w β T (x * Real.exp (π / T) ^ n) =
      (Real.exp (π / T) ^ n) ^ (β - 1 / 2) * relativeCellShare w β T x := by
  rw [relativeCellShare_iterate hT hx w n, ← Real.exp_nat_mul, ← Real.exp_mul]
  congr 2
  ring

/-! ## C3 : constante ⟺ ligne -/

theorem relativeCellShare_next_eq_iff {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) {w : ℂ} (hw : w ≠ 0) :
    relativeCellShare w β T (x * Real.exp (π / T)) = relativeCellShare w β T x ↔ β = 1 / 2 := by
  rw [relativeCellShare_next hT hx w]
  have hr : 0 < relativeCellShare w β T x := relativeCellShare_pos hT hx hw
  constructor
  · intro h
    have h2 : Real.exp (π / T * (β - 1 / 2)) = 1 :=
      mul_right_cancel₀ hr.ne' (h.trans (one_mul _).symm)
    have h3 : π / T * (β - 1 / 2) = 0 := Real.exp_injective (h2.trans Real.exp_zero.symm)
    have hc : π / T ≠ 0 := (div_pos Real.pi_pos hT).ne'
    have h4 : β - 1 / 2 = 0 := (mul_eq_zero.mp h3).resolve_left hc
    linarith
  · intro h
    subst h
    simp

/-! ## C4 : miroir non borné, membre bas évanescent -/

theorem relativeCellShare_unbounded_of_half_lt {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) {w : ℂ} (hw : w ≠ 0)
    (hβ : 1 / 2 < β) (M : ℝ) :
    ∃ n : ℕ, M < relativeCellShare w β T (x * Real.exp (π / T) ^ n) := by
  have hr : 0 < relativeCellShare w β T x := relativeCellShare_pos hT hx hw
  have hc0 : 0 < π / T * (β - 1 / 2) := mul_pos (div_pos Real.pi_pos hT) (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_gt ((M / relativeCellShare w β T x - 1) / (π / T * (β - 1 / 2)))
  refine ⟨n, ?_⟩
  rw [relativeCellShare_iterate hT hx w n]
  have h1 : M / relativeCellShare w β T x - 1 < n * (π / T * (β - 1 / 2)) := by
    rwa [div_lt_iff₀ hc0] at hn
  have h2 := Real.add_one_le_exp (n * (π / T * (β - 1 / 2)))
  have h3 : M / relativeCellShare w β T x < Real.exp (n * (π / T * (β - 1 / 2))) := by linarith
  rwa [div_lt_iff₀ hr] at h3

theorem relativeCellShare_vanishes_of_lt_half {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ)
    (hβ : β < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, relativeCellShare w β T (x * Real.exp (π / T) ^ n) < ε := by
  have hd0 : 0 < π / T * (1 / 2 - β) := mul_pos (div_pos Real.pi_pos hT) (by linarith)
  have hr0 : 0 ≤ relativeCellShare w β T x := relativeCellShare_nonneg w β T x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ((relativeCellShare w β T x / ε - 1) / (π / T * (1 / 2 - β)))
  refine ⟨n, ?_⟩
  rw [relativeCellShare_iterate hT hx w n]
  have hneg : Real.exp (n * (π / T * (β - 1 / 2))) = 1 / Real.exp (n * (π / T * (1 / 2 - β))) := by
    have hr : (n : ℝ) * (π / T * (β - 1 / 2)) = -(n * (π / T * (1 / 2 - β))) := by ring
    rw [hr, Real.exp_neg]
    exact (one_div _).symm
  rw [hneg]
  have h1 : relativeCellShare w β T x / ε - 1 < n * (π / T * (1 / 2 - β)) := by
    rwa [div_lt_iff₀ hd0] at hn
  have h2 := Real.add_one_le_exp (n * (π / T * (1 / 2 - β)))
  have h3 : relativeCellShare w β T x / ε < Real.exp (n * (π / T * (1 / 2 - β))) := by linarith
  have hE : 0 < Real.exp (n * (π / T * (1 / 2 - β))) := Real.exp_pos _
  rw [div_lt_iff₀ hε] at h3
  rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hE]
  linarith

/-! ## C5 : la paire au cumul -/

noncomputable def pairRelativeShare (w w' : ℂ) (β T x : ℝ) : ℝ :=
  relativeCellShare w β T x + relativeCellShare w' (1 - β) T x

theorem pairRelativeShare_unbounded_of_lt_half {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) {w' : ℂ}
    (hw' : w' ≠ 0) (hβ : β < 1 / 2) (M : ℝ) :
    ∃ n : ℕ, M < pairRelativeShare w w' β T (x * Real.exp (π / T) ^ n) := by
  obtain ⟨n, hn⟩ := relativeCellShare_unbounded_of_half_lt hT hx hw' (by linarith : 1 / 2 < 1 - β) M
  refine ⟨n, lt_of_lt_of_le hn ?_⟩
  unfold pairRelativeShare
  exact le_add_of_nonneg_left
    (relativeCellShare_nonneg w β T _ (mul_pos hx (pow_pos (Real.exp_pos _) _)))

/-! ## C6 : par cellule, l'écart est fractionnel -/

theorem cell_ratio_fractional {β T : ℝ} (hT : 0 < T) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    Real.exp (-(π / (2 * T))) ≤ Real.exp (π / T * (β - 1 / 2)) ∧
      Real.exp (π / T * (β - 1 / 2)) ≤ Real.exp (π / (2 * T)) := by
  have hp : 0 ≤ π / T := (div_pos Real.pi_pos hT).le
  constructor
  · apply Real.exp_le_exp.mpr
    have : π / T * (-(1 / 2)) ≤ π / T * (β - 1 / 2) := mul_le_mul_of_nonneg_left (by linarith) hp
    calc -(π / (2 * T)) = π / T * (-(1 / 2)) := by field_simp
      _ ≤ _ := this
  · apply Real.exp_le_exp.mpr
    have : π / T * (β - 1 / 2) ≤ π / T * (1 / 2) := mul_le_mul_of_nonneg_left (by linarith) hp
    calc π / T * (β - 1 / 2) ≤ π / T * (1 / 2) := this
      _ = π / (2 * T) := by field_simp

/-! ## C7 : dans toute recomposition, la part relative d'une porteuse est positive sur chaque cellule -/

theorem recomposition_carrier_relativeShare_pos {ι : Type*} (Rec : ArithmeticRecomposition ι)
    {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hc : IsCarrier β T) :
    ∃ i, Rec.point i = towerPoint β T ∧ 0 < relativeCellShare (Rec.weight i) β T x := by
  obtain ⟨i, hi, hw⟩ := recomposition_cellShare_ne_zero_of_isCarrier Rec hT hx hc
  exact ⟨i, hi, relativeCellShare_pos hT hx ((towerCellShare_ne_zero_iff hT hx _).mp hw)⟩

#print axioms towerCellShare_iterate
#print axioms relativeCellShare_iterate
#print axioms relativeCellShare_log_range
#print axioms relativeCellShare_next_eq_iff
#print axioms relativeCellShare_unbounded_of_half_lt
#print axioms relativeCellShare_vanishes_of_lt_half
#print axioms pairRelativeShare_unbounded_of_lt_half
#print axioms cell_ratio_fractional
#print axioms recomposition_carrier_relativeShare_pos

end RHV6Fresh
