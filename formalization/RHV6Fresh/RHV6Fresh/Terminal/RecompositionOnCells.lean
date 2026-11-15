/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ArithmeticRealization

/-!
# RHV6Fresh — Terminal/RecompositionOnCells : la recomposition des premiers lue sur les cellules d'une Tour
(E463, plan Φ étape Φ7, §19.93, 2026-11-09 ; module isolé, NON importé par `RHV6Fresh.lean` ;
aucune hypothèse, aucun axiome, aucun `sorry`)

Pont entre le découpage par les contacts d'une Tour (E436–E438) et la recomposition unique du signal lissé des premiers (E462).
Multiplié par l'abscisse, le noyau lissé d'une Tour est une primitive de sa valeur brute ; sa variation d'une abscisse à l'abscisse
située une cellule plus loin (facteur `e^{π/T}`) est la part de la Tour sur cette cellule.

* K1 `integratedKernel`, `integratedKernel_eq`.
* K2 `cell_step_cpow`, `cell_step_kernel` : avancer d'une cellule multiplie le noyau intégré par `−e^{π(1+β)/T}`.
* K3 `towerCellShare`, `towerCellShare_eq` ; K4 `towerCellShare_next` : parts consécutives dans ce même rapport.
* K5 `cell_ratio_reads_radial` : à fréquence donnée, le rapport détermine la position radiale.
* K6 `towerCellShare_ne_zero_iff` : part non nulle ⟺ poids non nul.
* K7 `recomposition_piece_balance` : sur toute pièce, la somme des parts de tous les membres d'une recomposition arithmétique égale
  la variation du signal lissé des premiers (fond retiré) multiplié par l'abscisse.
* K8 `recomposition_cellShare_ne_zero_of_isCarrier`, `recomposition_cellShare_eq_zero_of_not_isCarrier`.

Portée : identités exactes, valables sur la ligne comme hors ligne ; le rapport lit la position radiale et n'en interdit aucune.
Rien n'exclut un zéro hors ligne.
-/

namespace RHV6Fresh

open Real RHV3Lean

/-! ## K1 : noyau intégré -/

noncomputable def integratedKernel (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) * Perron.f x s

theorem integratedKernel_eq {x : ℝ} (hx : 0 < x) (s : ℂ) :
    integratedKernel x s = (x : ℂ) ^ (s + 1) / (s * (s + 1)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
  change (x : ℂ) * ((x : ℂ) ^ s / (s * (s + 1))) = (x : ℂ) ^ s * (x : ℂ) / (s * (s + 1))
  ring

theorem ofReal_cpow_eq_exp_log_mul {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s = Complex.exp ((Real.log x : ℂ) * s) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]

/-! ## K2 : un pas d'une cellule -/

theorem cell_step_cpow {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    ((x * Real.exp (π / T) : ℝ) : ℂ) ^ (towerPoint β T + 1) =
      -(Real.exp (π / T * (1 + β)) : ℂ) * (x : ℂ) ^ (towerPoint β T + 1) := by
  have hy : 0 < x * Real.exp (π / T) := mul_pos hx (Real.exp_pos _)
  have h1 : ((π / T : ℝ) : ℂ) * (towerPoint β T + 1) =
      ((π / T * (1 + β) : ℝ) : ℂ) + ((π / T * T : ℝ) : ℂ) * Complex.I := by
    unfold towerPoint
    push_cast
    ring
  have h2 : π / T * T = π := by
    field_simp
  rw [ofReal_cpow_eq_exp_log_mul hy, ofReal_cpow_eq_exp_log_mul hx,
    Real.log_mul hx.ne' (Real.exp_pos (π / T)).ne', Real.log_exp, Complex.ofReal_add, add_mul,
    Complex.exp_add, h1, h2, Complex.exp_add, Complex.exp_pi_mul_I, Complex.ofReal_exp]
  ring

theorem cell_step_kernel {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    integratedKernel (x * Real.exp (π / T)) (towerPoint β T) =
      -(Real.exp (π / T * (1 + β)) : ℂ) * integratedKernel x (towerPoint β T) := by
  rw [integratedKernel_eq (mul_pos hx (Real.exp_pos (π / T))), integratedKernel_eq hx,
    cell_step_cpow hT hx]
  ring

/-! ## K3–K4 : la part d'une Tour sur une cellule -/

noncomputable def towerCellShare (w : ℂ) (β T x : ℝ) : ℂ :=
  w * (integratedKernel (x * Real.exp (π / T)) (towerPoint β T) - integratedKernel x (towerPoint β T))

theorem towerCellShare_eq {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) :
    towerCellShare w β T x =
      -w * ((1 + Real.exp (π / T * (1 + β)) : ℝ) : ℂ) * integratedKernel x (towerPoint β T) := by
  unfold towerCellShare
  rw [cell_step_kernel hT hx]
  push_cast
  ring

theorem towerCellShare_next {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) :
    towerCellShare w β T (x * Real.exp (π / T)) =
      -(Real.exp (π / T * (1 + β)) : ℂ) * towerCellShare w β T x := by
  rw [towerCellShare_eq hT (mul_pos hx (Real.exp_pos (π / T))) w, towerCellShare_eq hT hx w,
    cell_step_kernel hT hx]
  ring

/-! ## K5 : le rapport lit la position radiale -/

theorem cell_ratio_reads_radial {β β' T : ℝ} (hT : 0 < T)
    (h : Real.exp (π / T * (1 + β)) = Real.exp (π / T * (1 + β'))) : β = β' := by
  have h1 := Real.exp_injective h
  have hc : π / T ≠ 0 := (div_pos Real.pi_pos hT).ne'
  have h2 := mul_left_cancel₀ hc h1
  linarith

/-! ## K6 : part non nulle ⟺ poids non nul -/

theorem towerPoint_ne_zero_of_height_pos {β T : ℝ} (hT : 0 < T) : towerPoint β T ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  rw [towerPoint_im] at him
  simp at him
  linarith

theorem towerPoint_add_one_ne_zero_of_height_pos {β T : ℝ} (hT : 0 < T) : towerPoint β T + 1 ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  rw [Complex.add_im, towerPoint_im] at him
  simp at him
  linarith

theorem integratedKernel_towerPoint_ne_zero {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    integratedKernel x (towerPoint β T) ≠ 0 := by
  rw [integratedKernel_eq hx, ofReal_cpow_eq_exp_log_mul hx]
  exact div_ne_zero (Complex.exp_ne_zero _)
    (mul_ne_zero (towerPoint_ne_zero_of_height_pos hT) (towerPoint_add_one_ne_zero_of_height_pos hT))

theorem towerCellShare_ne_zero_iff {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) :
    towerCellShare w β T x ≠ 0 ↔ w ≠ 0 := by
  rw [towerCellShare_eq hT hx]
  have hc : ((1 + Real.exp (π / T * (1 + β)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hk : integratedKernel x (towerPoint β T) ≠ 0 := integratedKernel_towerPoint_ne_zero hT hx
  constructor
  · intro h hw
    apply h
    rw [hw]
    ring
  · intro hw
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hw) hc) hk

/-! ## K7 : bilan collectif sur une pièce -/

theorem recomposition_term_summable {ι : Type*} (Rec : ArithmeticRecomposition ι) {x : ℝ} (hx : 1 < x) :
    Summable fun i => Rec.weight i * Perron.f x (Rec.point i) := by
  have hfun : (fun i => Rec.weight i * Perron.f x (Rec.point i)) =
      fun i => Rec.weight i / (Rec.point i * (Rec.point i + 1)) * (x : ℂ) ^ Rec.point i := by
    funext i
    change Rec.weight i * ((x : ℂ) ^ Rec.point i / (Rec.point i * (Rec.point i + 1))) =
      Rec.weight i / (Rec.point i * (Rec.point i + 1)) * (x : ℂ) ^ Rec.point i
    ring
  rw [hfun]
  exact summable_profiles Rec.point (fun i => Rec.weight i / (Rec.point i * (Rec.point i + 1)))
    Rec.re_le_one Rec.summable hx

theorem recomposition_piece_balance {ι : Type*} (Rec : ArithmeticRecomposition ι) {a b : ℝ}
    (ha : 1 < a) (hb : 1 < b) :
    ∑' i, Rec.weight i * (integratedKernel b (Rec.point i) - integratedKernel a (Rec.point i)) =
      (b : ℂ) * (smoothedVonMangoldtSum b - smoothedZeroBackground b) -
        (a : ℂ) * (smoothedVonMangoldtSum a - smoothedZeroBackground a) := by
  have hsb := (recomposition_term_summable Rec hb).mul_left (b : ℂ)
  have hsa := (recomposition_term_summable Rec ha).mul_left (a : ℂ)
  calc ∑' i, Rec.weight i * (integratedKernel b (Rec.point i) - integratedKernel a (Rec.point i))
      = ∑' i, ((b : ℂ) * (Rec.weight i * Perron.f b (Rec.point i)) -
          (a : ℂ) * (Rec.weight i * Perron.f a (Rec.point i))) :=
        tsum_congr fun i => by
          simp only [integratedKernel]
          ring
    _ = ∑' i, (b : ℂ) * (Rec.weight i * Perron.f b (Rec.point i)) -
          ∑' i, (a : ℂ) * (Rec.weight i * Perron.f a (Rec.point i)) := hsb.tsum_sub hsa
    _ = (b : ℂ) * (smoothedVonMangoldtSum b - smoothedZeroBackground b) -
          (a : ℂ) * (smoothedVonMangoldtSum a - smoothedZeroBackground a) := by
        rw [tsum_mul_left, tsum_mul_left, Rec.recomposes b hb, Rec.recomposes a ha]

/-! ## K8 : dans toute recomposition, la part d'une Tour sur chacune de ses cellules -/

theorem recomposition_cellShare_ne_zero_of_isCarrier {ι : Type*} (Rec : ArithmeticRecomposition ι)
    {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hc : IsCarrier β T) :
    ∃ i, Rec.point i = towerPoint β T ∧ towerCellShare (Rec.weight i) β T x ≠ 0 := by
  obtain ⟨i, hi, hw⟩ := recomposition_contains_carrier Rec hT hc
  exact ⟨i, hi, (towerCellShare_ne_zero_iff hT hx _).mpr hw⟩

theorem recomposition_cellShare_eq_zero_of_not_isCarrier {ι : Type*} (Rec : ArithmeticRecomposition ι)
    {β T : ℝ} (hT : 0 < T) (hc : ¬ IsCarrier β T) (i : ι) (hi : Rec.point i = towerPoint β T) (x : ℝ) :
    towerCellShare (Rec.weight i) β T x = 0 := by
  rw [recomposition_weight_eq_zero_of_not_isCarrier Rec hT hc i hi]
  unfold towerCellShare
  rw [zero_mul]

#print axioms cell_step_cpow
#print axioms cell_step_kernel
#print axioms towerCellShare_eq
#print axioms towerCellShare_next
#print axioms cell_ratio_reads_radial
#print axioms towerCellShare_ne_zero_iff
#print axioms recomposition_piece_balance
#print axioms recomposition_cellShare_ne_zero_of_isCarrier
#print axioms recomposition_cellShare_eq_zero_of_not_isCarrier

end RHV6Fresh
