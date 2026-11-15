/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.EulerMaclaurinFine
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Certificat d'Euler-Maclaurin a N = 10, T = 15 (verification (V1), version fine)

Pour `1/2 ≤ σ < 1` : `‖s‖‖s+1‖/12 · (10^{-σ-2} + 10^{-σ-1}/(σ+1)) < ‖eulerMaclaurinMain 10 s‖`, `s = σ + 15 i`.
Fichier GENERE par `experiments/e191_em10_certificate_generator.py` (constantes rationnelles verifiees par Lean) :
logarithmes certifies (Mathlib `log_two_gt_d9`, `abs_log_sub_add_sum_range_le`), `cos/sin (15 log n)` par Taylor d'ordre 12
(`Complex.exp_bound`) et puissance quatrieme, puissances `n^{-p/32}` encadrees par `x^32`, seize sous-intervalles de `σ`
avec une rotation rationnelle `r1 + r2 i` par sous-intervalle. Aucune preuve admise, aucun axiome ajouté.
-/

namespace RHV6Fresh
open Complex

namespace EM10

noncomputable def tC1 (u : ℝ) : ℝ := 1 - u^2/2 + u^4/24 - u^6/720 + u^8/40320 - u^10/3628800
noncomputable def tS1 (u : ℝ) : ℝ := u - u^3/6 + u^5/120 - u^7/5040 + u^9/362880 - u^11/39916800

lemma taylor_split (u : ℝ) :
    ∑ m ∈ Finset.range 12, ((u:ℂ) * I)^m / (m.factorial : ℂ) = (tC1 u : ℂ) + (tS1 u : ℂ) * I := by
  have h2 : I^2 = -1 := I_sq
  have h3 : I^3 = -I := by rw [pow_succ, I_sq]; ring
  have h4 : I^4 = 1 := by rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num
  have h5 : I^5 = I := by rw [pow_succ, h4]; ring
  have h6 : I^6 = -1 := by rw [pow_succ, h5, ← sq, I_sq]
  have h7 : I^7 = -I := by rw [pow_succ, h6]; ring
  have h8 : I^8 = 1 := by rw [show (8:ℕ) = 4 * 2 from rfl, pow_mul, h4]; norm_num
  have h9 : I^9 = I := by rw [pow_succ, h8]; ring
  have h10 : I^10 = -1 := by rw [pow_succ, h9, ← sq, I_sq]
  have h11 : I^11 = -I := by rw [pow_succ, h10]; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, mul_pow, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    Nat.factorial, tC1, tS1]
  push_cast
  ring

lemma exp_taylor (u : ℝ) (hu : |u| ≤ 1) :
    ‖exp ((u:ℂ) * I) - ((tC1 u : ℂ) + (tS1 u : ℂ) * I)‖ ≤ 3/10^9 := by
  have hn : ‖(u:ℂ) * I‖ ≤ 1 := by simpa using hu
  have h := Complex.exp_bound hn (n := 12) (by norm_num)
  rw [taylor_split] at h
  refine h.trans ?_
  have h12 : ‖(u:ℂ)*I‖ ^ 12 ≤ 1 := pow_le_one₀ (norm_nonneg _) hn
  have : ((12:ℕ).succ : ℝ) * (((12:ℕ).factorial : ℝ) * (12:ℕ))⁻¹ ≤ 3/10^9 := by
    norm_num [Nat.factorial]
  calc _ ≤ 1 * (((12:ℕ).succ : ℝ) * (((12:ℕ).factorial : ℝ) * (12:ℕ))⁻¹) := by
        gcongr
    _ ≤ _ := by linarith

lemma pow4_ri (a b : ℝ) : (((a:ℂ) + b*I))^4 =
    ((a^4 - 6*a^2*b^2 + b^4 : ℝ):ℂ) + ((4*a^3*b - 4*a*b^3 : ℝ):ℂ)*I := by
  push_cast
  linear_combination (6*(a:ℂ)^2*b^2 + 4*a*b^3*I + (b:ℂ)^4*(I^2-1)) * I_sq

lemma norm_ri_le (a b : ℝ) : ‖(a:ℂ) + b*I‖ ≤ |a| + |b| := by
  refine (norm_add_le _ _).trans ?_
  simp

lemma cis4 (y : ℝ) (hy : |y| ≤ 4) :
    ‖exp ((y:ℂ) * I) - ((((tC1 (y/4))^4 - 6*(tC1 (y/4))^2*(tS1 (y/4))^2 + (tS1 (y/4))^4 : ℝ) : ℂ) +
      ((4*(tC1 (y/4))^3*tS1 (y/4) - 4*tC1 (y/4)*(tS1 (y/4))^3 : ℝ) : ℂ) * I)‖ ≤ 1/10^7 := by
  set u : ℝ := y/4 with hu
  have hu1 : |u| ≤ 1 := by
    rw [hu, abs_div]; norm_num; linarith
  have ht := exp_taylor u hu1
  set Q : ℂ := (tC1 u : ℂ) + (tS1 u : ℂ) * I with hQ
  set z : ℂ := exp ((u:ℂ) * I) with hz
  have hz1 : ‖z‖ = 1 := by rw [hz]; exact Complex.norm_exp_ofReal_mul_I u
  have hQ2 : ‖Q‖ ≤ 2 := by
    have : ‖Q‖ ≤ ‖z‖ + ‖z - Q‖ := by
      calc ‖Q‖ = ‖z - (z - Q)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hexp : exp ((y:ℂ) * I) = z^4 := by
    rw [hz, ← Complex.exp_nat_mul]; congr 1
    rw [hu]; push_cast; ring
  rw [hexp, ← pow4_ri]
  have hfac : z^4 - Q^4 = (z - Q) * (z^3 + z^2*Q + z*Q^2 + Q^3) := by ring
  rw [hfac, norm_mul]
  have hs : ‖z^3 + z^2*Q + z*Q^2 + Q^3‖ ≤ 15 := by
    have e1 := norm_add_le (z^3 + z^2*Q + z*Q^2) (Q^3)
    have e2 := norm_add_le (z^3 + z^2*Q) (z*Q^2)
    have e3 := norm_add_le (z^3) (z^2*Q)
    simp only [norm_mul, norm_pow, hz1] at e1 e2 e3
    have : ‖Q‖^3 ≤ 8 := by nlinarith [norm_nonneg Q]
    have : ‖Q‖^2 ≤ 4 := by nlinarith [norm_nonneg Q]
    nlinarith [norm_nonneg Q]
  calc ‖z - Q‖ * ‖z^3 + z^2*Q + z*Q^2 + Q^3‖ ≤ (3/10^9) * 15 := by
        apply mul_le_mul ht hs (norm_nonneg _) (by norm_num)
    _ ≤ _ := by norm_num



lemma exp_neg_log_approx (Lg lo hi : ℝ) (hlo : lo ≤ Lg) (hhi : Lg ≤ hi) (k : ℕ) (y0 η w1 w2 : ℝ)
    (hy : |y0| ≤ 4)
    (h1 : 2*k*3.14159265358979323847 - 15*lo ≤ y0 + η)
    (h2 : y0 - η ≤ 2*k*3.14159265358979323846 - 15*hi)
    (hw1 : |(tC1 (y0/4))^4 - 6*(tC1 (y0/4))^2*(tS1 (y0/4))^2 + (tS1 (y0/4))^4 - w1| ≤ 1/10^12)
    (hw2 : |4*(tC1 (y0/4))^3*tS1 (y0/4) - 4*tC1 (y0/4)*(tS1 (y0/4))^3 - w2| ≤ 1/10^12) :
    ‖exp (-(((15*Lg : ℝ) : ℂ) * I)) - ((w1:ℂ) + (w2:ℂ) * I)‖ ≤ η + 1/10^7 + 2/10^12 := by
  have hpl := Real.pi_gt_d20
  have hpu := Real.pi_lt_d20
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  set y : ℝ := 2*k*Real.pi - 15*Lg with hydef
  have hyy : |y - y0| ≤ η := by
    have a1 : (k:ℝ) * Real.pi ≤ k * 3.14159265358979323847 := mul_le_mul_of_nonneg_left hpu.le hk
    have a2 : (k:ℝ) * 3.14159265358979323846 ≤ k * Real.pi := mul_le_mul_of_nonneg_left hpl.le hk
    rw [abs_le]; constructor <;> nlinarith
  have hper : exp (-(((15*Lg : ℝ) : ℂ) * I)) = exp ((y:ℂ) * I) := by
    have := (Complex.exp_periodic.nat_mul k) (-(((15*Lg : ℝ) : ℂ) * I))
    rw [← this]; congr 1
    rw [hydef]; push_cast; ring
  have hLip : ‖exp ((y:ℂ) * I) - exp ((y0:ℂ) * I)‖ ≤ η := by
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := y - y0)
    have e : exp ((y:ℂ) * I) - exp ((y0:ℂ) * I) = exp ((y0:ℂ) * I) * (exp (I * ((y - y0 : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, ← Complex.exp_add]; push_cast
      rw [mul_one]; congr 2; ring
    rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact h.trans (by simpa using hyy)
  have hc := cis4 y0 hy
  have hr : ‖((((tC1 (y0/4))^4 - 6*(tC1 (y0/4))^2*(tS1 (y0/4))^2 + (tS1 (y0/4))^4 : ℝ) : ℂ) +
      ((4*(tC1 (y0/4))^3*tS1 (y0/4) - 4*tC1 (y0/4)*(tS1 (y0/4))^3 : ℝ) : ℂ) * I) - ((w1:ℂ) + (w2:ℂ) * I)‖ ≤ 2/10^12 := by
    have e : ((((tC1 (y0/4))^4 - 6*(tC1 (y0/4))^2*(tS1 (y0/4))^2 + (tS1 (y0/4))^4 : ℝ) : ℂ) +
      ((4*(tC1 (y0/4))^3*tS1 (y0/4) - 4*tC1 (y0/4)*(tS1 (y0/4))^3 : ℝ) : ℂ) * I) - ((w1:ℂ) + (w2:ℂ) * I)
      = (((tC1 (y0/4))^4 - 6*(tC1 (y0/4))^2*(tS1 (y0/4))^2 + (tS1 (y0/4))^4 - w1 : ℝ) : ℂ) +
        ((4*(tC1 (y0/4))^3*tS1 (y0/4) - 4*tC1 (y0/4)*(tS1 (y0/4))^3 - w2 : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [e]
    refine (norm_ri_le _ _).trans ?_
    linarith
  rw [hper]
  generalize (((((tC1 (y0/4))^4 - 6*(tC1 (y0/4))^2*(tS1 (y0/4))^2 + (tS1 (y0/4))^4 : ℝ) : ℂ) +
      ((4*(tC1 (y0/4))^3*tS1 (y0/4) - 4*tC1 (y0/4)*(tS1 (y0/4))^3 : ℝ) : ℂ) * I)) = M at hc hr
  have e : exp ((y:ℂ) * I) - ((w1:ℂ) + (w2:ℂ) * I) =
      (exp ((y:ℂ) * I) - exp ((y0:ℂ) * I)) + (exp ((y0:ℂ) * I) - M) + (M - ((w1:ℂ) + (w2:ℂ) * I)) := by ring
  rw [e]
  have t1 := norm_add_le (exp ((y:ℂ) * I) - exp ((y0:ℂ) * I) + (exp ((y0:ℂ) * I) - M)) (M - ((w1:ℂ) + (w2:ℂ) * I))
  have t2 := norm_add_le (exp ((y:ℂ) * I) - exp ((y0:ℂ) * I)) (exp ((y0:ℂ) * I) - M)
  linarith



noncomputable def Eθ (n : ℕ) : ℂ := exp (-(((15 * Real.log n : ℝ) : ℂ) * I))

lemma inv_cpow (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) :
    1 / (n:ℂ) ^ ((σ:ℂ) + ((15:ℝ):ℂ) * I) = (((n:ℝ) ^ (-σ) : ℝ) : ℂ) * Eθ n := by
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hpos : (0:ℝ) < n := by exact_mod_cast hn
  rw [one_div, ← Complex.cpow_neg, Complex.cpow_def_of_ne_zero hn0]
  have hl : Complex.log (n:ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hpos.le]; simp
  rw [hl, Real.rpow_def_of_pos hpos, Complex.ofReal_exp, Eθ, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma EM_ten (σ : ℝ) (hσ : σ < 1) :
    eulerMaclaurinMain 10 ((σ:ℂ) + ((15:ℝ):ℂ) * I) =
      1 + (((2:ℝ)^(-σ) : ℝ):ℂ) * Eθ 2 + (((3:ℝ)^(-σ) : ℝ):ℂ) * Eθ 3 + (((4:ℝ)^(-σ) : ℝ):ℂ) * Eθ 4
      + (((5:ℝ)^(-σ) : ℝ):ℂ) * Eθ 5 + (((6:ℝ)^(-σ) : ℝ):ℂ) * Eθ 6 + (((7:ℝ)^(-σ) : ℝ):ℂ) * Eθ 7
      + (((8:ℝ)^(-σ) : ℝ):ℂ) * Eθ 8 + (((9:ℝ)^(-σ) : ℝ):ℂ) * Eθ 9
      + ((((10:ℝ)^(-σ) / 2 : ℝ)) : ℂ) * Eθ 10
      - (((10 * (10:ℝ)^(-σ) / ((1-σ)^2 + 225) : ℝ)) : ℂ) * (Eθ 10 * (((1 - σ : ℝ) : ℂ) + 15 * I)) := by
  set s : ℂ := (σ:ℂ) + ((15:ℝ):ℂ) * I with hs
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hs] at this
  have hD : (((1-σ)^2 + 225 : ℝ) : ℂ) ≠ 0 := by
    have : (0:ℝ) < (1-σ)^2 + 225 := by positivity
    exact_mod_cast this.ne'
  have key : (1 - s) * (((1 - σ : ℝ) : ℂ) + 15 * I) = (((1-σ)^2 + 225 : ℝ) : ℂ) := by
    rw [hs]; push_cast
    linear_combination (-225) * I_sq
  have h1s : (1 - s) ≠ 0 := by
    intro h; rw [h, zero_mul] at key; exact hD key.symm
  have hinv : 1 / (1 - s) = (((1 - σ : ℝ) : ℂ) + 15 * I) / (((1-σ)^2 + 225 : ℝ) : ℂ) := by
    rw [div_eq_div_iff h1s hD, one_mul, ← key]; ring
  have h10 : ((10:ℕ):ℂ) ≠ 0 := by norm_num
  have h10pow : ((10:ℕ):ℂ) ^ (1 - s) = 10 * ((((10:ℝ)^(-σ) : ℝ) : ℂ) * Eθ 10) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ h10, Complex.cpow_one, Complex.cpow_neg]
    have := inv_cpow 10 (by norm_num) σ
    rw [one_div] at this
    rw [hs, this]; norm_num
  have h10neg : ((10:ℕ):ℂ) ^ (-s) = (((10:ℝ)^(-σ) : ℝ) : ℂ) * Eθ 10 := by
    rw [Complex.cpow_neg]
    have := inv_cpow 10 (by norm_num) σ
    rw [one_div] at this
    rw [hs, this]; norm_num
  unfold eulerMaclaurinMain
  rw [h10pow, h10neg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [inv_cpow 2 (by norm_num), inv_cpow 3 (by norm_num), inv_cpow 4 (by norm_num), inv_cpow 5 (by norm_num),
    inv_cpow 6 (by norm_num), inv_cpow 7 (by norm_num), inv_cpow 8 (by norm_num), inv_cpow 9 (by norm_num),
    inv_cpow 10 (by norm_num)]
  have e0 : 1 / ((0:ℕ):ℂ) ^ s = 0 := by
    simp [Complex.zero_cpow hs0]
  have e1 : 1 / ((1:ℕ):ℂ) ^ s = 1 := by simp
  rw [e0, e1, div_eq_mul_one_div _ (1 - s), hinv]
  push_cast
  ring



lemma norm_ri_le_one (r1 r2 : ℝ) (hr : r1^2 + r2^2 ≤ 1) : ‖(r1:ℂ) + r2 * I‖ ≤ 1 := by
  have h : ‖(r1:ℂ) + r2 * I‖^2 = r1^2 + r2^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  nlinarith [norm_nonneg ((r1:ℂ) + r2 * I)]

lemma rot_bounds (r1 r2 w1 w2 ε : ℝ) (E : ℂ) (hr : r1^2 + r2^2 ≤ 1)
    (hE : ‖E - ((w1:ℂ) + (w2:ℂ) * I)‖ ≤ ε) :
    (r1*w1 - r2*w2) - ε ≤ (((r1:ℂ) + r2 * I) * E).re ∧ (((r1:ℂ) + r2 * I) * E).re ≤ (r1*w1 - r2*w2) + ε ∧
    (r1*w2 + r2*w1) - ε ≤ (((r1:ℂ) + r2 * I) * E).im ∧ (((r1:ℂ) + r2 * I) * E).im ≤ (r1*w2 + r2*w1) + ε := by
  have hrot := norm_ri_le_one r1 r2 hr
  set rot : ℂ := (r1:ℂ) + r2 * I with hrot_def
  have hd : ‖rot * (E - ((w1:ℂ) + (w2:ℂ) * I))‖ ≤ ε := by
    rw [norm_mul]
    calc ‖rot‖ * ‖E - ((w1:ℂ) + (w2:ℂ) * I)‖ ≤ 1 * ε :=
          mul_le_mul hrot hE (norm_nonneg _) (by norm_num)
      _ = ε := one_mul ε
  have hre := Complex.abs_re_le_norm (rot * (E - ((w1:ℂ) + (w2:ℂ) * I)))
  have him := Complex.abs_im_le_norm (rot * (E - ((w1:ℂ) + (w2:ℂ) * I)))
  have e : rot * E = rot * ((w1:ℂ) + (w2:ℂ) * I) + rot * (E - ((w1:ℂ) + (w2:ℂ) * I)) := by ring
  have er : (rot * ((w1:ℂ) + (w2:ℂ) * I)).re = r1*w1 - r2*w2 := by
    rw [hrot_def]; simp
  have ei : (rot * ((w1:ℂ) + (w2:ℂ) * I)).im = r1*w2 + r2*w1 := by
    rw [hrot_def]; simp
  rw [e, Complex.add_re, Complex.add_im, er, ei]
  rw [abs_le] at hre him
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma re_le_norm_of (rot z : ℂ) (h : ‖rot‖ ≤ 1) : (rot * z).re ≤ ‖z‖ := by
  calc (rot * z).re ≤ ‖rot * z‖ := Complex.re_le_norm _
    _ = ‖rot‖ * ‖z‖ := norm_mul _ _
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖z‖ := one_mul _

lemma re_EM (σ : ℝ) (hσ : σ < 1) (rot : ℂ) :
    (rot * eulerMaclaurinMain 10 ((σ:ℂ) + ((15:ℝ):ℂ) * I)).re =
      rot.re + (2:ℝ)^(-σ) * (rot * Eθ 2).re + (3:ℝ)^(-σ) * (rot * Eθ 3).re + (4:ℝ)^(-σ) * (rot * Eθ 4).re
      + (5:ℝ)^(-σ) * (rot * Eθ 5).re + (6:ℝ)^(-σ) * (rot * Eθ 6).re + (7:ℝ)^(-σ) * (rot * Eθ 7).re
      + (8:ℝ)^(-σ) * (rot * Eθ 8).re + (9:ℝ)^(-σ) * (rot * Eθ 9).re
      + ((10:ℝ)^(-σ) / 2) * (rot * Eθ 10).re
      - (10 * (10:ℝ)^(-σ) / ((1-σ)^2 + 225)) * ((1 - σ) * (rot * Eθ 10).re - 15 * (rot * Eθ 10).im) := by
  have hm : ∀ (c : ℝ) (X : ℂ), (rot * ((c:ℂ) * X)).re = c * (rot * X).re := by
    intro c X; rw [mul_left_comm]; exact Complex.re_ofReal_mul c _
  have ht : ∀ (c t : ℝ) (E : ℂ), (rot * ((c:ℂ) * (E * ((t:ℂ) + 15 * I)))).re =
      c * (t * (rot * E).re - 15 * (rot * E).im) := by
    intro c t E
    have : rot * ((c:ℂ) * (E * ((t:ℂ) + 15 * I))) = (c:ℂ) * ((rot * E) * ((t:ℂ) + 15 * I)) := by ring
    have h2 : ∀ Z : ℂ, (Z * ((t:ℂ) + 15 * I)).re = t * Z.re - 15 * Z.im := by
      intro Z; simp [Complex.mul_re]; ring
    rw [this, Complex.re_ofReal_mul, h2]
  rw [EM_ten σ hσ]
  rw [mul_sub, Complex.sub_re, ht]
  simp only [mul_add, Complex.add_re, mul_one, hm]



lemma mul_lb (x c cl xl xu m : ℝ) (hx0 : 0 ≤ x) (hxl : xl ≤ x) (hxu : x ≤ xu) (hc : cl ≤ c)
    (hm1 : m ≤ xl * cl) (hm2 : m ≤ xu * cl) : m ≤ x * c := by
  have h1 : x * cl ≤ x * c := mul_le_mul_of_nonneg_left hc hx0
  rcases le_total 0 cl with h | h
  · nlinarith
  · nlinarith

lemma tail_bound (A g D Au gu Dl : ℝ) (hA : 0 ≤ A) (hAu : A ≤ Au) (hg : g ≤ gu) (hgu : 0 ≤ gu)
    (hD : Dl ≤ D) (hDl : 0 < Dl) : (A / D) * g ≤ Au * gu / Dl := by
  have hD0 : 0 < D := lt_of_lt_of_le hDl hD
  have h1 : A / D ≤ Au / Dl := by
    calc A / D ≤ Au / D := by gcongr
      _ ≤ Au / Dl := by gcongr; exact hA.trans hAu
  have h2 : 0 ≤ A / D := by positivity
  rcases le_total g 0 with h | h
  · have : A / D * g ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2 h
    have : 0 ≤ Au * gu / Dl := by
      have : 0 ≤ Au := hA.trans hAu
      positivity
    linarith
  · calc A / D * g ≤ Au / Dl * gu := mul_le_mul h1 hg h (by have := hA.trans hAu; positivity)
      _ = Au * gu / Dl := by ring

lemma pw_lo (n σ b : ℝ) (hn : 1 ≤ n) (hσ : σ ≤ b) (p : ℕ) (hb : b = p / 32) (L : ℝ) (hL : 0 ≤ L)
    (h : L^32 * n^p ≤ 1) : L ≤ n ^ (-σ) := by
  have hn0 : 0 ≤ n := by linarith
  have h1 : n ^ (-b) ≤ n ^ (-σ) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  refine le_trans ?_ h1
  have hnp : 0 < n ^ p := by positivity
  have e : (n ^ (-b)) ^ (32:ℕ) = (n ^ p)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0, hb]
    have : -(p / 32 : ℝ) * ((32:ℕ):ℝ) = -(p:ℝ) := by push_cast; ring
    rw [this, Real.rpow_neg hn0, Real.rpow_natCast]
  have hpos : 0 ≤ n ^ (-b) := Real.rpow_nonneg hn0 _
  have : L ^ 32 ≤ (n ^ (-b)) ^ (32:ℕ) := by
    rw [e, ← one_div, le_div_iff₀ hnp]; exact h
  exact (pow_le_pow_iff_left₀ hL hpos (by norm_num)).mp this


lemma pw_hi (n σ a : ℝ) (hn : 1 ≤ n) (hσ : a ≤ σ) (p : ℕ) (ha : a = p / 32) (U : ℝ) (hU : 0 ≤ U)
    (h : 1 ≤ U^32 * n^p) : n ^ (-σ) ≤ U := by
  have hn0 : 0 ≤ n := by linarith
  have h1 : n ^ (-σ) ≤ n ^ (-a) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  refine le_trans h1 ?_
  have hnp : 0 < n ^ p := by positivity
  have e : (n ^ (-a)) ^ (32:ℕ) = (n ^ p)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0, ha]
    have : -(p / 32 : ℝ) * ((32:ℕ):ℝ) = -(p:ℝ) := by push_cast; ring
    rw [this, Real.rpow_neg hn0, Real.rpow_natCast]
  have hpos : 0 ≤ n ^ (-a) := Real.rpow_nonneg hn0 _
  have : (n ^ (-a)) ^ (32:ℕ) ≤ U ^ 32 := by
    rw [e, ← one_div, div_le_iff₀ hnp]; linarith
  exact (pow_le_pow_iff_left₀ hpos hU (by norm_num)).mp this

lemma norm_sq_15 (a : ℝ) : ‖(a:ℂ) + ((15:ℝ):ℂ) * I‖^2 = a^2 + 225 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

lemma lhs_bound (σ a b K x : ℝ) (ha : 0 ≤ a) (h1 : a ≤ σ) (h2 : σ ≤ b) (hK0 : 0 ≤ K)
    (hK : (b^2 + 225) * ((b+1)^2 + 225) ≤ K^2) (hx : (10:ℝ)^(-σ) ≤ x) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) ≤ K / 12 * (x / 100 + x / 10 / (a + 1)) := by
  have hs1 : (σ : ℂ) + (15 : ℝ) * I + 1 = ((σ + 1 : ℝ) : ℂ) + ((15:ℝ):ℂ) * I := by push_cast; ring
  have n1 := norm_sq_15 σ
  have n2 := norm_sq_15 (σ + 1)
  rw [hs1]
  set u := ‖(σ : ℂ) + (15 : ℝ) * I‖ with hu
  set v := ‖((σ + 1 : ℝ) : ℂ) + ((15:ℝ):ℂ) * I‖ with hv
  have hu0 : 0 ≤ u := norm_nonneg _
  have hv0 : 0 ≤ v := norm_nonneg _
  have huv : u * v ≤ K := by
    have : (u*v)^2 ≤ K^2 := by
      calc (u*v)^2 = (σ^2+225) * ((σ+1)^2+225) := by rw [mul_pow, n1, n2]
        _ ≤ (b^2+225) * ((b+1)^2+225) := by
          apply mul_le_mul <;> nlinarith
        _ ≤ K^2 := hK
    exact (pow_le_pow_iff_left₀ (mul_nonneg hu0 hv0) hK0 (by norm_num)).mp this
  have e1 : (10:ℝ) ^ (-σ - 2) = (10:ℝ)^(-σ) / 100 := by
    rw [Real.rpow_sub (by norm_num)]; norm_num
  have e2 : (10:ℝ) ^ (-σ - 1) = (10:ℝ)^(-σ) / 10 := by
    rw [Real.rpow_sub (by norm_num)]; norm_num
  rw [e1, e2]
  have hx0 : 0 ≤ (10:ℝ)^(-σ) := by positivity
  have hq : (10:ℝ)^(-σ) / 10 / (σ + 1) ≤ x / 10 / (a + 1) := by
    apply div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
  have hS : (10:ℝ)^(-σ) / 100 + (10:ℝ)^(-σ) / 10 / (σ + 1) ≤ x / 100 + x / 10 / (a + 1) := by linarith
  have hS0 : 0 ≤ (10:ℝ)^(-σ) / 100 + (10:ℝ)^(-σ) / 10 / (σ + 1) :=
    add_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
  calc u * v / 12 * ((10:ℝ)^(-σ) / 100 + (10:ℝ)^(-σ) / 10 / (σ + 1))
      ≤ K / 12 * (x / 100 + x / 10 / (a + 1)) := by
        apply mul_le_mul (by linarith) hS hS0 (div_nonneg hK0 (by norm_num))



lemma g_bound (t P Q tl tu ph qh ε gu : ℝ) (htl : tl ≤ t) (htu : t ≤ tu) (ht0 : 0 ≤ t) (hε : 0 ≤ ε)
    (hP : P ≤ ph + ε) (hQ : qh - ε ≤ Q)
    (h1 : tl * ph + tu * ε - 15 * (qh - ε) ≤ gu) (h2 : tu * ph + tu * ε - 15 * (qh - ε) ≤ gu) :
    t * P - 15 * Q ≤ gu := by
  have e1 : t * P ≤ t * (ph + ε) := mul_le_mul_of_nonneg_left hP ht0
  have e2 : t * ε ≤ tu * ε := mul_le_mul_of_nonneg_right htu hε
  have e3 : t * ph ≤ max (tl * ph) (tu * ph) := by
    rcases le_total 0 ph with h | h
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_right htu h)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_right htl h)
  have e4 : max (tl * ph) (tu * ph) ≤ gu - tu * ε + 15 * (qh - ε) := by
    apply max_le <;> linarith
  nlinarith


lemma log2_bd : (0.6931471803:ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 0.6931471808 :=
  ⟨Real.log_two_gt_d9.le, Real.log_two_lt_d9.le⟩


lemma log3_bd : 1.098612288258 ≤ Real.log 3 ∧ Real.log 3 ≤ 1.098612289045 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/3:ℝ)) (by rw [abs_of_pos (by norm_num)]; norm_num) 20
  have e : (1:ℝ) - 1/3 = 2/3 := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), abs_le] at h
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9

  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith


lemma log5_aux : Real.log (4/5) = 2 * Real.log 2 - Real.log 5 := by
  rw [Real.log_div (by norm_num) (by norm_num), show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
lemma log7_aux : Real.log (7/8) = Real.log 7 - 3 * Real.log 2 := by
  rw [Real.log_div (by norm_num) (by norm_num), show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num


lemma log5_bd : 1.609437911695 ≤ Real.log 5 ∧ Real.log 5 ≤ 1.609437913105 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/5)) (by rw [abs_of_pos (by norm_num)]; norm_num) 13
  have e : (1:ℝ) - 1/5 = 4/5 := by norm_num
  rw [e, log5_aux, abs_le] at h
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith

lemma log7_bd : 1.945910148154 ≤ Real.log 7 ∧ Real.log 7 ≤ 1.945910149921 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ((1:ℝ)/8)) (by rw [abs_of_pos (by norm_num)]; norm_num) 10
  have e : (1:ℝ) - 1/8 = 7/8 := by norm_num
  rw [e, log7_aux, abs_le] at h
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  obtain ⟨h1, h2⟩ := h
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith


lemma trig_2 : ‖Eθ 2 - (((-0.5632935954295):ℝ) + (0.826256815608:ℝ) * I)‖ ≤ 2/10^7 := by
  have h2 := log2_bd
  have h3 := log3_bd
  have h5 := log5_bd
  have h7 := log7_bd
  have hl : 0.6931471803 ≤ Real.log ((2:ℕ):ℝ) ∧ Real.log ((2:ℕ):ℝ) ≤ 0.6931471808 := by
    rw [Nat.cast_ofNat]
    constructor <;> linarith
  have := exp_neg_log_approx (Real.log ((2:ℕ):ℝ)) 0.6931471803 0.6931471808 hl.1 hl.2 2 2.1691629 0.00000000986 (-0.5632935954295) 0.826256815608
    (by norm_num [abs_le]) (by norm_num) (by norm_num) (by norm_num [tC1, tS1, abs_le]) (by norm_num [tC1, tS1, abs_le])
  unfold Eθ
  refine this.trans ?_
  norm_num


lemma trig_3 : ‖Eθ 3 - (((-0.7170601161939):ℝ) + (0.6970113268357:ℝ) * I)‖ ≤ 2/10^7 := by
  have h2 := log2_bd
  have h3 := log3_bd
  have h5 := log5_bd
  have h7 := log7_bd
  have hl : 1.098612288258 ≤ Real.log ((3:ℕ):ℝ) ∧ Real.log ((3:ℕ):ℝ) ≤ 1.098612289045 := by
    rw [Nat.cast_ofNat]
    constructor <;> linarith
  have := exp_neg_log_approx (Real.log ((3:ℕ):ℝ)) 1.098612288258 1.098612289045 hl.1 hl.2 3 2.3703716 0.00000001414 (-0.7170601161939) 0.6970113268357
    (by norm_num [abs_le]) (by norm_num) (by norm_num) (by norm_num [tC1, tS1, abs_le]) (by norm_num [tC1, tS1, abs_le])
  unfold Eθ
  refine this.trans ?_
  norm_num


lemma trig_4 : ‖Eθ 4 - (((-0.3654006440121):ℝ) + ((-0.9308503474528):ℝ) * I)‖ ≤ 2/10^7 := by
  have h2 := log2_bd
  have h3 := log3_bd
  have h5 := log5_bd
  have h7 := log7_bd
  have e : Real.log 4 = 2 * Real.log 2 := by rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have hl : 1.3862943606 ≤ Real.log ((4:ℕ):ℝ) ∧ Real.log ((4:ℕ):ℝ) ≤ 1.3862943616 := by
    rw [Nat.cast_ofNat]
    constructor <;> linarith [e]
  have := exp_neg_log_approx (Real.log ((4:ℕ):ℝ)) 1.3862943606 1.3862943616 hl.1 hl.2 3 (-1.9448595) 0.00000001254 (-0.3654006440121) (-0.9308503474528)
    (by norm_num [abs_le]) (by norm_num) (by norm_num) (by norm_num [tC1, tS1, abs_le]) (by norm_num [tC1, tS1, abs_le])
  unfold Eθ
  refine this.trans ?_
  norm_num


lemma trig_5 : ‖Eθ 5 - ((0.5477092431889:ℝ) + (0.8366687426487:ℝ) * I)‖ ≤ 2/10^7 := by
  have h2 := log2_bd
  have h3 := log3_bd
  have h5 := log5_bd
  have h7 := log7_bd
  have hl : 1.609437911695 ≤ Real.log ((5:ℕ):ℝ) ∧ Real.log ((5:ℕ):ℝ) ≤ 1.609437913105 := by
    rw [Nat.cast_ofNat]
    constructor <;> linarith
  have := exp_neg_log_approx (Real.log ((5:ℕ):ℝ)) 1.609437911695 1.609437913105 hl.1 hl.2 4 0.9911725 0.0000000533 0.5477092431889 0.8366687426487
    (by norm_num [abs_le]) (by norm_num) (by norm_num) (by norm_num [tC1, tS1, abs_le]) (by norm_num [tC1, tS1, abs_le])
  unfold Eθ
  refine this.trans ?_
  norm_num


lemma trig_6 : ‖Eθ 6 - (((-0.1719949813052):ℝ) + ((-0.9850978258047):ℝ) * I)‖ ≤ 2/10^7 := by
  have h2 := log2_bd
  have h3 := log3_bd
  have h5 := log5_bd
  have h7 := log7_bd
  have e : Real.log 6 = Real.log 2 + Real.log 3 := by rw [show (6:ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hl : 1.791759468558 ≤ Real.log ((6:ℕ):ℝ) ∧ Real.log ((6:ℕ):ℝ) ≤ 1.791759469845 := by
    rw [Nat.cast_ofNat]
    constructor <;> linarith [e]
  have := exp_neg_log_approx (Real.log ((6:ℕ):ℝ)) 1.791759468558 1.791759469845 hl.1 hl.2 4 (-1.7436508) 0.00000001896 (-0.1719949813052) (-0.9850978258047)
    (by norm_num [abs_le]) (by norm_num) (by norm_num) (by norm_num [tC1, tS1, abs_le]) (by norm_num [tC1, tS1, abs_le])
  unfold Eθ
  refine this.trans ?_
  norm_num


lemma trig_7 : ‖Eθ 7 - (((-0.6103306811647):ℝ) + (0.7921467412141:ℝ) * I)‖ ≤ 2/10^7 := by
  have h2 := log2_bd
  have h3 := log3_bd
  have h5 := log5_bd
  have h7 := log7_bd
  have hl : 1.945910148154 ≤ Real.log ((7:ℕ):ℝ) ∧ Real.log ((7:ℕ):ℝ) ≤ 1.945910149921 := by
    rw [Nat.cast_ofNat]
    constructor <;> linarith
  have := exp_neg_log_approx (Real.log ((7:ℕ):ℝ)) 1.945910148154 1.945910149921 hl.1 hl.2 5 2.2272743 0.00000001359 (-0.6103306811647) 0.7921467412141
    (by norm_num [abs_le]) (by norm_num) (by norm_num) (by norm_num [tC1, tS1, abs_le]) (by norm_num [tC1, tS1, abs_le])
  unfold Eθ
  refine this.trans ?_
  norm_num


lemma trig_8 : ‖Eθ 8 - ((0.9749492864381:ℝ) + (0.2224272664803:ℝ) * I)‖ ≤ 2/10^7 := by
  have h2 := log2_bd
  have h3 := log3_bd
  have h5 := log5_bd
  have h7 := log7_bd
  have e : Real.log 8 = 3 * Real.log 2 := by rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
  have hl : 2.0794415409 ≤ Real.log ((8:ℕ):ℝ) ∧ Real.log ((8:ℕ):ℝ) ≤ 2.0794415424 := by
    rw [Nat.cast_ofNat]
    constructor <;> linarith [e]
  have := exp_neg_log_approx (Real.log ((8:ℕ):ℝ)) 2.0794415409 2.0794415424 hl.1 hl.2 5 0.2243034 0.0000000224 0.9749492864381 0.2224272664803
    (by norm_num [abs_le]) (by norm_num) (by norm_num) (by norm_num [tC1, tS1, abs_le]) (by norm_num [tC1, tS1, abs_le])
  unfold Eθ
  refine this.trans ?_
  norm_num


lemma trig_9 : ‖Eθ 9 - ((0.0283504276599:ℝ) + ((-0.9995980458421):ℝ) * I)‖ ≤ 2/10^7 := by
  have h2 := log2_bd
  have h3 := log3_bd
  have h5 := log5_bd
  have h7 := log7_bd
  have e : Real.log 9 = 2 * Real.log 3 := by rw [show (9:ℝ) = 3^2 by norm_num, Real.log_pow]; norm_num
  have hl : 2.197224576516 ≤ Real.log ((9:ℕ):ℝ) ∧ Real.log ((9:ℕ):ℝ) ≤ 2.19722457809 := by
    rw [Nat.cast_ofNat]
    constructor <;> linarith [e]
  have := exp_neg_log_approx (Real.log ((9:ℕ):ℝ)) 2.197224576516 2.19722457809 hl.1 hl.2 5 (-1.5424421) 0.00000003546 0.0283504276599 (-0.9995980458421)
    (by norm_num [abs_le]) (by norm_num) (by norm_num) (by norm_num [tC1, tS1, abs_le]) (by norm_num [tC1, tS1, abs_le])
  unfold Eθ
  refine this.trans ?_
  norm_num


lemma trig_10 : ‖Eθ 10 - (((-0.9998243594199):ℝ) + ((-0.0187416559615):ℝ) * I)‖ ≤ 2/10^7 := by
  have h2 := log2_bd
  have h3 := log3_bd
  have h5 := log5_bd
  have h7 := log7_bd
  have e : Real.log 10 = Real.log 2 + Real.log 5 := by rw [show (10:ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hl : 2.302585091995 ≤ Real.log ((10:ℕ):ℝ) ∧ Real.log ((10:ℕ):ℝ) ≤ 2.302585093905 := by
    rw [Nat.cast_ofNat]
    constructor <;> linarith [e]
  have := exp_neg_log_approx (Real.log ((10:ℕ):ℝ)) 2.302585091995 2.302585093905 hl.1 hl.2 5 (-3.1228499) 0.00000005598 (-0.9998243594199) (-0.0187416559615)
    (by norm_num [abs_le]) (by norm_num) (by norm_num) (by norm_num [tC1, tS1, abs_le]) (by norm_num [tC1, tS1, abs_le])
  unfold Eθ
  refine this.trans ?_
  norm_num

lemma xlo_2_17 (σ : ℝ) (h : σ ≤ 17/32) : 0.69195494 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_18 (σ : ℝ) (h : σ ≤ 18/32) : 0.67712777 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_19 (σ : ℝ) (h : σ ≤ 19/32) : 0.66261832 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_20 (σ : ℝ) (h : σ ≤ 20/32) : 0.64841977 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_21 (σ : ℝ) (h : σ ≤ 21/32) : 0.63452547 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_22 (σ : ℝ) (h : σ ≤ 22/32) : 0.6209289 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_23 (σ : ℝ) (h : σ ≤ 23/32) : 0.60762367 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_24 (σ : ℝ) (h : σ ≤ 24/32) : 0.59460355 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_25 (σ : ℝ) (h : σ ≤ 25/32) : 0.58186242 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_26 (σ : ℝ) (h : σ ≤ 26/32) : 0.56939431 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_27 (σ : ℝ) (h : σ ≤ 27/32) : 0.55719337 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_28 (σ : ℝ) (h : σ ≤ 28/32) : 0.54525386 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_29 (σ : ℝ) (h : σ ≤ 29/32) : 0.5335702 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_30 (σ : ℝ) (h : σ ≤ 30/32) : 0.52213689 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_31 (σ : ℝ) (h : σ ≤ 31/32) : 0.51094857 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_2_32 (σ : ℝ) (h : σ ≤ 32/32) : 0.5 ≤ (2:ℝ) ^ (-σ) :=
  pw_lo 2 σ (32/32) (by norm_num) h 32 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_16 (σ : ℝ) (h : 16/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.70710679 :=
  pw_hi 2 σ (16/32) (by norm_num) h 16 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_17 (σ : ℝ) (h : 17/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.69195495 :=
  pw_hi 2 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_18 (σ : ℝ) (h : 18/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.67712778 :=
  pw_hi 2 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_19 (σ : ℝ) (h : 19/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.66261833 :=
  pw_hi 2 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_20 (σ : ℝ) (h : 20/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.64841978 :=
  pw_hi 2 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_21 (σ : ℝ) (h : 21/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.63452548 :=
  pw_hi 2 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_22 (σ : ℝ) (h : 22/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.62092891 :=
  pw_hi 2 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_23 (σ : ℝ) (h : 23/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.60762368 :=
  pw_hi 2 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_24 (σ : ℝ) (h : 24/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.59460356 :=
  pw_hi 2 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_25 (σ : ℝ) (h : 25/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.58186243 :=
  pw_hi 2 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_26 (σ : ℝ) (h : 26/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.56939432 :=
  pw_hi 2 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_27 (σ : ℝ) (h : 27/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.55719338 :=
  pw_hi 2 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_28 (σ : ℝ) (h : 28/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.54525387 :=
  pw_hi 2 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_29 (σ : ℝ) (h : 29/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.53357021 :=
  pw_hi 2 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_30 (σ : ℝ) (h : 30/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.5221369 :=
  pw_hi 2 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xhi_2_31 (σ : ℝ) (h : 31/32 ≤ σ) : (2:ℝ) ^ (-σ) ≤ 0.51094858 :=
  pw_hi 2 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_17 (σ : ℝ) (h : σ ≤ 17/32) : 0.55786528 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_18 (σ : ℝ) (h : σ ≤ 18/32) : 0.53903789 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_19 (σ : ℝ) (h : σ ≤ 19/32) : 0.5208459 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_20 (σ : ℝ) (h : σ ≤ 20/32) : 0.50326788 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_21 (σ : ℝ) (h : σ ≤ 21/32) : 0.48628309 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_22 (σ : ℝ) (h : σ ≤ 22/32) : 0.46987153 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_23 (σ : ℝ) (h : σ ≤ 23/32) : 0.45401384 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_24 (σ : ℝ) (h : σ ≤ 24/32) : 0.43869133 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_25 (σ : ℝ) (h : σ ≤ 25/32) : 0.42388594 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_26 (σ : ℝ) (h : σ ≤ 26/32) : 0.40958022 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_27 (σ : ℝ) (h : σ ≤ 27/32) : 0.3957573 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_28 (σ : ℝ) (h : σ ≤ 28/32) : 0.38240089 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_29 (σ : ℝ) (h : σ ≤ 29/32) : 0.36949525 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_30 (σ : ℝ) (h : σ ≤ 30/32) : 0.35702516 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_31 (σ : ℝ) (h : σ ≤ 31/32) : 0.34497592 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_3_32 (σ : ℝ) (h : σ ≤ 32/32) : 0.33333333 ≤ (3:ℝ) ^ (-σ) :=
  pw_lo 3 σ (32/32) (by norm_num) h 32 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_16 (σ : ℝ) (h : 16/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.57735027 :=
  pw_hi 3 σ (16/32) (by norm_num) h 16 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_17 (σ : ℝ) (h : 17/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.55786529 :=
  pw_hi 3 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_18 (σ : ℝ) (h : 18/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.5390379 :=
  pw_hi 3 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_19 (σ : ℝ) (h : 19/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.52084591 :=
  pw_hi 3 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_20 (σ : ℝ) (h : 20/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.50326789 :=
  pw_hi 3 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_21 (σ : ℝ) (h : 21/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.4862831 :=
  pw_hi 3 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_22 (σ : ℝ) (h : 22/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.46987154 :=
  pw_hi 3 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_23 (σ : ℝ) (h : 23/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.45401385 :=
  pw_hi 3 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_24 (σ : ℝ) (h : 24/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.43869134 :=
  pw_hi 3 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_25 (σ : ℝ) (h : 25/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.42388595 :=
  pw_hi 3 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_26 (σ : ℝ) (h : 26/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.40958023 :=
  pw_hi 3 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_27 (σ : ℝ) (h : 27/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.39575731 :=
  pw_hi 3 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_28 (σ : ℝ) (h : 28/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.3824009 :=
  pw_hi 3 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_29 (σ : ℝ) (h : 29/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.36949526 :=
  pw_hi 3 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_30 (σ : ℝ) (h : 30/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.35702517 :=
  pw_hi 3 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xhi_3_31 (σ : ℝ) (h : 31/32 ≤ σ) : (3:ℝ) ^ (-σ) ≤ 0.34497593 :=
  pw_hi 3 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_17 (σ : ℝ) (h : σ ≤ 17/32) : 0.47880164 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_18 (σ : ℝ) (h : σ ≤ 18/32) : 0.45850202 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_19 (σ : ℝ) (h : σ ≤ 19/32) : 0.43906304 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_20 (σ : ℝ) (h : σ ≤ 20/32) : 0.4204482 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_21 (σ : ℝ) (h : σ ≤ 21/32) : 0.40262258 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_22 (σ : ℝ) (h : σ ≤ 22/32) : 0.3855527 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_23 (σ : ℝ) (h : σ ≤ 23/32) : 0.36920653 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_24 (σ : ℝ) (h : σ ≤ 24/32) : 0.35355339 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_25 (σ : ℝ) (h : σ ≤ 25/32) : 0.33856388 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_26 (σ : ℝ) (h : σ ≤ 26/32) : 0.32420988 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_27 (σ : ℝ) (h : σ ≤ 27/32) : 0.31046445 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_28 (σ : ℝ) (h : σ ≤ 28/32) : 0.29730177 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_29 (σ : ℝ) (h : σ ≤ 29/32) : 0.28469715 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_30 (σ : ℝ) (h : σ ≤ 30/32) : 0.27262693 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_31 (σ : ℝ) (h : σ ≤ 31/32) : 0.26106844 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_4_32 (σ : ℝ) (h : σ ≤ 32/32) : 0.25 ≤ (4:ℝ) ^ (-σ) :=
  pw_lo 4 σ (32/32) (by norm_num) h 32 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_16 (σ : ℝ) (h : 16/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.5 :=
  pw_hi 4 σ (16/32) (by norm_num) h 16 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_17 (σ : ℝ) (h : 17/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.47880165 :=
  pw_hi 4 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_18 (σ : ℝ) (h : 18/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.45850203 :=
  pw_hi 4 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_19 (σ : ℝ) (h : 19/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.43906305 :=
  pw_hi 4 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_20 (σ : ℝ) (h : 20/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.42044821 :=
  pw_hi 4 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_21 (σ : ℝ) (h : 21/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.40262259 :=
  pw_hi 4 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_22 (σ : ℝ) (h : 22/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.38555271 :=
  pw_hi 4 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_23 (σ : ℝ) (h : 23/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.36920654 :=
  pw_hi 4 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_24 (σ : ℝ) (h : 24/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.3535534 :=
  pw_hi 4 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_25 (σ : ℝ) (h : 25/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.33856389 :=
  pw_hi 4 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_26 (σ : ℝ) (h : 26/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.32420989 :=
  pw_hi 4 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_27 (σ : ℝ) (h : 27/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.31046446 :=
  pw_hi 4 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_28 (σ : ℝ) (h : 28/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.29730178 :=
  pw_hi 4 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_29 (σ : ℝ) (h : 29/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.28469716 :=
  pw_hi 4 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_30 (σ : ℝ) (h : 30/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.27262694 :=
  pw_hi 4 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xhi_4_31 (σ : ℝ) (h : 31/32 ≤ σ) : (4:ℝ) ^ (-σ) ≤ 0.26106845 :=
  pw_hi 4 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_17 (σ : ℝ) (h : σ ≤ 17/32) : 0.42527728 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_18 (σ : ℝ) (h : σ ≤ 18/32) : 0.40441697 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_19 (σ : ℝ) (h : σ ≤ 19/32) : 0.38457988 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_20 (σ : ℝ) (h : σ ≤ 20/32) : 0.36571581 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_21 (σ : ℝ) (h : σ ≤ 21/32) : 0.34777706 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_22 (σ : ℝ) (h : σ ≤ 22/32) : 0.33071822 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_23 (σ : ℝ) (h : σ ≤ 23/32) : 0.31449613 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_24 (σ : ℝ) (h : σ ≤ 24/32) : 0.29906975 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_25 (σ : ℝ) (h : σ ≤ 25/32) : 0.28440006 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_26 (σ : ℝ) (h : σ ≤ 26/32) : 0.27044992 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_27 (σ : ℝ) (h : σ ≤ 27/32) : 0.25718406 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_28 (σ : ℝ) (h : σ ≤ 28/32) : 0.2445689 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_29 (σ : ℝ) (h : σ ≤ 29/32) : 0.23257253 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_30 (σ : ℝ) (h : σ ≤ 30/32) : 0.2211646 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_31 (σ : ℝ) (h : σ ≤ 31/32) : 0.21031623 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_5_32 (σ : ℝ) (h : σ ≤ 32/32) : 0.2 ≤ (5:ℝ) ^ (-σ) :=
  pw_lo 5 σ (32/32) (by norm_num) h 32 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_16 (σ : ℝ) (h : 16/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.4472136 :=
  pw_hi 5 σ (16/32) (by norm_num) h 16 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_17 (σ : ℝ) (h : 17/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.42527729 :=
  pw_hi 5 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_18 (σ : ℝ) (h : 18/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.40441698 :=
  pw_hi 5 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_19 (σ : ℝ) (h : 19/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.38457989 :=
  pw_hi 5 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_20 (σ : ℝ) (h : 20/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.36571582 :=
  pw_hi 5 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_21 (σ : ℝ) (h : 21/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.34777707 :=
  pw_hi 5 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_22 (σ : ℝ) (h : 22/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.33071823 :=
  pw_hi 5 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_23 (σ : ℝ) (h : 23/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.31449614 :=
  pw_hi 5 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_24 (σ : ℝ) (h : 24/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.29906976 :=
  pw_hi 5 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_25 (σ : ℝ) (h : 25/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.28440007 :=
  pw_hi 5 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_26 (σ : ℝ) (h : 26/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.27044993 :=
  pw_hi 5 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_27 (σ : ℝ) (h : 27/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.25718407 :=
  pw_hi 5 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_28 (σ : ℝ) (h : 28/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.24456891 :=
  pw_hi 5 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_29 (σ : ℝ) (h : 29/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.23257254 :=
  pw_hi 5 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_30 (σ : ℝ) (h : 30/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.22116461 :=
  pw_hi 5 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xhi_5_31 (σ : ℝ) (h : 31/32 ≤ σ) : (5:ℝ) ^ (-σ) ≤ 0.21031624 :=
  pw_hi 5 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_17 (σ : ℝ) (h : σ ≤ 17/32) : 0.38601763 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_18 (σ : ℝ) (h : σ ≤ 18/32) : 0.36499752 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_19 (σ : ℝ) (h : σ ≤ 19/32) : 0.34512204 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_20 (σ : ℝ) (h : σ ≤ 20/32) : 0.32632884 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_21 (σ : ℝ) (h : σ ≤ 21/32) : 0.30855901 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_22 (σ : ℝ) (h : σ ≤ 22/32) : 0.29175681 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_23 (σ : ℝ) (h : σ ≤ 23/32) : 0.27586956 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_24 (σ : ℝ) (h : σ ≤ 24/32) : 0.26084743 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_25 (σ : ℝ) (h : σ ≤ 25/32) : 0.2466433 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_26 (σ : ℝ) (h : σ ≤ 26/32) : 0.23321265 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_27 (σ : ℝ) (h : σ ≤ 27/32) : 0.22051334 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_28 (σ : ℝ) (h : σ ≤ 28/32) : 0.20850556 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_29 (σ : ℝ) (h : σ ≤ 29/32) : 0.19715165 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_30 (σ : ℝ) (h : σ ≤ 30/32) : 0.186416 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_31 (σ : ℝ) (h : σ ≤ 31/32) : 0.17626495 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_6_32 (σ : ℝ) (h : σ ≤ 32/32) : 0.16666666 ≤ (6:ℝ) ^ (-σ) :=
  pw_lo 6 σ (32/32) (by norm_num) h 32 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_16 (σ : ℝ) (h : 16/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.4082483 :=
  pw_hi 6 σ (16/32) (by norm_num) h 16 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_17 (σ : ℝ) (h : 17/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.38601764 :=
  pw_hi 6 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_18 (σ : ℝ) (h : 18/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.36499753 :=
  pw_hi 6 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_19 (σ : ℝ) (h : 19/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.34512205 :=
  pw_hi 6 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_20 (σ : ℝ) (h : 20/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.32632885 :=
  pw_hi 6 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_21 (σ : ℝ) (h : 21/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.30855902 :=
  pw_hi 6 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_22 (σ : ℝ) (h : 22/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.29175682 :=
  pw_hi 6 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_23 (σ : ℝ) (h : 23/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.27586957 :=
  pw_hi 6 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_24 (σ : ℝ) (h : 24/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.26084744 :=
  pw_hi 6 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_25 (σ : ℝ) (h : 25/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.24664331 :=
  pw_hi 6 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_26 (σ : ℝ) (h : 26/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.23321266 :=
  pw_hi 6 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_27 (σ : ℝ) (h : 27/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.22051335 :=
  pw_hi 6 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_28 (σ : ℝ) (h : 28/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.20850557 :=
  pw_hi 6 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_29 (σ : ℝ) (h : 29/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.19715166 :=
  pw_hi 6 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_30 (σ : ℝ) (h : 30/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.18641601 :=
  pw_hi 6 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xhi_6_31 (σ : ℝ) (h : 31/32 ≤ σ) : (6:ℝ) ^ (-σ) ≤ 0.17626496 :=
  pw_hi 6 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_17 (σ : ℝ) (h : σ ≤ 17/32) : 0.35566543 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_18 (σ : ℝ) (h : σ ≤ 18/32) : 0.33468199 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_19 (σ : ℝ) (h : σ ≤ 19/32) : 0.31493653 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_20 (σ : ℝ) (h : σ ≤ 20/32) : 0.296356 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_21 (σ : ℝ) (h : σ ≤ 21/32) : 0.27887167 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_22 (σ : ℝ) (h : σ ≤ 22/32) : 0.26241889 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_23 (σ : ℝ) (h : σ ≤ 23/32) : 0.24693678 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_24 (σ : ℝ) (h : σ ≤ 24/32) : 0.23236808 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_25 (σ : ℝ) (h : σ ≤ 25/32) : 0.21865889 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_26 (σ : ℝ) (h : σ ≤ 26/32) : 0.20575852 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_27 (σ : ℝ) (h : σ ≤ 27/32) : 0.19361924 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_28 (σ : ℝ) (h : σ ≤ 28/32) : 0.18219615 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_29 (σ : ℝ) (h : σ ≤ 29/32) : 0.171447 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_30 (σ : ℝ) (h : σ ≤ 30/32) : 0.16133202 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_31 (σ : ℝ) (h : σ ≤ 31/32) : 0.1518138 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_7_32 (σ : ℝ) (h : σ ≤ 32/32) : 0.14285714 ≤ (7:ℝ) ^ (-σ) :=
  pw_lo 7 σ (32/32) (by norm_num) h 32 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_16 (σ : ℝ) (h : 16/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.37796448 :=
  pw_hi 7 σ (16/32) (by norm_num) h 16 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_17 (σ : ℝ) (h : 17/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.35566544 :=
  pw_hi 7 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_18 (σ : ℝ) (h : 18/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.334682 :=
  pw_hi 7 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_19 (σ : ℝ) (h : 19/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.31493654 :=
  pw_hi 7 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_20 (σ : ℝ) (h : 20/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.29635601 :=
  pw_hi 7 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_21 (σ : ℝ) (h : 21/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.27887168 :=
  pw_hi 7 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_22 (σ : ℝ) (h : 22/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.2624189 :=
  pw_hi 7 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_23 (σ : ℝ) (h : 23/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.24693679 :=
  pw_hi 7 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_24 (σ : ℝ) (h : 24/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.23236809 :=
  pw_hi 7 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_25 (σ : ℝ) (h : 25/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.2186589 :=
  pw_hi 7 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_26 (σ : ℝ) (h : 26/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.20575853 :=
  pw_hi 7 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_27 (σ : ℝ) (h : 27/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.19361925 :=
  pw_hi 7 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_28 (σ : ℝ) (h : 28/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.18219616 :=
  pw_hi 7 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_29 (σ : ℝ) (h : 29/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.17144701 :=
  pw_hi 7 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_30 (σ : ℝ) (h : 30/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.16133203 :=
  pw_hi 7 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xhi_7_31 (σ : ℝ) (h : 31/32 ≤ σ) : (7:ℝ) ^ (-σ) ≤ 0.15181381 :=
  pw_hi 7 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_17 (σ : ℝ) (h : σ ≤ 17/32) : 0.33130916 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_18 (σ : ℝ) (h : σ ≤ 18/32) : 0.31046445 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_19 (σ : ℝ) (h : σ ≤ 19/32) : 0.29093121 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_20 (σ : ℝ) (h : σ ≤ 20/32) : 0.27262693 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_21 (σ : ℝ) (h : σ ≤ 21/32) : 0.25547428 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_22 (σ : ℝ) (h : σ ≤ 22/32) : 0.23940082 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_23 (σ : ℝ) (h : σ ≤ 23/32) : 0.22433863 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_24 (σ : ℝ) (h : σ ≤ 24/32) : 0.2102241 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_25 (σ : ℝ) (h : σ ≤ 25/32) : 0.1969976 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_26 (σ : ℝ) (h : σ ≤ 26/32) : 0.18460326 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_27 (σ : ℝ) (h : σ ≤ 27/32) : 0.17298873 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_28 (σ : ℝ) (h : σ ≤ 28/32) : 0.16210494 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_29 (σ : ℝ) (h : σ ≤ 29/32) : 0.15190591 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_30 (σ : ℝ) (h : σ ≤ 30/32) : 0.14234857 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_31 (σ : ℝ) (h : σ ≤ 31/32) : 0.13339255 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_8_32 (σ : ℝ) (h : σ ≤ 32/32) : 0.125 ≤ (8:ℝ) ^ (-σ) :=
  pw_lo 8 σ (32/32) (by norm_num) h 32 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_16 (σ : ℝ) (h : 16/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.3535534 :=
  pw_hi 8 σ (16/32) (by norm_num) h 16 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_17 (σ : ℝ) (h : 17/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.33130917 :=
  pw_hi 8 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_18 (σ : ℝ) (h : 18/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.31046446 :=
  pw_hi 8 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_19 (σ : ℝ) (h : 19/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.29093122 :=
  pw_hi 8 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_20 (σ : ℝ) (h : 20/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.27262694 :=
  pw_hi 8 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_21 (σ : ℝ) (h : 21/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.25547429 :=
  pw_hi 8 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_22 (σ : ℝ) (h : 22/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.23940083 :=
  pw_hi 8 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_23 (σ : ℝ) (h : 23/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.22433864 :=
  pw_hi 8 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_24 (σ : ℝ) (h : 24/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.21022411 :=
  pw_hi 8 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_25 (σ : ℝ) (h : 25/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.19699761 :=
  pw_hi 8 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_26 (σ : ℝ) (h : 26/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.18460327 :=
  pw_hi 8 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_27 (σ : ℝ) (h : 27/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.17298874 :=
  pw_hi 8 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_28 (σ : ℝ) (h : 28/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.16210495 :=
  pw_hi 8 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_29 (σ : ℝ) (h : 29/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.15190592 :=
  pw_hi 8 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_30 (σ : ℝ) (h : 30/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.14234858 :=
  pw_hi 8 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xhi_8_31 (σ : ℝ) (h : 31/32 ≤ σ) : (8:ℝ) ^ (-σ) ≤ 0.13339256 :=
  pw_hi 8 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_17 (σ : ℝ) (h : σ ≤ 17/32) : 0.31121367 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_18 (σ : ℝ) (h : σ ≤ 18/32) : 0.29056184 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_19 (σ : ℝ) (h : σ ≤ 19/32) : 0.27128045 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_20 (σ : ℝ) (h : σ ≤ 20/32) : 0.25327856 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_21 (σ : ℝ) (h : σ ≤ 21/32) : 0.23647125 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_22 (σ : ℝ) (h : σ ≤ 22/32) : 0.22077926 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_23 (σ : ℝ) (h : σ ≤ 23/32) : 0.20612857 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_24 (σ : ℝ) (h : σ ≤ 24/32) : 0.19245008 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_25 (σ : ℝ) (h : σ ≤ 25/32) : 0.17967929 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_26 (σ : ℝ) (h : σ ≤ 26/32) : 0.16775596 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_27 (σ : ℝ) (h : σ ≤ 27/32) : 0.15662384 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_28 (σ : ℝ) (h : σ ≤ 28/32) : 0.14623044 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_29 (σ : ℝ) (h : σ ≤ 29/32) : 0.13652674 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_30 (σ : ℝ) (h : σ ≤ 30/32) : 0.12746696 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_31 (σ : ℝ) (h : σ ≤ 31/32) : 0.11900838 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_9_32 (σ : ℝ) (h : σ ≤ 32/32) : 0.11111111 ≤ (9:ℝ) ^ (-σ) :=
  pw_lo 9 σ (32/32) (by norm_num) h 32 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_16 (σ : ℝ) (h : 16/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.33333334 :=
  pw_hi 9 σ (16/32) (by norm_num) h 16 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_17 (σ : ℝ) (h : 17/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.31121368 :=
  pw_hi 9 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_18 (σ : ℝ) (h : 18/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.29056185 :=
  pw_hi 9 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_19 (σ : ℝ) (h : 19/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.27128046 :=
  pw_hi 9 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_20 (σ : ℝ) (h : 20/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.25327857 :=
  pw_hi 9 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_21 (σ : ℝ) (h : 21/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.23647126 :=
  pw_hi 9 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_22 (σ : ℝ) (h : 22/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.22077927 :=
  pw_hi 9 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_23 (σ : ℝ) (h : 23/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.20612858 :=
  pw_hi 9 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_24 (σ : ℝ) (h : 24/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.19245009 :=
  pw_hi 9 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_25 (σ : ℝ) (h : 25/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.1796793 :=
  pw_hi 9 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_26 (σ : ℝ) (h : 26/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.16775597 :=
  pw_hi 9 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_27 (σ : ℝ) (h : 27/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.15662385 :=
  pw_hi 9 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_28 (σ : ℝ) (h : 28/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.14623045 :=
  pw_hi 9 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_29 (σ : ℝ) (h : 29/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.13652675 :=
  pw_hi 9 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_30 (σ : ℝ) (h : 30/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.12746697 :=
  pw_hi 9 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xhi_9_31 (σ : ℝ) (h : 31/32 ≤ σ) : (9:ℝ) ^ (-σ) ≤ 0.11900839 :=
  pw_hi 9 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_17 (σ : ℝ) (h : σ ≤ 17/32) : 0.29427271 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_18 (σ : ℝ) (h : σ ≤ 18/32) : 0.27384196 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_19 (σ : ℝ) (h : σ ≤ 19/32) : 0.25482967 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_20 (σ : ℝ) (h : σ ≤ 20/32) : 0.23713737 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_21 (σ : ℝ) (h : σ ≤ 21/32) : 0.2206734 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_22 (σ : ℝ) (h : σ ≤ 22/32) : 0.2053525 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_23 (σ : ℝ) (h : σ ≤ 23/32) : 0.19109529 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_24 (σ : ℝ) (h : σ ≤ 24/32) : 0.17782794 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_25 (σ : ℝ) (h : σ ≤ 25/32) : 0.1654817 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_26 (σ : ℝ) (h : σ ≤ 26/32) : 0.15399265 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_27 (σ : ℝ) (h : σ ≤ 27/32) : 0.14330125 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_28 (σ : ℝ) (h : σ ≤ 28/32) : 0.13335214 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_29 (σ : ℝ) (h : σ ≤ 29/32) : 0.12409377 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_30 (σ : ℝ) (h : σ ≤ 30/32) : 0.11547819 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_31 (σ : ℝ) (h : σ ≤ 31/32) : 0.10746078 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma xlo_10_32 (σ : ℝ) (h : σ ≤ 32/32) : 0.1 ≤ (10:ℝ) ^ (-σ) :=
  pw_lo 10 σ (32/32) (by norm_num) h 32 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_16 (σ : ℝ) (h : 16/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.31622777 :=
  pw_hi 10 σ (16/32) (by norm_num) h 16 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_17 (σ : ℝ) (h : 17/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.29427272 :=
  pw_hi 10 σ (17/32) (by norm_num) h 17 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_18 (σ : ℝ) (h : 18/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.27384197 :=
  pw_hi 10 σ (18/32) (by norm_num) h 18 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_19 (σ : ℝ) (h : 19/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.25482968 :=
  pw_hi 10 σ (19/32) (by norm_num) h 19 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_20 (σ : ℝ) (h : 20/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.23713738 :=
  pw_hi 10 σ (20/32) (by norm_num) h 20 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_21 (σ : ℝ) (h : 21/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.22067341 :=
  pw_hi 10 σ (21/32) (by norm_num) h 21 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_22 (σ : ℝ) (h : 22/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.20535251 :=
  pw_hi 10 σ (22/32) (by norm_num) h 22 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_23 (σ : ℝ) (h : 23/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.1910953 :=
  pw_hi 10 σ (23/32) (by norm_num) h 23 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_24 (σ : ℝ) (h : 24/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.17782795 :=
  pw_hi 10 σ (24/32) (by norm_num) h 24 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_25 (σ : ℝ) (h : 25/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.16548171 :=
  pw_hi 10 σ (25/32) (by norm_num) h 25 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_26 (σ : ℝ) (h : 26/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.15399266 :=
  pw_hi 10 σ (26/32) (by norm_num) h 26 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_27 (σ : ℝ) (h : 27/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.14330126 :=
  pw_hi 10 σ (27/32) (by norm_num) h 27 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_28 (σ : ℝ) (h : 28/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.13335215 :=
  pw_hi 10 σ (28/32) (by norm_num) h 28 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_29 (σ : ℝ) (h : 29/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.12409378 :=
  pw_hi 10 σ (29/32) (by norm_num) h 29 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_30 (σ : ℝ) (h : 30/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.1154782 :=
  pw_hi 10 σ (30/32) (by norm_num) h 30 rfl _ (by norm_num) (by norm_num)

lemma xhi_10_31 (σ : ℝ) (h : 31/32 ≤ σ) : (10:ℝ) ^ (-σ) ≤ 0.10746079 :=
  pw_hi 10 σ (31/32) (by norm_num) h 31 rfl _ (by norm_num) (by norm_num)

lemma sub_0 (σ : ℝ) (h1 : (16:ℝ)/32 ≤ σ) (h2 : σ ≤ (17:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.21233:ℝ)^2 + ((-0.97719):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.21233:ℝ) ((-0.97719):ℝ) hr
  have hre := re_EM σ hσ1 ((0.21233:ℝ) + ((-0.97719):ℝ) * I)
  have hle := re_le_norm_of (((0.21233:ℝ):ℂ) + (((-0.97719):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.21233) ((-0.97719)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_17 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_16 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.21233) ((-0.97719)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_17 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_16 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.21233) ((-0.97719)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_17 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_16 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.21233) ((-0.97719)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_17 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_16 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.21233) ((-0.97719)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_17 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_16 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.21233) ((-0.97719)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_17 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_16 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.21233) ((-0.97719)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_17 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_16 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.21233) ((-0.97719)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_17 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_16 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.21233) ((-0.97719)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_17 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_16 σ (by exact_mod_cast h1)
  have hrr : (((0.21233:ℝ):ℂ) + (((-0.97719):ℝ):ℂ) * I).re = 0.21233 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.4759304609) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.2950320317) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.4936016849)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.3971576197) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.407900325)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.2292214474) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1405958402) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.3235925959)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.29427271/2) (0.31622777/2) ((-0.036462179)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 17/32) (1 - 16/32) (0.21233 * (-0.9998243594199) - (-0.97719) * (-0.0187416559615)) (0.21233 * (-0.0187416559615) + (-0.97719) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.31622777) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (16/32) (17/32) 226.3112 0.31622777 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (226.3112:ℝ) / 12 * (0.31622777 / 100 + 0.31622777 / 10 / (16/32 + 1)) ≤ 0.4572264946 := by norm_num
  have hTu : (10:ℝ) * 0.31622777 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_1 (σ : ℝ) (h1 : (17:ℝ)/32 ≤ σ) (h2 : σ ≤ (18:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.24713:ℝ)^2 + ((-0.96898):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.24713:ℝ) ((-0.96898):ℝ) hr
  have hre := re_EM σ hσ1 ((0.24713:ℝ) + ((-0.96898):ℝ) * I)
  have hle := re_le_norm_of (((0.24713:ℝ):ℂ) + (((-0.96898):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.24713) ((-0.96898)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_18 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_17 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.24713) ((-0.96898)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_18 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_17 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.24713) ((-0.96898)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_18 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_17 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.24713) ((-0.96898)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_18 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_17 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.24713) ((-0.96898)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_18 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_17 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.24713) ((-0.96898)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_18 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_17 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.24713) ((-0.96898)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_18 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_17 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.24713) ((-0.96898)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_18 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_17 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.24713) ((-0.96898)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_18 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_17 σ (by exact_mod_cast h1)
  have hrr : (((0.24713:ℝ):ℂ) + (((-0.96898):ℝ):ℂ) * I).re = 0.24713 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.4478654318) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.2685393886) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.4751038797)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.3826069502) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.3848771166)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.2064128174) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1417166487) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.2992582426)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.27384196/2) (0.29427272/2) ((-0.0390274905)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 18/32) (1 - 17/32) (0.24713 * (-0.9998243594199) - (-0.96898) * (-0.0187416559615)) (0.24713 * (-0.0187416559615) + (-0.96898) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.29427272) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (17/32) (18/32) 226.3765 0.29427272 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (226.3765:ℝ) / 12 * (0.29427272 / 100 + 0.29427272 / 10 / (17/32 + 1)) ≤ 0.4180520762 := by norm_num
  have hTu : (10:ℝ) * 0.29427272 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_2 (σ : ℝ) (h1 : (18:ℝ)/32 ≤ σ) (h2 : σ ≤ (19:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.28163:ℝ)^2 + ((-0.95952):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.28163:ℝ) ((-0.95952):ℝ) hr
  have hre := re_EM σ hσ1 ((0.28163:ℝ) + ((-0.95952):ℝ) * I)
  have hle := re_le_norm_of (((0.28163:ℝ):ℂ) + (((-0.95952):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.28163) ((-0.95952)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_19 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_18 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.28163) ((-0.95952)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_19 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_18 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.28163) ((-0.95952)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_19 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_18 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.28163) ((-0.95952)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_19 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_18 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.28163) ((-0.95952)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_19 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_18 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.28163) ((-0.95952)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_19 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_18 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.28163) ((-0.95952)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_19 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_18 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.28163) ((-0.95952)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_19 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_18 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.28163) ((-0.95952)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_19 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_18 σ (by exact_mod_cast h1)
  have hrr : (((0.28163:ℝ):ℂ) + (((-0.95952):ℝ):ℂ) * I).re = 0.28163 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.4202122388) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.243157152) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.4567035599)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.3680627687) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.3626835232)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.1852434659) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1419739004) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.2763679577)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.25482967/2) (0.27384197/2) ((-0.0410165608)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 19/32) (1 - 18/32) (0.28163 * (-0.9998243594199) - (-0.95952) * (-0.0187416559615)) (0.28163 * (-0.0187416559615) + (-0.95952) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.27384197) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (18/32) (19/32) 226.4437 0.27384197 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (226.4437:ℝ) / 12 * (0.27384197 / 100 + 0.27384197 / 10 / (18/32 + 1)) ≤ 0.3823936983 := by norm_num
  have hTu : (10:ℝ) * 0.27384197 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_3 (σ : ℝ) (h1 : (19:ℝ)/32 ≤ σ) (h2 : σ ≤ (20:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.3157:ℝ)^2 + ((-0.94885):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.3157:ℝ) ((-0.94885):ℝ) hr
  have hre := re_EM σ hσ1 ((0.3157:ℝ) + ((-0.94885):ℝ) * I)
  have hle := re_le_norm_of (((0.3157:ℝ):ℂ) + (((-0.94885):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.3157) ((-0.94885)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_20 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_19 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.3157) ((-0.94885)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_20 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_19 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.3157) ((-0.94885)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_20 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_19 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.3157) ((-0.94885)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_20 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_19 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.3157) ((-0.94885)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_20 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_19 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.3157) ((-0.94885)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_20 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_19 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.3157) ((-0.94885)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_20 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_19 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.3157) ((-0.94885)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_20 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_19 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.3157) ((-0.94885)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_20 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_19 σ (by exact_mod_cast h1)
  have hrr : (((0.3157:ℝ):ℂ) + (((-0.94885):ℝ):ℂ) * I).re = 0.3157 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.3930472893) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.218913032) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.4384459625)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.3535684659) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.3413288438)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.1656472495) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1414501384) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.2548730315)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.23713737/2) (0.25482968/2) ((-0.0424836461)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 20/32) (1 - 19/32) (0.3157 * (-0.9998243594199) - (-0.94885) * (-0.0187416559615)) (0.3157 * (-0.0187416559615) + (-0.94885) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.25482968) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (19/32) (20/32) 226.5129 0.25482968 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (226.5129:ℝ) / 12 * (0.25482968 / 100 + 0.25482968 / 10 / (19/32 + 1)) ≤ 0.3499173178 := by norm_num
  have hTu : (10:ℝ) * 0.25482968 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_4 (σ : ℝ) (h1 : (20:ℝ)/32 ≤ σ) (h2 : σ ≤ (21:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.3492:ℝ)^2 + ((-0.93704):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.3492:ℝ) ((-0.93704):ℝ) hr
  have hre := re_EM σ hσ1 ((0.3492:ℝ) + ((-0.93704):ℝ) * I)
  have hle := re_le_norm_of (((0.3492:ℝ):ℂ) + (((-0.93704):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.3492) ((-0.93704)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_21 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_20 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.3492) ((-0.93704)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_21 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_20 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.3492) ((-0.93704)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_21 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_20 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.3492) ((-0.93704)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_21 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_20 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.3492) ((-0.93704)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_21 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_20 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.3492) ((-0.93704)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_21 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_20 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.3492) ((-0.93704)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_21 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_20 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.3492) ((-0.93704)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_21 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_20 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.3492) ((-0.93704)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_21 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_20 σ (by exact_mod_cast h1)
  have hrr : (((0.3492:ℝ):ℂ) + (((-0.93704):ℝ):ℂ) * I).re = 0.3492 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.3664596285) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.1958407407) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.4203818274)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.3391702546) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.3208259386)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.1475636916) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1402235314) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.2347293552)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.2206734/2) (0.23713738/2) ((-0.0434792036)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 21/32) (1 - 20/32) (0.3492 * (-0.9998243594199) - (-0.93704) * (-0.0187416559615)) (0.3492 * (-0.0187416559615) + (-0.93704) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.23713738) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (20/32) (21/32) 226.584 0.23713738 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (226.584:ℝ) / 12 * (0.23713738 / 100 + 0.23713738 / 10 / (20/32 + 1)) ≤ 0.3203226192 := by norm_num
  have hTu : (10:ℝ) * 0.23713738 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_5 (σ : ℝ) (h1 : (21:ℝ)/32 ≤ σ) (h2 : σ ≤ (22:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.38201:ℝ)^2 + ((-0.92415):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.38201:ℝ) ((-0.92415):ℝ) hr
  have hre := re_EM σ hσ1 ((0.38201:ℝ) + ((-0.92415):ℝ) * I)
  have hle := re_le_norm_of (((0.38201:ℝ):ℂ) + (((-0.92415):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.38201) ((-0.92415)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_22 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_21 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.38201) ((-0.92415)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_22 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_21 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.38201) ((-0.92415)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_22 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_21 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.38201) ((-0.92415)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_22 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_21 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.38201) ((-0.92415)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_22 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_21 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.38201) ((-0.92415)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_22 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_21 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.38201) ((-0.92415)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_22 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_21 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.38201) ((-0.92415)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_22 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_21 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.38201) ((-0.92415)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_22 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_21 σ (by exact_mod_cast h1)
  have hrr : (((0.38201:ℝ):ℂ) + (((-0.92415):ℝ):ℂ) * I).re = 0.38201 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.3405181847) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.1739552188) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.4025550496)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.3249100231) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.3011789543)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.1309233526) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1383727966) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.2158861028)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.2053525/2) (0.22067341/2) ((-0.0440533865)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 22/32) (1 - 21/32) (0.38201 * (-0.9998243594199) - (-0.92415) * (-0.0187416559615)) (0.38201 * (-0.0187416559615) + (-0.92415) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.22067341) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (21/32) (22/32) 226.6571 0.22067341 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (226.6571:ℝ) / 12 * (0.22067341 / 100 + 0.22067341 / 10 / (21/32 + 1)) ≤ 0.2933398396 := by norm_num
  have hTu : (10:ℝ) * 0.22067341 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_6 (σ : ℝ) (h1 : (22:ℝ)/32 ≤ σ) (h2 : σ ≤ (23:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.41402:ℝ)^2 + ((-0.91026):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.41402:ℝ) ((-0.91026):ℝ) hr
  have hre := re_EM σ hσ1 ((0.41402:ℝ) + ((-0.91026):ℝ) * I)
  have hle := re_le_norm_of (((0.41402:ℝ):ℂ) + (((-0.91026):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.41402) ((-0.91026)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_23 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_22 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.41402) ((-0.91026)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_23 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_22 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.41402) ((-0.91026)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_23 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_22 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.41402) ((-0.91026)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_23 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_22 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.41402) ((-0.91026)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_23 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_22 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.41402) ((-0.91026)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_23 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_22 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.41402) ((-0.91026)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_23 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_22 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.41402) ((-0.91026)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_23 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_22 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.41402) ((-0.91026)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_23 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_22 σ (by exact_mod_cast h1)
  have hrr : (((0.41402:ℝ):ℂ) + (((-0.91026):ℝ):ℂ) * I).re = 0.41402 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.3152919816) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.153267854) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.3850126324)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.310831769) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.2823928)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.115657825) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1359749968) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.1982943747)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.19109529/2) (0.20535251/2) ((-0.0442542115)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 23/32) (1 - 22/32) (0.41402 * (-0.9998243594199) - (-0.91026) * (-0.0187416559615)) (0.41402 * (-0.0187416559615) + (-0.91026) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.20535251) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (22/32) (23/32) 226.7321 0.20535251 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (226.7321:ℝ) / 12 * (0.20535251 / 100 + 0.20535251 / 10 / (22/32 + 1)) ≤ 0.2687259596 := by norm_num
  have hTu : (10:ℝ) * 0.20535251 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_7 (σ : ℝ) (h1 : (23:ℝ)/32 ≤ σ) (h2 : σ ≤ (24:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.44512:ℝ)^2 + ((-0.89546):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.44512:ℝ) ((-0.89546):ℝ) hr
  have hre := re_EM σ hσ1 ((0.44512:ℝ) + ((-0.89546):ℝ) * I)
  have hle := re_le_norm_of (((0.44512:ℝ):ℂ) + (((-0.89546):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.44512) ((-0.89546)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_24 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_23 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.44512) ((-0.89546)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_24 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_23 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.44512) ((-0.89546)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_24 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_23 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.44512) ((-0.89546)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_24 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_23 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.44512) ((-0.89546)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_24 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_23 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.44512) ((-0.89546)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_24 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_23 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.44512) ((-0.89546)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_24 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_23 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.44512) ((-0.89546)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_24 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_23 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.44512) ((-0.89546)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_24 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_23 σ (by exact_mod_cast h1)
  have hrr : (((0.44512:ℝ):ℂ) + (((-0.89546):ℝ):ℂ) * I).re = 0.44512 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.2908482352) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.1337867139) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.367798603)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.2969761213) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.2644690684)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.1016994054) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1331021163) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.1819045397)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.17782794/2) (0.1910953/2) ((-0.0441262383)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 24/32) (1 - 23/32) (0.44512 * (-0.9998243594199) - (-0.89546) * (-0.0187416559615)) (0.44512 * (-0.0187416559615) + (-0.89546) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.1910953) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (23/32) (24/32) 226.8091 0.1910953 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (226.8091:ℝ) / 12 * (0.1910953 / 100 + 0.1910953 / 10 / (23/32 + 1)) ≤ 0.246262233 := by norm_num
  have hTu : (10:ℝ) * 0.1910953 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_8 (σ : ℝ) (h1 : (24:ℝ)/32 ≤ σ) (h2 : σ ≤ (25:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.47525:ℝ)^2 + ((-0.87985):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.47525:ℝ) ((-0.87985):ℝ) hr
  have hre := re_EM σ hσ1 ((0.47525:ℝ) + ((-0.87985):ℝ) * I)
  have hle := re_le_norm_of (((0.47525:ℝ):ℂ) + (((-0.87985):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.47525) ((-0.87985)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_25 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_24 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.47525) ((-0.87985)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_25 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_24 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.47525) ((-0.87985)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_25 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_24 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.47525) ((-0.87985)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_25 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_24 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.47525) ((-0.87985)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_25 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_24 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.47525) ((-0.87985)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_25 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_24 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.47525) ((-0.87985)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_25 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_24 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.47525) ((-0.87985)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_25 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_24 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.47525) ((-0.87985)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_25 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_24 σ (by exact_mod_cast h1)
  have hrr : (((0.47525:ℝ):ℂ) + (((-0.87985):ℝ):ℂ) * I).re = 0.47525 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.2672357811) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.1155014564) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.3509602748)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.2833880539) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.2474083548)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.0889745882) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1298306928) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.1666662043)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.1654817/2) (0.17782795/2) ((-0.0437151403)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 25/32) (1 - 24/32) (0.47525 * (-0.9998243594199) - (-0.87985) * (-0.0187416559615)) (0.47525 * (-0.0187416559615) + (-0.87985) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.17782795) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (24/32) (25/32) 226.888 0.17782795 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (226.888:ℝ) / 12 * (0.17782795 / 100 + 0.17782795 / 10 / (24/32 + 1)) ≤ 0.2257512277 := by norm_num
  have hTu : (10:ℝ) * 0.17782795 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_9 (σ : ℝ) (h1 : (25:ℝ)/32 ≤ σ) (h2 : σ ≤ (26:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.50431:ℝ)^2 + ((-0.86351):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.50431:ℝ) ((-0.86351):ℝ) hr
  have hre := re_EM σ hσ1 ((0.50431:ℝ) + ((-0.86351):ℝ) * I)
  have hle := re_le_norm_of (((0.50431:ℝ):ℂ) + (((-0.86351):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.50431) ((-0.86351)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_26 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_25 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.50431) ((-0.86351)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_26 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_25 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.50431) ((-0.86351)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_26 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_25 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.50431) ((-0.86351)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_26 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_25 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.50431) ((-0.86351)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_26 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_25 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.50431) ((-0.86351)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_26 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_25 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.50431) ((-0.86351)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_26 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_25 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.50431) ((-0.86351)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_26 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_25 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.50431) ((-0.86351)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_26 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_25 σ (by exact_mod_cast h1)
  have hrr : (((0.50431:ℝ):ℂ) + (((-0.86351):ℝ):ℂ) * I).re = 0.50431 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.2445014638) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.0984038856) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.3345261711)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.2700947852) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.2311987064)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.0774126445) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1262214902) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.1525235956)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.15399265/2) (0.16548171/2) ((-0.0430587737)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 26/32) (1 - 25/32) (0.50431 * (-0.9998243594199) - (-0.86351) * (-0.0187416559615)) (0.50431 * (-0.0187416559615) + (-0.86351) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.16548171) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (25/32) (26/32) 226.9689 0.16548171 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (226.9689:ℝ) / 12 * (0.16548171 / 100 + 0.16548171 / 10 / (25/32 + 1)) ≤ 0.2070148982 := by norm_num
  have hTu : (10:ℝ) * 0.16548171 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_10 (σ : ℝ) (h1 : (26:ℝ)/32 ≤ σ) (h2 : σ ≤ (27:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.53226:ℝ)^2 + ((-0.84657):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.53226:ℝ) ((-0.84657):ℝ) hr
  have hre := re_EM σ hσ1 ((0.53226:ℝ) + ((-0.84657):ℝ) * I)
  have hle := re_le_norm_of (((0.53226:ℝ):ℂ) + (((-0.84657):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.53226) ((-0.84657)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_27 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_26 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.53226) ((-0.84657)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_27 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_26 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.53226) ((-0.84657)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_27 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_26 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.53226) ((-0.84657)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_27 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_26 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.53226) ((-0.84657)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_27 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_26 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.53226) ((-0.84657)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_27 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_26 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.53226) ((-0.84657)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_27 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_26 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.53226) ((-0.84657)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_27 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_26 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.53226) ((-0.84657)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_27 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_26 σ (by exact_mod_cast h1)
  have hrr : (((0.53226:ℝ):ℂ) + (((-0.84657):ℝ):ℂ) * I).re = 0.53226 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.2226909017) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.0824782993) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.3185421583)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.2571383273) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.215838437)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.0669444056) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1223422241) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.1394287169)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.14330125/2) (0.15399266/2) ((-0.0421965172)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 27/32) (1 - 26/32) (0.53226 * (-0.9998243594199) - (-0.84657) * (-0.0187416559615)) (0.53226 * (-0.0187416559615) + (-0.84657) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.15399266) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (26/32) (27/32) 227.0517 0.15399266 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (227.0517:ℝ) / 12 * (0.15399266 / 100 + 0.15399266 / 10 / (26/32 + 1)) ≤ 0.1898922932 := by norm_num
  have hTu : (10:ℝ) * 0.15399266 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_11 (σ : ℝ) (h1 : (27:ℝ)/32 ≤ σ) (h2 : σ ≤ (28:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.55906:ℝ)^2 + ((-0.82912):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.55906:ℝ) ((-0.82912):ℝ) hr
  have hre := re_EM σ hσ1 ((0.55906:ℝ) + ((-0.82912):ℝ) * I)
  have hle := re_le_norm_of (((0.55906:ℝ):ℂ) + (((-0.82912):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.55906) ((-0.82912)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_28 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_27 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.55906) ((-0.82912)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_28 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_27 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.55906) ((-0.82912)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_28 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_27 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.55906) ((-0.82912)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_28 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_27 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.55906) ((-0.82912)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_28 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_27 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.55906) ((-0.82912)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_28 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_27 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.55906) ((-0.82912)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_28 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_27 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.55906) ((-0.82912)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_28 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_27 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.55906) ((-0.82912)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_28 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_27 σ (by exact_mod_cast h1)
  have hrr : (((0.55906:ℝ):ℂ) + (((-0.82912):ℝ):ℂ) * I).re = 0.55906 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.2018262252) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.0676949774) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.3030343389)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.2445446674) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.2013110527)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.0574961921) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1182513135) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.1273253763)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.13335214/2) (0.14330126/2) ((-0.041163365)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 28/32) (1 - 27/32) (0.55906 * (-0.9998243594199) - (-0.82912) * (-0.0187416559615)) (0.55906 * (-0.0187416559615) + (-0.82912) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.14330126) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (27/32) (28/32) 227.1365 0.14330126 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (227.1365:ℝ) / 12 * (0.14330126 / 100 + 0.14330126 / 10 / (27/32 + 1)) ≤ 0.1742380054 := by norm_num
  have hTu : (10:ℝ) * 0.14330126 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_12 (σ : ℝ) (h1 : (28:ℝ)/32 ≤ σ) (h2 : σ ≤ (29:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.58469:ℝ)^2 + ((-0.81125):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.58469:ℝ) ((-0.81125):ℝ) hr
  have hre := re_EM σ hσ1 ((0.58469:ℝ) + ((-0.81125):ℝ) * I)
  have hle := re_le_norm_of (((0.58469:ℝ):ℂ) + (((-0.81125):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.58469) ((-0.81125)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_29 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_28 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.58469) ((-0.81125)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_29 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_28 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.58469) ((-0.81125)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_29 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_28 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.58469) ((-0.81125)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_29 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_28 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.58469) ((-0.81125)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_29 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_28 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.58469) ((-0.81125)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_29 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_28 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.58469) ((-0.81125)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_29 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_28 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.58469) ((-0.81125)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_29 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_28 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.58469) ((-0.81125)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_29 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_28 σ (by exact_mod_cast h1)
  have hrr : (((0.58469:ℝ):ℂ) + (((-0.81125):ℝ):ℂ) * I).re = 0.58469 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.1819199643) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.0540173824) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.2880255622)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.2323370351) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.1875975816)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.0489951974) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1140034134) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.1161578514)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.12409377/2) (0.13335215/2) ((-0.0399917546)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 29/32) (1 - 28/32) (0.58469 * (-0.9998243594199) - (-0.81125) * (-0.0187416559615)) (0.58469 * (-0.0187416559615) + (-0.81125) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.13335215) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (28/32) (29/32) 227.2232 0.13335215 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (227.2232:ℝ) / 12 * (0.13335215 / 100 + 0.13335215 / 10 / (28/32 + 1)) ≤ 0.159920373 := by norm_num
  have hTu : (10:ℝ) * 0.13335215 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_13 (σ : ℝ) (h1 : (29:ℝ)/32 ≤ σ) (h2 : σ ≤ (30:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.60911:ℝ)^2 + ((-0.79307):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.60911:ℝ) ((-0.79307):ℝ) hr
  have hre := re_EM σ hσ1 ((0.60911:ℝ) + ((-0.79307):ℝ) * I)
  have hle := re_le_norm_of (((0.60911:ℝ):ℂ) + (((-0.79307):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.60911) ((-0.79307)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_30 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_29 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.60911) ((-0.79307)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_30 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_29 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.60911) ((-0.79307)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_30 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_29 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.60911) ((-0.79307)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_30 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_29 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.60911) ((-0.79307)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_30 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_29 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.60911) ((-0.79307)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_30 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_29 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.60911) ((-0.79307)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_30 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_29 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.60911) ((-0.79307)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_30 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_29 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.60911) ((-0.79307)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_30 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_29 σ (by exact_mod_cast h1)
  have hrr : (((0.60911:ℝ):ℂ) + (((-0.79307):ℝ):ℂ) * I).re = 0.60911 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.1629962722) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.0414185193) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.27353671)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.2205346915) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.1746794455)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.0413766771) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1096442069) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.1058741591)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.11547819/2) (0.12409378/2) ((-0.0387089861)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 30/32) (1 - 29/32) (0.60911 * (-0.9998243594199) - (-0.79307) * (-0.0187416559615)) (0.60911 * (-0.0187416559615) + (-0.79307) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.12409378) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (29/32) (30/32) 227.3119 0.12409378 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (227.3119:ℝ) / 12 * (0.12409378 / 100 + 0.12409378 / 10 / (29/32 + 1)) ≤ 0.146820291 := by norm_num
  have hTu : (10:ℝ) * 0.12409378 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_14 (σ : ℝ) (h1 : (30:ℝ)/32 ≤ σ) (h2 : σ ≤ (31:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.63235:ℝ)^2 + ((-0.77468):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.63235:ℝ) ((-0.77468):ℝ) hr
  have hre := re_EM σ hσ1 ((0.63235:ℝ) + ((-0.77468):ℝ) * I)
  have hle := re_le_norm_of (((0.63235:ℝ):ℂ) + (((-0.77468):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.63235) ((-0.77468)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_31 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_30 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.63235) ((-0.77468)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_31 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_30 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.63235) ((-0.77468)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_31 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_30 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.63235) ((-0.77468)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_31 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_30 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.63235) ((-0.77468)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_31 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_30 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.63235) ((-0.77468)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_31 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_30 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.63235) ((-0.77468)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_31 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_30 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.63235) ((-0.77468)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_31 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_30 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.63235) ((-0.77468)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_31 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_30 σ (by exact_mod_cast h1)
  have hrr : (((0.63235:ℝ):ℂ) + (((-0.77468):ℝ):ℂ) * I).re = 0.63235 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.1450510051) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.0298499281) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.2595878599)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.209158288) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.1625355245)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.0345706485) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1052225693) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.096421296)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.10746078/2) (0.1154782/2) ((-0.0373432203)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 31/32) (1 - 30/32) (0.63235 * (-0.9998243594199) - (-0.77468) * (-0.0187416559615)) (0.63235 * (-0.0187416559615) + (-0.77468) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.1154782) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (30/32) (31/32) 227.4025 0.1154782 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (227.4025:ℝ) / 12 * (0.1154782 / 100 + 0.1154782 / 10 / (30/32 + 1)) ≤ 0.134829731 := by norm_num
  have hTu : (10:ℝ) * 0.1154782 * 0 / 225 ≤ 0 := by norm_num
  linarith

lemma sub_15 (σ : ℝ) (h1 : (31:ℝ)/32 ≤ σ) (h2 : σ ≤ (32:ℝ)/32) (hσ1 : σ < 1) :
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  have hr : (0.6544:ℝ)^2 + ((-0.75614):ℝ)^2 ≤ 1 := by norm_num
  have hrn := norm_ri_le_one (0.6544:ℝ) ((-0.75614):ℝ) hr
  have hre := re_EM σ hσ1 ((0.6544:ℝ) + ((-0.75614):ℝ) * I)
  have hle := re_le_norm_of (((0.6544:ℝ):ℂ) + (((-0.75614):ℝ):ℂ) * I) (eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)) hrn
  rw [hre] at hle
  have hb2 := rot_bounds (0.6544) ((-0.75614)) ((-0.5632935954295)) (0.826256815608) (2/10^7) (Eθ 2) hr (trig_2)
  have hxl2 := xlo_2_32 σ (by exact_mod_cast h2)
  have hxu2 := xhi_2_31 σ (by exact_mod_cast h1)
  have hb3 := rot_bounds (0.6544) ((-0.75614)) ((-0.7170601161939)) (0.6970113268357) (2/10^7) (Eθ 3) hr (trig_3)
  have hxl3 := xlo_3_32 σ (by exact_mod_cast h2)
  have hxu3 := xhi_3_31 σ (by exact_mod_cast h1)
  have hb4 := rot_bounds (0.6544) ((-0.75614)) ((-0.3654006440121)) ((-0.9308503474528)) (2/10^7) (Eθ 4) hr (trig_4)
  have hxl4 := xlo_4_32 σ (by exact_mod_cast h2)
  have hxu4 := xhi_4_31 σ (by exact_mod_cast h1)
  have hb5 := rot_bounds (0.6544) ((-0.75614)) (0.5477092431889) (0.8366687426487) (2/10^7) (Eθ 5) hr (trig_5)
  have hxl5 := xlo_5_32 σ (by exact_mod_cast h2)
  have hxu5 := xhi_5_31 σ (by exact_mod_cast h1)
  have hb6 := rot_bounds (0.6544) ((-0.75614)) ((-0.1719949813052)) ((-0.9850978258047)) (2/10^7) (Eθ 6) hr (trig_6)
  have hxl6 := xlo_6_32 σ (by exact_mod_cast h2)
  have hxu6 := xhi_6_31 σ (by exact_mod_cast h1)
  have hb7 := rot_bounds (0.6544) ((-0.75614)) ((-0.6103306811647)) (0.7921467412141) (2/10^7) (Eθ 7) hr (trig_7)
  have hxl7 := xlo_7_32 σ (by exact_mod_cast h2)
  have hxu7 := xhi_7_31 σ (by exact_mod_cast h1)
  have hb8 := rot_bounds (0.6544) ((-0.75614)) (0.9749492864381) (0.2224272664803) (2/10^7) (Eθ 8) hr (trig_8)
  have hxl8 := xlo_8_32 σ (by exact_mod_cast h2)
  have hxu8 := xhi_8_31 σ (by exact_mod_cast h1)
  have hb9 := rot_bounds (0.6544) ((-0.75614)) (0.0283504276599) ((-0.9995980458421)) (2/10^7) (Eθ 9) hr (trig_9)
  have hxl9 := xlo_9_32 σ (by exact_mod_cast h2)
  have hxu9 := xhi_9_31 σ (by exact_mod_cast h1)
  have hb10 := rot_bounds (0.6544) ((-0.75614)) ((-0.9998243594199)) ((-0.0187416559615)) (2/10^7) (Eθ 10) hr (trig_10)
  have hxl10 := xlo_10_32 σ (by exact_mod_cast h2)
  have hxu10 := xhi_10_31 σ (by exact_mod_cast h1)
  have hrr : (((0.6544:ℝ):ℂ) + (((-0.75614):ℝ):ℂ) * I).re = 0.6544 := by simp
  rw [hrr] at hle
  have hm2 := mul_lb ((2:ℝ)^(-σ)) _ _ _ _ (0.1280731498) (by positivity) hxl2 hxu2 hb2.1 (by norm_num) (by norm_num)
  have hm3 := mul_lb ((3:ℝ)^(-σ)) _ _ _ _ (0.0192646013) (by positivity) hxl3 hxu3 hb3.1 (by norm_num) (by norm_num)
  have hm4 := mul_lb ((4:ℝ)^(-σ)) _ _ _ _ ((-0.2461801244)) (by positivity) hxl4 hxu4 hb4.1 (by norm_num) (by norm_num)
  have hm5 := mul_lb ((5:ℝ)^(-σ)) _ _ _ _ (0.1982118863) (by positivity) hxl5 hxu5 hb5.1 (by norm_num) (by norm_num)
  have hm6 := mul_lb ((6:ℝ)^(-σ)) _ _ _ _ ((-0.1511340866)) (by positivity) hxl6 hxu6 hb6.1 (by norm_num) (by norm_num)
  have hm7 := mul_lb ((7:ℝ)^(-σ)) _ _ _ _ (0.0285104621) (by positivity) hxl7 hxu7 hb7.1 (by norm_num) (by norm_num)
  have hm8 := mul_lb ((8:ℝ)^(-σ)) _ _ _ _ (0.1007740957) (by positivity) hxl8 hxu8 hb8.1 (by norm_num) (by norm_num)
  have hm9 := mul_lb ((9:ℝ)^(-σ)) _ _ _ _ ((-0.0877429517)) (by positivity) hxl9 hxu9 hb9.1 (by norm_num) (by norm_num)
  have hm10 := mul_lb (((10:ℝ)^(-σ))/2) _ _ (0.1/2) (0.10746079/2) ((-0.0359164359)) (by positivity) (by linarith) (by linarith) hb10.1 (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ 1 - σ := by linarith
  have hg := g_bound (1 - σ) _ _ (1 - 32/32) (1 - 31/32) (0.6544 * (-0.9998243594199) - (-0.75614) * (-0.0187416559615)) (0.6544 * (-0.0187416559615) + (-0.75614) * (-0.9998243594199)) (2/10^7) 0 (by linarith) (by linarith) ht0 (by norm_num) hb10.2.1 hb10.2.2.1 (by norm_num) (by norm_num)
  have hD : (225:ℝ) ≤ (1 - σ)^2 + 225 := le_add_of_nonneg_left (sq_nonneg _)
  have ht := tail_bound (10 * (10:ℝ)^(-σ)) _ ((1 - σ)^2 + 225) (10 * 0.10746079) 0 225 (by positivity) (by linarith) hg (by norm_num) hD (by norm_num)
  have hE := lhs_bound σ (31/32) (32/32) 227.4951 0.10746079 (by norm_num) h1 h2 (by norm_num) (by norm_num) hxu10
  have hEu : (227.4951:ℝ) / 12 * (0.10746079 / 100 + 0.10746079 / 10 / (31/32 + 1)) ≤ 0.1238508679 := by norm_num
  have hTu : (10:ℝ) * 0.10746079 * 0 / 225 ≤ 0 := by norm_num
  linarith


end EM10

theorem em10_fifteen_certificate : ∀ σ : ℝ, 1 / 2 ≤ σ → σ < 1 →
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ := by
  intro σ h1 h2
  by_cases c0 : σ ≤ (17:ℝ)/32
  · exact EM10.sub_0 σ (by norm_num; linarith) c0 h2
  by_cases c1 : σ ≤ (18:ℝ)/32
  · exact EM10.sub_1 σ (by norm_num; linarith) c1 h2
  by_cases c2 : σ ≤ (19:ℝ)/32
  · exact EM10.sub_2 σ (by norm_num; linarith) c2 h2
  by_cases c3 : σ ≤ (20:ℝ)/32
  · exact EM10.sub_3 σ (by norm_num; linarith) c3 h2
  by_cases c4 : σ ≤ (21:ℝ)/32
  · exact EM10.sub_4 σ (by norm_num; linarith) c4 h2
  by_cases c5 : σ ≤ (22:ℝ)/32
  · exact EM10.sub_5 σ (by norm_num; linarith) c5 h2
  by_cases c6 : σ ≤ (23:ℝ)/32
  · exact EM10.sub_6 σ (by norm_num; linarith) c6 h2
  by_cases c7 : σ ≤ (24:ℝ)/32
  · exact EM10.sub_7 σ (by norm_num; linarith) c7 h2
  by_cases c8 : σ ≤ (25:ℝ)/32
  · exact EM10.sub_8 σ (by norm_num; linarith) c8 h2
  by_cases c9 : σ ≤ (26:ℝ)/32
  · exact EM10.sub_9 σ (by norm_num; linarith) c9 h2
  by_cases c10 : σ ≤ (27:ℝ)/32
  · exact EM10.sub_10 σ (by norm_num; linarith) c10 h2
  by_cases c11 : σ ≤ (28:ℝ)/32
  · exact EM10.sub_11 σ (by norm_num; linarith) c11 h2
  by_cases c12 : σ ≤ (29:ℝ)/32
  · exact EM10.sub_12 σ (by norm_num; linarith) c12 h2
  by_cases c13 : σ ≤ (30:ℝ)/32
  · exact EM10.sub_13 σ (by norm_num; linarith) c13 h2
  by_cases c14 : σ ≤ (31:ℝ)/32
  · exact EM10.sub_14 σ (by norm_num; linarith) c14 h2
  exact EM10.sub_15 σ (by have := not_le.mp c14; linarith) (by norm_num; linarith) h2

end RHV6Fresh

#print axioms RHV6Fresh.em10_fifteen_certificate
