/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.DemandLevelPremise
import RHV6Fresh.Terminal.RemainderExponent

/-!
# Le pont des rencontres (module isolé, non importé par la chaîne)

Solution 1 du maître §16.7 (validée par l'auteur le 2026-10-29). Objet : relier « la demande est bornée aux
rencontres » à « la demande est bornée en tout point » dans la seule langue des premiers, sans zéro.

Ce qui est compilé :

1. **Pente bornée de la somme lissée** (`smoothedVonMangoldtSum_sub_le`) : entre deux points `p ≤ x` au-delà
   de un, la somme lissée de von Mangoldt varie d'au plus `2·(log 4 + 4)·(x − p)`, par positivité de `Λ` et
   les bornes de Tchebychev de Mathlib (`Chebyshev.psi_le_const_mul_self`).
2. **Le fond varie d'une pente un demi plus une constante** (`smoothedZeroBackground_sub_le`) : la somme des
   zéros triviaux est bornée (`trivialZeroSum_norm_le`), il n'est pas besoin de sa pente.
3. **La demande entre deux points** (`smoothedRemainder_sub_le`) : `‖A(x) − A(p)‖ ≤ pente·(x − p) + décalage`,
   avec une pente et un décalage explicites, fixés par Tchebychev.
4. **Le niveau dans un écart** (`demandRelativeLevel_le_of_mem_gap`) : le niveau en un point d'un écart est au
   plus le niveau à la rencontre précédente, plus la pente fois l'écart rapporté à la racine du premier, plus
   le décalage.
5. **Le pont** (`demandBoundedEverywhere_of_meetings_of_gaps`) : demande bornée aux rencontres ET écarts de
   l'ordre de la racine du premier (`GapsRootOrder`, hypothèse nommée) donnent la demande bornée en tout
   point, donc RH (`riemannHypothesis_of_meetings_of_gaps`) et la prémisse unique de la chaîne.

**Correction au maître §16.7, dite avant d'écrire** : le maître annonçait une équivalence « bornée partout ssi
bornée aux rencontres et écarts de l'ordre de la racine ». Seule l'implication de droite à gauche est compilée
ici. La réciproque n'est pas connue : la demande bornée partout (RH) ne donne pas d'écarts de l'ordre de la
racine (sous RH on ne sait que `√p · log p`, Cramér). `GapsRootOrder` est donc une hypothèse nommée plus forte
que ce que la cible fournit ; elle est conjecturée vraie et jamais posée comme démontrée.

Aucun axiome, aucun `sorry`. La chaîne est intacte.
-/

namespace RHV6Fresh

open Complex RHV3Lean ArithmeticFunction

/-! ## 1. La somme lissée entre deux points -/

/-- `Σ_{n < ⌈x⌉} Λ(n) ≤ ψ(x)`. -/
theorem sum_vonMangoldt_range_ceil_le_psi (x : ℝ) :
    ∑ n ∈ Finset.range ⌈x⌉₊, Λ n ≤ Chebyshev.psi x := by
  calc ∑ n ∈ Finset.range ⌈x⌉₊, Λ n
      ≤ ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun _ _ _ => vonMangoldt_nonneg
        rw [Finset.mem_range] at hn
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor (Nat.lt_ceil.mp hn).le⟩
    _ = Chebyshev.psi x := (Chebyshev.psi_eq_sum_Icc x).symm

/-- La constante de Tchebychev de Mathlib : `ψ(x) ≤ (log 4 + 4)·x`. -/
noncomputable def chebyshevConstant : ℝ := Real.log 4 + 4

theorem chebyshevConstant_nonneg : 0 ≤ chebyshevConstant := by
  unfold chebyshevConstant
  have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  linarith

/-- **Pente bornée** : entre `p ≤ x` (au-delà de un), la somme lissée varie d'au plus
`2·(log 4 + 4)·(x − p)`. -/
theorem smoothedVonMangoldtSum_sub_le {p x : ℝ} (hp : 1 ≤ p) (hpx : p ≤ x) :
    ‖smoothedVonMangoldtSum x - smoothedVonMangoldtSum p‖ ≤ 2 * chebyshevConstant * (x - p) := by
  have hx1 : 1 ≤ x := hp.trans hpx
  have hx0 : 0 < x := by linarith
  have hp0 : 0 < p := by linarith
  have hxp : 0 ≤ x - p := by linarith
  have hC0 := chebyshevConstant_nonneg
  have hceil : ⌈p⌉₊ ≤ ⌈x⌉₊ := Nat.ceil_mono hpx
  unfold smoothedVonMangoldtSum
  rw [← Finset.sum_range_add_sum_Ico _ hceil]
  have hsplit : (∑ n ∈ Finset.range ⌈p⌉₊, (Λ n : ℂ) * (1 - (n : ℂ) / (x : ℂ)) +
        ∑ n ∈ Finset.Ico ⌈p⌉₊ ⌈x⌉₊, (Λ n : ℂ) * (1 - (n : ℂ) / (x : ℂ))) -
      ∑ n ∈ Finset.range ⌈p⌉₊, (Λ n : ℂ) * (1 - (n : ℂ) / (p : ℂ)) =
      ∑ n ∈ Finset.range ⌈p⌉₊, (Λ n : ℂ) * ((n : ℂ) / (p : ℂ) - (n : ℂ) / (x : ℂ)) +
        ∑ n ∈ Finset.Ico ⌈p⌉₊ ⌈x⌉₊, (Λ n : ℂ) * (1 - (n : ℂ) / (x : ℂ)) := by
    rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hsplit]
  have hT1 : ‖∑ n ∈ Finset.range ⌈p⌉₊, (Λ n : ℂ) * ((n : ℂ) / (p : ℂ) - (n : ℂ) / (x : ℂ))‖ ≤
      chebyshevConstant * (x - p) := by
    calc ‖∑ n ∈ Finset.range ⌈p⌉₊, (Λ n : ℂ) * ((n : ℂ) / (p : ℂ) - (n : ℂ) / (x : ℂ))‖
        ≤ ∑ n ∈ Finset.range ⌈p⌉₊, ‖(Λ n : ℂ) * ((n : ℂ) / (p : ℂ) - (n : ℂ) / (x : ℂ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range ⌈p⌉₊, Λ n * ((x - p) / x) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hnp : (n : ℝ) < p := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
          have hc : ((n : ℂ) / (p : ℂ) - (n : ℂ) / (x : ℂ)) = (((n : ℝ) / p - n / x : ℝ) : ℂ) := by
            push_cast; ring
          rw [hc, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg vonMangoldt_nonneg]
          refine mul_le_mul_of_nonneg_left ?_ vonMangoldt_nonneg
          have hkey : (n : ℝ) / p - n / x = n * (x - p) / (p * x) := by
            rw [div_sub_div _ _ hp0.ne' hx0.ne']
            congr 1
            ring
          have h0 : 0 ≤ (n : ℝ) / p - n / x := by
            rw [hkey]; positivity
          rw [abs_of_nonneg h0, hkey]
          have h1 : (n : ℝ) * (x - p) / (p * x) ≤ p * (x - p) / (p * x) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hnp.le hxp) (by positivity)
          have h2 : p * (x - p) / (p * x) = (x - p) / x := mul_div_mul_left _ _ hp0.ne'
          linarith
      _ = (∑ n ∈ Finset.range ⌈p⌉₊, Λ n) * ((x - p) / x) := by rw [Finset.sum_mul]
      _ ≤ Chebyshev.psi p * ((x - p) / x) :=
          mul_le_mul_of_nonneg_right (sum_vonMangoldt_range_ceil_le_psi p) (div_nonneg hxp hx0.le)
      _ ≤ (chebyshevConstant * p) * ((x - p) / x) :=
          mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self hp0.le) (div_nonneg hxp hx0.le)
      _ ≤ chebyshevConstant * (x - p) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hC0
          rw [mul_div_assoc', div_le_iff₀ hx0]
          nlinarith [sq_nonneg (x - p)]
  have hT2 : ‖∑ n ∈ Finset.Ico ⌈p⌉₊ ⌈x⌉₊, (Λ n : ℂ) * (1 - (n : ℂ) / (x : ℂ))‖ ≤
      chebyshevConstant * (x - p) := by
    calc ‖∑ n ∈ Finset.Ico ⌈p⌉₊ ⌈x⌉₊, (Λ n : ℂ) * (1 - (n : ℂ) / (x : ℂ))‖
        ≤ ∑ n ∈ Finset.Ico ⌈p⌉₊ ⌈x⌉₊, ‖(Λ n : ℂ) * (1 - (n : ℂ) / (x : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ico ⌈p⌉₊ ⌈x⌉₊, Λ n * ((x - p) / x) := by
          refine Finset.sum_le_sum fun n hn => ?_
          obtain ⟨hn1, hn2⟩ := Finset.mem_Ico.mp hn
          have hnx : (n : ℝ) < x := Nat.lt_ceil.mp hn2
          have hpn : p ≤ n := (Nat.le_ceil p).trans (by exact_mod_cast hn1)
          have hc : (1 - (n : ℂ) / (x : ℂ)) = ((1 - n / x : ℝ) : ℂ) := by push_cast; ring
          rw [hc, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg vonMangoldt_nonneg]
          refine mul_le_mul_of_nonneg_left ?_ vonMangoldt_nonneg
          have h0 : 0 ≤ 1 - (n : ℝ) / x := by rw [sub_nonneg, div_le_one hx0]; exact hnx.le
          have he : (x - n) / x = 1 - (n : ℝ) / x := by rw [sub_div, div_self hx0.ne']
          rw [abs_of_nonneg h0, ← he]
          exact div_le_div_of_nonneg_right (by linarith) hx0.le
      _ = (∑ n ∈ Finset.Ico ⌈p⌉₊ ⌈x⌉₊, Λ n) * ((x - p) / x) := by rw [Finset.sum_mul]
      _ ≤ (∑ n ∈ Finset.range ⌈x⌉₊, Λ n) * ((x - p) / x) := by
          refine mul_le_mul_of_nonneg_right ?_ (div_nonneg hxp hx0.le)
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => vonMangoldt_nonneg
          intro n hn
          rw [Finset.mem_range]
          exact (Finset.mem_Ico.mp hn).2
      _ ≤ Chebyshev.psi x * ((x - p) / x) :=
          mul_le_mul_of_nonneg_right (sum_vonMangoldt_range_ceil_le_psi x) (div_nonneg hxp hx0.le)
      _ ≤ (chebyshevConstant * x) * ((x - p) / x) :=
          mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self hx0.le) (div_nonneg hxp hx0.le)
      _ = chebyshevConstant * (x - p) := by
          rw [mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ hx0.ne']
  calc ‖∑ n ∈ Finset.range ⌈p⌉₊, (Λ n : ℂ) * ((n : ℂ) / (p : ℂ) - (n : ℂ) / (x : ℂ)) +
        ∑ n ∈ Finset.Ico ⌈p⌉₊ ⌈x⌉₊, (Λ n : ℂ) * (1 - (n : ℂ) / (x : ℂ))‖
      ≤ ‖∑ n ∈ Finset.range ⌈p⌉₊, (Λ n : ℂ) * ((n : ℂ) / (p : ℂ) - (n : ℂ) / (x : ℂ))‖ +
        ‖∑ n ∈ Finset.Ico ⌈p⌉₊ ⌈x⌉₊, (Λ n : ℂ) * (1 - (n : ℂ) / (x : ℂ))‖ := norm_add_le _ _
    _ ≤ chebyshevConstant * (x - p) + chebyshevConstant * (x - p) := add_le_add hT1 hT2
    _ = 2 * chebyshevConstant * (x - p) := by ring

/-! ## 2. Le fond entre deux points -/

/-- Le fond varie d'une pente un demi, plus une constante (les zéros triviaux sont bornés). -/
theorem smoothedZeroBackground_sub_le {p x : ℝ} (hp : 1 < p) (hpx : p ≤ x) :
    ‖smoothedZeroBackground x - smoothedZeroBackground p‖ ≤
      (x - p) / 2 + 2 * ‖logDeriv riemannZeta (-1)‖ + 2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
  have hx : 1 < x := hp.trans_le hpx
  unfold smoothedZeroBackground
  have hre : ((x : ℂ) / 2 + (-logDeriv riemannZeta 0) + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹ +
        ∑' n : ℕ, trivialZeroResidueTerm x n) -
      ((p : ℂ) / 2 + (-logDeriv riemannZeta 0) + logDeriv riemannZeta (-1) * (p : ℂ)⁻¹ +
        ∑' n : ℕ, trivialZeroResidueTerm p n) =
      (((x - p) / 2 : ℝ) : ℂ) +
        (logDeriv riemannZeta (-1) * (x : ℂ)⁻¹ - logDeriv riemannZeta (-1) * (p : ℂ)⁻¹) +
        (∑' n : ℕ, trivialZeroResidueTerm x n - ∑' n : ℕ, trivialZeroResidueTerm p n) := by
    push_cast; ring
  rw [hre]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) (norm_sub_le _ _)).trans ?_
  have h1 : ‖(((x - p) / 2 : ℝ) : ℂ)‖ = (x - p) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have h2 : ‖logDeriv riemannZeta (-1) * (x : ℂ)⁻¹ - logDeriv riemannZeta (-1) * (p : ℂ)⁻¹‖ ≤
      2 * ‖logDeriv riemannZeta (-1)‖ := by
    refine (norm_sub_le _ _).trans ?_
    have hxinv : ‖(x : ℂ)⁻¹‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), inv_eq_one_div,
        div_le_one (by linarith)]
      exact hx.le
    have hpinv : ‖(p : ℂ)⁻¹‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), inv_eq_one_div,
        div_le_one (by linarith)]
      exact hp.le
    rw [norm_mul, norm_mul]
    nlinarith [norm_nonneg (logDeriv riemannZeta (-1))]
  have h3 := trivialZeroSum_norm_le hx
  have h4 := trivialZeroSum_norm_le hp
  rw [h1]
  linarith

/-! ## 3. La demande entre deux points -/

/-- Pente du pont : `2·(log 4 + 4) + 1/2`. -/
noncomputable def bridgeSlope : ℝ := 2 * chebyshevConstant + 1 / 2

/-- Décalage du pont : deux fois la constante `c₁` plus deux fois la somme des zéros triviaux. -/
noncomputable def bridgeOffset : ℝ :=
  2 * ‖logDeriv riemannZeta (-1)‖ + 2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2

theorem bridgeSlope_nonneg : 0 ≤ bridgeSlope := by
  unfold bridgeSlope; linarith [chebyshevConstant_nonneg]

theorem bridgeOffset_nonneg : 0 ≤ bridgeOffset := by
  unfold bridgeOffset
  have h : 0 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := tsum_nonneg fun n => by positivity
  linarith [norm_nonneg (logDeriv riemannZeta (-1))]

/-- **La demande entre deux points** : `‖A(x) − A(p)‖ ≤ pente·(x − p) + décalage`. -/
theorem smoothedRemainder_sub_le {p x : ℝ} (hp : 1 < p) (hpx : p ≤ x) :
    ‖smoothedRemainder x - smoothedRemainder p‖ ≤ bridgeSlope * (x - p) + bridgeOffset := by
  unfold smoothedRemainder
  have e : (smoothedVonMangoldtSum x - smoothedZeroBackground x) -
      (smoothedVonMangoldtSum p - smoothedZeroBackground p) =
      (smoothedVonMangoldtSum x - smoothedVonMangoldtSum p) -
        (smoothedZeroBackground x - smoothedZeroBackground p) := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 := smoothedVonMangoldtSum_sub_le hp.le hpx
  have h2 := smoothedZeroBackground_sub_le hp hpx
  unfold bridgeSlope bridgeOffset
  linarith

/-! ## 4. Le niveau dans un écart -/

/-- **Le niveau en un point d'un écart** est au plus le niveau à la rencontre précédente `p`, plus la pente fois
l'écart rapporté à la racine de `p`, plus le décalage. -/
theorem demandRelativeLevel_le_of_mem_gap {p x : ℝ} (hp : 1 < p) (hpx : p ≤ x) {g : ℝ}
    (hg : x - p ≤ g) :
    demandRelativeLevel x ≤
      demandRelativeLevel p + bridgeSlope * (g / p ^ (1 / 2 : ℝ)) + bridgeOffset := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x := by linarith
  have hsp : 0 < p ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hp0 _
  have hsx : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hsps : p ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hp0.le hpx (by norm_num)
  have h1sx : 1 ≤ x ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hA : ‖smoothedRemainder x‖ ≤ ‖smoothedRemainder p‖ + bridgeSlope * (x - p) + bridgeOffset := by
    have := smoothedRemainder_sub_le hp hpx
    have h' := norm_sub_norm_le (smoothedRemainder x) (smoothedRemainder p)
    linarith
  have hS0 := bridgeSlope_nonneg
  have hO0 := bridgeOffset_nonneg
  have hg0 : 0 ≤ g := by linarith
  unfold demandRelativeLevel
  calc ‖smoothedRemainder x‖ / x ^ (1 / 2 : ℝ)
      ≤ (‖smoothedRemainder p‖ + bridgeSlope * (x - p) + bridgeOffset) / x ^ (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_right hA hsx.le
    _ = ‖smoothedRemainder p‖ / x ^ (1 / 2 : ℝ) + bridgeSlope * (x - p) / x ^ (1 / 2 : ℝ) +
        bridgeOffset / x ^ (1 / 2 : ℝ) := by rw [add_div, add_div]
    _ ≤ ‖smoothedRemainder p‖ / p ^ (1 / 2 : ℝ) + bridgeSlope * (g / p ^ (1 / 2 : ℝ)) + bridgeOffset := by
        have a1 : ‖smoothedRemainder p‖ / x ^ (1 / 2 : ℝ) ≤ ‖smoothedRemainder p‖ / p ^ (1 / 2 : ℝ) :=
          div_le_div_of_nonneg_left (norm_nonneg _) hsp hsps
        have a2 : bridgeSlope * (x - p) / x ^ (1 / 2 : ℝ) ≤ bridgeSlope * (g / p ^ (1 / 2 : ℝ)) := by
          rw [mul_div_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hS0
          calc (x - p) / x ^ (1 / 2 : ℝ) ≤ g / x ^ (1 / 2 : ℝ) := div_le_div_of_nonneg_right hg hsx.le
            _ ≤ g / p ^ (1 / 2 : ℝ) := div_le_div_of_nonneg_left hg0 hsp hsps
        have a3 : bridgeOffset / x ^ (1 / 2 : ℝ) ≤ bridgeOffset := div_le_self hO0 h1sx
        linarith

/-! ## 5. Le pont, sous écarts de l'ordre de la racine -/

/-- **Écarts de l'ordre de la racine (hypothèse nommée, jamais posée)** : il existe `G` tel que tout écart
entre premiers consécutifs est au plus `G` fois la racine du premier. Plus forte que ce que RH fournit. -/
def GapsRootOrder : Prop :=
  ∃ G : ℝ, ∀ n : ℕ,
    (fnPrimeAtRank (n + 1) : ℝ) - fnPrimeAtRank n ≤ G * (fnPrimeAtRank n : ℝ) ^ (1 / 2 : ℝ)

/-- Tout point au-delà du premier premier est dans un écart. -/
theorem exists_rank_le_lt {x : ℝ} (hx : (fnPrimeAtRank 0 : ℝ) ≤ x) :
    ∃ n : ℕ, (fnPrimeAtRank n : ℝ) ≤ x ∧ x < fnPrimeAtRank (n + 1) := by
  classical
  have hex : ∃ n : ℕ, x < fnPrimeAtRank (n + 1) := by
    obtain ⟨m, hm⟩ := exists_nat_gt x
    refine ⟨m, hm.trans_le ?_⟩
    have h1 : m + 1 ≤ fnPrimeAtRank (m + 1) := thm_primeAtRank_strictMono.id_le (m + 1)
    exact_mod_cast (Nat.le_succ m).trans h1
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; exact hx
  · have hmin := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hex)] at hmin
    exact not_lt.mp hmin

/-- **Le pont des rencontres** : demande bornée aux rencontres et écarts de l'ordre de la racine donnent la
demande bornée en tout point. -/
theorem demandBoundedEverywhere_of_meetings_of_gaps (hdem : DemandBoundedAtMeetings)
    (hgap : GapsRootOrder) : DemandBoundedEverywhere := by
  obtain ⟨C, hC⟩ := hdem
  obtain ⟨G, hG⟩ := hgap
  obtain ⟨C₁, hC₁⟩ := smoothedRemainder_linear_growth
  refine ⟨max (|C₁| * (fnPrimeAtRank 1 : ℝ) ^ (1 / 2 : ℝ)) (C + bridgeSlope * G + bridgeOffset),
    fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  by_cases hxp : x < (fnPrimeAtRank 1 : ℝ)
  · refine le_trans ?_ (le_max_left _ _)
    unfold demandRelativeLevel
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)]
    calc ‖smoothedRemainder x‖ ≤ C₁ * x ^ (1 : ℝ) := hC₁ x hx
      _ ≤ |C₁| * x := by
          rw [Real.rpow_one]
          exact mul_le_mul_of_nonneg_right (le_abs_self C₁) hx0.le
      _ = |C₁| * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by
          rw [← Real.rpow_add hx0]; norm_num
      _ ≤ |C₁| * ((fnPrimeAtRank 1 : ℝ) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx0.le hxp.le (by norm_num))
            (Real.rpow_nonneg hx0.le _)
      _ = |C₁| * (fnPrimeAtRank 1 : ℝ) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by ring
  · push Not at hxp
    have h0 : (fnPrimeAtRank 0 : ℝ) ≤ x := by
      have h01 : fnPrimeAtRank 0 < fnPrimeAtRank 1 := thm_primeAtRank_strictMono (by norm_num)
      have h01' : (fnPrimeAtRank 0 : ℝ) < fnPrimeAtRank 1 := by exact_mod_cast h01
      linarith
    obtain ⟨n, hn1, hn2⟩ := exists_rank_le_lt h0
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      rcases n with _ | m
      · exact absurd (lt_of_le_of_lt hxp hn2) (lt_irrefl _)
      · exact ⟨m, rfl⟩
    refine le_trans ?_ (le_max_right _ _)
    have hpm : 1 < (fnPrimeAtRank (m + 1) : ℝ) := by
      have h2 := (thm_primeAtRank_isPrime (m + 1)).two_le
      exact_mod_cast (by omega : 1 < fnPrimeAtRank (m + 1))
    have hgm : x - (fnPrimeAtRank (m + 1) : ℝ) ≤ G * (fnPrimeAtRank (m + 1) : ℝ) ^ (1 / 2 : ℝ) := by
      have := hG (m + 1)
      linarith
    have key := demandRelativeLevel_le_of_mem_gap hpm hn1 hgm
    have hdiv : G * (fnPrimeAtRank (m + 1) : ℝ) ^ (1 / 2 : ℝ) / (fnPrimeAtRank (m + 1) : ℝ) ^ (1 / 2 : ℝ)
        = G := mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos (by linarith) _).ne'
    rw [hdiv] at key
    have hCm : demandRelativeLevel (fnPrimeAtRank (m + 1) : ℝ) ≤ C := hC ⟨m⟩
    linarith

/-- **Le pont nommé de `DemandLevelPremise.lean` est vrai sous écarts de l'ordre de la racine.** -/
theorem meetingsBridge_of_gaps (hgap : GapsRootOrder) : MeetingsBridge :=
  fun hdem => demandBoundedEverywhere_of_meetings_of_gaps hdem hgap

/-- **Hypothèse de clôture + écarts de l'ordre de la racine donnent RH.** Deux hypothèses nommées sur les seuls
premiers, aucun zéro. -/
theorem riemannHypothesis_of_meetings_of_gaps (hdem : DemandBoundedAtMeetings) (hgap : GapsRootOrder) :
    RiemannHypothesis :=
  riemannHypothesis_of_demandBoundedEverywhere (demandBoundedEverywhere_of_meetings_of_gaps hdem hgap)

/-- Sous écarts de l'ordre de la racine, l'hypothèse de clôture seule est la prémisse unique de la chaîne. -/
theorem expectedFrequencyRises_iff_meetings_of_gaps (hgap : GapsRootOrder) :
    ExpectedFrequencyRises ↔ DemandBoundedAtMeetings :=
  expectedFrequencyRises_iff_meetings_of_bridge (meetingsBridge_of_gaps hgap)

end RHV6Fresh
