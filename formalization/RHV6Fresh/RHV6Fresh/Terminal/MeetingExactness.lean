/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MeetingPoint

/-!
# L'exactitude comme demande aux points de rencontre (module isolé, non importé par la chaîne, 2026-10-29)

Validé par l'auteur après E395 (« la constance tient aux points de rencontre ET au fait que tous les zéros jusqu'à
l'infini doivent accomplir le reste exact ; cette exactitude est aussi une demande »). Deux faits, dérivés des seules
définitions, sans prémisse, sans hypothèse sur aucune position radiale :

1. **À l'intérieur d'un écart, la demande est fixée par l'état à la rencontre précédente.** L'état arithmétique à
   l'entier `N` est le couple (masse de von Mangoldt, masse pondérée) jusqu'à `N`. Sur toute cellule `]N, N+1]` la somme
   lissée vaut `massA N − massB N / x` (`smoothedVonMangoldtSum_cell`) ; sur un écart premier sans puissance de premier à
   l'intérieur, l'incrément de la demande du premier `p` à tout point `x ≤ p'` est `massB p · (1/p − 1/x)` moins
   l'incrément du fond (`demand_interior_fixed_by_meeting`). Seule la rencontre change l'état : le poids du premier
   suivant entre dans les deux masses (`state_jump_at_meeting`).
2. **Aucune famille finie de parts n'accomplit la demande sur un voisinage d'une rencontre.** La somme lissée n'est pas
   dérivable en un premier : ses dérivées à gauche et à droite diffèrent exactement du poids du premier divisé par le
   premier (`smoothedVonMangoldtSum_not_differentiableAt_prime`). Le fond est dérivable pour `x > 1`
   (`smoothedZeroBackground_differentiableAt`), donc le reste ne l'est pas à la rencontre
   (`smoothedRemainder_not_differentiableAt_meeting`). Toute somme finie de parts est dérivable
   (`finite_family_differentiableAt`), donc aucune n'égale le reste au voisinage d'une rencontre
   (`no_finite_family_accomplishes_demand`), et la queue infinie n'y est jamais identiquement nulle
   (`tail_not_eventually_zero`). Avec la synchronisation compilée (`localSynchronization`), la demande à la rencontre est
   accomplie par la totalité des zéros et par aucune partie finie (`exactness_is_a_demand`).

Aucune ligne de la chaîne n'est modifiée. Axiomes standard seulement (voir `#print axioms`).
-/

namespace RHV6Fresh

open Complex RHV3Lean ArithmeticFunction Set Filter Topology

/-! ## 1. L'état arithmétique et la cellule -/

/-- Masse de von Mangoldt jusqu'à `N` (inclus). -/
noncomputable def massA (N : ℕ) : ℝ := ∑ n ∈ Finset.range (N + 1), vonMangoldt n

/-- Masse de von Mangoldt pondérée par l'entier, jusqu'à `N` (inclus). -/
noncomputable def massB (N : ℕ) : ℝ := ∑ n ∈ Finset.range (N + 1), (n : ℝ) * vonMangoldt n

theorem massA_succ (N : ℕ) : massA (N + 1) = massA N + vonMangoldt (N + 1) := by
  unfold massA; rw [Finset.sum_range_succ]

theorem massB_succ (N : ℕ) : massB (N + 1) = massB N + ((N + 1 : ℕ) : ℝ) * vonMangoldt (N + 1) := by
  unfold massB; rw [Finset.sum_range_succ]

/-- La somme lissée en partie réelle explicite (même preuve que `PrimeBlockDecomposition`). -/
theorem smoothedVonMangoldtSum_real' (x : ℝ) :
    smoothedVonMangoldtSum x = ((∑ n ∈ Finset.range ⌈x⌉₊, vonMangoldt n * (1 - n / x) : ℝ) : ℂ) := by
  unfold smoothedVonMangoldtSum; push_cast; rfl

/-- **Cellule** : sur `]N, N+1]`, la somme lissée est fixée par l'état en `N` et par `x`. -/
theorem smoothedVonMangoldtSum_cell {N : ℕ} {x : ℝ} (hx : (N : ℝ) < x) (hx' : x ≤ N + 1) :
    smoothedVonMangoldtSum x = ((massA N - massB N * x⁻¹ : ℝ) : ℂ) := by
  have hx0 : x ≠ 0 := (lt_of_le_of_lt (Nat.cast_nonneg N) hx).ne'
  have hceil : ⌈x⌉₊ = N + 1 := by
    rw [Nat.ceil_eq_iff (by omega)]; push_cast; exact ⟨by simpa using hx, hx'⟩
  rw [smoothedVonMangoldtSum_real', hceil]
  congr 1
  unfold massA massB
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  first
  | (field_simp; done)
  | (field_simp; ring)

/-- En un entier `N ≥ 1`, la même formule (le terme de `N` entre avec le poids nul `1 − N/N`). -/
theorem smoothedVonMangoldtSum_natCast_state {N : ℕ} (hN : 1 ≤ N) :
    smoothedVonMangoldtSum (N : ℝ) = ((massA N - massB N * (N : ℝ)⁻¹ : ℝ) : ℂ) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [smoothedVonMangoldtSum_real', Nat.ceil_natCast]
  congr 1
  unfold massA massB
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have h1 : ∑ n ∈ Finset.range N, vonMangoldt n * (1 - n / N) =
      ∑ n ∈ Finset.range N, (vonMangoldt n - n * vonMangoldt n * (N : ℝ)⁻¹) :=
    Finset.sum_congr rfl fun n _ => by
      first
      | (field_simp; done)
      | (field_simp; ring)
  rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul]
  first
  | (field_simp; done)
  | (field_simp; ring)

/-! ## 2. Rien n'arrive à l'intérieur d'un écart -/

/-- Aucun événement (poids de von Mangoldt non nul) dans `]N, M]`. -/
def NoEventBetween (N M : ℕ) : Prop := ∀ k : ℕ, N < k → k ≤ M → vonMangoldt k = 0

theorem massA_eq_of_noEvent {N M : ℕ} (hNM : N ≤ M) (h : NoEventBetween N M) : massA M = massA N := by
  unfold massA
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.add_le_add_right hNM 1)]
  have h0 : ∑ k ∈ Finset.Ico (N + 1) (M + 1), vonMangoldt k = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    exact h k (by omega) (by omega)
  rw [h0, add_zero]

theorem massB_eq_of_noEvent {N M : ℕ} (hNM : N ≤ M) (h : NoEventBetween N M) : massB M = massB N := by
  unfold massB
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.add_le_add_right hNM 1)]
  have h0 : ∑ k ∈ Finset.Ico (N + 1) (M + 1), (k : ℝ) * vonMangoldt k = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    rw [h k (by omega) (by omega), mul_zero]
  rw [h0, add_zero]

/-- **Sans événement entre `N` et `x`, la somme lissée en `x` est fixée par l'état en `N` et par `x`.** -/
theorem smoothedVonMangoldtSum_gap_state {N : ℕ} {x : ℝ} (hx : (N : ℝ) < x)
    (hno : ∀ k : ℕ, N < k → (k : ℝ) < x → vonMangoldt k = 0) :
    smoothedVonMangoldtSum x = ((massA N - massB N * x⁻¹ : ℝ) : ℂ) := by
  have hpos : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr (lt_of_le_of_lt (Nat.cast_nonneg N) hx)
  obtain ⟨M, hM1⟩ : ∃ M, ⌈x⌉₊ = M + 1 := ⟨⌈x⌉₊ - 1, by omega⟩
  have hxM : (M : ℝ) < x := Nat.lt_ceil.mp (by omega)
  have hxM' : x ≤ M + 1 := by
    have h := Nat.le_ceil x
    rw [hM1] at h; push_cast at h; exact h
  rw [smoothedVonMangoldtSum_cell hxM hxM']
  have hNM : N ≤ M := by
    have h1 : (N : ℝ) < M + 1 := lt_of_lt_of_le hx hxM'
    have h2 : N < M + 1 := by exact_mod_cast h1
    omega
  have hne : NoEventBetween N M := fun k hk hkM =>
    hno k hk (lt_of_le_of_lt (by exact_mod_cast hkM) hxM)
  rw [massA_eq_of_noEvent hNM hne, massB_eq_of_noEvent hNM hne]

/-- **La demande à l'intérieur d'un écart est fixée par la rencontre précédente.** Sur l'écart `I` sans puissance
de premier à l'intérieur, pour tout `x` entre le premier `p` (exclu) et la rencontre (incluse), l'incrément du reste de
`p` à `x` est `massB p · (1/p − 1/x)` moins l'incrément du fond : rien d'autre n'y entre. -/
theorem demand_interior_fixed_by_meeting (I : PrimeGapInterval) {x : ℝ}
    (hx : I.lower < x) (hx' : x ≤ meetingPoint I)
    (hno : ∀ k : ℕ, fnPrimeAtRank I.rank < k → k < fnPrimeAtRank (I.rank + 1) → vonMangoldt k = 0) :
    smoothedRemainder x - smoothedRemainder I.lower =
      ((massB (fnPrimeAtRank I.rank) * ((fnPrimeAtRank I.rank : ℝ)⁻¹ - x⁻¹) : ℝ) : ℂ)
        - (smoothedZeroBackground x - smoothedZeroBackground I.lower) := by
  have hp1 : 1 ≤ fnPrimeAtRank I.rank := (thm_primeAtRank_isPrime _).one_lt.le
  have hlow : I.lower = (fnPrimeAtRank I.rank : ℝ) := rfl
  have hup : meetingPoint I = (fnPrimeAtRank (I.rank + 1) : ℝ) := rfl
  rw [hlow] at hx ⊢
  rw [hup] at hx'
  have hno' : ∀ k : ℕ, fnPrimeAtRank I.rank < k → (k : ℝ) < x → vonMangoldt k = 0 := by
    intro k hk hkx
    apply hno k hk
    have : (k : ℝ) < fnPrimeAtRank (I.rank + 1) := lt_of_lt_of_le hkx hx'
    exact_mod_cast this
  unfold smoothedRemainder
  rw [smoothedVonMangoldtSum_gap_state hx hno', smoothedVonMangoldtSum_natCast_state hp1]
  push_cast
  ring

/-- **Seule la rencontre change l'état** : le poids du premier suivant (son logarithme) entre dans les deux masses. -/
theorem state_jump_at_meeting (I : PrimeGapInterval) :
    ∃ M : ℕ, fnPrimeAtRank (I.rank + 1) = M + 1 ∧
      massA (fnPrimeAtRank (I.rank + 1)) = massA M + Real.log (fnPrimeAtRank (I.rank + 1)) ∧
      massB (fnPrimeAtRank (I.rank + 1)) =
        massB M + (fnPrimeAtRank (I.rank + 1) : ℝ) * Real.log (fnPrimeAtRank (I.rank + 1)) := by
  have hq : (fnPrimeAtRank (I.rank + 1)).Prime := thm_primeAtRank_isPrime _
  obtain ⟨M, hM⟩ : ∃ M, fnPrimeAtRank (I.rank + 1) = M + 1 := ⟨fnPrimeAtRank (I.rank + 1) - 1, by have := hq.two_le; omega⟩
  refine ⟨M, hM, ?_, ?_⟩
  · rw [hM, massA_succ, ← hM, vonMangoldt_apply_prime hq]
  · rw [hM, massB_succ, ← hM, vonMangoldt_apply_prime hq]

/-! ## 3. La somme lissée n'est pas dérivable en un premier -/

theorem hasDerivAt_state (N : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => ((massA N - massB N * y⁻¹ : ℝ) : ℂ))
      ((massB N * (x ^ 2)⁻¹ : ℝ) : ℂ) x := by
  have h := (((hasDerivAt_inv hx).const_mul (massB N)).const_sub (massA N)).ofReal_comp
  convert h using 1
  push_cast
  ring

/-- **La somme lissée n'est pas dérivable en un premier** : dérivée à droite `massB q / q²`, à gauche
`massB (q−1) / q²`, et leur différence est le poids du premier divisé par `q`, strictement positif. -/
theorem smoothedVonMangoldtSum_not_differentiableAt_prime {q : ℕ} (hq : q.Prime) :
    ¬ DifferentiableAt ℝ smoothedVonMangoldtSum (q : ℝ) := by
  obtain ⟨M, rfl⟩ : ∃ M, q = M + 1 := ⟨q - 1, by have := hq.two_le; omega⟩
  intro hdiff
  have hq0 : ((M + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hM1 : (M : ℝ) < ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
  -- dérivée à droite, état en `M + 1`
  have hR : HasDerivWithinAt smoothedVonMangoldtSum
      ((massB (M + 1) * (((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) (Ici ((M + 1 : ℕ) : ℝ)) ((M + 1 : ℕ) : ℝ) := by
    refine ((hasDerivAt_state (M + 1) hq0).hasDerivWithinAt).congr_of_eventuallyEq ?_
      (smoothedVonMangoldtSum_natCast_state (by omega))
    have hmem : Ici ((M + 1 : ℕ) : ℝ) ∩ Iio (((M + 1 : ℕ) : ℝ) + 1) ∈ 𝓝[Ici ((M + 1 : ℕ) : ℝ)] ((M + 1 : ℕ) : ℝ) :=
      inter_mem_nhdsWithin _ (Iio_mem_nhds (lt_add_one _))
    filter_upwards [hmem] with x hx
    rcases eq_or_lt_of_le (mem_Ici.mp hx.1) with heq | hlt
    · rw [← heq]; exact smoothedVonMangoldtSum_natCast_state (by omega)
    · exact smoothedVonMangoldtSum_cell hlt (mem_Iio.mp hx.2).le
  -- dérivée à gauche, état en `M`
  have hL : HasDerivWithinAt smoothedVonMangoldtSum
      ((massB M * (((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) (Iic ((M + 1 : ℕ) : ℝ)) ((M + 1 : ℕ) : ℝ) := by
    refine ((hasDerivAt_state M hq0).hasDerivWithinAt).congr_of_eventuallyEq ?_
      (smoothedVonMangoldtSum_cell hM1 (by push_cast; exact le_rfl))
    have hmem : Iic ((M + 1 : ℕ) : ℝ) ∩ Ioi (M : ℝ) ∈ 𝓝[Iic ((M + 1 : ℕ) : ℝ)] ((M + 1 : ℕ) : ℝ) :=
      inter_mem_nhdsWithin _ (Ioi_mem_nhds hM1)
    filter_upwards [hmem] with x hx
    exact smoothedVonMangoldtSum_cell (mem_Ioi.mp hx.2) (by have := mem_Iic.mp hx.1; push_cast at this; exact this)
  have hd := hdiff.hasDerivAt
  have e1 := (uniqueDiffWithinAt_Ici _).eq_deriv _ hd.hasDerivWithinAt hR
  have e2 := (uniqueDiffWithinAt_Iic _).eq_deriv _ hd.hasDerivWithinAt hL
  have e3 := Complex.ofReal_inj.mp (e1.symm.trans e2)
  have hq2 : ((((M + 1 : ℕ) : ℝ)) ^ 2)⁻¹ ≠ 0 := by positivity
  have e4 : massB (M + 1) = massB M := mul_right_cancel₀ hq2 e3
  have hΛ : 0 < vonMangoldt (M + 1) := vonMangoldt_pos_iff.mpr hq.isPrimePow
  have hqpos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have := massB_succ M
  nlinarith [mul_pos hqpos hΛ]

/-! ## 4. Le fond est dérivable pour `x > 1` -/

theorem hasDerivAt_trivialTerm (n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => trivialZeroResidueTerm z n)
      (-((y : ℂ) ^ (trivialZetaZeroAt n - 1) / (trivialZetaZeroAt n + 1))) y := by
  have ht : trivialZetaZeroAt n ≠ 0 := by
    unfold trivialZetaZeroAt
    have : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    exact mul_ne_zero (by norm_num) this
  have hfun : (fun z : ℝ => trivialZeroResidueTerm z n) =
      fun z : ℝ => -((z : ℂ) ^ trivialZetaZeroAt n / (trivialZetaZeroAt n * (trivialZetaZeroAt n + 1))) := by
    funext z
    simp [trivialZeroResidueTerm, zetaZeroMultiplicity_trivialZetaZeroAt, Perron.f]
  rw [hfun]
  have h := ((hasDerivAt_ofReal_cpow_const hy.ne' ht).div_const
    (trivialZetaZeroAt n * (trivialZetaZeroAt n + 1))).neg
  exact h.congr_deriv (by rw [mul_div_mul_left _ _ ht])

theorem trivialTerm_deriv_norm_le (n : ℕ) {r y : ℝ} (hr : 1 < r) (hy : r ≤ y) :
    ‖-((y : ℂ) ^ (trivialZetaZeroAt n - 1) / (trivialZetaZeroAt n + 1))‖ ≤ (r⁻¹) ^ n := by
  have hy0 : 0 < y := by linarith
  have hre : (trivialZetaZeroAt n - 1).re = -(2 * (n : ℝ) + 3) := by
    unfold trivialZetaZeroAt
    first
    | (simp; done)
    | (simp; ring)
  have hden : 1 ≤ ‖trivialZetaZeroAt n + 1‖ := by
    have : trivialZetaZeroAt n + 1 = ((-(2 * (n : ℝ) + 1) : ℝ) : ℂ) := by
      unfold trivialZetaZeroAt; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    linarith
  rw [norm_neg, norm_div, norm_cpow_eq_rpow_re_of_pos hy0, hre]
  have h1 : y ^ (-(2 * (n : ℝ) + 3)) ≤ r ^ (-(2 * (n : ℝ) + 3)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hy (by linarith)
  have h2 : r ^ (-(2 * (n : ℝ) + 3)) = (r⁻¹) ^ (2 * n + 3) := by
    rw [Real.rpow_neg (by linarith), inv_pow]
    norm_cast
  have h3 : (r⁻¹) ^ (2 * n + 3) ≤ (r⁻¹) ^ n :=
    pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hr.le) (by omega)
  calc y ^ (-(2 * (n : ℝ) + 3)) / ‖trivialZetaZeroAt n + 1‖
      ≤ y ^ (-(2 * (n : ℝ) + 3)) / 1 := div_le_div_of_nonneg_left (by positivity) one_pos hden
    _ = y ^ (-(2 * (n : ℝ) + 3)) := div_one _
    _ ≤ r ^ (-(2 * (n : ℝ) + 3)) := h1
    _ = (r⁻¹) ^ (2 * n + 3) := h2
    _ ≤ (r⁻¹) ^ n := h3

theorem hasDerivAt_trivialZeroSum {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun z : ℝ => ∑' n : ℕ, trivialZeroResidueTerm z n)
      (∑' n : ℕ, -((x : ℂ) ^ (trivialZetaZeroAt n - 1) / (trivialZetaZeroAt n + 1))) x := by
  have hr1 : 1 < (1 + x) / 2 := by linarith
  have hrx : (1 + x) / 2 < x := by linarith
  refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℂ)
    (u := fun n : ℕ => (((1 + x) / 2)⁻¹) ^ n) (t := Ioi ((1 + x) / 2))
    (g := fun n (z : ℝ) => trivialZeroResidueTerm z n)
    (g' := fun n (y : ℝ) => -((y : ℂ) ^ (trivialZetaZeroAt n - 1) / (trivialZetaZeroAt n + 1)))
    ?_ isOpen_Ioi isPreconnected_Ioi ?_ ?_ (y₀ := x) hrx ?_ hrx
  · exact summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hr1)
  · intro n y hy
    exact hasDerivAt_trivialTerm n (by linarith [mem_Ioi.mp hy])
  · intro n y hy
    exact trivialTerm_deriv_norm_le n hr1 (le_of_lt (mem_Ioi.mp hy))
  · exact trivial_zero_residue_series_summable hx

/-- **Le fond est dérivable pour `x > 1`** (il ne contient aucun zéro non trivial). -/
theorem smoothedZeroBackground_differentiableAt {x : ℝ} (hx : 1 < x) :
    DifferentiableAt ℝ smoothedZeroBackground x := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by linarith)
  have h1 : DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) / 2) x :=
    ((hasDerivAt_id x).ofReal_comp.div_const 2).differentiableAt
  have h2 : DifferentiableAt ℝ (fun y : ℝ => logDeriv riemannZeta (-1) * (y : ℂ)⁻¹) x :=
    ((hasDerivAt_inv hx0).comp_ofReal.const_mul _).differentiableAt
  have h3 := (hasDerivAt_trivialZeroSum hx).differentiableAt
  have hfun : smoothedZeroBackground = fun y : ℝ => (y : ℂ) / 2 + (-logDeriv riemannZeta 0) +
      logDeriv riemannZeta (-1) * (y : ℂ)⁻¹ + ∑' n : ℕ, trivialZeroResidueTerm y n := by
    funext y; rfl
  rw [hfun]
  exact ((h1.add_const _).add h2).add h3

/-! ## 5. Aucune famille finie n'accomplit la demande au voisinage d'une rencontre -/

/-- **Le reste n'est pas dérivable à la rencontre** (somme lissée non dérivable, fond dérivable). -/
theorem smoothedRemainder_not_differentiableAt_meeting (I : PrimeGapInterval) :
    ¬ DifferentiableAt ℝ smoothedRemainder (meetingPoint I) := by
  intro h
  have hq : (fnPrimeAtRank (I.rank + 1)).Prime := thm_primeAtRank_isPrime _
  have hmp : meetingPoint I = (fnPrimeAtRank (I.rank + 1) : ℝ) := rfl
  have hB := smoothedZeroBackground_differentiableAt I.one_lt_upper
  have hS : DifferentiableAt ℝ smoothedVonMangoldtSum (meetingPoint I) := by
    have hfun : smoothedVonMangoldtSum = fun y => smoothedRemainder y + smoothedZeroBackground y := by
      funext y; unfold smoothedRemainder; ring
    rw [hfun]; exact h.add hB
  rw [hmp] at hS
  exact smoothedVonMangoldtSum_not_differentiableAt_prime hq hS

/-- La part d'un vrai zéro est dérivable en tout `x > 0`. -/
theorem residueTerm_differentiableAt (ρ : ExplicitIndex) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (fun y : ℝ => nontrivialZeroResidueTerm y ρ) x := by
  obtain ⟨h0, _⟩ := explicitIndex_ne_zero ρ
  have hfun : (fun y : ℝ => nontrivialZeroResidueTerm y ρ) =
      fun y : ℝ => -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * ((y : ℂ) ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))) := by
    funext y; rfl
  rw [hfun]
  exact (((hasDerivAt_ofReal_cpow_const hx.ne' h0).div_const _).const_mul _).differentiableAt

/-- **Toute famille finie de parts est dérivable.** -/
theorem finite_family_differentiableAt (s : Finset ExplicitIndex) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (fun y : ℝ => ∑ ρ ∈ s, nontrivialZeroResidueTerm y ρ) x :=
  DifferentiableAt.fun_sum fun ρ _ => residueTerm_differentiableAt ρ hx

/-- **Aucune famille finie de parts n'accomplit la demande sur un voisinage d'une rencontre.** -/
theorem no_finite_family_accomplishes_demand (I : PrimeGapInterval) (s : Finset ExplicitIndex) :
    ¬ (∀ᶠ x in 𝓝 (meetingPoint I), smoothedRemainder x = ∑ ρ ∈ s, nontrivialZeroResidueTerm x ρ) := by
  intro h
  have hpos : (0 : ℝ) < meetingPoint I := by
    have h1 : (1 : ℝ) < meetingPoint I := I.one_lt_upper
    linarith
  exact smoothedRemainder_not_differentiableAt_meeting I
    ((finite_family_differentiableAt s hpos).congr_of_eventuallyEq h)

/-- **La queue infinie n'est jamais identiquement nulle au voisinage d'une rencontre** : ce qu'une famille finie
laisse dû à la rencontre n'est accompli que par les zéros omis. -/
theorem tail_not_eventually_zero (I : PrimeGapInterval) (s : Finset ExplicitIndex) :
    ¬ (∀ᶠ x in 𝓝 (meetingPoint I),
        ∑' ρ : ((s : Set ExplicitIndex)ᶜ : Set ExplicitIndex), nontrivialZeroResidueTerm x ρ.1 = 0) := by
  intro h
  apply no_finite_family_accomplishes_demand I s
  filter_upwards [h, eventually_gt_nhds I.one_lt_upper] with x hx hx1
  rw [smoothedRemainder_eq_tsum_residueTerm hx1,
    ← (nontrivial_zero_residue_series_summable hx1).sum_add_tsum_compl (s := s), hx, add_zero]

/-- **L'exactitude est une demande** : à chaque rencontre, la demande de l'écart est accomplie par la totalité des
zéros (synchronisation compilée) et par aucune famille finie sur un voisinage de la rencontre. -/
theorem exactness_is_a_demand (I : PrimeGapInterval) :
    localArithmeticTarget I = ∑' ρ : ExplicitIndex, smoothedLocalContribution ρ I ∧
      ∀ s : Finset ExplicitIndex,
        ¬ (∀ᶠ x in 𝓝 (meetingPoint I), smoothedRemainder x = ∑ ρ ∈ s, nontrivialZeroResidueTerm x ρ) :=
  ⟨localSynchronization I, fun s => no_finite_family_accomplishes_demand I s⟩

#print axioms RHV6Fresh.demand_interior_fixed_by_meeting
#print axioms RHV6Fresh.state_jump_at_meeting
#print axioms RHV6Fresh.smoothedVonMangoldtSum_not_differentiableAt_prime
#print axioms RHV6Fresh.smoothedZeroBackground_differentiableAt
#print axioms RHV6Fresh.no_finite_family_accomplishes_demand
#print axioms RHV6Fresh.tail_not_eventually_zero
#print axioms RHV6Fresh.exactness_is_a_demand

end RHV6Fresh
