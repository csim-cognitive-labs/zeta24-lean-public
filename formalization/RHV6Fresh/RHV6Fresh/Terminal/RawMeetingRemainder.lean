/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MeetingExactness
import RHV6Fresh.Terminal.RemainderExponent

/-!
# Le reste brut aux points de rencontre (§19.35, module isolé, 2026-11-02)

Module ISOLÉ (non ajouté à `RHV6Fresh.lean`). Canal BRUT côté premiers, élémentaire : le reste brut
à
l'entier `N` est `ψ(N) − N`, écrit avec `massA` de `MeetingExactness` (`psiRemainder` ; l'objet réel
`rawRemainder` du corpus, avec fond, n'est pas touché). Aucun zéro n'entre dans sa définition.

1. **Entre deux rencontres brutes** (entiers de poids `Λ` non nul), le reste brut descend
d'exactement
   une unité par entier (`psiRemainder_of_noEvent`) ; il est donc pris entre ses valeurs aux deux
   rencontres (`abs_psiRemainder_le_of_noEvent`). À la rencontre il saute du poids
   (`psiRemainder_succ`).
2. **Pont brut → lissé à l'entier** : `M · A(M)` est le cumul brut, somme des `ψ(k)` pour `k < M`
   (`natMul_smoothedVonMangoldtSum_eq`, `rawCumulative_eq_sum_massA`, `sum_psiRemainder`).
3. **Réduction aux rencontres** : une borne `|ψ(E) − E| ≤ C·E^θ` des deux côtés de chaque rencontre
   brute se propage à tout entier (`psiRemainder_bound_of_events`, Bertrand), puis au reste lissé
   partout (`mem_remainderExponents_of_psiRemainder`), puis à toute position radiale : `β ≤ θ`
   (`zero_re_le_of_psiRemainder_at_events`) ; avec `θ = 1/2 + ε` pour tout `ε` : RH
   (`riemannHypothesis_of_psiRemainder_at_events`).
4. **Lecture OFF** : un membre à `β` force, pour tout `θ < β` et toute constante, une rencontre
brute
   où le reste brut dépasse `C·E^θ` d'un côté ou de l'autre
   (`off_member_forces_raw_excess_at_event`).

Tout est axe réel (R12) : vrais premiers, vraies rencontres, aucune projection. Aucune hypothèse
nommée, aucun `sorry`. Le manque unique, affiché par le compilateur, est consigné en §19.35.3 : la
borne du reste brut aux rencontres depuis les seuls premiers.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction Finset

/-! ## 1. Le canal brut, lu entier par entier -/

/-- Reste brut à l'entier `N` : masse de von Mangoldt jusqu'à `N` moins `N` (après le saut en `N`).
-/
noncomputable def psiRemainder (N : ℕ) : ℝ := massA N - N

/-- D'un entier au suivant : saut du poids de l'entier, descente d'une unité. -/
theorem psiRemainder_succ (N : ℕ) :
    psiRemainder (N + 1) = psiRemainder N + vonMangoldt (N + 1) - 1 := by
  unfold psiRemainder; rw [massA_succ]; push_cast; ring

/-- Entre deux rencontres (aucun événement dans `]N, M]`) : descente d'exactement une unité par
entier. -/
theorem psiRemainder_of_noEvent {N M : ℕ} (hNM : N ≤ M) (h : NoEventBetween N M) :
    psiRemainder M = psiRemainder N - ((M - N : ℕ) : ℝ) := by
  unfold psiRemainder; rw [massA_eq_of_noEvent hNM h, Nat.cast_sub hNM]; ring

/-- **Encadrement par les rencontres** : entre deux rencontres, le reste brut est pris entre ses
valeurs
aux deux bouts. -/
theorem abs_psiRemainder_le_of_noEvent {N K M : ℕ} (hNK : N ≤ K) (hKM : K ≤ M)
    (h : NoEventBetween N M) :
    |psiRemainder K| ≤ max |psiRemainder N| |psiRemainder M| := by
  have hK := psiRemainder_of_noEvent hNK (fun k hk hk' => h k hk (hk'.trans hKM))
  have hM := psiRemainder_of_noEvent (hNK.trans hKM) h
  have hc : ((K - N : ℕ) : ℝ) ≤ ((M - N : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le_sub_right hKM N
  have h0 : (0 : ℝ) ≤ ((K - N : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor
  · have h1 := neg_abs_le (psiRemainder M)
    have h2 := le_max_right |psiRemainder N| |psiRemainder M|
    linarith
  · have h1 := le_abs_self (psiRemainder N)
    have h2 := le_max_left |psiRemainder N| |psiRemainder M|
    linarith

/-! ## 2. Le cumul brut et le pont vers le canal lissé -/

/-- Cumul brut à l'entier `M` : `Σ_{n<M} Λ(n)·(M − n)`. -/
noncomputable def rawCumulative (M : ℕ) : ℝ := ∑ n ∈ range M, vonMangoldt n * ((M : ℝ) - n)

theorem rawCumulative_succ (M : ℕ) : rawCumulative (M + 1) = rawCumulative M + massA M := by
  unfold rawCumulative massA
  rw [sum_range_succ _ M, sum_range_succ _ M]
  push_cast
  have hc : ∀ n ∈ range M, vonMangoldt n * ((M : ℝ) + 1 - n) =
      vonMangoldt n * ((M : ℝ) - n) + vonMangoldt n := fun n _ => by ring
  rw [sum_congr rfl hc, sum_add_distrib]
  ring

/-- Le cumul brut est la somme des `ψ(k)`, `k < M`. -/
theorem rawCumulative_eq_sum_massA (M : ℕ) : rawCumulative M = ∑ k ∈ range M, massA k := by
  induction M with
  | zero => simp [rawCumulative]
  | succ M ih => rw [rawCumulative_succ, ih, sum_range_succ]

/-- **Pont brut → lissé à l'entier** : `M · A(M)` est le cumul brut. -/
theorem natMul_smoothedVonMangoldtSum_eq (M : ℕ) :
    (M : ℂ) * smoothedVonMangoldtSum (M : ℝ) = (rawCumulative M : ℂ) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [rawCumulative]
  · have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [smoothedVonMangoldtSum_real', Nat.ceil_natCast]
    unfold rawCumulative
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    congr 1
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    field_simp

/-- Somme des restes bruts : cumul brut moins l'aire du triangle. -/
theorem sum_psiRemainder (M : ℕ) :
    ∑ k ∈ range M, psiRemainder k = rawCumulative M - (M : ℝ) * ((M : ℝ) - 1) / 2 := by
  have htri : ∀ M : ℕ, ∑ k ∈ range M, (k : ℝ) = (M : ℝ) * ((M : ℝ) - 1) / 2 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih => rw [sum_range_succ, ih]; push_cast; ring
  rw [rawCumulative_eq_sum_massA]
  unfold psiRemainder
  rw [sum_sub_distrib, htri]

/-! ## 3. Le fond, à une constante près -/

/-- Constante du fond : les parties du fond lissé autres que `x/2`. -/
noncomputable def backgroundConstant : ℝ :=
  ‖-logDeriv riemannZeta 0‖ + ‖logDeriv riemannZeta (-1)‖ + ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2

theorem backgroundConstant_nonneg : 0 ≤ backgroundConstant := by
  unfold backgroundConstant
  have hK : 0 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := tsum_nonneg fun n => by positivity
  linarith [norm_nonneg (-logDeriv riemannZeta 0), norm_nonneg (logDeriv riemannZeta (-1))]

/-- Le fond moins `x/2` est borné pour `x > 1`. -/
theorem norm_background_sub_half_le {x : ℝ} (hx : 1 < x) :
    ‖smoothedZeroBackground x - (x : ℂ) / 2‖ ≤ backgroundConstant := by
  have hx0 : 0 < x := lt_trans one_pos hx
  have hT := trivialZeroSum_norm_le hx
  have hinv : ‖logDeriv riemannZeta (-1) * (x : ℂ)⁻¹‖ ≤ ‖logDeriv riemannZeta (-1)‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    exact mul_le_of_le_one_right (norm_nonneg _) (inv_le_one_of_one_le₀ hx.le)
  have heq : smoothedZeroBackground x - (x : ℂ) / 2 = (-logDeriv riemannZeta 0) +
      logDeriv riemannZeta (-1) * (x : ℂ)⁻¹ + ∑' n : ℕ, trivialZeroResidueTerm x n := by
    unfold smoothedZeroBackground; ring
  rw [heq]
  unfold backgroundConstant
  calc ‖(-logDeriv riemannZeta 0) + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹ +
        ∑' n : ℕ, trivialZeroResidueTerm x n‖
      ≤ ‖(-logDeriv riemannZeta 0) + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹‖ +
        ‖∑' n : ℕ, trivialZeroResidueTerm x n‖ := norm_add_le _ _
    _ ≤ (‖-logDeriv riemannZeta 0‖ + ‖logDeriv riemannZeta (-1) * (x : ℂ)⁻¹‖) +
        ‖∑' n : ℕ, trivialZeroResidueTerm x n‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := add_le_add (add_le_add le_rfl hinv) hT

/-! ## 4. Du reste brut aux entiers au reste lissé partout -/

/-- **Aux entiers** : une borne du reste brut à tout entier donne une borne du reste lissé à tout
entier `M ≥ 2`. -/
theorem norm_smoothedRemainder_nat_le {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (h : ∀ k : ℕ, 1 ≤ k → |psiRemainder k| ≤ C * (k : ℝ) ^ θ) {M : ℕ} (hM : 2 ≤ M) :
    ‖smoothedRemainder (M : ℝ)‖ ≤ (C + 1 / 2 + backgroundConstant) * (M : ℝ) ^ θ := by
  have hM1 : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have hMpos : (0 : ℝ) < M := by linarith
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hMθ : (1 : ℝ) ≤ (M : ℝ) ^ θ := Real.one_le_rpow hM1.le hθ
  have hr0 : psiRemainder 0 = 0 := by simp [psiRemainder, massA]
  have hsum : |∑ k ∈ range M, psiRemainder k| ≤ C * (M : ℝ) ^ θ * M := by
    calc |∑ k ∈ range M, psiRemainder k| ≤ ∑ k ∈ range M, |psiRemainder k| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range M, C * (M : ℝ) ^ θ := by
          refine sum_le_sum fun k hk => ?_
          rcases Nat.eq_zero_or_pos k with rfl | hk1
          · rw [hr0, abs_zero]
            exact mul_nonneg hC (Real.rpow_nonneg hMpos.le _)
          · refine (h k hk1).trans (mul_le_mul_of_nonneg_left ?_ hC)
            exact Real.rpow_le_rpow (Nat.cast_nonneg _)
              (by exact_mod_cast (mem_range.mp hk).le) hθ
      _ = C * (M : ℝ) ^ θ * M := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hS : smoothedVonMangoldtSum (M : ℝ) = ((rawCumulative M / M : ℝ) : ℂ) := by
    have hid := natMul_smoothedVonMangoldtSum_eq M
    push_cast
    rw [← hid, mul_div_cancel_left₀ _ hMc]
  have hrc : rawCumulative M / M - (M : ℝ) / 2 = (∑ k ∈ range M, psiRemainder k) / M - 1 / 2 := by
    rw [sum_psiRemainder]
    field_simp
    ring
  have hmain : |rawCumulative M / M - (M : ℝ) / 2| ≤ C * (M : ℝ) ^ θ + 1 / 2 := by
    rw [hrc]
    have h1 : |(∑ k ∈ range M, psiRemainder k) / M| ≤ C * (M : ℝ) ^ θ := by
      rw [abs_div, abs_of_pos hMpos, div_le_iff₀ hMpos]; exact hsum
    have h2 : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_pos (by norm_num)
    have h3 := abs_sub ((∑ k ∈ range M, psiRemainder k) / M) (1 / 2 : ℝ)
    linarith
  have hB := norm_background_sub_half_le hM1
  have hdecomp : smoothedRemainder (M : ℝ) =
      ((rawCumulative M / M - (M : ℝ) / 2 : ℝ) : ℂ) -
        (smoothedZeroBackground (M : ℝ) - ((M : ℝ) : ℂ) / 2) := by
    unfold smoothedRemainder; rw [hS]; push_cast; ring
  rw [hdecomp]
  calc ‖((rawCumulative M / M - (M : ℝ) / 2 : ℝ) : ℂ) -
        (smoothedZeroBackground (M : ℝ) - ((M : ℝ) : ℂ) / 2)‖
      ≤ ‖((rawCumulative M / M - (M : ℝ) / 2 : ℝ) : ℂ)‖ +
        ‖smoothedZeroBackground (M : ℝ) - ((M : ℝ) : ℂ) / 2‖ := norm_sub_le _ _
    _ ≤ (C * (M : ℝ) ^ θ + 1 / 2) + backgroundConstant := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact add_le_add hmain hB
    _ ≤ (C + 1 / 2 + backgroundConstant) * (M : ℝ) ^ θ := by
        nlinarith [mul_nonneg (by linarith [backgroundConstant_nonneg] :
          (0 : ℝ) ≤ 1 / 2 + backgroundConstant) (sub_nonneg.mpr hMθ)]

/-- Sur la cellule `]N, N+1]`, `N ≥ 2` : la somme lissée est croissante en `x` (poids `Λ ≥ 0`) et le
fond varie
d'au plus une constante, donc le reste en `x` est contrôlé par le reste aux deux entiers. -/
theorem norm_smoothedRemainder_cell_le {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : (N : ℝ) < x)
    (hx' : x ≤ N + 1) :
    ‖smoothedRemainder x‖ ≤ ‖smoothedRemainder ((N + 1 : ℕ) : ℝ)‖ +
      2 * ‖smoothedRemainder (N : ℝ)‖ + 1 + 4 * backgroundConstant := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hx1 : 1 < x := by linarith
  have hN1' : (N : ℝ) < ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hAx := smoothedVonMangoldtSum_cell hx hx'
  have hAN := smoothedVonMangoldtSum_natCast_state (N := N) (by omega)
  have hAN1 := smoothedVonMangoldtSum_cell hN1' (by push_cast; exact le_rfl)
  have hmB : 0 ≤ massB N := sum_nonneg fun n _ => mul_nonneg (Nat.cast_nonneg _) vonMangoldt_nonneg
  -- monotonie : A(N) ≤ A(x) ≤ A(N+1), en réels
  have hinv1 : x⁻¹ ≤ (N : ℝ)⁻¹ := inv_anti₀ hNpos hx.le
  have hinv2 : (((N + 1 : ℕ) : ℝ))⁻¹ ≤ x⁻¹ := inv_anti₀ (by linarith) (by push_cast; exact hx')
  have hmono1 : massA N - massB N * (N : ℝ)⁻¹ ≤ massA N - massB N * x⁻¹ := by nlinarith
  have hmono2 : massA N - massB N * x⁻¹ ≤ massA N - massB N * (((N + 1 : ℕ) : ℝ))⁻¹ := by nlinarith
  have hSx : ‖smoothedVonMangoldtSum x - smoothedVonMangoldtSum (N : ℝ)‖ ≤
      ‖smoothedVonMangoldtSum ((N + 1 : ℕ) : ℝ) - smoothedVonMangoldtSum (N : ℝ)‖ := by
    rw [hAx, hAN, hAN1, ← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  -- le fond varie d'au plus 1/2 + 2·constante sur la cellule et entre N et N+1
  have hBx := norm_background_sub_half_le hx1
  have hBN := norm_background_sub_half_le hN1
  have hBN1 := norm_background_sub_half_le (hN1.trans hN1')
  have hhalf1 : ‖(x : ℂ) / 2 - ((N : ℝ) : ℂ) / 2‖ ≤ 1 / 2 := by
    rw [← sub_div, ← Complex.ofReal_sub, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    norm_num
    linarith
  have hhalf2 : ‖(((N + 1 : ℕ) : ℝ) : ℂ) / 2 - ((N : ℝ) : ℂ) / 2‖ ≤ 1 / 2 := by
    rw [← sub_div, ← Complex.ofReal_sub, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    norm_num
  have hBdx : ‖smoothedZeroBackground x - smoothedZeroBackground (N : ℝ)‖ ≤
      1 / 2 + 2 * backgroundConstant := by
    have heq : smoothedZeroBackground x - smoothedZeroBackground (N : ℝ) =
        (smoothedZeroBackground x - (x : ℂ) / 2) -
          (smoothedZeroBackground (N : ℝ) - ((N : ℝ) : ℂ) / 2)
          + ((x : ℂ) / 2 - ((N : ℝ) : ℂ) / 2) := by ring
    rw [heq]
    calc _ ≤ ‖(smoothedZeroBackground x - (x : ℂ) / 2) -
            (smoothedZeroBackground (N : ℝ) - ((N : ℝ) : ℂ) / 2)‖ +
          ‖(x : ℂ) / 2 - ((N : ℝ) : ℂ) / 2‖ := norm_add_le _ _
      _ ≤ (‖smoothedZeroBackground x - (x : ℂ) / 2‖ +
            ‖smoothedZeroBackground (N : ℝ) - ((N : ℝ) : ℂ) / 2‖) +
          ‖(x : ℂ) / 2 - ((N : ℝ) : ℂ) / 2‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ _ := by linarith
  have hBdN : ‖smoothedZeroBackground ((N + 1 : ℕ) : ℝ) - smoothedZeroBackground (N : ℝ)‖ ≤
      1 / 2 + 2 * backgroundConstant := by
    have heq : smoothedZeroBackground ((N + 1 : ℕ) : ℝ) - smoothedZeroBackground (N : ℝ) =
        (smoothedZeroBackground ((N + 1 : ℕ) : ℝ) - (((N + 1 : ℕ) : ℝ) : ℂ) / 2) -
          (smoothedZeroBackground (N : ℝ) - ((N : ℝ) : ℂ) / 2)
          + ((((N + 1 : ℕ) : ℝ) : ℂ) / 2 - ((N : ℝ) : ℂ) / 2) := by ring
    rw [heq]
    calc _ ≤ ‖(smoothedZeroBackground ((N + 1 : ℕ) : ℝ) - (((N + 1 : ℕ) : ℝ) : ℂ) / 2) -
            (smoothedZeroBackground (N : ℝ) - ((N : ℝ) : ℂ) / 2)‖ +
          ‖(((N + 1 : ℕ) : ℝ) : ℂ) / 2 - ((N : ℝ) : ℂ) / 2‖ := norm_add_le _ _
      _ ≤ (‖smoothedZeroBackground ((N + 1 : ℕ) : ℝ) - (((N + 1 : ℕ) : ℝ) : ℂ) / 2‖ +
            ‖smoothedZeroBackground (N : ℝ) - ((N : ℝ) : ℂ) / 2‖) +
          ‖(((N + 1 : ℕ) : ℝ) : ℂ) / 2 - ((N : ℝ) : ℂ) / 2‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ _ := by linarith
  -- la différence des sommes lissées entre N et N+1 est contrôlée par les restes et le fond
  have hSN : ‖smoothedVonMangoldtSum ((N + 1 : ℕ) : ℝ) - smoothedVonMangoldtSum (N : ℝ)‖ ≤
      ‖smoothedRemainder ((N + 1 : ℕ) : ℝ)‖ + ‖smoothedRemainder (N : ℝ)‖ +
        (1 / 2 + 2 * backgroundConstant) := by
    have heq : smoothedVonMangoldtSum ((N + 1 : ℕ) : ℝ) - smoothedVonMangoldtSum (N : ℝ) =
        (smoothedRemainder ((N + 1 : ℕ) : ℝ) - smoothedRemainder (N : ℝ)) +
          (smoothedZeroBackground ((N + 1 : ℕ) : ℝ) - smoothedZeroBackground (N : ℝ)) := by
      unfold smoothedRemainder; ring
    rw [heq]
    calc _ ≤ ‖smoothedRemainder ((N + 1 : ℕ) : ℝ) - smoothedRemainder (N : ℝ)‖ +
          ‖smoothedZeroBackground ((N + 1 : ℕ) : ℝ) - smoothedZeroBackground (N : ℝ)‖ :=
            norm_add_le _ _
      _ ≤ (‖smoothedRemainder ((N + 1 : ℕ) : ℝ)‖ + ‖smoothedRemainder (N : ℝ)‖) +
          (1 / 2 + 2 * backgroundConstant) := by gcongr; exact norm_sub_le _ _
  -- assemblage
  have heq : smoothedRemainder x = (smoothedVonMangoldtSum x - smoothedVonMangoldtSum (N : ℝ)) +
      smoothedRemainder (N : ℝ) - (smoothedZeroBackground x - smoothedZeroBackground (N : ℝ)) := by
    unfold smoothedRemainder; ring
  rw [heq]
  calc _ ≤ ‖(smoothedVonMangoldtSum x - smoothedVonMangoldtSum (N : ℝ)) +
        smoothedRemainder (N : ℝ)‖ +
        ‖smoothedZeroBackground x - smoothedZeroBackground (N : ℝ)‖ := norm_sub_le _ _
    _ ≤ (‖smoothedVonMangoldtSum x - smoothedVonMangoldtSum (N : ℝ)‖ +
        ‖smoothedRemainder (N : ℝ)‖) +
        ‖smoothedZeroBackground x - smoothedZeroBackground (N : ℝ)‖ := by
          gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith

/-- **Du canal brut aux entiers vers un exposant admissible du reste lissé.** -/
theorem mem_remainderExponents_of_psiRemainder {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (h : ∀ k : ℕ, 1 ≤ k → |psiRemainder k| ≤ C * (k : ℝ) ^ θ) : θ ∈ remainderExponents := by
  have hbg := backgroundConstant_nonneg
  set C' := C + 1 / 2 + backgroundConstant with hC'def
  have hC'0 : 0 ≤ C' := by rw [hC'def]; linarith
  have h2θ : (1 : ℝ) ≤ (2 : ℝ) ^ θ := Real.one_le_rpow (by norm_num) hθ
  have hbig : 0 ≤ 3 * C' * 2 ^ θ + 1 + 4 * backgroundConstant := by
    have : 0 ≤ 3 * C' * 2 ^ θ := by positivity
    linarith
  refine ⟨3 * C' * 2 ^ θ + 1 + 4 * backgroundConstant + (1 + backgroundConstant), fun x hx => ?_⟩
  have hxθ : 1 ≤ x ^ θ := Real.one_le_rpow hx.le hθ
  have hx0 : 0 < x := lt_trans one_pos hx
  rcases le_or_gt x 2 with hx2 | hx2
  · -- `1 < x ≤ 2` : la somme lissée est nulle (aucun poids avant 2)
    have hA : smoothedVonMangoldtSum x = 0 := by
      rw [smoothedVonMangoldtSum_cell (N := 1) (by exact_mod_cast hx) (by exact_mod_cast hx2)]
      simp [massA, massB, Finset.sum_range_succ]
    have hBx := norm_background_sub_half_le hx
    have hx2' : ‖(x : ℂ) / 2‖ ≤ 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; norm_num; linarith
    have hR : ‖smoothedRemainder x‖ ≤ 1 + backgroundConstant := by
      unfold smoothedRemainder
      rw [hA, zero_sub, norm_neg]
      have heq : smoothedZeroBackground x =
          (smoothedZeroBackground x - (x : ℂ) / 2) + (x : ℂ) / 2 := by
        ring
      rw [heq]
      calc _ ≤ ‖smoothedZeroBackground x - (x : ℂ) / 2‖ + ‖(x : ℂ) / 2‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    calc ‖smoothedRemainder x‖ ≤ 1 + backgroundConstant := hR
      _ ≤ (1 + backgroundConstant) * x ^ θ := le_mul_of_one_le_right (by linarith) hxθ
      _ ≤ _ := by nlinarith
  · -- `x > 2` : cellule `]N, N+1]` avec `N = ⌈x⌉₊ − 1 ≥ 2`
    obtain ⟨N, hN2, hxN, hxN1⟩ : ∃ N : ℕ, 2 ≤ N ∧ (N : ℝ) < x ∧ x ≤ N + 1 := by
      have h3 : 2 < ⌈x⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hx2)
      refine ⟨⌈x⌉₊ - 1, by omega, ?_, ?_⟩
      · have := Nat.ceil_lt_add_one hx0.le
        rw [Nat.cast_sub (by omega), Nat.cast_one]; linarith
      · have := Nat.le_ceil x
        rw [Nat.cast_sub (by omega), Nat.cast_one]; linarith
    have hcell := norm_smoothedRemainder_cell_le hN2 hxN hxN1
    have hRN := norm_smoothedRemainder_nat_le hθ hC h hN2
    have hRN1 := norm_smoothedRemainder_nat_le hθ hC h (M := N + 1) (by omega)
    -- `N + 1 ≤ 2x`, donc `(N+1)^θ ≤ 2^θ · x^θ`
    have hN1x : ((N + 1 : ℕ) : ℝ) ≤ 2 * x := by push_cast; linarith
    have hNx : (N : ℝ) ≤ 2 * x := by linarith
    have hpow1 : ((N + 1 : ℕ) : ℝ) ^ θ ≤ 2 ^ θ * x ^ θ := by
      rw [← Real.mul_rpow (by norm_num) hx0.le]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) hN1x hθ
    have hpow2 : (N : ℝ) ^ θ ≤ 2 ^ θ * x ^ θ := by
      rw [← Real.mul_rpow (by norm_num) hx0.le]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) hNx hθ
    have hpos : 0 < (2 : ℝ) ^ θ * x ^ θ := by positivity
    calc ‖smoothedRemainder x‖
        ≤ ‖smoothedRemainder ((N + 1 : ℕ) : ℝ)‖ + 2 * ‖smoothedRemainder (N : ℝ)‖ + 1 +
          4 * backgroundConstant := hcell
      _ ≤ C' * (2 ^ θ * x ^ θ) + 2 * (C' * (2 ^ θ * x ^ θ)) + 1 + 4 * backgroundConstant := by
          have e1 := hRN1.trans (mul_le_mul_of_nonneg_left hpow1 hC'0)
          have e2 := hRN.trans (mul_le_mul_of_nonneg_left hpow2 hC'0)
          rw [hC'def]
          linarith
      _ = 3 * C' * 2 ^ θ * x ^ θ + 1 + 4 * backgroundConstant := by ring
      _ ≤ (3 * C' * 2 ^ θ + 1 + 4 * backgroundConstant + (1 + backgroundConstant)) * x ^ θ := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 + 5 * backgroundConstant)
            (sub_nonneg.mpr hxθ)]

/-- **Toute position radiale est bornée par l'exposant du reste brut aux entiers.** -/
theorem zero_re_le_of_psiRemainder {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (h : ∀ k : ℕ, 1 ≤ k → |psiRemainder k| ≤ C * (k : ℝ) ^ θ) (ρ : ExplicitIndex) :
    (ρ : ℂ).re ≤ θ := by
  obtain ⟨C', hC'⟩ := mem_remainderExponents_of_psiRemainder hθ hC h
  exact smoothedRemainder_growth_bounds_zero hC' ρ

/-! ## 5. Les rencontres suffisent -/

/-- Rencontre brute : entier de poids de von Mangoldt non nul (premier ou puissance de premier). -/
def IsRawEvent (E : ℕ) : Prop := vonMangoldt E ≠ 0

theorem isRawEvent_of_prime {p : ℕ} (hp : p.Prime) : IsRawEvent p := by
  unfold IsRawEvent
  rw [vonMangoldt_apply_prime hp]
  exact (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'

/-- **Les rencontres suffisent** : une borne du reste brut aux deux côtés de chaque rencontre brute
se propage à
tout entier, au prix du facteur `2^θ` (Bertrand : une rencontre entre `k` et `2k`) plus un (l'entier
`1`). -/
theorem psiRemainder_bound_of_events {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (h : ∀ E : ℕ, IsRawEvent E →
      |psiRemainder E| ≤ C * (E : ℝ) ^ θ ∧ |psiRemainder (E - 1)| ≤ C * (E : ℝ) ^ θ) :
    ∀ k : ℕ, 1 ≤ k → |psiRemainder k| ≤ (C * 2 ^ θ + 1) * (k : ℝ) ^ θ := by
  classical
  intro k hk
  have hkθ : 1 ≤ (k : ℝ) ^ θ := Real.one_le_rpow (by exact_mod_cast hk) hθ
  have hC2 : 0 ≤ C * 2 ^ θ := mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  rcases eq_or_lt_of_le hk with rfl | hk2
  · have h1 : psiRemainder 1 = -1 := by simp [psiRemainder, massA, Finset.sum_range_succ]
    rw [h1, abs_neg, abs_one]
    nlinarith
  · -- `E₀` : la plus grande rencontre `≤ k` ; `E₁` : la première rencontre `> k`, au plus `2k`
    have h2 : IsRawEvent 2 := isRawEvent_of_prime Nat.prime_two
    have hE₀ev : IsRawEvent (Nat.findGreatest IsRawEvent k) :=
      Nat.findGreatest_spec (P := IsRawEvent) (by omega : 2 ≤ k) h2
    have hE₀k : Nat.findGreatest IsRawEvent k ≤ k := Nat.findGreatest_le k
    obtain ⟨p, hp, hkp, hp2k⟩ := Nat.exists_prime_lt_and_le_two_mul k (by omega)
    have hex : ∃ E, k < E ∧ IsRawEvent E := ⟨p, hkp, isRawEvent_of_prime hp⟩
    have hE₁spec : k < Nat.find hex ∧ IsRawEvent (Nat.find hex) := Nat.find_spec hex
    have hE₁le : Nat.find hex ≤ p := Nat.find_min' hex ⟨hkp, isRawEvent_of_prime hp⟩
    have hno : NoEventBetween (Nat.findGreatest IsRawEvent k) (Nat.find hex - 1) := by
      intro j hj hj'
      by_contra hjev
      rcases le_or_gt j k with hjk | hjk
      · exact Nat.findGreatest_is_greatest hj hjk hjev
      · exact Nat.find_min hex (by omega : j < Nat.find hex) ⟨hjk, hjev⟩
    have hbr := abs_psiRemainder_le_of_noEvent hE₀k (by omega : k ≤ Nat.find hex - 1) hno
    have hb0 := (h _ hE₀ev).1
    have hb1 := (h _ hE₁spec.2).2
    have h2k : ((2 * k : ℕ) : ℝ) ^ θ = 2 ^ θ * (k : ℝ) ^ θ := by
      push_cast; exact Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    have hE₀r : C * ((Nat.findGreatest IsRawEvent k : ℕ) : ℝ) ^ θ ≤ C * (2 ^ θ * (k : ℝ) ^ θ) := by
      rw [← h2k]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (by omega : _ ≤ 2 * k)) hθ) hC
    have hE₁r : C * ((Nat.find hex : ℕ) : ℝ) ^ θ ≤ C * (2 ^ θ * (k : ℝ) ^ θ) := by
      rw [← h2k]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (by omega : _ ≤ 2 * k)) hθ) hC
    have hmax : |psiRemainder k| ≤ C * 2 ^ θ * (k : ℝ) ^ θ := by
      calc |psiRemainder k| ≤ max |psiRemainder (Nat.findGreatest IsRawEvent k)|
            |psiRemainder (Nat.find hex - 1)| := hbr
        _ ≤ C * 2 ^ θ * (k : ℝ) ^ θ :=
            max_le (hb0.trans (by linarith)) (hb1.trans (by linarith))
    nlinarith

/-- **La contradiction finale, localisée aux rencontres** : une borne du reste brut aux deux côtés
de chaque
rencontre brute, d'exposant `θ`, borne toute position radiale par `θ`. -/
theorem zero_re_le_of_psiRemainder_at_events {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (h : ∀ E : ℕ, IsRawEvent E →
      |psiRemainder E| ≤ C * (E : ℝ) ^ θ ∧ |psiRemainder (E - 1)| ≤ C * (E : ℝ) ^ θ)
    (ρ : ExplicitIndex) : (ρ : ℂ).re ≤ θ :=
  zero_re_le_of_psiRemainder hθ (by positivity) (psiRemainder_bound_of_events hθ hC h) ρ

/-- **RH depuis les rencontres brutes** : si, pour tout `ε > 0`, le reste brut aux deux côtés de
chaque rencontre
est borné par `C·E^{1/2+ε}`, alors RH. -/
theorem riemannHypothesis_of_psiRemainder_at_events
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℕ, IsRawEvent E →
      |psiRemainder E| ≤ C * (E : ℝ) ^ (1 / 2 + ε) ∧
        |psiRemainder (E - 1)| ≤ C * (E : ℝ) ^ (1 / 2 + ε)) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_remainder_growth_all_eps.mpr fun ε hε => ?_
  obtain ⟨C, hC, hE⟩ := h ε hε
  exact mem_remainderExponents_of_psiRemainder (by linarith) (by positivity)
    (psiRemainder_bound_of_events (by linarith) hC hE)

/-- **Lecture OFF** : un membre de position radiale `β` force, pour tout exposant `θ < β` et toute
constante,
une rencontre brute où le reste brut dépasse `C·E^θ` d'un côté ou de l'autre de la rencontre. -/
theorem off_member_forces_raw_excess_at_event {θ : ℝ} (hθ : 0 ≤ θ) (ρ : ExplicitIndex)
    (hρ : θ < (ρ : ℂ).re) (C : ℝ) :
    ∃ E : ℕ, IsRawEvent E ∧
      (C * (E : ℝ) ^ θ < |psiRemainder E| ∨ C * (E : ℝ) ^ θ < |psiRemainder (E - 1)|) := by
  by_contra hcon
  push Not at hcon
  have h2 := (hcon 2 (isRawEvent_of_prime Nat.prime_two)).1
  have h2θ : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ θ := Real.rpow_pos_of_pos (by norm_num) _
  have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_right h2θ).mp ((abs_nonneg _).trans h2)
  exact absurd (zero_re_le_of_psiRemainder_at_events hθ hC hcon ρ) (not_le.mpr hρ)

#print axioms RHV6Fresh.abs_psiRemainder_le_of_noEvent
#print axioms RHV6Fresh.natMul_smoothedVonMangoldtSum_eq
#print axioms RHV6Fresh.psiRemainder_bound_of_events
#print axioms RHV6Fresh.zero_re_le_of_psiRemainder_at_events
#print axioms RHV6Fresh.riemannHypothesis_of_psiRemainder_at_events
#print axioms RHV6Fresh.off_member_forces_raw_excess_at_event

end RHV6Fresh
