/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PrimeTransitionDecomposition
import RHV6Fresh.Terminal.WindowProgression
import RHV6Fresh.Terminal.GrammarWordLoad

/-!
# Erreur signée par cellules entre premiers consécutifs, fenêtres de 12, 24, 36 transitions (auteur, 2026-10-11)

Objet du but (`DemonstrationChain.lean`) : `S(N) = Σ_{3<p<N premier} Λ(p)(N − p)` (premiers seuls, `primeTail`) et son
erreur signée `E(N) = S(N) − N²/2` (`goalError`). Conventions d'extrémité : `p < N` STRICT dans `S(N)` ;
`ϑ₃(M) = Σ_{3<p≤M premier} log p` (`cellTheta`, extrémité `M` INCLUSE) ; cellule `[p_k, p_{k+1}]`, `p_k = fnPrimeAtRank k`.

* §1 pas exact : `E(N+1) − E(N) = ϑ₃(N) − N − 1/2` ; `E(N) = Σ_{M<N} (ϑ₃(M) − M − 1/2)` ; `E(n) − E(m)` = somme sur `[m, n[` ;
* §2 cellule : `ϑ₃` constant sur `[p_k, p_{k+1}[` ; pour `p_k ≤ N ≤ p_{k+1}`,
  `E(N) − E(p_k) = (N − p_k)·ϑ₃(p_k) − (N² − p_k²)/2` (terme de bord partiel) ; cellule entière :
  `E(p_{k+1}) − E(p_k) = g_k·ϑ₃(p_k) − (p_{k+1}² − p_k²)/2` ;
* §3 fenêtres : composition exacte sur `m` transitions, instances 12, 24, 36 ; planchers compilés appliqués (longueur
  `≥ 3m` dès `p_k > 3`) et balance `|#AB − #BA| ≤ 1` sur la même fenêtre ; ni l'un ni l'autre ne porte sur le signe ;
* §4 accumulation : fenêtres successives télescopées, décomposition complète de `E(N)` = bord initial `E(5) = −25/2` +
  cellules + cellule partielle ; part des puissances et bord `{2, 3}` séparés (`primeMass_goal_split`) ;
* §5 composition vers le but : un contrôle SIGNÉ de `ϑ₃(M) − M` d'exposant `θ` donne les deux côtés du but d'exposant
  `1 + θ` (constante `C + 1/2`), chaque côté du but n'utilisant que le côté correspondant du contrôle.

Tout est démontré (axiomes standard). Le contrôle de `ϑ₃(M) − M` d'exposant `θ < 1` n'est PAS démontré.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction

/-! ## 0. Objets -/

/-- `S(N) = Σ_{3<p<N premier} Λ(p)(N − p)` (objet du but, extrémité `N` exclue). -/
noncomputable def primeTail (N : ℕ) : ℝ :=
  ∑ n ∈ ((Finset.range N).filter Nat.Prime).filter (fun q => 3 < q), Λ n * ((N : ℝ) - n)

/-- Erreur signée du but : `E(N) = S(N) − N²/2`. -/
noncomputable def goalError (N : ℕ) : ℝ := primeTail N - (N : ℝ) ^ 2 / 2

/-- `ϑ₃(M) = Σ_{3<p≤M premier} log p` (extrémité `M` incluse). -/
noncomputable def cellTheta (M : ℕ) : ℝ :=
  ∑ n ∈ ((Finset.range (M + 1)).filter Nat.Prime).filter (fun q => 3 < q), Λ n

/-- Poids d'un entier dans `S` : `Λ(n)` si `n` premier `> 3`, `0` sinon. -/
noncomputable def tailWeight (n : ℕ) : ℝ := if n.Prime ∧ 3 < n then Λ n else 0

/-- Accroissement exact d'une cellule `[p_j, p_{j+1}]`. -/
noncomputable def cellIncrement (j : ℕ) : ℝ :=
  ((fnPrimeAtRank (j + 1) : ℝ) - fnPrimeAtRank j) * cellTheta (fnPrimeAtRank j) -
    (((fnPrimeAtRank (j + 1) : ℝ)) ^ 2 - (fnPrimeAtRank j : ℝ) ^ 2) / 2

theorem primeTail_eq_sum (N : ℕ) : primeTail N = ∑ n ∈ Finset.range N, tailWeight n * ((N : ℝ) - n) := by
  unfold primeTail tailWeight
  rw [Finset.filter_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

theorem cellTheta_eq_sum (M : ℕ) : cellTheta M = ∑ n ∈ Finset.range (M + 1), tailWeight n := by
  unfold cellTheta tailWeight
  rw [Finset.filter_filter, Finset.sum_filter]

theorem cellTheta_succ (M : ℕ) : cellTheta (M + 1) = cellTheta M + tailWeight (M + 1) := by
  rw [cellTheta_eq_sum, cellTheta_eq_sum, Finset.sum_range_succ]

theorem cellTheta_zero : cellTheta 0 = 0 := by
  rw [cellTheta_eq_sum]; simp [tailWeight]

/-! ## 1. Pas exact et somme -/

theorem primeTail_succ (N : ℕ) : primeTail (N + 1) = primeTail N + cellTheta N := by
  rw [primeTail_eq_sum, primeTail_eq_sum, cellTheta_eq_sum, Finset.sum_range_succ, Finset.sum_range_succ]
  push_cast
  have h : ∑ n ∈ Finset.range N, tailWeight n * ((N : ℝ) + 1 - n) =
      ∑ n ∈ Finset.range N, tailWeight n * ((N : ℝ) - n) + ∑ n ∈ Finset.range N, tailWeight n := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun n _ => by ring
  rw [h]; ring

/-- **Pas exact** : `E(N+1) − E(N) = ϑ₃(N) − N − 1/2`. -/
theorem goalError_succ (N : ℕ) : goalError (N + 1) - goalError N = cellTheta N - N - 1 / 2 := by
  unfold goalError; rw [primeTail_succ]; push_cast; ring

theorem goalError_zero : goalError 0 = 0 := by simp [goalError, primeTail]

/-- **Erreur cumulée** : `E(N) = Σ_{M<N} (ϑ₃(M) − M − 1/2)`. -/
theorem goalError_eq_sum (N : ℕ) :
    goalError N = ∑ M ∈ Finset.range N, (cellTheta M - M - 1 / 2) := by
  induction N with
  | zero => simp [goalError_zero]
  | succ N ih => rw [Finset.sum_range_succ, ← ih]; linarith [goalError_succ N]

/-- **Accroissement entre deux extrémités quelconques** : `E(n) − E(m) = Σ_{m≤M<n} (ϑ₃(M) − M − 1/2)`. -/
theorem goalError_sub_eq_sum {m n : ℕ} (h : m ≤ n) :
    goalError n - goalError m = ∑ M ∈ Finset.Ico m n, (cellTheta M - M - 1 / 2) := by
  rw [Finset.sum_Ico_eq_sub _ h, goalError_eq_sum, goalError_eq_sum]

/-! ## 2. La cellule entre deux premiers consécutifs -/

/-- Aucun premier strictement entre `p_k` et `p_{k+1}`. -/
theorem not_prime_between {k q : ℕ} (h1 : fnPrimeAtRank k < q) (h2 : q < fnPrimeAtRank (k + 1)) : ¬ q.Prime := by
  intro hq
  have he : fnPrimeAtRank (Nat.count Nat.Prime q) = q := Nat.nth_count hq
  rw [← he] at h1 h2
  have a := thm_primeAtRank_strictMono.lt_iff_lt.mp h1
  have b := thm_primeAtRank_strictMono.lt_iff_lt.mp h2
  omega

/-- **`ϑ₃` est constant sur la cellule** `[p_k, p_{k+1}[`. -/
theorem cellTheta_on_cell (k : ℕ) : ∀ M, fnPrimeAtRank k ≤ M → M < fnPrimeAtRank (k + 1) →
    cellTheta M = cellTheta (fnPrimeAtRank k) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => intro _; rfl
  | succ M hM ih =>
    intro h2
    rw [cellTheta_succ, ih (by omega)]
    have : ¬ (M + 1).Prime := not_prime_between (by omega) h2
    simp [tailWeight, this]

theorem sum_Ico_mid {a : ℕ} : ∀ N, a ≤ N →
    ∑ M ∈ Finset.Ico a N, ((M : ℝ) + 1 / 2) = ((N : ℝ) ^ 2 - (a : ℝ) ^ 2) / 2 := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih => rw [Finset.sum_Ico_succ_top hN, ih]; push_cast; ring

/-- **Identité exacte dans une cellule, bord partiel conservé** : pour `p_k ≤ N ≤ p_{k+1}`,
`E(N) − E(p_k) = (N − p_k)·ϑ₃(p_k) − (N² − p_k²)/2`. -/
theorem goalError_in_cell (k N : ℕ) (h1 : fnPrimeAtRank k ≤ N) (h2 : N ≤ fnPrimeAtRank (k + 1)) :
    goalError N - goalError (fnPrimeAtRank k) =
      ((N : ℝ) - fnPrimeAtRank k) * cellTheta (fnPrimeAtRank k) - ((N : ℝ) ^ 2 - (fnPrimeAtRank k : ℝ) ^ 2) / 2 := by
  rw [goalError_sub_eq_sum h1]
  have hc : ∀ M ∈ Finset.Ico (fnPrimeAtRank k) N, cellTheta M - M - 1 / 2 =
      cellTheta (fnPrimeAtRank k) - ((M : ℝ) + 1 / 2) := by
    intro M hM
    rw [Finset.mem_Ico] at hM
    rw [cellTheta_on_cell k M hM.1 (by omega)]; ring
  rw [Finset.sum_congr rfl hc, Finset.sum_sub_distrib, sum_Ico_mid N h1, Finset.sum_const, Nat.card_Ico,
    nsmul_eq_mul, Nat.cast_sub h1]

/-- **Identité exacte d'une cellule entière** : `E(p_{k+1}) − E(p_k) = g_k·ϑ₃(p_k) − (p_{k+1}² − p_k²)/2`. -/
theorem goalError_cell (k : ℕ) :
    goalError (fnPrimeAtRank (k + 1)) - goalError (fnPrimeAtRank k) = cellIncrement k :=
  goalError_in_cell k _ (thm_primeAtRank_strictMono (Nat.lt_succ_self k)).le le_rfl

/-! ## 3. Fenêtres de transitions -/

/-- **Composition exacte sur `m` transitions** : `E(p_{k+m}) − E(p_k) = Σ_{j<m} cellIncrement(k + j)`. -/
theorem goalError_window (k m : ℕ) :
    goalError (fnPrimeAtRank (k + m)) - goalError (fnPrimeAtRank k) =
      ∑ j ∈ Finset.range m, cellIncrement (k + j) := by
  have h := Finset.sum_range_sub (fun j => goalError (fnPrimeAtRank (k + j))) m
  simp only [Nat.add_zero] at h
  rw [← h]
  exact (Finset.sum_congr rfl fun j _ => by rw [← goalError_cell, Nat.add_assoc]).symm

/-- **Fenêtre de `m` transitions, entiers explicites, planchers et balance compilés appliqués** : l'accroissement est la
somme des pas `ϑ₃(M) − M − 1/2` sur `[p_k, p_{k+m}[` ; pour `m` pair et `p_k > 3`, la fenêtre contient au moins `3m`
entiers (`primeAtRank_window_ge_three_mul`) ; sur la même fenêtre `|#AB − #BA| ≤ 1` (`prime_ab_ba_channel_lock`).
Aucune des deux propriétés grammaticales ne porte sur le signe des pas. -/
theorem goalError_window_profile (k m : ℕ) (hm : Even m) (h3 : 3 < fnPrimeAtRank k) :
    goalError (fnPrimeAtRank (k + m)) - goalError (fnPrimeAtRank k) =
        ∑ M ∈ Finset.Ico (fnPrimeAtRank k) (fnPrimeAtRank (k + m)), (cellTheta M - M - 1 / 2) ∧
      3 * m ≤ (Finset.Ico (fnPrimeAtRank k) (fnPrimeAtRank (k + m))).card ∧
      |∑ i ∈ Finset.range m, abMinusBa (state6 (fnPrimeAtRank (k + i)))
          (state6 (fnPrimeAtRank (k + (i + 1))))| ≤ 1 := by
  have hfl := primeAtRank_window_ge_three_mul k m hm h3
  refine ⟨goalError_sub_eq_sum (by omega), ?_, prime_ab_ba_channel_lock k m⟩
  rw [Nat.card_Ico]; omega

/-- **Fenêtres de 12, 24, 36 transitions** (composition exacte, planchers `36`, `72`, `108`). -/
theorem goalError_windows_12_24_36 (k : ℕ) (h3 : 3 < fnPrimeAtRank k) :
    (goalError (fnPrimeAtRank (k + 12)) - goalError (fnPrimeAtRank k) =
        ∑ j ∈ Finset.range 12, cellIncrement (k + j) ∧ fnPrimeAtRank k + 36 ≤ fnPrimeAtRank (k + 12)) ∧
    (goalError (fnPrimeAtRank (k + 24)) - goalError (fnPrimeAtRank k) =
        ∑ j ∈ Finset.range 24, cellIncrement (k + j) ∧ fnPrimeAtRank k + 72 ≤ fnPrimeAtRank (k + 24)) ∧
    (goalError (fnPrimeAtRank (k + 36)) - goalError (fnPrimeAtRank k) =
        ∑ j ∈ Finset.range 36, cellIncrement (k + j) ∧ fnPrimeAtRank k + 108 ≤ fnPrimeAtRank (k + 36)) :=
  ⟨⟨goalError_window k 12, primeAtRank_window_ge_three_mul k 12 ⟨6, rfl⟩ h3⟩,
    ⟨goalError_window k 24, primeAtRank_window_ge_three_mul k 24 ⟨12, rfl⟩ h3⟩,
    ⟨goalError_window k 36, primeAtRank_window_ge_three_mul k 36 ⟨18, rfl⟩ h3⟩⟩

/-! ## 4. Accumulation entre fenêtres et bords -/

/-- **Accumulation** : `W` fenêtres successives de `m` transitions se télescopent ; l'erreur au bout est la SOMME des
accroissements de fenêtre (aucune compensation entre fenêtres n'est imposée). -/
theorem goalError_windows_accumulate (k m W : ℕ) :
    goalError (fnPrimeAtRank (k + W * m)) - goalError (fnPrimeAtRank k) =
      ∑ w ∈ Finset.range W,
        (goalError (fnPrimeAtRank (k + (w + 1) * m)) - goalError (fnPrimeAtRank (k + w * m))) := by
  rw [Finset.sum_range_sub (fun w => goalError (fnPrimeAtRank (k + w * m)))]
  simp

/-- Bord initial : `S(N) = 0` pour `N ≤ 5`, donc `E(N) = −N²/2` (`E(5) = −25/2`). -/
theorem goalError_initial {N : ℕ} (hN : N ≤ 5) : goalError N = -((N : ℝ) ^ 2 / 2) := by
  have h0 : primeTail N = 0 := by
    unfold primeTail
    refine Finset.sum_eq_zero fun n hn => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    have h4 : n = 4 := by omega
    exact absurd hn.1.2 (by rw [h4]; decide)
  unfold goalError; rw [h0]; ring

/-- **Décomposition complète de l'erreur** pour `p_j ≤ N ≤ p_{j+1}`, `j ≥ 2` : bord initial `E(5) = −25/2`, cellules
entières de `p_2 = 5` à `p_j`, cellule partielle de bord. -/
theorem goalError_cumulative (j N : ℕ) (hj : 2 ≤ j) (h1 : fnPrimeAtRank j ≤ N) (h2 : N ≤ fnPrimeAtRank (j + 1)) :
    goalError N = -(25 / 2) + ∑ i ∈ Finset.range (j - 2), cellIncrement (2 + i) +
      (((N : ℝ) - fnPrimeAtRank j) * cellTheta (fnPrimeAtRank j) -
        ((N : ℝ) ^ 2 - (fnPrimeAtRank j : ℝ) ^ 2) / 2) := by
  have hc := goalError_in_cell j N h1 h2
  have hw := goalError_window 2 (j - 2)
  rw [show 2 + (j - 2) = j by omega] at hw
  have h5 : fnPrimeAtRank 2 = 5 := Nat.nth_prime_two_eq_five
  rw [h5, goalError_initial le_rfl] at hw
  norm_num at hw
  linarith

/-- **Premiers, bord `{2, 3}` et puissances séparés** : `primeMass N − N²/2 = E(N) + boundaryPart N + powerPart N`. -/
theorem primeMass_goal_split (N : ℕ) :
    primeMass N - (N : ℝ) ^ 2 / 2 = goalError N + boundaryPart N + powerPart N := by
  have h := primePart_four_transitions N
  rw [sum_transitionSum_eq] at h
  rw [primeMass_split, h]; unfold goalError primeTail; ring

/-! ## 5. Composition vers le but : contrôle signé des cellules -/

/-- **Accumulation des contrôles de cellule, signes séparés** : si `ϑ₃(M) − M ≤ C·M^θ` (resp. `M − ϑ₃(M) ≤ C·M^θ`) pour
tout `M ≥ 1`, alors le côté supérieur (resp. inférieur) du but tient avec la constante `C + 1/2` et l'exposant `1 + θ`. -/
theorem goal_sides_of_cell_control {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hup : ∀ M : ℕ, 1 ≤ M → cellTheta M - M ≤ C * (M : ℝ) ^ θ)
    (hlo : ∀ M : ℕ, 1 ≤ M → (M : ℝ) - cellTheta M ≤ C * (M : ℝ) ^ θ) :
    ∀ N : ℕ, 2 ≤ N →
      primeTail N - (N : ℝ) ^ 2 / 2 ≤ (C + 1 / 2) * (N : ℝ) ^ (1 + θ) ∧
      (N : ℝ) ^ 2 / 2 - primeTail N ≤ (C + 1 / 2) * (N : ℝ) ^ (1 + θ) := by
  intro N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hpow : (N : ℝ) ^ (1 + θ) = N * (N : ℝ) ^ θ := by rw [Real.rpow_add hN0, Real.rpow_one]
  have hNθ1 : 1 ≤ (N : ℝ) ^ θ := Real.one_le_rpow hN1 hθ
  have hmono : ∀ M ∈ Finset.range N, 1 ≤ M → C * (M : ℝ) ^ θ ≤ C * (N : ℝ) ^ θ := by
    intro M hM hM1
    rw [Finset.mem_range] at hM
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hM.le) hθ) hC
  have hE := goalError_eq_sum N
  have hCN : 0 ≤ C * (N : ℝ) ^ θ := mul_nonneg hC (by linarith)
  have hsum_up : ∑ M ∈ Finset.range N, (cellTheta M - M - 1 / 2) ≤
      ∑ M ∈ Finset.range N, C * (N : ℝ) ^ θ := by
    refine Finset.sum_le_sum fun M hM => ?_
    rcases Nat.eq_zero_or_pos M with rfl | hM1
    · simp [cellTheta_zero]; linarith
    · linarith [hup M hM1, hmono M hM hM1]
  have hsum_lo : ∑ M ∈ Finset.range N, -(cellTheta M - M - 1 / 2) ≤
      ∑ M ∈ Finset.range N, (C * (N : ℝ) ^ θ + 1 / 2) := by
    refine Finset.sum_le_sum fun M hM => ?_
    rcases Nat.eq_zero_or_pos M with rfl | hM1
    · simp [cellTheta_zero]; linarith
    · linarith [hlo M hM1, hmono M hM hM1]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_up hsum_lo
  rw [Finset.sum_neg_distrib] at hsum_lo
  unfold goalError at hE
  constructor
  · rw [hpow]; nlinarith
  · rw [hpow]; nlinarith

#print axioms primeTail_succ
#print axioms goalError_succ
#print axioms goalError_eq_sum
#print axioms goalError_sub_eq_sum
#print axioms not_prime_between
#print axioms cellTheta_on_cell
#print axioms goalError_in_cell
#print axioms goalError_cell
#print axioms goalError_window
#print axioms goalError_window_profile
#print axioms goalError_windows_12_24_36
#print axioms goalError_windows_accumulate
#print axioms goalError_initial
#print axioms goalError_cumulative
#print axioms primeMass_goal_split
#print axioms goal_sides_of_cell_control

end RHV6Fresh
