/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GrammarKinematics

/-!
# Fenêtres de `m` transitions : progression première minimale, phase, hauteur (E175, 2026-10-05)

Une fenêtre de `m` transitions = `m + 1` membres = `m + 1` occurrences `p_n, …, p_{n+m}` (`fnPrimeAtRank`, indexée à partir de
`0` : `p_0 = 2`, `p_1 = 3`, `p_2 = 5` ; `occurrence z = p_{nZeroSourceIndex z}`, `expectedMinimumPrime z = p_{nZeroSourceIndex z + 1}`).

1. **Progression première minimale** (premiers consécutifs `> 3`, aucune alternance stricte `2, 4` supposée) : `g_j + g_{j+1} ≥ 6`,
   `p_{n+m} − p_n ≥ 3m` pour `m` pair, `≥ 3m − 1` pour `m` impair, `log(p_{n+m}/p_n) ≥ log(1 + 3m/p_n)` ; classes d'écart modulo 6
   = transitions de résidus (`2` : `5 → 1`, `4` : `1 → 5`, `0` : même résidu).
2. **Phase** : la progression `T_j · log(p_{j+1}/p_j)` est strictement positive même quand la hauteur ne bouge pas ; c'est une
   progression de PHASE, pas de hauteur. Sur une chaîne, la somme des progressions de phase est au moins
   `c · log(1 + 3m/p_0)` pour toute hauteur minimale `c` de la fenêtre.
3. **Hauteur** : l'écart de hauteur d'une fenêtre est la somme des seuls pas non nuls ; l'identité d'Abel est vraie pour TOUTE
   suite de hauteurs, la suite constante comprise : la progression première n'exige aucune progression de hauteur.

Portée : bornes premières et identités ; aucun énoncé ne borne le nombre de passages de même hauteur d'une fenêtre. Aucun
`sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean Finset

/-! ## 1. Progression première minimale -/

/-- Deux nombres à bon état modulo 6 distincts diffèrent d'au moins `2`. -/
theorem goodMod6_step_ge_two {p q : ℕ} (hp : GoodMod6 p) (hq : GoodMod6 q) (hpq : p < q) :
    p + 2 ≤ q := by
  unfold GoodMod6 at hp hq
  omega

/-- **Deux écarts consécutifs entre premiers `> 3` font au moins `6`** : `g_n + g_{n+1} ≥ 6`, sans
alternance stricte supposée (un écart `≥ 6` est permis). -/
theorem primeAtRank_gap_pair_ge_six (n : ℕ) (h3 : 3 < fnPrimeAtRank n) :
    6 ≤ (fnPrimeAtRank (n + 1) - fnPrimeAtRank n) + (fnPrimeAtRank (n + 2) - fnPrimeAtRank (n + 1)) := by
  have h1 : fnPrimeAtRank n < fnPrimeAtRank (n + 1) := thm_primeAtRank_strictMono (by omega)
  have h2 : fnPrimeAtRank (n + 1) < fnPrimeAtRank (n + 2) := thm_primeAtRank_strictMono (by omega)
  have := primeAtRank_two_step_ge_six n h3
  omega

/-- **`2k` transitions avancent d'au moins `6k`** dès que `p_n > 3`. -/
theorem primeAtRank_even_window_ge (n k : ℕ) (h3 : 3 < fnPrimeAtRank n) :
    fnPrimeAtRank n + 6 * k ≤ fnPrimeAtRank (n + 2 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmono : fnPrimeAtRank n ≤ fnPrimeAtRank (n + 2 * k) :=
      thm_primeAtRank_strictMono.monotone (by omega)
    have h := primeAtRank_two_step_ge_six (n + 2 * k) (by omega)
    rw [show n + 2 * (k + 1) = n + 2 * k + 2 by ring]
    omega

/-- **`m` pair : `p_{n+m} − p_n ≥ 3m`.** -/
theorem primeAtRank_window_ge_three_mul (n m : ℕ) (hm : Even m) (h3 : 3 < fnPrimeAtRank n) :
    fnPrimeAtRank n + 3 * m ≤ fnPrimeAtRank (n + m) := by
  obtain ⟨k, rfl⟩ := hm
  have h := primeAtRank_even_window_ge n k h3
  rw [show n + (k + k) = n + 2 * k by ring]
  omega

/-- **`m` impair : `p_{n+m} − p_n ≥ 3m − 1`.** -/
theorem primeAtRank_window_odd_ge (n k : ℕ) (h3 : 3 < fnPrimeAtRank n) :
    fnPrimeAtRank n + 3 * (2 * k + 1) ≤ fnPrimeAtRank (n + (2 * k + 1)) + 1 := by
  have h := primeAtRank_even_window_ge n k h3
  have hlt : fnPrimeAtRank (n + 2 * k) < fnPrimeAtRank (n + 2 * k + 1) :=
    thm_primeAtRank_strictMono (by omega)
  have hstep := goodMod6_step_ge_two
    (prime_goodMod6 _ (thm_primeAtRank_isPrime (n + 2 * k)) (by omega))
    (prime_goodMod6 _ (thm_primeAtRank_isPrime (n + 2 * k + 1)) (by omega)) hlt
  rw [show n + (2 * k + 1) = n + 2 * k + 1 by ring]
  omega

/-- **Classe d'écart modulo 6 = transition de résidus** entre deux nombres à bon état : `2` ⟺ `5 → 1`,
`4` ⟺ `1 → 5`, `0` ⟺ même résidu. -/
theorem gapClass6_residue_transition {p q : ℕ} (hp : GoodMod6 p) (hq : GoodMod6 q) (hpq : p ≤ q) :
    (gapClass6 p q = 2 ↔ p % 6 = 5 ∧ q % 6 = 1) ∧
      (gapClass6 p q = 4 ↔ p % 6 = 1 ∧ q % 6 = 5) ∧
      (gapClass6 p q = 0 ↔ p % 6 = q % 6) := by
  unfold gapClass6
  unfold GoodMod6 at hp hq
  refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro h <;> omega

/-- **La progression logarithmique d'une fenêtre télescope** :
`Σ_{j<m} log(p_{n+j+1}/p_{n+j}) = log p_{n+m} − log p_n`. -/
theorem primeGapLogRatio_window_sum (n m : ℕ) :
    ∑ j ∈ range m, rPrimeGapLogRatio (n + j) =
      Real.log (fnPrimeAtRank (n + m) : ℝ) - Real.log (fnPrimeAtRank n : ℝ) := by
  have key : ∀ j, rPrimeGapLogRatio (n + j) =
      Real.log (fnPrimeAtRank (n + (j + 1)) : ℝ) - Real.log (fnPrimeAtRank (n + j) : ℝ) := by
    intro j
    unfold rPrimeGapLogRatio fnPrimeSuccessor
    have h0 : (0 : ℝ) < (fnPrimeAtRank (n + j) : ℝ) := by exact_mod_cast thm_primeAtRank_pos _
    have h1 : (0 : ℝ) < (fnPrimeAtRank (n + j + 1) : ℝ) := by exact_mod_cast thm_primeAtRank_pos _
    rw [Real.log_div h1.ne' h0.ne', show n + (j + 1) = n + j + 1 by ring]
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  have := Finset.sum_range_sub (fun j => Real.log (fnPrimeAtRank (n + j) : ℝ)) m
  simpa using this

/-- **Plancher logarithmique d'une fenêtre paire** : `L(n, m) = log(p_{n+m}/p_n) ≥ log(1 + 3m/p_n)`. -/
theorem primeWindow_log_ge (n m : ℕ) (hm : Even m) (h3 : 3 < fnPrimeAtRank n) :
    Real.log (1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ)) ≤
      Real.log ((fnPrimeAtRank (n + m) : ℝ) / (fnPrimeAtRank n : ℝ)) := by
  have h0 : (0 : ℝ) < (fnPrimeAtRank n : ℝ) := by exact_mod_cast thm_primeAtRank_pos n
  have hw : (fnPrimeAtRank n : ℝ) + 3 * (m : ℝ) ≤ (fnPrimeAtRank (n + m) : ℝ) := by
    exact_mod_cast primeAtRank_window_ge_three_mul n m hm h3
  apply Real.log_le_log (by positivity)
  rw [le_div_iff₀ h0]
  field_simp
  linarith

/-- La même borne, écrite sur la somme des progressions logarithmiques de la fenêtre. -/
theorem primeWindow_ratio_sum_ge (n m : ℕ) (hm : Even m) (h3 : 3 < fnPrimeAtRank n) :
    Real.log (1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ)) ≤ ∑ j ∈ range m, rPrimeGapLogRatio (n + j) := by
  rw [primeGapLogRatio_window_sum]
  have h0 : (0 : ℝ) < (fnPrimeAtRank n : ℝ) := by exact_mod_cast thm_primeAtRank_pos n
  have hm' : (0 : ℝ) < (fnPrimeAtRank (n + m) : ℝ) := by exact_mod_cast thm_primeAtRank_pos _
  rw [← Real.log_div hm'.ne' h0.ne']
  exact primeWindow_log_ge n m hm h3

/-! ## 2. Phase : progression positive même à hauteur constante -/

/-- **Toute progression de phase est strictement positive** : `T · log(p_{k+1}/p_k) > 0`. -/
theorem phaseIncrement_pos (z : TrueZero) (k : ℕ) : 0 < phaseIncrement z k := by
  rw [phaseIncrement_eq_height_mul_ratio]
  exact mul_pos z.2 (thm_primeGapLogRatio_pos k)

/-- **Sur un passage de même hauteur**, la hauteur n'avance pas et la phase avance strictement :
la progression `T_e · log(p_{n+1}/p_n)` n'est pas une progression de hauteur. -/
theorem sameHeight_phase_progress (e l : TrueZero) (hH : rZeroHeight e.1 = rZeroHeight l.1) :
    rZeroHeight l.1 - rZeroHeight e.1 = 0 ∧ 0 < phaseIncrement e (nZeroSourceIndex e.1) :=
  ⟨by rw [hH]; ring, phaseIncrement_pos e _⟩

/-- **Plancher de phase d'une chaîne paire** : pour toute hauteur minimale `c ≥ 0` de la fenêtre,
la somme des progressions de phase vaut au moins `c · log(1 + 3m/p_0)`. `c` est un paramètre (aucune
progression de hauteur n'est supposée). -/
theorem chain_phase_window_floor {m : ℕ} (c : ZeroChain m) (hm : Even m) (c0 : ℝ) (hc0 : 0 ≤ c0)
    (hT : ∀ j, j < m → c0 ≤ rZeroHeight (c.member j).1)
    (h3 : 3 < occurrence (c.member 0)) :
    c0 * Real.log (1 + 3 * (m : ℝ) / (occurrence (c.member 0) : ℝ)) ≤
      ∑ j ∈ range m, phaseIncrement (c.member j) (nZeroSourceIndex (c.member j).1) := by
  rw [chain_grammar_sum]
  rw [occurrence_eq_primeAtRank] at h3 ⊢
  set n := nZeroSourceIndex (c.member 0).1
  have hfloor := primeWindow_ratio_sum_ge n m hm h3
  calc c0 * Real.log (1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ))
      ≤ c0 * ∑ j ∈ range m, rPrimeGapLogRatio (n + j) := mul_le_mul_of_nonneg_left hfloor hc0
    _ = ∑ j ∈ range m, c0 * rPrimeGapLogRatio (n + j) := by rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ range m, rZeroHeight (c.member j).1 * rPrimeGapLogRatio (n + j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_right (hT j (Finset.mem_range.mp hj))
          (thm_primeGapLogRatio_pos _).le

/-! ## 3. Hauteur : aucune progression exigée par les premiers -/

/-- **L'écart de hauteur d'une fenêtre est la somme des seuls pas non nuls** : les passages de même
hauteur n'y contribuent pas. -/
theorem window_height_split (T : ℕ → ℝ) (m : ℕ) :
    T m - T 0 = ∑ j ∈ (range m).filter (fun j => T (j + 1) - T j ≠ 0), (T (j + 1) - T j) := by
  rw [Finset.sum_filter_ne_zero]
  exact (Finset.sum_range_sub T m).symm

/-- Passages de même hauteur + passages où la hauteur change = `m`. -/
theorem window_passage_count (T : ℕ → ℝ) (m : ℕ) :
    ((range m).filter (fun j => T (j + 1) - T j = 0)).card +
      ((range m).filter (fun j => ¬ (T (j + 1) - T j = 0))).card = m := by
  rw [Finset.card_filter_add_card_filter_not, Finset.card_range]

/-- **Identité d'Abel d'une fenêtre pour TOUTE suite de hauteurs** : progression de phase plus
déplacement de hauteur pondéré = `T_m log p_{n+m} − T_0 log p_n`. -/
theorem window_abel_any_heights (T : ℕ → ℝ) (n m : ℕ) :
    ∑ j ∈ range m, T j * rPrimeGapLogRatio (n + j) +
      ∑ j ∈ range m, (T (j + 1) - T j) * Real.log (fnPrimeAtRank (n + (j + 1)) : ℝ) =
      T m * Real.log (fnPrimeAtRank (n + m) : ℝ) - T 0 * Real.log (fnPrimeAtRank n : ℝ) := by
  rw [← Finset.sum_add_distrib]
  have key : ∀ j, T j * rPrimeGapLogRatio (n + j) +
      (T (j + 1) - T j) * Real.log (fnPrimeAtRank (n + (j + 1)) : ℝ) =
      T (j + 1) * Real.log (fnPrimeAtRank (n + (j + 1)) : ℝ) -
        T j * Real.log (fnPrimeAtRank (n + j) : ℝ) := by
    intro j
    unfold rPrimeGapLogRatio fnPrimeSuccessor
    have h0 : (0 : ℝ) < (fnPrimeAtRank (n + j) : ℝ) := by exact_mod_cast thm_primeAtRank_pos _
    have h1 : (0 : ℝ) < (fnPrimeAtRank (n + j + 1) : ℝ) := by exact_mod_cast thm_primeAtRank_pos _
    rw [Real.log_div h1.ne' h0.ne', show n + (j + 1) = n + j + 1 by ring]
    ring
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  have := Finset.sum_range_sub (fun j => T j * Real.log (fnPrimeAtRank (n + j) : ℝ)) m
  simpa using this

/-- **Toutes les transitions de même hauteur satisfont l'identité** : la suite constante `T_j = c`
(aucune progression de hauteur, `H = m`) la vérifie. La progression première minimale ne fixe donc
aucune progression de hauteur minimale. -/
theorem window_abel_all_sameHeight (c : ℝ) (n m : ℕ) :
    ∑ j ∈ range m, c * rPrimeGapLogRatio (n + j) +
      ∑ j ∈ range m, (c - c) * Real.log (fnPrimeAtRank (n + (j + 1)) : ℝ) =
      c * Real.log (fnPrimeAtRank (n + m) : ℝ) - c * Real.log (fnPrimeAtRank n : ℝ) :=
  window_abel_any_heights (fun _ => c) n m

#print axioms primeAtRank_gap_pair_ge_six
#print axioms primeAtRank_window_ge_three_mul
#print axioms primeAtRank_window_odd_ge
#print axioms gapClass6_residue_transition
#print axioms primeWindow_log_ge
#print axioms chain_phase_window_floor
#print axioms sameHeight_phase_progress
#print axioms window_height_split
#print axioms window_abel_any_heights
#print axioms window_abel_all_sameHeight

end RHV6Fresh
