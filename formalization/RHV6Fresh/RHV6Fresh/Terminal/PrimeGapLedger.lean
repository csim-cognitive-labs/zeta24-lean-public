/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TransmissionIncrements
import RHV6Fresh.Terminal.AmplitudePhase
import RHV6Fresh.Terminal.CountingFieldContacts

/-!
# Registre d'un écart de premiers : enveloppe de chaque contribution et partage du reste (auteur, 2026-10-12 ; E206)

Sur l'écart `[p_n, p_{n+1}]` entre deux premiers consécutifs, deux pièces déjà démontrées séparément sont réunies :

* §1 **enveloppe de comptage d'une contribution sur l'écart** : la variation de la contribution de comptage `b_ρ` d'un zéro
  entre deux premiers consécutifs est bornée par `2 p_n^{β−1} Δli_n ≤ 2 p_n^{β−1} g_n / log p_n`, avec
  `g_n = 6 m_n + a_n` (magnitude et classe de l'événement) : l'enveloppe est FIXÉE par la grammaire de l'écart et la
  position radiale du zéro ; sous la ligne elle est au plus celle de la ligne (`gap_envelope_le_onLine_of_low`) ;
* §2 **partage du reste sur l'écart** (canal `ψ` lissé, seule représentation démontrée) : l'incrément du reste entre les
  deux premiers = part déjà comblée par les zéros sous la hauteur de départ + part de la fibre du zéro suivant + part
  comblée par les zéros au-dessus de l'arrivée ; l'attendu de la fibre suivante sur l'écart = reste − passé − futur ;
  la part future et le retrait de l'historique sont bornés à l'exposant `1` seulement ;
* §3 **déficit de comptage sur l'écart** : `Δ(π − li₂) = 1 − Δli_n`, encadré par l'écart.

Portée : identités et majorations individuelles, vraies pour toute position radiale. Aucune formule explicite du canal
`J` n'existe dans le dépôt : la part des zéros dans le canal de comptage n'est pas reliée au canal `ψ` lissé (E206 la mesure
hors Lean). Rien ici ne fixe la position radiale du zéro suivant.
-/

namespace RHV6Fresh

open RHV3Lean

/-- `p_n > 1`. -/
theorem primeAtRank_gt_one (n : ℕ) : (1 : ℝ) < fnPrimeAtRank n := by
  have h2 : (2 : ℝ) ≤ fnPrimeAtRank n := by exact_mod_cast (thm_primeAtRank_isPrime n).two_le
  linarith

/-- `(g_n : ℝ) = p_{n+1} − p_n`. -/
theorem primeGap_cast (n : ℕ) :
    (nPrimeGap n : ℝ) = (fnPrimeAtRank (n + 1) : ℝ) - fnPrimeAtRank n := by
  unfold nPrimeGap fnPrimeSuccessor
  rw [Nat.cast_sub (thm_primeAtRank_strictMono (Nat.lt_succ_self n)).le]

/-- Enveloppe de comptage d'un zéro sur l'écart `n` : `2 p_n^{β−1} g_n / log p_n`. -/
noncomputable def gapCountingEnvelope (z : TrueZero) (n : ℕ) : ℝ :=
  2 * (fnPrimeAtRank n : ℝ) ^ (rZeroRadialPosition z.1 - 1) * (nPrimeGap n : ℝ) / Real.log (fnPrimeAtRank n)

/-! ## 1. Enveloppe d'une contribution sur un écart de premiers -/

/-- **Contribution d'un zéro sur l'écart, bornée par le fond de l'écart** : `|Δb_ρ| ≤ 2 p_n^{β−1} Δli_n`. -/
theorem gap_modulation_le_background (z : TrueZero) (n : ℕ) :
    |cellModulation z (fnPrimeAtRank n) (fnPrimeAtRank (n + 1))| ≤
      2 * (fnPrimeAtRank n : ℝ) ^ (rZeroRadialPosition z.1 - 1) *
        cellBackground (fnPrimeAtRank n) (fnPrimeAtRank (n + 1)) :=
  cellModulation_abs_le z (primeAtRank_gt_one n)
    (by exact_mod_cast (thm_primeAtRank_strictMono (Nat.lt_succ_self n)).le)

/-- **Enveloppe fixée par l'écart** : `|Δb_ρ| ≤ 2 p_n^{β−1} g_n / log p_n`. -/
theorem gap_modulation_le_envelope (z : TrueZero) (n : ℕ) :
    |cellModulation z (fnPrimeAtRank n) (fnPrimeAtRank (n + 1))| ≤ gapCountingEnvelope z n := by
  refine (gap_modulation_le_background z n).trans ?_
  have hpos : 0 < 2 * (fnPrimeAtRank n : ℝ) ^ (rZeroRadialPosition z.1 - 1) := by
    have := thm_primeAtRank_pos n
    positivity
  have hb := (logIntegral_prime_step_bounds n).2
  unfold gapCountingEnvelope
  rw [primeGap_cast, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hb hpos.le

/-- **L'enveloppe lue par la grammaire** : `2 p_n^{β−1} (6 m_n + a_n) / log p_n`. -/
theorem gapCountingEnvelope_grammar (z : TrueZero) (n : ℕ) :
    gapCountingEnvelope z n =
      2 * (fnPrimeAtRank n : ℝ) ^ (rZeroRadialPosition z.1 - 1) *
        (6 * (gapMagnitude n : ℝ) + (eventClass n : ℝ)) / Real.log (fnPrimeAtRank n) := by
  unfold gapCountingEnvelope
  rw [primeGap_eq_magnitude_class n]
  push_cast
  ring

/-- **Plancher grammatical de l'enveloppe** (`p_n > 3`) : `≥ 2 p_n^{β−1} plancher(a_n) / log p_n`. -/
theorem gapCountingEnvelope_ge_classFloor (z : TrueZero) (n : ℕ) (h3 : 3 < fnPrimeAtRank n) :
    2 * (fnPrimeAtRank n : ℝ) ^ (rZeroRadialPosition z.1 - 1) * (classFloor (eventClass n) : ℝ) /
        Real.log (fnPrimeAtRank n) ≤ gapCountingEnvelope z n := by
  unfold gapCountingEnvelope
  have hlog : 0 < Real.log (fnPrimeAtRank n) := Real.log_pos (primeAtRank_gt_one n)
  have hpos : 0 ≤ 2 * (fnPrimeAtRank n : ℝ) ^ (rZeroRadialPosition z.1 - 1) := by
    have := thm_primeAtRank_pos n
    positivity
  have hfl : (classFloor (eventClass n) : ℝ) ≤ nPrimeGap n := by
    exact_mod_cast primeGap_ge_classFloor n h3
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfl hpos) hlog.le

/-- **Sous la ligne, l'enveloppe est au plus celle de la ligne** : `β ≤ 1/2 ⟹ env(β) ≤ 2 p_n^{−1/2} g_n / log p_n`. -/
theorem gap_envelope_le_onLine_of_low (z : TrueZero) (n : ℕ) (hlow : rZeroRadialPosition z.1 ≤ 1 / 2) :
    gapCountingEnvelope z n ≤
      2 * (fnPrimeAtRank n : ℝ) ^ ((1 : ℝ) / 2 - 1) * (nPrimeGap n : ℝ) / Real.log (fnPrimeAtRank n) := by
  unfold gapCountingEnvelope
  have hlog : 0 < Real.log (fnPrimeAtRank n) := Real.log_pos (primeAtRank_gt_one n)
  have hp := primeAtRank_gt_one n
  have hrpow : (fnPrimeAtRank n : ℝ) ^ (rZeroRadialPosition z.1 - 1) ≤
      (fnPrimeAtRank n : ℝ) ^ ((1 : ℝ) / 2 - 1) :=
    Real.rpow_le_rpow_of_exponent_le hp.le (by linarith)
  have hg : (0 : ℝ) ≤ nPrimeGap n := Nat.cast_nonneg _
  apply div_le_div_of_nonneg_right _ hlog.le
  have := mul_le_mul_of_nonneg_left hrpow (by norm_num : (0 : ℝ) ≤ 2)
  exact mul_le_mul_of_nonneg_right this hg

/-- **Hiérarchie des enveloppes sur un même écart** : à position radiale égale, l'enveloppe de comptage ne dépend pas de
la hauteur (la hauteur règle la fréquence, non l'enveloppe de comptage). -/
theorem gapCountingEnvelope_eq_of_radial {z w : TrueZero}
    (h : rZeroRadialPosition z.1 = rZeroRadialPosition w.1) (n : ℕ) :
    gapCountingEnvelope z n = gapCountingEnvelope w n := by
  unfold gapCountingEnvelope; rw [h]

/-! ## 2. Partage du reste sur l'écart (canal `ψ` lissé) -/

/-- **Registre de l'écart** : `ΔR = ΔP_{T_e} (déjà comblé) + Δfibre]T_e, T_l] (zéro suivant) + ΔQ_{T_l} (au-dessus)` et
l'attendu de la fibre suivante sur l'écart `= ΔR − ΔP_{T_e} − ΔQ_{T_l}`. -/
theorem prime_gap_ledger (He Hl : ℝ) (n : ℕ) :
    let a : ℝ := fnPrimeAtRank n
    let b : ℝ := fnPrimeAtRank (n + 1)
    (smoothedRemainder b - smoothedRemainder a : ℂ) =
        (precedingSum He b - precedingSum He a) + (nextFiberSum He Hl b - nextFiberSum He Hl a) +
          (followingSum Hl b - followingSum Hl a) ∧
      nextFiberSum He Hl b - nextFiberSum He Hl a =
        (smoothedRemainder b - smoothedRemainder a) - (precedingSum He b - precedingSum He a) -
          (followingSum Hl b - followingSum Hl a) := by
  intro a b
  have ha : 1 < a := primeAtRank_gt_one n
  have hb : 1 < b := primeAtRank_gt_one (n + 1)
  exact ⟨transmission_increment_split He Hl ha hb, expected_next_fiber_increment He Hl ha hb⟩

/-- **Ce qui est borné sur l'écart** : la part au-dessus de l'arrivée et le retrait de l'historique, à l'exposant `1`
seulement : `≤ budget·(p_n + p_{n+1})`. -/
theorem prime_gap_ledger_bounds (He Hl : ℝ) (n : ℕ) :
    ‖followingSum Hl (fnPrimeAtRank (n + 1)) - followingSum Hl (fnPrimeAtRank n)‖ ≤
        followingBudget Hl * ((fnPrimeAtRank n : ℝ) + fnPrimeAtRank (n + 1)) ∧
      ‖(smoothedRemainder (fnPrimeAtRank (n + 1)) - precedingSum He (fnPrimeAtRank (n + 1))) -
          (smoothedRemainder (fnPrimeAtRank n) - precedingSum He (fnPrimeAtRank n))‖ ≤
        followingBudget He * ((fnPrimeAtRank n : ℝ) + fnPrimeAtRank (n + 1)) :=
  ⟨tail_window_increment_bound Hl (primeAtRank_gt_one n) (primeAtRank_gt_one (n + 1)),
    removal_increment_le He (primeAtRank_gt_one n) (primeAtRank_gt_one (n + 1))⟩

/-- **Fenêtre d'écarts consécutifs** : le registre se télescope de `p_n` à `p_{n+m}` (somme des parts sur les écarts =
parts entre les extrémités). -/
theorem prime_gap_ledger_window (He Hl : ℝ) (n m : ℕ) :
    ∑ j ∈ Finset.range m,
        (nextFiberSum He Hl (fnPrimeAtRank (n + j + 1)) - nextFiberSum He Hl (fnPrimeAtRank (n + j))) =
      nextFiberSum He Hl (fnPrimeAtRank (n + m)) - nextFiberSum He Hl (fnPrimeAtRank n) := by
  have := Finset.sum_range_sub (fun j => nextFiberSum He Hl (fnPrimeAtRank (n + j))) m
  simpa [add_assoc] using this

/-! ## 3. Déficit de comptage sur l'écart -/

/-- **`Δ(π − li₂)` sur l'écart, encadré par la grammaire** : `1 − g_n/log p_n ≤ Δ ≤ 1 − g_n/log p_{n+1}`. -/
theorem countingDeficit_gap_bounds (n : ℕ) :
    1 - (nPrimeGap n : ℝ) / Real.log (fnPrimeAtRank n) ≤
        countingDeficit (fnPrimeAtRank (n + 1)) - countingDeficit (fnPrimeAtRank n) ∧
      countingDeficit (fnPrimeAtRank (n + 1)) - countingDeficit (fnPrimeAtRank n) ≤
        1 - (nPrimeGap n : ℝ) / Real.log (fnPrimeAtRank (n + 1)) := by
  rw [countingDeficit_step, primeGap_cast]
  have h := logIntegral_prime_step_bounds n
  constructor <;> linarith [h.1, h.2]

/-- **Registre complet d'un écart pour le zéro atteint** : enveloppe de comptage fixée par la grammaire, partage du
reste lissé (passé / fibre suivante / futur), bornes acquises (exposant `1`), déficit de comptage encadré. Toute
position radiale. -/
theorem prime_gap_full_ledger (z : TrueZero) (He Hl : ℝ) (n : ℕ) :
    |cellModulation z (fnPrimeAtRank n) (fnPrimeAtRank (n + 1))| ≤ gapCountingEnvelope z n ∧
      gapCountingEnvelope z n =
        2 * (fnPrimeAtRank n : ℝ) ^ (rZeroRadialPosition z.1 - 1) *
          (6 * (gapMagnitude n : ℝ) + (eventClass n : ℝ)) / Real.log (fnPrimeAtRank n) ∧
      (nextFiberSum He Hl (fnPrimeAtRank (n + 1)) - nextFiberSum He Hl (fnPrimeAtRank n) =
        (smoothedRemainder (fnPrimeAtRank (n + 1)) - smoothedRemainder (fnPrimeAtRank n)) -
          (precedingSum He (fnPrimeAtRank (n + 1)) - precedingSum He (fnPrimeAtRank n)) -
          (followingSum Hl (fnPrimeAtRank (n + 1)) - followingSum Hl (fnPrimeAtRank n))) ∧
      ‖followingSum Hl (fnPrimeAtRank (n + 1)) - followingSum Hl (fnPrimeAtRank n)‖ ≤
        followingBudget Hl * ((fnPrimeAtRank n : ℝ) + fnPrimeAtRank (n + 1)) :=
  ⟨gap_modulation_le_envelope z n, gapCountingEnvelope_grammar z n, (prime_gap_ledger He Hl n).2,
    (prime_gap_ledger_bounds He Hl n).1⟩

#print axioms prime_gap_full_ledger
#print axioms gap_envelope_le_onLine_of_low
#print axioms gapCountingEnvelope_ge_classFloor
#print axioms countingDeficit_gap_bounds
#print axioms prime_gap_ledger_window

end RHV6Fresh
