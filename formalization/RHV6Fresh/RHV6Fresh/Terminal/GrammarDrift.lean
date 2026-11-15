/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MeetingPoint
import RHV6Fresh.Terminal.GrammarWordLoad

/-!
# La grammaire des écarts impose la dérive de l'amplitude aux rencontres (module isolé)

Correction de l'auteur (2026-10-29) : dire que la grammaire est « aveugle à la position radiale » ne
vaut que pour ses VALEURS (états, classes, transitions, magnitudes sont des fonctions du rang seul).
Ce que la grammaire IMPOSE aux rencontres n'est pas aveugle : entre deux rencontres, l'amplitude
relative de tout membre est multipliée par le rapport des deux premiers élevé à la position radiale
moins un demi. Ce pas vaut un, quel que soit l'écart, si et seulement si le membre est sur la ligne.
Hors ligne, chaque écart le fait dériver, et l'alternance forcée (deux changements d'état consécutifs
avancent exactement de six fois la somme des magnitudes plus un) fixe une dérive MINIMALE à chaque
paire de changements obligés : c'est la contrainte supplémentaire au point de rencontre.

Faits compilés, sans prémisse :

* `relativeAmplitude_ratio` : le rapport des amplitudes relatives en deux points est le rapport des
  points élevé à la position moins un demi ;
* `meeting_drift` : d'une rencontre à la suivante, la dérive est le rapport des premiers à cette
  puissance ; `meeting_drift_eq_one_iff` : neutre si et seulement si sur la ligne ;
* `alternation_drift` : sur deux changements d'état consécutifs au-delà de trois, la dérive vaut
  (un plus six fois l'avance grammaticale sur le premier) à cette puissance ;
* `alternation_drift_low_le`, `alternation_drift_high_ge` : sous la ligne, deux changements obligés
  font baisser l'amplitude relative d'au moins le facteur (un plus six sur le premier) à la puissance
  position moins un demi ; au-dessus, la font monter d'au moins l'inverse.

Aucun axiome, aucun `sorry`.
-/

namespace RHV6Fresh

open Complex RHV3Lean

/-- Le rapport des amplitudes relatives en deux points. -/
theorem relativeAmplitude_ratio (w : TrueZero) {x₁ x₂ : ℝ} (h₁ : 0 < x₁) (h₂ : 0 < x₂) :
    relativeAmplitude w x₂ / relativeAmplitude w x₁ = (x₂ / x₁) ^ (rZeroRadialPosition w.1 - 1 / 2) := by
  rw [relativeAmplitude_eq w h₁, relativeAmplitude_eq w h₂, Real.div_rpow h₂.le h₁.le]
  have hK : 0 < (zetaZeroMultiplicity (zeroPoint w) : ℝ) / (‖zeroPoint w‖ * ‖zeroPoint w + 1‖) :=
    div_pos (memberMultiplicity_pos w) (memberDenominator_pos w)
  have h1 : x₁ ^ (rZeroRadialPosition w.1 - 1 / 2) ≠ 0 := (Real.rpow_pos_of_pos h₁ _).ne'
  field_simp
  exact div_self (mul_pos (mul_pos (memberMultiplicity_pos w) (norm_zeroPoint_pos w))
    (norm_pos_iff.mpr (zeroPoint_add_one_ne_zero w))).ne'

theorem meetingPoint_pos (I : PrimeGapInterval) : 0 < meetingPoint I := by
  linarith [one_lt_meetingPoint I]

/-- **Dérive d'une rencontre à la suivante** : le rapport des deux premiers à la puissance position
moins un demi. -/
theorem meeting_drift (w : TrueZero) (n : ℕ) :
    relativeAmplitude w (meetingPoint ⟨n + 1⟩) / relativeAmplitude w (meetingPoint ⟨n⟩) =
      ((fnPrimeAtRank (n + 2) : ℝ) / (fnPrimeAtRank (n + 1) : ℝ)) ^ (rZeroRadialPosition w.1 - 1 / 2) :=
  relativeAmplitude_ratio w (meetingPoint_pos ⟨n⟩) (meetingPoint_pos ⟨n + 1⟩)

theorem meeting_ratio_gt_one (n : ℕ) : 1 < (fnPrimeAtRank (n + 2) : ℝ) / (fnPrimeAtRank (n + 1) : ℝ) := by
  rw [one_lt_div (by linarith [primeAtRank_one_lt_real (n + 1)])]
  exact_mod_cast thm_primeAtRank_strictMono (show n + 1 < n + 2 by omega)

/-- **Pas neutre si et seulement si sur la ligne**, quel que soit l'écart. -/
theorem meeting_drift_eq_one_iff (w : TrueZero) (n : ℕ) :
    relativeAmplitude w (meetingPoint ⟨n + 1⟩) / relativeAmplitude w (meetingPoint ⟨n⟩) = 1 ↔
      rZeroRadialPosition w.1 = 1 / 2 := by
  rw [meeting_drift]
  have hb := meeting_ratio_gt_one n
  have hb0 : 0 < (fnPrimeAtRank (n + 2) : ℝ) / (fnPrimeAtRank (n + 1) : ℝ) := by linarith
  have hlog : Real.log ((fnPrimeAtRank (n + 2) : ℝ) / (fnPrimeAtRank (n + 1) : ℝ)) ≠ 0 :=
    (Real.log_pos hb).ne'
  rw [Real.rpow_def_of_pos hb0, Real.exp_eq_one_iff, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hlog
    · linarith
  · intro h; right; linarith

/-- Au-delà du rang un, toute rencontre dépasse trois. -/
theorem primeAtRank_gt_three {n : ℕ} (hn : 2 ≤ n) : 3 < fnPrimeAtRank n := by
  have h0 := (thm_primeAtRank_isPrime 0).two_le
  have h01 := thm_primeAtRank_strictMono (show 0 < 1 by omega)
  have h1n := thm_primeAtRank_strictMono (show 1 < n by omega)
  have hp := thm_primeAtRank_isPrime n
  by_contra hcon
  have h4 : fnPrimeAtRank n = 4 := by omega
  rw [h4] at hp
  exact absurd hp (by decide)

/-- **Dérive sur deux changements d'état consécutifs** (rencontres au-delà de trois, classes non
nulles) : (un plus six fois l'avance grammaticale divisée par le premier) à la puissance position
moins un demi. -/
theorem alternation_drift (w : TrueZero) (n : ℕ) (hn : 2 ≤ n + 1)
    (h1 : gapClass6 (fnPrimeAtRank (n + 1)) (fnPrimeAtRank (n + 2)) ≠ 0)
    (h2 : gapClass6 (fnPrimeAtRank (n + 2)) (fnPrimeAtRank (n + 3)) ≠ 0) :
    relativeAmplitude w (meetingPoint ⟨n + 2⟩) / relativeAmplitude w (meetingPoint ⟨n⟩) =
      (1 + 6 * (((fnPrimeAtRank (n + 2) - fnPrimeAtRank (n + 1)) / 6 +
          (fnPrimeAtRank (n + 3) - fnPrimeAtRank (n + 2)) / 6 + 1 : ℕ) : ℝ) /
        (fnPrimeAtRank (n + 1) : ℝ)) ^ (rZeroRadialPosition w.1 - 1 / 2) := by
  rw [relativeAmplitude_ratio w (meetingPoint_pos ⟨n⟩) (meetingPoint_pos ⟨n + 2⟩)]
  change ((fnPrimeAtRank (n + 3) : ℝ) / (fnPrimeAtRank (n + 1) : ℝ)) ^ _ = _
  have hp3 : 3 < fnPrimeAtRank (n + 1) := primeAtRank_gt_three hn
  have hq3 : 3 < fnPrimeAtRank (n + 2) :=
    hp3.trans (thm_primeAtRank_strictMono (show n + 1 < n + 2 by omega))
  have hr3 : 3 < fnPrimeAtRank (n + 3) :=
    hq3.trans (thm_primeAtRank_strictMono (show n + 2 < n + 3 by omega))
  have hpq : fnPrimeAtRank (n + 1) ≤ fnPrimeAtRank (n + 2) :=
    (thm_primeAtRank_strictMono (show n + 1 < n + 2 by omega)).le
  have hqr : fnPrimeAtRank (n + 2) ≤ fnPrimeAtRank (n + 3) :=
    (thm_primeAtRank_strictMono (show n + 2 < n + 3 by omega)).le
  have hadv := alternating_two_step_gap (prime_goodMod6 _ (thm_primeAtRank_isPrime _) hp3)
    (prime_goodMod6 _ (thm_primeAtRank_isPrime _) hq3)
    (prime_goodMod6 _ (thm_primeAtRank_isPrime _) hr3) hpq hqr h1 h2
  congr 1
  have hp0 : (0 : ℝ) < fnPrimeAtRank (n + 1) := by exact_mod_cast (lt_trans (by norm_num) hp3)
  generalize (fnPrimeAtRank (n + 2) - fnPrimeAtRank (n + 1)) / 6 +
    (fnPrimeAtRank (n + 3) - fnPrimeAtRank (n + 2)) / 6 + 1 = k at hadv ⊢
  have hc : (fnPrimeAtRank (n + 3) : ℝ) = fnPrimeAtRank (n + 1) + 6 * (k : ℝ) := by
    have : fnPrimeAtRank (n + 3) = fnPrimeAtRank (n + 1) + 6 * k := by omega
    rw [this]; push_cast; ring
  rw [hc]
  field_simp

/-- L'avance grammaticale de deux changements vaut au moins un. -/
theorem two_step_advance_ge_one (a b : ℕ) : (1 : ℝ) ≤ ((a / 6 + b / 6 + 1 : ℕ) : ℝ) := by
  exact_mod_cast (show 1 ≤ a / 6 + b / 6 + 1 by omega)

/-- **Sous la ligne, deux changements obligés font baisser l'amplitude relative** d'au moins le
facteur (un plus six sur le premier) à la puissance position moins un demi (strictement sous un). -/
theorem alternation_drift_low_le (w : TrueZero) (hlow : rZeroRadialPosition w.1 ≤ 1 / 2) (n : ℕ)
    (hn : 2 ≤ n + 1)
    (h1 : gapClass6 (fnPrimeAtRank (n + 1)) (fnPrimeAtRank (n + 2)) ≠ 0)
    (h2 : gapClass6 (fnPrimeAtRank (n + 2)) (fnPrimeAtRank (n + 3)) ≠ 0) :
    relativeAmplitude w (meetingPoint ⟨n + 2⟩) ≤
      (1 + 6 / (fnPrimeAtRank (n + 1) : ℝ)) ^ (rZeroRadialPosition w.1 - 1 / 2) *
        relativeAmplitude w (meetingPoint ⟨n⟩) := by
  have hpos : 0 < relativeAmplitude w (meetingPoint ⟨n⟩) := by
    rw [relativeAmplitude_eq w (meetingPoint_pos _)]
    exact mul_pos (div_pos (memberMultiplicity_pos w) (memberDenominator_pos w))
      (Real.rpow_pos_of_pos (meetingPoint_pos _) _)
  have hd := alternation_drift w n hn h1 h2
  rw [div_eq_iff hpos.ne'] at hd
  rw [hd]
  refine mul_le_mul_of_nonneg_right ?_ hpos.le
  have hp0 : (0 : ℝ) < fnPrimeAtRank (n + 1) := by
    exact_mod_cast (lt_trans (by norm_num) (primeAtRank_gt_three hn))
  set k : ℕ := (fnPrimeAtRank (n + 2) - fnPrimeAtRank (n + 1)) / 6 +
    (fnPrimeAtRank (n + 3) - fnPrimeAtRank (n + 2)) / 6 + 1 with hkdef
  have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hbase : 1 + 6 / (fnPrimeAtRank (n + 1) : ℝ) ≤
      1 + 6 * (k : ℝ) / (fnPrimeAtRank (n + 1) : ℝ) := by
    have : 6 / (fnPrimeAtRank (n + 1) : ℝ) ≤ 6 * (k : ℝ) / (fnPrimeAtRank (n + 1) : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hp0.le
    linarith
  have h1pos : 0 < 1 + 6 / (fnPrimeAtRank (n + 1) : ℝ) := by positivity
  -- exposant non positif : la puissance est antitone en la base
  have hexp : rZeroRadialPosition w.1 - 1 / 2 ≤ 0 := by linarith
  calc (1 + 6 * (k : ℝ) / (fnPrimeAtRank (n + 1) : ℝ)) ^ (rZeroRadialPosition w.1 - 1 / 2)
      = ((1 + 6 * (k : ℝ) / (fnPrimeAtRank (n + 1) : ℝ))⁻¹) ^
          (-(rZeroRadialPosition w.1 - 1 / 2)) := by
        rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_neg]
    _ ≤ ((1 + 6 / (fnPrimeAtRank (n + 1) : ℝ))⁻¹) ^ (-(rZeroRadialPosition w.1 - 1 / 2)) := by
        refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
        exact inv_anti₀ h1pos hbase
    _ = (1 + 6 / (fnPrimeAtRank (n + 1) : ℝ)) ^ (rZeroRadialPosition w.1 - 1 / 2) := by
        rw [Real.inv_rpow h1pos.le, ← Real.rpow_neg h1pos.le, neg_neg]

/-- **Au-dessus de la ligne, deux changements obligés font monter l'amplitude relative** d'au moins le
facteur (un plus six sur le premier) à la puissance position moins un demi (strictement au-dessus de un). -/
theorem alternation_drift_high_ge (w : TrueZero) (hhigh : 1 / 2 ≤ rZeroRadialPosition w.1) (n : ℕ)
    (hn : 2 ≤ n + 1)
    (h1 : gapClass6 (fnPrimeAtRank (n + 1)) (fnPrimeAtRank (n + 2)) ≠ 0)
    (h2 : gapClass6 (fnPrimeAtRank (n + 2)) (fnPrimeAtRank (n + 3)) ≠ 0) :
    (1 + 6 / (fnPrimeAtRank (n + 1) : ℝ)) ^ (rZeroRadialPosition w.1 - 1 / 2) *
        relativeAmplitude w (meetingPoint ⟨n⟩) ≤
      relativeAmplitude w (meetingPoint ⟨n + 2⟩) := by
  have hpos : 0 < relativeAmplitude w (meetingPoint ⟨n⟩) := by
    rw [relativeAmplitude_eq w (meetingPoint_pos _)]
    exact mul_pos (div_pos (memberMultiplicity_pos w) (memberDenominator_pos w))
      (Real.rpow_pos_of_pos (meetingPoint_pos _) _)
  have hd := alternation_drift w n hn h1 h2
  rw [div_eq_iff hpos.ne'] at hd
  rw [hd]
  refine mul_le_mul_of_nonneg_right ?_ hpos.le
  have hp0 : (0 : ℝ) < fnPrimeAtRank (n + 1) := by
    exact_mod_cast (lt_trans (by norm_num) (primeAtRank_gt_three hn))
  set k : ℕ := (fnPrimeAtRank (n + 2) - fnPrimeAtRank (n + 1)) / 6 +
    (fnPrimeAtRank (n + 3) - fnPrimeAtRank (n + 2)) / 6 + 1 with hkdef
  have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hbase : 1 + 6 / (fnPrimeAtRank (n + 1) : ℝ) ≤
      1 + 6 * (k : ℝ) / (fnPrimeAtRank (n + 1) : ℝ) := by
    have : 6 / (fnPrimeAtRank (n + 1) : ℝ) ≤ 6 * (k : ℝ) / (fnPrimeAtRank (n + 1) : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hp0.le
    linarith
  exact Real.rpow_le_rpow (by positivity) hbase (by linarith)

/-- **Le facteur grammatical minimal est strictement sous un sous la ligne** (et strictement au-dessus
de un au-dessus) : la dérive imposée par deux changements obligés n'est jamais nulle hors ligne. -/
theorem grammar_factor_lt_one (w : TrueZero) (hlow : rZeroRadialPosition w.1 < 1 / 2) (n : ℕ) :
    (1 + 6 / (fnPrimeAtRank (n + 1) : ℝ)) ^ (rZeroRadialPosition w.1 - 1 / 2) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg
    (by have : (0 : ℝ) < fnPrimeAtRank (n + 1) := by linarith [primeAtRank_one_lt_real (n + 1)]
        have : 0 < 6 / (fnPrimeAtRank (n + 1) : ℝ) := by positivity
        linarith)
    (by linarith)

end RHV6Fresh
