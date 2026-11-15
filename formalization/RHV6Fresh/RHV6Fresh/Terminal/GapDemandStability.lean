/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.SpectralWindowProjection
import RHV6Fresh.Terminal.ConstantAmplitudeNeed
import RHV6Fresh.Terminal.WindowProgression
import RHV6Fresh.Terminal.GeneratedFrequency
import RHV6Fresh.Terminal.RegimeTrigger
import RHV6Fresh.Terminal.RaccordDetector
import RHV6Fresh.Terminal.AuthenticPassageProfile
import RHV6Fresh.Terminal.LocalPrimeGapSynchronization

/-!
# La demande des écarts premiers et la stabilité du régime engagé (E351, auteur, 2026-10-21)

Changement de forme de la fermeture demandé par l'auteur : ne plus prouver qu'un OFF est incompatible, mais que
**les écarts premiers réclament la stabilité de la ligne critique et rien d'autre**. Ce module écrit, du côté des
écarts, la quantité d'évolution logarithmique que les écarts mettent à disposition d'un signal, et les formes
positives de la stabilité ; il compile tout ce qui est démontrable pour toute position radiale, puis les fermetures
qui prennent la stabilité réclamée comme hypothèse, et enfin les équivalences qui disent exactement la force de
chaque forme.

## Identité de propagation de la dérive (texte de l'auteur, compilée)
Pour un mode de partie réelle `β`, `A_β(p) = p^{β−1/2}` (à la constante `2/‖ρ‖` près : `pairAmplitude`) ;
`log(A(p_{n+1})/A(p_n)) = (β − 1/2) log(1 + g_n/p_n)` ; sur une fenêtre de `m` écarts
`Σ log(A(p_{a+j+1})/A(p_{a+j})) = (β − 1/2) log(p_{a+m}/p_a)` (`window_drift_telescopes`). La dérive s'accumule selon
`log(p_m/p_0)`, pas selon le nombre d'écarts ; elle est nulle sur toute fenêtre à extrémités distinctes ⟺ `β = 1/2`
(`window_drift_zero_iff`). Le théorème `mirror_word_energy_debt` est bien une identité télescopique pour toute suite
positive (`mirror_debt_is_telescoping`).

## Objets côté écarts
* `gapBudget a m = log(p_{a+m}/p_a)` : quantité d'évolution logarithmique disponible sur la fenêtre (premiers seuls).
* `windowDrift z a m = Σ log(A_z(p_{r+1})/A_z(p_r))` : dérive de l'enveloppe normalisée d'un signal sur la fenêtre.
* `gapDemand I = R(b) − R(a)` : la demande exacte de l'écart (premiers seuls, `localArithmeticTarget`).

## Formes de stabilité (toutes caractérisent `β = 1/2`, aucune n'est dérivée)
* `WindowStable z` : dérive nulle sur toute fenêtre ; ⟺ ON (`windowStable_iff_onLine`).
* `DemandTransported p` : la dérive de l'arrivée égale celle du départ sur toute fenêtre ; depuis un départ ON ⟺
  arrivée ON (`demandTransported_iff_of_onLine`).
* `ImposedScaleStable z` : la contribution imposée (`R − part fixe des autres`) suit l'échelle commune `√x` d'un
  premier au suivant ; ⟺ ON (`imposedScaleStable_iff_onLine`).

## Fermetures (hypothèse = la stabilité réclamée, jamais un OFF)
* `regime_stable_of_window` : départ ON, passage qui monte, arrivée à dérive nulle ⟹ arrivée ON et le pas sortant monte.
* `regime_stable_of_transport`, `regime_stable_of_imposed_scale` : mêmes conclusions depuis les deux autres formes.
* `stability_law_iff_riemannHypothesis` : chacune des lois, quantifiée sur tous les passages qui montent depuis un
  membre ON, est équivalente à RH : aucune n'est plus faible que le but, aucune n'est dérivée ici.

## Ce que les écarts donnent sans la position (compilé, toute position radiale)
* la quantité disponible `gapBudget` est strictement positive dès `m ≥ 1`, bornée par la fenêtre (`gapBudget_pos`) ;
* la demande de chaque écart est la somme des contributions de tous les vrais zéros (`gapDemand_eq_sum`) ;
* la dérive d'un signal ne lit la fenêtre que par `gapBudget` (`windowDrift_eq`) : les écarts fixent la QUANTITÉ, le
  signe est fixé par `β − 1/2` seul.
-/

namespace RHV6Fresh

open Real RHV3Lean Finset

/-! ## 1. Quantité d'évolution disponible sur une fenêtre d'écarts (premiers seuls) -/

/-- Budget logarithmique d'une fenêtre de `m` écarts à partir du rang `a` : `log(p_{a+m}/p_a)`. -/
noncomputable def gapBudget (a m : ℕ) : ℝ :=
  Real.log (fnPrimeAtRank (a + m) : ℝ) - Real.log (fnPrimeAtRank a : ℝ)

theorem gapBudget_eq_sum (a m : ℕ) : gapBudget a m = ∑ j ∈ range m, rPrimeGapLogRatio (a + j) :=
  (primeGapLogRatio_window_sum a m).symm

theorem gapBudget_zero (a : ℕ) : gapBudget a 0 = 0 := by simp [gapBudget]

/-- Le budget est strictement positif dès qu'il y a un écart. -/
theorem gapBudget_pos (a m : ℕ) (hm : 0 < m) : 0 < gapBudget a m := by
  unfold gapBudget
  have h0 : (0 : ℝ) < (fnPrimeAtRank a : ℝ) := by exact_mod_cast thm_primeAtRank_pos a
  have hlt : (fnPrimeAtRank a : ℝ) < (fnPrimeAtRank (a + m) : ℝ) := by
    exact_mod_cast thm_primeAtRank_strictMono (Nat.lt_add_of_pos_right hm)
  linarith [Real.log_lt_log h0 hlt]

/-! ## 2. Dérive de l'enveloppe d'un signal sur une fenêtre -/

/-- Dérive logarithmique de l'enveloppe normalisée de `z` sur la fenêtre `[p_a, p_{a+m}]`. -/
noncomputable def windowDrift (z : TrueZero) (a m : ℕ) : ℝ :=
  ∑ j ∈ range m, Real.log (pairAmplitude z (fnPrimeSuccessor (a + j) : ℝ) /
    pairAmplitude z (fnPrimeAtRank (a + j) : ℝ))

/-- Sur un écart : `log(A(p_{r+1})/A(p_r)) = (β − 1/2) log(p_{r+1}/p_r)`. -/
theorem drift_step (z : TrueZero) (r : ℕ) :
    Real.log (pairAmplitude z (fnPrimeSuccessor r : ℝ) / pairAmplitude z (fnPrimeAtRank r : ℝ)) =
      (rZeroRadialPosition z.1 - 1 / 2) * rPrimeGapLogRatio r := by
  rw [pairAmplitude_prime_step, Real.log_exp]

/-- **Identité de propagation de la dérive (auteur)** : `Σ_{j<m} log(A(p_{a+j+1})/A(p_{a+j})) = (β − 1/2) log(p_{a+m}/p_a)`,
exacte pour toute fenêtre, toute longueur et toute `β`. -/
theorem window_drift_telescopes (z : TrueZero) (a m : ℕ) :
    windowDrift z a m = (rZeroRadialPosition z.1 - 1 / 2) * gapBudget a m := by
  unfold windowDrift
  rw [gapBudget_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => drift_step z (a + j)

/-- La dérive ne lit la fenêtre que par son budget ; le signe est celui de `β − 1/2` seul. -/
theorem windowDrift_eq (z : TrueZero) (a m : ℕ) :
    windowDrift z a m = (rZeroRadialPosition z.1 - 1 / 2) * gapBudget a m :=
  window_drift_telescopes z a m

/-- **La dérive est nulle sur une fenêtre à extrémités distinctes ⟺ `β = 1/2`.** -/
theorem window_drift_zero_iff (z : TrueZero) (a m : ℕ) (hm : 0 < m) :
    windowDrift z a m = 0 ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  rw [window_drift_telescopes]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · exact absurd h (gapBudget_pos a m hm).ne'
  · intro h; rw [h]; ring

/-- Sous un demi, la dérive est strictement négative sur toute fenêtre non vide ; au-dessus, strictement positive. -/
theorem window_drift_neg_of_low (z : TrueZero) (hz : rZeroRadialPosition z.1 < 1 / 2) (a m : ℕ) (hm : 0 < m) :
    windowDrift z a m < 0 := by
  rw [window_drift_telescopes]
  exact mul_neg_of_neg_of_pos (by linarith) (gapBudget_pos a m hm)

theorem window_drift_pos_of_high (z : TrueZero) (hz : 1 / 2 < rZeroRadialPosition z.1) (a m : ℕ) (hm : 0 < m) :
    0 < windowDrift z a m := by
  rw [window_drift_telescopes]
  exact mul_pos (by linarith) (gapBudget_pos a m hm)

/-- **La dérive s'accumule selon le budget logarithmique, pas selon le nombre d'écarts** : deux fenêtres de même budget
ont la même dérive quelle que soit leur longueur. -/
theorem window_drift_depends_on_budget_only (z : TrueZero) (a m a' m' : ℕ)
    (h : gapBudget a m = gapBudget a' m') : windowDrift z a m = windowDrift z a' m' := by
  rw [window_drift_telescopes, window_drift_telescopes, h]

/-- Paire miroir : les deux dérives sont opposées sur toute fenêtre (la somme des dérives est nulle), ce qui est la raison
pour laquelle une lecture paire en `d` ne voit pas la position. -/
theorem mirror_pair_drift_sum (z : TrueZero) (a m : ℕ) :
    windowDrift z a m + windowDrift (mirrorMember z) a m = 0 := by
  rw [window_drift_telescopes, window_drift_telescopes, mirrorMember_radial]; ring

/-- Le théorème `mirror_word_energy_debt` est une identité télescopique valable pour toute suite strictement positive. -/
theorem mirror_debt_is_telescoping (d : ℝ) (q : ℕ → ℝ) (m : ℕ) (hq : ∀ i, 0 < q i) :
    ∑ i ∈ range m, (2 * (1 / 2 + d) - 2 * (1 / 2 - d)) * (Real.log (q (i + 1)) - Real.log (q i)) =
      4 * d * Real.log (q m / q 0) :=
  mirror_word_energy_debt d q m (hq 0) (hq m)

/-! ## 3. La demande exacte d'un écart (premiers seuls) et sa réponse -/

/-- Demande d'un écart premier : incrément du reste des premiers entre ses deux bornes (objet des seuls premiers). -/
noncomputable def gapDemand (I : PrimeGapInterval) : ℂ := localArithmeticTarget I

/-- La demande de chaque écart est la somme des contributions locales de tous les vrais zéros (C126). -/
theorem gapDemand_eq_sum (I : PrimeGapInterval) :
    gapDemand I = ∑' ρ : ExplicitIndex, smoothedLocalContribution ρ I :=
  localSynchronization I

/-! ## 4. Les formes positives de la stabilité -/

/-- **Stabilité de fenêtre** : dérive nulle sur toute fenêtre d'écarts. -/
def WindowStable (z : TrueZero) : Prop := ∀ a m : ℕ, windowDrift z a m = 0

theorem windowStable_iff_onLine (z : TrueZero) : WindowStable z ↔ rZeroRadialPosition z.1 = 1 / 2 :=
  ⟨fun h => (window_drift_zero_iff z 0 1 one_pos).mp (h 0 1),
   fun h a m => by rw [window_drift_telescopes, h]; ring⟩

theorem windowStable_iff_constantNeed (z : TrueZero) : WindowStable z ↔ ConstantNeed z := by
  rw [windowStable_iff_onLine, constantNeed_iff_onLine]

/-- **Demande transportée** : sur un passage, la dérive de l'arrivée égale celle du départ sur toute fenêtre. -/
def DemandTransported (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) : Prop :=
  ∀ a m : ℕ, windowDrift ⟨p.zLaterMember, hL⟩ a m = windowDrift ⟨p.zEarlierMember, hE⟩ a m

/-- Demande transportée ⟺ même position radiale (identité du collé lue aux deux extrémités). -/
theorem demandTransported_iff (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    DemandTransported p hE hL ↔ rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember := by
  constructor
  · intro h
    have := h 0 1
    rw [window_drift_telescopes ⟨p.zLaterMember, hL⟩ 0 1,
      window_drift_telescopes ⟨p.zEarlierMember, hE⟩ 0 1] at this
    have hb := gapBudget_pos 0 1 one_pos
    have := mul_right_cancel₀ hb.ne' this
    linarith
  · intro h a m
    rw [window_drift_telescopes ⟨p.zLaterMember, hL⟩ a m,
      window_drift_telescopes ⟨p.zEarlierMember, hE⟩ a m, h]

/-- Depuis un départ ON : demande transportée ⟺ arrivée ON. -/
theorem demandTransported_iff_of_onLine (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    DemandTransported p hE hL ↔ rZeroRadialPosition p.zLaterMember = 1 / 2 := by
  rw [demandTransported_iff, hOn]

/-- **Échelle imposée stable** : la contribution imposée à `z` (reste des premiers moins la part fixe des autres vrais zéros)
suit l'échelle commune `√p` d'un premier au suivant. -/
def ImposedScaleStable (z : TrueZero) : Prop :=
  ∀ r : ℕ, ‖smoothedRemainder (fnPrimeSuccessor r : ℝ) - othersSum z (fnPrimeSuccessor r : ℝ)‖ /
      ‖smoothedRemainder (fnPrimeAtRank r : ℝ) - othersSum z (fnPrimeAtRank r : ℝ)‖ =
    Real.exp (1 / 2 * rPrimeGapLogRatio r)

theorem rPrimeGapLogRatio_pos (r : ℕ) : 0 < rPrimeGapLogRatio r := by
  unfold rPrimeGapLogRatio fnPrimeSuccessor
  have h0 : (0 : ℝ) < (fnPrimeAtRank r : ℝ) := by exact_mod_cast thm_primeAtRank_pos r
  have hlt : (fnPrimeAtRank r : ℝ) < (fnPrimeAtRank (r + 1) : ℝ) := by
    exact_mod_cast thm_primeAtRank_lt_successor r
  exact Real.log_pos ((one_lt_div h0).mpr hlt)

theorem imposedScaleStable_iff_onLine (z : TrueZero) :
    ImposedScaleStable z ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro h
    have := (imposed_contribution_drift z 0).1
    rw [h 0] at this
    have := Real.exp_injective this
    have hL := rPrimeGapLogRatio_pos 0
    have := mul_right_cancel₀ hL.ne' this
    linarith
  · intro hz r
    rw [(imposed_contribution_drift z r).1, hz]

/-- Les trois formes de stabilité coïncident (toutes caractérisent la ligne). -/
theorem stability_forms_agree (z : TrueZero) :
    (WindowStable z ↔ ImposedScaleStable z) ∧ (WindowStable z ↔ ConstantNeed z) := by
  refine ⟨?_, windowStable_iff_constantNeed z⟩
  rw [windowStable_iff_onLine, imposedScaleStable_iff_onLine]

/-! ## 5. Fermetures positives : la stabilité réclamée, jamais un OFF -/

/-- **Fermeture par la stabilité de fenêtre** : départ ON, passage qui monte, arrivée à dérive nulle sur UNE fenêtre non vide
⟹ arrivée ON et le pas sortant monte (la cascade continue par la hauteur). -/
theorem regime_stable_of_window {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hV : VerticalPassage p) (hL : 0 < rZeroHeight p.zLaterMember) (a m : ℕ) (hm : 0 < m)
    (hStable : windowDrift ⟨p.zLaterMember, hL⟩ a m = 0) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ∧ VerticalPassage q := by
  have hOnL : rZeroRadialPosition p.zLaterMember = 1 / 2 := (window_drift_zero_iff _ a m hm).mp hStable
  exact ⟨hOnL, (engaged_regime_kept hJ hV hOnL).1⟩

/-- **Fermeture par la demande transportée** depuis un départ ON. -/
theorem regime_stable_of_transport {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hV : VerticalPassage p) (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) (hT : DemandTransported p hE hL) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ∧ VerticalPassage q := by
  have hOnL := (demandTransported_iff_of_onLine p hE hL hOn).mp hT
  exact ⟨hOnL, (engaged_regime_kept hJ hV hOnL).1⟩

/-- **Fermeture par l'échelle imposée stable** sur un seul écart. -/
theorem regime_stable_of_imposed_scale {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hV : VerticalPassage p) (hL : 0 < rZeroHeight p.zLaterMember) (r : ℕ)
    (hStable : ‖smoothedRemainder (fnPrimeSuccessor r : ℝ) - othersSum ⟨p.zLaterMember, hL⟩ (fnPrimeSuccessor r : ℝ)‖ /
      ‖smoothedRemainder (fnPrimeAtRank r : ℝ) - othersSum ⟨p.zLaterMember, hL⟩ (fnPrimeAtRank r : ℝ)‖ =
      Real.exp (1 / 2 * rPrimeGapLogRatio r)) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ∧ VerticalPassage q := by
  have h := (imposed_contribution_drift ⟨p.zLaterMember, hL⟩ r).1
  rw [hStable] at h
  have h := mul_right_cancel₀ (rPrimeGapLogRatio_pos r).ne' (Real.exp_injective h)
  have hOnL : rZeroRadialPosition p.zLaterMember = 1 / 2 := by simpa using h.symm
  exact ⟨hOnL, (engaged_regime_kept hJ hV hOnL).1⟩

/-- Sur un passage qui monte, la dérive de l'arrivée est `≤ 0` sur toute fenêtre (côté haut exclu par l'ordre de la fibre) :
la stabilité réclamée se réduit à « la dérive ne descend pas ». -/
theorem arrival_drift_nonpos (p : TZeroPassage) (hV : VerticalPassage p) (hL : 0 < rZeroHeight p.zLaterMember)
    (a m : ℕ) : windowDrift ⟨p.zLaterMember, hL⟩ a m ≤ 0 := by
  rw [window_drift_telescopes ⟨p.zLaterMember, hL⟩ a m]
  have hle := passage_entry_radial_le_half p hV
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [gapBudget_zero]
  · exact mul_nonpos_of_nonpos_of_nonneg (by simpa using hle) (gapBudget_pos a m hm).le

/-- La stabilité réclamée, sur un passage qui monte, est exactement « la dérive de l'arrivée n'est pas négative sur UNE
fenêtre non vide ». -/
theorem arrival_onLine_iff_drift_nonneg (p : TZeroPassage) (hV : VerticalPassage p) (hL : 0 < rZeroHeight p.zLaterMember)
    (a m : ℕ) (hm : 0 < m) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ↔ 0 ≤ windowDrift ⟨p.zLaterMember, hL⟩ a m := by
  constructor
  · intro h
    rw [(window_drift_zero_iff ⟨p.zLaterMember, hL⟩ a m hm).mpr h]
  · intro h
    exact (window_drift_zero_iff ⟨p.zLaterMember, hL⟩ a m hm).mp
      (le_antisymm (arrival_drift_nonpos p hV hL a m) h)

/-! ## 6. Deux phénomènes distincts dans une projection (point 2 de l'auteur) -/

/-- **Cohérence de phase** : la projection d'un mode isolé sur sa propre fréquence est l'intégrale de son enveloppe, non
nulle pour TOUTE position radiale (un mode sous un demi produit un pic aussi net qu'un mode de la ligne) : l'existence d'un pic
ne prouve pas la stabilité. -/
theorem coherent_peak_any_radial (A : ℂ) (hA : A ≠ 0) (β T U L : ℝ) (hL : 0 < L) :
    logWindowProjection (isolatedMode A β T) T U L ≠ 0 := by
  rw [isolatedMode_projection]
  refine mul_ne_zero hA ?_
  have hpos : 0 < ∫ u in U..U + L, Real.exp ((β - 1 / 2) * u) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
      (fun _ _ => Real.exp_pos _) (by linarith)
  exact_mod_cast hpos.ne'

/-- **Évolution de l'amplitude** : seule la comparaison de deux fenêtres translatées lit l'exposant ; le rapport vaut un pour
toute translation ⟺ `β = 1/2`. Ni la cohérence ni la comparaison ne forcent l'exposant : elles le mesurent. -/
theorem translated_ratio_one_iff (A : ℂ) (hA : A ≠ 0) (β T U L H : ℝ) (hL : 0 < L) (hH : H ≠ 0) :
    ‖logWindowProjection (isolatedMode A β T) T (U + H) L‖ / ‖logWindowProjection (isolatedMode A β T) T U L‖ = 1 ↔
      β = 1 / 2 := by
  rw [isolatedMode_projection_ratio A β T U L H (coherent_peak_any_radial A hA β T U L hL)]
  constructor
  · intro h
    have := Real.exp_eq_one_iff _ |>.mp h
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd h' hH
  · intro h; rw [h]; simp

/-- La dérive de fenêtre d'écarts et le rapport de projections translatées lisent le MÊME nombre : sur une translation
`H = gapBudget a m`, `log` du rapport = `windowDrift z a m`. -/
theorem projection_ratio_eq_window_drift (A : ℂ) (hA : A ≠ 0) (z : TrueZero) (U L : ℝ) (hL : 0 < L) (a m : ℕ) :
    Real.log (‖logWindowProjection (isolatedMode A (rZeroRadialPosition z.1) (rZeroHeight z.1)) (rZeroHeight z.1)
        (U + gapBudget a m) L‖ /
      ‖logWindowProjection (isolatedMode A (rZeroRadialPosition z.1) (rZeroHeight z.1)) (rZeroHeight z.1) U L‖) =
      windowDrift z a m := by
  rw [isolatedMode_projection_ratio _ _ _ _ _ _ (coherent_peak_any_radial A hA _ _ U L hL), Real.log_exp,
    window_drift_telescopes]

/-! ## 7. Canal commun et canal différentiel (point 5 de l'auteur) : identité de découpage, compilée -/

/-- Découpage exact d'une somme sur les entiers `< N` d'un poids `w` en classes modulo `3` : classe `1`, classe `2`, reste
(multiples de `3`). C'est l'identité combinatoire derrière « canal commun = classe 1 + classe 5 (mod 6) + puissances de 2 et 3 »
(canal `Λ(n)`), valable pour tout poids. -/
theorem common_channel_split (w : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, w n =
      (∑ n ∈ range N, if n % 3 = 1 then w n else 0) + (∑ n ∈ range N, if n % 3 = 2 then w n else 0) +
        ∑ n ∈ range N, if n % 3 = 0 then w n else 0 := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  interval_cases hn : n % 3 <;> simp

/-- Canal différentiel `χ₃` : classe `1` moins classe `2`. Classe `1` et classe `2` se retrouvent exactement depuis les deux
canaux : `2·classe 1 = (commun − reste) + différentiel`, `2·classe 2 = (commun − reste) − différentiel`. -/
theorem differential_channel_recovers_classes (w : ℕ → ℝ) (N : ℕ) :
    2 * (∑ n ∈ range N, if n % 3 = 1 then w n else 0) =
      ((∑ n ∈ range N, w n) - ∑ n ∈ range N, if n % 3 = 0 then w n else 0) +
        ((∑ n ∈ range N, if n % 3 = 1 then w n else 0) - ∑ n ∈ range N, if n % 3 = 2 then w n else 0) ∧
    2 * (∑ n ∈ range N, if n % 3 = 2 then w n else 0) =
      ((∑ n ∈ range N, w n) - ∑ n ∈ range N, if n % 3 = 0 then w n else 0) -
        ((∑ n ∈ range N, if n % 3 = 1 then w n else 0) - ∑ n ∈ range N, if n % 3 = 2 then w n else 0) := by
  have h := common_channel_split w N
  constructor <;> linarith

/-- Les deux canaux ont des dérives de fenêtre de même forme pour toute enveloppe `p^{β−1/2}` : la dérive d'un mode ne
dépend pas du canal où on le lit (`windowDrift` ne lit que `β` et le budget). Identité, pas une contrainte : le canal
différentiel porte les modes de `L(χ₃)`, dont aucun théorème des bases ne relie la position à celle d'un zéro de `ζ`. -/
theorem drift_channel_independent (z : TrueZero) (a m : ℕ) :
    windowDrift z a m = (rZeroRadialPosition z.1 - 1 / 2) * ∑ j ∈ range m, rPrimeGapLogRatio (a + j) := by
  rw [window_drift_telescopes, gapBudget_eq_sum]

/-! ## 8. Force exacte de chaque loi de stabilité -/

/-- **Loi de stabilité de fenêtre** (toute fenêtre, sur tout passage qui monte depuis un membre ON) ⟺ loi de conservation du
régime de la chaîne. -/
theorem window_stability_law_iff_conservation :
    (∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      ∀ hL : 0 < rZeroHeight p.zLaterMember, WindowStable ⟨p.zLaterMember, hL⟩) ↔
    (∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember) := by
  constructor
  · intro h p hE hV hOn
    have hL : 0 < rZeroHeight p.zLaterMember := lt_trans hE hV
    rw [hOn]; exact (windowStable_iff_onLine _).mp (h p hE hV hOn hL)
  · intro h p hE hV hOn hL
    exact (windowStable_iff_onLine _).mpr (by rw [h p hE hV hOn, hOn])

/-- **Sous l'ancre, la loi de stabilité de fenêtre ⟺ RH** : la stabilité réclamée par les écarts, quantifiée, n'est pas plus
faible que le but ; elle n'est dérivée ici d'aucun fait. -/
theorem window_stability_law_iff_riemannHypothesis (hAnchor : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    (∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      ∀ hL : 0 < rZeroHeight p.zLaterMember, WindowStable ⟨p.zLaterMember, hL⟩) ↔ RiemannHypothesis := by
  rw [window_stability_law_iff_conservation]
  exact ⟨riemannHypothesis_of_anchor_and_conservation hAnchor, conservation_of_riemannHypothesis⟩

/-- Même force pour la demande transportée et pour l'échelle imposée stable. -/
theorem transport_law_iff_riemannHypothesis (hAnchor : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    (∀ p : TZeroPassage, ∀ hE : 0 < rZeroHeight p.zEarlierMember, VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      ∀ hL : 0 < rZeroHeight p.zLaterMember, DemandTransported p hE hL) ↔ RiemannHypothesis := by
  constructor
  · intro h
    refine riemannHypothesis_of_anchor_and_conservation hAnchor fun p hE hV hOn => ?_
    exact (demandTransported_iff p hE (lt_trans hE hV)).mp (h p hE hV hOn _)
  · intro hRH p hE hV hOn hL
    exact (demandTransported_iff p hE hL).mpr (conservation_of_riemannHypothesis hRH p hE hV hOn)

theorem imposed_scale_law_iff_riemannHypothesis (hAnchor : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    (∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      ∀ hL : 0 < rZeroHeight p.zLaterMember, ImposedScaleStable ⟨p.zLaterMember, hL⟩) ↔ RiemannHypothesis := by
  constructor
  · intro h
    refine riemannHypothesis_of_anchor_and_conservation hAnchor fun p hE hV hOn => ?_
    rw [hOn]; exact (imposedScaleStable_iff_onLine _).mp (h p hE hV hOn (lt_trans hE hV))
  · intro hRH p hE hV hOn hL
    exact (imposedScaleStable_iff_onLine _).mpr
      (by rw [conservation_of_riemannHypothesis hRH p hE hV hOn, hOn])

#print axioms window_drift_telescopes
#print axioms window_drift_zero_iff
#print axioms regime_stable_of_window
#print axioms regime_stable_of_transport
#print axioms regime_stable_of_imposed_scale
#print axioms arrival_onLine_iff_drift_nonneg
#print axioms coherent_peak_any_radial
#print axioms translated_ratio_one_iff
#print axioms differential_channel_recovers_classes
#print axioms window_stability_law_iff_riemannHypothesis

end RHV6Fresh
