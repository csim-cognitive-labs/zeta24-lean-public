/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MeetingContactReading

/-!
# RHV6Fresh — Terminal/GapPartialRemainders : les intervalles de contacts sont des restes partiels d'écart
(E436, §19.51–19.52, 2026-11-06 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse, aucun axiome,
aucun `sorry`)

Cadre de l'auteur (2026-11-06) : les intervalles définis par les contacts d'une Tour sont des restes partiels des écarts
des premiers ; ils ne sont pas liés directement aux premiers ; la somme infinie n'est pas un appui et ne comble aucun
écart. Objets : contact `contactAt`, valeur au contact `contactRealValue`, contribution de cellule brute
`towerValue ρ p_{n+1} − towerValue ρ p_n`, bilan au point de rencontre avec reste explicite (`breakResidual`).

## S1. Découpage
* `rawCellContribution ρ I = (p_{n+1}^ρ − p_n^ρ)/ρ` ; pour toute Tour `(β, T)` dont l'écart contient un contact
  (`GapHasContact`), `rawCellContribution_eq_remainders` : contribution = reste partiel initial (de `p_n` au premier
  contact, `initialEdgeRemainder`) + cellules entières (`wholeCellSum`) + reste partiel final (du dernier contact à
  `p_{n+1}`, `finalEdgeRemainder`). Identité télescopique, aucune hypothèse sur la Tour ni sur la position radiale.
* Les contacts du découpage sont dans l'écart (`firstContact_gt_lower`, `lastContact_le_upper`) ; les restes de bord
  couvrent des fractions de cellule : `initialRemainder_span` (`π(1 − f(p_n))/T`), `finalRemainder_span`
  (`π f(p_{n+1})/T`, `< π/T`). Sans contact dans l'écart, l'écart tient dans une cellule
  (`gap_span_lt_cell_of_no_contact`).

## S2. Fréquence partagée
* Deux Tours de même fréquence ont des positions d'étage décalées de la constante radiale `stageOffset`
  (`stagePosition_same_height`) ; leurs nombres de contacts dans tout écart diffèrent d'au plus un
  (`same_height_contact_count_diff`, instance miroir `mirror_contact_count_diff`).
* **Sur-amplitude du miroir aux contacts** : pour `β < 1/2`, le rapport de deux valeurs consécutives aux contacts du
  miroir dépasse strictement celui du zéro (`mirror_contact_ratio_gt`).

## S3. Série d'écarts
* Au point de rencontre `p_{n+1}`, le reste final de l'écart `n` et le reste initial de l'écart `n+1` recomposent
  exactement une cellule de la Tour (`edge_remainders_complete_cell`).
* Sur `J` écarts consécutifs, la somme des contributions de cellule télescope (`rawCellContribution_series`) et ne lit,
  pour chaque Tour, que des cellules entières et deux restes de bord (`rawCellContribution_series_eq_accumulation`).

## S4 (sondes, buts laissés : `experiments/E436_GapPartialRemainders/RESULTS.md`)
Bilan avec reste explicite pour une famille finie contenant la paire, croissance des valeurs aux contacts du miroir :
aucune contradiction dérivée ; buts reproduits intégralement. Rien ici n'exclut un zéro OFF.
-/

namespace RHV6Fresh

open Real RHV3Lean

/-! ## S1. Contribution de cellule brute d'une Tour sur un écart, découpée par ses propres contacts -/

/-- Contribution de cellule brute d'une Tour `ρ` à l'écart `I` : `(p_{n+1}^ρ − p_n^ρ)/ρ`. -/
noncomputable def rawCellContribution (ρ : ℂ) (I : PrimeGapInterval) : ℂ :=
  towerValue ρ I.upper - towerValue ρ I.lower

/-- Premier contact de la Tour `(β, T)` strictement après `p_n`. -/
noncomputable def firstContactAfterLower (β T : ℝ) (I : PrimeGapInterval) : ℤ :=
  lastContactBefore β T I.lower + 1

/-- Nombre de cellules entières de la Tour `(β, T)` contenues dans l'écart. -/
noncomputable def wholeCellCount (β T : ℝ) (I : PrimeGapInterval) : ℕ :=
  (lastContactBefore β T I.upper - firstContactAfterLower β T I).toNat

/-- Reste partiel initial : de `p_n` au premier contact dans l'écart. -/
noncomputable def initialEdgeRemainder (F : ℝ → ℂ) (β T : ℝ) (I : PrimeGapInterval) : ℂ :=
  F (contactAt β T (firstContactAfterLower β T I)) - F I.lower

/-- Reste partiel final : du dernier contact avant `p_{n+1}` à `p_{n+1}`. -/
noncomputable def finalEdgeRemainder (F : ℝ → ℂ) (β T : ℝ) (I : PrimeGapInterval) : ℂ :=
  F I.upper - F (contactAt β T (lastContactBefore β T I.upper))

/-- Somme des cellules entières de la Tour dans l'écart. -/
noncomputable def wholeCellSum (F : ℝ → ℂ) (β T : ℝ) (I : PrimeGapInterval) : ℂ :=
  contactAccumulation F β T (firstContactAfterLower β T I) (wholeCellCount β T I)

/-- L'écart contient au moins un contact de la Tour `(β, T)`. -/
def GapHasContact (β T : ℝ) (I : PrimeGapInterval) : Prop :=
  lastContactBefore β T I.lower < lastContactBefore β T I.upper

theorem firstContact_add_count {β T : ℝ} {I : PrimeGapInterval} (h : GapHasContact β T I) :
    firstContactAfterLower β T I + (wholeCellCount β T I : ℤ) = lastContactBefore β T I.upper := by
  unfold GapHasContact at h
  unfold wholeCellCount firstContactAfterLower
  rw [Int.toNat_of_nonneg (by omega)]
  ring

/-- **Découpage exact** : pour toute `F`, la variation sur l'écart est reste initial + cellules entières + reste final,
dès que l'écart contient un contact. -/
theorem gap_variation_eq_remainders (F : ℝ → ℂ) {β T : ℝ} {I : PrimeGapInterval} (h : GapHasContact β T I) :
    F I.upper - F I.lower =
      initialEdgeRemainder F β T I + wholeCellSum F β T I + finalEdgeRemainder F β T I := by
  have hk := firstContact_add_count h
  have hacc := contact_accumulation_eq_endpoint_difference F β T (firstContactAfterLower β T I)
    (wholeCellCount β T I) I.lower I.upper
  unfold accumulationFrom at hacc
  rw [hk] at hacc
  unfold initialEdgeRemainder wholeCellSum finalEdgeRemainder
  exact hacc.symm

/-- La contribution de cellule brute d'une Tour est lue sur ses propres contacts : restes de bord + cellules entières. -/
theorem rawCellContribution_eq_remainders (ρ : ℂ) {β T : ℝ} {I : PrimeGapInterval} (h : GapHasContact β T I) :
    rawCellContribution ρ I =
      initialEdgeRemainder (towerValue ρ) β T I + wholeCellSum (towerValue ρ) β T I +
        finalEdgeRemainder (towerValue ρ) β T I :=
  gap_variation_eq_remainders (towerValue ρ) h

/-- Les contacts du découpage sont dans l'écart : `p_n < C_{k₀}` et `C_{⌊s(p_{n+1})⌋} ≤ p_{n+1}`. -/
theorem firstContact_gt_lower {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) :
    I.lower < contactAt β T (firstContactAfterLower β T I) :=
  lt_contact_succ hT (by linarith [I.one_lt_lower])

theorem lastContact_le_upper {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) :
    contactAt β T (lastContactBefore β T I.upper) ≤ I.upper :=
  lastContact_le hT (by linarith [I.one_lt_upper])

/-- Le reste final couvre la fraction de cellule `f(p_{n+1})` : `log(p_{n+1}/C_last) = π f/T < π/T`. -/
theorem finalRemainder_span {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) :
    Real.log (I.upper / contactAt β T (lastContactBefore β T I.upper)) =
      Real.pi * cellFraction β T I.upper / T :=
  log_div_lastContact hT (by linarith [I.one_lt_upper])

theorem finalRemainder_span_lt {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) :
    Real.log (I.upper / contactAt β T (lastContactBefore β T I.upper)) < Real.pi / T := by
  rw [finalRemainder_span hT I, div_lt_div_iff_of_pos_right hT]
  have := cellFraction_lt_one β T I.upper
  nlinarith [Real.pi_pos]

/-- Le reste initial couvre la fraction complémentaire `1 − f(p_n)` : `log(C_{k₀}/p_n) = π(1 − f)/T`. -/
theorem initialRemainder_span {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) :
    Real.log (contactAt β T (firstContactAfterLower β T I) / I.lower) =
      Real.pi * (1 - cellFraction β T I.lower) / T := by
  have hl : 0 < I.lower := by linarith [I.one_lt_lower]
  have h1 := log_div_lastContact (β := β) hT hl
  have h2 : Real.log (contactAt β T (lastContactBefore β T I.lower + 1) /
      contactAt β T (lastContactBefore β T I.lower)) = Real.pi / T := by
    rw [contactAt_ratio hT.ne', Real.log_exp]
  unfold firstContactAfterLower
  rw [Real.log_div (contactAt_pos _ _ _).ne' hl.ne'] at *
  rw [Real.log_div hl.ne' (contactAt_pos _ _ _).ne'] at h1
  rw [Real.log_div (contactAt_pos _ _ _).ne' (contactAt_pos _ _ _).ne'] at h2
  have : Real.pi * (1 - cellFraction β T I.lower) / T = Real.pi / T - Real.pi * cellFraction β T I.lower / T := by
    ring
  rw [this]
  linarith

/-- Sans contact dans l'écart, la contribution est un seul reste partiel : `log(p_{n+1}/p_n) < π/T`. -/
theorem gap_span_lt_cell_of_no_contact {β T : ℝ} (hT : 0 < T) {I : PrimeGapInterval}
    (h : ¬ GapHasContact β T I) : Real.log (I.upper / I.lower) < Real.pi / T := by
  unfold GapHasContact at h
  push Not at h
  have hl : 0 < I.lower := by linarith [I.one_lt_lower]
  have hu : 0 < I.upper := by linarith [I.one_lt_upper]
  have hlog : Real.log I.lower ≤ Real.log I.upper := Real.log_le_log hl I.lower_lt_upper.le
  have hmono : stagePosition β T I.lower ≤ stagePosition β T I.upper := by
    unfold stagePosition
    apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    nlinarith
  have hfl : lastContactBefore β T I.lower = lastContactBefore β T I.upper :=
    le_antisymm (Int.floor_mono hmono) h
  have hlt : stagePosition β T I.upper - stagePosition β T I.lower < 1 := by
    have a := Int.floor_le (stagePosition β T I.lower)
    have b := Int.lt_floor_add_one (stagePosition β T I.upper)
    unfold lastContactBefore at hfl
    rw [hfl] at a
    linarith
  unfold stagePosition at hlt
  rw [div_sub_div_same, div_lt_one Real.pi_pos] at hlt
  rw [Real.log_div hu.ne' hl.ne', lt_div_iff₀ hT]
  linarith

/-! ## S2. Fréquence partagée : positions d'étage décalées d'une constante radiale -/

/-- Décalage d'étage entre deux Tours de même fréquence : part radiale seule. -/
noncomputable def stageOffset (β β' T : ℝ) : ℝ :=
  (Real.arctan (T / β) - Real.arctan (T / β')) / Real.pi

theorem stagePosition_same_height (β β' T x : ℝ) :
    stagePosition β' T x = stagePosition β T x + stageOffset β β' T := by
  unfold stagePosition stageOffset
  ring

/-- Le dernier contact de la seconde Tour est celui de la première décalé de `⌊c⌋` ou `⌊c⌋ + 1`. -/
theorem lastContact_same_height_bounds (β β' T x : ℝ) :
    ⌊stageOffset β β' T⌋ ≤ lastContactBefore β' T x - lastContactBefore β T x ∧
      lastContactBefore β' T x - lastContactBefore β T x ≤ ⌊stageOffset β β' T⌋ + 1 := by
  unfold lastContactBefore
  rw [stagePosition_same_height β β' T x]
  constructor
  · have := Int.le_floor_add (stagePosition β T x) (stageOffset β β' T); omega
  · have := Int.le_floor_add_floor (stagePosition β T x) (stageOffset β β' T); omega

/-- **Deux Tours de même fréquence ont, dans tout écart, des nombres de contacts qui diffèrent d'au plus un.** -/
theorem same_height_contact_count_diff (β β' T : ℝ) (I : PrimeGapInterval) :
    -1 ≤ (lastContactBefore β' T I.upper - lastContactBefore β' T I.lower) -
          (lastContactBefore β T I.upper - lastContactBefore β T I.lower) ∧
      (lastContactBefore β' T I.upper - lastContactBefore β' T I.lower) -
          (lastContactBefore β T I.upper - lastContactBefore β T I.lower) ≤ 1 := by
  have hu := lastContact_same_height_bounds β β' T I.upper
  have hl := lastContact_same_height_bounds β β' T I.lower
  omega

/-- Instance paire : la Tour `(β, T)` et son miroir `(1 − β, T)`. -/
theorem mirror_contact_count_diff (β T : ℝ) (I : PrimeGapInterval) :
    -1 ≤ (lastContactBefore (1 - β) T I.upper - lastContactBefore (1 - β) T I.lower) -
          (lastContactBefore β T I.upper - lastContactBefore β T I.lower) ∧
      (lastContactBefore (1 - β) T I.upper - lastContactBefore (1 - β) T I.lower) -
          (lastContactBefore β T I.upper - lastContactBefore β T I.lower) ≤ 1 :=
  same_height_contact_count_diff β (1 - β) T I


/-- **Sur-amplitude du miroir aux contacts** : pour `β < 1/2`, les valeurs aux contacts du miroir `(1 − β, T)`
croissent strictement plus vite, d'un contact au suivant, que celles du zéro `(β, T)`. -/
theorem mirror_contact_ratio_gt {β T : ℝ} (hβ : 0 < β) (hβ2 : β < 1 / 2) (hT : 0 < T) (k : ℤ) :
    |contactRealValue β T (k + 1)| / |contactRealValue β T k| <
      |contactRealValue (1 - β) T (k + 1)| / |contactRealValue (1 - β) T k| := by
  rw [abs_contactRealValue_ratio hβ hT.ne', abs_contactRealValue_ratio (by linarith) hT.ne', Real.exp_lt_exp]
  apply div_lt_div_of_pos_right _ hT
  nlinarith [Real.pi_pos]

/-! ## S3. Série d'écarts : les restes de part et d'autre d'un point de rencontre recomposent une cellule -/

theorem consecutive_lower_eq_upper {I J : PrimeGapInterval} (hIJ : J.rank = I.rank + 1) :
    J.lower = I.upper := by
  unfold PrimeGapInterval.lower PrimeGapInterval.upper
  rw [hIJ]

/-- **Au point de rencontre, les deux restes partiels recomposent exactement une cellule de la Tour.** -/
theorem edge_remainders_complete_cell (F : ℝ → ℂ) (β T : ℝ) {I J : PrimeGapInterval}
    (hIJ : J.rank = I.rank + 1) :
    finalEdgeRemainder F β T I + initialEdgeRemainder F β T J =
      contactVariation F β T (lastContactBefore β T I.upper) := by
  unfold finalEdgeRemainder initialEdgeRemainder firstContactAfterLower contactVariation
  rw [consecutive_lower_eq_upper hIJ]
  ring

/-- Série de `J` écarts consécutifs : la somme des contributions de cellule brutes télescope. -/
theorem rawCellContribution_series (ρ : ℂ) (n J : ℕ) :
    ∑ j ∈ Finset.range J, rawCellContribution ρ ⟨n + j⟩ =
      towerValue ρ (fnPrimeAtRank (n + J)) - towerValue ρ (fnPrimeAtRank n) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    unfold rawCellContribution PrimeGapInterval.upper PrimeGapInterval.lower
    simp only
    rw [show n + (J + 1) = n + J + 1 by ring]
    ring

/-- La série ne lit, pour chaque Tour, que des cellules entières et deux restes de bord (tout découpage). -/
theorem rawCellContribution_series_eq_accumulation (ρ : ℂ) (β T : ℝ) (k₀ : ℤ) (m n J : ℕ) :
    ∑ j ∈ Finset.range J, rawCellContribution ρ ⟨n + j⟩ =
      accumulationFrom (towerValue ρ) β T k₀ m (fnPrimeAtRank n) (fnPrimeAtRank (n + J)) := by
  rw [rawCellContribution_series, contact_accumulation_eq_endpoint_difference]

end RHV6Fresh

#print axioms RHV6Fresh.rawCellContribution_eq_remainders
#print axioms RHV6Fresh.initialRemainder_span
#print axioms RHV6Fresh.finalRemainder_span_lt
#print axioms RHV6Fresh.gap_span_lt_cell_of_no_contact
#print axioms RHV6Fresh.same_height_contact_count_diff
#print axioms RHV6Fresh.mirror_contact_ratio_gt
#print axioms RHV6Fresh.edge_remainders_complete_cell
#print axioms RHV6Fresh.rawCellContribution_series_eq_accumulation
