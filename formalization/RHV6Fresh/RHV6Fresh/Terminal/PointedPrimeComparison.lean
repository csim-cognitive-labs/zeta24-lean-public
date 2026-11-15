/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.EntryPositionArrow
import RHV6Fresh.Grammar.Mod6Rigidity

/-!
# RHV6Fresh — premiers pointés : 300 ON contre 150 paires OFF, protocole de E147 (auteur, 2026-10-01)

Demande de l'auteur : noter les premiers pointés par les contacts sur 300 membres en ligne, puis sur
150 paires hors ligne placées aux mêmes hauteurs, une sur deux ; comparer les premiers pointés, la
transition modulo 6 et l'alternance de la grammaire entre deux zéros.

Le monde OFF de l'expérience est fait de formules évaluées, pas de zéros : ce fichier écrit donc la
lecture d'une Tour comme fonction des paramètres `(β, T)` (`pointedPosition`), et la grammaire sur les
membres réels comme fonction du rang seul.

* **Grammaire, rang seul** (§1) : deux membres de même rang pointent la même occurrence, le même
  minimum attendu, la même classe d'écart modulo 6, quelles que soient leurs hauteurs et leurs
  positions radiales (`pointed_primes_rank_only`, `pointed_gapClass6_rank_only`).
* **Position d'un premier dans une Tour** (§2) : `Π(β, T, q) = (T log q − arctan(T/β))/π` ; en ligne,
  c'est la position de ligne (`pointedPosition_half`) ; un membre réel la lit à ses paramètres
  (`towerPosition_eq_pointedPosition`).
* **Trois comparaisons exactes** (§3) : même Tour, deux premiers : écart `T log(q'/q)/π`, hauteur seule
  (`pointedPosition_step`) ; même hauteur, deux positions radiales : translation `Δφ/π` indépendante
  du premier (`pointedPosition_sameHeight_shift`) ; même premier, deux Tours : part de hauteur
  `ΔT·log q/π` plus part de phase (`pointedPosition_samePrime`).
* **Le pas d'une paire contre le pas en ligne** (§4) : dans la paire `(β, T) → (1 − β, T)` le pas
  grammatical `p → p'` avance la position de `T log(p'/p)/π` plus la rotation de phase, sans part de
  hauteur (`pair_step_position`) ; entre deux membres en ligne il s'y ajoute `ΔT·log p'/π`
  (`line_step_position`). Les deux pas portent le même événement premier.

Borne : tout ce qui est écrit ici est une lecture ; la séparation observée dans E147 vient du poids et
du comptage, qui ne figurent pas dans ce pointage. Aucune prémisse, aucun `sorry`, aucun axiome.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. La grammaire entre deux zéros est une fonction du rang seul -/

/-- **Deux membres de même rang pointent les mêmes premiers**, quelles que soient leurs hauteurs et leurs
positions radiales. -/
theorem pointed_primes_rank_only (z w : TrueZero) (h : nZeroSourceIndex z.1 = nZeroSourceIndex w.1) :
    occurrence z = occurrence w ∧ expectedMinimumPrime z = expectedMinimumPrime w := by
  refine ⟨?_, ?_⟩
  · rw [occurrence_eq_primeAtRank, occurrence_eq_primeAtRank, h]
  · rw [expectedMinimum_eq_succ_occurrence, expectedMinimum_eq_succ_occurrence, h]

/-- **La transition modulo 6 d'un membre est une fonction de son rang seul.** -/
theorem pointed_gapClass6_rank_only (z w : TrueZero)
    (h : nZeroSourceIndex z.1 = nZeroSourceIndex w.1) :
    gapClass6 (occurrence z) (expectedMinimumPrime z) =
        gapClass6 (occurrence w) (expectedMinimumPrime w) ∧
      state6 (occurrence z) = state6 (occurrence w) ∧
        state6 (expectedMinimumPrime z) = state6 (expectedMinimumPrime w) := by
  obtain ⟨h1, h2⟩ := pointed_primes_rank_only z w h
  exact ⟨by rw [h1, h2], by rw [h1], by rw [h2]⟩

/-! ## 2. La position d'un premier dans une Tour de paramètres `(β, T)` -/

/-- Position, en cellules, du réel `q` dans la Tour de paramètres `(β, T)`. -/
noncomputable def pointedPosition (β T q : ℝ) : ℝ :=
  (T * Real.log q - Real.arctan (T / β)) / Real.pi

/-- En ligne, c'est la position de ligne. -/
theorem pointedPosition_half (T q : ℝ) : pointedPosition (1 / 2) T q = linePosition T q := rfl

/-- Un membre réel lit la position à ses propres paramètres. -/
theorem towerPosition_eq_pointedPosition (z : TrueZero) (q : ℝ) :
    towerPosition z q = pointedPosition (rZeroRadialPosition z.1) (rZeroHeight z.1) q := by
  unfold towerPosition pointedPosition
  rw [towerMotion_phase]

/-! ## 3. Trois comparaisons exactes -/

/-- **Même Tour, deux premiers** : l'écart ne dépend que de la hauteur. -/
theorem pointedPosition_step (β T q q' : ℝ) (hq : 0 < q) (hq' : 0 < q') :
    pointedPosition β T q' - pointedPosition β T q = T * Real.log (q' / q) / Real.pi := by
  unfold pointedPosition
  rw [Real.log_div hq'.ne' hq.ne']
  ring

/-- **Même hauteur, deux positions radiales** : translation rigide, la même pour tout premier. -/
theorem pointedPosition_sameHeight_shift (β β' T q : ℝ) :
    pointedPosition β T q - pointedPosition β' T q =
      (Real.arctan (T / β') - Real.arctan (T / β)) / Real.pi := by
  unfold pointedPosition
  ring

/-- **Même premier, deux Tours** : part de hauteur plus part de phase. -/
theorem pointedPosition_samePrime (β β' T T' q : ℝ) :
    pointedPosition β' T' q - pointedPosition β T q =
      ((T' - T) * Real.log q - (Real.arctan (T' / β') - Real.arctan (T / β))) / Real.pi := by
  unfold pointedPosition
  ring

/-! ## 4. Le pas d'une paire contre le pas en ligne -/

/-- **Pas grammatical dans une paire de même hauteur** `(β, T) → (1 − β, T)` : `p` pointé par le premier
membre, `p'` par le second. Aucune part de hauteur. -/
theorem pair_step_position (β T p p' : ℝ) (hp : 0 < p) (hp' : 0 < p') :
    pointedPosition (1 - β) T p' - pointedPosition β T p =
      (T * Real.log (p' / p) + (Real.arctan (T / β) - Real.arctan (T / (1 - β)))) / Real.pi := by
  unfold pointedPosition
  rw [Real.log_div hp'.ne' hp.ne']
  ring

/-- **Pas grammatical entre deux membres en ligne** `(1/2, T) → (1/2, T')` : la part de hauteur
`(T' − T)·log p'` s'ajoute au même pas grammatical. -/
theorem line_step_position (T T' p p' : ℝ) (hp : 0 < p) (hp' : 0 < p') :
    linePosition T' p' - linePosition T p =
      ((T' - T) * Real.log p' + T * Real.log (p' / p) - (linePhase T' - linePhase T)) / Real.pi := by
  unfold linePosition
  rw [Real.log_div hp'.ne' hp.ne']
  ring

#print axioms pointed_primes_rank_only
#print axioms pointed_gapClass6_rank_only
#print axioms pointedPosition_half
#print axioms towerPosition_eq_pointedPosition
#print axioms pointedPosition_step
#print axioms pointedPosition_sameHeight_shift
#print axioms pointedPosition_samePrime
#print axioms pair_step_position
#print axioms line_step_position

end RHV6Fresh
