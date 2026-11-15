/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TwoClocks
import RHV6Fresh.Terminal.ExplicitFormulaLink
import RHV6Fresh.Direct.PairTowers
import RHV6Fresh.Terminal.MirrorEventCollision

/-!
# RHV6Fresh — le miroir OFF comme second état de la MÊME fréquence (T1–T5, (30), (31))

Plan TDD (auteur, 2026-09-28) : `experiments/PLAN_TDD_MIROIR_FREQUENCE_20260928.md`, suite directe
de `Terminal/TwoClocks.lean` (commit `13df52ff`).  Aucune nouvelle prémisse : ce fichier compose
`pi_mul_towerPosition` (`Terminal/ExplicitFormulaLink.lean`), `TowerPrimeGapSpan` (base,
`TowerPrimeGapSpan.lean`) et le miroir (`Direct/MirrorCount.lean`, `Direct/PairTowers.lean`).

**Point d'honnêteté imposé (auteur)** : `n(z*) = n(z) + 1` ne se prouve QUE sous consécutivité
stricte (`mirror_sourceIndex_of_consecutive`, déjà compilé) ; la forme sans hypothèse est
`n(z*) ≠ n(z)` (et `n(z) < n(z*)` sous `β < 1/2`, `sourceIndex_lt_mirror`).  Ni `F_{ρ*} = −F_ρ`, ni
« quartet ⟹ contribution nulle » (faux, `pair_term_real`/`mirror_amplitude_exponent_dominates`), ni
`Δn = 1 ⟹ Δfréquence ≠ 0` (le maillon manquant, ⟺ RH via `clock_agree_iff_riemannHypothesis`) ne
sont formalisés ici.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## (30) — la portée de Tour EST l'accroissement de phase sur une arête première -/

/-- **La portée `TowerPrimeGapSpan z n` est exactement l'accroissement de phase `π · ΔΘ` du terme
explicite de `z` entre les deux premiers de la place `n`.**  La portée de Tour et l'accroissement de
phase sont le MÊME nombre, sans approximation. -/
theorem phase_increment_eq_pi_span (z : TrueZero) (n : ℕ) :
    Real.pi * towerPosition z (fnPrimeSuccessor n : ℝ) -
        Real.pi * towerPosition z (fnPrimeAtRank n : ℝ) =
      Real.pi * TowerPrimeGapSpan z n := by
  have hpos1 : (0 : ℝ) < (fnPrimeAtRank n : ℝ) := by exact_mod_cast thm_primeAtRank_pos n
  have hpos2 : (0 : ℝ) < (fnPrimeSuccessor n : ℝ) := by
    unfold fnPrimeSuccessor; exact_mod_cast thm_primeAtRank_pos (n + 1)
  unfold TowerPrimeGapSpan rPrimeGapLogRatio rTowerHeight
  rw [pi_mul_towerPosition, pi_mul_towerPosition, Real.log_div hpos2.ne' hpos1.ne']
  field_simp [Real.pi_pos.ne']
  ring

/-! ## T1 — même progression de phase pour `z` et son miroir, sur tout intervalle -/

/-- **Le miroir progresse en phase EXACTEMENT comme `z` sur tout intervalle `[q₁, q₂]`** : les
deux Tours partagent la même hauteur (`mirrorMember_ordinate`), donc le même terme
`T · (log q₂ − log q₁)` — le déphasage constant (T2) s'annule dans la différence. -/
theorem mirror_phase_increment_eq (z : TrueZero) (q₁ q₂ : ℝ) :
    Real.pi * towerPosition (mirrorMember z) q₂ - Real.pi * towerPosition (mirrorMember z) q₁ =
      Real.pi * towerPosition z q₂ - Real.pi * towerPosition z q₁ := by
  rw [pi_mul_towerPosition, pi_mul_towerPosition, pi_mul_towerPosition, pi_mul_towerPosition,
    mirrorMember_ordinate]
  ring

/-! ## T2 — le déphasage miroir est une constante indépendante de `q` -/

/-- **Le déphasage entre le terme de `z` et celui de son miroir, à `q` fixé, ne dépend que des deux
phases tangentielles** — pas de `q` : c'est la même constante à toute adresse. -/
theorem mirror_phase_offset_const (z : TrueZero) (q : ℝ) :
    Real.pi * towerPosition (mirrorMember z) q - Real.pi * towerPosition z q =
      (towerMotionOf z).phase - (towerMotionOf (mirrorMember z)).phase := by
  rw [pi_mul_towerPosition, pi_mul_towerPosition, mirrorMember_ordinate]
  ring

/-! ## T3 — même portée sur toute arête première -/

/-- **Le miroir lit exactement la même portée première `S_n` que `z`, sur tout rang `n`.**
Conséquence directe de `thm_towerPrimeGapSpan_eq_iff_height_eq` : la portée est une fonction de la
seule hauteur, et le miroir conserve la hauteur. -/
theorem mirror_span_eq (z : TrueZero) (n : ℕ) :
    TowerPrimeGapSpan (mirrorMember z) n = TowerPrimeGapSpan z n := by
  apply (thm_towerPrimeGapSpan_eq_iff_height_eq z (mirrorMember z) n).mpr
  unfold rTowerHeight
  exact mirrorMember_ordinate z

/-! ## T4 — l'horloge des membres avance de `z` à `z*` (deux formes, honnêtes) -/

/-- **Forme inconditionnelle, sous `β < 1/2`** : réexposition de `sourceIndex_lt_mirror`. -/
theorem member_index_lt_of_lowerSide {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    nZeroSourceIndex z.1 < nZeroSourceIndex (mirrorMember z).1 :=
  sourceIndex_lt_mirror hβ

/-- **Instanciation sur tout zéro hors ligne** (`off_lowerSide`) : un membre de la paire — celui de
côté bas, `z` ou son miroir — voit son horloge des membres avancer strictement au sien. -/
theorem off_member_index_lt_mirror {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    nZeroSourceIndex z.1 < nZeroSourceIndex (mirrorMember z).1 ∨
      nZeroSourceIndex (mirrorMember z).1 < nZeroSourceIndex (mirrorMember (mirrorMember z)).1 := by
  rcases off_lowerSide hOff with h | h
  · exact Or.inl (sourceIndex_lt_mirror h)
  · exact Or.inr (sourceIndex_lt_mirror h)

/-- **Forme `+1`, SOUS consécutivité stricte SEULEMENT** (réexposition de
`mirror_sourceIndex_of_consecutive`).  NE PAS écrire cette égalité sans `hab` : elle est fausse en
général — d'autres zéros de même hauteur peuvent s'intercaler entre `z` et son miroir. -/
theorem member_index_succ_of_consecutive {z : TrueZero}
    (hab : PZeroMembersConsecutive z.1 (mirrorMember z).1) :
    nZeroSourceIndex (mirrorMember z).1 = nZeroSourceIndex z.1 + 1 :=
  mirror_sourceIndex_of_consecutive hab

/-! ## T5 — l'horloge des hauteurs ne bouge pas -/

/-- **L'horloge des hauteurs du miroir est identique à celle de `z`.**  Réexposition de
`mirror_sameHeightIndex` (`Terminal/MirrorEventCollision.lean:60`), déjà compilé : pas de
duplication de preuve. -/
theorem mirror_heightEventIndex_eq (z : TrueZero) :
    nZeroHeightEventIndex (tZeroHeightEvent (mirrorMember z)) =
      nZeroHeightEventIndex (tZeroHeightEvent z) :=
  mirror_sameHeightIndex z

/-! ## (31) — le théorème de synthèse, sur la paire miroir OFF -/

/-- **Le miroir OFF est un second état de la MÊME fréquence** : même hauteur (`ΔT = 0`), même
événement de hauteur (`Δh = 0`), même portée première sur tout rang (`ΔS_n = 0` `∀n`), même
progression de phase sur tout intervalle (`ΔΘ` identique) — et pourtant une position radiale
distincte (`Δβ ≠ 0`) et un index de membre distinct (`Δn ≠ 0`) : la signature d'un zéro hors ligne
est tout entière dans `(Δβ, Δn)`, jamais dans la fréquence, la hauteur ou la portée première. -/
theorem off_mirror_same_frequency {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    rZeroHeight (mirrorMember z).1 = rZeroHeight z.1 ∧
    nZeroHeightEventIndex (tZeroHeightEvent (mirrorMember z)) =
      nZeroHeightEventIndex (tZeroHeightEvent z) ∧
    (∀ n : ℕ, TowerPrimeGapSpan (mirrorMember z) n = TowerPrimeGapSpan z n) ∧
    (∀ q₁ q₂ : ℝ, Real.pi * towerPosition (mirrorMember z) q₂ -
        Real.pi * towerPosition (mirrorMember z) q₁ =
      Real.pi * towerPosition z q₂ - Real.pi * towerPosition z q₁) ∧
    rZeroRadialPosition (mirrorMember z).1 ≠ rZeroRadialPosition z.1 ∧
    nZeroSourceIndex (mirrorMember z).1 ≠ nZeroSourceIndex z.1 := by
  refine ⟨mirrorMember_ordinate z, mirror_heightEventIndex_eq z, mirror_span_eq z,
    fun q₁ q₂ => mirror_phase_increment_eq z q₁ q₂, ?_, ?_⟩
  · rw [mirrorMember_radial]
    intro h
    exact hOff (by linarith)
  · intro h
    have hMem : mirrorMember z = z := thm_zeroSourceIndex_injective h
    exact thm_offCriticalLine_mirror_distinct hOff (congrArg Subtype.val hMem)

/-- **Version forte, sous consécutivité stricte** : ajoute `n(z*) = n(z) + 1` (au lieu du seul
`≠`) et `Occ(z*) = p_min(z)` — la progression obligatoire de la chaîne arithmétique déjà compilée
(`expectedMinimum_eq_mirror_occurrence_of_consecutive`). -/
theorem off_mirror_same_frequency_of_consecutive {z : TrueZero} (hOff : PIsOffCriticalLine z.1)
    (hab : PZeroMembersConsecutive z.1 (mirrorMember z).1) :
    (rZeroHeight (mirrorMember z).1 = rZeroHeight z.1 ∧
      nZeroHeightEventIndex (tZeroHeightEvent (mirrorMember z)) =
        nZeroHeightEventIndex (tZeroHeightEvent z) ∧
      (∀ n : ℕ, TowerPrimeGapSpan (mirrorMember z) n = TowerPrimeGapSpan z n) ∧
      (∀ q₁ q₂ : ℝ, Real.pi * towerPosition (mirrorMember z) q₂ -
          Real.pi * towerPosition (mirrorMember z) q₁ =
        Real.pi * towerPosition z q₂ - Real.pi * towerPosition z q₁) ∧
      rZeroRadialPosition (mirrorMember z).1 ≠ rZeroRadialPosition z.1 ∧
      nZeroSourceIndex (mirrorMember z).1 ≠ nZeroSourceIndex z.1) ∧
    nZeroSourceIndex (mirrorMember z).1 = nZeroSourceIndex z.1 + 1 ∧
    occurrence (mirrorMember z) = expectedMinimumPrime z :=
  ⟨off_mirror_same_frequency hOff, mirror_sourceIndex_of_consecutive hab,
    (expectedMinimum_eq_mirror_occurrence_of_consecutive hab).symm⟩

/-! ## Contraste sur la ligne : le second état n'existe pas -/

/-- **Sur la ligne critique, le miroir EST le zéro** : toutes les différences ci-dessus sont
triviales (`Δβ = 0`, `Δn = 0`) — le « second état de la même fréquence » n'existe pas sur la droite,
signature exclusive de (31) hors ligne. -/
theorem onLine_mirror_trivial {z : TrueZero} (hβ : rZeroRadialPosition z.1 = 1 / 2) :
    mirrorMember z = z ∧
    rZeroHeight (mirrorMember z).1 = rZeroHeight z.1 ∧
    nZeroHeightEventIndex (tZeroHeightEvent (mirrorMember z)) =
      nZeroHeightEventIndex (tZeroHeightEvent z) ∧
    (∀ n : ℕ, TowerPrimeGapSpan (mirrorMember z) n = TowerPrimeGapSpan z n) ∧
    rZeroRadialPosition (mirrorMember z).1 = rZeroRadialPosition z.1 ∧
    nZeroSourceIndex (mirrorMember z).1 = nZeroSourceIndex z.1 := by
  have hEq : mirrorMember z = z := mirrorMember_eq_self_of_onLine hβ
  refine ⟨hEq, mirrorMember_ordinate z, mirror_heightEventIndex_eq z, mirror_span_eq z, ?_, ?_⟩
  · rw [hEq]
  · rw [hEq]

/-!
## Verdict (ce que ce fichier ne prétend pas)

`off_mirror_same_frequency` matérialise, sur un seul énoncé, que le miroir hors ligne partage TOUT
ce qui est fonction de la seule hauteur (fréquence, portée, événement de hauteur) avec `z`, et ne
diffère que sur `(β, n)`.  Aucune contradiction n'en sort : `Δn ≠ 0` est établi sans aucun lien
démontré à `Δfréquence`, exactement la question que `clock_agree_iff_riemannHypothesis` pose déjà.
-/

#print axioms off_mirror_same_frequency
#print axioms phase_increment_eq_pi_span

end RHV6Fresh
