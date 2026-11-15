/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RemainderExponent

/-!
# Chaîne critique du reste

Ce module expose uniquement les raccords démontrés. La borne
`remainderExponent ≤ 1/2` reste un paramètre explicite : aucune déclaration
de ce fichier ne la dérive des premiers.
-/

namespace RHV6Fresh

open RHV3Lean

theorem critical_bound_implies_RH
    (hCritical : remainderExponent ≤ (1 / 2 : ℝ)) : RiemannHypothesis := by
  exact (riemannHypothesis_iff_remainderExponent_eq_half).mpr
    (le_antisymm hCritical remainderExponent_mem_bracket.1)

theorem sqrt_bound_implies_RH
    (hSqrt : ∃ C : ℝ, ∀ x : ℝ, 1 < x →
      ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 : ℝ)) : RiemannHypothesis := by
  obtain ⟨C, hC⟩ := hSqrt
  exact critical_bound_implies_RH
    (csInf_le remainderExponents_bddBelow ⟨C, hC⟩)

theorem epsilon_family_implies_RH
    (hAllEps : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 < x →
      ‖smoothedRemainder x‖ ≤ C * x ^ ((1 / 2 : ℝ) + ε)) : RiemannHypothesis :=
  riemannHypothesis_iff_remainder_growth_all_eps.mpr hAllEps

theorem critical_bound_makes_every_pair_onLine
    (hCritical : remainderExponent ≤ (1 / 2 : ℝ)) (z : TrueZero) :
    rZeroRadialPosition z.1 = 1 / 2 := by
  have hPair := mirror_pair_exponent_le_remainderExponent z
  have hup : rZeroRadialPosition z.1 ≤ 1 / 2 :=
    (le_max_left _ _).trans (hPair.trans hCritical)
  have hlo : 1 / 2 ≤ rZeroRadialPosition z.1 := by
    have hmirror : 1 - rZeroRadialPosition z.1 ≤ 1 / 2 :=
      (le_max_right _ _).trans (hPair.trans hCritical)
    linarith
  exact le_antisymm hup hlo

theorem off_pair_forces_strictly_supercritical
    (z : TrueZero) (hOff : rZeroRadialPosition z.1 ≠ 1 / 2) :
    (1 / 2 : ℝ) < remainderExponent := by
  have hPair := mirror_pair_exponent_le_remainderExponent z
  have hMax : (1 / 2 : ℝ) <
      max (rZeroRadialPosition z.1) (1 - rZeroRadialPosition z.1) := by
    rcases lt_or_gt_of_ne hOff with hlt | hgt
    · exact (by linarith : (1 / 2 : ℝ) < 1 - rZeroRadialPosition z.1) |>.trans_le
        (le_max_right _ _)
    · exact hgt.trans_le (le_max_left _ _)
  exact hMax.trans_le hPair

#print axioms critical_bound_implies_RH
#print axioms sqrt_bound_implies_RH
#print axioms epsilon_family_implies_RH
#print axioms critical_bound_makes_every_pair_onLine
#print axioms off_pair_forces_strictly_supercritical

end RHV6Fresh
