/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Tower.TrueTower

/-!
# RHV6Fresh — incidences indexées du mouvement

Les paires `(contactMinusAt z k, contactPlusAt z k) = (C_k, C_{k+1})` sont les
valeurs des formules tangentielles à la coordonnée `k` (maître mathématique §4).
Ce sont des contrôles de formule ; aucune d'elles n'est appelée état propre
(maître Lean §5.4, §22-A) ni contact de la Tour, qui n'en a que deux (§26), et
aucun premier n'entre ici.
-/

namespace RHV6Fresh

open RHV3Lean

noncomputable def contactMinusAt (z : TrueZero) (k : ℤ) : ℝ :=
  (towerMotionOf z).incidence k

noncomputable def contactPlusAt (z : TrueZero) (k : ℤ) : ℝ :=
  (towerMotionOf z).incidence (k + 1)

theorem contactAt_consecutive_logWidth (z : TrueZero) (k : ℤ) :
    Real.log (contactPlusAt z k) - Real.log (contactMinusAt z k) =
      Real.pi / rZeroHeight z.1 :=
  towerMotion_consecutive_width z k

theorem contactAt_ordered (z : TrueZero) (k : ℤ) :
    contactMinusAt z k < contactPlusAt z k :=
  towerMotion_incidence_strictOrder z (by omega)

theorem contactMinusAt_positive (z : TrueZero) (k : ℤ) :
    0 < contactMinusAt z k :=
  towerMotion_incidence_positive z k

theorem contactPlusAt_positive (z : TrueZero) (k : ℤ) :
    0 < contactPlusAt z k :=
  towerMotion_incidence_positive z (k + 1)

/-- TAN-Q at the left endpoint of any consecutive tower cell.  This is an
inverse certificate for a supplied analytic cell; it does not select one. -/
theorem contactAt_tangent_minus (z : TrueZero) (k : ℤ) :
    Real.tan (rZeroHeight z.1 * Real.log (contactMinusAt z k)) =
      rZeroHeight z.1 / rZeroRadialPosition z.1 := by
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  unfold contactMinusAt
  rw [(towerMotionOf z).incidence_eq, Real.log_exp,
    (towerMotionOf z).logIncidence_eq, towerMotion_phase]
  have harg :
      rZeroHeight z.1 *
          ((Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) +
              (k : ℝ) * Real.pi) / rZeroHeight z.1) =
        Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) +
          (k : ℝ) * Real.pi := by
    field_simp
  rw [harg, (Real.tan_periodic.int_mul k) _, Real.tan_arctan]

/-- TAN-Q at the right endpoint.  Consecutive endpoints differ by one period,
so they certify the same source ratio.  No endpoint is privileged here. -/
theorem contactAt_tangent_plus (z : TrueZero) (k : ℤ) :
    Real.tan (rZeroHeight z.1 * Real.log (contactPlusAt z k)) =
      rZeroHeight z.1 / rZeroRadialPosition z.1 := by
  unfold contactPlusAt
  rw [(towerMotionOf z).incidence_eq, Real.log_exp,
    (towerMotionOf z).logIncidence_eq, towerMotion_phase]
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  have harg :
      rZeroHeight z.1 *
          ((Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) +
              ((k + 1 : ℤ) : ℝ) * Real.pi) / rZeroHeight z.1) =
        Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) +
          ((k + 1 : ℤ) : ℝ) * Real.pi := by
    field_simp
  rw [harg, (Real.tan_periodic.int_mul (k + 1)) _, Real.tan_arctan]

/-- A tower state at an explicit analytic coordinate.  No prime enters here. -/
noncomputable def towerStateAt (z : TrueZero) (k : ℤ) :
    TTrueHarmonicTowerState z where
  contactMinus := contactMinusAt z k
  contactPlus := contactPlusAt z k
  contactMinus_pos := contactMinusAt_positive z k
  contactPlus_pos := contactPlusAt_positive z k
  ordered := contactAt_ordered z k
  consecutive_width := contactAt_consecutive_logWidth z k
  tangent_law := by
    have hBeta : rZeroRadialPosition z.1 ≠ 0 :=
      ne_of_gt (thm_zeroRadialPosition_positive z.1)
    rw [contactAt_tangent_minus z k]
    field_simp

end RHV6Fresh
