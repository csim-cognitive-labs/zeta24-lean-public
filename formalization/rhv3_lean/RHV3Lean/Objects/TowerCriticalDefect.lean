/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TrueTowerState

/-!
# RHV3Lean — le défaut critique d'un état propre, et son annulation en `beta=1/2`

    TRACE_ID              : RHV3-TOWER-CRITICAL-DEFECT
    SEMANTIC_OBJECT       : O3/O4 — le défaut critique d'un état propre de Tour.
    SEMANTIC_STATEMENT    : un état propre porte, par ses deux seules lois
                            exactes (largeur consécutive, loi tangentielle),
                            une quantité algébrique qui s'annule exactement
                            quand la position radiale du membre vaut `1/2`.
                            Cette quantité ne recoit ni premier, ni rang, ni
                            hypothèse de Riemann : elle est une relecture pure
                            des deux lois déjà prouvées de l'état propre.
    MATHEMATICAL_STATEMENT: pour un état propre `S` de largeur logarithmique
                            `delta = log C+ - log C-`, le défaut critique est
                            `delta * tan(pi * log C- / delta) - 2*pi`.  Comme
                            `delta = pi/T` (largeur consécutive) et
                            `beta * tan(T*log C-) = T` (loi tangentielle),
                            ce défaut vaut exactement `pi*(1/beta - 2)`, donc
                            s'annule exactement quand `beta = 1/2`.
    MATHEMATICAL_PARENT   : O3 — la Tour harmonique ; O4 — les contacts et la
                            cellule (`TrueTowerState.lean`).
    PROOF_STRATEGY        : substituer `delta` par `pi/T` dans l'argument de la
                            tangente (`pi * log C- / delta = T * log C-`), puis
                            utiliser la loi tangentielle pour remplacer
                            `tan(T*log C-)` par `T/beta`.  Aucune borne, aucune
                            approximation : deux réécritures exactes.
    REQUIRED_LEMMAS       : TTrueHarmonicTowerState.consecutive_width,
                            TTrueHarmonicTowerState.tangent_law,
                            thm_rZeroHeight (T != 0), thm_zeroRadialPosition
                            (beta != 0)
    WHY_EACH_LEMMA_EXISTS : les deux premiers sont les deux lois exactes de
                            l'état propre ; les deux derniers permettent les
                            deux divisions (par `T` puis par `beta`) sans
                            perte.
    LEAN_DEFINITION       : rTowerCriticalDefect
    LEAN_THEOREM          : thm_towerCriticalDefect_eq_radial,
                            thm_towerCriticalDefect_eq_zero_iff
    SAME_MEMBER_CHECK     : le défaut est une fonction du seul état propre `S`
                            reçu, jamais recalculé pour un autre membre.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre dans ce module.
    FORBIDDEN_PREMISES    : premier, rang, comptage, hypothèse de Riemann,
                            hypothèse de croissance ; toute adresse choisie.
    NEXT_CONSUMER         : `TowerTransition.lean` (passage à deux membres),
                            puis la signature OFF de la paire miroir.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

open TTrueHarmonicTowerState

variable {z : TUpperNonTrivialZetaZero}

/-! ## 1. Le défaut critique -/

/-- **Le défaut critique d'un état propre.**  Relecture pure des deux lois de
l'état : aucun premier, aucun rang, aucune hypothèse de croissance. -/
noncomputable def rTowerCriticalDefect (S : TTrueHarmonicTowerState z) : ℝ :=
  (Real.log S.contactPlus - Real.log S.contactMinus) *
      Real.tan (Real.pi * Real.log S.contactMinus /
        (Real.log S.contactPlus - Real.log S.contactMinus)) -
    2 * Real.pi

/-! ## 2. Le défaut critique EST la position radiale, à une remise à l'échelle
près -/

/-- **Le défaut critique vaut exactement `pi*(1/beta - 2)`.**  Conséquence
directe des deux lois exactes de l'état propre : aucune approximation. -/
theorem thm_towerCriticalDefect_eq_radial (S : TTrueHarmonicTowerState z) :
    rTowerCriticalDefect S = Real.pi * (1 / rZeroRadialPosition z.1 - 2) := by
  have hHeight : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  have hRadial : rZeroRadialPosition z.1 ≠ 0 :=
    ne_of_gt (thm_zeroRadialPosition_positive z.1)
  have hDelta : Real.log S.contactPlus - Real.log S.contactMinus =
      Real.pi / rZeroHeight z.1 := S.consecutive_width
  have hDeltaNe : Real.log S.contactPlus - Real.log S.contactMinus ≠ 0 := by
    rw [hDelta]; exact div_ne_zero (ne_of_gt Real.pi_pos) hHeight
  have hArg :
      Real.pi * Real.log S.contactMinus /
          (Real.log S.contactPlus - Real.log S.contactMinus) =
        rZeroHeight z.1 * Real.log S.contactMinus := by
    rw [hDelta]
    field_simp
  have hTan :
      Real.tan (rZeroHeight z.1 * Real.log S.contactMinus) =
        rZeroHeight z.1 / rZeroRadialPosition z.1 := by
    have hLaw := S.tangent_law
    exact (eq_div_iff hRadial).2 (by linarith [hLaw])
  unfold rTowerCriticalDefect
  rw [hArg, hTan, hDelta]
  field_simp

/-- **Le défaut critique s'annule exactement quand `beta = 1/2`.**  Aucune
hypothèse de Riemann n'est supposée : ceci est une équivalence algébrique pure,
jamais une conclusion sur le zéro lui-même. -/
theorem thm_towerCriticalDefect_eq_zero_iff (S : TTrueHarmonicTowerState z) :
    rTowerCriticalDefect S = 0 ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  rw [thm_towerCriticalDefect_eq_radial]
  have hRadial : rZeroRadialPosition z.1 ≠ 0 :=
    ne_of_gt (thm_zeroRadialPosition_positive z.1)
  constructor
  · intro hEq
    have hInv : 1 / rZeroRadialPosition z.1 = 2 := by
      have hPi : Real.pi ≠ 0 := Real.pi_ne_zero
      have := mul_eq_zero.mp hEq
      rcases this with h | h
      · exact absurd h hPi
      · linarith
    field_simp at hInv
    linarith
  · intro hEq
    rw [hEq]
    norm_num

/-! Surface audit. -/

#check rTowerCriticalDefect
#check thm_towerCriticalDefect_eq_radial
#check thm_towerCriticalDefect_eq_zero_iff

end RHV3Lean
