/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RayCapture
import RHV6Fresh.Terminal.GrammarForcesStop
import RHV6Fresh.Terminal.SuccessionInvariants

/-!
# RHV6Fresh — lecture énergétique orientée au raccord partagé (2026-09-29)

Proposition de l'auteur : remplacer « les rayons se superposent » (déjà `β = 1/2`) par une prémisse
portant sur ce que la cellule authentique lit : au raccord partagé `M = p_min(e) = Occ(l)` (fixé par
`M^Z = M`, rang), la lecture énergétique de `M` par la Tour LATER n'excède pas celle par la Tour
EARLIER : `q^{β_l}/‖ρ_l‖ ≤ q^{β_e}/‖ρ_e‖` en `q = M`.

Verdict du compilateur (sondes `experiments/e125_compiler_local_reading/`, P9 et P10) :

* L1 — mode A (`ΔT > 0`, `Δβ = 0`) : la prémisse est un THÉORÈME (`localReading_modeA`).
* L2 — mode C (même hauteur, le passage nul) : dès `T ≥ 2`, la prémisse est FAUSSE
  (`localReading_fails_modeC`) ; elle ne peut donc pas être dérivée, elle ne peut qu'exclure.
* L3 — mode B (mixte) : but résiduel `(β_l − β_e)·log M ≤ log‖ρ_l‖ − log‖ρ_e‖`, aucun théorème ne
  l'oriente (P9).
* L4 — RH ⟹ prémisse (`localReading_of_riemannHypothesis`).
* L5 — prémisse ⟹ RH, à UNE condition près, que P10 isole comme seul but restant :
  `2 ≤ T` pour un zéro hors ligne. C'est un fait classique vrai, sans rapport avec
  RH (le premier zéro est à `T ≈ 14,13`), mais absent de la base et de Mathlib.
  (`riemannHypothesis_of_localReading`).

La prémisse locale était donc, à cette condition près, exactement RH. Elle est retirée, avec sa
condition annexe (décision de l'auteur, 2026-09-30) : la prémisse unique est `PNoRegimeChange`
(`Terminal/NoRegimeChange.lean`), sans aucune condition de hauteur.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **L1** : en mode A (vertical pur), la lecture orientée est un théorème, pour tout `q > 0`, a
fortiori au raccord `M`. -/
theorem localReading_modeA (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hT : rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember)
    (hβ : rZeroRadialPosition p.zEarlierMember = rZeroRadialPosition p.zLaterMember) :
    ‖zeroTerm (⟨p.zLaterMember, hL⟩ : TrueZero) (occurrence ⟨p.zLaterMember, hL⟩ : ℝ)‖ ≤
      ‖zeroTerm (⟨p.zEarlierMember, hE⟩ : TrueZero) (occurrence ⟨p.zLaterMember, hL⟩ : ℝ)‖ := by
  have hM0 : (0 : ℝ) < (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) := by
    exact_mod_cast occurrence_pos ⟨p.zLaterMember, hL⟩
  exact (amplitude_lt_of_height_lt ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hβ hT hM0).le

/-- **L2** : en mode C (même hauteur, `β_e < β_l`), à `T ≥ 2`, la lecture orientée est FAUSSE au
raccord : la Tour LATER lit strictement plus. -/
theorem localReading_fails_modeC (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hSame : rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember)
    (hβ : rZeroRadialPosition p.zEarlierMember < rZeroRadialPosition p.zLaterMember)
    (hT2 : 2 ≤ rZeroHeight p.zEarlierMember) :
    ‖zeroTerm (⟨p.zEarlierMember, hE⟩ : TrueZero) (occurrence ⟨p.zLaterMember, hL⟩ : ℝ)‖ <
      ‖zeroTerm (⟨p.zLaterMember, hL⟩ : TrueZero) (occurrence ⟨p.zLaterMember, hL⟩ : ℝ)‖ :=
  (sameHeight_amplitude_inverts_at_raccords ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
    hSame hT2 hβ).1

#print axioms localReading_modeA
#print axioms localReading_fails_modeC
end RHV6Fresh
