/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Foundation.RHV3Primitives

/-!
# RHV6Fresh — clean contact-count front

This module deliberately has no RHV5 dependency.  It retains the proven
zero-side progression and the M^Z occurrence reconstruction from RHV3Lean.
The contact-count comparison is exposed with its exact missing endpoint rather
than being replaced by a false theorem.
-/

namespace RHV6Fresh

open RHV3Lean

abbrev TrueZero := TUpperNonTrivialZetaZero

noncomputable def occurrence (z : TrueZero) : ℕ :=
  nMemberMZOccurrence z

theorem occurrence_eq_canonicalAnchor (z : TrueZero) :
    occurrence z = nMemberCanonicalAnchor z := by
  exact thm_memberMZOccurrence_eq_canonicalAnchor_unconditional z

theorem occurrence_strict_of_passage
    (p : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight p.zEarlierMember)
    (hLaterUpper : 0 < rZeroHeight p.zLaterMember) :
      occurrence ⟨p.zEarlierMember, hEarlierUpper⟩ <
      occurrence ⟨p.zLaterMember, hLaterUpper⟩ := by
  calc
    occurrence ⟨p.zEarlierMember, hEarlierUpper⟩ =
        nMemberCanonicalAnchor ⟨p.zEarlierMember, hEarlierUpper⟩ :=
      occurrence_eq_canonicalAnchor _
    _ < nMemberCanonicalAnchor ⟨p.zLaterMember, hLaterUpper⟩ :=
      thm_memberCanonicalAnchors_strict_of_passage
        p hEarlierUpper hLaterUpper
    _ = occurrence ⟨p.zLaterMember, hLaterUpper⟩ :=
      (occurrence_eq_canonicalAnchor _).symm

theorem occurrence_successor_of_passage
    (p : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight p.zEarlierMember)
    (hLaterUpper : 0 < rZeroHeight p.zLaterMember) :
      occurrence ⟨p.zLaterMember, hLaterUpper⟩ =
      fnPrimeSuccessor (nZeroSourceIndex p.zEarlierMember) := by
  calc
    occurrence ⟨p.zLaterMember, hLaterUpper⟩ =
        nMemberCanonicalAnchor ⟨p.zLaterMember, hLaterUpper⟩ :=
      occurrence_eq_canonicalAnchor _
    _ = fnPrimeSuccessor (nZeroSourceIndex p.zEarlierMember) :=
      thm_memberCanonicalAnchor_succ_of_passage
        p hEarlierUpper hLaterUpper

/-!
Ce module s'arrête à la progression côté zéros et à la reconstruction de
l'occurrence (M^Z = M).  Les formules du mouvement donnent la valeur d'un rayon à
toute coordonnée entière ; la Tour n'a que deux contacts, portés par `TrueTower z`
(`Tower/ProperTower.lean`, maître sémantique §4–§5).  Aucun état `k = 0`, aucun
premier, aucune lecture n'entre ici.
-/

end RHV6Fresh
