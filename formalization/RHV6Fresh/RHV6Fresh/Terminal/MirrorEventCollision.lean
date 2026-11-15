/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.EventHeightProgression

/-!
# RHV6Fresh — tentative de clôture par collision d'événements (instruction de l'auteur, 2026-09-25)

La contradiction candidate n'est plus « lecture ∧ vérification de la seconde orientation », mais :

    la réflexion ne crée pas un nouvel événement   contre   l'ordre des membres fait avancer l'événement.

On ne raisonne qu'avec les deux membres supérieurs `z = (β, T)` et `z* = (1 − β, T)`, `β < 1/2`.
Aucune hypothèse nouvelle, aucune consécutivité supposée, aucun théorème RH-équivalent en prémisse.

## Verdict du compilateur

* **Cible A (progression stricte des membres)** : `mirror_occurrence_strict`, théorème.
* **Cible B (identité de l'événement de hauteur sous réflexion)** : `mirror_sameHeightEvent`,
  `mirror_sameHeightPrime`, `mirror_sameHeightIndex`, théorèmes ; le miroir ne consomme aucun
  événement de hauteur (`mirror_no_new_height_event`) mais consomme un index de membre
  (`mirror_consumes_member_index`) : ce sont deux grammaires distinctes, toutes deux compilées.
* **Cible C (`occurrence (mirrorMember z) = occurrence z`)** : **réfutée par théorème** pour tout
  `z` de côté bas (`mirror_event_identity_refuted`), conséquence directe de la Cible A.  L'exiger
  de tout zéro de côté bas est l'hypothèse de Riemann (`mirrorEventIdentity_iff_riemannHypothesis`).
* **Le raccord exact** que la fermeture demandait est le transport « occurrence par hauteur →
  occurrence par membre » au miroir (`memberHeightTransport (mirrorMember z)`).  Ce transport est
  **faux** pour tout `z` de côté bas (`mirror_transport_refuted`) : l'index de l'événement de
  hauteur du miroir est celui de `z`, au plus `n(z)`, strictement sous `n(z*)`.  Le transport au
  seul membre `z` ne donne rien sur `z*` (`transport_at_z_gives_nothing`).  L'exiger au miroir de
  tout zéro de côté bas est l'hypothèse de Riemann (`mirrorTransport_iff_riemannHypothesis`).

Le manque n'est donc pas « identité d'événement » (théorème) ; c'est « transport
event-height → member-occurrence », et ce transport n'est pas manquant : il est réfuté hors ligne.
La collision « même événement de hauteur, occurrence membre qui avance » est déjà le théorème
`off_mirror_two_grammars` ; ce n'est pas une contradiction, ce sont deux fonctions d'index
distinctes.  Aucun terme `RiemannHypothesis` ne sort de cette route.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Cible A : progression stricte des occurrences membres, sans consécutivité -/

/-- `Occ(z) < Occ(z*)` pour tout `z` de côté bas : M^Z = M et l'ordre strict des membres. -/
theorem mirror_occurrence_strict {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    occurrence z < occurrence (mirrorMember z) := by
  rw [occurrence_eq_primeAtRank, occurrence_eq_primeAtRank]
  exact thm_primeAtRank_strictMono (sourceIndex_lt_mirror hβ)

/-- Le miroir consomme un index de membre. -/
theorem mirror_consumes_member_index {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    nZeroSourceIndex z.1 < nZeroSourceIndex (mirrorMember z).1 :=
  sourceIndex_lt_mirror hβ

/-! ## 2. Cible B : la réflexion garde l'identité de l'événement de hauteur -/

theorem mirror_sameHeightEvent (z : TrueZero) :
    tZeroHeightEvent (mirrorMember z) = tZeroHeightEvent z :=
  thm_sameHeight_sameHeightEvent (mirrorMember_ordinate z)

theorem mirror_sameHeightIndex (z : TrueZero) :
    nZeroHeightEventIndex (tZeroHeightEvent (mirrorMember z)) =
      nZeroHeightEventIndex (tZeroHeightEvent z) :=
  thm_heightEventIndex_eq_of_sameHeight (mirrorMember_ordinate z)

theorem mirror_sameHeightPrime (z : TrueZero) :
    nHeightEventMZOccurrence (tZeroHeightEvent (mirrorMember z)) =
      nHeightEventMZOccurrence (tZeroHeightEvent z) :=
  thm_sameHeight_sameReconstructedPrime (mirrorMember_ordinate z)

/-- Le miroir ne consomme aucun événement de hauteur : même événement, même index, même premier. -/
theorem mirror_no_new_height_event (z : TrueZero) :
    tZeroHeightEvent (mirrorMember z) = tZeroHeightEvent z ∧
      nZeroHeightEventIndex (tZeroHeightEvent (mirrorMember z)) =
        nZeroHeightEventIndex (tZeroHeightEvent z) ∧
      nHeightEventMZOccurrence (tZeroHeightEvent (mirrorMember z)) =
        nHeightEventMZOccurrence (tZeroHeightEvent z) :=
  ⟨mirror_sameHeightEvent z, mirror_sameHeightIndex z, mirror_sameHeightPrime z⟩

/-! ## 3. Cible C : l'identité des occurrences membres est réfutée -/

/-- La Cible C est fausse pour tout `z` de côté bas : elle contredit la Cible A. -/
theorem mirror_event_identity_refuted {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    ¬ occurrence (mirrorMember z) = occurrence z := by
  intro h
  have hlt := mirror_occurrence_strict hβ
  rw [h] at hlt
  exact lt_irrefl _ hlt

/-! ## 4. Le raccord exact : transport event-height → member-occurrence -/

/-- Le transport au membre `w` : son occurrence membre est l'occurrence de son événement de
hauteur. -/
def memberHeightTransport (w : TrueZero) : Prop :=
  occurrence w = nHeightEventMZOccurrence (tZeroHeightEvent w)

/-- Le transport en `w` est l'égalité des deux index en `w`. -/
theorem memberHeightTransport_iff_index (w : TrueZero) :
    memberHeightTransport w ↔
      nZeroSourceIndex w.1 = nZeroHeightEventIndex (tZeroHeightEvent w) := by
  unfold memberHeightTransport
  rw [occurrence_eq_canonicalAnchor, thm_heightEventMZOccurrence_eq_canonicalPrime_unconditional]
  unfold nMemberCanonicalAnchor nHeightEventCanonicalPrime
  exact ⟨fun h => thm_primeAtRank_injective h, fun h => by rw [h]⟩

/-- Le transport aux deux membres de la paire donne la Cible C, donc `False` avec la Cible A. -/
theorem pair_transport_false {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (h₁ : memberHeightTransport z) (h₂ : memberHeightTransport (mirrorMember z)) : False := by
  apply mirror_event_identity_refuted hβ
  unfold memberHeightTransport at h₁ h₂
  rw [h₁, h₂, mirror_sameHeightPrime]

/-- **Le raccord manquant est réfuté** : le transport au miroir est faux pour tout `z` de côté
bas, car l'index de l'événement de hauteur du miroir est celui de `z`, au plus `n(z) < n(z*)`. -/
theorem mirror_transport_refuted {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    ¬ memberHeightTransport (mirrorMember z) := by
  intro h
  rw [memberHeightTransport_iff_index, mirror_sameHeightIndex] at h
  have h1 := heightEventIndex_le_sourceIndex z
  have h2 := sourceIndex_lt_mirror hβ
  omega

/-- Le transport au seul membre `z` ne dit rien du miroir : il fixe `Occ(z)` sur l'événement de
hauteur commun, et `Occ(z*)` reste strictement au-dessus. -/
theorem transport_at_z_gives_nothing {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (h₁ : memberHeightTransport z) :
    nHeightEventMZOccurrence (tZeroHeightEvent (mirrorMember z)) = occurrence z ∧
      occurrence z < occurrence (mirrorMember z) := by
  refine ⟨?_, mirror_occurrence_strict hβ⟩
  rw [mirror_sameHeightPrime]
  exact h₁.symm

/-! ## 5. La collision « même événement, occurrence qui avance » n'est pas une contradiction -/

/-- Ce que la route donne réellement : même événement de hauteur, même premier par hauteurs, et
deux occurrences membres strictement ordonnées.  Deux fonctions d'index distinctes, aucun `False`. -/
theorem mirror_event_collision_content {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    tZeroHeightEvent (mirrorMember z) = tZeroHeightEvent z ∧
      nHeightEventMZOccurrence (tZeroHeightEvent (mirrorMember z)) =
        nHeightEventMZOccurrence (tZeroHeightEvent z) ∧
      occurrence z < occurrence (mirrorMember z) :=
  ⟨mirror_sameHeightEvent z, mirror_sameHeightPrime z, mirror_occurrence_strict hβ⟩

end RHV6Fresh
