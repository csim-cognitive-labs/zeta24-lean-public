/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Tower.ProperTower

/-!
# RHV6Fresh — faits structurels du type porteur `TrueTower z` (2026-09-22, maître Lean §26)

Ce module remplace l'ancien `Tower/TrueTowerAudit.lean` (supprimé le 2026-09-22,
sixième correction) : les habitants « de contrôle » du type porteur
(`trueTowerAtControl z k`) et les énoncés de multiplicité qu'ils portaient
(« le type est infini », « l'état propre n'est pas déterminé par z ») ne sont pas
des énoncés sur la Tour.  L'auteur a clos ces questions : la Tour d'un vrai zéro a
**deux** contacts, et deux seulement, avec l'axe algébrique ; l'agrégat de cellules
n'existe pas ; un zéro et sa paire de contacts se déterminent dans les deux sens
(maître mathématique §5.e, sixième correction).  Les valeurs des formules
tangentielles à une autre coordonnée (`analyticPairAt z k`) sont des valeurs de
formule, jamais des contacts de la Tour ; en faire des habitants du type porteur
était une chimère de représentation, jamais une propriété de la Tour.

Restent ici les faits structurels vrais et utiles aux Tours produites (`firstTowerOf z`, `secondTowerOf z`) :
le mouvement est un singleton, une paire est déterminée par ses deux contacts ou
par ses deux lectures, une Tour portée est déterminée par sa paire.
Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-- Le mouvement est un singleton : ses champs sont fixés par `z`. -/
instance towerMotion_subsingleton (z : TrueZero) : Subsingleton (TowerMotion z) :=
  ⟨fun a b => by
    obtain ⟨pa, la, ia, hpa, hla, hia⟩ := a
    obtain ⟨pb, lb, ib, hpb, hlb, hib⟩ := b
    have hp : pa = pb := hpa.trans hpb.symm
    subst hp
    have hl : la = lb := funext fun k => (hla k).trans (hlb k).symm
    subst hl
    have hi : ia = ib := funext fun k => (hia k).trans (hib k).symm
    subst hi
    rfl⟩

theorem TrueTower.toTowerMotion_eq {z : TrueZero} (𝒯 : TrueTower z) :
    𝒯.toTowerMotion = towerMotionOf z := Subsingleton.elim _ _

/-- Une paire à deux lois est déterminée par ses deux contacts. -/
theorem AnalyticContactPair.ext_contacts {z : TrueZero} {P Q : AnalyticContactPair z}
    (hE : P.entryContact = Q.entryContact) (hL : P.lastRayContact = Q.lastRayContact) :
    P = Q := by
  cases P; cases Q
  cases hE; cases hL
  rfl

/-- Une paire à deux lois est déterminée par ses deux lectures `(k, m)`. -/
theorem AnalyticContactPair.ext_readings {z : TrueZero} {P Q : AnalyticContactPair z}
    (hk : P.entryCoordinate = Q.entryCoordinate) (hm : P.stageCount = Q.stageCount) :
    P = Q := by
  apply AnalyticContactPair.ext_contacts
  · rw [P.entryContact_eq_incidence, Q.entryContact_eq_incidence, hk]
  · rw [P.lastRayContact_eq_incidence, Q.lastRayContact_eq_incidence, hk, hm]

/-- Une Tour portée est déterminée par sa paire portée. -/
theorem TrueTower.ext_pair {z : TrueZero} {A B : TrueTower z}
    (h : A.toAnalyticContactPair = B.toAnalyticContactPair) : A = B := by
  obtain ⟨mA, pA⟩ := A
  obtain ⟨mB, pB⟩ := B
  have hm : mA = mB := Subsingleton.elim _ _
  cases hm
  cases h
  rfl

/-- Les lectures `(k, m)` identifient une Tour portée. -/
theorem TrueTower.readings_injective (z : TrueZero) :
    Function.Injective (fun 𝒯 : TrueTower z =>
      (𝒯.toAnalyticContactPair.entryCoordinate, 𝒯.toAnalyticContactPair.stageCount)) := by
  intro A B hEq
  simp only [Prod.mk.injEq] at hEq
  exact TrueTower.ext_pair (AnalyticContactPair.ext_readings hEq.1 hEq.2)

end RHV6Fresh
