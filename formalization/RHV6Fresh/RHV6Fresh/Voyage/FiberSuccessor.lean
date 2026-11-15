/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Direct.MirrorCount

/-!
# RHV6Fresh — le zéro suivant dans la fibre (maître mathématique §9, maître Lean §8)

Pour un membre de côté `β < 1/2`, l'ensemble `S(z) = {v ∈ F(T) : z ≺ v}` des
zéros de même ordonnée postérieurs à `z` est fini (`thm_zeroHeightFiber_finite`)
et non vide (`mirror_precedes`) ; son minimum pour la clé d'ordre est le zéro
suivant `z'`, consécutif à `z` parce que le verrou de la fibre
(`thm_sameFiberInterposition`) interdit toute interposition d'ordonnée
différente.  C'est l'argument de la preuve compilée de
`thm_existsConsecutiveInFiber` (RHV3Lean), transcrit avec `z` fixé en premier
membre.  Dérivation sans hypothèse ; aucun zéro n'est construit, calculé ni
approché.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **Le zéro suivant** : pour `β(z) < 1/2`, il existe un vrai zéro `z'` de même
ordonnée, consécutif à `z` dans l'ordre des membres. -/
theorem exists_fiberSuccessor {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    ∃ z' : TrueZero,
      rZeroHeight z'.1 = rZeroHeight z.1 ∧ PZeroMembersConsecutive z.1 z'.1 := by
  classical
  set sLater : Set TNonTrivialZetaZero :=
    {v | rZeroHeight v = rZeroHeight z.1 ∧ PZeroMemberPrecedes z.1 v} with hLaterDef
  have hFinite : sLater.Finite := by
    refine Set.Finite.subset (thm_zeroHeightFiber_finite (rZeroHeight z.1)) ?_
    intro v hv
    exact hv.1
  have hNonempty : sLater.Nonempty :=
    ⟨(mirrorMember z).1, mirrorMember_ordinate z, mirror_precedes hβ⟩
  obtain ⟨v, hvMem, hMinimal⟩ :=
    Set.exists_min_image sLater fnZeroOrderKey hFinite hNonempty
  have hvUpper : 0 < rZeroHeight v := by
    rw [hvMem.1]
    exact z.2
  refine ⟨⟨v, hvUpper⟩, hvMem.1, hvMem.2, ?_⟩
  rintro ⟨w, hAfter, hBefore⟩
  have hwHeight : rZeroHeight w = rZeroHeight z.1 :=
    thm_sameFiberInterposition (zEarlier := z.1) (zLater := v) hvMem.1.symm hAfter hBefore
  exact absurd (hMinimal w ⟨hwHeight, hAfter⟩) (not_le.mpr hBefore)

/-- Le zéro suivant est strictement plus à droite (`β(z) < β(z')`), dans la même fibre. -/
theorem fiberSuccessor_radial_gt {z z' : TrueZero}
    (hT : rZeroHeight z'.1 = rZeroHeight z.1)
    (hab : PZeroMembersConsecutive z.1 z'.1) :
    rZeroRadialPosition z.1 < rZeroRadialPosition z'.1 := by
  have h := (thm_zeroMemberPrecedes_iff_height_radial_lex z.1 z'.1).mp hab.1
  rcases h with hStrict | hEq
  · exfalso
    rw [hT] at hStrict
    exact lt_irrefl _ hStrict
  · exact hEq.2

/-- Le zéro suivant ne dépasse pas le miroir : `β(z') ≤ 1 − β(z)`. -/
theorem fiberSuccessor_radial_le_mirror {z z' : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (hT : rZeroHeight z'.1 = rZeroHeight z.1)
    (hab : PZeroMembersConsecutive z.1 z'.1) :
    rZeroRadialPosition z'.1 ≤ 1 - rZeroRadialPosition z.1 := by
  by_contra hNot
  rw [not_le] at hNot
  apply hab.2
  refine ⟨(mirrorMember z).1, mirror_precedes hβ, ?_⟩
  rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
  right
  refine ⟨(mirrorMember_ordinate z).trans hT.symm, ?_⟩
  rw [mirrorMember_radial]
  exact hNot

end RHV6Fresh
