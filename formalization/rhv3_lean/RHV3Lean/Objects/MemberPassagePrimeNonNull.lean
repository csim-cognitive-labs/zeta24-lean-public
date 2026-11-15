/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.MemberSensitiveMZCorrespondence
import RHV3Lean.Objects.Passage

/-!
# RHV3Lean — non-nullité arithmétique du passage membre-sensible

Ce module ferme, sans T1/T2 et sans lecture d'une cellule, la partie exacte
suivante de la chaîne : un passage zéro consécutif avance l'index zéro-source
d'une unité ; les deux ancres canoniques associées sont donc deux premiers
successifs et sont strictement distinctes.

Il NE convertit PAS cette distinction arithmétique en positivité du gap de
hauteur. Cette dernière conversion demanderait un théorème supplémentaire de
conservation/réflexion de nullité entre le passage zéro et son image
grammaticale. La dichotomie d'ordre zéro reste explicitement exposée : un
passage consécutif peut être soit strict en hauteur, soit à hauteur égale avec
ordre radial strict.
-/

namespace RHV3Lean

/-- Les ancres canoniques des deux extrémités d'un passage supérieur
consécutif sont strictement ordonnées. Le résultat utilise seulement l'avance
de un de l'index zéro-source et la stricte croissance de l'énumération
canonique des nombres premiers. -/
theorem thm_memberCanonicalAnchors_strict_of_passage
    (tPassage : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight tPassage.zEarlierMember)
    (hLaterUpper : 0 < rZeroHeight tPassage.zLaterMember) :
    nMemberCanonicalAnchor ⟨tPassage.zEarlierMember, hEarlierUpper⟩ <
      nMemberCanonicalAnchor ⟨tPassage.zLaterMember, hLaterUpper⟩ := by
  unfold nMemberCanonicalAnchor
  rw [thm_zeroSourceIndex_succ_of_passage tPassage hEarlierUpper]
  exact thm_primeAtRank_lt_successor (nZeroSourceIndex tPassage.zEarlierMember)

/-- En particulier les deux ancres canoniques du passage sont distinctes. -/
theorem thm_memberCanonicalAnchors_ne_of_passage
    (tPassage : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight tPassage.zEarlierMember)
    (hLaterUpper : 0 < rZeroHeight tPassage.zLaterMember) :
    nMemberCanonicalAnchor ⟨tPassage.zEarlierMember, hEarlierUpper⟩ ≠
      nMemberCanonicalAnchor ⟨tPassage.zLaterMember, hLaterUpper⟩ :=
  (thm_memberCanonicalAnchors_strict_of_passage
    tPassage hEarlierUpper hLaterUpper).ne

/-- Sous M9a, la même non-nullité est transportée aux occurrences de M^Z.
M9a n'est pas prouvé ici : ce théorème rend explicitement visible la seule
dépendance analytique de cette version M^Z. -/
theorem thm_memberMZOccurrences_ne_of_passage
    (hAgree : PM9aChannelIdentityOnNaturals)
    (tPassage : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight tPassage.zEarlierMember)
    (hLaterUpper : 0 < rZeroHeight tPassage.zLaterMember) :
    nMemberMZOccurrence ⟨tPassage.zEarlierMember, hEarlierUpper⟩ ≠
      nMemberMZOccurrence ⟨tPassage.zLaterMember, hLaterUpper⟩ := by
  rw [thm_memberMZOccurrence_eq_canonicalAnchor hAgree
      ⟨tPassage.zEarlierMember, hEarlierUpper⟩,
    thm_memberMZOccurrence_eq_canonicalAnchor hAgree
      ⟨tPassage.zLaterMember, hLaterUpper⟩]
  exact thm_memberCanonicalAnchors_ne_of_passage
    tPassage hEarlierUpper hLaterUpper

/-- Le contenu zéro-side exact disponible pour le même passage : l'ordre
membre-sensible est lexicographique hauteur puis position radiale. C'est cette
disjonction qui montre pourquoi la stricte croissance des premiers ne suffit
pas, à elle seule, à éliminer la branche de même hauteur. -/
theorem thm_passage_height_strict_or_sameHeight_radial
    (tPassage : TZeroPassage) :
    rZeroHeight tPassage.zEarlierMember < rZeroHeight tPassage.zLaterMember ∨
      (rZeroHeight tPassage.zEarlierMember = rZeroHeight tPassage.zLaterMember ∧
        rZeroRadialPosition tPassage.zEarlierMember <
          rZeroRadialPosition tPassage.zLaterMember) :=
  (thm_zeroMemberPrecedes_iff_height_radial_lex
    tPassage.zEarlierMember tPassage.zLaterMember).mp tPassage.precedes

/-- Théorème de synthèse maximal sans introduire de pont de nullité : le même
passage porte simultanément une transition première strictement non nulle et
la dichotomie zéro-side exacte. -/
theorem thm_memberPassage_primeNonNull_and_zeroOrder
    (tPassage : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight tPassage.zEarlierMember)
    (hLaterUpper : 0 < rZeroHeight tPassage.zLaterMember) :
    (nMemberCanonicalAnchor ⟨tPassage.zEarlierMember, hEarlierUpper⟩ <
      nMemberCanonicalAnchor ⟨tPassage.zLaterMember, hLaterUpper⟩) ∧
    (rZeroHeight tPassage.zEarlierMember < rZeroHeight tPassage.zLaterMember ∨
      (rZeroHeight tPassage.zEarlierMember = rZeroHeight tPassage.zLaterMember ∧
        rZeroRadialPosition tPassage.zEarlierMember <
          rZeroRadialPosition tPassage.zLaterMember)) :=
  ⟨thm_memberCanonicalAnchors_strict_of_passage
      tPassage hEarlierUpper hLaterUpper,
    thm_passage_height_strict_or_sameHeight_radial tPassage⟩

#check thm_memberCanonicalAnchors_strict_of_passage
#check thm_memberCanonicalAnchors_ne_of_passage
#check thm_memberMZOccurrences_ne_of_passage
#check thm_passage_height_strict_or_sameHeight_radial
#check thm_memberPassage_primeNonNull_and_zeroOrder

end RHV3Lean
