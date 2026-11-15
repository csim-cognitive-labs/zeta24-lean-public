/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TrueTowerCarrier

/-!
# RHV3Lean — diagnostic historique de collision du premier canonique miroir

STATUT : ROUTE SECONDAIRE ACTIVE, SANS PREMISSE AU-DELA DE SES DEUX FAITS
NOMMES. Discutee explicitement avec l'utilisateur le 2026-09-11 (voir
`docs/RH_STRATEGIE_LEAN.md` §30.2). Le statut anterieur (« LEGACY_DIAGNOSTIC »)
citait l'absence d'un candidat ailleurs dans le corpus comme preuve de
faiblesse mathematique de cette route — raisonnement desormais interdit
(`CLAUDE.md` §7.9). Le maitre mathematique §4-5 (« COLLISION DE HAUTEUR SOUS
OFF ») etablit deja, sans loi de nullite independante, que le quartet miroir
produit par OFF partage exactement la meme hauteur pour sa paire superieure.
Cette route reste PARALLELE, jamais substituee, a la route active de
`CanonicalT1.lean`/`CanonicalT2.lean` (nullite/loi locale, §30.1).

    TRACE_ID               : RHV3-SAME-PRIME-MIRROR-COLLISION
    SEMANTIC_OBJECT        : diagnostic sur le vrai couple miroir supérieur
    SEMANTIC_STATEMENT     : si deux membres miroir avaient le même C3 et si C3
                             était injectif, OFF serait impossible
    MATHEMATICAL_STATEMENT : C3(z)=C3(mirror z) et Injective(C3) impliquent
                             z=mirror z
    MATHEMATICAL_PARENT    : diagnostic seulement
    PROOF_STRATEGY         : injectivité puis distinction analytique du miroir
    REQUIRED_LEMMAS        : thm_offCriticalLine_mirror_distinct,
                             thm_riemannHypothesis_of_allUpperOnCriticalLine
    WHY_EACH_LEMMA_EXISTS  : le premier conserve la distinction analytique du
                             vrai miroir ; le second est seulement le consumer
                             public standard de la centralité supérieure
    LEAN_DEFINITION        : TOffCriticalLineUpperZero,
                             offOriginalUpperMember, offMirrorUpperMember,
                             PCentralPrimeInjective, PMirrorCollision
    LEAN_THEOREM           : thm_off_impossible_by_samePrimeCollision,
                             riemannHypothesis_of_samePrimeCollision,
                             thm_riemannHypothesis_of_named_mirrorCollision
    SAME_MEMBER_CHECK      : vrai membre OFF et vrai miroir fonctionnel
    SAME_PASSAGE_CHECK     : sans objet
    SAME_MIDDLE_CHECK      : sans objet à ce niveau
    SAME_HISTORY_CHECK     : même fonction C3 du même porteur
    FORBIDDEN_PREMISES     : utiliser cette route pour substituer, plutôt que
                             compléter, la route active de T1/T2
    NEXT_CONSUMER          : la contradiction terminale, en parallèle de la
                             route nullité/loi locale
    AXIOMS                 : propext, Classical.choice, Quot.sound
    LEAN_STATUS            : STRUCTURE_PRODUCED — PCentralPrimeInjective et
                             PMirrorCollision restent des Prop nommées, non
                             prouvées ici, reçues comme faits à établir au
                             même titre que PUniqueCenterRegime/
                             PCanonicalSuccession.
-/

namespace RHV3Lean

/-- Un vrai membre supérieur fourni avec la preuve qu'il est hors ligne. -/
abbrev TOffCriticalLineUpperZero :=
  {z : TUpperNonTrivialZetaZero // PIsOffCriticalLine z.1}

/-- Le membre original exact du couple OFF. -/
def offOriginalUpperMember (zOff : TOffCriticalLineUpperZero) :
    TUpperNonTrivialZetaZero :=
  zOff.1

/-- Le vrai miroir fonctionnel supérieur du même membre OFF. -/
noncomputable def offMirrorUpperMember (zOff : TOffCriticalLineUpperZero) :
    TUpperNonTrivialZetaZero :=
  zUpperMirrorZero zOff.1

@[simp]
theorem thm_offMirror_sameHeight (zOff : TOffCriticalLineUpperZero) :
    rZeroHeight (offMirrorUpperMember zOff).1 =
      rZeroHeight (offOriginalUpperMember zOff).1 :=
  thm_mirror_sameHeight zOff.1.1

theorem thm_offMirror_distinct (zOff : TOffCriticalLineUpperZero) :
    offOriginalUpperMember zOff ≠ offMirrorUpperMember zOff := by
  intro hEq
  exact thm_offCriticalLine_mirror_distinct zOff.2
    (Subtype.ext_iff.mp hEq.symm)

/-- Diagnostic conditionnel : même C3 sur le vrai couple miroir, puis
injectivité C3, contredit la distinction OFF. -/
theorem thm_off_impossible_by_samePrimeCollision
    (K : TTrueTowerCarrier)
    (hInjective : Function.Injective K.nCarrierCentralPrime)
    (zOff : TOffCriticalLineUpperZero)
    (hPrimeEq :
      K.nCarrierCentralPrime (offOriginalUpperMember zOff) =
        K.nCarrierCentralPrime (offMirrorUpperMember zOff)) : False := by
  exact thm_offMirror_distinct zOff (hInjective hPrimeEq)

/-- Diagnostic universel, non actif. -/
theorem thm_allUpperCentral_by_samePrimeCollision
    (K : TTrueTowerCarrier)
    (hInjective : Function.Injective K.nCarrierCentralPrime)
    (hMirrorCollision : ∀ zOff : TOffCriticalLineUpperZero,
      K.nCarrierCentralPrime (offOriginalUpperMember zOff) =
        K.nCarrierCentralPrime (offMirrorUpperMember zOff)) :
    ∀ z : TUpperNonTrivialZetaZero, rZeroRadialPosition z.1 = 1 / 2 := by
  intro z
  by_contra hOff
  exact thm_off_impossible_by_samePrimeCollision K hInjective ⟨z, hOff⟩
    (hMirrorCollision ⟨z, hOff⟩)

/-- **RH sur la route miroir.** -/
theorem riemannHypothesis_of_samePrimeCollision
    (K : TTrueTowerCarrier)
    (hInjective : Function.Injective K.nCarrierCentralPrime)
    (hMirrorCollision : ∀ zOff : TOffCriticalLineUpperZero,
      K.nCarrierCentralPrime (offOriginalUpperMember zOff) =
        K.nCarrierCentralPrime (offMirrorUpperMember zOff)) :
    RiemannHypothesis :=
  thm_riemannHypothesis_of_allUpperOnCriticalLine
    (thm_allUpperCentral_by_samePrimeCollision K hInjective hMirrorCollision)

/-! ## Route nommée, au même titre que T1/T2 -/

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-- **L'injectivité du premier central.**  Deux membres distincts portent
toujours des premiers centraux distincts. Reçu comme fait à établir, jamais
une hypothèse silencieuse. -/
def PCentralPrimeInjective : Prop :=
  Function.Injective tCarrier.nCarrierCentralPrime

/-- **La collision miroir sous OFF.**  Les deux Tours de la paire miroir
supérieure produite par OFF pointent sur le même premier canonique — même
si elles atterrissent sur l'axe algébrique en des points généralement
distincts. Reçu comme fait à établir (maître mathématique §4-5), jamais une
hypothèse silencieuse. -/
def PMirrorCollision : Prop :=
  ∀ zOff : TOffCriticalLineUpperZero,
    tCarrier.nCarrierCentralPrime (offOriginalUpperMember zOff) =
      tCarrier.nCarrierCentralPrime (offMirrorUpperMember zOff)

end TTrueTowerCarrier

/-- **RH, sur la route miroir, avec les deux faits nommés explicitement.**
Aucune autre prémisse. -/
theorem thm_riemannHypothesis_of_named_mirrorCollision
    (tCarrier : TTrueTowerCarrier)
    (hInjective : tCarrier.PCentralPrimeInjective)
    (hCollision : tCarrier.PMirrorCollision) :
    RiemannHypothesis :=
  riemannHypothesis_of_samePrimeCollision tCarrier hInjective hCollision

end RHV3Lean
