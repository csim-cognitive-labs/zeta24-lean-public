/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.CanonicalWindowRule
import RHV3Lean.Objects.TrueTowerCarrier

/-!
# RHV3Lean — le contrôle du rapport quatre, relu comme ETAT PROPRE

    TRACE_ID              : RHV3-RATIO-FOUR-STATE-CONTROL
    SEMANTIC_OBJECT       : CONTROLE — un habitant du type des états propres
    SEMANTIC_STATEMENT    : le type des états propres de Tour n'est pas vide ;
                            un membre admet au moins une paire de contacts
                            vérifiant la loi de hauteur et la loi tangentielle.
    MATHEMATICAL_STATEMENT: diagnostic historique uniquement ; la surface
                            active emploie la paire consécutive de §T.
    MATHEMATICAL_PARENT   : S4 corrigé — l'état propre.
    PROOF_STRATEGY        : calcul direct des deux angles, puis
                            `Real.sin_int_mul_pi` et `Real.sin_zero`.
    REQUIRED_LEMMAS       : Real.sin_int_mul_pi, Real.sin_zero, Real.exp_lt_exp
    WHY_EACH_LEMMA_EXISTS : les deux premiers ferment les deux lois ; le
                            troisième donne l'ordre des deux contacts.
    LEAN_DEFINITION       : tRatioFourState, tRatioFourCarrier
    LEAN_THEOREM          : thm_ratioFourState_contacts
    SAME_MEMBER_CHECK     : l'état est indexé par le membre lui-même ; aucun
                            changement de membre n'est exprimable.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre ici.
    FORBIDDEN_PREMISES    : présenter cet habitant comme le porteur CANONIQUE ;
                            l'inscrire au registre comme réalisateur.
    NEXT_CONSUMER         : aucun ; c'est un contrôle terminal.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

## STATUT

    CONTROL_ONLY
    NOT_THE_CANONICAL_CARRIER
    REALISES_NO_OBLIGATION

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

/-! ## 4. Le même contrôle, comme ETAT PROPRE (causalité corrigée) -/

/-- **L'état propre du contrôle.**  Les deux contacts sont donnés d'abord, et
les deux lois sont vérifiées : le contact d'entrée est l'incidence de phase, et
l'écart angulaire vaut exactement `N` demi-tours. -/
noncomputable def tRatioFourState (zUpperZero : TUpperNonTrivialZetaZero) :
    TTrueHarmonicTowerState zUpperZero :=
  tPrincipalBranchTowerState zUpperZero

/-- **Le porteur de contrôle.**  CONTROL_ONLY : il n'est le porteur canonique
d'aucun maître, et le registre ne l'inscrit comme réalisateur de rien. -/
noncomputable def tRatioFourCarrier : TTrueTowerCarrier where
  fnState := tRatioFourState

/-- Le contrôle rend exactement les contacts que la lecture par fenêtre donnait :
le type des états propres n'est donc pas vide. -/
theorem thm_ratioFourState_contacts (zUpperZero : TUpperNonTrivialZetaZero) :
    tRatioFourCarrier.rCarrierContactMinus zUpperZero =
        rPrincipalBranchContactMinus zUpperZero ∧
      tRatioFourCarrier.rCarrierContactPlus zUpperZero =
        rPrincipalBranchContactPlus zUpperZero :=
  ⟨rfl, rfl⟩

end RHV3Lean
