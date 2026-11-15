/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# RHV3Lean — O1, le vrai zéro

    TRACE_ID              : RHV3-O1
    SEMANTIC_OBJECT       : O1 — le vrai zéro
    SEMANTIC_STATEMENT    : un vrai zéro est un point complexe où zêta s'annule
                            réellement, objet-source de toute la démonstration,
                            dont cinq attributs constitutifs — hauteur, position
                            radiale, multiplicité, provenance zêta, identité
                            analytique — sont conservés intégralement par tout
                            transport.
    MATHEMATICAL_STATEMENT: rho = beta + iT avec zeta(rho) = 0, 0 < beta < 1 ;
                            la chaîne causale conserve la hauteur, la position
                            radiale, la multiplicité et l'identité de rho sans
                            recalcul ni approximation.
    MATHEMATICAL_PARENT   : aucun — objet-source, sans amont.
    PROOF_STRATEGY        : le zéro est un sous-type du plan complexe portant sa
                            propre annulation ; les cinq attributs sont des
                            projections de son support, donc conservés par
                            construction ; la multiplicité est l'ordre
                            d'annulation analytique au même point.
    REQUIRED_LEMMAS       : analyticOn_riemannZeta, analyticOrderAt,
                            AnalyticAt.analyticOrderAt_ne_zero, Subtype.ext
    WHY_EACH_LEMMA_EXISTS : le premier donne l'analyticité hors du pôle, sans
                            laquelle la multiplicité n'a pas de sens ; le
                            troisième dit que la multiplicité d'un vrai zéro
                            n'est jamais nulle ; le dernier porte l'identité
                            analytique.
    LEAN_DEFINITION       : PIsNonTrivialZetaZero, TNonTrivialZetaZero,
                            TUpperNonTrivialZetaZero, rZeroHeight,
                            rZeroRadialPosition, nZeroMultiplicity
    LEAN_THEOREM          : thm_zeroProvenance_zeta,
                            thm_zero_identity_of_sameSupport,
                            thm_zeroMultiplicity_ne_zero,
                            thm_zeroAttributes_are_functions_of_support
    SAME_MEMBER_CHECK     : tout attribut est une projection du support du MÊME
                            membre ; aucun n'est recalculé ni approché.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre ici.
    FORBIDDEN_PREMISES    : tout point synthétique tenant lieu de zéro ; toute
                            hypothèse sur la position radiale au-delà de la
                            bande ouverte ; toute mention d'un premier, d'une
                            Tour, d'un contact ou d'un comptage.
    NEXT_CONSUMER         : O7 (grammaire des écarts de zéros), O3 (Tour
                            harmonique).
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

/-! ## 1. Le vrai zéro et sa provenance zêta -/

/-- **Être un vrai zéro non trivial** : zêta s'y annule réellement, et le point
est dans la bande critique ouverte. -/
def PIsNonTrivialZetaZero (cPoint : ℂ) : Prop :=
  riemannZeta cPoint = 0 ∧ 0 < cPoint.re ∧ cPoint.re < 1

/-- **Le vrai zéro**, portant sa propre annulation.  Ce n'est jamais un point
synthétique : la provenance zêta est un champ de l'objet, pas une hypothèse
ajoutée en aval. -/
def TNonTrivialZetaZero := {cPoint : ℂ // PIsNonTrivialZetaZero cPoint}

/-- La branche supérieure : les vrais zéros de hauteur strictement positive. -/
def TUpperNonTrivialZetaZero := {zZero : TNonTrivialZetaZero // 0 < zZero.1.im}

/-- Support complexe du vrai zéro. -/
def cZeroSupport (zZero : TNonTrivialZetaZero) : ℂ := zZero.1

/-! ## 2. Les cinq attributs constitutifs -/

/-- **Attribut 1 — la hauteur.** -/
def rZeroHeight (zZero : TNonTrivialZetaZero) : ℝ := (cZeroSupport zZero).im

/-- **Attribut 2 — la position radiale.** -/
def rZeroRadialPosition (zZero : TNonTrivialZetaZero) : ℝ :=
  (cZeroSupport zZero).re

/-- **Attribut 3 — la multiplicité analytique**, ordre d'annulation de zêta au
même point, dans `ℕ∞`. -/
noncomputable def nZeroMultiplicity (zZero : TNonTrivialZetaZero) : ℕ∞ :=
  analyticOrderAt riemannZeta (cZeroSupport zZero)

/-- **Attribut 4 — la provenance zêta**, c'est-à-dire l'annulation elle-même. -/
theorem thm_zeroProvenance_zeta (zZero : TNonTrivialZetaZero) :
    riemannZeta (cZeroSupport zZero) = 0 := zZero.2.1

/-- **Attribut 5 — l'identité analytique** : un vrai zéro est déterminé par son
support, et deux vrais zéros de même support sont le même objet. -/
theorem thm_zero_identity_of_sameSupport
    {zLeftZero zRightZero : TNonTrivialZetaZero}
    (hSameSupport : cZeroSupport zLeftZero = cZeroSupport zRightZero) :
    zLeftZero = zRightZero := Subtype.ext hSameSupport

/-! ## 3. La bande ouverte, et le point n'est pas le pôle -/

theorem thm_zeroRadialPosition_positive (zZero : TNonTrivialZetaZero) :
    0 < rZeroRadialPosition zZero := zZero.2.2.1

theorem thm_zeroRadialPosition_lt_one (zZero : TNonTrivialZetaZero) :
    rZeroRadialPosition zZero < 1 := zZero.2.2.2

theorem thm_upperZeroHeight_positive (zUpperZero : TUpperNonTrivialZetaZero) :
    0 < rZeroHeight zUpperZero.1 := zUpperZero.2

/-- Le support d'un vrai zéro n'est jamais le pôle de zêta. -/
theorem thm_zeroSupport_ne_pole (zZero : TNonTrivialZetaZero) :
    cZeroSupport zZero ≠ 1 := by
  intro hIsPole
  have hRadial : rZeroRadialPosition zZero < 1 := thm_zeroRadialPosition_lt_one zZero
  have hRealPart : (cZeroSupport zZero).re = (1 : ℂ).re := congrArg Complex.re hIsPole
  rw [Complex.one_re] at hRealPart
  exact absurd hRealPart (ne_of_lt hRadial)

/-! ## 4. La multiplicité est bien définie et jamais nulle -/

/-- Zêta est analytique au support du vrai zéro : le pôle est exclu. -/
theorem thm_zeta_analyticAt_zero (zZero : TNonTrivialZetaZero) :
    AnalyticAt ℂ riemannZeta (cZeroSupport zZero) :=
  analyticOn_riemannZeta _ (by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using
      thm_zeroSupport_ne_pole zZero)

/-- **La multiplicité d'un vrai zéro n'est jamais nulle.**  C'est la traduction
exacte du fait que l'annulation est réelle : un ordre nul signifierait que zêta
ne s'annule pas au point. -/
theorem thm_zeroMultiplicity_ne_zero (zZero : TNonTrivialZetaZero) :
    nZeroMultiplicity zZero ≠ 0 :=
  (thm_zeta_analyticAt_zero zZero).analyticOrderAt_ne_zero.mpr
    (thm_zeroProvenance_zeta zZero)

/-! ## 5. Rigidité de transport de O1 -/

/-- **RIGIDITE.**  Les cinq attributs constitutifs sont des fonctions du seul
support du membre : deux lectures du même membre donnent exactement les mêmes
valeurs, sans recalcul ni approximation.  Aucune étape en aval ne peut donc
faire correspondre deux valeurs d'un attribut à un même vrai zéro. -/
theorem thm_zeroAttributes_are_functions_of_support
    {zLeftZero zRightZero : TNonTrivialZetaZero}
    (hSameSupport : cZeroSupport zLeftZero = cZeroSupport zRightZero) :
    rZeroHeight zLeftZero = rZeroHeight zRightZero ∧
      rZeroRadialPosition zLeftZero = rZeroRadialPosition zRightZero ∧
      nZeroMultiplicity zLeftZero = nZeroMultiplicity zRightZero := by
  have hSameZero : zLeftZero = zRightZero :=
    thm_zero_identity_of_sameSupport hSameSupport
  exact ⟨congrArg rZeroHeight hSameZero, congrArg rZeroRadialPosition hSameZero,
    congrArg nZeroMultiplicity hSameZero⟩

/-- **RIGIDITE, forme contrapposée.**  Deux vrais zéros distincts ont des
supports distincts : l'identité analytique n'est jamais perdue en aval. -/
theorem thm_distinctZeros_haveDistinctSupports
    {zLeftZero zRightZero : TNonTrivialZetaZero}
    (hDistinct : zLeftZero ≠ zRightZero) :
    cZeroSupport zLeftZero ≠ cZeroSupport zRightZero :=
  fun hSame => hDistinct (thm_zero_identity_of_sameSupport hSame)

/-! ## 6. Liaison à la conclusion recherchée -/

/-- **Sous l'hypothèse de Riemann de Mathlib, tout vrai zéro est sur la ligne
critique.**  Cette liaison est donnée ici dans le seul sens qui ne demande rien
d'autre que O1 : un vrai zéro de la bande ouverte n'est ni un zéro trivial ni
le pôle, donc l'énoncé de Mathlib s'y applique directement.

Le sens réciproque n'appartient pas à O1 : il demande le confinement dans la
bande, qui relève de la symétrie fonctionnelle et du miroir, objets produits
plus tard. Il n'est ni supposé ni utilisé ici. -/
theorem thm_zeroRadialPosition_half_of_riemannHypothesis
    (hRiemann : RiemannHypothesis) (zZero : TNonTrivialZetaZero) :
    rZeroRadialPosition zZero = 1 / 2 := by
  refine hRiemann (cZeroSupport zZero) (thm_zeroProvenance_zeta zZero) ?_
    (thm_zeroSupport_ne_pole zZero)
  rintro ⟨nIndex, hTrivial⟩
  have hPositive : 0 < rZeroRadialPosition zZero :=
    thm_zeroRadialPosition_positive zZero
  have hRealPart : rZeroRadialPosition zZero = -2 * ((nIndex : ℝ) + 1) := by
    show (cZeroSupport zZero).re = _
    rw [hTrivial]
    norm_num
  have hNonneg : (0 : ℝ) ≤ (nIndex : ℝ) := Nat.cast_nonneg nIndex
  rw [hRealPart] at hPositive
  nlinarith

end RHV3Lean
