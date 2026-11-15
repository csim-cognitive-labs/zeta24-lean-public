/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.ZetaRealSegment

/-!
# RHV3Lean — le représentant supérieur d'un vrai zéro

    TRACE_ID              : RHV3-UPPER-REP
    SEMANTIC_OBJECT       : la branche supérieure comme lecture EXHAUSTIVE
    SEMANTIC_STATEMENT    : tout vrai zéro non trivial possède un représentant
                            de la branche supérieure qui porte exactement la
                            même position radiale ; la branche supérieure ne
                            perd donc aucun membre.
    MATHEMATICAL_STATEMENT: la conjugaison envoie un vrai zéro sur un vrai zéro
                            de même position radiale et de hauteur opposée ; la
                            hauteur d'un vrai zéro n'étant jamais nulle, un des
                            deux membres du couple conjugué est de hauteur
                            strictement positive.
    MATHEMATICAL_PARENT   : O1 — le vrai zéro ; l'entrée analytique orthogonale.
    PROOF_STRATEGY        : `riemannZeta_conj` donne l'annulation au conjugué ;
                            les deux coordonnées se lisent directement ; la
                            trichotomie sur la hauteur est close par
                            `thm_zeroHeight_ne_zero`.
    REQUIRED_LEMMAS       : riemannZeta_conj, Complex.conj_re, Complex.conj_im
    WHY_EACH_LEMMA_EXISTS : le premier fait du conjugué un vrai zéro ; les deux
                            autres donnent ses deux coordonnées sans calcul.
    LEAN_DEFINITION       : zConjugateZero, zUpperRepresentative
    LEAN_THEOREM          : thm_conjugateZero_height, thm_conjugateZero_radialPosition,
                            thm_upperRepresentative_radialPosition
    SAME_MEMBER_CHECK     : le conjugué est un vrai zéro à part entière, avec
                            ses cinq attributs ; le représentant supérieur est
                            le membre lui-même quand sa hauteur est positive.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre ici.
    FORBIDDEN_PREMISES    : l'hypothèse de Riemann ou sa négation ; toute
                            hypothèse sur la position radiale.
    NEXT_CONSUMER         : la lecture canonique de l'opérateur sur un membre
                            quelconque, puis l'universalisation.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Attention à ne pas confondre avec S1 : le MIROIR FONCTIONNEL `1 - conj rho`
change la position radiale et conserve la hauteur ; la CONJUGAISON `conj rho`
conserve la position radiale et change le signe de la hauteur.  Les deux
symétries sont distinctes et ce module n'utilise que la seconde.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

open Complex

/-! ## 1. Le conjugué d'un vrai zéro est un vrai zéro -/

/-- **Le zéro conjugué** : `conj rho`.  Même position radiale, hauteur opposée. -/
noncomputable def zConjugateZero (zZero : TNonTrivialZetaZero) : TNonTrivialZetaZero :=
  ⟨(starRingEnd ℂ) (cZeroSupport zZero), by
      rw [riemannZeta_conj, thm_zeroProvenance_zeta, map_zero], by
      simpa [rZeroRadialPosition] using thm_zeroRadialPosition_positive zZero, by
      simpa [rZeroRadialPosition] using thm_zeroRadialPosition_lt_one zZero⟩

@[simp]
theorem thm_conjugateZero_height (zZero : TNonTrivialZetaZero) :
    rZeroHeight (zConjugateZero zZero) = -rZeroHeight zZero := by
  simp [zConjugateZero, rZeroHeight, cZeroSupport]

@[simp]
theorem thm_conjugateZero_radialPosition (zZero : TNonTrivialZetaZero) :
    rZeroRadialPosition (zConjugateZero zZero) = rZeroRadialPosition zZero := by
  simp [zConjugateZero, rZeroRadialPosition, cZeroSupport]

/-! ## 2. Le représentant supérieur -/

/-- Le membre porté par le représentant supérieur : le membre lui-même si sa
hauteur est positive, sinon son conjugué. -/
noncomputable def zUpperRepresentativeMember (zZero : TNonTrivialZetaZero) :
    TNonTrivialZetaZero :=
  if 0 < rZeroHeight zZero then zZero else zConjugateZero zZero

/-- **La hauteur du représentant est strictement positive.**  Le cas d'une
hauteur nulle est impossible, et c'est exactement l'entrée analytique
orthogonale qui le ferme. -/
theorem thm_upperRepresentativeMember_heightPositive (zZero : TNonTrivialZetaZero) :
    0 < rZeroHeight (zUpperRepresentativeMember zZero) := by
  unfold zUpperRepresentativeMember
  split_ifs with hPositive
  · exact hPositive
  · have hNeZero : rZeroHeight zZero ≠ 0 := thm_zeroHeight_ne_zero zZero
    have hNegative : rZeroHeight zZero < 0 := by
      rcases lt_trichotomy (rZeroHeight zZero) 0 with hLt | hEq | hGt
      · exact hLt
      · exact absurd hEq hNeZero
      · exact absurd hGt hPositive
    rw [thm_conjugateZero_height]
    linarith

/-- **Le représentant supérieur d'un vrai zéro.** -/
noncomputable def zUpperRepresentative (zZero : TNonTrivialZetaZero) :
    TUpperNonTrivialZetaZero :=
  ⟨zUpperRepresentativeMember zZero, thm_upperRepresentativeMember_heightPositive zZero⟩

/-- **Le représentant supérieur porte exactement la même position radiale.**

C'est la seule chose que l'universalisation lui demande : la centralité lue sur
la branche supérieure se relit inchangée sur le membre d'origine. -/
theorem thm_upperRepresentative_radialPosition (zZero : TNonTrivialZetaZero) :
    rZeroRadialPosition (zUpperRepresentative zZero).1 = rZeroRadialPosition zZero := by
  change rZeroRadialPosition (zUpperRepresentativeMember zZero) = _
  unfold zUpperRepresentativeMember
  split_ifs with hPositive
  · rfl
  · exact thm_conjugateZero_radialPosition zZero

/-- **Sur la branche supérieure, le représentant est le membre lui-même.**  La
lecture canonique d'un membre déjà supérieur n'est donc jamais déviée. -/
theorem thm_upperRepresentativeMember_of_positiveHeight
    {zZero : TNonTrivialZetaZero} (hPositive : 0 < rZeroHeight zZero) :
    zUpperRepresentativeMember zZero = zZero := by
  unfold zUpperRepresentativeMember
  rw [if_pos hPositive]

/-- **La branche supérieure est EXHAUSTIVE.**  Toute position radiale lue sur
la branche supérieure est la position radiale d'un membre quelconque. -/
theorem thm_allRadialPositions_of_upperBranch
    (hUpper : ∀ zUpperZero : TUpperNonTrivialZetaZero,
      rZeroRadialPosition zUpperZero.1 = 1 / 2) :
    ∀ zZero : TNonTrivialZetaZero, rZeroRadialPosition zZero = 1 / 2 := by
  intro zZero
  rw [← thm_upperRepresentative_radialPosition zZero]
  exact hUpper (zUpperRepresentative zZero)

end RHV3Lean
