/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.Passage
import RHV3Lean.Objects.FunctionalMirror
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# RHV3Lean — OFF, la fibre de hauteur et le passage consécutif de gap nul

    TRACE_ID              : RHV3-OFF-UPPER
    SEMANTIC_OBJECT       : OFF — un vrai zéro hors ligne critique produit, à la
                            MÊME hauteur, un vrai passage consécutif d'écart
                            nul.
    SEMANTIC_STATEMENT    : troisième paragraphe de la démonstration.  Le miroir
                            d'un zéro hors ligne est un second membre distinct à
                            la même hauteur ; la fibre de hauteur ne contient
                            qu'un nombre fini de membres ; donc parmi eux deux
                            sont VOISINS, sans aucun membre strictement
                            interposé, et l'écart de hauteur de ce couple est
                            nul puisque les deux sont à la même hauteur.
    MATHEMATICAL_STATEMENT: la fibre {rho : zeta(rho)=0, 0<Re rho<1, Im rho = T}
                            est incluse dans le compact [0,1] x {T} intersecté
                            avec l'ensemble des zéros de zêta, donc finie ; dans
                            un ensemble fini non vide totalement ordonné par la
                            clé (hauteur, position radiale), tout élément
                            majoré admet un successeur immédiat ; ce successeur
                            immédiat l'est GLOBALEMENT, car tout membre
                            strictement interposé entre deux membres de même
                            hauteur est lui-même de cette hauteur.
    MATHEMATICAL_PARENT   : O1 — le vrai zéro ; O7 — la grammaire des écarts de
                            zéros ; O8 — le passage ; S1 — le miroir.
    PROOF_STRATEGY        : (1) finitude par compacité, via l'injectivité du
                            support ; (2) le minimum de l'ensemble des membres
                            strictement postérieurs à un membre donné dans la
                            fibre est son voisin immédiat ; (3) la clause
                            lexicographique fait que rien d'étranger à la fibre
                            ne peut s'interposer ; (4) le miroir fournit le
                            second membre.
    REQUIRED_LEMMAS       : IsCompact.inter_riemannZetaZeros_finite,
                            isCompact_Icc, Set.Finite.exists_minimal_wrt
    WHY_EACH_LEMMA_EXISTS : le premier est la discrétion locale des zéros de
                            zêta, seule source admissible de la finitude ; le
                            deuxième fournit le compact qui la déclenche ; le
                            troisième extrait le voisin immédiat sans aucune
                            hypothèse d'ordre supplémentaire.
    LEAN_DEFINITION       : zUpperOfPositiveHeight, tPassageUpperEndpoints
    LEAN_THEOREM          : thm_zeroHeightFiber_finite,
                            thm_sameFiberInterposition,
                            thm_existsConsecutiveInFiber,
                            thm_offCriticalLine_existsNullPassage,
                            thm_passageEndpoints_upperBranch
    SAME_MEMBER_CHECK     : les deux extrémités extraites sont des membres de la
                            fibre elle-même, jamais des points synthétiques ;
                            le bridge vers la branche supérieure ne change pas
                            le membre, il ne fait que lui adjoindre la preuve de
                            hauteur positive.
    SAME_PASSAGE_CHECK    : le passage produit est UN objet TZeroPassage, et
                            c'est sur CE passage que son écart nul est établi.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre ici.
    FORBIDDEN_PREMISES    : toute hypothèse de positivité de l'écart des zéros ;
                            toute utilisation de l'hypothèse de Riemann ou de sa
                            négation ; toute finitude posée au lieu d'être
                            déduite de la discrétion des zéros de zêta.
    NEXT_CONSUMER         : la contradiction terminale SAME-E, qui opposera cet
                            écart nul à la positivité conclue de la loi locale
                            sur LE MÊME passage.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

open Complex

/-! ## 1. OFF.LOCAL_FINITENESS — la fibre de hauteur est finie -/

/-- Le segment vertical qui contient toute la fibre de hauteur : la bande
fermée `[0,1]` à hauteur fixée.  Il est compact comme image continue d'un
segment réel compact. -/
private noncomputable def sHeightSegment (rHeight : ℝ) : Set ℂ :=
  (fun rReal : ℝ => Complex.mk rReal rHeight) '' Set.Icc 0 1

private theorem thm_heightSegment_isCompact (rHeight : ℝ) :
    IsCompact (sHeightSegment rHeight) := by
  refine isCompact_Icc.image ?_
  have hContinuous :
      Continuous fun rReal : ℝ => Complex.mk rReal rHeight := by
    have : (fun rReal : ℝ => Complex.mk rReal rHeight) =
        fun rReal : ℝ => ((rReal : ℂ) + (rHeight : ℂ) * Complex.I) := by
      funext rReal
      apply Complex.ext <;> simp
    rw [this]
    fun_prop
  exact hContinuous

/-- **OFF.LOCAL_FINITENESS.**

La fibre de hauteur d'un vrai zéro ne porte qu'un nombre FINI de membres.

C'est la seule source admissible de la finitude : la discrétion locale des
zéros de zêta, appliquée à un compact.  Rien n'est posé ; la bande ouverte de
O1 fournit le compact, l'identité analytique de O1 fournit l'injectivité, et
Mathlib fournit la discrétion. -/
theorem thm_zeroHeightFiber_finite (rHeight : ℝ) :
    (sZeroHeightFiber rHeight).Finite := by
  have hInjective :
      Set.InjOn cZeroSupport (sZeroHeightFiber rHeight) := by
    intro zLeftZero _ zRightZero _ hSameSupport
    exact thm_zero_identity_of_sameSupport hSameSupport
  refine Set.Finite.of_finite_image ?_ hInjective
  refine Set.Finite.subset
    ((thm_heightSegment_isCompact rHeight).inter_riemannZetaZeros_finite) ?_
  rintro cPoint ⟨zZero, hMember, rfl⟩
  have hHeight : rZeroHeight zZero = rHeight := hMember
  refine ⟨⟨rZeroRadialPosition zZero, ?_, ?_⟩, ?_⟩
  · exact ⟨le_of_lt (thm_zeroRadialPosition_positive zZero),
      le_of_lt (thm_zeroRadialPosition_lt_one zZero)⟩
  · apply Complex.ext
    · rfl
    · exact hHeight.symm
  · exact thm_zeroProvenance_zeta zZero

/-! ## 2. Rien d'étranger à la fibre ne peut s'interposer -/

/-- **La clause lexicographique verrouille la fibre.**

Un membre strictement compris entre deux membres de la MÊME hauteur est
nécessairement de cette même hauteur.  C'est ce qui fait qu'un voisinage
constaté à l'intérieur de la fibre est un voisinage GLOBAL, et non un artefact
de restriction. -/
theorem thm_sameFiberInterposition
    {zEarlier zLater zBetween : TNonTrivialZetaZero}
    (hSameHeight : rZeroHeight zEarlier = rZeroHeight zLater)
    (hAfter : PZeroMemberPrecedes zEarlier zBetween)
    (hBefore : PZeroMemberPrecedes zBetween zLater) :
    rZeroHeight zBetween = rZeroHeight zEarlier := by
  rw [thm_zeroMemberPrecedes_iff_height_radial_lex] at hAfter hBefore
  rcases hAfter with hStrictAfter | hEqualAfter
  · rcases hBefore with hStrictBefore | hEqualBefore
    · exfalso; rw [hSameHeight] at hStrictAfter; linarith
    · exfalso; rw [hSameHeight] at hStrictAfter
      rw [hEqualBefore.1] at hStrictAfter; linarith
  · exact hEqualAfter.1.symm

/-! ## 3. L'extraction d'un couple GLOBALEMENT consécutif dans la fibre -/

/-- **L'extraction du voisin immédiat.**

Dès que la fibre porte deux membres distincts, elle porte un couple
CONSECUTIF : deux membres de la fibre entre lesquels aucun vrai zéro, d'où
qu'il vienne, ne s'interpose.

La finitude n'est utilisée qu'une fois, pour prendre le minimum de l'ensemble
des membres de la fibre strictement postérieurs à un membre donné.  Aucun ordre
supplémentaire n'est supposé : celui de O7 suffit. -/
theorem thm_existsConsecutiveInFiber
    {zLeftZero zRightZero : TNonTrivialZetaZero}
    (hDistinct : zLeftZero ≠ zRightZero)
    (hSameHeight : rZeroHeight zLeftZero = rZeroHeight zRightZero) :
    ∃ zEarlier zLater : TNonTrivialZetaZero,
      rZeroHeight zEarlier = rZeroHeight zLeftZero ∧
        rZeroHeight zLater = rZeroHeight zLeftZero ∧
          PZeroMembersConsecutive zEarlier zLater := by
  classical
  set rHeight := rZeroHeight zLeftZero with hHeightDef
  -- on oriente le couple donné
  obtain ⟨zEarlier, zLater, hEarlierHeight, hLaterHeight, hPrecedes⟩ :
      ∃ zEarlier zLater : TNonTrivialZetaZero,
        rZeroHeight zEarlier = rHeight ∧ rZeroHeight zLater = rHeight ∧
          PZeroMemberPrecedes zEarlier zLater := by
    rcases thm_distinctZeroMembers_comparable hDistinct with hOrder | hOrder
    · exact ⟨zLeftZero, zRightZero, rfl, hSameHeight.symm, hOrder⟩
    · exact ⟨zRightZero, zLeftZero, hSameHeight.symm, rfl, hOrder⟩
  -- l'ensemble des membres de la fibre strictement postérieurs à `zEarlier`
  set sLater : Set TNonTrivialZetaZero :=
    {zCandidate | rZeroHeight zCandidate = rHeight ∧
      PZeroMemberPrecedes zEarlier zCandidate} with hLaterDef
  have hFinite : sLater.Finite := by
    refine Set.Finite.subset (thm_zeroHeightFiber_finite rHeight) ?_
    intro zCandidate hCandidate
    exact hCandidate.1
  have hNonempty : sLater.Nonempty := ⟨zLater, hLaterHeight, hPrecedes⟩
  obtain ⟨zNeighbour, hNeighbourMember, hMinimal⟩ :=
    Set.exists_min_image sLater fnZeroOrderKey hFinite hNonempty
  refine ⟨zEarlier, zNeighbour, hEarlierHeight, hNeighbourMember.1, ?_, ?_⟩
  · exact hNeighbourMember.2
  · rintro ⟨zBetween, hAfter, hBefore⟩
    have hBetweenHeight : rZeroHeight zBetween = rHeight := by
      have := thm_sameFiberInterposition
        (zEarlier := zEarlier) (zLater := zNeighbour)
        (hEarlierHeight.trans hNeighbourMember.1.symm) hAfter hBefore
      exact this.trans hEarlierHeight
    have hBetweenMember : zBetween ∈ sLater := ⟨hBetweenHeight, hAfter⟩
    exact absurd (hMinimal zBetween hBetweenMember) (not_le.mpr hBefore)

/-! ## 4. OFF — le passage consécutif de gap nul -/

/-- **UN VRAI ZERO HORS LIGNE PRODUIT UN VRAI PASSAGE D'ECART NUL.**

C'est la seconde moitié du troisième paragraphe.  Le miroir donne un second
membre distinct à la même hauteur ; la fibre est finie ; l'extraction donne un
couple véritablement consécutif ; et l'écart de ce passage est nul parce que
ses deux extrémités sont à la même hauteur.

Aucune positivité n'est supposée nulle part, et l'hypothèse de Riemann n'entre
ni sous forme affirmée ni sous forme niée : seule la position radiale
différente de 1/2 est utilisée, et seulement pour distinguer le miroir. -/
theorem thm_offCriticalLine_existsNullPassage
    {zZero : TNonTrivialZetaZero} (hOff : PIsOffCriticalLine zZero) :
    ∃ tPassage : TZeroPassage,
      rZeroPassageHeightGap tPassage = 0 ∧
        rZeroHeight tPassage.zEarlierMember = rZeroHeight zZero := by
  obtain ⟨hDistinct, hSameHeight, _, _⟩ :=
    thm_offCriticalLineUpper_twoDistinctSameFiberMembers hOff
  obtain ⟨zEarlier, zLater, hEarlierHeight, hLaterHeight, hConsecutive⟩ :=
    thm_existsConsecutiveInFiber hDistinct hSameHeight
  refine ⟨⟨zEarlier, zLater, hConsecutive⟩, ?_, ?_⟩
  · change rZeroPairHeightGap zEarlier zLater = 0
    rw [thm_zeroPairHeightGap_zero_iff_sameFiber]
    exact hEarlierHeight.trans hLaterHeight.symm
  · exact hEarlierHeight.trans (thm_mirror_sameHeight zZero)

/-- La même conclusion, énoncée en nullité de la relation du passage : c'est la
forme que la contradiction terminale opposera, sur CE passage, à la positivité
conclue de la loi locale. -/
theorem thm_offCriticalLine_existsNullRelationPassage
    {zZero : TNonTrivialZetaZero} (hOff : PIsOffCriticalLine zZero) :
    ∃ tPassage : TZeroPassage, PZeroPassageRelationNull tPassage := by
  obtain ⟨tPassage, hGapZero, _⟩ := thm_offCriticalLine_existsNullPassage hOff
  exact ⟨tPassage, hGapZero⟩

/-! ## 5. Le bridge vers la branche supérieure -/

/-- **Le bridge d'un membre vers la branche supérieure.**  Il n'échange pas le
membre : il lui adjoint la preuve que sa hauteur est strictement positive.  La
composante `.1` est littéralement le membre de départ. -/
def zUpperOfPositiveHeight
    (zZero : TNonTrivialZetaZero) (hPositive : 0 < rZeroHeight zZero) :
    TUpperNonTrivialZetaZero := ⟨zZero, hPositive⟩

theorem thm_zUpperOfPositiveHeight_sameMember
    (zZero : TNonTrivialZetaZero) (hPositive : 0 < rZeroHeight zZero) :
    (zUpperOfPositiveHeight zZero hPositive).1 = zZero := rfl

/-- **LE BRIDGE DU PASSAGE VERS LA BRANCHE SUPERIEURE.**

Les deux extrémités d'un passage sont lisibles en branche supérieure dès que
l'extrémité d'ENTREE est de hauteur strictement positive : la positivité de
l'extrémité de sortie n'a pas à être supposée, elle est DEDUITE de la
non-négativité de l'écart, déjà acquise en O7.

C'est ce qui permet à chaque extrémité d'un passage de porter sa propre Tour,
sans qu'aucune hypothèse supplémentaire n'entre dans la route. -/
noncomputable def tPassageUpperEndpoints
    (tPassage : TZeroPassage)
    (hEarlierPositive : 0 < rZeroHeight tPassage.zEarlierMember) :
    TUpperNonTrivialZetaZero × TUpperNonTrivialZetaZero :=
  ⟨zUpperOfPositiveHeight tPassage.zEarlierMember hEarlierPositive,
    zUpperOfPositiveHeight tPassage.zLaterMember
      (lt_of_lt_of_le hEarlierPositive
        (by
          have hGap : 0 ≤ rZeroPassageHeightGap tPassage :=
            thm_zeroPassage_heightGap_nonnegative tPassage
          unfold rZeroPassageHeightGap rZeroPairHeightGap at hGap
          linarith))⟩

/-- **Le bridge ne change ni l'un ni l'autre membre.**  Les deux composantes
sont littéralement les deux extrémités propres du passage. -/
theorem thm_passageEndpoints_upperBranch
    (tPassage : TZeroPassage)
    (hEarlierPositive : 0 < rZeroHeight tPassage.zEarlierMember) :
    (tPassageUpperEndpoints tPassage hEarlierPositive).1.1 =
        tPassage.zEarlierMember ∧
      (tPassageUpperEndpoints tPassage hEarlierPositive).2.1 =
        tPassage.zLaterMember :=
  ⟨rfl, rfl⟩

end RHV3Lean
