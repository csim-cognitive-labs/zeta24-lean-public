/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.ZeroGapGrammar

/-!
# RHV3Lean — O8, le passage, et sa rigidité de transport R-PASS

    TRACE_ID              : RHV3-O8
    SEMANTIC_OBJECT       : O8 — le passage ; R-PASS — sa rigidité de transport
    SEMANTIC_STATEMENT    : le passage entre deux membres consécutifs est un
                            objet unitaire à part entière. R-PASS transporte
                            ses deux membres propres, dans leur ordre, vers les
                            deux extrémités de la même image ; le passage source
                            et son écart restent intégralement disponibles.
    MATHEMATICAL_STATEMENT: E = (Z_i, Z_(i+1)) avec Null_Z(E) :<=> d_i = 0 ;
                            le corps actuel conserve seulement les extrémités;
                            le R-PASS complet doit être dérivé du producteur T2.
    MATHEMATICAL_PARENT   : O7 — la grammaire des écarts de zéros.
    PROOF_STRATEGY        : le passage stocke ses deux extrémités et leur
                            consécutivité ; l'écart et la nullité restent des
                            données DERIVEES, jamais des champs. R-PASS est
                            exactement le transport membre-sensible des deux
                            extrémités ; le gap source reste projetable depuis
                            le même passage et n'est jamais perdu.
    REQUIRED_LEMMAS       : thm_zeroPairHeightGap_nonnegative,
                            thm_zeroPairHeightGap_zero_iff_sameFiber,
                            thm_consecutive_members_distinct
    WHY_EACH_LEMMA_EXISTS : le premier donne la non-négativité de l'écart du
                            passage, acquise en O7 et jamais re-supposée ; le
                            deuxième dit ce que nullité veut dire exactement ;
                            le troisième porte la distinction des extrémités
                            comme membres, qui n'est PAS la séparation des
                            extrémités de l'image.
    LEAN_DEFINITION       : TZeroPassage, rZeroPassageHeightGap,
                            PZeroPassageRelationNull,
                            PZeroPassageRelationNonNull,
                            PIsMemberSensitivePassageTransport
    LEAN_THEOREM          : thm_zeroPassage_heightGap_nonnegative,
                            thm_zeroPassage_null_iff_sameHeight,
                            thm_zeroPassage_nonNull_iff_gapPositive,
                            thm_rpass_endpoints_are_member_own
    SAME_MEMBER_CHECK     : les deux extrémités du passage sont ses propres
                            membres ; aucune n'est remplacée par un membre
                            étranger.
    SAME_PASSAGE_CHECK    : la nullité, l'écart et les extrémités sont lus sur
                            le MÊME passage, jamais reconstruits par comparaison
                            avec un second passage.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau — le triple est O9.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre ici ; le type des
                            images du transport reste abstrait.
    FORBIDDEN_PREMISES    : stocker la nullité source comme champ libre au lieu
                            de la dériver du même passage ; convertir sans preuve
                            cette nullité en égalité de premiers ; poser la positivité de
                            l'écart comme prémisse ; faire de R-PASS un théorème
                            à réétablir à chaque usage.
    NEXT_CONSUMER         : O9 (le triple), puis la loi locale du transport.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : PASSAGE_BODY_PRODUCED / COMPLETE_RPASS_TO_PRODUCE

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

/-! ## 1. Le passage -/

/-- **Le passage** entre deux membres consécutifs.  Il ne stocke que ses deux
extrémités et leur consécutivité véritable ; l'écart et la nullité restent des
données dérivées, jamais des champs que l'on pourrait poser à volonté. -/
structure TZeroPassage where
  /-- Extrémité d'entrée. -/
  zEarlierMember : TNonTrivialZetaZero
  /-- Extrémité de sortie. -/
  zLaterMember : TNonTrivialZetaZero
  /-- Voisinage : les deux extrémités sont véritablement consécutives. -/
  hConsecutive : PZeroMembersConsecutive zEarlierMember zLaterMember

namespace TZeroPassage

variable (tPassage : TZeroPassage)

/-- **Ordre** : l'extrémité d'entrée précède l'extrémité de sortie. -/
theorem precedes :
    PZeroMemberPrecedes tPassage.zEarlierMember tPassage.zLaterMember :=
  tPassage.hConsecutive.1

/-- **Extrémités distinctes comme membres.**  Attention : ceci est la
distinction des deux MEMBRES du passage, jamais la séparation des extrémités de
son image, qui est une propriété dérivée bien plus tard, de la loi locale. -/
theorem members_distinct :
    tPassage.zEarlierMember ≠ tPassage.zLaterMember :=
  thm_consecutive_members_distinct tPassage.hConsecutive

end TZeroPassage

/-! ## 2. L'écart, la nullité, la non-nullité — toutes dérivées -/

/-- **L'écart du passage**, lu sur ses propres extrémités. -/
def rZeroPassageHeightGap (tPassage : TZeroPassage) : ℝ :=
  rZeroPairHeightGap tPassage.zEarlierMember tPassage.zLaterMember

/-- **La nullité de la relation elle-même**, dérivée exactement de l'écart. -/
def PZeroPassageRelationNull (tPassage : TZeroPassage) : Prop :=
  rZeroPassageHeightGap tPassage = 0

/-- **La non-nullité de la relation elle-même.** -/
def PZeroPassageRelationNonNull (tPassage : TZeroPassage) : Prop :=
  ¬ PZeroPassageRelationNull tPassage

/-- **L'écart d'un passage est toujours non négatif.**  Acquis en O7 ; il ne
sera jamais re-supposé en aval, et surtout jamais posé strictement positif. -/
theorem thm_zeroPassage_heightGap_nonnegative (tPassage : TZeroPassage) :
    0 ≤ rZeroPassageHeightGap tPassage :=
  thm_zeroPairHeightGap_nonnegative tPassage.precedes

/-- **Un passage est nul exactement quand ses deux extrémités sont à la même
hauteur**, donc dans la même fibre. -/
theorem thm_zeroPassage_null_iff_sameHeight (tPassage : TZeroPassage) :
    PZeroPassageRelationNull tPassage ↔
      rZeroHeight tPassage.zEarlierMember =
        rZeroHeight tPassage.zLaterMember :=
  thm_zeroPairHeightGap_zero_iff_sameFiber _ _

/-- **Non nul équivaut à écart strictement positif.**  C'est le pas exact que la
démonstration utilisera : un écart déjà non négatif qui n'est pas nul est
strictement positif. Ce lemme ne fournit toutefois pas la non-nullité : celle-ci
doit être produite par un theorem scientifique séparé. -/
theorem thm_zeroPassage_nonNull_iff_gapPositive (tPassage : TZeroPassage) :
    PZeroPassageRelationNonNull tPassage ↔ 0 < rZeroPassageHeightGap tPassage := by
  constructor
  · intro hNonNull
    exact lt_of_le_of_ne (thm_zeroPassage_heightGap_nonnegative tPassage)
      (fun hEq => hNonNull hEq.symm)
  · intro hPositive hNull
    exact absurd hNull (ne_of_gt hPositive)

/-! ## 3. R-PASS — transport membre-sensible des extrémités -/

/-- **R-PASS : ce qu'une application doit conserver pour mériter le nom de
transport membre-sensible du passage.**

Le type des images reste abstrait. La condition contient exactement :

* **entrée** — l'extrémité d'entrée de l'image est l'image de l'extrémité
  d'entrée du passage ;
* **sortie** — de même pour l'extrémité de sortie.

L'ordre et le voisinage sont portés par les deux premières clauses : l'image
tient ses deux extrémités des deux extrémités propres du passage, prises dans
leur ordre, et jamais d'un membre étranger.

La nullité n'apparaît ni comme argument ni comme champ parce qu'elle est déjà
une projection déterministe du passage source donné à `fnTransport`. Elle
n'est donc ni perdue ni reposée. Cette définition n'affirme en revanche pas
que la nullité du gap source devient l'égalité des deux images. -/
def PIsMemberSensitivePassageTransport
    {TImageMember : Type*} {TImageRelation : Type*}
    (fnImageEarlierEndpoint fnImageLaterEndpoint : TImageRelation → TImageMember)
    (fnMemberImage : TNonTrivialZetaZero → TImageMember)
    (fnTransport : TZeroPassage → TImageRelation) : Prop :=
  ∀ tPassage : TZeroPassage,
      fnImageEarlierEndpoint (fnTransport tPassage) =
        fnMemberImage tPassage.zEarlierMember ∧
      fnImageLaterEndpoint (fnTransport tPassage) =
        fnMemberImage tPassage.zLaterMember

variable {TImageMember TImageRelation : Type*}
variable {fnImageEarlierEndpoint fnImageLaterEndpoint : TImageRelation → TImageMember}
variable {fnMemberImage : TNonTrivialZetaZero → TImageMember}
variable {fnTransport : TZeroPassage → TImageRelation}

/-- **Les deux extrémités de l'image sont les images des deux extrémités
propres du passage.**  Aucune substitution de membre n'est exprimable. -/
theorem thm_rpass_endpoints_are_member_own
    (hTransport :
      PIsMemberSensitivePassageTransport fnImageEarlierEndpoint
        fnImageLaterEndpoint fnMemberImage fnTransport)
    (tPassage : TZeroPassage) :
    fnImageEarlierEndpoint (fnTransport tPassage) =
        fnMemberImage tPassage.zEarlierMember ∧
      fnImageLaterEndpoint (fnTransport tPassage) =
        fnMemberImage tPassage.zLaterMember :=
  hTransport tPassage

end RHV3Lean
