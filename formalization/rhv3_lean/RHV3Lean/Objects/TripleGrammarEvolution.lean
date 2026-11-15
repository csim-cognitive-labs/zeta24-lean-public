/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TowerGrammarMorphism

/-!
# RHV3Lean — le triple de Tours propres, et l'adjacence de ses deux images

    TRACE_ID              : RHV3-TRIPLE-GRAMMAR-EVOLUTION
    SEMANTIC_OBJECT       : trois membres consécutifs `zPrev -> zMid -> zNext`,
                            portant deux passages de Tour qui PARTAGENT
                            littéralement le même état propre médian, et les
                            deux images grammaticales que le morphisme produit
                            sur chacun d'eux.
    SEMANTIC_STATEMENT    : le membre médian n'est jamais recollé après coup :
                            c'est le même champ `SMid`, reçu une seule fois par
                            la structure, qui joue à la fois le rôle de sortie
                            du premier passage et d'entrée du second.  Ceci
                            donne, SANS AUCUNE HYPOTHÈSE, que l'extrémité
                            d'entrée de la seconde image grammaticale est
                            exactement le premier central PROPRE du membre
                            médian.  Ce que cela ne donne PAS, et que ce module
                            isole avec précision, c'est que l'extrémité de
                            sortie de la PREMIÈRE image coïncide avec cette même
                            extrémité d'entrée : cette adjacence est
                            EXACTEMENT `PPassageReachesOwnLaterMember` appliqué
                            au premier passage, ni plus ni moins, jamais posée.
    MATHEMATICAL_STATEMENT: ELeft = (zPrev,zMid,SPrev,SMid),
                            ERight = (zMid,zNext,SMid,SNext) ;
                            GrammarImageEarlier(ERight)
                              = nCellCentralPrime(SMid.terminalCell) — PRODUIT ;
                            GrammarImageLater(ELeft) = GrammarImageEarlier(ERight)
                              ↔ PPassageReachesOwnLaterMember(ELeft) — ÉQUIVALENCE
                              EXACTE, ni renforcée ni affaiblie.
    MATHEMATICAL_PARENT   : `TowerTransition.lean`, `TowerGrammarMorphism.lean`,
                            et le patron déjà certifié de partage médian
                            définitionnel de `Triple.lean`
                            (`thm_triple_sameMiddleMember`), relu ici au niveau
                            des états de Tour plutôt qu'au niveau des seuls
                            membres.
    PROOF_STRATEGY        : le partage du champ médian rend
                            `ELeft.SRight = ERight.SLeft` vrai par construction
                            (même champ `Tp.SMid`) ; `GrammarImageEarlier` sur
                            `ERight` se déplie exactement sur le premier
                            central de ce champ (théorème déjà produit) ;
                            l'équivalence recherchée n'est donc rien de plus
                            qu'un dépliage de la définition de
                            `PPassageReachesOwnLaterMember` sur `ELeft`, aucune
                            construction supplémentaire.
    REQUIRED_LEMMAS       : thm_grammarImageEarlier_eq_leftCentralPrime,
                            PPassageReachesOwnLaterMember
    WHY_EACH_LEMMA_EXISTS : le premier donne l'entrée produite de la seconde
                            image ; le second nomme exactement la cible dont
                            l'équivalence dépend.
    LEAN_DEFINITION       : TTowerMemberTriple, tLeftTransition, tRightTransition
    LEAN_THEOREM          : thm_triple_sameMiddleState,
                            thm_rightImageEarlier_eq_midCentralPrime,
                            thm_sameMiddlePrime_iff_reachesOwnLaterMember,
                            thm_triple_both_images_gap_positive
    SAME_MEMBER_CHECK     : `SPrev`, `SMid`, `SNext` sont les seuls champs lus ;
                            aucune substitution n'est exprimable.
    SAME_PASSAGE_CHECK    : chaque image grammaticale est fonction de SON SEUL
                            passage (`ELeft` ou `ERight`), jamais des deux à la
                            fois.
    SAME_MIDDLE_CHECK     : `thm_triple_sameMiddleState`, vrai par `rfl` — le
                            même champ `SMid` est littéralement l'extrémité de
                            sortie de `ELeft` et l'extrémité d'entrée de
                            `ERight`.  C'est de CE partage, et de lui seul, que
                            vient `thm_rightImageEarlier_eq_midCentralPrime`.
    SAME_HISTORY_CHECK    : les deux images grammaticales sont indexées dans la
                            même et unique histoire première de O6.
    FORBIDDEN_PREMISES    : poser `PPassageReachesOwnLaterMember` comme
                            hypothèse d'un théorème de clôture ; créer deux
                            rangs indépendants pour le membre médian puis
                            supposer leur égalité ; introduire un rang cible.
    NEXT_CONSUMER         : `OffGrammarDetection.lean` — la question de savoir
                            si un passage OFF, inséré dans cette même
                            structure, peut ou non satisfaire
                            `PPassageReachesOwnLaterMember`.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED — l'adjacence reste EXACTEMENT
                            équivalente à la cible non prouvée nommée dans
                            `TowerGrammarMorphism.lean`, ni plus forte ni plus
                            faible : ce module ne la prouve pas davantage, il
                            en fixe la forme exacte au niveau du triple.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

/-! ## 1. Le triple de Tours propres, membre médian partagé -/

/-- **Trois membres consécutifs et leurs trois états propres**, le champ
médian étant reçu UNE SEULE FOIS. -/
structure TTowerMemberTriple where
  /-- Le membre antérieur. -/
  zPrev : TUpperNonTrivialZetaZero
  /-- Le membre médian, partagé par les deux passages. -/
  zMid : TUpperNonTrivialZetaZero
  /-- Le membre postérieur. -/
  zNext : TUpperNonTrivialZetaZero
  /-- L'état propre du membre antérieur. -/
  SPrev : TTrueHarmonicTowerState zPrev
  /-- L'état propre du membre médian — LE MÊME dans les deux passages. -/
  SMid : TTrueHarmonicTowerState zMid
  /-- L'état propre du membre postérieur. -/
  SNext : TTrueHarmonicTowerState zNext

/-- Le passage du membre antérieur vers le membre médian. -/
def tLeftTransition (Tp : TTowerMemberTriple) : TTowerMemberTransition where
  zLeft := Tp.zPrev
  zRight := Tp.zMid
  SLeft := Tp.SPrev
  SRight := Tp.SMid

/-- Le passage du MÊME membre médian vers le membre postérieur. -/
def tRightTransition (Tp : TTowerMemberTriple) : TTowerMemberTransition where
  zLeft := Tp.zMid
  zRight := Tp.zNext
  SLeft := Tp.SMid
  SRight := Tp.SNext

/-! ## 2. RIGIDITE — le même état médian, définitionnellement -/

/-- **SAME-MIDDLE, au niveau de l'état de Tour, définitionnel.**  L'extrémité
de sortie de `ELeft` et l'extrémité d'entrée de `ERight` sont littéralement le
même champ `Tp.SMid` — pas seulement le même membre, le même état propre. -/
theorem thm_triple_sameMiddleState (Tp : TTowerMemberTriple) :
    (tLeftTransition Tp).SRight = (tRightTransition Tp).SLeft := rfl

/-! ## 3. Ce que le partage médian PRODUIT, sans hypothèse -/

/-- **L'entrée de la seconde image grammaticale est le premier central PROPRE
du membre médian.**  Conséquence directe du partage définitionnel de l'état
médian et de `thm_grammarImageEarlier_eq_leftCentralPrime` — aucune hypothèse
nouvelle. -/
theorem thm_rightImageEarlier_eq_midCentralPrime (Tp : TTowerMemberTriple) :
    GrammarImageEarlier (tRightTransition Tp) = nCellCentralPrime Tp.SMid.terminalCell :=
  thm_grammarImageEarlier_eq_leftCentralPrime (tRightTransition Tp)

/-! ## 4. Ce que le partage médian NE PRODUIT PAS — la forme exacte de la cible -/

/-- **L'ADJACENCE DES DEUX IMAGES EST EXACTEMENT `PPassageReachesOwnLaterMember`
DU PREMIER PASSAGE — ni plus, ni moins.**

Cette équivalence ne construit rien de nouveau : elle montre que la question
« les deux transitions premières produites par les deux passages du triple
se recollent-elles sur la même occurrence médiane ? » n'est PAS une question
distincte de T2, c'est LA MÊME question, relue au niveau du triple.  Aucun des
deux côtés de cette équivalence n'est reçu comme hypothèse ailleurs. -/
theorem thm_sameMiddlePrime_iff_reachesOwnLaterMember (Tp : TTowerMemberTriple) :
    GrammarImageLater (tLeftTransition Tp) = GrammarImageEarlier (tRightTransition Tp) ↔
      PPassageReachesOwnLaterMember (tLeftTransition Tp) := by
  unfold PPassageReachesOwnLaterMember
  constructor
  · intro h
    rw [h, thm_grammarImageEarlier_eq_leftCentralPrime]
    rfl
  · intro h
    rw [h, thm_grammarImageEarlier_eq_leftCentralPrime]
    rfl

/-! ## 4b. La même cible, relue au niveau des RANGS DE MEMBRE -/

/-- **SAME-MIDDLE-PRIME, relue exactement comme succession du rang du membre
médian sur le rang du membre antérieur.**

Combine `thm_sameMiddlePrime_iff_reachesOwnLaterMember` (ce module) avec
`thm_reachesOwnLaterMember_iff_rank_succ` (`TowerGrammarMorphism.lean`) : la
question « les deux images grammaticales du triple se recollent-elles sur la
même occurrence médiane ? » est EXACTEMENT « le rang canonique du membre
médian est-il le successeur du rang canonique du membre antérieur ? » —
`memberPrimeRank Tp.SMid = memberPrimeRank Tp.SPrev + 1`.  C'est la forme
exacte réclamée par le contrôle T14/§12 : ni un rang cible, ni un premier
cible, seulement une égalité de deux rangs déjà produits séparément par
`memberPrimeRank` sur `SPrev` et `SMid`.  Elle reste NON prouvée ici : aucune
hypothèse supplémentaire n'est introduite, seule la forme est rendue la plus
dépouillée possible. -/
theorem thm_sameMiddlePrime_iff_midRank_succ_prevRank (Tp : TTowerMemberTriple) :
    GrammarImageLater (tLeftTransition Tp) = GrammarImageEarlier (tRightTransition Tp) ↔
      memberPrimeRank Tp.SMid = memberPrimeRank Tp.SPrev + 1 := by
  rw [thm_sameMiddlePrime_iff_reachesOwnLaterMember,
    thm_reachesOwnLaterMember_iff_rank_succ]
  change memberPrimeRank Tp.SPrev + 1 = memberPrimeRank Tp.SMid ↔
      memberPrimeRank Tp.SMid = memberPrimeRank Tp.SPrev + 1
  exact eq_comm

/-! ## 5. Ce qui reste acquis indépendamment de l'adjacence -/

/-- **Les deux images grammaticales portent chacune un écart strictement
positif**, que l'adjacence médiane soit ou non établie : c'est la positivité
primitive de O6, appliquée séparément aux deux passages. -/
theorem thm_triple_both_images_gap_positive (Tp : TTowerMemberTriple) :
    GrammarImageEarlier (tLeftTransition Tp) < GrammarImageLater (tLeftTransition Tp) ∧
      GrammarImageEarlier (tRightTransition Tp) < GrammarImageLater (tRightTransition Tp) :=
  ⟨thm_grammarImage_gap_positive (tLeftTransition Tp),
    thm_grammarImage_gap_positive (tRightTransition Tp)⟩

/-! Surface audit. -/

#check TTowerMemberTriple
#check thm_triple_sameMiddleState
#check thm_rightImageEarlier_eq_midCentralPrime
#check thm_sameMiddlePrime_iff_reachesOwnLaterMember
#check thm_sameMiddlePrime_iff_midRank_succ_prevRank
#check thm_triple_both_images_gap_positive

end RHV3Lean
