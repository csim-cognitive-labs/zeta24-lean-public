# AUDIT — Boucle de production et de critique du 2026-09-22, analyse à rebours, interdictions fatales

Dépôt de départ : a4076a04. Maître de référence : `RHV6_STRATEGIE_LEAN.md` §28–§30. Ce fichier n'est pas une autorité (CLAUDE.md §1) ; il trace la mission.

## 1. L'identifiant qui échoue

`lake build RHV6Closure` : `RHV6Closure.lean:35:8: Unknown identifier next_not_reaches_expected`. Le terme `lowerSide_false` nomme trois identifiants absents ; Lean signale le premier rencontré dans l'élaboration (`next_not_reaches_expected`) ; causalement, `trueTowerOf` est premier (les deux constats sont énoncés sur `(trueTowerOf z').properState`), puis `properState_reaches_occurrence`.

Énoncé attendu (maître Lean §9.2) :

```lean
theorem next_not_reaches_expected {z z' : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2) (hab : PZeroMembersConsecutive z.1 z'.1) :
    ¬ reaches (trueTowerOf z').properState (expectedMinimumPrime z)
-- forme réduite (Direct/Raccords) : φ(z') + (k' + m')·π < T·log p_{n(z')},  k', m' lus sur l'état de z'
```

## 2. Versions antérieures de cet identifiant dans le projet (inventaire exhaustif, git + arbre)

| Génération, fichier, commit | Identifiant | Énoncé | Hypothèses / statut | Sort |
|---|---|---|---|---|
| RHV6, `RHV6Closure.lean`, f21fbbe7 → d9d0773d | `next_pointed_ne_expected` | `countedPrime (trueTowerOf z').properState ≠ expectedMinimumPrime z` | forme égalité ; 0/15 sur états publiés | retirée (sixième correction, LEAN §26-2) |
| RHV6, maître Lean §9, 4c6b30ac | `off_deficit_on_proper_state` | `(properTowerOf (mirrorMember z)).contactPlus < p_min(z)` | « déficit » ; `properTowerOf` avec `entryAddress` calculé | retirée (troisième correction) |
| RHV6, 4c6b30ac | `mirror_off_deficit_counted` | `countedPrime (mirrorMember z) < p_min(z)` | déficit compté | retirée |
| RHV6, 4c6b30ac | `mandatory_bound_same_counted` | `p_min(a) ≤ countedPrime (mirrorMember a)` | borne | retirée |
| RHV6, `Direct/MirrorCount.lean`, fb719b89 → a4076a04 | `mirror_deficit_of_firstTower_below` | `C⁺_k(z) < p_min(z) → C⁺_k(z*) < p_min(z)` | hypothèse `hFirst` (première Tour sous p_min) + recul `mirror_contactPlusAt_lt` | supprimée (sixième correction, recul) |
| RHV6, fb719b89 | `mirror_countedDeficit_of_firstTower_below` | forme comptée de la précédente | idem | supprimée |
| RHV5Fresh, `Off/OrientedCell.lean` | `thm_off_mirror_weld_false` | lectures orientées soudées aux occurrences `M^Z` de `z` et `z*` à un étage commun `j ≤ k` ⇒ `False` | hypothèses `hwz`, `hwz'` (soudure) + étage commun | **compilée**, jamais déchargée : « le résidu de la route est l'étage effectif du postérieur (objet S7) » |
| RHV5Fresh, `Off/MirrorOrientation.lean`, `Tower/CountingChain.lean` | `thm_sameHeight_later_cannot_reach_forward`, `thm_sameHeight_contactPlus_lt`, `thm_sameHeight_later_gain_backward` | à même ordonnée, `z ≺ w` : `C⁺_k(w) < C⁺_k(z)` pour tout `k` ; tout point au-delà de `C⁺_k(z)` est non atteint par `C⁺_j(w)`, `j ≤ k` ; gain vers l'arrière `< 1/T²` en logarithme | **sans hypothèse** ; c'est le recul (« hauteur » dans le nom) | interdites en RHV6 (nom « hauteur » ; recul jamais étudié ; aucun transport de `k`) |
| RHV3Lean, `Objects/CanonicalRiemannHypothesis.lean` | `thm_riemannHypothesis` | `POffMirrorSameReconstructedPrime → RiemannHypothesis` | une prémisse `P…` (même premier reconstruit) | conditionnelle ; « même premier » refusé comme terminal (CLAUDE.md §4) |
| RHV3Lean | `thm_offMirror_sameReconstructedPrime_contradiction` | même premier reconstruit pour `z`, `z*` ⇒ `False` | hypothèse-libre mais sur une prémisse d'égalité d'occurrences | hors terminal |
| zeta23 (`/tmp/zeta23-v1.0-audit.sRPFRG/Zeta23`, 316 fichiers) | — | aucune Tour, aucun contact, aucun « atteint » | — | seuls ponts zéros ↔ premiers : `EF_lit`/`EF_paper`, `WeilEF.full_line_identity` (formule explicite), `Ncount`/RvM (comptage `N(T)`), `Chebyshev.sum_vonMangoldt_*` ; ils bornent des sommes et des comptes, ils ne produisent aucun rayon |

Conclusion de l'inventaire : la seule version **sans hypothèse** d'un énoncé « non atteint au zéro suivant » jamais compilée est le recul à étage commun (RHV5 `thm_sameHeight_later_cannot_reach_forward`) ; toutes les autres portent une hypothèse (étage commun, soudure, première Tour sous `p_min`, prémisse `P…`). Aucune version dans zeta23.

## 3. Analyse à rebours (de la fin vers le début) et point de raccord

```text
RiemannHypothesis
  ⇐ ∀ z, ¬ β(z) < 1/2                                   riemannHypothesis_of_noLowerSide   COMPILÉ
  ⇐ ∀ z, β(z) < 1/2 → False                               lowerSide_false                    ÉCRIT
  ⇐ z' successeur consécutif, T(z') = T(z)                exists_fiberSuccessor, Raccords    COMPILÉ
  ⇐ Occ(z') = p_min(z)                                    progression_occurrence             COMPILÉ
  ⇐ reaches S' p_min(z)  ∧  ¬ reaches S' p_min(z)         reaches_and_not_reaches_false      COMPILÉ
       avec S' = (trueTowerOf z').properState
  ⇐ (i)  reaches S' Occ(z')      = C_lecture(z')          NON_PRODUIT
    (ii) ¬ reaches S' Occ(z')    = C_vérif(z, z')         NON_PRODUIT
  ⇐ S' = trueTowerOf z'                                   NON_PRODUIT
```

Fait compilé (tour 1, `lecture_iff_not_verif`, `reaches_iff_readCoordinates`) : (i) et (ii) sont, sur le même état `S'`, une inégalité et sa négation portant sur **un seul nombre**, le dernier rayon `C⁺(S') = exp((φ' + ℓ'π)/T)`, `ℓ' = k' + m'` lu : `T·log p_{n(z')} ≤ φ' + ℓ'π` et `φ' + ℓ'π < T·log p_{n(z')}`. Aucune valeur de `ℓ'` ne satisfait les deux. Le raccord ne peut donc être qu'entre **deux déterminations indépendantes** de `ℓ'` (ou de `C⁺(S')`) : l'une donnant « atteint », l'autre « non atteint ». Le point de raccord est là et nulle part ailleurs.

Ce que fournissent les maîtres pour chacune des deux déterminations :

- Détermination A (« atteint ») : SEM §9 la fonde sur la rigidité `M^Z = M` (« le comptage jusqu'au dernier rayon et l'occurrence sont lus dans la même histoire par le même canal »). Compilé : `Occ(w) = p_{n(w)}` (`occurrence_eq_primeAtRank`). Non compilé : toute inégalité entre `p_{n(w)}` et un rayon de la Tour de `w`. L'égalité `M^Z = M` identifie deux énumérations de premiers ; elle ne place aucun premier par rapport à un rayon. Aucun théorème du projet ni de zeta23 ne relie `nZeroSourceIndex` à `exp((φ + ℓπ)/T)` (grep exhaustif, tours 1 et 2).
- Détermination B (« non atteint ») : les maîtres disent qu'elle est « produite par la vérification elle-même, sur la Tour de `z'`, dont le dernier rayon est calculé par les mêmes formules » (SEM §9, MATH §9). Mais le même calcul, sur le même état, ne peut pas donner A et B. B doit venir d'un fait **extérieur à l'état de `z'`** : le seul jamais compilé est le recul à étage commun avec la première Tour (RHV5) — `C⁺_k(z') < C⁺_k(z)` — joint à `p_min(z) ∈ ]C⁺_k(z'), C⁺_k(z)]`.

## 4. Interdictions fatales (argumentées depuis le texte des maîtres)

**F1 — Le terme est exigé et toute règle le définissant est interdite.** MATH §5.e exige une fonction `z ↦ (C⁻, C⁺)(z)` (« Lean : le terme `trueTowerOf`, à produire »). MATH §5.c : « `k` et `m` sont lus sur l'état, jamais cherchés, jamais posés en entrée. Toute formule de sélection de `k` est interdite (§10) » ; MATH §5.g « Interdits pour l'état propre : … toute formule de sélection de `k` » ; SEM §10 « Traiter la coordonnée interne lue sur l'état comme une donnée d'entrée » interdit ; CLAUDE.md §3 « never look for a selection formula for `k` ». Or, en Lean, toute fonction `(z : TrueZero) → TrueTower z` est extensionnellement une règle `(β, T) ↦ (k, m)` (compilé, tour 1 : `producer_determined_by_support`, `producer_state_eq_control` ; le zéro n'a en Lean que les données `β`, `T`, `m_ρ` et des preuves). Lue à la lettre, l'interdiction porte sur **toute** définition possible du terme ; le terme reste alors indéfinissable par construction, quel que soit l'agent. Ce n'est pas une frontière scientifique : c'est une contradiction interne du texte entre « à produire » et « aucune règle ». Le validateur du tour 2 (LEAN §28-4) a refusé d'écrire « aucune donnée ne détermine `(k, m)` », à juste titre ; mais il reste que le texte ne distingue pas la **règle de production du mouvement** (celle que l'auteur nomme « projection dans le processus de création du zéro », à écrire) de la **formule de sélection nourrie par un premier ou un seuil** (interdite à bon droit). Tant que cette distinction n'est pas écrite avec la règle, F1 arrête toute production Lean.

**F2 — La vérification a besoin d'un fait extérieur à l'état de `z'`, et tout fait extérieur est interdit.** §3 ci-dessus : B ne peut pas venir du même calcul que A. Les seuls faits extérieurs jamais compilés sont le recul à étage commun (RHV5) et la première Tour sous `p_min` (RHV6 fb719b89). SEM §8 : « Aucun traitement, aucune considération, aucune explication par le recul n'entre dans la démonstration, ni comme énoncé, ni comme prémisse, ni comme lemme, ni comme transport » ; MATH §8 : « aucun transport de la coordonnée `k` de `z` vers `z*` n'est un constructeur » ; MATH §9 : « rien n'est transporté de l'une à l'autre » ; SEM §10, MATH §10 : « même hauteur ⇒ … » interdit ; CLAUDE.md §4 : « the retreat in any role (premise, explanation, lemma, transport, width) ». Sous ces interdictions, les deux Tours sont indépendantes et la vérification à `z'` est une lecture de `z'` seul : elle ne peut produire que A ou ¬A, jamais les deux. F2 arrête la production de `next_not_reaches_expected` même si `trueTowerOf` était donné.

**F3 — Ordre de grandeur (contrôle sur les zéros publiés, jamais une réfutation d'un maître).** Si la détermination B devait venir du recul à étage commun, elle exigerait `p_min(z)` dans la bande de recul sous `C⁺(z)`, de largeur logarithmique `< 1/T²` (RHV5 `thm_sameHeight_later_gain_backward`). Sur les quinze paires publiées (table MATH §5.g), la distance `log C⁺ − log p_min` vaut de 0,0002 (Z3) à 0,121 (Z1), soit de 0,2 % à 95 % de la largeur de cellule `π/T`, contre `1/T² ≤ 0,005`. Aucun zéro hors ligne n'est calculé ici ; seules les quinze paires publiées sont lues. Ce contrôle dit seulement qu'un recul « à même `k` » ne fournirait pas B en général ; il ne dit rien de la règle que l'auteur a en tête.

**F4 — Ce qui n'est pas fatal.** Les agents ont lu les bons maîtres (RHV6, chemins imposés, lecture intégrale vérifiée par le validateur). Les chimères répétées (k = 0, seuil 2, branche nourrie par un premier, habitants sans propriété, `∃!`) ne sont pas des erreurs de lecture : ce sont les seules définitions que Lean admet quand F1 interdit la règle et F2 interdit le lien ; chaque agent les a classées interdites lui-même. La répétition est le symptôme de F1 et F2, pas sa cause.

## 5. Ce que la levée de F1 et F2 exigerait de l'auteur (pas une obligation inférée : une demande de texte)

- Pour F1 : écrire, en sémantique, la règle par laquelle le mouvement de `z` projette son entrée (la « projection dans le processus de création du zéro »), en précisant qu'elle n'est pas une formule de sélection au sens de §10 ; le maître mathématique la transcrira en formule, le Lean en terme.
- Pour F2 : écrire d'où vient la détermination « non atteint » à `z'` si ce n'est ni de l'état de `z'` seul (impossible, §3) ni d'un lien avec la première Tour (interdit). Si le lien existe (recul à étage commun, ou autre), le texte doit l'autoriser sous le nom qu'il choisit ; sinon la contradiction n'a pas de source.

Horodatage : 2026-09-22T16:11Z. Signataire : Claude Fable 5.1 (modèle claude-fable-5-1).
