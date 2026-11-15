# RHV6Fresh — comptage direct à la seconde Tour (miroir), sans hauteur — 2026-09-22

Module actif : `RHV6Fresh/Direct/MirrorCount.lean`. Modules retirés de l'arbre à la demande de
l'utilisateur (toute implémentation fondée sur la hauteur est interdite) :
`Voyage/{SecondTower,Fibre,Journey,CoarseJourney,AuthenticCount}.lean` et l'audit
`AUDIT_VOYAGE_DEUX_TOURS_20260922.md`. Restent `Voyage/Progression.lean` (progression depuis les
zéros seuls) et `Voyage/TowerReading.lean` (lecture Von Mangoldt d'un état), tous deux sans hauteur.

Chaîne transcrite :

```
progression déjà prouvée
        ↓
premier minimum attendu
        │
        │       seconde Tour / contacts authentiques
        │                    ↓
        │           comptage des premiers
        │                    ↓
        │            premier constaté
        │                    │
        └──────── comparaison directe ────────┘
```

## 1. Où la hauteur n'entre plus

- La seconde Tour est `mirrorMember z := zUpperMirrorZero z`, de coordonnées `(1−β, T)`. Ses
  contacts sont recalculés par les formules tangentielles exactes
  (`mirrorMember_contactMinusAt`, `mirrorMember_contactPlusAt`). L'égalité `T* = T` est un théorème
  du miroir fonctionnel, jamais une hypothèse d'un théorème.
- Aucun `sameHeight`, aucune fibre, aucun passage nul, aucune loi « même hauteur ⇒ même étage »
  dans le graphe terminal. Les seules hypothèses des théorèmes sont `β a < 1/2` (côté à déplacement
  négatif) et, au terminal, les lois nommées §4.

## 2. Théorèmes compilés (0 sorry, 0 admit, axiomes standard)

| Étape | Théorème | Énoncé |
|---|---|---|
| progression → minimum | `expectedMinimum_le_mirror_occurrence` | `β a < 1/2 → p_{n(a)+1} ≤ occurrence (mirror a)` |
| idem, consécutif | `expectedMinimum_eq_mirror_occurrence_of_consecutive` | égalité |
| seconde Tour | `mirrorMember_contactPlusAt` | `C⁺(a*,k) = exp((atan(T/(1−β)) + (k+1)π)/T)` |
| recul | `mirror_contactPlusAt_lt`, `mirror_contactMinusAt_lt` | `β a < 1/2 → ∀k, C±(a*,k) < C±(a,k)` |
| recul < un pas | `contactMinusAt_lt_mirror_contactPlusAt` | `∀k, C⁻(a,k) < C⁺(a*,k)` |
| comptage | `countedPrimeAt_eq_vonMangoldt` | `p_constaté = p_(π_Λ(⌊C⁺⌋)−1)` |
| « +1 » impossible | `mirror_algebraicPosition_le` | `⌊C⁺(a*,k)⌋ ≤ ⌊C⁺(a,k)⌋` |
| | `mirror_countedRank_le`, `mirror_countedPrime_le` | `π(C⁺(a*,k)) ≤ π(C⁺(a,k))`, `p_constaté(a*) ≤ p_constaté(a)` |
| déficit, forme T | `mirror_contactPlusAt_lt_nextCandidate` | `C⁺(a*,k) < p_{π(C⁺(a,k))}` |
| | `mirror_countedPrime_lt_nextPrime` | `p_constaté(a*,k) < p_{π(C⁺(a,k))}` |
| déficit, forme Z | `mirror_countedDeficit_of_firstTower_below` | `C⁺(a,k) < p_min(a) → p_constaté(a*,k) < p_min(a)` |
| comparaison directe | `mirror_expected_le_counted_lt_expected_false` | `p_min ≤ p_constaté → p_constaté < p_min → False` |
| OFF → côté bas | `off_lowerSide` | OFF z → `β z < 1/2 ∨ β z* < 1/2` |
| RH | `riemannHypothesis_of_noLowerSide` | `(∀ z, ¬ β z < 1/2) → RH` |

Terminal, pour toute loi de coordonnée `stage : TrueZero → ℤ` (produite par la Tour, sans premier) :

- `riemannHypothesis_of_reaches_below stage : PSecondTourReaches stage → PFirstTourBelow stage → RH`
  avec `PSecondTourReaches := ∀ a, β a < 1/2 → p_min(a) ≤ p_constaté(a*, stage a*)` (mâchoire de
  progression, maître Lean §6) et `PFirstTourBelow := ∀ a, β a < 1/2 → C⁺(a, stage a*) < p_min(a)`.
- `riemannHypothesis_of_advances stage : PSecondTourAdvances stage → RH` avec
  `PSecondTourAdvances := ∀ a, β a < 1/2 → p_constaté(a, stage a*) < p_constaté(a*, stage a*)`.
- `riemannHypothesis_of_reads_below_sameStage stage` : lois sur **toutes** les Tours,
  `PTourReadsOccurrence` (∀ w, `occurrence w ≤ p_constaté(w, stage w)`),
  `PTourBelowExpected` (∀ w, `C⁺(w, stage w) < p_min(w)`), `PMirrorSameStage` (∀ w,
  `stage w* = stage w`) → RH.

## 2bis. Liaison collective de Von Mangoldt : fixe sous réflexion, une seule lecture

Énoncé de l'utilisateur : « L'histoire première impose que sa liaison collective de von Mangoldt
soit fixe sous réflexion et possède une seule lecture d'importance sur toute la tour orientée. »
Il n'est pas écrit sous cette forme dans les maîtres ni dans RHV3Lean ; ce qui le porte est
compilé dans `MirrorCount.lean` §9 :

| Théorème | Contenu |
|---|---|
| `vonMangoldt_channel_reflectionFixed` | la Tour et son miroir lisent le **même** canal `nPrimeCountingFromJ rChebyshevJNat` ; seul le contact change |
| `countedPrimeAt_of_contactPlus_eq` | la lecture ne dépend que du contact : contacts égaux ⇒ même premier constaté, pour deux membres quelconques |
| `countedPrimeAt_mono_oriented` | une seule loi de lecture, monotone, sur toute la Tour orientée |
| `mirror_countedPrimeAt_le_of_le` | à coordonnée commune ou antérieure, le miroir (côté `β<1/2` pour la première) constate au plus ce que la première constate |

Ce que l'énoncé ne peut pas signifier sans réactiver une route archivée : « les deux Tours miroir
constatent le **même** premier » est la collision SAME-PRIME, exclue du terminal par le maître
Lean §8, et contredite pour les occurrences par `thm_offMirror_memberMZOccurrences_distinct`
(RHV3Lean, inconditionnel). L'implémentation reflète donc la lecture « même canal, même loi »,
pas « même premier ».

## 2ter. La cible « chaque Tour lit son occurrence sans atteindre son minimum suivant »

Note reçue le 2026-09-22 : la cible n'est plus une inégalité OFF mais une coordonnée `stage`
produite par le voyage telle que chaque Tour lise son occurrence sans atteindre son minimum
suivant, transportée au miroir sans poser `PMirrorSameStage`. Deux réserves : (a) la forme
comptée du déficit demande `0 < countedRankAt` ; (b) aucun `stage` ne satisfait les trois lois.

Réponse compilée (`MirrorCount.lean` §10, 0 sorry, axiomes standard) :

| Théorème | Contenu |
|---|---|
| `countedRank_pos_of_two_le`, `countedRank_pos_of_reads` | le compte est positif dès que `C⁺ ≥ 2`, ou dès que la Tour lit au moins son occurrence (membre d'indice > 0) |
| `mirror_countedPrime_lt_nextPrime_of_two_le`, `…_of_reads` | réserve (a) levée : sur la route de lecture, la forme comptée du déficit n'a plus d'hypothèse de compte |
| `occurrence_le_counted_iff` | dualité exacte : `occurrence w ≤ p_constaté(w,k) ↔ p_{n(w)} ≤ C⁺(w,k)` |
| `reads_below_of_inOwnCell`, `inOwnCell_of_reads_below` | `PTourReadsOccurrence ∧ PTourBelowExpected` ⇔ **`p_{n(w)} ≤ C⁺(w, stage w) < p_{n(w)+1}`** pour tout membre d'indice > 0 (`PTourInOwnCell`) |
| `exists_inOwnCell_iff` | une telle `stage` existe ⇔ chaque Tour possède un contact supérieur dans sa propre cellule première |
| `no_stage_of_cell_between_contacts` | si deux contacts consécutifs encadrent strictement la cellule `[p_n, p_{n+1})`, aucune coordonnée ne convient |

La cible est donc une propriété de **chaque Tour seule** : son réseau tangentiel
`exp((φ + jπ)/T)` doit rencontrer `[p_{n}, p_{n+1})`. Aucun miroir, aucune hauteur, aucun
transport n'y entre. Elle se teste membre par membre sur les zéros connus (droite critique,
`φ = atan(2T)`), `experiments/own_cell_contact_check.py` :

| cellule testée | zéros sans contact dans la cellule (n ≤ 300) | premiers échecs |
|---|---|---|
| `[p_{n-1}, p_n)` | 79 | 18, 21, 34, 42, 46 |
| `[p_n, p_{n+1})` | 88 | 20, 26, 28, 33, 43 |
| `[p_{n+1}, p_{n+2})` | 95 | 19, 27, 34, 40, 51 |

Raison de structure : la largeur logarithmique de la cellule `log(p_{n+1}/p_n) ≈ g_n/p_n` est en
moyenne `1/n`, la période tangentielle `π/T_n ≈ log n/(2n)` est plus grande ; en périodes, la
cellule mesure en moyenne `0,73` pour `n ∈ [250, 300]` et décroît. Dès le zéro 20 (cellule
`[71, 73)`, `T = 77,145`) aucun contact n'y tombe. La loi `PTourReadsOccurrence ∧
PTourBelowExpected` est donc numériquement fausse sur la droite critique, quelle que soit la
coordonnée choisie et avant tout transport au miroir. Ce constat est numérique (aucun zéro
certifié dans Lean) ; la partie compilée est l'équivalence exacte avec la cellule propre.

Conséquence pour la cible : « chaque Tour lit **exactement** son occurrence » ne peut pas être
la loi de lecture du voyage. Une loi de lecture viable doit accepter que la Tour lise un premier
antérieur à son occurrence (contact sous `p_n`) ou postérieur au minimum suivant ; dans les deux
cas la fermeture littérale `p_min ≤ p_constaté < p_min` ne se forme plus à coordonnée commune, et
l'argument doit être reconstruit sur une autre comparaison. Rien de tel n'est produit ici.

## 2quater. Correction : la cellule complète `(C⁻, C⁺]`, la lecture plurielle, la coordonnée produite

Note reçue le 2026-09-22 (seconde) : le test §2ter est correct mais réfute une cible Lean trop
forte. `PTourInOwnCell` exigeait que le **contact supérieur** tombe dans `[p_n, p_{n+1})`, ce qui
interdit tout bond ; la vraie cellule de Tour est l'intervalle entre deux contacts consécutifs,
son ensemble de premiers est en général pluriel (cas compilé
`thm_sameHeight_sameStage_reading_plural_consistent`), et `C⁻` manquait au test. Au zéro 20 la
cellule `(70,4921, 73,4221]` contient 71 et 73 : un bond, pas un échec.

Provenance des zéros : `mpmath.zetazero` (calcul sur ζ, Riemann–Siegel), recoupé sur la table
publiée d'Odlyzko (`zeros1`, 100 000 zéros, 9 décimales ; les 300 premiers archivés dans
`experiments/data/odlyzko_zeros1_first300.txt`, sha256 `894a5320…`). Écart maximal `5·10⁻¹⁰`,
résultats identiques (`experiments/own_cell_contact_check_published.py`). Aucun zéro synthétique.

Réponse compilée (`MirrorCount.lean` §11, 0 sorry, axiomes standard) :

| Théorème | Contenu |
|---|---|
| `cellStage w = ⌈(T log p_n − φ)/π⌉ − 1` | coordonnée de la cellule complète, dérivée de l'occurrence du zéro (branche historique CLAUDE.md §2), aucun premier fourni |
| `cellStage_left`, `cellStage_right`, `cellStage_unique` | `C⁻(w, cellStage w) < p_{n(w)} ≤ C⁺(w, cellStage w)`, cellule unique |
| `reads_cellStage` | **`PTourReadsOccurrence cellStage` sans hypothèse** : la loi de lecture est instanciée, plus posée ; le bond reste permis |
| `secondTourReaches_cellStage` | `PSecondTourReaches cellStage` : la mâchoire de progression au miroir est instanciée **sans `PMirrorSameStage`** |
| `firstTourBelow_cellStage_iff_riemannHypothesis` | l'unique obligation restante, `PFirstTourBelow cellStage` (première Tour sans bond à la coordonnée de cellule de son miroir), **↔ RH** |
| `cellStage_eq_forces_plural` | si les deux Tours miroir ont la même coordonnée de cellule, la cellule de la première contient l'occurrence du miroir : plurielle, aucune contradiction |
| `cellStage_lt_of_not_plural` | si la cellule de la première Tour n'est pas plurielle, le miroir lit à une coordonnée strictement plus grande |

Lecture de la cellule complète sur les zéros publiés (`experiments/full_cell_reading_published.py`) :

| mesure (n ≤ 300, droite critique) | valeur |
|---|---|
| cellules contenant `p_n` | 300/300 (théorème) |
| cellules plurielles | 158/300 |
| cellules contenant `p_{n+1}` | 88/300 (les mêmes zéros que §2ter) |
| premiers par cellule | min 1, moyenne 1,64, max 4 |

Exemples : n=20 `(70,49, 73,42]` → {71, 73} ; n=26 `(99,72, 103,16]` → {101, 103} ;
n=100 `(538,71, 545,91]` → {541} ; n=300 `(1983,04, 1994,57]` → {1987, 1993}.

Conséquence. La progression de l'ensemble de premiers entre Tour et miroir à la coordonnée
produite est entièrement compilée : le miroir recule (`mirror_countedPrime_le`), lit au moins le
minimum attendu à sa propre coordonnée (`secondTourReaches_cellStage`), et la fermeture littérale
n'a lieu que si la première Tour est **sans bond** à la coordonnée du miroir. Cette dernière
condition, restreinte aux membres `β < 1/2`, est RH (`firstTourBelow_cellStage_iff_riemannHypothesis`),
et sa version universelle (`PTourBelowExpected cellStage`) est la condition de §2ter, fausse sur
88/300 zéros de la droite. Le cas pluriel, que les maîtres autorisent, est exactement le cas où la
comparaison same-stage ne ferme pas (`cellStage_eq_forces_plural`). Aucune autre comparaison
n'est fournie par les maîtres ; aucun terme inconditionnel `RiemannHypothesis` n'existe.

## 2quinquies. Rangs de bloc, liste ordonnée `foundPrimes`, offset grammatical (§12)

Note du relecteur : le bond n'est pas le problème ; le lemme manquant doit comparer le rang/offset
grammatical **à l'intérieur des blocs pluriels** des deux cellules, non exiger `C⁺ < p_min`.

Objets compilés (`Direct/MirrorCount.lean` §12) :

| objet | définition | fait compilé |
|---|---|---|
| `contactBlockLeftRank w k` | `π(C⁻(w,k))` | `rank_in_block_iff` : `p_r ∈ (C⁻,C⁺] ⇔ π(C⁻) ≤ r < π(C⁺)` |
| `contactBlockRightRank w k` | `π(C⁺(w,k))` (= rang compté) | `contactBlockLeftRank_le_right` |
| `foundPrimes w k` | liste `[p_{π(C⁻)}, …, p_{π(C⁺)−1}]` | `foundPrimes_sorted`, `foundPrimes_length`, `mem_foundPrimes_iff_contact` |
| `occurrenceOffset w` | `n − π(C⁻)` à `cellStage w` | `occurrence_mem_foundPrimes`, `offset_add_headroom` |
| `occurrenceHeadroom w` | `π(C⁺) − 1 − n` à `cellStage w` | `headroom_eq_zero_iff : headroom = 0 ⇔ ¬PCellPlural` |

Comparaison au miroir d'un membre `β < 1/2` (`k = cellStage z`, `k* = cellStage z*`) :

- à toute coordonnée commune, les deux rangs de bloc du miroir sont `≤` ceux de la première Tour
  (`mirror_blockLeftRank_le`, `mirror_blockRightRank_le`) ;
- **régime reculé `k* ≤ k`** : le bloc de la première Tour contient toute la progression
  `p_n, …, p_{n*}` (`firstBlock_contains_progression_of_cellStage_le`) ; l'offset du miroir dépasse
  strictement celui de la première Tour (`mirror_offset_gt_of_cellStage_le` :
  `offset z + 1 ≤ offset z*`) — **le recul ne fait pas perdre l'avance grammaticale** ; ce qu'il
  fait perdre est une unité de marge droite (`mirror_headroom_lt_of_cellStage_le` :
  `headroom z* + 1 ≤ headroom z`), donc `headroom z ≥ 1` : bond obligatoire, cas pluriel cohérent ;
- **régime avancé `k* > k`** : aucune comparaison de blocs n'est fournie par le recul ; la seule
  contrainte est la fenêtre `C⁻(z, k*−1) < p_{n*} ≤ C⁺(z, k*)` (`mirror_occurrence_window`,
  forme rang `mirror_occurrence_window_rank`) ;
- dichotomie compilée : `headroom_pos_or_cellStage_lt`.

Conséquence de la fenêtre, **nouvelle et exacte** : `not_firstTourBelow_at_lowerSide` — chez tout
membre `β < 1/2`, `p_{n+1} ≤ p_{n*} ≤ C⁺(z, k*)`, donc la première Tour lue à la coordonnée de
cellule de son miroir **atteint toujours** son minimum attendu. `PFirstTourBelow cellStage` n'est
donc jamais satisfaite de façon non vide : `firstTourBelow_cellStage_iff_noLowerSide` la compile
comme « aucun membre `β < 1/2` ». L'unique obligation restante à la coordonnée produite est donc
littéralement la conclusion visée, et le déficit de forme Z ne peut pas être instancié par
`cellStage`. Le lemme demandé (« le recul fait perdre l'avance exigée ») est **réfuté** dans le
seul régime où le recul compare les blocs, et sans contenu dans l'autre.

Numérique, zéros publiés Odlyzko, `n ≤ 300`, première Tour seule (`experiments/block_ranks_published.py`) :

| mesure | valeur |
|---|---|
| longueur de `foundPrimes` | 1 : 142, 2 : 126, 3 : 30, 4 : 2 |
| `occurrenceOffset` | 0 : 221, 1 : 69, 2 : 10 |
| `occurrenceHeadroom` | 0 : 212, 1 : 73, 2 : 15 |

Exemples : n=20 `[71, 73]` offset 0, marge 1 ; n=100 `[541]` ; n=300 `[1987, 1993]`.
Le miroir n'est pas testable numériquement (aucun zéro hors droite connu).

## 2sexies. Cellule de voyage `J(z)` : mêmes objets, comparaison `J(z)` / `J(z*)` (§13)

Correction de portée de §2quinquies : `cellStage` contient `log (occurrence w)` et l'occurrence
**est un premier** (`fnPrimeAtRank n`). `cellStage` est donc sélectionnée arithmétiquement par
l'occurrence ; ce n'est pas la cellule effectivement parcourue `J(z)` (maître Lean §10, TDD-2,
objet S7 : produit par la géométrie propre de la Tour, sans premier, rang premier ni adresse de
comptage). Aucun maître ne donne l'algorithme de `J` ; `trueTowerOf` ne porte que la famille
d'incidences. Le §13 transcrit donc les objets demandés pour **toute** loi `J : TrueZero → ℤ`, de
sorte qu'un producteur de `J` s'instancie sans rien changer.

Objets : `journeyLeftRank J w = π(C⁻(w, J w))`, `journeyRightRank J w = π(C⁺(w, J w))`,
`journeyFoundPrimes J w` (liste ordonnée), `journeyOffset`, `journeyHeadroom` ;
`journey_reads_iff_ranks`, `journey_offset_add_headroom`, `journey_headroom_eq_zero_iff`
(marge nulle ⇔ `C⁺(w, J w) < p_{n+1}`).

Lois : `PJourneyReads J` (GP1 : tout membre lit son occurrence dans sa cellule de voyage),
`PJourneyMirrorTransport J` (TDD-2 : `J z* = J z` pour `β < 1/2`), `PFirstJourneyBelow J`.

Comparaison `J(z)` / `J(z*)` (membre `β < 1/2`, `J z* ≤ J z`, GP1 aux deux membres) :
- `mirror_journey_occurrence_mem_first` : `p_{n*} ∈ journeyFoundPrimes J z` ;
- `mirror_journeyOffset_gt` : `offset z + 1 ≤ offset z*` ;
- `mirror_journeyHeadroom_lt` : `headroom z* + 1 ≤ headroom z` ;
- `blockLeftRank_le_mirror_blockRightRank` : chevauchement des blocs transportés.

Lemme visé, forme déficit — `mirror_journey_loses_reading_of_firstBelow` : première Tour sous son
minimum à `J(z)` et `J z* ≤ J z` ⇒ le miroir **ne lit pas** son occurrence à `J(z*)` : le recul lui
fait perdre l'avance grammaticale exigée par la progression.

Terminal — `riemannHypothesis_of_journey : PJourneyReads J → PJourneyMirrorTransport J →
PFirstJourneyBelow J → RiemannHypothesis`. Poids — `firstJourneyBelow_iff_noLowerSide` : sous GP1
et TDD-2, `PFirstJourneyBelow J ⇔ aucun membre β < 1/2`, pour toute `J`. Le contenu fermant doit
donc venir du producteur de `J` : il doit rendre `PFirstJourneyBelow J` (marge nulle à `J(z)`,
`journey_headroom_eq_zero_iff`) un théorème de la première Tour seule. `cellStage` satisfait GP1
(`cellStage_journeyReads`) mais pas le contrat S7.

## 3. Ce qui est établi, ce qui ne l'est pas

Établi sans hypothèse : à toute coordonnée, la seconde Tour recule, ne parcourt pas +1 sur l'axe
algébrique, et son premier constaté est strictement sous le premier qui suit le premier constaté
de la première Tour. La comparaison directe est la fermeture littérale du maître.

Non établi : la mâchoire de progression sur le premier constaté de la seconde Tour. Son poids est
compilé :

- `advances_iff_riemannHypothesis stage : PSecondTourAdvances stage ↔ RH` ;
- `reaches_and_below_iff_riemannHypothesis stage : (PSecondTourReaches ∧ PFirstTourBelow) ↔ RH`.

Raison, indépendante de toute hauteur : ces lois ne parlent que des membres `β < 1/2` ; sous RH il
n'y en a aucun, elles y sont satisfaites à vide ; et le recul étant démontré à toute coordonnée,
chacune implique RH. Les lois de §8 (`PTourReadsOccurrence`, `PTourBelowExpected`,
`PMirrorSameStage`) portent sur toutes les Tours et ne sont pas vides sous RH ; aucune `stage` ne
les satisfait dans le dépôt. `PTourReadsOccurrence ∧ PTourBelowExpected` à une même `stage` dit que
chaque Tour lit exactement son occurrence ; `PMirrorSameStage` est l'objet S7 des maîtres (étage
commun des deux Tours miroir), non produit.

## 4. RÉFUTÉ / BORNÉ / SÉLECTIONS

RÉFUTÉ (compilé) :
- « la seconde Tour peut parcourir +1 sur l'axe algébrique à coordonnée commune » :
  `mirror_algebraicPosition_le`, `mirror_countedPrime_le`.
- « la mâchoire de progression et le déficit coexistent à un même membre `β < 1/2` » :
  `lowerSide_false_of_reaches_below`.

RÉFUTÉ (numérique, portée : 300 premiers zéros, droite critique, sans miroir) :
- « il existe une coordonnée `stage` avec `PTourReadsOccurrence ∧ PTourBelowExpected` » :
  équivalent compilé à la cellule propre (`inOwnCell_of_reads_below`), fausse au zéro 20 et à
  87 autres ≤ 300 (`experiments/own_cell_contact_check.py`). Non compilé en Lean (aucun zéro
  certifié) ; la réfutation ne porte pas sur une loi de lecture qui autoriserait un premier
  antérieur à l'occurrence. **Portée corrigée (§2quater)** : elle réfute la loi « sans bond »
  `PTourBelowExpected`, pas la lecture de la cellule complète, qui est instanciée
  (`reads_cellStage`). Zéros publiés Odlyzko, résultats identiques.

BORNÉ (portée exacte) :
- La forme comptée du déficit est inconditionnelle sur la route de lecture
  (`mirror_countedPrime_lt_nextPrime_of_reads`) ; hors de cette route elle demande `C⁺ ≥ 2`.
- Le déficit en forme Z (`p_constaté(a*) < p_min(a)`) n'est prouvé que sous
  `C⁺(a, k) < p_min(a)` (première Tour sans bond à la coordonnée lue). En forme T il est
  inconditionnel.
- Le terminal est conditionnel à une loi de coordonnée `stage` et à une mâchoire de progression ;
  chaque forme restreinte aux membres `β < 1/2` est équivalente à RH (théorèmes ci-dessus).
- `PMirrorSameStage` n'est plus nécessaire à la mâchoire de progression
  (`secondTourReaches_cellStage`). Pour la coordonnée produite, `cellStage (mirror z) = cellStage z`
  force la cellule plurielle (`cellStage_eq_forces_plural`) : la géométrie same-stage ne ferme pas.
- L'unique obligation restante à la coordonnée produite est `PFirstTourBelow cellStage`, ↔ RH ;
  précisée en §2quinquies : elle est **exactement** l'absence de membre `β < 1/2`
  (`firstTourBelow_cellStage_iff_noLowerSide`), jamais satisfaite de façon non vide.
- Comparaison de blocs (§12) : ne compare que dans le régime `cellStage z* ≤ cellStage z` ; le
  régime `cellStage z* > cellStage z` n'a que la fenêtre `mirror_occurrence_window`.

BORNÉ (compilé, §12, portée corrigée en §2sexies) :
- `mirror_offset_gt_of_cellStage_le` / `not_firstTourBelow_at_lowerSide` ne portent que sur les
  cellules `cellStage`, sélectionnées par l'occurrence (un premier). Ils ne disent rien des
  cellules `J(z)`, `J(z*)` du voyage authentique.

PROUVÉ (compilé, §13, toute loi `J`) :
- le lemme visé, en forme déficit : `mirror_journey_loses_reading_of_firstBelow` ;
- la comparaison offset/marge sur `J(z)` / `J(z*)` : `mirror_journeyOffset_gt`,
  `mirror_journeyHeadroom_lt` (mêmes inégalités que pour `cellStage`, sous GP1 aux deux membres) ;
- le terminal `riemannHypothesis_of_journey`.

BORNÉ (§13) :
- le producteur de `J` (objet S7) n'existe pas : aucun maître n'en donne l'algorithme, la Tour
  Lean n'a que la famille d'incidences. Sans producteur, `PFirstJourneyBelow J` reste une
  obligation ; sous GP1 ∧ TDD-2 elle vaut « aucun membre `β < 1/2` »
  (`firstJourneyBelow_iff_noLowerSide`). Le producteur doit la rendre théorème de la première Tour
  seule (marge nulle à `J(z)`).
- `expectedMinimum_le_mirror_occurrence` n'affirme pas que le miroir est le successeur immédiat ;
  seul `n* > n` est utilisé.

SÉLECTIONS :
- côté `β < 1/2` = première Tour (déplacement négatif du miroir) ;
- comparaison à la coordonnée transportée `J z* = J z` (TDD-2) ;
- `cellStage` est sélectionnée par l'occurrence, donc par un premier : hors contrat S7, gardée
  seulement comme instance de GP1 ;
- la couche §13 ne sélectionne rien : `J` y est un paramètre.

## 5. Manifeste

```
BUILD=PASS (3848 jobs)
SORRY=0
ADMIT=0
AXIOMS=[propext, Classical.choice, Quot.sound]
HEIGHT_IN_TERMINAL_GRAPH=NONE
MIRROR_RETREAT=PROVED
PLUS_ONE_IMPOSSIBLE=PROVED
DEFICIT_T_FORM=PROVED
DEFICIT_Z_FORM=PROVED_CONDITIONAL
DIRECT_COMPARISON=PROVED
TERMINAL=PROVED_CONDITIONAL
OBLIGATION_WEIGHT=PROVED (↔ RH)
DEFICIT_COUNT_FORM_ON_READING_ROUTE=PROVED
READS_BELOW_EXACT_CONTACT_FORM=PROVED (⇔ cellule propre)
OWN_CELL_STAGE_NUMERIC=FALSE_ON_LINE (88/300, premier échec n=20 ; zéros publiés Odlyzko)
FULL_CELL_STAGE=PRODUCED (cellStage : C⁻ < p_n ≤ C⁺, unique)
TOUR_READS_OCCURRENCE=INSTANTIATED (reads_cellStage)
SECOND_TOUR_REACHES=INSTANTIATED (secondTourReaches_cellStage, sans PMirrorSameStage)
REMAINING_OBLIGATION=PFirstTourBelow cellStage (↔ RH, firstTourBelow_cellStage_iff_riemannHypothesis)
FULL_CELL_NUMERIC=plural 158/300, contains p_{n+1} 88/300, mean 1.64 primes/cell
BLOCK_RANKS=PRESENT (contactBlockLeftRank/RightRank, rank_in_block_iff)
FOUND_PRIMES=PRESENT (liste ordonnée, foundPrimes_sorted, mem_foundPrimes_iff_contact)
GRAMMATICAL_OFFSET=PRESENT (occurrenceOffset, occurrenceHeadroom, headroom_eq_zero_iff)
MIRROR_BLOCK_COMPARISON=PROVED (régime reculé : offset z+1 ≤ offset z*, headroom z*+1 ≤ headroom z)
MIRROR_OCCURRENCE_WINDOW=PROVED (C⁻(z,k*−1) < p_{n*} ≤ C⁺(z,k*))
FIRST_TOUR_BELOW_AT_CELLSTAGE=NEVER_NONVACUOUS (firstTourBelow_cellStage_iff_noLowerSide)
BLOCK_NUMERIC=length 1:142/2:126/3:30/4:2 ; headroom 0:212/1:73/2:15 (zéros publiés)
JOURNEY_CELL_LAYER=PRESENT (toute loi J : journeyLeftRank/RightRank/FoundPrimes/Offset/Headroom)
JOURNEY_CELL_PRODUCER=ABSENT (objet S7 ; cellStage = GP1 mais sélectionnée par l'occurrence)
JOURNEY_MIRROR_COMPARISON=PROVED (offset z+1 ≤ offset z*, headroom z*+1 ≤ headroom z, sous J z* ≤ J z)
JOURNEY_RETREAT_LOSES_READING=PROVED (mirror_journey_loses_reading_of_firstBelow)
JOURNEY_TERMINAL=PROVED_CONDITIONAL (riemannHypothesis_of_journey : GP1 ∧ TDD-2 ∧ PFirstJourneyBelow)
JOURNEY_REMAINING_OBLIGATION_WEIGHT=PROVED (firstJourneyBelow_iff_noLowerSide, toute J)
MANIFEST_AXIOM_LINES=68, tous [propext, Classical.choice, Quot.sound]
RH_FOUND=FALSE
```
