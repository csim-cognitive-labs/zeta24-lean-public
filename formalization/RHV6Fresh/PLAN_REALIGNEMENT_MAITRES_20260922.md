# RHV6 — plan de réalignement des trois maîtres et de CLAUDE.md — 2026-09-22

Décision de l'utilisateur (2026-09-22) : plan accepté avec la correction suivante, qui prime sur
toute formulation antérieure du REX.

## 0. La route à formaliser (fixée par l'utilisateur)

```text
ρ vrai zéro de ζ
→ (β, T)
→ Tour propre complète
→ état propre de cette Tour
→ (C⁻, C⁺)
```

puis, et seulement ensuite :

```text
(C⁻, C⁺) → comptage Von Mangoldt / Chebyshev → p_constaté
```

Certification inverse : `(C⁻, C⁺) → (T, β)` ; d'où la boucle
`ρ → (T, β) → Tour → (C⁻, C⁺) → (T, β)`.

La Tour n'existe que parce que `(β, T)` sont issus d'un vrai zéro de ζ ; un point synthétique
`(β, T)` n'a pas de Tour. Un éventuel entier `k` est **interne à l'état propre**, jamais fourni par
un premier, un rang, une occurrence, un minimum attendu ou un comptage.

Hors droite critique : le miroir `(1−β, T)` est un second vrai zéro ; sa Tour est produite par
**le même constructeur** ; son premier constaté est comparé au minimum `p_min` obtenu
indépendamment par la progression déjà démontrée.

Correction imposée à l'étape Lean 1 : elle ne dit **pas** « contacts propres = paire k=0 ».
Le fichier `AuthenticContacts.lean` appelle lui-même cette paire « paire de contrôle », et les
contacts historiques authentiques sont aux adresses 4, 10, 14, 22, … (contacts
2,7119/3,3869 ; 4,7971/5,5703 ; …).

## 1. Causes racines retenues (REX, toutes côté Lean ou documentation)

| # | Cause racine | Preuve |
|---|---|---|
| RC0 | Le seul producteur prime-free compilé (`authenticContacts` = état k=0, RHV4/RHV5) a été rétrogradé en « contrôle » le 2026-09-14 puis interdit par CLAUDE.md §4 sur la base d'E071, qui le comparait à des contacts historiques eux-mêmes sélectionnés par un pivot premier. On a jugé le producteur légitime à l'aune de références interdites. | `RHV5Fresh/Tower/AuthenticContacts.lean` l.152–158 ; E071 `FIXED_ORIGIN_2_SELECTOR… = 0/165` ; E65 : « le choix historique de l'occurrence de contact dans E45 était aligné sur l'événement/pivot » |
| RC1 | `RHV6Fresh/Tower/TrueTower.lean` : `TrueTower` ne porte que `incidence : ℤ → ℝ`. La Tour Lean est une famille sans contact propre ; chaque implémentation doit ensuite inventer d'où vient `k`. | fichier, 77 lignes, aucun champ contact |
| RC2 | Tous les substituts de `k` (pivot premier, occurrence, `cellStage`, seuil 2, hauteur, `J(z)`) sont soit fournis par un premier, soit équivalents à RH une fois compilés. | `advances_iff_riemannHypothesis`, `reaches_and_below_iff_riemannHypothesis`, `firstTourBelow_cellStage_iff_riemannHypothesis` |
| RC3 | Méthode « terminal d'abord » : la contradiction finale a été écrite avant le producteur, puis le producteur cherché pour la satisfaire. | historique des commits 02a6de82 → aebc7319 |
| RC4 | Le maître Lean donne des signatures élidées (`authenticJourneyState (b) := ...`) au lieu d'une stratégie de production. | RHV6_STRATEGIE_LEAN.md, correction §4 |
| RC5 | CLAUDE.md prescrit les autorités RHV5, la branche `k(β,T,p)` fournie par un premier, « dériver p(z) puis k », le terminal SAME EVENT : contradictoire avec les maîtres RHV6 et avec la règle « aucun premier en entrée ». | CLAUDE.md §1–§5 |
| RC6 | Les trois maîtres portent le titre RHV5, 2 973 lignes d'archives identiques chacun, et du vocabulaire interdit (mâchoire, hauteur, J(z), stage, barreau) dans le corps normatif. | `diff` des trois blocs d'archives = identique |
| RC7 | Des constats numériques sur la droite (88/300) ont été rapportés comme réfutations alors qu'ils ne portaient que sur une loi annexe (cellule propre) jamais énoncée par les maîtres. | mémoire de session, AUDIT_COMPTAGE_DIRECT_MIROIR |

Aucun énoncé du maître sémantique n'est réfuté.

## 2. Faits vérifiés sur les producteurs prime-free existants

1. `betaTContactState z` (RHV3Lean) = état aux incidences 0 et 1, formules
   `C⁻ = exp(φ/T)`, `C⁺ = exp((φ+π)/T)`, `φ = atan(T/β)`. Boucle
   `ρ → (β,T) → (C⁻,C⁺) → (β,T)` compilée (`thm_decodedHeight_eq_zeroHeight`,
   `thm_decodedRadialPosition_eq_zeroRadialPosition`, `thm_contacts_decode_same_member`,
   `thm_same_true_contacts_same_member`). Pour tout zéro publié, `C⁺ < 2` dès `T > 6,8`.
2. `canonicalTrueTowerState z` (RHV3Lean, `CanonicalTrueTowerState.lean`) = plus petite
   adresse dont l'incidence atteint 2 : `κ*(z) = ⌈max(0, (T log 2 − φ)/π)⌉`. Prime-free.
   Ne reproduit aucun contact historique (0/165, E071).
3. Contacts historiques E45/E65/E071 (15 zéros) : adresses 4, 10, 14, 22, 26, 33, 37, 42, 50,
   53, 60, 66, 70, 74, 81 = `⌊(T log p − φ)/π⌋` pour le pivot `p` = 3, 5, 7, 11, … (163/165).
   Ils sont **sélectionnés par un premier**. Ce n'est pas une donnée admissible pour produire
   l'état propre ; c'est un **test de fidélité a posteriori** du producteur.
4. Contrat historique RHV3 (`rhv3_lean/CONTRACTS.md`, O3) : l'état propre de la Tour comprend
   « le membre unique ; la phase ; la vitesse de rotation ; la famille des rayons ;
   **l'incidence d'entrée** ; le nombre d'étages ; le dernier rayon », avec l'interdiction de
   choisir l'incidence d'entrée depuis un premier, un rang, un comptage ou une histoire
   première. Aucun document ni fichier du dépôt ne donne la règle de l'incidence d'entrée.
5. Le maître sémantique RHV5 (§10–§11, archivé) exigeait déjà : « voyage géométrique
   → sélection unique k*(z) → vrais contacts », producteur « Tour-intrinsèque : phase,
   rotation, position radiale, angle/incidence et événement géométrique terminal ». Cette
   obligation n'a jamais été transcrite ; elle a été remplacée par des sélecteurs.

## 3. Le point exact à imposer avant toute réécriture Lean terminale

**Obligation O-ENTRÉE (incidence d'entrée de la Tour propre).**

La Tour propre complète d'un vrai zéro porte un état propre unique. Cet état est déterminé par
les seules données de la Tour (phase `φ = atan(T/β)`, vitesse de rotation `T`, famille des
rayons `φ + kπ`, incidence d'entrée). Ses deux contacts `(C⁻, C⁺)` sont les deux incidences
consécutives de cet état. La coordonnée `k` de l'état est une **lecture** de l'état dans la
famille, jamais une **entrée** du producteur.

Les maîtres doivent :

- SÉMANTIQUE : dire en prose que la Tour propre a une incidence d'entrée déterminée par sa
  propre mécanique, que ses deux contacts sont ceux de cet état, et que rien de premier n'entre.
- MATHÉMATIQUE : donner les formules de la Tour (phase, vitesse, rayons, incidences,
  largeur, inversion), écrire l'état propre comme `(C⁻, C⁺) = (C_{k*}, C_{k*+1})` avec `k*`
  fonction de `(β, T)` seuls, énoncer le test de fidélité a posteriori
  `k*(z) = ⌊(T log p − φ)/π⌋` sur les 15 zéros historiques (statut : VÉRIFICATION, jamais
  DÉFINITION), et marquer la caractérisation de `k*` comme **obligation ouverte** tant que la
  mécanique historique ne l'a pas fournie.
- LEAN : imposer l'étape L1 = `properTowerOf : (z) → TrueTower z` avec champs
  `contactMinus / contactPlus` produits par la mécanique de la Tour, théorèmes de largeur,
  de loi tangentielle, de décodage `(β, T)` et d'injectivité ; interdire tout terminal tant que
  L1 n'est pas produite avec sa preuve de fidélité ; retirer `baseContacts`/k=0 comme
  « contacts propres » (contrôle analytique seulement).

Ce qui est **interdit** pour produire `k*` : premier, rang, occurrence, `p_min`, comptage,
seuil arithmétique (2 ou autre), hauteur, choix a posteriori d'une cellule contenant un premier,
loi `J`, `stage`, `cellStage`, sélecteur quelconque prenant un premier en argument.

Ce qui est **exigé** comme test de fidélité (script sur zéros publiés Odlyzko, jamais synthétiques) :
le producteur reproduit 2,711958785357 / 3,386956682246 (Z1), 4,797132274455 / 5,570367919385
(Z2), 6,175152195952 / 7,001627926974 (Z3), 10,203703046818 / 11,313628568043 (Z4), et les
onze suivants de la table E071.

## 4. Structure cible des trois maîtres

Titre commun : `RHV6 — MAÎTRE … — 2026-09-22`. Aucune archive dans le corps. Les archives
(2 973 lignes identiques dans les trois fichiers) vont dans
`formalization/RHV6Fresh/archives/ARCHIVES_MAITRES_RHV4_RHV5_20260921.md` en **une** copie,
référencées en une ligne par chaque maître, non normatives.

### 4.1 `RHV6_STRATEGIE_SEMANTIQUE.md` — la démonstration, en prose seulement

Interdits dans ce fichier : formule, symbole mathématique, nom de fonction ou de théorème Lean,
bloc de code, acronyme codé (pas de OFF, RH, TAN-Q, GP1–GP4, M^Z, EVENT-MIN, S7, J(z), RC…),
mots « mâchoire », « hauteur » comme argument, « barreau », « stage », « étage » comme
sélecteur, « k ». On écrit « hors de la droite critique », « l'hypothèse de Riemann »,
« la partie réelle », « la partie imaginaire », « la fonction zêta ».

Sections :

1. Autorité et cascade (sémantique → mathématique → Lean → code ; aucun build ne réécrit le sens).
2. Domaine : vrais zéros non triviaux de la fonction zêta seulement ; un point synthétique du
   plan n'a pas de Tour ; tout test numérique utilise les zéros publiés.
3. Les trois objets et rien d'autre : les vrais zéros ordonnés ; la Tour propre de chaque zéro ;
   l'unique histoire des nombres premiers.
4. La Tour propre complète : produite par la partie réelle et la partie imaginaire du zéro ;
   phase, vitesse de rotation, rayons, incidences consécutives à pas interne fixe ; la partie
   réelle déplace l'origine, pas le pas.
5. L'état propre et ses deux contacts (O-ENTRÉE) : incidence d'entrée déterminée par la
   mécanique de la Tour ; deux contacts consécutifs ; la coordonnée interne est une lecture ;
   aucun premier n'entre ; les deux contacts redonnent exactement le zéro (certification
   inverse) ; deux zéros distincts n'ont jamais les mêmes contacts.
6. Le comptage aux contacts : Von Mangoldt / Chebyshev lit l'unique histoire première entre les
   deux contacts ; le premier constaté est une sortie, jamais une entrée.
7. La progression déjà démontrée et le minimum attendu : membres consécutifs → occurrence
   suivante → minimum attendu ; sa définition ignore la seconde Tour.
8. Le miroir : hors de la droite critique, la symétrie fonctionnelle donne un second vrai zéro de
   même partie imaginaire et de partie réelle complémentaire ; il a sa Tour propre par le même
   mécanisme ; ses contacts reculent (côté partie réelle inférieure à un demi), de moins d'un pas.
9. La contradiction : le premier constaté à la seconde Tour est inférieur au minimum attendu
   (déficit) alors que la progression exige qu'il l'atteigne ; ordre impossible sur deux
   premiers de la même histoire ; donc aucun zéro hors de la droite ; donc hypothèse de Riemann.
10. Interdictions absolues (liste en mots).
11. Statut de vérité : non certifiée tant qu'aucun terme Lean inconditionnel n'existe.
12. Règle anti-régression documentaire.

### 4.2 `RHV6_STRATEGIE_MATHEMATIQUE.md` — toutes les formules clés, étape par étape

Même numérotation que le sémantique (une section mathématique par section sémantique), avec :
domaine `z = β+iT`, miroir `z* = 1−β+iT` ; `φ = atan(T/β)` ; `tan(T log C) = T/β` ;
`C_k = exp((φ+kπ)/T)` ; `log C_{k+1} − log C_k = π/T` ; inversion `T = π/log(C⁺/C⁻)`,
`β = T/tan(T log C⁻)` ; état propre `(C_{k*}, C_{k*+1})`, `k* = k*(β,T)` (O-ENTRÉE, obligation
ouverte, test de fidélité E071 en VÉRIFICATION) ; injectivité ; comptage `N = π(C⁺)`,
`p_constaté = p_{N−1}` ; conversion `C⁺ < p_min ⇒ p_constaté < p_min` ; progression
`Occ(b) = p_{n(a)+1} = p_min(a)` ; miroir `φ* = atan(T/(1−β))`, `Δ = (φ* − φ)/T`,
`0 < |Δ| < π/(2T)`, recul `C_k(z*) < C_k(z)` pour `β < 1/2`, `C_k(z) < C_{k+1}(z*)` ;
contradiction `p_min ≤ p_constaté < p_min → False` ; obligations restantes nommées
(O-ENTRÉE ; déficit sur l'état propre ; borne de progression sur le même premier constaté) ;
interdictions mathématiques. Pas de nom Lean, pas de code Lean : formules seulement.

### 4.3 `RHV6_STRATEGIE_LEAN.md` — une seule stratégie holistique de production

Contenu : base = RHV3Lean par `lakefile` (jamais d'import de `formalization/*`, port seulement) ;
primitives réutilisées (`TUpperNonTrivialZetaZero`, `rTowerPhase`, `rTowerLogIncidence`,
`rTowerIncidence`, `TTrueHarmonicTowerState`, `rDecodedHeight`, `rDecodedRadialPosition`,
`zUpperMirrorZero`, `nEdgePrimeRank`, `fnPrimeAtRank`, `fnPrimeSuccessor`, `nZeroSourceIndex`,
`PIsOffCriticalLine`, `RiemannHypothesis`) ; étapes de production dans l'ordre causal :

```text
L0  Zéro : TrueZero := TUpperNonTrivialZetaZero ; aucun point synthétique.
L1  Tour propre complète : structure TrueTower z avec phase, logIncidence, incidence,
    ET contactMinus, contactPlus, entryAddress (interne) ; producteur properTowerOf z ;
    théorèmes : largeur π/T, loi tangentielle, décodage (β,T), injectivité,
    contactMinus = incidence entryAddress, contactPlus = incidence (entryAddress+1).
    PRÉREQUIS : O-ENTRÉE fournie par le maître mathématique. Tant qu'elle ne l'est pas,
    L1 porte le statut TRANSCRIPTION_REQUISE et AUCUN théorème terminal n'est écrit.
    Test de fidélité : script Odlyzko reproduisant la table E071 (15 zéros).
L2  Comptage : countedRank z := π(C⁺(z)), countedPrime z := p_(countedRank−1),
    lecture Von Mangoldt (canal unique, fixé par réflexion).
L3  Progression : expectedMinimumPrime a = p_(n(a)+1) = occurrence b (déjà compilé).
L4  Miroir : mirrorMember z := zUpperMirrorZero z ; properTowerOf (mirrorMember z) par le
    MÊME constructeur ; recul de chaque incidence pour β < 1/2 ; recul < un pas.
L5  Déficit : C⁺(properTowerOf z*) < p_min, puis countedPrime z* < p_min (conversion L2).
    Borne : p_min ≤ countedPrime z* par L3 et la lecture au même état propre.
L6  Fermeture : expected_le_counted_lt_expected_false ; ¬ lowerSide ; RiemannHypothesis.
```

Objets à supprimer du graphe (avec la raison « entrée première » ou « ↔ RH ») :
`Direct/MirrorCount.lean` §7 (`PSecondTourReaches/PFirstTourBelow/PSecondTourAdvances` sur
`stage`), §8, §10–§13 (`PTourInOwnCell`, `cellStage`, rangs de bloc, `foundPrimes`, `J`,
`journey*`) ; `Tower/AuthenticState.lean` (`authenticAddress` depuis l'occurrence) ;
`Terminal/ExpectedObserved.lean` parties `*AtAuthentic*` ; `Terminal/OffCountExperiment.lean` ;
tout `P…Law` portant une inégalité terminale. Objets conservés : `MirrorCount.lean` §1–§6, §9 ;
`Terminal/ArithmeticClosure.lean` (fermeture arithmétique ; anciennement `Terminal/AuthenticCountComparison.lean`, RC12) ; `Voyage/Progression.lean` ;
`Voyage/TowerReading.lean` ; `Tower/TrueTower.lean` (à étendre) ; `Tower/Incidences.lean` ;
`Tower/MirrorGeometry.lean` ; `Grammar/ExpectedMinimum.lean`.

Règles : 0 sorry/admit/axiome ; aucune hypothèse `P…` équivalente à RH ; aucun mot « mâchoire »
ni « hauteur » dans un nom de théorème ; zéros publiés Odlyzko pour tout script ; rapport de
build au format fixe ; `RH_FOUND=FALSE` tant qu'aucun terme inconditionnel `RiemannHypothesis`.

### 4.4 `CLAUDE.md`

Remplacer §1–§5 : autorités = les trois maîtres RHV6 (`formalization/RHV6Fresh/RHV6_STRATEGIE_*.md`)
puis le code `formalization/RHV6Fresh/RHV6Fresh/` ; supprimer la doctrine `k(β,T,p)` fournie par
un premier, « dériver p(z) puis k », SAME EVENT / M^Z=M comme terminal, E071 et l'audit
archéologique comme autorités ; §4 « retirés » ne doit plus interdire le producteur prime-free
mais interdire tout sélecteur prenant un premier ; ajouter O-ENTRÉE comme frontière déclarée ;
ajouter les règles utilisateur : zéros publiés seulement, aucune hauteur comme argument, port
jamais import, pas de J/stage/cellStage/sélecteur, bloc RÉFUTÉ/BORNÉ/SÉLECTIONS + RH_FOUND par
livraison. Conserver §7 (discipline Lean), §8 (certification), §9 (exécution) mis à jour.

## 5. Exécution (Haiku, séquentiel, un maître à la fois)

1. Extraction des archives en une copie (`archives/`), suppression des blocs d'archives et des
   manifestes de restauration des trois maîtres (mécanique, sans Haiku).
2. Haiku — maître SÉMANTIQUE (brief §4.1, sources : corps normatif actuel + correction
   terminale du 21/09 + §0–§3 du présent plan).
3. Haiku — maître MATHÉMATIQUE (brief §4.2 ; cohérence de numérotation avec le sémantique produit).
4. Haiku — maître LEAN (brief §4.3 ; noms vérifiés contre RHV3Lean et RHV6Fresh).
5. Haiku — CLAUDE.md (brief §4.4).
6. Contrôle de cohérence (grep) : titres RHV6 ; aucun mot interdit dans le sémantique ; aucun
   symbole/code dans le sémantique ; aucune référence à J(z), stage, cellStage, mâchoire,
   barreau, SAME EVENT, k=0 comme contacts propres dans les trois corps ; les trois numérotations
   alignées ; O-ENTRÉE présente dans les trois ; RH_FOUND=FALSE partout.
7. Relecture par Fable, corrections, commit.

## 6. Ce qui n'est pas dans ce plan

Aucune modification Lean n'est faite dans cette étape. La suite Lean (L1) n'est autorisée qu'une
fois O-ENTRÉE fixée dans le maître mathématique.

## 7. Bloc de livraison

```text
RÉFUTÉ    : rien dans la démonstration.
BORNÉ     : AuthenticContacts.lean compile la boucle (β,T)→(C⁻,C⁺)→(β,T) pour l'état k=0 et
            pour tout état fourni ; il ne produit pas k. canonicalTrueTowerState (seuil 2) est
            prime-free mais ne reproduit aucun contact historique (0/165). Les contacts
            historiques 2,7119/3,3869… sont sélectionnés par pivot premier (E65) : test de
            fidélité, pas producteur.
SÉLECTIONS: aucune.
RH_FOUND  : FALSE.
```

## 8. Seconde correction du 2026-09-22 — RC8 : le faux verrou O-ENTRÉE (REX de l'utilisateur)

La §3 ci-dessus (« Obligation O-ENTRÉE ») et la §6 (« L1 seulement après O-ENTRÉE ») sont
**retirées**. Elles sont conservées pour la traçabilité de l'erreur.

| RC | Constat | Preuve |
|---|---|---|
| RC8 | O-ENTRÉE répète O-ADR, obligation « ρ ↦ (κ, m) par règle canonique » ouverte dans le maître RHV2 puis **retirée le 2026-09-08** : « inférer "non déterminé" de "aucune formule fermée écrite dans le document" était un pas fautif ». Le même pas a été refait le 2026-09-22 au matin. | commit 8dffd6fa (`RHV2: withdraw O-ADR, an obligation opened in error`) ; `docs/RHV2_HANDOVER_20260908.md` l.138 |
| RC8-Lean | L'erreur est de représentation : au commit 87f84474 l'état de Tour portait {contact d'entrée, contact terminal (dernier rayon), loi de hauteur (m étages), loi tangentielle} et **lisait** κ et m (`recoveredKappa`, `recoveredSpan`). Le commit f8a880b4 l'a remplacé par {contacts consécutifs} puis par la branche principale `C⁻ = exp(φ/T), C⁺ = exp((φ+π)/T)` (k = 0). La Tour est devenue une famille statique indexée par k ; d'où `cellStage`, `J(z)`, « multiples cellules », puis le faux verrou. | `git show 87f84474:formalization/rhv3_lean/RHV3Lean/Objects/TrueTowerState.lean` ; `git show f8a880b4` (`tPrincipalBranchTowerState`) |

Correction appliquée (cascade) :

- SÉMANTIQUE §5, §11, §13 : la Tour est un mouvement unique portant une incidence d'entrée et un
  dernier rayon ; k et m sont des lectures ; aucune obligation d'incidence d'entrée.
- MATHÉMATIQUE §5.a–5.f, §11, §13 : état propre = (entrée, dernier rayon) ; loi tangentielle et loi
  de rotation ; lectures k, m ; inversion `T = mπ/log(C⁺/C⁻)`, `β = T/tan(T log C⁻)` ; injectivité
  avec m ; O-ENTRÉE révoquée ; §5.g test de fidélité relu (15/15, m = 1).
- LEAN §5, §6, §8, §9, §12, §13, §15, §17 : L1 = `ProperTower z` COMPILÉ (port de 87f84474), aucune
  formule de k, L2–L6 quantifiés sur la Tour propre portée.
- CLAUDE.md §2–§4 : O-ENTRÉE révoquée et listée parmi les directives retirées.
- Lean : `RHV6Fresh/Tower/ProperTower.lean` (build PASS, 0 sorry/admit/axiome nouveau) ;
  script `experiments/proper_state_fidelity_published.py` (zéros Odlyzko publiés).

Vérification numérique (zéros Odlyzko publiés, 9 décimales) : les 15 paires E071 satisfont les
deux lois (résidus < 2·10⁻⁹), lisent k = k_hist (à 5·10⁻¹⁰) et m = 1 (à 2·10⁻¹¹).

```text
RÉFUTÉ    : rien dans la démonstration. Réfuté côté documentation : O-ENTRÉE (doublon d'O-ADR).
BORNÉ     : L1 représente l'état propre porté (entrée, dernier rayon, deux lois, lectures,
            inversions, rigidité) ; aucun terme z ↦ ProperTower z n'est défini ni cherché ;
            L5 reste à produire sur l'état propre porté par la Tour du miroir.
SÉLECTIONS: aucune (properTowerAt z k = contrôle de cohérence, k = 0 sans privilège).
RH_FOUND  : FALSE.
```

## 9. Troisième correction du 2026-09-22 — RC9 : formulation de la conclusion et représentation des zéros hors ligne (REX de l'utilisateur)

| RC | Constat | Correction |
|---|---|---|
| RC9-a | Le recul du miroir était écrit comme ce qui est à prouver (§8/§9 SEM, « déficit » MATH §9). Le recul n'est qu'une explication ; ce qui est à prouver est que le premier pointé à l'état propre du zéro suivant hors ligne n'est pas le premier minimum attendu. | SEM §8, §9, §10, §11, §14 ; MATH §8, §9, §10, §11, §14 ; LEAN §1, §2, §8, §9, §10, §12, §13, §15, §18 ; CLAUDE.md §2, §3, §4, §5, §7. |
| RC9-b | La conclusion était formulée comme l'étude d'un déficit (`C⁺(z*) < p_min`) et d'une borne (`p_min ≤ p_constaté`). La démonstration étudie la contradiction de la progression des premiers pointés : `p_pointé(z') = p_min(z)` (progression + lecture) et `p_pointé(z') ≠ p_min(z)` (à prouver). | Idem ; L5 = `properState_points_occurrence` + `next_pointed_ne_expected`, NON_PRODUIT. |
| RC9-c | Les zéros hors ligne ne se calculent pas. La seule méthode est de copier la méthode compilée de `anthropics/formal-math/zeta23` (validée par ses auteurs mathématiciens ; même toolchain `v4.33.0-rc2`, même Mathlib `51e6992e`) et de la retranscrire. | `RHV6Fresh/Foundation/ZetaReflect.lean` : port de `Zeta23/Statement.lean`, `Defs.lean` (§3), `ZetaReflect.lean`, `Statement/Seam.lean`, `SeamClosed.lean` — `zetaReflect` (= `cMirrorSupport`, rfl), `analyticOrderAt_zeta_one_sub`, `zeta_reflect_zero`, `zeta_mult_reflect`, `mirror_multiplicity`, `zeta_window_finite`, `zetaZeroConfig`. |
| RC9-d | L'ordre des zéros n'était pas énoncé dans le maître sémantique ; il est celui de RHV3Lean (T, puis β). | SEM §2. |
| RC9-e | Les deux énoncés L5 étaient écrits comme des hypothèses (« H_lecture », « H_point », « ce qui est à démontrer »). La démonstration ne fait aucune hypothèse : un seul test de vérification V pour tout zéro, sur ou hors ligne ; ses résultats sont des constats (C_lecture, C_vérif) ; c'est la vérification qui crée la contradiction. | SEM §9, §10, §11, §14 ; MATH §9, §11, §14 ; LEAN §1, §2, §9, §18 ; CLAUDE.md §3. Aucun changement Lean. |

```text
RÉFUTÉ    : rien dans la démonstration. Réfuté côté documentation : le recul comme énoncé à prouver ;
            le déficit / la borne comme objet d'étude.
BORNÉ     : représentation des zéros hors ligne COMPILÉE (port zeta23) ; L5 (lecture du pointé à
            l'état propre porté ; pointé ≠ attendu au zéro suivant hors ligne) NON_PRODUIT.
SÉLECTIONS: aucune.
RH_FOUND  : FALSE.
```

## 10. Cinquième correction du 2026-09-22 — RC10 : la première partie de la démonstration fonde le test (REX de l'utilisateur)

| RC | Constat | Correction |
|---|---|---|
| RC10-a | Un verdict sur le maître sémantique avait été argumenté à partir de Lean produit par l'agent (circulaire, contraire à la hiérarchie SEM → MATH → LEAN). | Verdict repris en termes sémantiques seulement ; règle enregistrée. |
| RC10-b | SEM §11 disait « le travail restant est de démonstration : établir les deux constats », phrase insérée au réalignement, qui présentait les constats comme une démonstration manquante. | SEM §11 reformulée : le travail restant est la représentation et la transcription de la lecture et de la validation ; MATH §11 « à établir » → « à transcrire » ; LEAN §9 « À PRODUIRE » → « À TRANSCRIRE » ; CLAUDE.md §3. |
| RC10-c | La première partie de la démonstration (reconstruction de la grammaire première depuis les zéros par Von Mangoldt/Chebyshev, M^Z = M, fibre) n'était pas écrite dans les maîtres RHV6 alors qu'elle est compilée dans la base RHV3Lean et qu'elle rigidifie la relation zéro → premier, prouve la liaison et la progression, et fonde le test V. Les sauts premiers imprévisibles motivent le premier minimal. | SEM §6, §7, §9, §15 ; MATH §6, §7, §11, §15 ; LEAN §7.1, §9, §13, §15, §19 ; CLAUDE.md §2. Aucun changement Lean. |

```text
RÉFUTÉ    : rien dans la démonstration. Réfuté côté documentation : « travail restant de démonstration »
            (SEM §11) ; verdict fondé sur du Lean produit par l'agent.
BORNÉ     : première partie (M^Z = M, index zéro-source, occurrence, progression, fibre, comptage)
            COMPILÉE sans hypothèse ; lecture et validation (C_lecture, C_vérif) à transcrire sur
            l'état propre porté.
SÉLECTIONS: aucune.
RH_FOUND  : FALSE.
```

## 11. Sixième correction du 2026-09-22 — RC11 : chimères de multiplicité, lecture par égalité, étude du recul (REX de l'utilisateur)

**Cause racine RC11.** L'audit de clôture (LEAN §24, MATH §18, SEM §17) a produit trois « manques » qui n'étaient pas des manques de la démonstration mais des artefacts de représentation : (a) une multiplicité de rencontres avec l'axe algébrique et un « type infini » (chimère : la Tour a deux contacts, unicité dans les deux sens) ; (b) une lecture par égalité « dernier premier compté = occurrence » (transcription trop étroite : la lecture est « atteint », vérifiée 15/15) ; (c) une étude du recul transportée au successeur (le recul n'est jamais étudié : cause, jamais objet).

**Corrections.** SEM §4/§5/§8/§9/§10/§18 ; MATH §4/§5.a/§5.e/§5.g/§6/§8/§9/§10/§19 ; LEAN §2/§5/§6/§8/§9/§10/§11/§12/§13/§26/§27 ; CLAUDE.md §2–§5 ; §17 SEM, §18 MATH, §24–§25 LEAN marqués « réfutés par l'auteur ». Code : `Voyage/SuccessorRetreat.lean` et `Tower/TrueTowerAudit.lean` §1 supprimés, recul/déficit de `MirrorCount` et `mirror_logIncidence_sub` supprimés ; `Tower/TrueTowerStructure.lean`, `Direct/Reached.lean` ajoutés ; `RHV6Closure.lean` sur `reaches`. Questions closes, jamais rouvertes : multiplicité des contacts, début du mouvement, première rencontre parmi plusieurs, type infini, recul.

```text
RÉFUTÉ    : aucun énoncé de maître ; réfutées par l'auteur : les trois « frontières » de l'audit de clôture.
BORNÉ     : L0–L4 compilés sans recul ; lecture « atteint » compilée et vérifiée sur zéros publiés ;
            terme trueTowerOf (zéro → contacts) et constats 9.1/9.2 à transcrire.
SÉLECTIONS: aucune.
RH_FOUND  : FALSE.
```

## 12. RC12 — Boucle de production et de critique (2026-09-22, après la sixième correction)

Ordre : relancer la production et le challenge critique jusqu'à plus d'idées, fidèle à la contradiction exacte, sans chimère, sans question close, sans hypothèse, avec échange des rôles, validation de fidélité depuis le texte des maîtres et revue d'architecture. Exécution : deux tours de quatre agents (maître Lean §28). Résultat : aucun producteur fidèle du terme `trueTowerOf` ; tous les candidats (k = 0, k constant, seuil 2, rapport quatre, adresse grossière depuis la majoration du comptage des zéros, branche nourrie par un premier, multiplicité analytique comme nombre d'étages, habitants sans propriété, existence-unicité pour toute propriété écrite) classés interdits ou chimères avec la section du maître ; forme des constats compilée hors dépôt (sous le constat de lecture, le constat de vérification est la conclusion elle-même, transcription de SEM §9/§16) et non installée (constat en hypothèse, SEM §10). Installé : `Direct/Raccords.lean` (raccords du zéro suivant depuis `hβ`, `hab` seuls ; lecture « atteint » aux coordonnées lues ; raccord d'un étage), renommage `Terminal/ArithmeticClosure.lean`, trois corrections documentaires. Le validateur a refusé d'inscrire toute phrase rouvrant O-ENTRÉE (« aucune donnée ne détermine (k, m) ») ou assimilant un terme à une formule de k. Build PASS, RHV6Closure FAIL inchangé, RH_FOUND = FALSE.

## 13. RC13 — Septième correction : clôture relationnelle à deux Tours (2026-09-22, après RC12 et §30–§31 du maître Lean)

Constat de l'auteur : les trois maîtres avaient convergé vers une fermeture « une seule seconde Tour, p_min atteint ∧ non atteint sur le même état », qui n'est pas la clôture demandée. Ordre : deux zéros hors ligne, deux couples (β, T) et (1 − β, T), deux Tours produites séparément ; pour chacune, contacts authentiques sans premier, puis comptage Von Mangoldt, puis confrontation au même p_min(z) ; la première atteint p_min(z) (référence effective), la seconde (miroir) ne l'atteint pas ; la progression impose seulement Occ(z*) ≥ p_min(z) (z ≺ z*), jamais l'égalité, aucune hypothèse d'interposition ; aucun recul. Cascade exécutée : SEM §8/§9/§10/§11 + §19 ; MATH §8/§9/§10/§11 (formes égalité périmées de §11 alignées) + §20 ; LEAN §8/§9/§10/§11/§13/§24-III + §32 ; CLAUDE.md §2/§3/§4/§5. Code : `Terminal/TwoTowersComparison.lean` (comparaison finale compilée sur tout état porté, sans RH : `mirror_radial_ne`, `mirror_phase_ne`, `expected_le_mirror_occurrence`, `mirror_must_reach_expected`, `two_towers_contradiction`, `counted_regression`, `counted_regression_against_order`, `two_towers_false`) ; `RHV6Closure.lean` réécrit sur `mirrorMember z` (sans `exists_fiberSuccessor`, sans `hab`) ; identifiants L5 : `firstTower_reaches_expected`, `properState_reaches_occurrence`, `mirror_not_reaches_expected` ; `next_not_reaches_expected` retiré. Inspiration (jamais copie) des fins compilées de RHV3Lean (membres `offOriginalUpperMember` / `offMirrorUpperMember`, bandes comptées), RHV6 ancien MirrorCount/AuthenticCount (miroir par formules tangentielles, `countedPrimeAt`), RHV5 weld, RHV4 (sorry) : consignée au maître Lean §32-2. Audit de relecture croisée par un agent Haiku. Build par défaut PASS ; `RHV6Closure` FAIL sur `properState_reaches_occurrence` (causalement `trueTowerOf`) ; RH_FOUND = FALSE.

Rectification du même jour (ordre de l'auteur : « la deuxième, c'est p_min(z') ») : chaque Tour est confrontée au minimum attendu de SON PROPRE zéro (Tour de z ↔ p_min(z), Tour de z* ↔ p_min(z*)) ; l'exigence sur la seconde Tour est la progression elle-même appliquée à z*, constatée vraie sur la première Tour et sur les quinze zéros publiés, sans autre source ; aucune référence commune, aucun ordre z ≺ z* dans la contradiction (fait conservé hors route). Cascade : SEM §9/§10/§11 + §19 (rectification) ; MATH §9/§10/§11 + §20 (rectification) ; LEAN §9/§10/§11/§13 + §32-4 + §33 ; CLAUDE.md §2–§5. Lean : `Terminal/TwoTowersComparison.lean` réécrit (`occurrence_lt_expected`, `reaches_occurrence_of_reaches_expected`, `expected_lt_mirror_expected`, `two_towers_contradiction` sur p_min(z*), `counted_forms`, `order_facts_off_route`) ; identifiants L5 : `towerReachesExpected` (R, remplace `firstTower_reaches_expected` et `properState_reaches_occurrence`), `mirror_not_reaches_expected` (sur p_min(z*)) ; `RHV6Closure.lean` et `RHV6Demonstration.lean` réalignés. Build par défaut PASS (3851 jobs, 2 652 lignes, 60 #print axioms standard) ; `RHV6Closure` FAIL sur `towerReachesExpected` (causalement `trueTowerOf`) ; RH_FOUND = FALSE.
