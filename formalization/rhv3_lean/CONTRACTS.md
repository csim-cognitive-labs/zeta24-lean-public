# RHV3Lean — registre de production

Sources normatives RHV3, dans cet ordre :

1. `docs/RH_STRATEGIE_SEMANTIQUE.md`
2. `docs/RH_STRATEGIE_MATHEMATIQUE.md` (conversion mathématique directe du
   maître sémantique — scellement normatif ; ne porte pas le préfixe RHV2)
3. `docs/RH_STRATEGIE_LEAN.md` (matrice L01–L30 et classification exhaustive
   des modules)
4. `formalization/rhv3_lean/**`
5. présent registre `CONTRACTS.md`

    ACTIVE_SEMANTIC_MASTER      = docs/RH_STRATEGIE_SEMANTIQUE.md
    ACTIVE_MATHEMATICAL_MASTER  = docs/RH_STRATEGIE_MATHEMATIQUE.md
    ACTIVE_LEAN_MASTER          = docs/RH_STRATEGIE_LEAN.md
    ACTIVE_CODEBASE             = formalization/rhv3_lean/**
    ACTIVE_CONTRACT_REGISTRY    = formalization/rhv3_lean/CONTRACTS.md

Tous les documents RHV2, RHV2Fresh, rh_gap_criterion et archives sont
`HISTORICAL_ONLY`. Ils ne peuvent jamais modifier : le sens d'un objet RHV3 ;
le statut d'un théorème RHV3 ; l'ordre causal RHV3 ; les critères de fermeture
RHV3 ; une décision STOP/CONTINUE.

Ce fichier ne contient aucune mathématique et n'en produit aucune : il fixe ce
qui doit être écrit, dans quel ordre, et sous quelles conditions un module a le
droit d'entrer dans la racine `RHV3Lean.lean`.

## Règle d'entrée dans la racine

Un module entre dans `RHV3Lean.lean` seulement si, simultanément :

1. il compile, `sorry` = 0, `admit` = 0, aucun `axiom` nouveau ;
2. sa fiche de traçabilité § 1 du maître Lean est remplie, tous champs ;
3. il ne consomme aucune hypothèse hors de la liste des entrées déclarées de
   son objet ;
4. il matérialise T1 (`N_P=1`) lorsqu'il produit la cellule canonique et ne
   reçoit jamais la séparation des extrémités comme obligation ouverte ;
5. tous ses consommateurs en aval nomment le MÊME objet, jamais un second ;
6. sa cible Comparator DELTA existe et passe si le tour ajoute ou modifie une
   surface publique ;
7. l'audit de fidélité du tour est PASS, avec SAME-object explicites ;
8. le commit du tour est poussé sur `origin/main` et le SHA distant vérifié.

Un module/tour qui échoue à l'un de ces huit points reste hors validation. Il n'existe
pas de statut intermédiaire.

## Couche 0 — ce qui doit exister AVANT la première étape

Trois objets n'ont aucun amont et conditionnent tout le reste. Rien d'autre ne
peut être énoncé tant qu'ils ne sont pas produits.

### O2 — l'axe algébrique                                  STATUT : BODY_PRODUCED
    SURFACE LEAN   : l'axe réel positif, la coordonnée logarithmique, la suite
                     fixe des premiers, et l'ensemble des nombres trouvés d'un
                     intervalle algébrique.
    CONTRAT        : ordre total ; conversion x = e^u exacte ; chaque premier
                     isolé et fixe ; pour C- < C+, l'ensemble trouvé est fini,
                     ordonné, déterminé, EN GENERAL PLURIEL.
    RIGIDITE       : aucune lecture, aucun contact, aucun comptage ne déplace un
                     premier ni n'altère la conversion u <-> x.
    INTERDIT       : toute clause forçant l'ensemble trouvé à un singleton.

### O6 — la grammaire des écarts premiers                  STATUT : BODY_PRODUCED
    SURFACE LEAN   : la suite des premiers avec la stricte croissance et la
                     positivité de tout écart successif.
    CONTRAT        : g_n > 0 ; aucun premier strictement entre deux successifs ;
                     unicité de l'histoire première qui les porte.
    RIGIDITE       : g_n ne dépend que de n, jamais du zéro qui vient la lire ;
                     aucune lecture issue des zéros ne fabrique une seconde
                     suite d'écarts.
    ROLE           : c'est ici, et nulle part ailleurs, que vit le fait
                     primitif « aucune place nulle », dont dérive plus tard la
                     séparation des extrémités.

### O1 — le vrai zéro                                      STATUT : BODY_PRODUCED
    SURFACE LEAN   : le zéro non trivial de zêta et sa vue branche supérieure.
    CONTRAT        : hauteur ; position radiale ; multiplicité ; provenance
                     zêta, c'est-à-dire l'annulation elle-même ; identité
                     analytique du point.
    RIGIDITE       : toute la chaîne causale conserve ces cinq attributs sans
                     recalcul ni approximation.
    INTERDIT       : tout point synthétique tenant lieu de zéro.

## Couche 1 — côté zéro seul

### O7 — la grammaire des écarts de zéros                  STATUT : BODY_PRODUCED
    CONTRAT        : fibre de hauteur ; ordre membre-sensible, hauteur puis
                     position radiale ; consécutivité ; écart de hauteur.
    RIGIDITE       : l'écart est toujours >= 0, et nul si et seulement si les
                     deux membres sont à la même hauteur.

### O8 — le passage                                        STATUT : ACTIVE_PARTIAL
    CONTRAT, LISTE CLOSE : les deux extrémités ; l'ordre ; le voisinage ;
                     l'entrée et la sortie ; la nullité ou la non-nullité de la
                     relation elle-même.
    RIGIDITE R-PASS : le transport canonique produit en T2 conserve la TOTALITE
                     de ces attributs, nullité comprise. Une définition de
                     contrat ne remplace pas le theorem et son producteur.
    INTERDIT       : exposer la nullité comme une hypothèse terminale séparée du
                     transport.

### O9 — le triple                                         STATUT : BODY_PRODUCED
    CONTRAT        : deux passages ; le membre médian STRICTEMENT identique dans
                     les deux ; les deux écarts pris SEPAREMENT.
    RIGIDITE       : aucune moyenne des deux écarts ne remplace le couple.

## Couche 2 — la Tour et sa cellule

### O3 — la Tour harmonique                                STATUT : BODY_PRODUCED
    CONTRAT        : le membre unique ; la phase ; la vitesse de rotation ; la
                     famille des rayons ; l'incidence d'entrée ; le nombre
                     d'étages ; le dernier rayon.
    RIGIDITE       : la Tour ne transporte jamais deux zéros distincts à la fois.
    INTERDIT       : choisir l'incidence d'entrée ou le nombre d'étages à partir
                     d'un premier, d'un rang, d'un comptage ou d'une histoire
                     première.

### O4 — les contacts et la cellule terminale              STATUT : BODY_PRODUCED
    CONTRAT        : C- < C+ ; diamètre strictement positif ; l'inversion
                     complète des contacts vers la hauteur et la position
                     radiale ; la provenance du membre portée par cette
                     inversion, jamais reconstruite après coup.
    RIGIDITE       : l'inversion est une application, jamais multivaluée ; même
                     hauteur n'implique jamais mêmes contacts ; même donnée
                     complète de contacts implique le même membre.
    ORDRE          : la Tour précède les contacts ; les contacts précèdent la
                     cellule ; la cellule précède le comptage.

## Couche 3 — la lecture

### O10 — la rigidité de comptage                          STATUT : BODY_PRODUCED
    CONTRAT        : il LIT la cellule déjà produite ; il donne les deux rangs
                     aux bords, le cardinal de l'ensemble trouvé, puis le rang
                     CENTRAL ; il donne l'ordre, le voisinage et les écarts des
                     premiers déjà présents.
    RIGIDITE       : ces quantités sont fonctions de la cellule seule ; le
                     comptage ne crée, ne déplace et ne choisit jamais un
                     contact.
    INTERDIT       : construire la Tour, les coordonnées ou les contacts à
                     partir du comptage.

### O5 — l'occurrence première                             STATUT : BODY_PRODUCED
    CONTRAT        : le premier ; son rang ; ses deux arêtes ; son orientation ;
                     son écart ; sa PROVENANCE DE LECTURE, la cellule qui l'a
                     produite.
    RIGIDITE R-ATT : deux membres distincts ont deux occurrences distinctes,
                     par la seule composante de provenance.
    LIMITE EXACTE  : R-ATT ne donne JAMAIS la distinction des nombres premiers
                     portés. Toute étape qui a besoin de deux premiers distincts
                     s'appuie sur la loi locale, jamais sur R-ATT.

## Propriété dérivée, jamais une obligation

### Séparation des extrémités                                STATUT : A DERIVER
    Elle se déduit, en amont, de la loi locale du transport et de la positivité
    primitive des écarts entre premiers successifs (O6). Elle n'est ni une
    obligation ouverte, ni une hypothèse, ni un attribut à déclarer.

## Lois actives et propriété dérivée

    1. T1 est actif : la cellule terminale canonique contient exactement un
       premier (`N_P=1`). Il doit être produit après les contacts, jamais posé
       ni obtenu en choisissant la cellule autour d'un premier.
    2. la séparation des extrémités reste une propriété dérivée de la place
       canonique ; elle n'est jamais une obligation libre.
    3. R-PASS complet transporte le statut relationnel du même passage ; son
       terme canonique doit être produit par T2.

## Journal de production

    2026-09-09  couche 0 produite et entrée dans la racine.
                O2  Objects/AlgebraicAxis.lean
                O6  Objects/PrimeGapGrammar.lean
                O1  Objects/TrueZero.lean
                lake build : PASS ; sorry 0 ; admit 0 ;
                axiomes [propext, Classical.choice, Quot.sound].
    2026-09-09  couche 1 produite et entrée dans la racine.
                O7  Objects/ZeroGapGrammar.lean
                O8  Objects/Passage.lean
                O9  Objects/Triple.lean
                lake build : PASS ; sorry 0 ; admit 0 ;
                axiomes [propext, Classical.choice, Quot.sound].
    2026-09-09  couche 2 produite et entrée dans la racine.
                O3  Objects/HarmonicTower.lean
                O4  Objects/ContactsAndCell.lean
                dont l'INVERSION : la hauteur et la position radiale du membre
                sont RETROUVEES depuis les contacts et le nombre d'étages, donc
                même donnée complète de contacts implique le même membre.
                lake build : PASS ; sorry 0 ; admit 0 ;
                axiomes [propext, Classical.choice, Quot.sound].
    2026-09-09  couche 3 produite et entrée dans la racine.
                O10 Objects/CountingRigidity.lean
                O5  Objects/PrimeOccurrence.lean
                dont la dualité comptage/rang : l'intervalle rencontre les
                premiers exactement aux rangs a..b-1, d'où N = b - a et le rang
                central r = a + ceil(N/2) ; et R-ATT avec sa limite exacte,
                exhibée par deux occurrences de même premier et de provenances
                distinctes.
                lake build : PASS ; sorry 0 ; admit 0 ;
                axiomes [propext, Classical.choice, Quot.sound].

    2026-09-09  couche 4 produite et entrée dans la racine.
                la place et la loi locale   Objects/PlaceAndLocalLaw.lean
                le miroir fonctionnel       Objects/FunctionalMirror.lean
                la séparation des extrémités est DERIVEE, jamais posée ; les
                deux écarts du triple sont conclus strictement positifs ; le
                miroir d'un zéro hors ligne est un vrai zéro DISTINCT à la MEME
                hauteur, obtenu par conjugaison puis équation fonctionnelle.
                lake build : PASS ; sorry 0 ; admit 0 ;
                axiomes [propext, Classical.choice, Quot.sound].

    2026-09-09  JOURNAL HISTORIQUE, RÉTRACTÉ PAR QF-S03/QF-S27.
                Le rapport de la couche 2 avait declare « 7/7 attributs
                prouves » pour la Tour alors que l'adresse d'entree et le
                nombre d'etages n'avaient aucune declaration Lean : ils
                vivaient dans une fenetre parametrique sans producteur.
                La conclusion historique qui exigeait une relecture d'adresse
                ne gouverne plus la route. La surface active est directement
                membre -> Tour propre -> contacts -> inversion -> cellule.
                `audit_contracts.sh` verifie desormais mecaniquement que chaque
                attribut nomme une declaration existante ; il a ete verifie
                qu'il ECHOUE sur un realisateur inexistant.

## Reste à produire

Le compteur historique « 6 » est remplacé par le compteur issu du graphe P du
maître. Deux obligations de route supplémentaires ont été rendues visibles :

    le bridge explicite entre le triple/passage générique et la branche
    supérieure consommée par la Tour ;
    la preuve que chaque cellule canonique effectivement lue possède un ensemble
    trouvé NON VIDE, afin que son premier central soit réellement dans cette
    cellule.

Restent donc au minimum :

    le bridge de typage vers la branche supérieure ;
    un terme habitant l'opérateur canonique ;
    la non-vacuité des cellules canoniques utilisées sur la route ;
    un transport réel satisfaisant R-PASS ;
    le producteur de la loi locale sur CE MEME opérateur/transport ;
    l'existence d'un vrai passage CONSECUTIF de gap nul dans la fibre OFF ;
    la contradiction terminale sur le MEME E_OFF ;
    la conclusion RiemannHypothesis sans argument scientifique résiduel.

Toute nouvelle obligation critique découverte par l'audit de fidélité est ajoutée
immédiatement à cette table ; le compteur ne peut jamais être figé par convention.

### 2026-09-09 — T00-BOOTSTRAP — infrastructure de validation et replay cumulatif

Tour d'INFRASTRUCTURE uniquement (maître Lean § N.9, exception nommée).  Aucun
théorème scientifique, aucune obligation de route fermée.

    BUILD = PASS
    CONTRACT_AUDIT = PASS
    COMPARATOR_DELTA = PASS
    COMPARATOR_CUMULATIVE = PASS
    CHALLENGE_BLOB = aca5654b2aa5b3680d3360d107fae21298389e62
    THEOREM_NAMES_COMPARED = 38 (Certification/comparator.json, familles C0..C4)
    PERMITTED_AXIOMS = [propext, Quot.sound, Classical.choice]
    LEAN_KERNEL_REPLAY = PASS
    EXTERNAL_KERNEL_REPLAY = PASS (nanoda)
    COMPARATOR_TOOLCHAIN_ID = lean-4.33.0-rc2 / mathlib 51e6992e
    SAME_OBJECT_GATES = PASS
    FIDELITY_AUDIT = PASS

Produit : `Certification/{ChallengeDeps,Challenge,Solution,PrintAxioms}.lean`,
`comparator.json`, `comparator_manifest.json`, `CHALLENGE_FROZEN_GIT_BLOB`,
`run_comparator.sh`, `audit_fidelity.sh`, `validate_cycle.sh`, extension de
`audit_contracts.sh` (couverture Comparator + cohérence registre/manifeste),
`audits/REPLAY_LAYERS_0_4.md`, `audits/tours/T00-BOOTSTRAP.md`.

Journal historique T00 : les gardes avaient alors rejeté la loi de comptage,
selon l'ancien maître. Cette décision est révoquée par l'autorité active : T1
`N_P=1` doit désormais être produit et certifié. Les autres contrôles T00
(cible Comparator, mutation du Challenge, vocabulaire de fidélité) demeurent.

Le replay cumulatif des couches 0–4 a trouvé DEUX obligations qui n'étaient
enregistrées nulle part, et les a inscrites immédiatement :

    LL.SAME_OPERATOR      l'énoncé de la loi locale porte une fonction LIBRE
                          fnMemberCentralPrime, jamais nOperatorCentralPrime ;
                          il est donc plus faible que le maître.
    OFF.LOCAL_FINITENESS  la discrétion locale de la fibre de hauteur, entrée
                          non compensable de l'extraction du couple consécutif.

    RESIDUAL_OBLIGATIONS_BEFORE = 8
    RESIDUAL_OBLIGATIONS_AFTER  = 10

Ce n'est pas une régression de production : c'est une correction du compteur.

Prochaine obligation dans l'ordre causal § P / § Q.7 : `S4.INHABITANT`.

### 2026-09-09 — T01-OFF-UPPER — la fibre finie et le passage consécutif de gap nul

Premier tour scientifique après le bootstrap, autorisé par § Q.10.

    BUILD = PASS
    CONTRACT_AUDIT = PASS
    COMPARATOR_DELTA = PASS
    COMPARATOR_CUMULATIVE = PASS
    CHALLENGE_BLOB avant = aca5654b2aa5b3680d3360d107fae21298389e62
    CHALLENGE_BLOB après = fefc90e35ae520189050ba0221597b3f0703f22e
    THEOREM_NAMES_COMPARED = 44 (dont 6 nouvelles : C5-01..C5-05, ROUTE)
    PERMITTED_AXIOMS = [propext, Quot.sound, Classical.choice]
    LEAN_KERNEL_REPLAY = PASS
    EXTERNAL_KERNEL_REPLAY = PASS (nanoda)
    COMPARATOR_TOOLCHAIN_ID = lean-4.33.0-rc2 / mathlib 51e6992e
    SAME_OBJECT_GATES = PASS
    FIDELITY_AUDIT = PASS
    SCIENTIFIC_RESIDUAL_INPUT_COUNT = 0

Le blob du Challenge change par AJOUT seul : 58 insertions, 0 suppression, et
le préfixe est byte-identique à la version gelée en T00.  Aucun énoncé existant
n'est modifié.

Produit : `RHV3Lean/Objects/OffFibreAndPassage.lean`.

Trois lignes du registre passent de `—` à un réalisateur :

    OFF.LOCAL_FINITENESS                    thm_zeroHeightFiber_finite
    OFF, passage CONSECUTIF de gap nul      thm_offCriticalLine_existsNullPassage
    ROUTE, bridge vers branche supérieure   thm_passageEndpoints_upperBranch

    RESIDUAL_OBLIGATIONS_BEFORE = 10
    RESIDUAL_OBLIGATIONS_AFTER  = 7

Deux points de fidélité que ce tour tient explicitement.  La finitude n'est pas
posée : elle vient de `IsCompact.inter_riemannZetaZeros_finite`, appliquée au
compact `[0,1] x {T}` que la bande ouverte de O1 fournit, l'injectivité du
support faisant le reste.  Et la positivité de la hauteur de l'extrémité de
SORTIE du passage n'est pas supposée dans le bridge : elle est déduite de la
non-négativité de l'écart, déjà acquise en O7.

S4 n'est pas touché : sa règle de fenêtre canonique n'est pas déterminée par le
maître Lean, qui fixe `C_- = min(C1,C2)` sans définir C1 et C2.

Prochaine obligation dans l'ordre causal § P : `S4.INHABITANT`, puis
`LL.SAME_OPERATOR`.

### 2026-09-09 — T02-MACRO-CLOSURE — le porteur habité, le transport décomposé, l'universalisation

Premier MACRO-CYCLE au sens de § S : les sept fronts sont attaqués ensemble,
aucun n'attend passivement son parent.

    BUILD = PASS
    CONTRACT_AUDIT = PASS
    COMPARATOR_DELTA = PASS
    COMPARATOR_CUMULATIVE = PASS
    CHALLENGE_BLOB avant = fefc90e35ae520189050ba0221597b3f0703f22e
    CHALLENGE_BLOB après = b49d66328392410cb053714abecbc6e6d1c2c188
    THEOREM_NAMES_COMPARED = 61 (dont 17 nouvelles : familles C6 et C7)
    PERMITTED_AXIOMS = [propext, Quot.sound, Classical.choice]
    LEAN_KERNEL_REPLAY = PASS
    EXTERNAL_KERNEL_REPLAY = PASS (nanoda)
    COMPARATOR_TOOLCHAIN_ID = lean-4.33.0-rc2 / mathlib 51e6992e
    SAME_OBJECT_GATES = PASS
    FIDELITY_AUDIT = PASS
    SCIENTIFIC_RESIDUAL_INPUT_COUNT = 1

Le blob du Challenge change par AJOUT seul : le préfixe est byte-identique à la
version gelée en T01 et le contrôle `PREFIX_IDENTICAL` le confirme.  Aucun
énoncé existant n'est modifié.

Produits : `RHV3Lean/Objects/ZetaRealSegment.lean`,
`RHV3Lean/Objects/UpperRepresentative.lean`,
`RHV3Lean/Objects/CanonicalWindowRule.lean`,
`RHV3Lean/Objects/TransportOnOperator.lean`,
`RHV3Lean/Objects/Universalization.lean`. La mention historique « lois
retirées » ne gouverne plus T1, restauré par le maître actif.

Quatre lignes du registre ont été inscrites ce tour, dont DEUX SONT RETRACTEES
au tour T03 ; la rédaction ci-dessous est corrigée en conséquence et la
correction fait autorité :

    S4, habitant du type                        tRatioFourOperator          RETRACTE
    S4/O10, cellule non vide sur ce contrôle    thm_ratioFourOperator_...   RETRACTE
    LL.SAME_OPERATOR                            PLocalLawOnOperator         tenu
    TERMINAL, contradiction sur le même passage thm_sameE_...impossible     tenu, CONDITIONAL

    RESIDUAL_OBLIGATIONS_BEFORE = 7
    RESIDUAL_OBLIGATIONS_AFTER  = 3
    RESIDUAL_OBLIGATIONS_AFTER_CORRECTION_T03 = 5

Les deux rétractations sont motivées au tour T03 : exhiber un habitant d'un type
ne réalise jamais un objet dit CANONIQUE.  Aucun statut `CLOS conditionnellement`
ne doit plus être écrit : `CONDITIONAL` n'est pas `EXACT`.

Le point de fidélité central de ce tour est la DECOMPOSITION de R-PASS.  Le
maître interdit de dissimuler la conclusion dans un prédicat ; l'interdiction
est ici appliquée à R-PASS lui-même.  `thm_rpass_iff_localLaw_and_noNullPassage`
établit que R-PASS sur le porteur équivaut exactement à la loi locale sur ce
même porteur conjuguée à `PNoNullZeroPassage`, et
`thm_noNullPassage_iff_allOnCriticalLine` avec
`thm_noNullPassage_of_riemannHypothesis` établissent, dans les deux sens et par
équivalence compilée, que cette clause est de force strictement égale à
`RiemannHypothesis`.  La force résiduelle est donc NOMMEE, jamais dissimulée.

Ce n'est pas une circularité : la clause n'est dérivée de la conclusion nulle
part.  La garde d'anti-circularité de `audit_fidelity.sh` est d'ailleurs
renforcée ce tour : un théorème qui prend `RiemannHypothesis` en hypothèse doit
figurer dans `audits/RH_REVERSE_CONTROLS.txt` ET n'être référencé par aucune
autre déclaration de `RHV3Lean`.  Les deux conditions sont vérifiées
mécaniquement, et les trois gardes ont été éprouvées sur violation plantée avant
d'être crues.

Le porteur produit est un terme réel dont les contacts sont lus sur le seul
état de Tour, sans obligation d'adresse discrète. Le
module dit explicitement ce qu'il ne prétend pas : il ne fixe pas la fenêtre
CANONIQUE du maître, parce que § S4 donne `C_- = min(C1,C2)` sans définir `C1`
ni `C2`.  C'est exactement pour cela que le producteur de la loi locale reste
à matérialiser à ce tour historique. La révision §49/§T rend désormais ce
diagnostic de fenêtre obsolète : la route active est contacts-only.

    LEAN_FINAL_RH_CERTIFIED = false

### 2026-09-09 — T03-TRUE-STATE — la causalité de S4 corrigée, et deux rétractations

Macro-cycle unique.  Aucune théorie géométrique nouvelle, aucune interprétation
nouvelle : une seule correction, celle de la CAUSALITE de S4.

    BUILD = PASS
    CONTRACT_AUDIT = PASS
    SPECIFICATION_STRENGTH_AUDIT = PASS
    FIDELITY_AUDIT = PASS
    COMPARATOR_DELTA = COMPARATOR_CUMULATIVE = PASS
    CHALLENGE_BLOB avant = b49d66328392410cb053714abecbc6e6d1c2c188
    CHALLENGE_BLOB après = 909a7dfd70f9cffb1b282337ebdb907ac1f5d7b0
    THEOREM_NAMES_COMPARED = 71 (dont 10 nouvelles : famille C8)
    PERMITTED_AXIOMS = [propext, Quot.sound, Classical.choice]
    LEAN_KERNEL_REPLAY = PASS
    EXTERNAL_KERNEL_REPLAY = PASS (nanoda)
    SAME_OBJECT_GATES = PASS
    RH_EQUIVALENT_CONTRACTS = PNoNullZeroPassage
    SCIENTIFIC_RESIDUAL_INPUT_COUNT = 1

    RESIDUAL_OBLIGATIONS_BEFORE = 3
    RESIDUAL_OBLIGATIONS_AFTER  = 5

Le compte REMONTE, et c'est le résultat correct.

## La correction

L'état propre de la Tour porte désormais ses DEUX CONTACTS comme données, avec
deux lois qui ne nomment aucun entier : la loi de hauteur dit que l'écart
angulaire des deux contacts est un multiple entier du demi-tour, la loi
tangentielle dit que le contact d'entrée est une incidence de la phase propre.
Les coordonnées discrètes ne sont plus des objets de la surface active. Une
lecture indexée peut survivre dans les modules historiques comme dictionnaire
interne seulement. La cellule, le comptage, le premier central et la loi locale
sont tous relus sur les contacts du même état.

## Les deux rétractations

`tRatioFourOperator` et `thm_ratioFourOperator_cellFoundCount_positive` sont
retirés du registre.  Ils restent vrais et compilés, comme CONTROLES.  La raison
est une règle générale, désormais mécanique : exhiber un HABITANT d'un type ne
réalise jamais un objet que les maîtres appellent CANONIQUE.  Un habitant prouve
que le type n'est pas vide ; il ne fournit aucune règle de détermination, et
c'est la règle qui est l'obligation.

## Deux gardes nouvelles

`audit_strength.sh` porte les deux défauts que ni le build, ni Comparator, ni
l'audit de contrats ne peuvent voir :

    SPECIFICATION  tout habitant clos d'un type porteur doit être déclaré dans
                   `audits/CONTROL_ONLY_INHABITANTS.txt` ou
                   `audits/DERIVED_CARRIER_MAPS.txt`, et un nom qui y figure ne
                   peut pas apparaître comme réalisateur du registre.

    STRENGTH       tout contrat de force équivalente à la conclusion doit être
                   déclaré dans `audits/RH_EQUIVALENT_CONTRACTS.txt` avec ses
                   deux preuves compilées, et signalé dans le manifeste du tour.

`run_comparator.sh` exécute cet audit en ETAPE 0 et refuse de certifier quoi que
ce soit s'il échoue : Comparator compare des énoncés, il ne mesure jamais leur
force.  Les quatre scénarios de violation ont été plantés et vérifiés avant que
la moindre ligne PASS ne soit crue.

    LEAN_FINAL_RH_CERTIFIED = false

### 2026-09-09 — T04-CONTACTS-ONLY — révision normative §49/§T

Ce tour remplace l'état T03 actif par les deux vrais contacts consécutifs et
leurs deux lois exactes. Les anciens indices, fenêtres et opérateurs restent
uniquement des diagnostics historiques et sortent de la surface Comparator.

Productions kernel-validées : inversion contacts-only de la hauteur et de la
position radiale ; décodage et rigidité du membre ; porteur canonique ; cellule
directe ; provenance et occurrence sans `nSpan`/`TTowerWindow` ; comptage C3 ;
reconstruction arithmétique explicite `Λ → ψ → J → π` reliée aux deux bords de
la même cellule ; place de passage construite depuis le rang de l'occurrence
d'entrée ; tous les consommateurs triple, OFF, SAME-E et universalisation
conservés.

La surface active laisse quatre corps Lean à matérialiser, inscrits par des
tirets dans la table : non-vacuité des cellules canoniques, succession de
l'occurrence de sortie, conservation membre-sensible de la nullité sur ce même
passage, et theorem final sans hypothèse. Aucun de ces corps n'est requalifié en
question mathématique.

    LEAN_FINAL_RH_CERTIFIED = false

## Table des réalisateurs — contrôlée mécaniquement par `audit_contracts.sh`

Rétraction de fidélité T05 : `exp(phi/T), exp((phi+pi)/T)` est la seule
incidence zéro. Les cellules historiques Z1--Z4 proviennent respectivement des
incidences diagnostiques 4, 10, 14 et 22. Les deux lois de l'état inversent
une paire donnée mais ne déterminent pas cette incidence. En conséquence,
`tPrincipalBranchCarrier` est CONTROL_ONLY et aucun porteur canonique n'est
enregistré ci-dessous. `RHV2Master.lean` confirme indépendamment que la
non-vacuité/localisation de la cellule est sa première obligation non dérivée.

Chaque attribut constitutif d'un objet doit nommer la déclaration Lean qui le
porte. Un attribut sans réalisateur s'écrit `—` et est compté comme NON PRODUIT.
Aucun pourcentage de fidélité ne peut être écrit sans passer par cette table :
un rapport antérieur a déclaré « 7/7 attributs prouvés » pour la Tour alors que
l'adresse d'entrée et le nombre d'étages n'avaient AUCUNE déclaration.

| objet | attribut | réalisateur |
|---|---|---|
| O1 | hauteur | rZeroHeight |
| O1 | position radiale | rZeroRadialPosition |
| O1 | multiplicité | nZeroMultiplicity |
| O1 | provenance zêta | thm_zeroProvenance_zeta |
| O1 | identité analytique | thm_zero_identity_of_sameSupport |
| O1 | rigidité de transport | thm_zeroAttributes_are_functions_of_support |
| O2 | ordre total | thm_algebraicAxis_log_lt_log_iff |
| O2 | conversion exacte | thm_algebraicAxis_exp_log |
| O2 | conversion exacte inverse | thm_algebraicAxis_log_exp |
| O2 | ensemble trouvé | sAlgebraicIntervalFoundPrimes |
| O2 | ensemble trouvé ordonné | thm_foundPrimes_sorted |
| O2 | ensemble trouvé pluriel | thm_foundPrimes_generallyPlural |
| O2 | rigidité de transport | thm_foundPrimes_determined_by_endpoints |
| O2 | aucun premier déplacé | thm_foundPrimes_no_prime_is_moved |
| O6 | positivité stricte de l'écart | thm_primeGap_positive |
| O6 | ordre des premiers | thm_primeAtRank_strictMono |
| O6 | voisinage, corridor vide | thm_noPrimeStrictlyBetweenSuccessivePrimes |
| O6 | unicité de l'histoire première | thm_primeHistory_unique |
| O6 | rigidité de transport | thm_primeGap_depends_on_rank_alone |
| O7 | fibre de hauteur | sZeroHeightFiber |
| O7 | ordre membre-sensible | thm_zeroMemberPrecedes_iff_height_radial_lex |
| O7 | ordre séparant la fibre | thm_zeroOrderKey_injective |
| O7 | consécutivité | PZeroMembersConsecutive |
| O7 | écart de hauteur | rZeroPairHeightGap |
| O7 | rigidité, non négativité | thm_zeroPairHeightGap_nonnegative |
| O7 | rigidité, nullité et fibre | thm_zeroPairHeightGap_zero_iff_sameFiber |
| O8 | extrémités | TZeroPassage |
| O8 | ordre | precedes |
| O8 | voisinage | hConsecutive |
| O8 | nullité de la relation | PZeroPassageRelationNull |
| O8 | non-nullité de la relation | PZeroPassageRelationNonNull |
| O8 | R-PASS endpoint-only historique, insuffisant | PIsMemberSensitivePassageTransport |
| O8 | R-PASS complet, énoncé (extrémités + nullité du même passage) | PIsFullMemberSensitivePassageTransport |
| O8 | R-PASS complet implique R-PASS extrémités-only | thm_fullRpass_is_memberSensitive |
| O8 | Null_Z(E) => Null_P(Phi(E)), maître §6.2 | thm_fullRpass_null_of_sourceNull |
| O8 | NonNull_Z(E) => NonNull_P(Phi(E)), maître §6.2 | thm_fullRpass_nonNull_of_sourceNonNull |
| O8 | R-PASS, transport réel qui le satisfait | — |
| O9 | deux passages | tEarlierPassage |
| O9 | deux passages, second | tLaterPassage |
| O9 | membre médian identique | thm_triple_sameMiddleMember |
| O9 | deux écarts séparés | rEarlierZeroHeightGap |
| O9 | deux écarts séparés, second | rLaterZeroHeightGap |
| O9 | rigidité, aucune moyenne | thm_triple_mean_does_not_determine_pair |
| O3 | membre unique | thm_tTowerState_sourceZero |
| O3 | phase propre | rTowerPhase |
| O3 | vitesse de rotation | rTowerHeight |
| O3 | vrai contact inférieur porté par un état fourni | contactMinus |
| O3 | vrai contact supérieur consécutif porté par un état fourni | contactPlus |
| O3 | largeur consécutive exacte | consecutive_width |
| O3 | loi tangentielle exacte | tangent_law |
| O3 | rigidité, source unique | thm_tTowerState_injective |
| O4 | orientation des vrais contacts | ordered |
| O4 | cellule directe contacts-only | tCarrierCell |
| O4 | inversion contacts-only, hauteur | thm_decodedHeight_eq_zeroHeight |
| O4 | inversion contacts-only, position radiale | thm_decodedRadialPosition_eq_zeroRadialPosition |
| O4 | décodage du même membre | thm_contacts_decode_same_member |
| O4 | rigidité contacts-only | thm_same_true_contacts_same_member |
| O10 | rang au bord gauche | nCellLeftEdgeRank |
| O10 | rang au bord droit | nCellRightEdgeRank |
| O10 | cardinal de l'ensemble trouvé | thm_cellFoundCount_eq_edgeRankDifference |
| O10 | rangs présents dans la cellule | thm_foundPrime_iff_rank_between |
| O10 | rang central | nCellCentralRank |
| O10 | premier central réellement dans la cellule canonique | — |
| O10 | rigidité, le comptage ne déplace rien | thm_countingReads_doesNotMoveContacts |
| O10 | fonction de von Mangoldt | rVonMangoldtWeight |
| O10 | canal Chebyshev psi | rChebyshevPsiNat |
| O10 | fonction J depuis Lambda | rChebyshevJNat |
| O10 | saut de psi égal à Lambda | thm_psiJump_eq_vonMangoldt |
| O10 | saut de J reconstruit Lambda | thm_jJump_mul_log_eq_vonMangoldt |
| O10 | pi reconstruit depuis J | nPrimeCountingFromJ |
| O10 | reconstruction reliée aux deux bords et C3 | thm_vonMangoldtChebyshev_reads_same_interval |
| O5 | occurrence centrale réelle contacts-only | — |
| O5 | premier porté et rang central C3 | TPrimeOccurrence |
| O5 | provenance des deux vrais contacts | TReadingProvenance |
| O5 | R-ATT contacts-only | thm_sameCarrierProvenance_sameMember |
| O5 | occurrences distinctes des membres distincts | thm_distinctMembers_distinctCarrierOccurrences |
| ROUTE | bridge triple/passage vers branche supérieure | thm_passageEndpoints_upperBranch |
| ROUTE | le bridge ne change pas le membre | thm_zUpperOfPositiveHeight_sameMember |
| S4/O10 | cellule canonique non vide sur la route | — |
| S4 | type du porteur contacts-only | TTrueTowerCarrier |
| S4 | porteur CANONIQUE déterminé par les vrais contacts consécutifs | — |
| S4 | même état canonique threadé | — |
| S4 | lectures fonctions du seul membre | thm_carrierReadings_are_functions_of_member |
| S4 | premier central du membre | nCarrierCentralPrime |
| LOI LOCALE | place de l'histoire première | TPrimeHistoryPlace |
| LOI LOCALE | aucune place nulle | thm_place_isNeverNull |
| LOI LOCALE | corridor vide de la place | thm_place_corridorEmpty |
| LOI LOCALE | énoncé de la loi locale | PLocalLawTransportsPassageOntoPlace |
| LOI LOCALE | séparation des extrémités, dérivée | thm_endpointsDistinct_of_localLaw |
| LOI LOCALE | écart de hauteur strictement positif dérivé | — |
| LOI LOCALE | deux écarts du triple positifs dérivés | — |
| LOI LOCALE | SAME-CARRIER — énoncé porté sur la cellule contacts-only | PLocalLawOnCarrier |
| LOI LOCALE | place construite depuis le rang C3 d'entrée | fnCarrierPassagePlace |
| LOI LOCALE | extrémité d'entrée égale à p_r | thm_carrierPassagePlace_earlierEndpoint |
| LOI LOCALE | corps de succession C3(sortie)=p_(r+1) | — |
| LOI LOCALE | conservation relationnelle de nullité par R-PASS complet | — |
| MIROIR | zêta s'annule au miroir | thm_mirrorSupport_zetaVanishes |
| MIROIR | même hauteur | thm_mirror_sameHeight |
| MIROIR | distinction hors ligne critique | thm_offCriticalLine_mirror_distinct |
| MIROIR | deux membres distincts de même fibre | thm_offCriticalLineUpper_twoDistinctSameFiberMembers |
| OFF | OFF.LOCAL_FINITENESS — discretion locale de la fibre de hauteur | thm_zeroHeightFiber_finite |
| OFF | aucun membre étranger ne s'interpose dans une fibre | thm_sameFiberInterposition |
| OFF | extraction d'un couple consécutif dans la fibre | thm_existsConsecutiveInFiber |
| OFF | passage CONSECUTIF de gap nul | thm_offCriticalLine_existsNullPassage |
| OFF | nullité de la relation du passage OFF | thm_offCriticalLine_existsNullRelationPassage |
| TERMINAL | contradiction sur le même passage | — |
| ANALYTIQUE | aucun vrai zéro n'est réel | thm_noRealZetaZeroInOpenUnitSegment |
| ANALYTIQUE | hauteur d'un vrai zéro non nulle | thm_zeroHeight_ne_zero |
| ROUTE | représentant supérieur d'un membre quelconque | zUpperRepresentative |
| ROUTE | le représentant conserve la position radiale | thm_upperRepresentative_radialPosition |
| ROUTE | la branche supérieure est exhaustive | thm_allRadialPositions_of_upperBranch |
| LOI LOCALE | lecture centrale portée par le porteur contacts-only | fnCarrierMemberCentralPrime |
| LOI LOCALE | clause d'ordre de l'image | thm_rpassClause_order |
| LOI LOCALE | corridor vide de l'image | thm_rpassClause_corridorEmpty |
| O8 | R-PASS porté par le porteur | PRPassOnCarrier |
| TERMINAL | confinement dans la bande ouverte | thm_inOpenStrip_of_mathlibHypotheses |
| TERMINAL | universalisation vers l'énoncé public | thm_riemannHypothesis_of_allUpperOnCriticalLine |
| S4 | état PROPRE de Tour, deux contacts et deux lois | TTrueHarmonicTowerState |
| S4 | contact inférieur positif | contactMinus_pos |
| S4 | contact supérieur positif | contactPlus_pos |
| S4 | contacts strictement ordonnés | ordered |
| S4 | largeur exactement consécutive | consecutive_width |
| S4 | loi tangentielle | tangent_law |
| S4 | décodeur de hauteur contacts-only | rDecodedHeight |
| S4 | décodeur radial contacts-only | rDecodedRadialPosition |
| S4 | inversion de hauteur depuis les contacts | thm_decodedHeight_eq_zeroHeight |
| S4 | inversion tangentielle depuis les contacts | thm_decodedRadialPosition_eq_zeroRadialPosition |
| S4 | décodage du membre | thm_contacts_decode_same_member |
| S4 | rigidité, même paire vraie de contacts | thm_same_true_contacts_same_member |
| PORTEUR | famille d'états propres | TTrueTowerCarrier |
| PORTEUR | cellule lue sur l'état propre | tCarrierCell |
| PORTEUR | premier central lu sur l'état propre | nCarrierCentralPrime |
| PORTEUR | formule centrale C3 | thm_carrierCentralPrime_is_C3 |
| PORTEUR | cellule directement égale aux deux contacts | thm_carrierCell_contactsOnly |
| PORTEUR | occurrence directement égale aux contacts et à C3 | tCarrierPrimeOccurrence |
| PORTEUR | lectures fonctions du seul membre | thm_carrierReadings_are_functions_of_member |
| LOI LOCALE | loi locale portée par le porteur d'états | PLocalLawOnCarrier |
| O8 | R-PASS porté par le porteur d'états | PRPassOnCarrier |
| O8 | R-PASS extrémités-only équivalent à la loi locale | thm_rpass_iff_localLaw_generic |
| TERMINAL | contradiction sur le même passage, porteur d'états | — |
| TERMINAL | énoncé public depuis la conservation dérivée | — |
| TERMINAL | conclusion RiemannHypothesis | — |
| COLLISION | vrai membre OFF original | offOriginalUpperMember |
| COLLISION | vrai miroir fonctionnel du même OFF | offMirrorUpperMember |
| COLLISION | même hauteur analytique | thm_offMirror_sameHeight |
| COLLISION | membres miroir distincts sous OFF | thm_offMirror_distinct |
| COLLISION | contacts propres et potentiellement distincts | TTrueTowerCarrier |
| COLLISION | cellules propres et potentiellement distinctes | tCarrierCell |
| COLLISION | injectivité C3 depuis provenance placeIndex | — |
| COLLISION | Y.3, vrai couple OFF vers même événement/C3 | — |
| COLLISION | contradiction après Y.3 et injectivité | thm_off_impossible_by_samePrimeCollision |
| COLLISION | centralité supérieure après producteurs | thm_allUpperCentral_by_samePrimeCollision |
| COLLISION | composition RH après producteurs | riemannHypothesis_of_samePrimeCollision |
| COLLISION | theorem fermé RiemannHypothesis | — |
| S4 | contact d'entrée canonique dans la région de comptage x>=2 | thm_canonicalContactMinus_ge_two |

### 2026-09-10 — T10-CANONICAL-CONTACT-PRODUCER — le producteur causal existe, T1 reste ouvert

Recherche historique exhaustive (pas seulement HEAD) : le corpus
`formalization/rh_gap_criterion/RiemannHypothesisProof/RHV2TrueContacts.lean`
contient `canonicalContactAddress`, une règle de détermination en forme close
(plus petite adresse dont l'incidence atteint `x>=2`), fonction des seules
coordonnées propres du membre. Ce n'est ni une recherche de premier ni un
habitant arbitraire.

Conséquence précise : l'affirmation « aucun producteur canonique des contacts
n'existe » était FAUSSE et est réfutée par un contre-exemple constructif porté
dans RHV3 sans coordonnée retirée (`canonicalTrueTowerState`,
`kCanonicalContactAddress` reste interne). Les deux lois de
`TTrueHarmonicTowerState` sont obtenues par pure instanciation des théorèmes
génériques déjà prouvés — aucune preuve nouvelle des lois elles-mêmes.

Ce que ce tour NE change PAS : T1 (`N_P=1` sur la cellule de cet état)
reste `NOT_YET_CERTIFIED_LEAN`. Le corpus historique le savait déjà et gardait
l'énoncé analogue (`EveryCanonicalCenterHitsPrime`) comme proposition non
prouvée ; ce tour fait le même choix (`PCanonicalCellFoundCountOne`, définie,
non prouvée). `tCanonicalTrueTowerCarrier` reste CONTROL_ONLY : aucun maître
actuel ne désigne cette règle précise comme LA règle canonique (aucune section
« S4 »/« C1,C2 » n'existe dans les maîtres actuels — vérifié par recherche).

    BUILD = PASS (3618 jobs)
    CONTRACT_AUDIT = PASS
    SPECIFICATION_STRENGTH_AUDIT = PASS
    FIDELITY_AUDIT = PASS (T10-CANONICAL-CONTACT-PRODUCER)
    COMPARATOR_DELTA = PASS (54 cibles, Nanoda + noyau Lean)
    COMPARATOR_CUMULATIVE = PASS (54 cibles, Nanoda + noyau Lean)
    AXIOMS = [propext, Classical.choice, Quot.sound] seulement
    SORRY = 0 ; ADMIT = 0

    LEAN_FINAL_RH_CERTIFIED = false
