# E460 — Audit Φ4 du poids : où l'ordre d'annulation entre-t-il, et sélectionne-t-il les porteurs ? (2026-11-08 → 2026-11-09)

Audit par lecture, sans module, sans compilation, sans jumeau (aucun chiffre n'est produit). Maître : §19.84 (inventaire), §19.85
(rectification de portée d'E457), §19.86 (conclusion). Aucune théorie spectrale n'est utilisée ; les modules des canaux de sommation
sont seulement CLASSÉS (ils portent le poids comme coefficient d'une somme), jamais cités comme résultat.

## 1. Deux questions

* **Q1 (plan Φ4, §19.80)** : existe-t-il un énoncé reliant l'ordre d'annulation à une quantité lue aux contacts d'UNE Tour (sa propre
  amplitude, son propre prix), sans somme sur les premiers ni sur les zéros ?
* **Q2 (consigne de l'auteur à la reprise du 2026-11-09)** : existe-t-il, dans les théorèmes existants, une condition arithmétique
  INDÉPENDANTE sélectionnant les porteurs, qui ne soit pas une reformulation équivalente à RH transformée en prémisse ?

## 2. Méthode et périmètre réellement lu

Recensement par grep du poids (`zeroMult`, `zetaZeroMultiplicity`, `analyticOrder…`) : 57 fichiers de `Terminal`, 1 de `Foundation`,
1 de `RhGapPort`, 17 de `Zeta23Port` (ce dernier hors périmètre : interdit). Lus en entier ou par en-tête et liste d'énoncés le
2026-11-09 : `PrimeWeightResponse`, `BoxAnchor`, `BoxCount`, `BoxCountHeight`, `ZetaRealSegment`, `FirstThreeZerosCertified`,
`FirstArrivalsAnchor` (énoncé de l'ancre), `CountingDeficit`, `ArrivalFiberHypotheses`, `MirrorAntisymmetry` (en-tête),
`ZetaBoxGeneric`, `ZetaBoxNumeric` (listes d'énoncés) ; échantillonnés par leurs lignes portant le poids : `PairMeetingImposition`,
`PairBreakOfZero`, `AmplitudeContact`, `MeetingPoint`, `LineCountingDefect`, `JointParameterReading`. Les autres fichiers sont classés
par famille d'après leur nom et leurs occurrences, sans relecture : c'est une limite de l'audit, dite ici.

## 3. Les cinq rôles du poids dans le corpus

1. **Définition et symétries ponctuelles** (`Foundation/ZetaReflect`, `PairBreakOfZero`, `CarrierSelection`) : ordre d'annulation de
   zêta ; fini hors du pôle ; nul si et seulement si zêta ne s'annule pas ; au moins un en un zéro ; égal aux quatre points de
   l'orbite (conjugaison, réflexion). Aucune de ces propriétés ne distingue une position radiale de sa réfléchie.
2. **Coefficient du terme d'une Tour** (fil des contacts : `PairBreakOfZero`, `PairMeetingImposition`, `AmplitudeContact`,
   `MeetingPoint`, `JointParameterReading`) : le poids multiplie le terme du zéro ; il est positif ; il se met en facteur dans la
   paire (même poids au miroir). Il n'est jamais LU : aucun énoncé ne le retrouve à partir des contacts, de l'amplitude ou du prix,
   qui sont définis pour tout couple (position radiale, hauteur) sans référence à zêta.
3. **Coefficient dans une somme sur les zéros** (canaux de sommation, interdits ; classés seulement) : le poids est le coefficient
   de chaque terme d'une somme collective. Hors route.
4. **Hypothèse de simplicité** (`PrimeWeightResponse`, `ArrivalFiberHypotheses`) : la réponse radiale au premier ordre d'un membre
   EN LIGNE et SIMPLE est nulle pour toute direction qui conserve la réflexion. L'en-tête du module le dit lui-même : l'annulation
   vient de la réflexion et de la simplicité, pas des poids premiers exacts ; elle tient à l'identique dans un monde témoin sans
   premiers dont le régime change ; elle porte sur un membre déjà en ligne. Aucune sélection.
5. **Comptage avec multiplicité, lu sur un contour** (`ArgumentPrinciple`, `BoxCount`, `BoxAnchor`, `BoxCountHeight`,
   `CountingDeficit`, `ArrivalFiberHypotheses`, `LineCountingDefect`, certificats de boîte aux hauteurs quinze, vingt-deux,
   vingt-huit) : la somme des poids dans un rectangle est l'intégrale de bord de la dérivée logarithmique ; par réflexion, le
   comptage total vaut le comptage en ligne plus deux fois le comptage du côté bas ; comptage égal à un implique en ligne ;
   comptage impair implique au moins un membre en ligne ; un zéro hors ligne impose un poids de fibre d'au moins deux à sa hauteur ;
   poids de fibre strictement inférieur à deux si et seulement si la fibre est un point unique et simple. Les certificats de boîte
   évaluent zêta sur le bord par une somme FINIE sur les entiers avec reste majoré (jamais sur les premiers, jamais sur les zéros).

`ZetaRealSegment` : zêta ne s'annule pas sur le segment réel ouvert ; comme l'isolement des zéros, cela dit où les porteurs ne sont
PAS, jamais où ils sont.

## 4. Réponse à Q1 : NON

Aucun énoncé du corpus ne relie l'ordre d'annulation à une quantité lue aux contacts d'une seule Tour. Le poids y est un coefficient
(rôle 2), jamais une lecture. Le constat provisoire de §19.84 est confirmé.

## 5. Réponse à Q2 : UN seul mécanisme, le poids de fibre lu par comptage ; il n'est pas plus faible que RH

Le rôle 5 est le SEUL endroit du corpus où le poids sélectionne et force :
* il **sélectionne** : un comptage non nul sur un contour certifie l'existence d'un porteur dans le rectangle (c'est ainsi que les
  trois premiers porteurs sont établis) ;
* il **force la ligne** : poids de fibre inférieur à deux à une hauteur implique un porteur unique, simple, en ligne (compilé) ;
* il est **indépendant** du canal des contacts (lu sur zêta le long d'un contour) et **fait intervenir le poids**.

Mais, classé selon la règle des trois rubriques de §19.83 :
* (i) « toute hauteur porteuse a un poids de fibre inférieur à deux » IMPLIQUE RH (compilé, par contraposée du poids de fibre d'un
  zéro bas) ; RH ne l'implique PAS dans le corpus (un zéro double en ligne la viole) : la condition uniforme est RH ET simplicité,
  donc au moins aussi forte que RH. Ce n'est pas une hypothèse plus faible ; elle ne sera jamais posée.
* (ii) aucun contre-modèle au niveau des Tours n'a de sens ici : le poids de fibre n'est pas défini sur les Tours non porteuses.
* (iii) la version par parité (« poids de fibre impair ») n'est ni impliquée par RH ni suffisante pour RH (elle n'exclut pas une
  paire hors ligne à la même hauteur qu'un membre en ligne) ; question ouverte dite comme telle, sans intérêt de route.
* Le comptage n'est lu NI aux contacts NI sur les premiers : il est lu sur zêta le long d'un contour, hauteur par hauteur, par
  certificat fini. Le pont « premiers → pas de comptage » est l'hypothèse de transport de `ArrivalFiberHypotheses`, dont l'en-tête
  dit qu'aucun énoncé ne la ferme. C'est la même arête manquante, vue du côté du comptage.
* Rappel de doctrine (§19.20) : l'auteur a récusé le comptage comme CAUSE (constat d'aval). L'audit ne le réintroduit pas comme
  cause ; il constate seulement que c'est l'unique porteur de poids qui force.

## 6. Conclusion

1. Q1 : non. Q2 : un seul mécanisme (poids de fibre par comptage), certifiable cas par cas, dont la forme uniforme est RH plus
   simplicité. **Le corpus ne contient aucune condition arithmétique indépendante, lue sur les premiers ou aux contacts, qui
   sélectionne les porteurs.**
2. Aucun module E460 : l'audit n'exhibe aucun énoncé ponctuel nouveau à compiler (les énoncés de fibre existent déjà ; les réécrire
   serait une duplication).
3. Conséquence pour E458 : le poids de fibre rencontre la bande miroir par un énoncé sans hypothèse — un poids de fibre inférieur à
   deux impose une bande vide ; une bande non vide impose un poids de fibre d'au moins deux. C'est le seul point de contact
   compilable entre poids et bande ; il est ajouté au pré-enregistrement d'E458 (énoncé B5).
4. Prévision pour E459, écrite avant exécution : H-a et H-b ne portent que sur la bande, sans le poids ; le critère d'arrêt du plan
   (hypothèse plus faible que RH, vraie sur les contrôles, dont l'exigence compilée fait intervenir le poids) ne sera donc pas
   atteint par elles seules. E459 reste à exécuter pour le classement en trois rubriques.
5. Décision de route : à l'auteur.
