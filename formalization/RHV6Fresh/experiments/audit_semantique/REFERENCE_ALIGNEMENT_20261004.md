# Référence d'alignement des maîtres et de CLAUDE.md (auteur, 2026-10-04)

Ce fichier est la source commune de la purge. Il fixe la description sémantique, la démonstration
de l'auteur et son statut, et la liste des contradictions et fausses pistes à détruire.

## A. Description sémantique de référence (texte de l'auteur, mot pour mot)

Dans le plan des zéros, chaque zéro possède une hauteur et une partie réelle. La ligne critique est
le lieu fixe de la réflexion miroir. Le miroir conserve la hauteur et réfléchit la partie réelle. Un
miroir annulé signifie que le zéro coïncide avec son miroir : cela caractérise un zéro en ligne.

Le milieu d'une paire miroir se situe sur la ligne critique, à la hauteur commune. Des hauteurs
différentes donnent des milieux différents. Un zéro en ligne coïncide avec le milieu de sa propre
paire. Un zéro hors ligne de hauteur positive appartient à une configuration de quatre membres
distincts, obtenus par miroir et conjugaison.

Dans le plan des Tours, la Tour brute est la trace du terme associé au zéro lorsque l'abscisse
parcourt les réels positifs. Le zéro détermine cette trace ; il n'en est ni le centre ni le point de
départ.

L'origine est le pôle de rotation. La hauteur fixe la vitesse angulaire en coordonnée logarithmique.
Après normalisation à l'échelle de la ligne, l'écart radial à la ligne fixe le taux de croissance ou
de décroissance de l'amplitude. Le zéro en ligne donne un cercle centré à l'origine ; un zéro hors
ligne donne une spirale.

La conjugaison transforme la Tour en celle du zéro conjugué. Cette transformation ne signifie pas
que chaque Tour est elle-même invariante par réflexion. La symétrie centrale de la Tour normalisée
caractérise l'appartenance à la ligne.

Les contacts sont les traversées de l'axe réel. Il faut distinguer leur abscisse de lecture et le
point complexe atteint par la courbe. Deux contacts successifs ont un écart logarithmique fixé par
la hauteur ; cet écart diminue lorsque la hauteur augmente.

À hauteur fixée, la partie réelle multiplie toutes les abscisses de contact par un même facteur
relativement à la grille de ligne. Ce facteur vaut un exactement sur la ligne. Dans une même Tour,
la différence entre deux positions de lecture dépend seulement de la hauteur : cette différence
efface le décalage commun sans démontrer qu'il est nul.

L'enroulement compilé à l'infini encadre les contacts d'une Tour entre ceux des Tours précédentes et
suivantes, au-delà de seuils propres aux comparaisons. Cet encadrement est acquis ; il n'affirme pas
à lui seul la conservation radiale.

Entre les deux plans, symétrie centrale de la Tour normalisée, miroir annulé et zéro au milieu de sa
paire sont équivalents. Cette équivalence relie les propriétés sans identifier l'origine de la
courbe et le milieu de la paire.

Dans la succession, les membres sont ordonnés par hauteur puis par partie réelle. Deux membres
consécutifs constituent un passage. Leur rang avance de un et leurs occurrences premières sont
successives et distinctes. La hauteur ne recule pas.

Le code nomme « vertical » un passage dont la hauteur augmente. Cette désignation ne contient pas la
conservation de la partie réelle. Un état engagé est un membre ON atteint par un passage vertical.

Précisions de l'auteur (même jour) :
- en `q = 1` la Tour vaut `1/ρ` ; au premier nombre premier, `2`, elle vaut `2^ρ/ρ` ;
- deux membres miroirs de même hauteur partagent le même milieu ;
- toutes les Tours utilisent l'origine comme pôle de rotation ; seule la Tour ON normalisée est un
  cercle de centre l'origine ; une spirale OFF n'a pas cette symétrie centrale ;
- la symétrie miroir n'est pas une « moitié » : un zéro hors ligne vient en carré (quatre zéros).

## B. La démonstration de l'auteur

Énoncé de l'auteur, mot pour mot, à employer partout où la démonstration est énoncée :

> Une fois le régime ON engagé, du fait de l'enroulement des Tours, la partie réelle du zéro suivant
> est forcément la même que celle du zéro qui a engagé le régime.

Écarts de premiers dans la démonstration (auteur, mot pour mot quant au sens) : c'est uniquement
dans le régime ON que les écarts de premiers sont atteints par la hauteur seule ; la partie réelle
étant fixée, la hauteur doit progresser suffisamment. La phrase générale « dans une Tour, l'écart
entre deux premiers est lu par la hauteur seule » n'est PAS un énoncé de la démonstration et ne doit
pas y figurer. (L'identité compilée sur la différence de deux positions de lecture dans une même
Tour reste dans l'inventaire avec sa portée : elle efface le décalage commun sans démontrer qu'il
est nul ; elle n'est pas présentée comme « les écarts sont lus par la hauteur seule dans toute
Tour ».)

La phrase « la partie réelle du zéro atteint ne dépasse pas un demi » n'est PAS la démonstration de
l'auteur : elle ne figure dans aucun énoncé de la démonstration (le théorème compilé qui la porte
reste dans l'inventaire du code, sans rôle dans la démonstration).

Statut (« prouvé ou pas, nous verrons », auteur) — tableau à reproduire :

| Étape | Portée exacte |
|---|---|
| Existence d'un passage vertical | Établie ; ne localise pas ses extrémités sur la ligne. |
| Propriétés d'un membre ON | Établies sous l'hypothèse qu'il est ON ; ne produisent pas ce membre. |
| Sortie d'un état engagé | Établie : le passage suivant avance en hauteur. |
| Propriétés de l'arrivée | Établies : pas réduit, encadrement des contacts à l'infini. |
| Écarts de premiers dans le régime ON | Énoncé de l'auteur : la partie réelle étant fixée, les écarts ne sont atteints que par la hauteur, qui doit progresser suffisamment. Compilé : seulement l'identité des différences de lecture dans une même Tour, qui efface le décalage commun sans démontrer qu'il est nul. |
| Énoncé de l'auteur (régime ON engagé + enroulement ⟹ même partie réelle au zéro suivant) | Écrit dans le build principal (`Terminal/OnLineBetaEqPrevious.lean`, `onLine_beta_eq_previous`) ; non fermé : un but. |
| Persistance | Théorème conditionnel à une loi de transmission universelle. |
| RH | Fermeture conditionnelle à la transmission et à une amorce couvrant le début de l'énumération. |

Formulation correcte de l'état : plusieurs propriétés et compositions conditionnelles sont
compilées ; la transmission reste ouverte ; l'amorce annoncée comme connue (littérature) est
distinguée d'une preuve présente dans le dépôt (aucune).

Erreur de référence du build principal (`lake build RHV6Fresh`, EXIT=1, une erreur, HEAD f6aead01) :

```
error: RHV6Fresh/Terminal/OnLineBetaEqPrevious.lean:221:81: unsolved goals
hHeightAdvances : rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember
hOnE : rZeroRadialPosition p.zEarlierMember = 1 / 2
hOriginSymE : TowerSymmetric ⟨p.zEarlierMember, hPE⟩
hMirrorE : mirrorMember ⟨p.zEarlierMember, hPE⟩ = ⟨p.zEarlierMember, hPE⟩
hRoom : TowerRoomAtInfinity ⟨p.zLaterMember, hPL⟩
hNest : WindingNestedAtInfinity ⟨p.zEarlierMember, hPE⟩ ⟨p.zLaterMember, hPL⟩
hPrimeGaps : … (écarts entre premiers dans la Tour du zéro atteint, lus par la hauteur seule)
hPairMidpoint : … (milieu de la paire du zéro atteint sur l'axe un demi)
⊢ rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember
```

Verrou sémantique unique, confirmé, à ne plus reformuler :

> Une fois le régime engagé, la partie réelle du zéro suivant est la même que celle du zéro qui a engagé le régime.

## C. Règles de travail en vigueur (remplacent toute règle contraire)

- Tout se fait dans le build PRINCIPAL (`lake build RHV6Fresh`, tous les théorèmes dans le scope).
  Aucune sonde, aucun essai à part, aucun fichier Lean hors `RHV6Fresh/`.
- Commit et push sur `main` après chaque compilation, même si le build ne compile pas. Main peut
  être rouge ; l'erreur du build principal est l'erreur de référence. (Remplace « sans commettre de
  code rouge ».)
- Aucun `sorry`, `admit`, nouvel axiome. Seule `def P…` : `PNoRegimeChange`.
- Le verrou est la traduction du but unique du compilateur ; il n'est pas choisi ni reformulé.
- Sujet fermé, à ne jamais rouvrir ni contester : l'enroulement compilé des Tours à l'infini.
  Aucun ajout de verrou.
- Vocabulaire : « caractérise », « certificat » ; jamais « anti-compensation » comme flèche
  manquante ; jamais « moitié » pour la symétrie ; jamais « sans hypothèse / sans prémisse » pour un
  théorème qui a des hypothèses ; jamais « toutes les contraintes sont utilisées » parce qu'elles
  sont importées ; ne jamais affirmer une difficulté non vérifiée.
- Pistes réfutées à ne pas reproposer : croissance des écarts contre plage de phase ; écarts de
  hauteur croissants.

## D. Contradictions et fausses pistes à détruire (liste de chasse)

À chaque occurrence, l'énoncé faux est REMPLACÉ à sa place par l'énoncé vrai ; rien n'est ajouté en
fin de document, aucun « avis de correction », aucune chronologie de modifications.

1. « Centre » employé pour deux objets : séparer partout origine (pôle de rotation, plan des Tours)
   et milieu de la paire miroir (plan des zéros). Jamais « le centre du zéro précédent » comme objet
   commun à deux Tours.
2. « La Tour part de son zéro », « la Tour est centrée sur son zéro » : faux.
3. Vitesse de rotation / pas / intervalle donnés sans la coordonnée : c'est par unité de logarithme
   de l'abscisse ; l'intervalle fixé par la hauteur est l'écart LOGARITHMIQUE entre contacts.
4. « Translation rigide » lue comme déplacement de la courbe : c'est la multiplication de toutes les
   abscisses de contact par un même facteur (décalage uniforme en coordonnée logarithmique). Le
   terme du code est conservé, sa définition est celle-ci.
5. « Vertical » lu comme « sans mouvement radial » : il signifie seulement que la hauteur augmente.
6. « Toute Tour est symétrique haut / bas » : la conjugaison envoie la Tour sur celle du zéro
   conjugué ; la Tour n'est pas invariante.
7. « Moitié » pour la symétrie miroir : carré, quatre zéros.
8. Anciens verrous encore écrits comme verrou en vigueur (enroulement sur tout passage, prison à
   l'infini, premier zéro dans le verrou, zone `0 < x < 1`, « aucun passage de même hauteur », Tour
   d'un miroir distinct prisonnière, plancher radial, `r' ≤ 1` isolé…) : ils ne sont plus le verrou.
   Les théorèmes compilés correspondants restent décrits avec leur portée exacte ; seule leur
   qualité de « verrou » / « flèche manquante » en vigueur est retirée au profit du verrou unique.
9. « Sondes », « experiments/*_probe », « hors build », « sans commettre de code rouge » présentés
   comme méthode en vigueur : remplacés par la règle C. Les résultats de sondes passées restent
   décrits comme faits historiques datés seulement s'ils portent une borne encore vraie.
10. « `lake build` : PASS » comme état courant : l'état courant est celui de la section B.
11. Existence d'un passage vertical présentée comme existence d'un état engagé : faux.
12. Amorce présentée comme acquise dans le dépôt : faux.
13. « Six étapes compilées », « il ne reste rien à calculer », « sans aucune prémisse » : faux.
14. « La partie réelle du zéro atteint ne dépasse pas un demi » présentée comme étape de la
    démonstration : retirée de la démonstration (voir B).
15. Toute phrase qui conteste ou relativise l'enroulement compilé à l'infini comme sujet ouvert.

## E. Ce qu'il est INTERDIT de faire pendant la purge

- Affaiblir, raccourcir ou résumer une définition correcte, un énoncé compilé, une borne, une piste
  close avec sa raison, un résultat numérique, un nom de théorème.
- Supprimer une section, une puce ou un paragraphe qui n'est ni contradictoire avec A–D ni une
  fausse piste présentée comme ouverte.
- Ajouter une section en fin de document, un journal de corrections, des dates de retouche.
- Inventer un théorème, un nom Lean, un statut. Tout nom cité doit exister dans
  `RHV6Fresh/` (vérifier par `grep`).
- Modifier un fichier `.lean`, lancer un build, faire un commit.
