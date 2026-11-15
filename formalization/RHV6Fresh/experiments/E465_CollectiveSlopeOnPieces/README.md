# E465 — Φ8 : le bilan collectif écrit en pentes de la demande sur les pièces découpées par les contacts — pré-enregistrement

Référence : `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.95 ; E463 (§19.93), E438 (§19.55–19.56), E464 (§19.94). Ordre de l'auteur du
2026-11-09 : « je suis d'accord avec la prochaine tâche […] fais-la complète ». Aucune hypothèse admise, aucun axiome, aucun `sorry` ;
module isolé `RHV6Fresh/Terminal/CollectiveSlopeOnPieces.lean`, NON ajouté à `RHV6Fresh.lean`. Ce commit contient le module définitif et
précède toute compilation (aucune sonde).

## Audit (fait avant ce pré-enregistrement)
* E463 (K7) : sur toute pièce, la somme des parts de tous les membres d'une recomposition égale la variation du signal LISSÉ des
  premiers multiplié par l'abscisse. Le membre arithmétique n'était pas écrit avec la demande brute.
* E438 : la demande brute, sur toute pièce, descend d'une unité par unité de longueur et reçoit le poids de chaque entier franchi ;
  le découpage d'un écart par les contacts (`gap_variation_eq_remainders`) vaut pour TOUTE fonction.
* Le pont : l'abscisse fois le signal lissé est la somme des poids franchis depuis l'origine, chacun multiplié par sa distance à
  l'abscisse ; c'est une quantité intégrée (du second ordre) de la demande. Sur une pièce elle varie donc d'une AIRE de la demande.
* Noms vérifiés par grep : aucun doublon (`integratedSignal`, `demandArea`, `residualBackground`, `integratedDemandC`, …).

## Ce que le module doit compiler (énoncés pré-écrits, en mots)
* S1 l'abscisse fois le signal lissé est le signal intégré (somme des poids fois distance).
* S2 sur une pièce, le signal intégré varie du niveau de départ fois la longueur, plus chaque poids franchi fois sa distance à la fin.
* S3 terme principal retiré, cette variation est l'aire de la demande : demande au départ fois longueur, moins le demi-carré de la
  longueur (descente de pente un), plus chaque poids franchi fois sa distance à la fin de la pièce.
* S4 pièce sans poids : descente pure. S5 les aires s'ajoutent de pièce en pièce.
* S6 pièce intérieure à un écart : seuls des poids non premiers.
* S7 pièce d'un écart allant jusqu'à la rencontre : le poids du premier de la rencontre entre avec une distance NULLE ; aucun poids
  premier n'entre dans l'aire d'un écart (il entre par le niveau de départ de l'écart suivant).
* S8 pièce franchissant un seul entier, premier : son poids entre par sa distance à la fin de la pièce.
* S9 une pièce plus courte qu'un pas d'entier franchit au plus un entier (leçon d'E464, voir ci-dessous).
* S10 bilan collectif : la somme des parts de tous les membres sur une pièce égale l'aire de la demande, moins la variation du fond
  résiduel (fond d'E462 privé de son terme principal).
* S11 sur une cellule entre deux contacts consécutifs d'une Tour : le terme de cette Tour dans le total est sa part d'E463 ; le total
  est l'aire de la demande sur la cellule.
* S12 l'aire de la demande sur un écart se découpe par les contacts d'une Tour (reste initial, cellules entières, reste final) ;
  chaque reste est une aire ; bilan collectif de l'écart entier.

## Leçons d'E464 utilisées
* L1 (échelle) : le prédicteur ne sépare un entier que si la cellule de la Tour la plus haute est nettement plus courte qu'un pas
  d'entier. D'où S9 : c'est le seuil géométrique en deçà duquel une cellule isole au plus un poids ; au-delà, l'aire d'une cellule
  mélange plusieurs poids et aucune lecture « un premier par cellule » n'est permise (cohérent avec E446 : régime fini).
* L2 (ordre de lecture) : le prédicteur lit un SAUT de la demande brute reconstituée ; le signal recomposé sans reste est du second
  ordre : une rencontre n'y fait pas de saut, elle change la pente. D'où S7–S8 : le poids entre par une distance, nulle à la rencontre.
* L3 (méthode) : l'horizon numérique annoncé avant E464 était faux d'un facteur 2 à 3. Ici aucun seuil numérique n'est annoncé ;
  le jumeau ne vérifie que des identités exactes, avec une tolérance d'arrondi pré-écrite.

## Classement contre RH (dit avant compilation)
Aucune hypothèse posée. S1–S12 sont des identités inconditionnelles, valables pour toute recomposition, sur la ligne comme hors ligne.
Elles n'excluent aucun zéro hors ligne. La part d'UNE Tour reste non lue sur les premiers de sa cellule : seul le total l'est.

## Jumeau déterministe (pré-écrit)
`twin.py` : arithmétique à 50 chiffres ; vérifie S1–S3, S5, S7, S8 et S12 sur les cellules de contacts des 5 premières Tours de la
ligne et sur les 200 premiers écarts ; critère : écart relatif au plus 10^-30 partout. Borné (moins d'une minute), sous `nohup`.

## Verdicts pré-écrits
A : S1–S12 compilés en au plus deux tentatives, axiomes standard, build complet vert, jumeau conforme. B : un énoncé change de forme
(dit tel quel). C : échec après deux tentatives (consigné, module retiré).
