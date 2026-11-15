> Version française conservée à titre de référence. Main language: English, see README.md.

# E464 — expérience demandée par l'auteur : un « prédicteur » de nombres premiers par les Tours — pré-enregistrement

Ordre de l'auteur (2026-11-09) : tenter un prédicteur de premiers avec la grammaire, la reconstitution par les contacts et les
découvertes du projet ; but évoqué : un premier d'un million de chiffres, contrôlé seulement à la fin. Expérience LATÉRALE : elle
n'appartient pas à la route de preuve (la règle « ne jamais tester les premiers directement », §19.40, vaut pour la route ; l'auteur
ordonne ici explicitement cette expérience). Aucune sortie fabriquée ; ce commit précède toute exécution.

## Méthode (fixée avant exécution)
* Données : `experiments/data/odlyzko_zeros6_2001052.txt` (2 001 052 hauteurs de zéros, toutes sur la ligne dans cette plage).
* Prédicteur : pour un entier `n`, la somme des Tours (valeur réelle de chaque Tour, poids de Fejér `1 − hauteur/hauteur max`) donne
  une demande reconstituée ; la prédiction lit son SAUT entre `n − 1/2` et `n + 1/2`. Règle : « `n` est premier » si et seulement si
  le saut dépasse les trois quarts de `log n` (un carré de premier saute de la moitié, un composé de zéro).
* Aucun crible, aucun test de primalité dans la prédiction. Le contrôle (crible exact) n'est fait qu'À LA FIN, sur la fenêtre entière.
* Fenêtres : 300 entiers consécutifs à partir de 10^3, 10^4, 10^5, 2·10^5, 3·10^5, 5·10^5, 10^6, 10^7, 10^8.
* Deux familles : les 2 001 052 Tours, puis les 500 000 premières (pour lire comment l'horizon dépend de la hauteur maximale).
* Mesures par fenêtre : premiers vrais, prédits, justes, manqués, faux ; longueur de la cellule de la Tour la plus haute à cette abscisse.

## Attente écrite avant exécution (règle du seuil, E441–E443)
La cellule de la Tour la plus haute mesure environ `π·x / hauteur max`. Tant qu'elle est plus courte qu'un pas d'entier, le saut
est résolu et la prédiction doit être exacte ; au-delà, les Tours ne séparent plus deux entiers voisins. Horizon attendu : `x` de l'ordre
de la hauteur maximale divisée par π (environ 360 000 pour 2 millions de Tours, environ 100 000 pour 500 000).

## Faisabilité du million de chiffres (dite avant exécution)
Si l'horizon suit cette loi, localiser un premier près de `10^(10^6)` demande des Tours jusqu'à une hauteur de cet ordre, donc un nombre
de zéros lui-même d'environ un million de chiffres : hors de toute portée. De plus, contrôler « les 30 derniers chiffres » ne contrôle
pas la primalité : elle dépend du nombre entier. L'expérience mesure donc l'horizon réel et la loi d'échelle ; elle ne promet pas le
million de chiffres.

## Verdicts pré-écrits
* A : prédiction exacte (aucun manqué, aucun faux) dans toutes les fenêtres sous l'horizon attendu, dégradée au-delà, horizon
  proportionnel à la hauteur maximale entre les deux familles.
* B : exacte sous l'horizon mais loi d'échelle différente de l'attente (dite telle quelle).
* C : erreurs sous l'horizon attendu (le prédicteur ne tient pas).
Exécution bornée sous `nohup`, journal versionné en `.txt`.
