# E466 — confrontation de quatre lectures du prédicteur de premiers (pré-enregistrement, 2026-11-12)

Expérience LATÉRALE (hors route de preuve, comme E464). Réponse à l'audit externe transmis par l'auteur le 2026-11-12, dont les points
sont acceptés et repris ici comme cahier des charges : (A) E464 n'utilisait aucune grammaire ; (B) le seuil 0,75 est arbitraire et a masqué
une séparation encore présente à cellule 0,55–0,83 ; (C) l'effet de Fejér doit être MESURÉ, non expliqué ; (D) la seconde différence
du signal intégré (E465) vaut le poids exact seulement pour le signal exact, l'erreur de troncature reste dans la seconde différence et
doit être mesurée, le fond exigé par la formule doit être conservé ; (E) l'horizon « hauteur max / pi » est une échelle de résolution de
la méthode, soutenue par les mesures, PAS une impossibilité démontrée (le théorème `short_piece_crosses_at_most_one` ne prouve qu'un
sens). Rectification consignée : ma phrase du 2026-11-12 « horizon hors de portée pour une raison de théorème » est RETIRÉE.

## Ce qui est figé
* E464 reste la référence immuable (code, résultats, journal inchangés). Son canal est reproduit ici tel quel (variante J-F).
* Données : `experiments/data/odlyzko_zeros6_2001052.txt`, deux familles (2 001 052 Tours ; 500 000 Tours), comme E464.
* Fenêtres de 300 entiers. Fenêtres de référence (celles d'E464) : 10^3, 10^4, 10^5, 2·10^5, 3·10^5, 5·10^5, 10^6, 10^7, 10^8.
  Fenêtres INÉDITES (jamais lues auparavant) : 5·10^4, 1,5·10^5, 2,5·10^5, 4·10^5, 7·10^5.
* Aucun crible, aucun test de primalité dans la prédiction. Contrôle exact (division) À LA FIN seulement, catégorisé : premiers,
  puissances de premiers, autres composés (point 6 de l'audit).

## Les quatre canaux de score (tous normalisés par le logarithme de l'entier)
* J-F : saut de la demande reconstituée entre n−1/2 et n+1/2, poids de Fejér (= E464 exactement).
* J-noF : même saut, sans Fejér (coupure nette à la hauteur maximale).
* D2-F : seconde différence sur un pas d'entier du signal INTÉGRÉ reconstitué (E465 : x fois la somme lissée), poids de Fejér.
  Le signal intégré reconstitué conserve le fond exigé par la formule : moitié du carré, terme linéaire du logarithme de deux pi,
  somme des zéros triviaux (cinq termes) ; les constantes disparaissent dans la seconde différence, la moitié du carré donne exactement un.
* D2-noF : même seconde différence, sans Fejér.
Valeur exacte attendue du score (signal exact) : 1 sur un premier, 1/k sur une puissance k-ième, 0 ailleurs.

## Décisions pré-écrites (aucune ne sera modifiée après lecture des résultats)
* R0 : « premier » si score > 0,75 (règle E464, conservée pour comparaison).
* R1 : « premier » si score > 0,75 ET l'entier passe la grammaire modulo 6 (reste 1 ou 5 ; nécessaire, jamais suffisante). Elle ne
  peut que retirer des faux positifs ; elle ne peut créer aucun manqué.
* R2 (abstention géométrique) : la décision est DIFFÉRÉE sur toute fenêtre où la cellule de la Tour la plus haute dépasse 1 pas
  d'entier (information des contacts/cellules utilisable AVANT la prédiction, non circulaire). Les erreurs sont comptées séparément
  sur fenêtres décidées et différées.
* Les scores bruts (min sur premiers, max sur composés, max sur puissances de premiers, marge = min premiers − max composés)
  sont conservés pour chaque fenêtre et chaque canal, indépendamment de tout seuil.
* Erreur de reconstruction (point D) : pour chaque canal, max sur la fenêtre de |score − valeur exacte|, sur chaque catégorie.

## Information des contacts : ce que j'ai cherché et ce que je n'ai pas trouvé (dit avant exécution)
Hors la résolution (longueur de la cellule la plus fine, utilisée par R2), je n'ai identifié aucune utilisation NON circulaire des
contacts qui discrimine deux entiers voisins : les théorèmes de succession (écart, rencontre, reste final) prennent les premiers vrais
en entrée. Toute variante qui les utiliserait serait circulaire. Ce point est consigné comme négatif de recherche, à rouvrir si un
énoncé compilé donne une lecture des contacts calculable sans les premiers.

## Attentes écrites avant exécution
* A1 : J-F reproduit E464 à l'identique (mêmes comptes, mêmes scores à 10^-9).
* A2 : les canaux D2 et J donnent des scores très proches (la seconde différence du signal intégré tronqué est, au premier ordre,
  le saut du signal tronqué) ; je n'attends PAS de gain de résolution du seul passage à la seconde différence.
* A3 : sans Fejér, séparation plus nette là où elle existe (cellule < 1) mais oscillations parasites plus fortes : marge pouvant
  augmenter OU diminuer ; je n'annonce aucun sens. Ma conjecture « Fejér divise la hauteur efficace par deux » est TESTÉE par la
  comparaison des horizons de marge positive entre F et noF ; elle est réfutée si l'horizon de marge positive ne bouge pas.
* A4 : la grammaire modulo 6 ne change rien aux comptes (E464 n'avait aucun faux positif).
* A5 : fenêtres inédites : mêmes régimes qu'E464 aux mêmes cellules (exact ≤ 0,28 ; séparation sans seuil 0,5–0,85 ; recouvrement ≥ 1).

## Verdicts pré-écrits
* A : A1 vraie, et un canal au moins possède une marge positive sur une fenêtre où J-F n'en a pas (gain d'information mesuré).
* B : A1 vraie, aucun canal n'étend l'horizon de marge positive de J-F (le changement de lecture n'apporte rien ; seule la
  calibration du seuil comptait).
* C : A1 fausse (reproduction d'E464 échouée) : tout le reste est suspendu.
Exécution bornée sous `nohup`, `timeout` 45 min, journal `logs/run.txt` versionné, résultats `results.json`.
