> Version française conservée à titre de référence. Main language: English, see README.md.

# E426 — Rencontres entre Tours successives sur l'axe réel (pré-enregistrée 2026-11-03)

Correction de la démarche (auteur) : E420–E425 ont étudié les Tours séparément puis leurs valeurs croisées, jamais les
**rencontres** entre leurs trajectoires sur l'axe réel. Chaîne corrigée : Tours → contacts réels → valeurs réelles →
**points de rencontre entre Tours** → succession des rencontres (cassures : fin d'un écart, début d'un autre) →
raccordement aux premiers et aux écarts. Aucune projection spectrale, aucune hypothèse OFF, aucune recherche de contradiction.
Module Lean de référence, compilé avant exécution : `Terminal/TowerMeetings.lean` (isolé, 27 déclarations, aucun `sorry`,
axiomes standards ; deux tentatives journalisées `logs/lean_attempt1.log`, `logs/lean_attempt2.log`).

Lexique : « point de rencontre » reste le nom de la fin d'un écart premier (`meetingPoint`) ; ici « rencontre entre
Tours » désigne les trois objets de l'auteur : (A) coïncidence de contacts, (B) rencontre de valeurs (mêmes parties
réelles à la même abscisse), (C) rencontre collective (succession / coïncidence des rencontres de paires voisines).

## Prédictions compilées que l'expérience doit retrouver à l'arrondi
* `unitMeeting_iff`, `slow_sin_eq_zero_iff`, `fast_sin_eq_zero_iff` : les rencontres des trajectoires unitaires forment deux
  réseaux en abscisse logarithmique, lent (pas 2π/(T₂−T₁)) et rapide (pas 2π/(T₁+T₂)).
* `gap_of_slowMeetings`, `sum_of_fastMeetings` : l'écart des hauteurs est relu exactement dans deux rencontres lentes
  consécutives ; la somme dans deux rencontres rapides consécutives.
* `slowMeetingLog_zero_pos`, `slowMeetingLog_zero_lt` : la rencontre lente d'indice 0 est dans (0, 1/(2T₁)) (collée à x = 1).
* `contactsCoincide_not_meeting` : une coïncidence de contacts n'est jamais une rencontre de valeurs brutes.
* `towerMeeting_of_unitMeeting_iff` : en un point du réseau unitaire, la rencontre brute n'a lieu que si la valeur est nulle ;
  donc les rencontres brutes sont **déplacées** par rapport au réseau unitaire (sauf aux passages par zéro).

## E426(a) — toutes les paires consécutives (2 001 051), réseaux analytiques (`scripts/e426_lattice_all.py`)
1. Vérification des prédictions compilées (indice 0 dans (0, 1/(2T₁)) : 0 violation ; écart et somme relus : erreur relative
   ≤ 10⁻⁹).
2. Première rencontre lente u₁ par bande de hauteur, comparée à log(T/2π) : **mesure**, aucune loi pré-enregistrée.
3. Contacts encadrant u₁ pour chaque Tour (indice avant, fraction de cellule, parité) ; coïncidences exactes de contacts
   (|fraction| < 10⁻⁹) : comptées, attendues 0 ; valeur unitaire commune en u₁ (identique pour les deux Tours : écart ≤ 10⁻⁸).
4. Cassure (C) : position de la première rencontre lente de la paire suivante (n+1, n+2) sur le réseau lent de la paire
   (n, n+1) : fraction de pas, histogramme 20 classes, coïncidences exactes (|d| < 10⁻⁹). **Aucune loi pré-enregistrée.**
5. Raccordement : x₁ = exp(u₁) ; écart premier [p_j, p_{j+1}] contenant x₁ (premiers ≤ 10⁸, fraction de paires couvertes
   consignée) ; fraction de position dans l'écart premier (histogramme 20 classes) ; produits g·log(p_{j+1}/p_j) et g·log x₁
   (médiane, déciles) par bande. Jumeau déterministe : pseudo-premiers de densité 1/log n, graine 20261103, même procédure.
   Lecture : si le produit réel et le produit jumeau ont la même distribution, le raccordement observé est celui de la
   densité seule ; une différence serait une mesure, pas une loi.

## E426(b) — rencontres brutes par bande (`scripts/e426_raw_meetings.py`)
Bandes : rangs 1–101, 100 000–100 100, 2 000 951–2 001 052. Pour chaque paire : toutes les racines de
cos(T₁u−φ₁)/|ρ₁| − cos(T₂u−φ₂)/|ρ₂| sur [0, u₁ + 3 pas rapides] (grille 8 points par période rapide, bissection 48 pas ;
paires de plus de 3·10⁷ racines sautées et comptées). Mesures : nombre de rencontres brutes contre nombre de points des
réseaux unitaires (différence consignée par histogramme) ; déplacement de chaque racine au point de réseau le plus proche
(pas rapides ; max et rms ; attendu décroissant avec la hauteur puisque les modules se rapprochent — mesure) ; racine la plus
proche de u₁ : valeurs réelles brutes des deux Tours, contacts avant/après de chaque Tour, cosinus unitaire ; ordre : nombre
de racines brutes entre u₀ et u₁ contre nombre de points rapides. Jumeau : mpmath 30 chiffres, raffinement des 20 premières
racines et de la racine proche de u₁ pour les rangs 1, 2, 100 001, 2 001 051 ; critère : écart float/mpmath ≤ 10⁻⁹·u.

Rien ici ne présume une contrainte sur la position radiale ; toute contrainte serait d'abord compilée. Résultats, y compris
négatifs, publiés dans `RESULTS.md`.
