# E459 — Résultats (2026-11-09) : hypothèses locales H-a et H-b classées — verdict A, critère d'arrêt du plan NON atteint

Pré-enregistrement et classement : `README.md` (commit c55c6980, avant le module définitif ; une sonde sans erreur l'a précédé,
`attempts/probe1.txt`). Module `RHV6Fresh/Terminal/CarrierLocalReading.lean` : isolé, 17 déclarations, vert à la PREMIÈRE tentative
(`attempts/build_attempt1.txt`), 10 énoncés imprimés sur les trois axiomes standard, grep du ban à zéro, `lake build RHV6Fresh`
complet vert (`logs/lake_build_full.txt`).

## Compilé (aucune hypothèse posée)
* Dictionnaire : la cellule de rencontre d'un écart est le mot au rang suivant ; même cellule de rencontre que le miroir ⟺ même
  lecture à ce rang.
* **H-a, rubrique (ii)** : hors contact exact, le mot est localement constant en la position radiale ; sur tout ensemble fini de rangs
  sans contact exact de la ligne, il existe une fenêtre ouverte autour de la ligne où toute Tour a la même lecture ; une Tour du côté
  bas, hors ligne, la satisfait (contre-modèle au niveau des Tours).
* **H-a, classement exact** : la même lecture au rang `n` force la ligne à la hauteur `T` si et seulement si le premier de rang `n`
  est exactement sur un contact de la ligne de hauteur `T` (branche logique ; jamais affirmé qu'un premier est sur un contact).
* **H-a, rubrique (i)** : RH ⟹ H-a à tout rang. **Rubrique (iii)** : H-a ⟹ RH reste OUVERTE, dite comme telle.
* **H-b** : sur les Tours, même lecture à partir d'un rang quelconque ⟺ ligne ; sur les zéros vrais, H-b (toutes les rencontres, ou
  à partir d'un rang) ⟺ RH : REFORMULATION, jamais posée.

## Jumeau (`e459_local_reading.py`, une exécution sous nohup, `logs/e459_output.txt`)
200 premières hauteurs, 78 498 premiers jusqu'à un million, contrôles 0,3 ; 0,4 ; 0,45 (Tours non porteuses).
* (a) Ligne, dix premiers rangs : plus petite distance de la fraction de cellule à un contact 5,1·10⁻⁴, strictement positive aux 200
  hauteurs : branche non dégénérée partout (attendu réalisé).
* (b) Fenêtre exacte de même lecture : au rang 0, la fenêtre est TOTALE aux 200 hauteurs (toute position radiale basse a la même
  lecture que son miroir au premier de rang 0) ; sur les dix premiers rangs, totale à 196 hauteurs, demi-largeur minimale 0,146.
  Recoupement direct : 0 désaccord sur 2 000 tests en deçà du bord, 0 sur 4 au-delà.
* (c) H-a est satisfaite par 200/200 Tours de contrôle au rang 0 pour les trois contrôles ; sur les dix premiers rangs : 199/200,
  200/200, 200/200 ; accord avec la fenêtre exacte 400/400 à chaque fois (attendu « majoritaire » réalisé, en fait quasi total).
* (d) Premier rang de bande (où H-b casse) : fini pour 200/200 Tours de chaque contrôle ; minimum, médiane, maximum : 3 / 1 223 /
  14 242 ; 12 / 2 242,5 / 23 773 ; 80 / 4 636,5 / 46 078. Mesure, aucune loi.

## Lecture
* **H-a est plus faible que RH sur les Tours, vraie sur les contrôles, mais presque vide** : le décalage de phase entre une Tour et
  son miroir est petit devant la cellule, si bien qu'à rang fixé presque toute Tour hors ligne lit comme son miroir. Elle ne contraint
  pas la position radiale, et son exigence compilée (fenêtre autour de la ligne fixée par la fraction de cellule) ne fait PAS
  intervenir le poids.
* **H-b est RH** sous un autre nom ; les Tours de contrôle la cassent toutes à un rang fini mesuré.
* **Critère d'arrêt du plan Φ** (hypothèse plus faible que RH, vraie sur les contrôles, dont l'exigence compilée fait intervenir le
  poids) : NON atteint, conformément à la prévision écrite d'avance (§19.86, §19.88).

## Verdict
A pour l'exécution (tout compilé en une tentative, attendus du jumeau réalisés, classement en trois rubriques complet). Résultat de
route : NÉGATIF pour la recherche d'une arête — aucune hypothèse locale de lecture ne sélectionne les porteurs.
