# E426 — Résultats (exécutée 2026-11-03 ; pré-enregistrement a2420c40)

Données : 2 001 052 zéros d'Odlyzko (SHA-256 2ef7b752…), posés sur la ligne. Module compilé de référence :
`Terminal/TowerMeetings.lean` (27 déclarations, aucun `sorry`, axiomes standards, deux tentatives ; cible par défaut verte,
9 064 tâches, `logs/lake_build_default.log`). Journaux : `logs/e426a.log`, `logs/e426b.log` ; données :
`data/e426a_results.json`, `data/e426b_results.json`.

## E426(a) — réseaux de rencontres de toutes les paires consécutives (2 001 051 paires, 9 s)

### Identités (prédictions compilées, retrouvées à l'arrondi)
| Objet | Prédiction compilée | Mesure |
|---|---|---|
| rencontre lente d'indice 0 dans (0, 1/(2T₁)) | `slowMeetingLog_zero_pos/_lt` | 0 violation sur 2 001 051 |
| écart relu dans deux rencontres lentes consécutives | `gap_of_slowMeetings` | erreur relative max 5,6·10⁻¹⁶ |
| somme relue dans deux rencontres rapides consécutives | `sum_of_fastMeetings` | 4,4·10⁻¹⁶ |
| valeur unitaire commune des deux Tours à la rencontre lente | `unitMeeting_iff` (famille lente) | écart max 1,6·10⁻⁷ (arrondi T·ε) |
| coïncidence exacte de contacts à la rencontre lente | `contactsCoincide_iff` (relation exacte) | 0 cas |

**Corrections de lecture consignées.** (i) Le produit g·log x₁ pré-enregistré comme « mesure » est une **identité**
(g·u₁ = Δφ + 2π par définition de u₁) : il vaut 2π à 10⁻⁶ près et ne porte aucune information ; il est retiré des mesures.
(ii) À la rencontre lente, les positions d'étage des deux Tours diffèrent exactement de 2 (même phase modulo 2π) : les deux
histogrammes de fraction de cellule et les parités sont **identiques par construction**, non par mesure.

### Mesures (aucune loi pré-enregistrée)
* **Première rencontre lente u₁ = log x₁ contre log(T/2π)** (rapport médian par bande) :

| bande | paires | u₁ moyen | log(T/2π) moyen | rapport médian | déciles |
|---|---|---|---|---|---|
| T < 10³ | 649 | 5,08 | 4,31 | 1,043 | 0,67 – 1,83 |
| 10³–10⁴ | 9 493 | 8,14 | 6,68 | 1,038 | 0,66 – 1,93 |
| 10⁴–10⁵ | 127 927 | 11,11 | 8,97 | 1,035 | 0,65 – 1,98 |
| 10⁵–10⁶ | 1 609 077 | 14,10 | 11,26 | 1,034 | 0,65 – 2,02 |
| T ≥ 10⁶ | 253 905 | 15,10 | 12,04 | 1,034 | 0,65 – 2,03 |

  La première rencontre lente de deux zéros consécutifs tombe, en médiane, à l'abscisse x₁ ≈ T/2π (dualité des densités :
  u₁ ≈ 2π/g et g ≈ 2π/log(T/2π) en moyenne), avec la dispersion des écarts (déciles 0,65 – 2). Stable en hauteur.
* **Contacts encadrant u₁** : fraction de cellule équirépartie (écart max à l'uniforme 0,5 % sur 20 classes), parité de
  l'indice 0,5002. La rencontre lente n'est pas un point remarquable de la grille de contacts.
* **Cassure (C)** — première rencontre lente de la paire suivante lue sur le réseau lent de la paire précédente : fraction de
  pas **non uniforme** (écart max 19 %, maximum en ½, minimum aux bords), 0 coïncidence exacte. Cette fraction est, à Δφ
  près, la partie fractionnaire du **rapport des écarts consécutifs** g_{n+1}/g_n (relation compilée
  `slowMeetings_coincide_iff`) ; l'histogramme reproduit exactement celui de frac(g_{n+1}/g_n) (médiane du rapport 1,0005,
  mode vers 0,6, longue queue). Aucune structure au-delà de la statistique connue des rapports d'écarts consécutifs.
* **Raccordement aux écarts premiers** — x₁ = exp(u₁) (médiane 1,05·10⁵ ; 82,6 % des paires dans [2, 10⁸], 1 652 900
  paires) ; écart premier contenant x₁ :

| bande | n | fraction de position : écart max à l'uniforme (réel / jumeau) | g·log(p_{j+1}/p_j) médiane (réel / jumeau) | décile 90 (réel / jumeau) |
|---|---|---|---|---|
| T < 10³ | 646 | 0,35 / 0,42 | 0,098 / 0,070 | 0,46 / 0,78 |
| 10³–10⁴ | 9 178 | 0,10 / 0,08 | 0,0088 / 0,0084 | 0,123 / 0,125 |
| 10⁴–10⁵ | 116 198 | 0,041 / 0,033 | 0,0011 / 0,0013 | 0,026 / 0,039 |
| 10⁵–10⁶ | 1 325 941 | 0,008 / 0,010 | 0,0002 / 0,0002 | 0,0078 / 0,0083 |
| T ≥ 10⁶ | 200 937 | 0,020 / 0,014 | 0,0001 / 0,0001 | 0,0048 / 0,0055 |
| toutes | 1 652 900 | 0,006 / 0,008 | 0,0002 / 0,0002 | 0,0087 / 0,0090 |

  La position de x₁ dans son écart premier est équirépartie ; 0 paire avec x₁ sur un premier (à 10⁻⁹). Le produit de l'écart
  des zéros par la longueur logarithmique de l'écart premier est indiscernable du jumeau de densité (pseudo-premiers de
  densité 1/log n). **Le raccordement observé est celui de la densité seule** ; aucune relation paire à paire entre la
  première rencontre lente et l'écart premier qui la contient.

## E426(b) — rencontres brutes de Tours consécutives par bande (300 paires, 1 117 s)

Racines de cos(T₁u−φ₁)/|ρ₁| − cos(T₂u−φ₂)/|ρ₂| sur [0, u₁ + 3 pas rapides] (de 6 racines au rang 1 à 9,7 millions au rang
2 000 952). Jumeau mpmath 30 chiffres : écart float/mpmath 2·10⁻¹⁶ (rangs 1, 2), 1,1·10⁻¹⁰ (rang 100 001), 2,2·10⁻¹¹
(rang 2 001 051) ; critère 10⁻⁹·u tenu.

| bande | paires | n_brut − n_unitaire | brut − rapide entre u₀ et u₁ | déplacement rms (pas rapides) | déplacement max | racine la plus proche de u₁ : déplacement médian / max | \|cos\| unitaire médian à cette racine |
|---|---|---|---|---|---|---|---|
| rangs 1–101 | 100 | −4 : 78, −3 : 22 | −2 : 49, −1 : 51 | 0,025 | 0,97 | 0,58 / 0,89 | 0,86 |
| rangs 100 000–100 100 | 100 | −4 : 75, −3 : 25 | −2 : 48, −1 : 52 | 5,6·10⁻⁴ | 0,97 | 0,64 / 0,88 | 0,90 |
| rangs 2 000 951–2 001 052 | 100 | −4 : 65, −3 : 35 | −2 : 42, −1 : 58 | 1,4·10⁻⁴ | 0,97 | 0,64 / 0,89 | 0,90 |

Lecture (mesures, pas lois) :
1. **Loin des rencontres lentes**, les rencontres brutes convergent vers le réseau rapide quand la hauteur croît (rms
   0,025 → 1,4·10⁻⁴ pas rapides) : à grande hauteur, les deux Tours se rencontrent presque exactement sur la famille
   rapide (fréquence T₁ + T₂).
2. **Au voisinage de chaque rencontre lente** (u₀ près de 1, u₁ ≈ 2π/g), la géométrie brute est **invariante en hauteur** :
   deux racines disparaissent par rencontre lente (n_brut − n_unitaire = −4, ou −3 au bord de fenêtre), la racine brute la
   plus proche de u₁ est déplacée d'environ 0,6 pas rapide (médiane 0,58–0,64, max 0,89), et la valeur unitaire qu'elle
   porte est loin de zéro (|cos| ≈ 0,9). C'est la trace mesurée de `towerMeeting_of_unitMeeting_iff` : en u₁ la rencontre
   brute n'a pas lieu (valeur non nulle), elle est déplacée d'une fraction de pas rapide fixée par le rapport
   cos b / sin(phase rapide), indépendante de T. **La rencontre lente, où l'écart est lu, n'est jamais une rencontre brute.**
3. Aux rencontres brutes, les deux Tours portent la même valeur réelle brute (identité, écart à l'arrondi) ; la valeur
   est signée, d'amplitude x^½/|ρ| ; aux rangs élevés la première rencontre lente tombe à des abscisses très grandes quand
   l'écart est petit (rang 2 000 952 : x₁ ≈ 5·10¹¹ pour g ≈ 0,23).
4. Contacts encadrant la racine proche de u₁ : les fractions de cellule des deux Tours sont égales à 10⁻⁵ près (héritage de
   l'identité de phase à la rencontre lente), l'indice de la seconde Tour dépasse celui de la première de 2 ; aucune
   coïncidence exacte de contacts (prédiction compilée `contactsCoincide_not_meeting` : une coïncidence ne serait de toute
   façon pas une rencontre).

## Verdict E426
* La géométrie réelle des rencontres entre deux Tours consécutives est **entièrement décrite** : deux réseaux unitaires
  compilés (lent, pas 2π/g ; rapide, pas 2π/(T₁+T₂)), l'écart relu exactement dans le réseau lent, les rencontres brutes
  collées au réseau rapide à grande hauteur et déplacées d'une fraction de pas fixe près des rencontres lentes.
* **Succession / cassure** : la rencontre lente de la paire suivante se place sur le réseau de la précédente selon le
  rapport des écarts consécutifs, sans coïncidence exacte ; rien au-delà de la statistique des rapports d'écarts.
* **Raccordement** : la position de la première rencontre lente relativement aux premiers est celle de la densité seule
  (jumeau indiscernable) ; aucune relation paire à paire.
* Aucune contrainte sur la position radiale n'a été lue ni cherchée ; RH n'est pas démontrée ; rien ici n'est lu comme
  excluant un zéro OFF. Résultat **négatif** sur le raccordement, **positif** sur la description compilée des rencontres.
