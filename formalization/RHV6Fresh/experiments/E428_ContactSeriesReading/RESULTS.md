# E428 — résultats (exécutée le 2026-11-04 ; `logs/e428{a,b}.log`, `data/e428{a,b}_results.json`)

Pré-enregistrement : `README.md` (commit c2e3e812, avant exécution). Aucun critère modifié après exécution. Module Lean
compilé avant exécution : `Terminal/ContactSeriesReading.lean` (deux tentatives journalisées `logs/lean_attempt{1,2}.log` ;
la seconde corrige une seule erreur de transport de cast (`push_cast` manquant sur deux hypothèses) et remplace un
`push_neg` déprécié par une réécriture explicite ; aucun énoncé changé ; aucun `sorry`, axiomes standards).

## E428(a) — lecture certifiée par série (4,5 s)

8 Tours authentiques (β = ½) + 16 Tours de séparation (β = 0,3 ; 0,7, mêmes hauteurs) ; ancrages 5, 541, 7 919 ;
séries de 12, 120, 1 200 écarts ; 96 120 lectures au total.

| Mesure | Valeur | Nature |
|---|---|---|
| encadrement `q̂e^{−h} < q < q̂e^{h}` | vrai sur les 96 120 lectures | identité (`estimate_brackets`) |
| lectures certifiées (`q̂(e^h − 1) < ½`) | 36 141 | mesure |
| **lectures certifiées fausses** | **0** | attendu compilé (`certified_rounding`, `certified_unique_integer`) |
| transitions lues (classe mod 6) fausses entre deux lectures certifiées | 0 | attendu compilé (`transitionOf_cls`) |
| lectures exactes non certifiées | 7 819 | mesure (jamais revendiquées) |
| ancien seuil (sur `q` inconnu) vs seuil corrigé (sur `q̂`) | 0 désaccord dans les deux sens ; 0 lecture fausse sous l'ancien | mesure, attendu compilé (`true_threshold_also_certifies`) |
| écart max `|q̂ − q|` sur lectures certifiées | < ½ partout | identité |
| jumeau mpmath 30 chiffres (zéros 1 et 2 001 052, ancrage 5, 13 membres, β = ½ et 0,3) | indices identiques, `q̂` à 6·10⁻¹⁶ relatif, mêmes certifications, mêmes entiers | jumeau |

Portée de la certification par Tour (β = ½ ; identique à β = 0,3 et 0,7) — premier membre non certifié :

| rang | T | h = π/T | T/(2π) | premier non certifié | lecture complète jusqu'à 19 400 ? |
|---|---|---|---|---|---|
| 1 | 14,13 | 0,222 | 2,2 | 5 (aucune) | non |
| 10 | 49,77 | 0,063 | 7,9 | 11 | non |
| 100 | 236,5 | 0,0133 | 37,6 | 41 | non |
| 1 000 | 1 419 | 0,00221 | 226 | 227 | non |
| 10 000 | 9 878 | 3,2·10⁻⁴ | 1 572 | 1 579 | non |
| 100 000 | 74 921 | 4,2·10⁻⁵ | 11 924 | 11 927 | non (ancrage 7 919 : 429/1 201) |
| 1 000 000 | 600 270 | 5,2·10⁻⁶ | 95 536 | aucun | **oui** |
| 2 001 052 | 1 132 491 | 2,8·10⁻⁶ | 180 248 | aucun | **oui** |

Lecture : la certification s'arrête exactement au premier qui dépasse `T/(2π)` (identité `q̂(e^h − 1) < ½` avec
`e^h − 1 ≈ h`). **La portée de la lecture est une fonction de la fréquence seule** ; elle est la même pour la Tour et
ses deux Tours de séparation à même hauteur.

**Information radiale dans les indices** (obligation C, volet a) : à même fréquence, les décalages `Δk` de la Tour
β = 0,3 diffèrent de ceux de la Tour β = ½ sur au plus 1 % des membres (valeurs −1 ou 0), uniquement pour les rangs
≤ 100 et sur des membres **non certifiés** ; pour les rangs ≥ 1 000, aucun décalage ne diffère. Sur les lectures
certifiées, les entiers lus sont identiques pour β = 0,3 ; 0,5 ; 0,7 (0 lecture fausse dans les trois cas).

## E428(b) — miroir, raccord individuel–collectif, recherche d'une loi (3,1 s)

2 001 événements (5 ≤ p ≤ 17 393) ; paires (β, 1 − β) = (0,3 ; 0,7) et (½ ; ½) à chaque hauteur.

**C — indices du miroir (corrigé, mesuré, jamais présumé)**

| rang | décalage de phase / π | indices absolus Tour ≠ miroir | différences de série Tour/miroir : valeurs ; violations de {−1, 0, 1} ; fraction ≠ 0 (2 001 000 paires) |
|---|---|---|---|
| 1 | 0,0090 | 1,0 % | {−1, 0, 1} ; 0 ; 2,0 % |
| 10 | 0,0026 | 0,10 % | {−1, 0, 1} ; 0 ; 0,2 % |
| 100 | 0,00054 | 0,10 % | {−1, 0, 1} ; 0 ; 0,2 % |
| 1 000 | 0,00009 | 0,05 % | {−1, 0, 1} ; 0 ; 0,1 % |
| ≥ 10 000 | < 10⁻⁵ | 0 | {0} ; 0 ; 0 |
| (½ ; ½), tous rangs | 0 | 0 | {0} ; 0 ; 0 |

Identités retrouvées : indices absolus du miroir dans {⌊s⌋, ⌈s⌉} du décalage (`mirror_stagePosition_difference`,
vrai partout) ; `log(C_0(β)/C_0(1−β))` contre la formule : 10⁻¹⁷ (`mirror_contact_log_ratio`) ; norme de la somme
miroir contre `2cosh(dt)` : 2·10⁻¹⁵, minimum 2,10 > 2 hors ligne (`mirrorMode_add_norm`) ; norme de la différence
contre `2|sinh(dt)|` : 2·10⁻¹⁵, de 0,65 à 6,9 (`mirrorMode_sub_norm` : aucun plancher). Jumeau mpmath (zéro 1, 10
événements, paire (0,3 ; 0,7)) : écarts d'indices identiques à numpy.

Lecture : la correction de l'auteur est exacte — Tour et miroir ne traversent pas toujours les mêmes cellules, et leurs
différences d'indices sur une série diffèrent d'une unité dans une fraction des cas, dans {−1, 0, 1} sans exception.
Cette information radiale des indices **décroît comme 1/T** (décalage `(φ_β − φ_{1−β})/π ≈ (1 − 2β)/(πT)`) : elle
existe aux basses fréquences et disparaît numériquement dès le rang 10 000. Elle est portée par les **positions
exactes des contacts**, pas par les lectures certifiées.

**A0 — raccord individuel–collectif** (H = 1 000, 649 zéros, canal intégré, convention `x·Σ`) : pour N ∈ {5, 7, 11, 101,
1 009}, somme des contributions individuelles = pas collectif direct à 10⁻¹³ près (identité
`truncatedStep_eq_sum_individual`) ; la plus grande contribution d'une Tour seule vaut entre 0,32 et 0,75 du collectif,
jamais 1 (`collective_eq_individual_add_rest`). Le pas « fond + collectif » vaut 4,09 ; 6,04 ; 10,22 ; 98,5 ; 1 000,0 :
c'est le pas de la primitive intégrée, c'est-à-dire ψ(N) tronqué à H (ψ(11) = 10,24, ψ(1009) ≈ 1 000), **pas** Λ(N)
(l'étiquette `log N` dans la ligne de journal et le champ `log_N` du JSON est une comparaison mal nommée, consignée
telle quelle ; Λ̂(N) est la différence seconde, `reconstructedVonMangoldt_eq_limit_of_individual_sums`).

**A4 — recherche d'une loi sur série** (1 989 fenêtres de 12 transitions, 1 652 mots distincts, 276 groupes de mots
partagés par ≥ 2 fenêtres) — critère : étendue ≤ 10⁻⁹ dans tous les groupes :

| candidat | loi ? | étendue max (rang 1 / rang 2 001 052, paire (0,3 ; 0,7)) | groupes constants |
|---|---|---|---|
| amplitude totale `β·log(p_fin/p_début)` | non | 0,67 / 0,67 | 0 % |
| somme des valeurs signées aux contacts de rencontre | non | 29,9 / 2·10⁻⁴ | 5 % / 0 % |
| somme orientée pondérée | non | 2,76 / 1,3·10⁻⁴ | 40 % / 0,4 % |
| nombre d'écarts d'indices Tour/miroir dans la fenêtre | non à bas rang (étendue 2, 87 %) ; « oui » dès le rang 10 000 **parce que identiquement nul** | — | — |
| différence d'amplitude Tour/miroir `(1 − 2β)·log` | non (nulle, donc « loi », seulement pour β = ½) | 0,89 | 0 % |

Même résultat pour la paire (½ ; ½) sur les candidats de longueur. **Aucune grandeur sur série n'est fonction du mot** ;
les seules « lois » sont des zéros identiques (candidat miroir à haute fréquence, différence d'amplitude en ligne).

## Verdict (critères pré-enregistrés)

* **A0 / A1–A3 : réussi.** Énoncés compilés ; 0 lecture certifiée fausse sur 36 141 ; mot lu exact sur toutes les
  paires certifiées ; jumeau exact. La loi de lecture existe et elle est certifiée depuis `(p_r, T, Δk)` seuls.
* **C : réussi au sens du critère** (0 violation de {−1, 0, 1}) ; information radiale des indices **mesurée** : présente
  aux basses fréquences (jusqu'à 2 % des paires de série au rang 1), nulle dès le rang 10 000, toujours en dehors des
  lectures certifiées.
* **A4 / B : négatif.** Aucun candidat ne satisfait le critère de mot. Aucune loi de conservation sur série déclarée.
* **D : non exécuté.** Frontière inchangée (réduction compilée à deux bornes, aucune démontrée). RH non démontrée ;
  rien n'exclut un zéro OFF.
