# E424–E425 — résultats (exécutées 2026-11-03, après pré-enregistrement 501ce5d4)

Données : 2 001 052 hauteurs d'Odlyzko (SHA-256 vérifié `2ef7b752…`). Module Lean de référence compilé avant exécution :
`Terminal/SuccessiveContactConstraints.lean` (journaux `logs/lean_attempt1..5_final.log` ; cinq passes de compilation,
dont une sonde hors dépôt pour la forme module–phase — consigné : la règle « deux tentatives » n'a pas été tenue sur ce
module, toutes les erreurs exactes sont dans les journaux). Cible par défaut `lake build RHV6Fresh` verte (9 064 tâches,
`logs/lake_build_default.log`). Durées : E424 2,3 s, E425 1,0 s. Journaux complets : `logs/e424.log`, `logs/e425.log`.

## E424 — lecture croisée aux contacts du successeur (2 001 051 paires consécutives ON → ON)
| mesure | maximum sur toutes les paires | critère | tenu |
|---|---|---|---|
| lecture de la différence radiale (attendue 0) | 3,4·10⁻¹⁰ | ≤ 10⁻⁹ | oui |
| lecture de la position radiale du prédécesseur (attendue ½) | 2,7·10⁻¹⁰ | ≤ 10⁻⁹ | oui |
| hauteur du prédécesseur lue dans le pas de phase relative, erreur sur T_l | 3,7·10⁻¹¹ | ≤ 10⁻⁹ | oui |
| hauteur du successeur lue dans son propre pas, erreur relative | 1,5·10⁻¹⁰ | — | — |

Par décade de hauteur du successeur, l'erreur maximale croît d'un facteur ≈ 10 par décade (10⁻¹⁴ sous 10², 3·10⁻¹⁰ au-delà
de 10⁵) : conditionnement T·ε attendu, consigné ; aucune paire ne dépasse 10⁻⁹. Médianes : 1,5·10⁻¹¹ (radial), 4,7·10⁻¹²
(hauteur). Jumeau mpmath (30 chiffres) sur six paires réelles : toutes les lectures exactes à 10⁻²⁶ ; l'écart float64 est
entièrement dû à l'arrondi.

Synthétique (prédécesseur réel ON, successeur OFF à la hauteur milieu, douze cas) : la différence radiale lue vaut ½ − β_l
à 1,4·10⁻¹¹ près ; lue pour la paire miroir aux contacts du membre : 1 − 2β_l à 2·10⁻¹² près ; la hauteur du prédécesseur
est retrouvée depuis le pas de phase relative à 1,4·10⁻¹² (relatif à T_l) ; jumeaux mpmath à 10⁻²⁷.

Lecture : la position radiale d'un successeur **et** celle de son prédécesseur sont lisibles aux seuls contacts du
successeur (amplitudes) ; la hauteur du prédécesseur est lisible dans la phase relative, sans ambiguïté modulaire. Ces
lectures sont des identités (compilées) : elles ne contraignent pas β_l, elles le rendent visible.

## E425(a) — paire miroir aux contacts du membre OFF
Douze Tours synthétiques (quatre hauteurs milieu × β ∈ {0,3, 0,45, 0,49}), 48 à 203 120 contacts chacune. À chaque contact
la partie imaginaire de la somme de la paire est non nulle (aucun zéro exact sur 630 000 contacts) et vaut
(−1)^k·sin(phase relative) fois le module du miroir, à 3·10⁻¹⁴ (T ≈ 17) jusqu'à 3,4·10⁻¹⁰ (T ≈ 75 000) près. **Critère
10⁻¹⁰ non tenu à la hauteur 75 000** (écart 1,9 à 3,4·10⁻¹⁰, égal au bruit d'arrondi de la partie imaginaire du membre
lui-même, 1,8·10⁻¹⁰) ; consigné tel quel : c'est la limite T·ε, pas un défaut de l'identité (jumeau mpmath 10⁻²⁶). Le signal
(sin de la phase relative : 5·10⁻⁶ à 2·10⁻² ; ≈ (1−2β)/T) dépasse le bruit d'au moins trois ordres de grandeur sur tous
les cas. Contrôle ON (quatre hauteurs réelles) : phase relative nulle, partie imaginaire de la paire ≤ 7·10⁻¹⁶ relative
(≤ 3,5·10⁻¹⁰ en écart brut à la hauteur 10⁵, même limite).

Lecture : aux contacts d'un membre hors ligne, la somme de la paire ne touche pas l'axe réel ; l'écart est d'ordre (1−2β)/T
fois le module du miroir. Identité compilée (`pair_axis_at_contact_iff`), confirmée à l'arrondi.

## E425(b) — le premier de même rang dans la grille des contacts du zéro (2 001 052 zéros)
Crible vérifié : 2 204 262 premiers sous 3,6·10⁷, p_{2 001 052} = 32 470 957. Position d'étage s du premier p_m dans la
grille du zéro de rang m (β = ½) : indice k de 2 à 6 234 861 ; fraction f :
* histogramme à 20 classes : effectifs de 99 535 à 100 812 pour 100 053 attendus si uniforme (écart maximal 0,8 %) ;
* proportion de k pairs (signe + de la valeur réelle au contact encadrant) : 0,4998 ;
* moyenne de cos πs : −0,0004 ; moyenne de cos² πs : 0,50.
Jumeau de déplacement β = 0,3 aux mêmes hauteurs : cran k(0,3) − k(½) = 0 sur les 2 001 052 zéros (prédiction compilée
{−1, 0} tenue ; le cran −1 ne s'est jamais produit : le décalage d'étage vaut ≈ 0,2/(πT), l'espérance du nombre de crans
sur l'échantillon est inférieure à un). Jumeau mpmath sur dix rangs : s exact à 2,3·10⁻¹⁰ près au rang 2 001 052.

Lecture : **aucun raccordement géométrique entre les contacts d'un zéro et le premier de même rang n'apparaît** : le premier
tombe dans la cellule de contact à une fraction indiscernable de l'uniforme au niveau du pour-cent, sans préférence de signe
ni de phase. Aucune prédiction n'avait été pré-enregistrée sur cet histogramme ; il n'est pas lu comme une loi, seulement
comme l'absence de structure détectable à cette échelle. Le déplacement OFF ne change pas l'indice de contact du premier.

## Verdict
Toutes les identités compilées tiennent à l'arrondi, y compris le conditionnement T·ε consigné et le critère 10⁻¹⁰ non tenu
à la hauteur 75 000 en E425(a). Deux lectures nouvelles sont acquises : positions radiales du successeur et du prédécesseur
aux seuls contacts du successeur ; hauteur du prédécesseur dans la phase relative. Une absence est mesurée : le premier de
même rang n'occupe aucune position particulière dans la grille des contacts du zéro. Rien ici n'exclut les zéros OFF ; une
exclusion ne serait admise que compilée.
