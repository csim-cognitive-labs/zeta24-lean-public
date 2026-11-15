> Version française conservée à titre de référence. Main language: English, see README.md.

# E463 — Φ7 : la recomposition des premiers lue sur les cellules d'une Tour — pré-enregistrement

Référence : `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.93 ; E462 (§19.92), E436–E438 (§19.52–19.56). Ordre de l'auteur du 2026-11-09 :
« Fais cet audit et continue ». Aucune hypothèse admise, aucun axiome, aucun `sorry` ; module isolé
`RHV6Fresh/Terminal/RecompositionOnCells.lean`, NON ajouté à `RHV6Fresh.lean`. Ce commit précède toute compilation (aucune sonde).

## Audit (fait avant ce pré-enregistrement)
* E436–E438 découpent un écart par les contacts d'UNE Tour, dans le canal brut, pour des familles FINIES avec un reste explicite ;
  E437 compile que le saut d'une rencontre est porté en entier par ce reste, jamais par une famille finie.
* E462 recompose le signal LISSÉ des premiers par la famille entière, sans reste, de façon unique.
* Les deux n'ont jamais été réunis. Le pont : multiplié par l'abscisse, le noyau lissé d'une Tour est une primitive de sa valeur
  brute ; sa variation d'une abscisse à l'abscisse située une cellule plus loin est donc la part de la Tour sur cette cellule.

## Ce que le module doit compiler (énoncés pré-écrits, en mots)
* K1 `integratedKernel` (définition : abscisse fois noyau lissé) et sa forme close `integratedKernel_eq`.
* K2 `cell_step_cpow`, `cell_step_kernel` : avancer d'une cellule de la Tour multiplie son noyau intégré par un facteur exact,
  négatif, dont le module ne dépend que de la fréquence et de la position radiale.
* K3 `towerCellShare` (définition : part de la Tour sur une cellule) et `towerCellShare_eq` (forme close).
* K4 `towerCellShare_next` : les parts sur deux cellules consécutives sont dans ce même rapport (signe alterné, amplitude fixée).
* K5 `cell_ratio_reads_radial` : à fréquence donnée, ce rapport détermine la position radiale.
* K6 `towerCellShare_ne_zero_iff` : la part sur une cellule est non nulle si et seulement si le poids est non nul.
* K7 `recomposition_piece_balance` : pour toute recomposition arithmétique et toute pièce, la somme des parts de tous les membres
  égale la variation du signal lissé des premiers (fond retiré), multiplié par l'abscisse.
* K8 `recomposition_cellShare_ne_zero_of_isCarrier`, `recomposition_cellShare_eq_zero_of_not_isCarrier` : dans toute recomposition,
  une Tour porteuse a une part non nulle sur CHACUNE de ses cellules ; une Tour non porteuse a une part nulle sur chacune.

## Classement contre RH (dit avant compilation)
Aucune hypothèse posée. K1–K8 valent sur la ligne comme hors ligne. Le rapport de K4 lit la position radiale (troisième ordre respecté)
mais n'en interdit aucune : rien n'exclut un zéro hors ligne. Non fait ici : écrire le membre arithmétique de K7 comme somme de pentes
de la demande brute sur les pièces d'E438 (identité finie, à faire dans un second temps si l'auteur le veut).

## Verdicts pré-écrits
A : K1–K8 compilés en au plus deux tentatives, axiomes standard, build complet vert. B : un énoncé change de forme (dit tel quel).
C : échec après deux tentatives (consigné, module retiré). Pas de jumeau numérique : identités exactes.
