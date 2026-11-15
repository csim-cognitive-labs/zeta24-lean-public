> Version française conservée à titre de référence. Main language: English, see README.md.

# E462 — Φ6 : la réalisation arithmétique d'une Tour, définie par la recomposition collective des premiers — pré-enregistrement

Référence : `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.92 ; §19.90–19.91 (E461, proposition de l'auteur, levée de l'interdiction du
collectif) ; `Terminal/SpectralUniqueness.lean` (unicité de la représentation du canal, 2026-09-30). Ordre de l'auteur du 2026-11-09 :
« je valide continues » (piste nommée en §19.91). Aucune hypothèse admise, aucun axiome, aucun `sorry` ; module isolé
`RHV6Fresh/Terminal/ArithmeticRealization.lean`, NON ajouté à `RHV6Fresh.lean`. Aucun premier ni zéro hors ligne testé. Ce commit précède
toute compilation du module (aucune sonde préalable).

## Audit préalable des modules collectifs (fait avant ce pré-enregistrement)
`SpectralUniqueness.lean` compile déjà, sans prémisse : le canal des zéros est une fonction du seul côté arithmétique
(`channel_eq_arithmetic` : somme lissée de von Mangoldt moins le fond) ; toute représentation de ce canal par une famille localement
finie de points distincts contient chaque zéro avec sa multiplicité (`contains_member`) et ne porte aucun poids hors des zéros
(`no_intruder`). Ce module n'a jamais été relié aux Tours ni au lecteur d'E461. E462 fait ce raccord, sans rien démontrer de neuf en
analyse.

## Définition proposée (indépendante du poids et de l'annulation de zêta au point de la Tour)
* `ArithmeticRecomposition` : une famille de points distincts du plan, localement finie, munie de poids, dont la série de noyaux redonne,
  pour tout `x > 1`, la somme lissée de von Mangoldt moins le fond lisse. Le membre de droite ne lit que les premiers et un fond FIXE,
  le même pour toutes les Tours. Dit honnêtement : ce fond contient la série des zéros triviaux et deux constantes de zêta (dérivée
  logarithmique en 0 et en −1) ; il ne contient ni le point de la Tour, ni son poids, ni aucun zéro non trivial.
* `ArithmeticallyRealized β T` : il existe une recomposition arithmétique qui porte un poids non nul au point de la Tour.

## Ce que le module doit compiler (énoncés pré-écrits, en mots)
* R1 `ArithmeticRecomposition.toSpectral` : toute recomposition arithmétique est une représentation du canal (par `channel_eq_arithmetic`).
* R2 `trueRecomposition` : une recomposition arithmétique existe (celle des zéros).
* R3 `arithmeticallyRealized_iff_isCarrier` : pour toute hauteur strictement positive, réalisée ⟺ porteuse.
* R4 `arithmeticallyRealized_iff_zeta_eq_zero` : pour toute hauteur strictement positive, réalisée ⟺ zêta s'annule au point de la Tour.
  C'est l'énoncé demandé par la relecture externe : « réalisation arithmétique exacte ⟺ Tour issue d'un zéro ».
* R5 `recomposition_contains_carrier` : TOUTE recomposition arithmétique porte un poids non nul au point de toute Tour porteuse ;
  `recomposition_weight_eq_zero_of_not_isCarrier` : AUCUNE ne porte de poids au point d'une Tour non porteuse. (Il existe ⟺ pour toute.)
* R6 `arithmeticWordCarrier` et `readsCarriers_arithmeticWordCarrier` : le lecteur du mot total défini par la réalisation arithmétique
  lit la sélection (c'est un `ReadsCarriers` d'E461, cette fois défini sans le poids).
* R7 `arithmeticWordCarrier_iff_totalWordCarrier` : il coïncide avec le lecteur d'E461 sur tous les mots.
* R8 `riemannHypothesis_iff_realized_on_line` : RH ⟺ toute Tour réalisée (hauteur positive) est sur la ligne.

## Classement contre RH (dit avant compilation)
* La définition n'est pas une hypothèse : rien n'est posé. R3–R7 sont inconditionnels et valent pour les porteurs de la ligne comme hors
  ligne ; ils n'excluent aucun zéro hors ligne. Ce n'est pas une reformulation de RH.
* R8 est le classement lui-même : « réalisée ⟹ sur la ligne » ÉQUIVAUT à RH (implication et réciproque compilées) ; ce n'est jamais une
  prémisse. La frontière ne bouge pas : il reste à trouver pourquoi une Tour hors ligne ne peut pas figurer dans la recomposition.
* Limite dite d'avance : la réalisation ainsi définie est COLLECTIVE et existentielle (elle quantifie sur les recompositions du signal
  entier des premiers) ; ce n'est pas un critère lu sur les cellules de la seule Tour. « Les premiers tombent dans les cellules
  lorsqu'ils le doivent », lu cellule par cellule sur une Tour seule, n'est pas fourni ; E457 interdit d'ailleurs toute fenêtre finie.

## Verdicts pré-écrits
* A : R1–R8 compilés en au plus deux tentatives, axiomes standard, build complet vert.
* B : un énoncé demande une forme différente de celle pré-écrite (dite telle quelle).
* C : échec après deux tentatives (consigné, module retiré).
Pas de jumeau numérique : aucun énoncé chiffré, tout est logique.
