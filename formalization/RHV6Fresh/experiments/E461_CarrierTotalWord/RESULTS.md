# E461 — résultats (2026-11-09) : verdict A

* Module `RHV6Fresh/Terminal/CarrierTotalWord.lean` : isolé, 2 définitions et 7 théorèmes, compilé à la PREMIÈRE tentative
  (`attempts/build_attempt1.txt`, EXIT=0), 7 `#print axioms` standard (propext, Classical.choice, Quot.sound), bannissement spectral à
  zéro, aucun `sorry` (le seul mot « sorry » du fichier est dans l'en-tête), build complet vert (`logs/lake_build_full.txt`, 9064 jobs).
* T1–T7 compilés dans la forme pré-écrite, sans changement.
* Pas de jumeau numérique : aucun énoncé chiffré.

## Ce que cela dit de la proposition de l'auteur, en mots
* ACQUIS par théorème : le mot total d'une Tour décide si elle est porteuse. Un lecteur de la sélection sur le mot total existe ; il
  est unique sur les mots de Tours ; il est vrai sur le mot de tout zéro vrai ; il ne dépend jamais d'une fenêtre finie. La forme
  « la totalité des contacts identifie un zéro » est donc vraie au sens de l'existence.
* NON acquis : le lecteur compilé est défini par le poids, c'est-à-dire par l'annulation de zêta. La « relation exacte aux premiers »
  qui le définirait sans zêta n'existe pas dans le corpus. C'est l'obligation ouverte, seulement nommée (réalisation arithmétique).
* Classement : « lecteur ⟺ porteur » vaut pour les zéros de la ligne comme pour d'éventuels zéros hors ligne : pas une reformulation
  de RH, aucune exclusion hors ligne à elle seule. Aucune contradiction ; frontière inchangée.

## Ajout du 2026-11-09 (§19.91) : T8–T9, verdict A
Proposition précisée de l'auteur : une Tour qui a les mêmes contacts que la Tour d'un zéro, aux mêmes endroits, avec les premiers dans
les mêmes cellules à l'infini, est un zéro. Compilé à la première tentative (`attempts/build_T8T9_attempt1.txt`, EXIT=0, axiomes
standard ; build complet vert, `logs/lake_build_full_T8T9.txt`) :
* T8 `tower_is_zero_of_same_word_as_zero` : même mot total que le mot d'un zéro vrai ⟹ porteuse, même hauteur, même position radiale.
* T9 `zeta_eq_zero_of_same_word_as_zero` : zêta s'annule alors au point de la Tour.
Limite dite telle quelle : le théorème compare à la Tour d'un zéro déjà connu ; le critère sans zéro de référence reste ouvert.
