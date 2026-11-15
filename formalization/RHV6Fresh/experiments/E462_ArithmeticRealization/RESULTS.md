# E462 — résultats (2026-11-09) — verdict A

* Module `RHV6Fresh/Terminal/ArithmeticRealization.lean` (isolé, non importé par `RHV6Fresh.lean`) : 1 structure, 4 définitions,
  11 théorèmes ; compilé à la PREMIÈRE tentative (`attempts/build_attempt1.txt`, EXIT=0) ; 8 `#print axioms`, tous
  `[propext, Classical.choice, Quot.sound]` ; aucun `sorry`. Build complet vert (`logs/lake_build_full.txt`, 9064 jobs, EXIT=0).
* R1–R8 compilés dans la forme pré-écrite, sans changement d'énoncé.

## Ce qui est acquis
* Une définition de la réalisation arithmétique d'une Tour qui ne lit ni son poids ni l'annulation de zêta en son point : figurer, avec
  un poids non nul, dans une recomposition du signal lissé des premiers (moins un fond fixe).
* Réalisée ⟺ porteuse ⟺ zêta s'annule au point de la Tour (hauteur positive). L'énoncé de la relecture externe est un théorème.
* Il existe ⟺ pour toute : toute recomposition contient chaque porteuse ; aucune ne charge une non-porteuse.
* Le lecteur du mot total défini par cette réalisation est un lecteur d'E461, et coïncide avec lui sur tous les mots.
* Classement : « réalisée ⟹ sur la ligne » ⟺ RH (compilé dans les deux sens). Jamais une prémisse.

## Ce qui n'est pas acquis (dit tel quel)
* Aucune exclusion d'un zéro hors ligne : une Tour hors ligne porteuse est réalisée comme les autres. Frontière inchangée.
* La réalisation est collective et existentielle ; aucun critère cellule par cellule sur la seule Tour.
* Le fond fixe contient encore deux constantes de zêta et la série des zéros triviaux. Une version où ces deux constantes sont laissées
  libres est possible (même unicité, deux exposants de plus) ; elle n'est pas faite ici.
* L'analyse est celle de `SpectralUniqueness.lean` (2026-09-30) ; E462 est un raccord, pas un résultat d'analyse nouveau.
