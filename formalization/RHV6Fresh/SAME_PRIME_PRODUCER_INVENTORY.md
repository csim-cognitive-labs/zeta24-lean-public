# SAME-PRIME : provenance des producteurs au HEAD 8d294e78

Aucun nouveau producteur ni lecteur n'est défini. Les noms RHV5 sont conservés.

| Objet | INPUTS | HOW_STATE_IS_SELECTED | memberMZOccurrence utilisé | nZeroSourceIndex utilisé | TARGET_PRIME utilisé | CAN_BE_AUTHENTIC_INDEPENDENT_PRODUCER |
|---|---|---|---|---|---|---|
| selectedState | z | floor depuis memberCanonicalAnchor | oui, égalité M9 | oui transitivement | oui | FALSE |
| authenticStateFromZero | z | alias selectedState | oui | oui | oui | FALSE |
| canonicalState | z | countingState z (memberMZOccurrence z) | oui | oui | oui | FALSE |
| heightEventState | z | countingState z (heightEventPrime z) | non | non (index hauteur distinct) | oui, premier de hauteur | FALSE |
| towerStateAt | z,k | k fourni | non intrinsèquement | non intrinsèquement | dépend de k fourni | FALSE : famille sans sélection |
| countingState | z,q | ceil((T log q-phase)/pi)-1 | dépend de q | dépend de q | oui si q est la cible | FALSE : localisation fournie |
| trueTowerOf | z | famille entière, aucune cellule sélectionnée | non | non | non | FALSE : ne produit pas un état distingué |
| betaTContactState/baseContacts | z | branche zéro | non | non | non | FALSE : contrôle, authenticité non prouvée |
| thresholdStateFromZero | z | première incidence non négative >=2 | non | non | non | FALSE : round-trip prouvé, identification événementielle absente |
| pointedPrime | S | aucune sélection; (engagedEvent S).leftPrime | hérité de S | hérité de S | hérité de S | FALSE : lecteur, pas producteur d'état |
| engagedEvent | S | rang countedPlace S - 1 | hérité de S | hérité de S | hérité de S | FALSE : même distinction |
| countedPlace | S | comptage nEdgePrimeRank S.contactPlus | hérité de S | hérité de S | hérité de S | FALSE : même distinction |
| nextCountedAnchor | S | fnPrimeAtRank (countedPlace S) | hérité de S | hérité de S | hérité de S | FALSE : même distinction |

## Dépendances vérifiées

selectedState -> selectedAddress -> memberAnchorReal -> memberCanonicalAnchor
= memberMZOccurrence -> fnPrimeAtRank(nZeroSourceIndex z).

heightEventState -> countingState -> countingAddress(heightEventPrime z);
heightEventPrime -> nHeightEventMZOccurrence(heightEventOf z)
-> fnPrimeAtRank(nZeroHeightEventIndex(heightEventOf z)).
Ce n'est pas un comptage calculé indépendamment depuis les contacts.

pointedPrime -> engagedEvent -> countedPlace -> contactBlockRightRank
-> nEdgePrimeRank(contactPlus). Ce lecteur existant est disponible une fois S produit.

Les fichiers AxialIncidenceReading, PassageTravel et MirrorOrientation fournissent
des comparaisons de familles ou des cellules sélectionnées depuis une donnée préalable;
ils ne fournissent pas la sélection indépendante demandée. SameRungCounting exige
explicitement une égalité de comptage; l'absence de premier dans la fenêtre est un
critère équivalent, pas une conclusion inconditionnelle.

## Premier maillon manquant

membre -> état authentiquement distingué, sans cible arithmétique de sélection.
Le type `TTrueHarmonicTowerState z` seul ne certifie pas cette provenance :
`towerStateAt z k` l'habite pour tout k. La bibliothèque ne contient pas de prédicat
indépendant certifiant l'authenticité demandée; nous n'en inventons pas un.

L'unique lecture existante donnant SAME-PRIME inconditionnellement à même hauteur
est la lecture hauteur. Son raccord exact serait, pour le second membre b :

```lean
⊢ memberMZOccurrence b = heightEventPrime b
```

`height_member_identification_iff b` le réduit à `nFibreLaterCount b = 0`.
`offPair_existing_readings` fournit au contraire
`memberMZOccurrence b ≠ heightEventPrime b` pour le même b extrait sous OFF.
Cela n'est pas une contradiction tant que l'égalité n'est pas prouvée indépendamment.
Aucun terme de cette égalité n'est ajouté.

CLASSIFICATION=C
MASTER_SOURCE=NONE pour un producteur indépendant satisfaisant la nouvelle directive.
Les maîtres du HEAD de base décrivent EXPECTED MINIMUM, pas ce producteur.
NEW_MATHEMATICAL_FORMULA_REQUIRED=FALSE : aucune formule nouvelle justifiée identifiée;
une preuve de sélection/authenticité manque avant tout calcul terminal.

La paire miroir littérale et le passage consécutif extrait ne sont pas identifiés.
Aucun troisième membre n'est introduit dans la composition.

Les imports historiques de ce diagnostic servent à vérifier les signatures et les
preuves existantes; ils ne réactivent aucune ancienne route terminale.
