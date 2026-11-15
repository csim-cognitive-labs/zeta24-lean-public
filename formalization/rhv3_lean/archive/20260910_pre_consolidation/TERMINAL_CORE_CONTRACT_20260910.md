# RHV3Lean — CONTRAT TERMINAL NORMATIF — FIBRE / PASSAGE / R-PASS / EncZ=M

Date : 2026-09-10.

Autorités, dans cet ordre :

1. `docs/RHV2_STRATEGIE_SEMANTIQUE.md`, verrou final fibre/passsage ;
2. `docs/RHV2_STRATEGIE_MATHEMATIQUE.md`, §53 ;
3. `docs/RHV2_STRATEGIE_LEAN_TERMINAL_CORE_20260910.md` ;
4. le présent contrat d'implémentation RHV3.

Ce fichier ne crée aucune mathématique. Il rend les exigences terminales mécaniquement auditables et complète `formalization/rhv3_lean/CONTRACTS.md` sans modifier les autres contrats.

```text
ACTIVE_TERMINAL_ROUTE = FIBRE_PASSAGE_RPASS_MZ_EQ_M_NONZERO_PLACE_COLLISION
ACTIVE_SOURCE = O7_PLUS_O8
ACTIVE_SAME_OBJECT = SAME_PASSAGE
ACTIVE_TRANSPORT = T2_PLUS_R_PASS
ACTIVE_HISTORY = ENC_Z_EQ_M
ACTIVE_PRIME_FACT = EVERY_CANONICAL_PLACE_IS_NONNULL
ACTIVE_OFF_FACT = OFF_PRODUCES_REAL_CONSECUTIVE_NULL_PASSAGE
ACTIVE_CONTRADICTION = SAME_E_NULL_AND_NONNULL
```

## 1. Contrats de type

### ZERO-PASSAGE

Doit conserver simultanément :

```text
EARLIER_MEMBER
LATER_MEMBER
ORDER
CONSECUTIVITY
HEIGHT_GAP
NULLITY
NONNULLITY.
```

La nullité est :

```text
PZeroPassageRelationNull E <-> rZeroHeightGap E = 0
                               <-> same height endpoints.
```

### PRIME-PLACE

Doit conserver :

```text
RANK
ENTRY_PRIME = p_n
EXIT_PRIME = p_(n+1)
CANONICAL_HISTORY
TRANSITION_OCCURRENCE
PROVENANCE.
```

Chaque place est non nulle par stricte croissance des premiers.

### T2/R-PASS

Le réalisateur terminal est un **terme produit**, pas une `Prop` libre. Il transporte le même `TZeroPassage` vers la même `TPrimeHistoryPlace` et rend accessibles comme projections :

```text
endpoint preservation
order preservation
neighbourhood/corridor preservation
entry/exit preservation
occurrence/provenance preservation
nullity/non-nullity preservation.
```

Aucune de ces lois ne peut être un argument scientifique du theorem terminal.

## 2. Réalisateurs CORE obligatoires

| ID | Sortie forte | Nature requise | Entrées scientifiques résiduelles autorisées |
|---|---|---|---|
| CORE-01 | vrai miroir OFF | theorem | 0 |
| CORE-02 | deux membres distincts même fibre | theorem | 0 |
| CORE-03 | fibre finie | theorem | 0 |
| CORE-04 | paire consécutive dans fibre | theorem | 0 |
| CORE-05 | `E_OFF : TZeroPassage` | producer | 0 |
| CORE-06 | `PZeroPassageRelationNull E_OFF` | theorem | 0 |
| CORE-07 | transport T2/R-PASS canonique | producer/inhabitant | 0 |
| CORE-08 | occurrence de `E` dans `EncZ` | theorem | 0 |
| CORE-09 | `EncZ = M` | theorem | 0 |
| CORE-10 | occurrence de `E` dans `M` | theorem | 0 |
| CORE-11 | occurrence = place canonique `Theta_n` | theorem | 0 |
| CORE-12 | place canonique non nulle | theorem | 0 |
| CORE-13 | `Null_Z(E) -> Null_P(Phi(E))` | theorem projection de CORE-07 | 0 loi globale libre |
| CORE-14 | SAME-E contradiction | theorem | 0 |
| CORE-15 | aucun OFF supérieur | theorem | 0 |
| CORE-16 | tous vrais zéros non triviaux centraux | theorem | 0 |
| CORE-17 | `RiemannHypothesis` | terminal theorem | 0 |

Règle : un theorem de forme `hTransport -> ...`, `hRPass -> ...`, `hLocalLaw -> ...`, `hSameC3 -> ...` ne réalise aucun CORE si l'argument est précisément la loi à produire.

## 3. Gates SAME-object

À chaque handoff :

```text
SAME_MEMBER
SAME_PASSAGE
SAME_OCCURRENCE
SAME_HISTORY
SAME_E_OFF
```

et, pour le triple :

```text
SAME_MIDDLE
SAME_MIDDLE_TOWER
SAME_MIDDLE_CONTACTS
SAME_MIDDLE_C3
SAME_MIDDLE_OCCURRENCE.
```

Une égalité de valeur numérique ne réalise pas un SAME-object.

## 4. Handoff source -> EncZ -> M

Le contrat exact est :

```text
E : TZeroPassage
  -> T2/R-PASS produit Phi(E)
  -> Phi(E) est l'occurrence reconstruite de E dans EncZ
  -> EncZ=M réécrit CETTE occurrence
  -> Phi(E)=Theta_n dans M.
```

Interdit :

```text
choisir n puis déclarer que Theta_n représente E ;
construire une nouvelle occurrence après EncZ=M ;
perdre la fibre avant T2 ;
prendre EncZ=M seul comme substitut de T2/R-PASS ;
identifier numériquement gap zéro et gap premier.
```

## 5. Handoff OFF -> E_OFF

Le theorem OFF doit produire lui-même :

```text
true mirror
same height
distinct members
same real fiber
finite fiber
adjacent pair A,B
real TZeroPassage E_OFF
Null_Z(E_OFF).
```

Aucun argument `hConsecutive`, `hFiniteFiber`, `exactlyTwoMembers` n'est admis dans le terminal.

## 6. Tous les cas de fibre

Le producteur doit fonctionner indépendamment du cardinal exact :

```text
cardinality=2      -> paire miroir adjacente ;
cardinality>2      -> paire adjacente interne dans le bloc de même hauteur ;
triple local       -> (0,d), (d,0) ou (0,0) ;
quartet conjugate  -> contrainte dupliquée, aucune compensation.
```

Le cardinal exact n'est jamais une prémisse.

## 7. Transitions

Rigidités conservées :

```text
tau11 <-> 1->1 <-> residue 0
tau15 <-> 1->5 <-> residue 4
tau51 <-> 5->1 <-> residue 2
tau55 <-> 5->5 <-> residue 0.
```

Le terminal ne suppose ni `tau15` ni `tau51`. Toutes les places physiques sont non nulles :

```text
tau11 -> p_n != p_(n+1)
tau15 -> p_n != p_(n+1)
tau51 -> p_n != p_(n+1)
tau55 -> p_n != p_(n+1).
```

Les labels 2/4 servent à l'orientation et à la non-substitution de l'occurrence, pas à créer la contradiction.

## 8. Modules existants : classement terminal

```text
Objects/OffFibreAndPassage.lean
  ROLE = ACTIVE_PRODUCER

Objects/PrimeGapGrammar.lean
  ROLE = ACTIVE_PRODUCER

Objects/PlaceAndLocalLaw.lean
  ROLE = ACTIVE_PARENT

Objects/Passage.lean
  ROLE = ACTIVE_O8

Objects/Triple.lean
  ROLE = ACTIVE_O9

Objects/TransportOnOperator.lean
  ROLE = PARTIAL_BUILDING_BLOCK_UNTIL_FULL_T2_RPASS_PRODUCER

Objects/TripleTransitionRigidity.lean
  theorem thm_off_impossible_of_transitionDegeneracyTransport
  ROLE = LEGACY_DIAGNOSTIC_CONDITIONAL_ONLY
  TERMINAL_CONE = FORBIDDEN

Objects/SamePrimeCollision.lean
  ROLE = LEGACY_DIAGNOSTIC
  TERMINAL_CONE = FORBIDDEN
```

## 9. Interdictions terminales

Le strength audit doit refuser le theorem final ou ses producteurs si leur cône contient comme prémisse scientifique libre :

```text
RiemannHypothesis
allUpperOnCriticalLine
PNoNullZeroPassage
PSameHeightSameCentralPrime
sameC3(original,mirror)
hTransitionTransport
PTransitionNullityPreserved
hNullityPreserved
hRPass non produit
hLocalLaw non produit
same contacts from same height
same cell from same height
dZeroGap = primeGap
exactlyTwoMembers
exactlyThreePrimes
nearestPrime
free rank matching
tau15/tau51 required case
prime-driven Tour/contact selection.
```

## 10. Cibles Comparator minimales

```text
CORE.OFF_TRUE_MIRROR
CORE.OFF_SAME_FIBRE
CORE.OFF_CONSECUTIVE_NULL_PASSAGE
CORE.T2_RPASS_PRODUCER
CORE.PASSAGE_TO_ENCZ_OCCURRENCE
CORE.ENCZ_EQ_M
CORE.PASSAGE_TO_CANONICAL_OCCURRENCE
CORE.CANONICAL_PLACE_NONNULL
CORE.NULLITY_TRANSPORT_PROJECTION
CORE.SAME_E_CONTRADICTION
CORE.ALL_UPPER_CENTRAL
CORE.ALL_NONTRIVIAL_CENTRAL
CORE.RIEMANN_HYPOTHESIS
```

Comparator doit comparer les **types forts**, pas seulement des consumers conditionnels.

## 11. Theorem terminal cible

Le seul statut final admissible est un theorem de type exact :

```lean
theorem riemannHypothesis_by_samePassage : RiemannHypothesis := by
  ...
```

Aucun argument scientifique.

Avant certification :

```text
lake build = PASS
sorry = 0
admit = 0
new axiom = 0
#print axioms = [propext, Classical.choice, Quot.sound]
Comparator delta = PASS
Comparator cumulative = PASS
fidelity audit = PASS
SAME-object gates = PASS
CORE-01..CORE-17 = EXACT/CLOSED_ON_ROUTE.
```

## 12. Statut de migration

Ce contrat ne prétend pas que le code courant réalise déjà CORE-01..CORE-17. Il fixe la cible non affaiblie.

```text
MASTER_SEMANTIC = CLOSED
MASTER_MATHEMATICAL = CLOSED
MASTER_LEAN_TERMINAL_CORE = FROZEN
RHV3_CONTRACT = FROZEN_BY_THIS_FILE
CURRENT_CODE_MUST_BE_REALIGNED = true
LEAN_FINAL_RH_CERTIFIED = false
```

La prochaine modification de code doit donc **réaligner les réalisateurs sur ce contrat**, et non créer une quatrième route terminale.