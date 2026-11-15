> **SUPERSEDED 2026-09-22** — modules supprimés ; voir `AUDIT_VOYAGE_DEUX_TOURS_20260922.md`.

# AUDIT — Mâchoires terminales RHV6 : fidélité de la solution Lean et poids logique exact de ce qui manque

Date : 2026-09-21. Base auditée : `formalization/RHV6Fresh` à `6e8d8aae` (solution livrée par la session précédente, « solution de Sonnet »), maîtres `RHV6_STRATEGIE_{SEMANTIQUE,MATHEMATIQUE,LEAN}.md` — sections normatives terminales du 2026-09-21 (« CORRECTION NORMATIVE TERMINALE / LEAN — DIRECT EXPECTED/OBSERVED »).

Tout ce qui est affirmé ci-dessous comme *compilé* l'est dans `RHV6Fresh/Terminal/JawEquivalence.lean` et `RHV6Fresh/Tower/CoarseJourneyState.lean`, rattachés à `RHV6Fresh.lean`, build vert, `#print axioms` = `[propext, Classical.choice, Quot.sound]` pour chaque théorème cité (voir `RHV6Fresh/Audit.lean`).

---

## 0. Résumé exécutif

1. La solution précédente est architecturalement propre (0 orphelin, 0 objet interdit vivant, 0 sorry/admit) mais son théorème final `riemannHypothesis_conditional` **n'est pas une décomposition de RH** : chacune de ses deux hypothèses implique RH à elle seule, et la seconde est réfutable.
   - `POffImpliesObligations ↔ RiemannHypothesis` — compilé (`offImpliesObligations_iff_riemannHypothesis`).
   - `PEveryUpperHasAuthenticPredecessor → IsEmpty TrueZero` — compilé (`isEmpty_of_everyUpperHasPredecessor`) : le plus petit zéro supérieur n'a pas de prédécesseur supérieur.
2. La raison de fond, compilée pour **tout** producteur d'état `J` : dès que la mâchoire de progression (obligation B) tient, la mâchoire OFF (obligation A) **est** l'hypothèse de Riemann, mot pour mot :
   `PProgressionJaw J → (POffDeficitJaw J ↔ RiemannHypothesis)` (`offDeficitJaw_iff_riemannHypothesis`).
3. L'obligation B est déchargée inconditionnellement par un producteur Tour-intrinsèque explicite, `coarseJourneyState` (forme close de `(T, φ)` et d'une constante universelle du comptage des zéros de Backlund — aucun premier n'entre) : `progressionJaw_coarseJourneyState`. Donc B n'a pas de contenu propre ; tout le poids du terminal est dans A, et A ≡ RH.
4. Conséquence : **aucune liste de lemmes portant sur la Tour, les contacts, les grammaires ou le comptage ne peut produire la contradiction terminale sans une entrée de force RH.** Ce n'est pas une estimation de difficulté : c'est une équivalence compilée. `RH_FOUND=FALSE` reste exact.

---

## 1. Audit de fidélité de la solution précédente, fichier par fichier

| Fichier | Verdict | Détail |
|---|---|---|
| `CleanTerminal.lean` | CONFORME | `occurrence z := nMemberMZOccurrence z`, `= p_{n(z)}` via M9a prouvé (`thm_memberMZOccurrence_eq_canonicalAnchor_unconditional`). Transcrit Math §1 (« M^Z = M → progression obligatoire »). Aucun objet interdit. |
| `Grammar/ExpectedMinimum.lean` | CONFORME | `expectedMinimumPrime a := p_{n(a)+1}`, `= occurrence b` sur un passage. Math §1 exact. |
| `Tower/{TrueTower,Incidences}.lean` | CONFORME | Tour = `exp((φ+kπ)/T)`, φ = atan(T/β). Aucun sélecteur. Lean master §19 respecté (incidences candidates). |
| `Terminal/ExpectedObserved.lean` | CONFORME (générique) / HORS ROUTE (instanciation) | `primeCountAtStateUpper`, `lastPrimeAtStateUpper` = Lean master §2. L'instanciation à `authenticStateFromZero` est explicitement hors route terminale (Lean master §3) et n'est plus consommée par le terminal. Correct. |
| `Terminal/IndependentContactComparison.lean` | CONFORME et **central** | `expectedMinimum_le_stateReadout_iff : p_min ≤ p_compté ↔ p_min ≤ C⁺` et `stateReadout_lt_expectedMinimum_iff : p_compté < p_min ↔ C⁺ < p_min`. C'est la « dualité rang/contact » de Math §3 — et c'est aussi le théorème qui rend visible que les deux mâchoires sont les deux moitiés d'une trichotomie réelle sur **un seul** nombre `C⁺`. |
| `Terminal/AuthenticCountComparison.lean` | CONFORME | `expected_le_counted_lt_expected_false` (omega), `directContactCountContradiction`. Lean master §1 verbatim. |
| `Tower/AuthenticState.lean` | CONFORME comme parent, HORS ROUTE comme observation | `authenticAddress z = ⌊(T log Occ(z) − φ)/π⌋` : sélection par l'occurrence, interdite comme observation indépendante (Sem §2, Lean master §3). Documenté comme tel. |
| `Terminal/OffCountExperiment.lean` | CONFORME (diagnostic) | Prouve `¬(p_compté(authentic) < p_min)` sur tout passage : c'est simplement `PProgressionJaw authenticStateFromZero`. |
| `Terminal/ConditionalClosure.lean` | **DÉFAUT DE FIDÉLITÉ** | Voir §2. `POffImpliesObligations` est une prémisse de force RH déguisée (interdit par Sem §6 « nouvelle prémisse scientifique portant directement p_compté < p_min », CLAUDE.md §7 « RH-equivalent assumption »). `PEveryUpperHasAuthenticPredecessor` est réfutable. La chaîne n'utilise pas `thm_offCriticalLine_existsNullPassage` : l'étape « OFF → passage nul → seconde Tour » de Sem §5 est absente et remplacée par une totalité fausse. |
| `Parents/CompiledGeometry.lean` | CONFORME (classification) / **RECOMMANDATION CADUQUE** | La docstring recommande « un producteur Tour-intrinsèque indépendant de l'occurrence » comme voie vers A. Réfuté par `offDeficitJaw_iff_riemannHypothesis` : aucun producteur ne change le fait que A ≡ RH sous B. |
| `Audit.lean` (version 6e8d8aae) | **TROMPEUR** | `RIEMANN_HYPOTHESIS_TERM=PRESENT_CONDITIONAL` laissait entendre une réduction. Réécrit. |
| `Tower/MirrorGeometry.lean`, `Off/PassageGeometryBoundary.lean`, `Terminal/AuthenticPassageReadout.lean`, `Tower/IndependentTerminalBoundary.lean` | CONFORME (parents) | Aucun défaut. |

Objets interdits (SAME-EVENT, SAME-PRIME, C3, N_P=1, k=0 sélecteur, heightGap terminal, receptionState, syncState, contact=premier par définition, π/T borne inter-membre) : **aucun hit vivant** — confirmé.

---

## 2. Pourquoi la solution ne va pas jusqu'à RH — analyse exacte

### 2.1 Ce que le terminal des maîtres est, une fois les définitions dépliées

Objets compilés (RHV3Lean) :

- `n(z) := nZeroSourceIndex z` = nombre de zéros supérieurs qui précèdent `z` dans l'ordre (hauteur, puis β).
- `Occ(z) = p_{n(z)}` (n-ième premier, `p_0 = 2`), théorème inconditionnel (M9a + M9b).
- `p_min(a) = p_{n(a)+1} = Occ(b) = p_{n(b)}` pour tout passage consécutif `(a,b)` (`mandatoryExpected_eq_laterOccurrence`).
- Tout état de Tour `S` de `b` a `C⁺(S) = exp((φ_b + (k+1)π)/T_b)` pour un entier `k` (`stateAddress_plus`).
- `p_compté(S) = ` plus grand premier `≤ C⁺(S)`.

Donc, pour **le même** état `S` :

```
mâchoire B  (p_min ≤ p_compté)   ⟺   p_{n(b)} ≤ C⁺(S)      [expectedMinimum_le_stateReadout_iff]
mâchoire A  (p_compté < p_min)   ⟺   C⁺(S) < p_{n(b)}      [stateReadout_lt_expectedMinimum_iff]
```

Les deux mâchoires sont les deux moitiés de la trichotomie du réel `C⁺(S)` par rapport à l'entier `p_{n(b)}` (`jaw_dichotomy`). La « contradiction d'ordre » finale (`omega`) est donc vide de contenu : elle dit qu'un réel n'est pas à la fois `≥` et `<` un même entier. **Tout le contenu est dans la production des deux inégalités**, jamais dans leur collision.

### 2.2 Ce que « OFF » fournit réellement à la géométrie

La seule manière dont `β ≠ 1/2` entre dans les objets compilés est `thm_offCriticalLine_existsNullPassage` : un zéro OFF possède un miroir distinct à la même hauteur, d'où un passage consécutif `(a,b)` d'écart nul. Rien d'autre : la Tour de `b` ne « sait » pas que `b` est OFF autrement que par la valeur de `φ_b = atan(T/β_b)`.

Compilé ici en forme utile : tout zéro OFF est **le membre postérieur** d'un passage nul dont il est OFF (`off_exists_offLater_nullPassage` : on prend `z` si `β>1/2`, son miroir sinon, puis le plus grand membre de la fibre qui le précède).

### 2.3 La chaîne fidèle, pour un producteur quelconque

Soit `J : ∀ b, TTrueHarmonicTowerState b` un producteur quelconque (Lean master §4 : « authenticJourneyState »). Définitions compilées :

```
PProgressionJaw J := ∀ a b, consécutifs → p_min(a) ≤ p_compté(J b)                       -- obligation B, Lean master §6
POffDeficitJaw  J := ∀ a b, consécutifs → même hauteur → C⁺(J b) < p_min(a)               -- obligation A, Lean master §5, Sem §3
```

Théorèmes compilés :

```
riemannHypothesis_of_jaws           : PProgressionJaw J → POffDeficitJaw J → RiemannHypothesis     -- la cascade Sem §5 / Math §7, fidèle
offDeficitJaw_of_allUpperNotOff     : (∀ z, ¬OFF z) → POffDeficitJaw J                            -- sous RH, aucun passage nul n'existe
offDeficitJaw_iff_riemannHypothesis : PProgressionJaw J → (POffDeficitJaw J ↔ RiemannHypothesis)
jaws_iff_riemannHypothesis_and_progression : (Prog J ∧ OffJaw J) ↔ (RiemannHypothesis ∧ Prog J)
```

Lecture : la mâchoire OFF est un énoncé **sur des objets hypothétiques** (passages nuls). Sous RH ils n'existent pas et A est vide ; sans RH, A doit être fausse pour au moins un producteur satisfaisant B... et en fait pour tous, puisque B et A sur le même `C⁺` s'excluent. Il n'y a donc aucune répartition possible de la difficulté : **prouver A, c'est prouver RH**, quel que soit `J`.

### 2.4 B n'a pas de contenu propre

`coarseJourneyState b := towerStateAt b ⌈(T·B(T)·log 2 − φ)/π⌉` avec `B(T) = A·(T+2)^{3/2} + 1`, `A` = constante universelle de `Backlund.zetaCounting_crude_majorant` (théorème inconditionnel de la base : `|N(T)| ≤ A T^{3/2}`). Aucun premier, rang, occurrence, minimum attendu ou état de réception n'entre.

Chaîne compilée :

```
zeroSourceIndex_le_zetaCounting : n(b) ≤ N(T_b + 2)          (chaque zéro précédent est un zéro de ζ d'ordre ≥ 1 dans le rectangle)
primeAtRank_le_two_pow          : p_n ≤ 2^{n+1}               (Bertrand)
two_rpow_coarseBound_le_contactPlus : 2^{B(T_b)} ≤ C⁺(coarse b)
progressionJaw_coarseJourneyState : PProgressionJaw coarseJourneyState
offDeficitJaw_coarse_iff_riemannHypothesis : POffDeficitJaw coarseJourneyState ↔ RiemannHypothesis
```

Ce producteur est « Tour-intrinsèque » au sens littéral du Lean master §4 (aucun premier cible), et il décharge B. Il montre que l'exigence « B doit venir de la progression et du raccord universel, pas de la définition de J » (Lean master §6) ne peut pas être un critère : *tout* état assez loin sur la Tour satisfait B. Le seul objet qui donnerait un contenu à B serait une définition du « voyage propre » — et cette définition n'existe dans aucun des trois maîtres (Sem §10-11 le nomme, ne le définit pas).

### 2.5 Les deux hypothèses de la solution précédente

- `POffImpliesObligations` demande, sous `OFF b`, **les deux** mâchoires pour **tout** état `S` de comptage positif. Comme un tel état existe toujours (`countingState`, Tour seule), c'est exactement `∀ a b consécutifs, ¬OFF b` (`offImpliesObligations_iff_noOffLater`), donc RH (`offImpliesObligations_iff_riemannHypothesis`, les deux sens).
- `PEveryUpperHasAuthenticPredecessor` : le plus petit zéro supérieur (minimum de l'ensemble fini `sUpperZerosBelow z ∪ {z}`) n'a aucun prédécesseur supérieur (`exists_upper_without_upperPredecessor`). L'hypothèse implique donc `IsEmpty TrueZero`, et RH trivialement (`riemannHypothesis_of_everyUpperHasPredecessor`).

`riemannHypothesis_conditional` est donc un théorème vrai mais **vide** : chacune de ses prémisses est RH ou plus fort.

---

## 3. Liste exacte de ce qui créerait la contradiction et terminerait la démonstration

Il n'y a qu'une seule forme possible, et elle est maintenant compilée :

```
∃ J : ∀ b, TTrueHarmonicTowerState b,   PProgressionJaw J   ∧   POffDeficitJaw J
```

1. **Un producteur `J`.** Fait : `coarseJourneyState` (ou n'importe quel autre ; `authenticStateFromZero` convient aussi pour B, `progressionJaw_authenticStateFromZero`).
2. **`PProgressionJaw J`.** Fait, inconditionnel, pour `coarseJourneyState` et pour `authenticStateFromZero`.
3. **`POffDeficitJaw J`.** Ouvert, et compilé comme **équivalent à `RiemannHypothesis`** pour tout `J` satisfaisant 2.

Énoncé exact restant à prouver (forme la plus faible possible dans ces objets) :

```
∀ a b : TrueZero, PZeroMembersConsecutive a.1 b.1 → rZeroHeight a.1 = rZeroHeight b.1 →
  (coarseJourneyState b).contactPlus < (expectedMinimumPrime a : ℝ)
```

c'est-à-dire : *deux zéros distincts de ζ à la même hauteur `T` sont impossibles* (puisque `expectedMinimumPrime a = p_{n(b)} ≤ C⁺(coarse b)` est déjà un théorème, la conclusion est `False`). Ce n'est pas un lemme de Tour : c'est `∀ T, ζ a au plus un zéro de partie réelle dans (0,1) à la hauteur T`, qui est RH par le miroir fonctionnel (`riemannHypothesis_iff_allUpperNotOff`).

**Aucune réécriture, restructuration, nouveau sélecteur, nouvelle lecture de contact, nouveau raccord grammaire↔Tour ne peut contourner ce point**, parce que l'équivalence est prouvée *pour tout producteur* et ne dépend d'aucun choix d'implémentation.

Ce qu'une preuve de 3 devrait contenir, dans cette base, à titre de remarque scientifique (non compilée, non revendiquée comme résultat) : la seule liaison analytique zéros → premiers compilée est la formule explicite lissée `smoothed_riemann_explicit_formula` (P4.6, `ZetaSmoothedExplicitFormulaP4_6.lean`) et son délissage `psiRecoveredFromZeros_eq_psi`. Un zéro OFF `β+iT` y contribue par un terme d'amplitude `x^β/|ρ|` ; en tirer une contradiction demanderait une borne supérieure inconditionnelle de type puissance sur `ψ(x) − x`, ce qui est une région sans zéro de type puissance, c'est-à-dire une forme de RH. La Tour, elle, ne contient aucune information sur les premiers : `C⁺ = exp((φ+kπ)/T)` est une fonction de `(β, T, k)` seulement, et `Occ(z) = p_{n(z)}` est une **assignation par rang**, pas une relation analytique.

---

## 4. Ce qui a été ajouté au dépôt

- `RHV6Fresh/Terminal/JawEquivalence.lean` — 22 théorèmes, dont : `countingState_count_pos`, `jaw_dichotomy`, `offImpliesObligations_iff_noOffLater`, `exists_fiberPredecessor_consecutive`, `off_exists_offLater_nullPassage`, `riemannHypothesis_iff_allUpperNotOff`, `offImpliesObligations_iff_riemannHypothesis`, `exists_upper_without_upperPredecessor`, `isEmpty_of_everyUpperHasPredecessor`, `riemannHypothesis_of_everyUpperHasPredecessor`, `PProgressionJaw`, `POffDeficitJaw`, `noOff_of_jaws`, `riemannHypothesis_of_jaws`, `off_of_nullPassage`, `offDeficitJaw_iff_riemannHypothesis`, `jaws_iff_riemannHypothesis_and_progression`, `progressionJaw_authenticStateFromZero`, `offDeficit_at_authentic_iff_riemannHypothesis`.
- `RHV6Fresh/Tower/CoarseJourneyState.lean` — `primeAtRank_le_two_pow`, `riemannZeta_analyticOrderAt_ne_top`, `one_le_zetaOrder_of_zero`, `zeroSourceIndex_le_zetaCounting`, `crudeZeroConstant`, `coarseBound`, `coarseAddress`, `coarseJourneyState`, `progressionJaw_coarseJourneyState`, `offDeficitJaw_coarse_iff_riemannHypothesis`.
- `RHV6Fresh/Audit.lean` — manifeste réécrit ; `#print axioms` sur tous les théorèmes ci-dessus.
- `RHV6Fresh/Terminal/ConditionalClosure.lean` — docstring corrigée (les théorèmes sont conservés comme trace de la tentative).

Vérification : `lake build` → `Build completed successfully (3848 jobs)` ; 0 `sorry`, 0 `admit`, 0 axiome nouveau ; tous les `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

---

## 5. Statut

```
BUILD=PASS (3848/3848)
SORRY=0  ADMIT=0  NEW_AXIOM=0
TOWER_INTRINSIC_SECOND_TOWER_STATE=PRESENT (coarseJourneyState)
MANDATORY_BOUND_SAME_READOUT=PROVED (progressionJaw_coarseJourneyState)
OFF_CONTACT_DEFICIT=EQUIVALENT_TO_RH (offDeficitJaw_iff_riemannHypothesis, pour tout producteur satisfaisant B)
CONDITIONAL_CLOSURE_OF_6e8d8aae=VACUOUS (chaque hypothèse implique RH seule)
RH_FOUND=FALSE
```

**RÉFUTÉ :** (1) la lecture de `riemannHypothesis_conditional` comme réduction de RH à deux obligations indépendantes — chaque hypothèse implique RH seule (`offImpliesObligations_iff_riemannHypothesis`, `riemannHypothesis_of_everyUpperHasPredecessor`) ; (2) `PEveryUpperHasAuthenticPredecessor` — réfutée dès qu'un zéro existe (`isEmpty_of_everyUpperHasPredecessor`) ; (3) la recommandation « construire un producteur Tour-intrinsèque pour atteindre A » — pour tout producteur satisfaisant B, A ≡ RH (`offDeficitJaw_iff_riemannHypothesis`).

**BORNÉ (portée) :** la cascade des maîtres est compilée fidèlement pour tout producteur (`riemannHypothesis_of_jaws`) ; l'obligation B est déchargée pour un producteur Tour-intrinsèque explicite ; l'obligation A reste ouverte et est **exactement** `RiemannHypothesis` — pas « aussi difficile que », mais équivalente, par un `↔` compilé aux trois axiomes standard. Les preuves n'utilisent que les objets des maîtres (Tour, contacts, comptage Von Mangoldt/Chebyshev, grammaire des zéros, miroir fonctionnel) plus deux théorèmes inconditionnels de la base (`zetaCounting_crude_majorant`, Bertrand via Mathlib).

**SÉLECTIONS :** aucun travail Lean supplémentaire dans le périmètre Tour/contacts/grammaires ne peut fermer A. Deux choix seulement restent au niveau des maîtres : (a) constater que le terminal DIRECT EXPECTED/OBSERVED est une reformulation de RH et le retirer du statut « démonstration » ; (b) chercher une entrée analytique nouvelle hors du périmètre actuel (formule explicite + borne inconditionnelle de type puissance sur `ψ(x)−x`), en sachant qu'une telle borne est elle-même de force RH. Je ne recommande pas (b) comme « prochaine étape Lean » : c'est un problème ouvert de mathématiques, pas une transcription.
