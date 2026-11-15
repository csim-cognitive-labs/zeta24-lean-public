# RHV6Fresh — première arête Lean de fidélité non produite

## 0. Correction normative après restauration des maîtres

Ce fichier est subordonné aux trois maîtres restaurés :

```text
formalization/RHV5Fresh/RHV5_STRATEGIE_SEMANTIQUE.md
formalization/RHV5Fresh/RHV5_STRATEGIE_MATHEMATIQUE.md
formalization/RHV5Fresh/RHV5_STRATEGIE_LEAN.md
```

La formulation précédente de ce fichier était erronée sur un point central :

```text
PREVIOUS_FIRST_MISSING_OBJECT =
  towerTerminalAddress : TrueZero → ℤ
```

n'est **pas** le premier objet scientifique manquant.

Les maîtres restaurés imposent explicitement :

```text
k : ℤ = coordonnée technique de la famille analytique
k n'est pas un objet sémantique terminal
ne pas "chercher k"
ne pas créer un nouveau sélecteur scientifique
ne pas sélectionner la cellule depuis un premier cible
```

Ainsi l'absence d'un indice privilégié dans la famille

```lean
towerStateAt z k
```

ne justifie pas la création d'un nouveau `towerTerminalAddress`.

Le front correct est une **transcription Lean de fidélité** des étapes déjà fixées par les
maîtres :

```text
TDD-2 JOURNEY CELL
→ M1 SAME_EVENT
→ TDD-3 SAME-PRIME MIRROR
→ M2/M3/M4/M5/M6/M7
→ RH.
```

Il n'y a donc pas, à ce stade, de « première arête scientifique » déclarée ouverte par les
maîtres. Il y a une première arête **Lean non transcrite fidèlement**.

---

## 1. Ce que la Tour analytique produit effectivement

Pour un vrai zéro

```text
z = β + iT,
0 < β < 1,
T > 0,
```

la Tour propre fournit la famille :

```text
φ(z) = atan(T/β)
T log C_k = φ(z)+kπ
C_k = exp((φ(z)+kπ)/T).
```

Le HEAD actif contient les états explicites :

```lean
towerStateAt z k
```

et TAN-Q certifie toute paire consécutive fournie :

```text
log C_(k+1)-log C_k = π/T.
```

Les théorèmes tangents des deux extrémités certifient également :

```text
tan(T log C_k)=T/β
tan(T log C_(k+1))=T/β.
```

Ces résultats prouvent la géométrie interne d'une cellule candidate fournie.

Ils ne disent pas :

```text
cet entier k est l'événement terminal du membre.
```

Mais le maître ne demande pas non plus d'ajouter un entier k comme nouvelle donnée
scientifique.

---

## 2. Pourquoi l'ancien `authenticAddress` n'est pas une lecture indépendante

Le sélecteur historique se développe en :

```lean
authenticAddress z =
  ⌊(rZeroHeight z.1 * Real.log (occurrence z : ℝ) -
      (trueTowerOf z).phase) / Real.pi⌋
```

et :

```lean
authenticStateFromZero z =
  towerStateAt z (authenticAddress z).
```

La sélection est donc reconstruite à partir de l'occurrence première.

Elle peut servir à localiser/certifier une occurrence déjà reconstruite, mais elle ne peut
pas constituer la mâchoire indépendante :

```text
Tour → cellule → lecture première
```

utilisée ensuite pour prétendre retrouver la même occurrence.

Classification :

```text
OCCURRENCE_SELECTED_STATE = VALID_AS_LOCALIZATION
OCCURRENCE_SELECTED_STATE = INVALID_AS_INDEPENDENT_TERMINAL_READOUT
```

---

## 3. Pourquoi `k=0` et le seuil 2 ne sont pas le terminal

La famille analytique possède plusieurs états valides ; aucun principe tangentiellement
interne ne privilégie `0`.

La route fixant `k=0` a été retirée au commit :

```text
2a33ee6b965abd76e377458f9629bb39be847dbd
remove fixed-index intrinsic terminal readout
```

Cette suppression doit être conservée.

Le sélecteur historique « première incidence au moins égale à 2 » reste un contrôle de
portée. Il ne constitue pas le voyage terminal sémantique et sa cellule est vide de premier
à grande hauteur dans les contrôles déjà compilés.

Donc :

```text
k=0                    = REJECTED_AS_TERMINAL
threshold-at-2         = CONTROL_ONLY
occurrence-selected k  = CIRCULAR_FOR_INDEPENDENT_READOUT
```

Aucun de ces trois cas ne doit être remplacé par un quatrième sélecteur inventé.

---

## 4. Première arête réelle : TDD-2 JOURNEY CELL

Le maître mathématique restauré note, uniquement comme spécification :

```text
J(z) = cellule effectivement parcourue/lue
       par le voyage propre de la Tour de z.
```

Cette notation ne crée :

```text
ni nouvel axiome,
ni nouveau k scientifique,
ni nouveau premier,
ni nouvelle grammaire,
ni nouvelle P...Law.
```

La première tâche RHV6 est :

```text
identifier dans l'API scientifique existante du voyage
la construction qui correspond à J(z),
ou transcrire directement cette construction depuis ses objets primitifs,
sans sélectionner la cellule par une occurrence première.
```

Le contrat de fidélité est :

```text
TRUE_ZERO
→ PROPER_TOWER
→ REAL_JOURNEY
→ EFFECTIVELY_TRAVERSED_CELL J(z)
→ EFFECTIVE_CONTACTS
```

avec les tests :

```text
NO_PRIME_INPUT
NO_EXPECTED_PRIME_SEARCH
NO_MEMBER_MZ_OCCURRENCE_SELECTION
NO_CANONICAL_ADDRESS_AS_CAUSE
NO_COUNTING_ADDRESS_AS_CAUSE
NO_RECEPTION_STATE_SELECTION
SOURCE_ZERO_PRESERVED
TAN_Q_CERTIFIES_THE_RESULTING_CONTACTS
MIRROR_TRANSFORMATION_PRESERVED
```

Une adresse Lean peut apparaître **après** cette production comme coordonnée de la cellule
obtenue. Elle ne peut pas être le producteur scientifique.

---

## 5. Ce que RHV6 ne doit donc PAS produire

Ne pas créer comme solution du front :

```lean
noncomputable def towerTerminalAddress (z : TrueZero) : ℤ := ...
```

si cette définition constitue une nouvelle règle scientifique choisissant un barreau.

Ne pas créer non plus :

```text
PTerminalAddressLaw
PJourneySelectorLaw
PSameEventLaw
PAuthenticCellLaw
```

portant en hypothèse la propriété qu'il faut démontrer.

La seule forme acceptable d'une adresse terminale dans le code est :

```text
voyage réel déjà produit
→ cellule déjà produite
→ adresse technique de cette cellule.
```

---

## 6. Deuxième arête : M1 SAME_EVENT

Une fois la cellule du voyage réel transcrite, il faut démontrer qu'elle lit le **même
événement grammatical** que le membre et M^Z.

Le contrat maître est :

```text
EV_Z
= EV_Tour/Journey
= EV_MZ
= EV_M.
```

Il est interdit de remplacer cela par deux événements indépendants :

```text
E_Z
E_Tour
```

puis d'ajouter leur égalité comme hypothèse.

La cible Lean doit être une composition de la provenance du vrai membre, du voyage,
des contacts/lectures et du Seam M^Z=M.

---

## 7. TDD-3 SAME-PRIME MIRROR

Après TDD-2 et M1, la mâchoire OFF visée par les maîtres est :

```text
primeRead(J(b)) = primeRead(J(a))
```

sur la configuration OFF authentique concernée.

Le snapshot mathématique récupéré donne le statut :

```text
singleton : partiellement fermé sous borne d'étage
pluriel   : NON FERMÉ
```

Ce statut ne doit pas être masqué.

La preuve TDD-3 doit couvrir :

```text
SINGLETON
PLURAL
```

sans utiliser :

```text
receptionState
syncState = receptionState
same-rung arbitraire
premier cible pour choisir J
```

---

## 8. Pourquoi `receptionState` ne ferme pas TDD-3

Le corpus prouve :

```text
thm_reception_progression
```

mais la réception est construite pour atteindre la cible arithmétique.

Il prouve également :

```text
thm_reception_progression_self
```

ce qui montre que cette progression caractérise le mécanisme de sélection, pas le membre
suivant.

À même hauteur, le corpus prouve :

```text
thm_sameHeight_sync_noProgression
thm_sameHeight_sync_ne_reception.
```

Donc le système cohérent actuel est :

```text
sync observation     : no progression
reception selection  : progression by construction
sync ≠ reception.
```

Il n'existe aucune contradiction entre ces trois faits.

En particulier, il est interdit d'introduire :

```text
syncState S w = receptionState S w.
```

---

## 9. Expected minimum : auxiliaire, pas front terminal

Les théorèmes historiques :

```text
thm_trap_expectedMinimum
thm_expectedMinimum_ge_nextPrime
thm_expectedMinimum_cases
thm_canonical_nextAnchor_ge_occurrence
thm_contactPlus_lt_nextCountedAnchor
thm_nextCountedAnchor_minimal
```

fournissent la mâchoire arithmétique :

```text
p_(n+1) ≤ q_min(a)
C⁺(a) < q_min(a).
```

Ils ne produisent pas J(b).

Ils ne prouvent pas que l'observation OFF intrinsèque atteint ou n'atteint pas q_min.

Classification :

```text
EXPECTED_MINIMUM = AUXILIARY_ARITHMETIC_FRONT
EXPECTED_MINIMUM ≠ JOURNEY_CELL_PRODUCER
EXPECTED_MINIMUM ≠ SAME_EVENT_PROOF
EXPECTED_MINIMUM ≠ TDD3
```

---

## 10. Comparaison exacte pour un état fourni indépendamment

`Terminal/IndependentContactComparison.lean` peut être conservé comme outil de lecture.

Pour tout état fourni indépendamment avec compteur positif, il établit les équivalences
de la forme :

```text
expectedMinimumPrime a ≤ lastPrimeAtStateUpper S
↔
(expectedMinimumPrime a : ℝ) ≤ S.contactPlus

lastPrimeAtStateUpper S < expectedMinimumPrime a
↔
S.contactPlus < (expectedMinimumPrime a : ℝ).
```

Ces équivalences sont utiles **après** qu'un état S fidèle au voyage a été produit.

Elles ne sélectionnent pas S.

Elles ne doivent donc plus être décrites comme nécessitant un nouveau
`towerTerminalAddress`; elles attendent simplement l'instanciation par la cellule J issue
de TDD-2.

---

## 11. Front miroir : distinction et consécutivité

Le miroir fonctionnel authentique fournit :

```text
z* ≠ z
T(z*) = T(z)
β(z*) = 1-β(z).
```

Il reste correct que :

```text
distinct + sameHeight + mirror symmetry
```

ne suffit pas logiquement à démontrer :

```text
Consecutive_Z(z,z*) ∨ Consecutive_Z(z*,z).
```

Le contre-modèle ordinal abstrait à trois points montre seulement cette non-implication.

Par conséquent, le théorème :

```lean
offMirror_pair_is_a_passage
```

ne doit pas être inventé sans un parent supplémentaire réellement démontré.

Mais ce point n'est plus le **premier front** du document.

Le maître terminal doit utiliser la configuration authentique exacte à laquelle sa
progression grammaticale s'applique. Si la route choisie exige littéralement le couple
`(z,z*)` consécutif, alors cette consécutivité devient une obligation distincte et doit
être démontrée ; elle ne peut pas être obtenue par simple symétrie.

---

## 12. Passage authentique extrait de la fibre

Le théorème :

```text
off_exists_authenticPassage_boundary
```

peut conserver l'existence d'un passage consécutif réel dans la fibre sans l'identifier
au couple miroir littéral.

Les bornes de contacts déjà obtenues sur ce passage restent des faits de portée.

Elles ne doivent pas être requalifiées en preuve du SAME EVENT ou de TDD-3 sans le raccord
de voyage requis par les maîtres.

---

## 13. Chaîne terminale restaurée

La chaîne à produire dans RHV6 est :

```text
M2 PRE-OFF EVENT SUCCESSOR
  Consecutive_Z(a,b)
  → E(b)=E(a)+1
  → Occ_MZ(a)=p_n
  → Occ_MZ(b)=p_(n+1)
  → p_n≠p_(n+1)

TDD-2 / M1
  vrai membre
  → Tour propre
  → voyage réel
  → J(member)
  → lecture du même E

M3 OFF NO-INCREMENT
  vraie configuration OFF à même hauteur
  → lecture du même E sans incrément
  → E(b)=E(a)

M4
  E(b)=E(a)+1
  ∧ E(b)=E(a)
  → collision

M5
  M^Z=M
  → p_(n+1)=p_n

M6
  prime rigidity
  → p_(n+1)≠p_n

M7
  False
  → RiemannHypothesis.
```

---

## 14. Statut exact du front

```text
FIRST_UNSOLVED_CLASS=LEAN_TRANSCRIPTION_FIDELITY
FIRST_UNSOLVED_MASTER_STEP=TDD-2_JOURNEY_CELL
NEXT_MASTER_STEP=M1_SAME_EVENT
NEXT_OFF_STEP=TDD-3_SAME_PRIME_MIRROR
NEW_TOWER_TERMINAL_ADDRESS_REQUIRED=false
NEW_SCIENTIFIC_SELECTOR_REQUIRED=false
EXPECTED_MINIMUM_TERMINAL_COMPLETE=false
SYNC_EQUALS_RECEPTION=false
FIXED_K0_TERMINAL=false
THRESHOLD2_TERMINAL=false
OCCURRENCE_SELECTED_STATE_INDEPENDENT=false
MIRROR_CONSECUTIVITY_FROM_SYMMETRY=false
RH_FOUND=false
```

La prochaine production Lean doit donc chercher/transcrire **le voyage réel déjà défini par
la sémantique**, et non définir un nouvel entier terminal.
