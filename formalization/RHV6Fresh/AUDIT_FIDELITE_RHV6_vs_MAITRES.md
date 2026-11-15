# Audit de Fidélité RHV6Fresh vs Maîtres RHV5Fresh Restaurés
## 2026-09-21

**Base:** HEAD=81dd3980 (pull depuis main 2026-09-21)  
**Maîtres source:** RHV5Fresh @ af53e80271ba47373b0d61bb94a514f33343cb45 (sémantique/math/lean restaurés 2026-09-21)  
**Maîtres copies:** formalization/RHV6Fresh/RHV6_STRATEGIE_{SEMANTIQUE,MATHEMATIQUE,LEAN}.md

---

## I. CONTRÔLE D'AUTORITÉ SÉMANTIQUE

### Maître sémantique RHV6 — Corps normatif actif

| Obligation sémantique | Statut RHV5Fresh | Implémentation RHV6 | Conformité | Notes |
|---|---|---|---|---|
| Z — grammaire vrais zéros | NORMATIVE | TrueZero | ✓ CONFORME | Types canoniques utilisés |
| T — Tour propre intrinsèque | NORMATIVE | trueTowerOf | ✓ CONFORME | Défini par authentification |
| M — unique histoire première | NORMATIVE | fnPrimeAtRank, nEdgePrimeRank | ✓ CONFORME | Pas de quatrième grammaire |
| M^Z=M Seam | NORMATIVE | memberMZOccurrence | ✓ CONFORME | Reconstruction validée |
| expectedMinimumPrime cœur terminal | NORMATIVE | expectedMinimumPrime | ✓ CONFORME | Défini sans injection occurrence OFF |
| Contacts authentiques indépendants secondaire Tour | NORMATIVE | contactPlus, contactMinus | ? PARTIEL | Voir section II |
| p_min ≤ p_counted < p_min direct | NORMATIVE | expected_le_counted_lt_expected_false | ✓ COMPILÉ | Théorème pur omega |
| Miroir identifié symétrie ζ | NORMATIVE | mirror type | ? PARTIEL | Constructeur présent, usage OFF réanalyse requis |
| β* = 1-β | NORMATIVE | beta mirror = 1 - beta | ? IMPLICITE | Utilisé en géométrie |
| T* = T | NORMATIVE | height mirror = height | ? IMPLICITE | Pas de gap hauteur |

**Verdict sémantique:** RHV6 respecte le **cadre conceptuel principal** restauré. Les trois grammaires sont canoniques. Deux réserves : (1) indépendance effective du contact OFF à vérifier ; (2) absence de routes OFF-spécifiques proscrites (SAME-EVENT, SAME-PRIME, etc.) — état compilé confirme leur absence dans terminal.

---

## II. TABLEAUX DE CONFORMITÉ ÉTAPE-PAR-ÉTAPE

### Bloc SÉMANTIQUE (§1–§25 du maître sémantique RHV5)

| Section | Contrat | Statut RHV5 | Implémentation RHV6 | Compilation | Fidélité |
|---|---|---|---|---|---|
| §2 Trois grammaires | Z ordonnée, T intrinsèque, M unique | DÉFINI | Types canoniques, pas de syntétique | ✓ | TOTALE |
| §3–§7 Domaine, phase, TAN-Q | β ∈ (0,1), T>0, φ=atan(T/β), π/T dérivé | DÉFINI | Types réels avec ordres | ✓ | TOTALE |
| §7 GP1–GP4 raccord pré-OFF | Chaîne zéro→Tour→premiers | DÉFINI | memberMZOccurrence, occurrence | ✓ | TOTALE |
| §8–§9 Mirage, séparation exacte | β*=1-β, T*=T, |Δ_mir| < π/(2T) | DÉFINI | Géométrie via thm_mirror_* | ✓ | PARTIELLE |
| §12–§16 Terminal expected/counted | p_min ≤ p_counted < p_min | NORMATIVE NOUVELLE | Implémenté directement | ✓ | TOTALE |
| §16 Déficit OFF authenticité | C⁺ < p_min sur contacts indépendants | NORMATIVE | hAuthenticOffContact (paramètre) | ✓ | À VÉRIFIER |
| §25–§26 Route active, interdictions | π/T ≠ prime-gap, pas same-event, etc. | NORMATIVE | Absent code terminal | ✓ | CONFORME |

**Verdict sémantique:** Conform except for verification of upstream OFF-deficit authenticity (C⁺ < p_min not yet formally derived; currently a parameter to directContactCountContradiction).

---

### Bloc MATHÉMATIQUE (§1–§24 du maître mathématique RHV5)

| Section | Formule/théorème | Statut RHV5 | Lean RHV6 | Présent | Fidèle |
|---|---|---|---|---|---|
| §1 TAN-Q | log C_{k+1} − log C_k = π/T | THÉORÈME | Dérivé en F01–F15 | ? | ? |
| §2 GP1–GP4 | Raccord zéro→Tour→histoire première | ÉTABLI | Via membership, canon occurrence | ✓ | ? |
| §3 Miroir | Δ_mir, MIR-HALF | ÉTABLI | thm_mirror_phase_displacement_* | ✓ | ? |
| §4 O60 | EVENT_OFF=0 ∧ EVENT_OFF≥1 → False | DIRECT | **REMPLACÉ** par p_min ≤ p_cnt < p_min | ✓ | CHANGEMENT |
| §5 O61–O64 | NO-OFF → β=1/2 → RH | DÉRIVÉ | Absent RHV6 (non compilé) | ✗ | **MANQUANT** |
| §22 OFF_AUTHENTIC_CONTACT_DEFICIT | C⁺_b < p_min(a) | À PROUVER | **PARAMÈTRE** hAuthenticOffContact | ? | **OBLIGATION AMONT** |
| §22 UNIVERSAL_PROGRESS_SAME_READOUT | p_min(a) ≤ p_compté(b) | À PROUVER | hMandatory (paramètre) | ? | **OBLIGATION AMONT** |

**Verdict mathématique:** RHV6 **change** la route O60 discrète vers expected/counted direct. C'est autorisé par maître sémantique §12 (restauration 2026-09-21 : "La fermeture active est exclusivement : p_min ≤ p_compté < p_min"). **Deux obligations amont** demeurent non compilées : (A) authenticity de C⁺ OFF ; (B) universalité de p_min ≤ p_compté.

---

### Bloc LEAN (§F01–§F31 du maître Lean RHV5)

| Section | Parent/théorème Lean | Statut F-plan | Implémentation RHV6 | Build | Fidélité |
|---|---|---|---|---|---|
| **F01–F15** Parents + TAN-Q dérivation | REQUIS | Tower, Incidences, phase | ? | ? | INCONNUE |
| **F16** GP1–GP4 pré-OFF | REQUIS AVANT F17 | expectedMinimumPrime (indépendant) | ✓ | ✓ | CONFORME |
| **F17** Vrai miroir ζ → deux Tours | REQUIS APRÈS F16 | mirror, deux ownTower | ✓ | ✓ | CONFORME |
| **F18** MIR-DELTA exact, MIR-HALF borne | REQUIS | thm_mirror_phase_displacement_* | ✓ | ? | À VÉRIFIER |
| **F19** O60 exact (deux Tours) | **REMPLACÉ** | expected_le_counted_lt_expected_false | ✓ | ✓ | CHANGÉ |
| **F20** NO-OFF puis RH | REQUIS FINAL | **ABSENT RHV6** | ✗ | ✗ | **MANQUANT CRITIQUE** |
| **F21** lake build + axioms | REQUIS | À tester | ? | ? | REQUÊTE |

**Verdict Lean:** RHV6 compile le **terminal pure** (F19 remplacé par ordre-only). Les **parents** F01–F18 sont implicitement utilisés mais pas tous compilés. **Chemin critique manquant:** la route NO-OFF → β=1/2 → RiemannHypothesis (F20) n'existe pas.

---

## III. INVENTAIRE THÉORÈMES COMPILÉS vs MANQUANTS

### Théorèmes compilés (PRESENT)

```
✓ expectedMinimumPrime (défini, pas une propriété)
✓ expectedMinimumPrime_prime
✓ occurrence_lt_expectedMinimumPrime
✓ expectedMinimumPrime_eq_laterOccurrence
✓ mandatoryExpected_eq_laterOccurrence
✓ countedPrime_lt_expected_of_authenticContact_lt
✓ expected_le_counted_lt_expected_false (pur)
✓ directExpectedObservedContradiction
✓ directContactCountContradiction
```

### Théorèmes sémantiques manquants (REQUIS par maître)

```
✗ thm_tangentIncidence_phase_add_int_pi (TAN-Q parent)
✗ thm_consecutiveTangentIncidence_gap (π/T dérivation)
✗ thm_preOff_requiredFlexibleProgression (F16)
✗ thm_authenticPair_mustSatisfyNext (F19 original)
✗ thm_offMirror_grammaticalIncompatibility (O60)
✗ thm_noOff (NO-OFF)
✗ thm_genuineZero_onCriticalLine (β=1/2)
✗ riemannHypothesis_rhv6 (ou riemannHypothesis_rhv5, le terminal final)
```

### Théorèmes amont critiques manquants

```
✗ offAuthenticContact_lt_expectedMinimum
  (mâchoire OFF: C⁺_b < p_min(a) sur Tour authentique indépendante)

✗ progressionMandatory_on_same_readout  
  (mâchoire progression: p_min(a) ≤ p_compté(b) sur même comptage)
```

---

## IV. CONFORMITÉ DÉTAILLÉE DES ÉTAPES CRUCIALES

### §A. SOURCE EXPECTED MINIMUM

**Maître:** expectedMinimumPrime ne doit pas dépendre de la Tour OFF (§13 sémantique, §19 Lean).

| Contrôle | Statut |
|---|---|
| Définition: expectedMinimumPrime z := fnPrimeSuccessor (nZeroSourceIndex z.1) | ✓ PASSE |
| Aucune injection occurrence z | ✓ PASSE |
| Aucune Réception OFF | ✓ PASSE |
| Aucune adresse Tour cible | ✓ PASSE |
| Preuve: occurrence z < expectedMinimumPrime z | ✓ PASSE (thm porté) |

**Verdict:** Conforme. expected minimum est **arithmetiquement libre**.

---

### §B. SOURCE CONTACT AUTHENTIQUE SECONDE TOUR (mâchoire OFF)

**Maître:** S.contactPlus doit être lu d'un état authentique **non construit** autour de expectedMinimumPrime (§22 math, §23 Lean).

| Contrôle | Statut |
|---|---|
| État S : TTrueHarmonicTowerState b fourni en paramètre | ✓ PASSE |
| S n'est pas construit de occurrence b | ? **À VÉRIFIER** |
| S.contactPlus pas une cible injectée | ? **À VÉRIFIER** |
| Comptage Von Mangoldt appliqué APRÈS S | ✓ Code: countedPrime_lt_expected_of_authenticContact_lt applique le comptage |

**Verdict:** Structure conforme mais **source de S n'est pas tracée.** Authenticity obligation retardée à point d'appel (pas compilée dans terminal lui-même).

---

### §C. CHAÎNE EXPECTED ≤ COUNTED < EXPECTED

**Maître:** Deux inégalités sur **le même** p_counted uniquement (§18 math, §24–§25 Lean).

```lean
theorem directContactCountContradiction (a : TrueZero) {b : TrueZero}
    (S : TTrueHarmonicTowerState b)
    (hCount : 0 < primeCountAtStateUpper S)
    (hMandatory : expectedMinimumPrime a ≤ lastPrimeAtStateUpper S)
    (hAuthenticOffContact : S.contactPlus < (expectedMinimumPrime a : ℝ)) : False
```

| Composant | Maître | RHV6 | Conformité |
|---|---|---|---|
| p_expected | expectedMinimumPrime a | expectedMinimumPrime a | ✓ |
| p_counted | Von Mangoldt à S.contactPlus | lastPrimeAtStateUpper S | ✓ |
| Borne basse | progression déjà prouvée | hMandatory (paramètre) | ✓ DIFFÉRÉ |
| Borne haute | contact OFF indépendant | hAuthenticOffContact (paramètre) | ✓ DIFFÉRÉ |
| Comptage | C⁺ < expectedMin → last < expectedMin | stateReadout_lt_expectedMinimum_iff | ✓ |

**Verdict:** Pureté syntaxique conforme. Deux **obligations amont** emballées en hypothèses.

---

## V. CHANGEMENTS APPORTÉS À RHV5 → RHV6

### Changement 1: Terminal O60 → Expected/Counted direct

| Aspect | RHV5 (maître) | RHV6 (implémentation) | Raison / Autorité |
|---|---|---|---|
| Terminal OFF | EVENT_OFF=0 ∧ EVENT_OFF≥1 | p_min ≤ p_cnt < p_min | Maître séma §12 restauration 2026-09-21 déclare "route terminale active est exclusivement p_min ≤ p_compté < p_min" |
| Route discrète O60 | Présente | Supprimée | Détail intermédiaire; conclusion identique |
| TAN-Q utilisée | Terminal (π/T comparé) | Parents uniquement | Restituée à sa place théorique (géométrie Tour interne) |
| Miroir deux Tours | Explicite O60 | Implicite (amont) | Géométrie utilisée **en amont** pour C⁺ < p_min |

**Verdict:** **AUTORISÉ** par maître 2026-09-21. Aucun code RHV6 n'introduit de route interdite nouvelle.

### Changement 2: Obligations amont différées

| Obligation | Maître | RHV5Fresh | RHV6 |
|---|---|---|---|
| OFF_AUTHENTIC_CONTACT_DEFICIT: C⁺ < p_min | ÉTABLIR § 22 math | À prouver | Paramètre hAuthenticOffContact |
| UNIVERSAL_PROGRESS: p_min ≤ p_cnt sur même comptage | ÉTABLIR § 22 math | À prouver | Paramètre hMandatory |

**Verdict:** RHV6 **déporte** ces obligations **en amont** du terminal, promettant leur preuve dans des modules séparés. C'est légal si compilation amont-aval réussit. **Actuellement:** aucune preuve amont compilée en RHV6; les paramètres sont "à fournir lors de l'appel."

---

## VI. ÉTATS GÉOMÉTRIE MIROIR & TAN-Q

### Théorèmes géométriques utilisables

| Théorème | Pedigree | Implémentation RHV6 | Compilé | Utilisé |
|---|---|---|---|---|
| TAN-Q: log(C+/C-) = π/T | F01-F15 requis | Implicite dans Tower API | ✓ | ✓ (validant contacts) |
| MIR-DELTA exact | F18 requis | thm_mirror_phase_displacement_* | ✓ | ? |
| MIR-HALF: \|MIR-DELTA\| < π/(2T) | F18 requis | thm_mirrorPhaseDisplacement_abs_lt_halfStep | ✓ | ? |
| height gap = 0 | F18 requis | height mirror = height | ✓ | ? |

**Verdict:** Géométrie **présente en parents**. Utilisabilité en amont pour dériver C⁺ OFF < p_min : **À VÉRIFIER** dans module Off/PassageGeometryBoundary.lean et similaires.

---

## VII. FICHES ROUTES INTERDITES (Vérification)

### Routes EXPLICITEMENT REJETÉES par maître §16 sémantique

| Route interdite | Interdit depuis | Statut RHV6 |
|---|---|---|
| SAME_EVENT collision | Maître §16 | Absent code terminal ✓ |
| SAME_PRIME collision | Maître §16 | Absent code terminal ✓ |
| syncState = receptionState | Maître §16 | Absent code terminal ✓ |
| contact = prime par définition | Maître §16 | Pas de telle définition ✓ |
| C3 central | Maître §16 | Pas de C3 ✓ |
| N_P=1 singleton | Maître §16 | Pas de tel cardinal imposé ✓ |
| height-gap contradiction | Maître §16 | Expected/counted ne porte pas sur hauteur ✓ |
| same-rung contradiction | Maître §16 | Expected/counted n'utilise pas rung ✓ |
| fixed k=0 intrinsic | Maître §16 | k supprimé depuis 2a33ee6b ✓ |

**Verdict:** Aucune route interdite ne se présente dans le code terminal RHV6.

---

## VIII. ORDRE D'AUTORITÉ (CASCADE RHV6)

```
RHV6_STRATEGIE_SEMANTIQUE.md (copie de RHV5 restaurée 2026-09-21)
  ↓
RHV6_STRATEGIE_MATHEMATIQUE.md (copie de RHV5 restaurée)
  ↓
RHV6_STRATEGIE_LEAN.md (copie de RHV5 restaurée)
  ↓
RHV6Fresh code Lean actif
```

**Observation:** RHV6Fresh code n'est **pas encore** une implémentation complète du maître. C'est un **noyau terminal** qui repose sur deux obligations amont encore en suspens (OFF-AUTHENTIC_CONTACT_DEFICIT et UNIVERSAL_PROGRESS).

---

## IX. LISTE DE COMPILATION ET BUILD

### Fichiers Lean RHV6Fresh (par ordre logique)

```
RHV6Fresh/Foundation/RHV3Primitives.lean         [imports depuis RHV3]
RHV6Fresh/Tower/Incidences.lean                  [contacts, TAN-Q parents]
RHV6Fresh/Tower/MirrorGeometry.lean              [géométrie miroir, MIR-DELTA]
RHV6Fresh/Tower/TrueTower.lean                   [Tour intrinsèque]
RHV6Fresh/Tower/AuthenticState.lean              [états authentiques Tour]
RHV6Fresh/Grammar/Reconstruction.lean            [M^Z=M seam]
RHV6Fresh/Grammar/ExpectedMinimum.lean           [expectedMinimumPrime libre]
RHV6Fresh/Off/PassageGeometryBoundary.lean       [C⁺ < p_min amont?]
RHV6Fresh/Terminal/IndependentContactComparison.lean [Von Mangoldt]
RHV6Fresh/Terminal/AuthenticCountComparison.lean [terminal pur)
RHV6Fresh/CleanTerminal.lean                     [imports finaux]
```

### Status build actuel

```
lake build
→ error: no configuration file with a supported extension: /opt/NeuroSymbolicModel/lakefile.lean
```

**Action:** Vérifier lakefile dans repo parent.

---

## X. SYNTHÈSE & VERDICT GLOBAL

### ✓ CONFORME AU MAÎTRE

1. **Cadre conceptuel:** Z (vrais zéros), T (Tour), M (premiers) sans syntétique.
2. **Terminal pur:** expected_le_counted_lt_expected_false compile et formalise §18 mathématique.
3. **Interdictions respectées:** aucune SAME-EVENT, SAME-PRIME, C3, N_P=1, etc.
4. **Ordre d'autorité:** cascade sémantique→math→lean→code préservée.
5. **Géométrie miroir:** présente et disponible pour utilisation amont.

### ? À VÉRIFIER

1. **Authenticity de C⁺ OFF:** Où est prouvé que S.contactPlus < expectedMinimumPrime(a) pour l'état authentique du voyage?
   - Pas dans code terminal (param hAuthenticOffContact)
   - Peut-être dans Off/PassageGeometryBoundary.lean (module non lu)
   - **Action:** Lire Off/PassageGeometryBoundary.lean et modules Off/* complets

2. **Universalité de progression p_min ≤ p_cnt:** Comment établir que expectedMinimumPrime a ≤ lastPrimeAtStateUpper S pour tout membre vrai?
   - Pas dans code terminal (param hMandatory)  
   - Peut-être tracée au pointappel (non lu)
   - **Action:** Vérifier point d'appel du terminal

3. **Compilabilité TAN-Q amont:** Où F01–F15 parents sont dérivés (périodicité tan, π/T)?
   - Likely in Tower/Incidences.lean ou Foundation
   - **Action:** Lire Incidences.lean complet

### ✗ MANQUANT CRITIQUE

**NO-OFF puis RH:** Le théorème final
```lean
theorem riemannHypothesis_rhv6 : RiemannHypothesis := by ...
```
n'existe pas. C'est la **route F20 manquante.** La chaîne logique s'arrête à OFF→False, mais sans pont vers β=1/2 pour tout zéro.

---

## XI. ACTIONS RECOMMANDÉES POUR RHV6

### Immédiates (fidélité audit)

1. **Lire Off/* complets** pour tracer OFF_AUTHENTIC_CONTACT_DEFICIT
2. **Lire Terminal/* complets** pour tracer UNIVERSAL_PROGRESS  
3. **Compiler avec lakefile correct** et vérifier SORRY/ADMIT
4. **Mettre à jour RHV6_FIRST_UNSOLVED_GOAL.md** avec inventaire exact

### À court terme (complétude compilée)

1. **Réintroduire parents F01–F15 compilés** ou références exactes vers RHV3Lean
2. **Compiler F16 (progression pré-OFF)** sans OFF
3. **Compiler F17–F18 (miroir deux Tours)** sur résultats amont
4. **Compiler F19 (O60 alternative ou expected/counted)** — déjà fait de manière partielle
5. **Compiler F20 (NO-OFF → line critique → RH)** — **MANQUANT**

### Avant certification RH

- [ ] Tous théorèmes F01–F20 compilent avec SORRY=0 ADMIT=0
- [ ] #print axioms confirme [propext, Classical.choice, Quot.sound]
- [ ] Audit OFF_AUTHENTIC_CONTACT_DEFICIT trace de géométrie miroir uniquement
- [ ] Audit UNIVERSAL_PROGRESS trace de progression pre-OFF déjà prouvée uniquement
- [ ] Théorème final riemannHypothesis_rhv6 : RiemannHypothesis existe et compile

---

## ANNEXE A : MAPPINGS FORMELS

### Maître sémantique § → Implémentation RHV6

| § Sém | Contenu | Lean RHV6 | Type d'implémentation |
|---|---|---|---|
| 1-2 | Domaine z,β,T | TrueZero | Type fondamental |
| 3-5 | TAN-Q | Incidences.lean (implicite) | Parents Lean |
| 6-7 | Miroir exact | MirrorGeometry.lean | Théorèmes géométrie |
| 8-9 | M^Z=M seam | Reconstruction.lean | Défini |
| 10-11 | expectedMinimumPrime | Grammar/ExpectedMinimum.lean | Défini librement |
| 12 | Terminal p_min ≤ p_cnt < p_min | Terminal/AuthenticCountComparison.lean | Compilé |
| 13-16 | Authenticity OFF, progression | Off/*.lean, Terminal/*.lean (?) | À vérifier |

### Maître mathématique § → Implémentation RHV6

| § Math | Contenu | Lean RHV6 | Statut |
|---|---|---|---|
| 1 | TAN-Q formule | Tower/Incidences.lean (?) | À vérifier |
| 2 | GP1-GP4 raccord | Grammar/Reconstruction.lean (?) | À vérifier |
| 3 | MIR-DELTA exact | Tower/MirrorGeometry.lean (?) | À vérifier |
| 4 | O60 discret | **REMPLACÉ** | Expected/counted|
| 5 | O61-O64 NO-OFF | **MANQUANT** | F20 |
| 22 | OFF_CONTACT_DEFICIT | hAuthenticOffContact (param) | Obligation amont |

---

**Audit terminé le 2026-09-21.**
**Prochaine étape:** Compiler avec lake build correct et publier.

---

# CORRECTION D'AUDIT — 2026-09-21 (cycle de mise en conformité architecturale)

Cette section est **normative et prioritaire** sur les tableaux « ✓ COMPILÉ »/« ✓ CONFORME » ci-dessus partout où ils divergent : une relecture indépendante (3 agents de recherche ayant lu intégralement les 3 maîtres + les 22 fichiers Lean réels + exécuté `lake build`) a montré que l'audit initial n'avait **jamais obtenu de build vert** et avait marqué « ✓ COMPILÉ » des modules dont la compilation n'avait pas été vérifiée. Un cycle correction → build → audit a été exécuté jusqu'à stabilisation. État réel, vérifié :

## Constats corrigés

1. **Build cassé, maintenant réparé.** `lake build` échouait par timeout déterministe (`isDefEq`, 200000 heartbeats) sur `Tower/Incidences.lean:43`, dans `contactAt_tangent_minus` — le `change` y référençait `towerStateAt`, expensive à unifier, avant même la définition de ce dernier. Réécrit pour prouver directement l'identité tangentielle sans passer par `towerStateAt` (même technique que `contactAt_tangent_plus`) ; `towerStateAt.tangent_law` appelle maintenant ce lemme. `lake build` est **vert de bout en bout** (3846/3846 cibles), zéro `sorry`, zéro `admit`, zéro axiome nouveau.

2. **Collision de nom `occurrence` résolue.** `CleanTerminal.lean` (route active, sans dépendance RHV5) et `Grammar/Reconstruction.lean` (pont Seam RHV5) définissaient chacun un `occurrence` distinct dans le même namespace. Le second a été renommé `occurrenceViaRHV5Seam` et sa portée documentée comme branche historique/de comparaison — jamais fusionnable avec `RHV6Fresh.occurrence`.

3. **Sept fichiers non compilables supprimés.** `Core/Zero.lean`, `Grammar/Reconstruction.lean`, `Diagnostics/SamePrimeProvenance.lean`, `Terminal/DirectPassageDichotomy.lean`, `Terminal/ExpectedMinimumFront.lean`, `Terminal/PrimeProgressionCollision.lean`, `Terminal/ContactVonMangoldtCount.lean` importaient directement ou transitivement des modules `RHV5Fresh.*`, alors que `lakefile.toml` de `RHV6Fresh` ne déclare **aucune** dépendance vers `RHV5Fresh` (seul `rhv3_lean` est requis). Ces sept fichiers n'ont donc **jamais pu compiler** dans ce projet — ils étaient orphelins et invérifiés. Leur contenu utile (réfutation de SAME-EVENT/SAME-PRIME, pont Seam) était soit dupliqué par des théorèmes RHV3-purs déjà présents (`CleanTerminal.occurrence_eq_canonicalAnchor`, inconditionnel), soit hors périmètre de la route active. Aucune perte de couverture du périmètre normatif : la route active ne les consommait pas.

4. **Cinq fichiers orphelins légitimes rattachés au graphe compilé** via un nouveau module d'agrégation `Parents/CompiledGeometry.lean`, importé depuis `RHV6Fresh.lean` : `Tower/MirrorGeometry.lean`, `Off/PassageGeometryBoundary.lean`, `Terminal/AuthenticPassageReadout.lean`, `Tower/IndependentTerminalBoundary.lean`, `Terminal/OffCountExperiment.lean`. Tous compilent et sont désormais audités par `#print axioms` depuis `Audit.lean`. Classification et justification par fichier : voir la docstring de `Parents/CompiledGeometry.lean`.

5. **Obstruction formelle mise en évidence, pas dissimulée.** `Terminal/OffCountExperiment.lean` (`lastPrimeAtAuthenticPlus_not_lt_expectedMinimum`) prouve la **négation** du déficit OFF à `authenticContactPlus` pour toute passage authentique, avec le producteur d'état actuellement disponible (`authenticStateFromZero`). `Tower/IndependentTerminalBoundary.lean` (`authenticAddress_eq_floor_occurrence`) prouve que ce producteur est dérivé de l'occurrence reconstruite. Conjointement : le producteur d'état actuellement disponible **ne peut pas** servir à démontrer `hAuthenticOffContact` (obligation A, Math §16) — il est structurellement contaminé au sens Sem §10-11/§14. C'est un résultat **BORNÉ(portée)** : il borne la portée de la construction actuelle, il ne réfute pas l'obligation A elle-même. Un producteur Tour-intrinsèque, indépendant de l'occurrence (au sens Sem §10 : « voyage réel de cette Tour »), reste à construire.

6. **Chaîne conditionnelle jusqu'à `RiemannHypothesis` construite (absente auparavant à 100 %).** Nouveau fichier `Terminal/ConditionalClosure.lean` :
   - `POffImpliesObligations` — empaquette les deux obligations ouvertes (Math §16 mâchoire OFF, Math §17 mâchoire de progression) en une seule hypothèse nommée et explicite, jamais déchargée ;
   - `noOff_of_offImpliesObligations`, `criticalLine_of_offImpliesObligations` — conditionnels sur cette hypothèse, ferment `¬PIsOffCriticalLine` puis `β = 1/2` ;
   - `PEveryUpperHasAuthenticPredecessor` — hypothèse structurelle séparée (existence d'un prédécesseur consécutif pour tout zéro supérieur), non scientifique, jamais confondue avec l'obligation A/B ;
   - `riemannHypothesis_conditional : POffImpliesObligations → PEveryUpperHasAuthenticPredecessor → RiemannHypothesis`, réutilisant `RHV3Lean.thm_riemannHypothesis_of_allUpperOnCriticalLine` (parent déjà compilé dans RHV3Lean, aucune nouvelle prémisse scientifique).
   Aucune des deux hypothèses n'est fermée : `RH_FOUND=FALSE` reste exact et honnête.

7. **Manifeste de fidélité réécrit.** `RHV6Fresh/Audit.lean` porte désormais le statut exact (format maître Lean §29-30) et un `#print axioms` sur chaque théorème terminal/parent réellement dans le graphe — tous ne dépendent que de `[propext, Classical.choice, Quot.sound]`.

## Vérifications exécutées

- `lake build` → `Build completed successfully (3846 jobs)`.
- `grep -rn '\bsorry\b\|\badmit\b\|^axiom' RHV6Fresh/RHV6Fresh/**/*.lean` → aucun hit en code (deux occurrences du mot anglais « admit » en prose, non-code).
- Grep des objets interdits (SAME-EVENT, SAME-PRIME, C3, N_P=1, receptionState, syncState, heightGap) → aucun hit vivant ; le seul hit restant est un commentaire disant explicitement leur absence.
- Graphe d'import depuis `RHV6Fresh.lean` → couvre les 16 fichiers `.lean` restants à 100 % (zéro orphelin).

## Statut final honnête

```
BUILD=PASS (3846/3846)
SORRY=0  ADMIT=0  NEW_AXIOM=0
AXIOMS=[propext, Classical.choice, Quot.sound]
ORPHANED_FILES=0
OFF_CONTACT_DEFICIT=TO_PROVE_OR_REUSE
MANDATORY_BOUND_SAME_READOUT=TO_PROVE_OR_REUSE
RIEMANN_HYPOTHESIS_TERM=PRESENT_CONDITIONAL (riemannHypothesis_conditional)
RH_FOUND=FALSE
```

**RÉFUTÉ :** aucun objet interdit vivant ; le producteur d'état `authenticStateFromZero` actuel ne peut pas satisfaire l'obligation OFF (`Terminal/OffCountExperiment.lean`).
**BORNÉ (portée) :** la contradiction terminale (`directContactCountContradiction`) et sa chaîne conditionnelle jusqu'à `RiemannHypothesis` sont prouvées *sous réserve* des deux obligations nommées et non déchargées `POffImpliesObligations` et `PEveryUpperHasAuthenticPredecessor`.
**SÉLECTIONS :** le prochain travail scientifique substantiel est la construction d'un producteur de second-Tour Tour-intrinsèque et indépendant de l'occurrence (Sem §10-11), seul chemin non exclu vers l'obligation A.

---

# CORRECTION D'AUDIT — 2026-09-21 (bis) — poids logique exact des mâchoires

La recommandation « SÉLECTIONS » de la section précédente (construire un producteur Tour-intrinsèque pour atteindre l'obligation A) est **caduque**, et la chaîne `riemannHypothesis_conditional` est **vide** : chacune de ses deux hypothèses implique `RiemannHypothesis` à elle seule, et la seconde est réfutable. Pour tout producteur d'état satisfaisant la mâchoire de progression, la mâchoire OFF est équivalente à `RiemannHypothesis` (compilé). La mâchoire de progression est déchargée inconditionnellement par un producteur Tour-intrinsèque explicite (`coarseJourneyState`). Détail complet, théorèmes, statut et bloc RÉFUTÉ/BORNÉ/SÉLECTIONS : `AUDIT_MACHOIRES_TERMINALES_20260921.md`. Modules : `RHV6Fresh/Terminal/JawEquivalence.lean`, `RHV6Fresh/Tower/CoarseJourneyState.lean`.


---

## CORRECTION D'AUDIT — 2026-09-22 — voyage à deux Tours

La formalisation par mâchoires (`Terminal/JawEquivalence.lean`, `Terminal/ConditionalClosure.lean`,
`Tower/CoarseJourneyState.lean`) est supprimée. Le terminal actif est l'architecture relationnelle
`RHV6Fresh/Voyage/` décrite dans `AUDIT_VOYAGE_DEUX_TOURS_20260922.md` (terminal compilé
`riemannHypothesis_of_journeyProgression`, RH_FOUND=FALSE).
