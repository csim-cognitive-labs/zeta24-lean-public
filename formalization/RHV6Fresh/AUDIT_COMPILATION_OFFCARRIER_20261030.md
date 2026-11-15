# Audit exact des tentatives de compilation — `Terminal/OffCarrier.lean` (2026-10-30)

Objet : consigner **toutes** les tentatives de compilation du module porteur du zéro OFF, et la tentative directe de
fermeture qui l'a précédée ; pour chaque tentative, l'état du source soumis, le verdict du compilateur, et pour chaque
erreur : le message exact, la cause analysée, la correction appliquée, le résultat de la correction. Les journaux sont
conservés dans `audits_compilation/offcarrier/` (tranche du journal de `lake build` à partir de la première ligne qui
concerne le module ; les 30 000 lignes de rejeu des dépendances ne sont pas conservées, elles ne contiennent aucune
erreur et sont identiques d'une tentative à l'autre).

Règle de lecture : une tentative est **réussie** si et seulement si `lake build` termine par `Build completed
successfully`, aucune ligne `error`, et chaque ligne `#print axioms` du module ne mentionne que
`[propext, Classical.choice, Quot.sound]`. Un `sorryAx` dans une ligne d'axiomes signifie qu'une preuve du module a été
remplacée par `sorry` par le compilateur à la suite d'une erreur d'élaboration : la tentative est un échec même si
d'autres théorèmes passent.

Commande de chaque tentative :
`cd formalization/RHV6Fresh && timeout 600 lake build RHV6Fresh.Terminal.OffCarrier > <journal> 2>&1` (bornée ; 900 s
pour les tentatives 1 à 6). Durée observée d'une tentative : entre 30 s et 90 s (rejeu des dépendances compris).

| # | Heure (UTC) | Section soumise | Journal | Verdict | Erreurs |
|---|---|---|---|---|---|
| 0 | 05:49–05:53 | tentative directe de fermeture (hors module) | `closure_attempts.lean`, `closure_attempts.log` | négatif (attendu) | 5 × `exact?` sans résultat |
| 1 | 06:10 | §1–§6 (module initial, plan §19.8) | `offcarrier1.module.log` | réussi | 0 |
| 2 | 06:21 | §5bis | `offcarrier2.module.log` | réussi | 0 |
| 3 | 06:28 | §5ter | `offcarrier3.module.log` | **échec** | 2 (+ 1 `sorryAx` induit) |
| 4 | 06:29 | §5ter corrigé | `offcarrier4.module.log` | réussi | 0 |
| 5 | 06:32 | §5quater | `offcarrier5.module.log` | **échec** | 1 (+ 1 `sorryAx` induit) |
| 6 | 06:33 | §5quater corrigé | `offcarrier6.module.log` | réussi | 0 |
| 7 | 07:03 | §5quinquies | `offcarrier7.module.log` | **échec** | 17 lignes d'erreur, 8 causes distinctes (+ 1 `sorryAx` induit) |
| 8 | 07:04 | §5quinquies corrigé (1) | `offcarrier8.module.log` | **échec** | 1 |
| 9 | 07:05 | §5quinquies corrigé (2) | `offcarrier9.module.log` | réussi | 0 ; 23 lignes `#print axioms`, toutes standard |
| 10 | 07:2x | §5sexies | `offcarrier10.module.log` | **échec** | 2 |
| 11 | 07:2x | §5sexies corrigé | `offcarrier11.module.log` | réussi | 0 ; 29 lignes `#print axioms`, toutes standard |
| 12 | 07:4x | §5septies | `offcarrier12.module.log` | réussi | 0 ; 33 lignes `#print axioms`, toutes standard |

Sources soumis conservés : `sec5ter_attempt1_source.lean` (tentative 3), `sec5quater_attempt1_source.lean` (tentative 5),
`sec5quinquies_attempt1_source.lean` (7), `sec5quinquies_attempt2_source.lean` (8), `sec5quinquies_attempt3_source.lean`
(9), `sec5sexies_attempt1_source.lean` (10), `sec5sexies_attempt2_source.lean` (11), `sec5septies_attempt1_source.lean` (12, identique au module validé). Les versions validées des §5ter et §5quater sont celles des commits `08ed3405` et
`64038422`.

---

## Tentative 0 — tentative directe de fermeture (05:49, hors module ; consignée au maître §19.9.4)

Fichier `closure_attempts.lean` : cinq énoncés soumis à `exact?` (recherche exhaustive de la bibliothèque compilée) :
`DemandBoundedAtMeetings`, `SupremumAttained`, `UniformVariationAtGaps`, `DemandBoundedEverywhere`, et une borne du
niveau de la demande à une rencontre par la norme de la série des résidus.

Résultat exact (journal `closure_attempts.log`) : cinq fois
`error: exact? could not close the goal. Try apply? to see partial suggestions.` (lignes 12, 17, 22, 27, 33).

Analyse : aucun de ces énoncés n'est une instance d'un théorème de la bibliothèque, ni ne s'en déduit par une
application directe. Ce résultat **n'est pas une erreur de rédaction** : c'est le constat négatif prévu, qui a motivé le
retrait de la voie clôture/supremum/variation uniforme (§19) comme dérive. Aucune correction : la tentative est close.

## Tentatives 1 et 2 — module initial (§1–§6) et §5bis : réussies du premier coup

Aucune erreur. Journaux conservés pour la traçabilité (16 puis 8 lignes d'axiomes standard, uniquement des
avertissements de longueur de ligne).

## Tentative 3 — §5ter (06:28) : deux erreurs

### Erreur 3.1 — `OffCarrier.lean:466:2: Type mismatch`

Message exact :
```
error: RHV6Fresh/Terminal/OffCarrier.lean:466:2: Type mismatch
  shared_frequency_no_common_meeting C.zero C.outgoingMember (Eq.symm (outgoing_same_height C)) (outgoing_radial_lt C)
has type
  ∀ (k k' : ℤ), smoothedMeeting (zeroPoint C.zero) k ≠ smoothedMeeting (zeroPoint C.outgoingMember) k'
but is expected to have type
  smoothedMeeting (zeroPoint C.zero) k ≠ smoothedMeeting (zeroPoint C.outgoingMember) k'
```
Théorème concerné : `outgoing_no_common_smoothed_meeting (k k' : ℤ)`.
Cause : le théorème de la bibliothèque `shared_frequency_no_common_meeting` est quantifié sur les deux indices `k k'`
dans sa conclusion ; l'énoncé du module fixe `k k'` comme arguments. Le terme fourni est donc une fonction de `k k'`
là où une proposition instanciée est attendue.
Correction : appliquer le théorème aux deux indices (`... C.outgoing_radial_lt k k'`).
Résultat : erreur disparue à la tentative 4.

### Erreur 3.2 — `OffCarrier.lean:475:73: linarith failed to find a contradiction`

Message exact :
```
error: RHV6Fresh/Terminal/OffCarrier.lean:475:73: linarith failed to find a contradiction
C : OffCarrier
hx : 0 < meetingPoint C.gap
a✝ : rZeroRadialPosition ↑C.outgoingMember - 1 ≤ rZeroRadialPosition ↑C.zero - 1
⊢ False
```
Théorème concerné : `outgoing_amplitude_gt_zero_at_meeting`.
Cause : `linarith` travaille sur des atomes syntaxiques. Le but, après réécriture par `zeroTerm_density_norm`, contient
`rZeroRadialPosition ↑C.outgoingMember` (le membre sortant vu comme `TrueZero`, projeté), tandis que l'hypothèse
disponible `C.outgoing_radial_lt` parle de `rZeroRadialPosition C.outgoing.zLaterMember`. Les deux termes sont égaux par
définition (`outgoingMember_val : (C.outgoingMember).1 = C.outgoing.zLaterMember := rfl`) mais ne sont pas
syntaxiquement identiques, et `linarith` ne déplie pas les définitions.
Correction : introduire explicitement `have hr : rZeroRadialPosition C.zero.1 < rZeroRadialPosition C.outgoingMember.1
:= C.outgoing_radial_lt` (la coercion de type accepte le terme par définition), puis `linarith`.
Résultat : erreur disparue à la tentative 4.

### Conséquence induite 3.3 — `sorryAx` sur `outgoing_no_common_smoothed_meeting`

Ligne `#print axioms` de la tentative 3 : `[propext, sorryAx, Classical.choice, Quot.sound]` pour ce théorème. Ce n'est
pas une troisième erreur : c'est la trace de l'erreur 3.1 (le compilateur remplace une preuve en échec par `sorry` pour
poursuivre). Disparue avec 3.1.

## Tentative 4 — §5ter corrigé (06:29) : réussie

16 lignes d'axiomes standard. Commit `08ed3405`.

## Tentative 5 — §5quater (06:32) : une erreur

### Erreur 5.1 — `OffCarrier.lean:550:53: Function expected`

Message exact :
```
error: RHV6Fresh/Terminal/OffCarrier.lean:550:53: Function expected at
  rZeroHeight ↑(mirrorMember C.zero)
but this term has type
  ℝ
Note: Expected a function because this term is being applied to the argument
  rw
```
Théorème concerné : `fiber_eq_pair_of_mirror`.
Cause : un bloc `by show ... ⏎ rw [...]` écrit sur deux lignes **comme argument** de `Complex.ext` (donc à l'intérieur
d'un terme, pas d'une tactique de premier niveau). L'analyseur syntaxique a lu la seconde ligne `rw ...` comme un
argument appliqué à la fin de l'énoncé du `show` (le terme `rZeroHeight ↑(mirrorMember C.zero)` étant alors « appliqué »
à `rw`). C'est une erreur de disposition, non de mathématique.
Correction : sortir l'égalité des hauteurs dans un `have hH : rZeroHeight w.1 = rZeroHeight (mirrorMember C.zero).1 :=
by rw [mirrorMember_ordinate]; exact hw` **avant** l'appel, puis `Complex.ext heq' hH`.
Résultat : erreur disparue à la tentative 6.

### Conséquence induite 5.2 — `sorryAx` sur `fiber_eq_pair_of_mirror`

Trace de 5.1 (même mécanisme que 3.3). Disparue avec 5.1.

## Tentative 6 — §5quater corrigé (06:33) : réussie

16 lignes d'axiomes standard. Commit `64038422`.

## Tentative 7 — §5quinquies (07:03) : 17 lignes d'erreur, 8 causes distinctes

Source soumis : `sec5quinquies_attempt1_source.lean`. Journal : `offcarrier7.module.log`.

### Erreur 7.1 — `Unknown identifier volume` (lignes 744, 746, 865) et `Unknown identifier integral_add` (769, 867)

Messages exacts :
```
error: RHV6Fresh/Terminal/OffCarrier.lean:744:47: Unknown identifier `volume`
error: RHV6Fresh/Terminal/OffCarrier.lean:746:67: Unknown identifier `volume`
error: RHV6Fresh/Terminal/OffCarrier.lean:769:47: Unknown identifier `integral_add`
error: RHV6Fresh/Terminal/OffCarrier.lean:865:75: Unknown identifier `volume`
error: RHV6Fresh/Terminal/OffCarrier.lean:867:47: Unknown identifier `integral_add`
```
Théorèmes concernés : `realCountingDensity_intervalIntegrable`, `pair_real_signature_explicit`, `gapTerm_mirror_pair`.
Cause : le module n'ouvre que l'espace de noms `RHV3Lean`. La mesure de Lebesgue `volume` vit dans `MeasureTheory`, et
`integral_add`/`integral_sub` pour les intégrales sur un segment vivent dans `intervalIntegral`. Le module
`LocalPrimeGapSynchronization` d'où viennent les énoncés réutilisés ouvre ces deux espaces ; le porteur ne le faisait pas.
Correction : ajouter `open MeasureTheory intervalIntegral ComplexConjugate` en tête de la section 5quinquies.
Résultat : les cinq lignes disparaissent à la tentative 8.

### Erreur 7.2 — `unsolved goals` (759:52 et 863:76), conséquences de 7.1

Messages exacts (extrait) :
```
error: RHV6Fresh/Terminal/OffCarrier.lean:759:52: unsolved goals
...
hI1 : IntervalIntegrable (realCountingDensity (C.linePoint - ↑C.radialShift)) sorry I.a I.b
...
error: RHV6Fresh/Terminal/OffCarrier.lean:863:76: unsolved goals
...
hc : ∀ (σ : ℂ), IntervalIntegrable (fun t ↦ Complex.exp (σ * ↑t)) sorry a b
```
Cause : la mesure inconnue (`volume`) a été remplacée par `sorry` dans les hypothèses d'intégrabilité ; la suite de la
preuve (`rw [← integral_add ...]`) n'a pas pu s'appliquer. Aucune cause propre : ces deux erreurs sont induites par 7.1.
Résultat : disparues à la tentative 8 sans autre modification.

### Erreur 7.3 — `'show' tactic failed` (797:2)

Message exact :
```
error: RHV6Fresh/Terminal/OffCarrier.lean:797:2: 'show' tactic failed, pattern
  fnPrimeAtRank (C.n - 1 + 1) = fnPrimeAtRank C.n
is not definitionally equal to target
  C.previousGap.upper = C.gap.lower
```
Théorème concerné : `previousGap_upper_eq_gap_lower`.
Cause : `PrimeGapInterval.upper` est à valeurs **réelles** : `fnPrimeAtRank (I.rank + 1)` y est coercé de `ℕ` vers `ℝ`.
Le `show` proposait une égalité dans `ℕ`, qui n'est pas le but (égalité dans `ℝ` entre deux coercions). Erreur de type,
pas de mathématique.
Correction : `have h : C.n - 1 + 1 = C.n := by have := C.one_le_n; omega` puis `simp only [PrimeGapInterval.upper,
PrimeGapInterval.lower, previousGap, gap, h]` (le simplificateur réduit la projection du constructeur et réécrit `h`
sous la coercion).
Résultat : erreur disparue à la tentative 8.

### Erreur 7.4 — `linarith failed` (914:2)

Message exact :
```
error: RHV6Fresh/Terminal/OffCarrier.lean:914:2: linarith failed to find a contradiction
w w' : TrueZero
h : conjIndex w = memberIndex w'
him : -rZeroHeight ↑w = rZeroHeight ↑w'
⊢ False
```
Théorème concerné : `conjIndex_ne_memberIndex`.
Cause : les positivités `w.2`, `w'.2` ont été passées à `linarith` sous la forme de projections de sous-type dont le
type n'est pas syntaxiquement `0 < rZeroHeight ↑w` (il l'est par définition seulement). `linarith` ne les a pas
reconnues comme inégalités sur les mêmes atomes (même mécanisme que l'erreur 3.2).
Correction : `have hw : 0 < rZeroHeight w.1 := w.2` et `have hw' : 0 < rZeroHeight w'.1 := w'.2`, puis `linarith`.
Résultat : erreur disparue à la tentative 8.

### Erreur 7.5 — `Unknown identifier conj` (919:12, 919:38, 928:9, 947:18) et `unsolved goals` induit (916:93)

Messages exacts :
```
error: RHV6Fresh/Terminal/OffCarrier.lean:919:12: Unknown identifier `conj`
error: RHV6Fresh/Terminal/OffCarrier.lean:919:38: Unknown identifier `conj`
error: RHV6Fresh/Terminal/OffCarrier.lean:916:93: unsolved goals
error: RHV6Fresh/Terminal/OffCarrier.lean:928:9: Unknown identifier `conj`
error: RHV6Fresh/Terminal/OffCarrier.lean:947:18: Unknown identifier `conj`
```
Théorèmes concernés : `conjIndex_ne_mirrorConjIndex`, `conjIndex_mem_packet`, `packet_mem_cases`.
Cause : la notation `conj` pour la conjugaison complexe est fournie par l'espace de noms de notations
`ComplexConjugate`, non ouvert dans le module (il l'est dans `CanonicalEnumeration` où `conjIndex` est défini).
Correction : incluse dans l'ouverture ajoutée pour 7.1 (`open ... ComplexConjugate`).
Résultat : les cinq lignes disparaissent à la tentative 8.

### Erreur 7.6 — `rewrite failed: Did not find an occurrence of the pattern |(↑↑w).im|` (941:25)

Message exact :
```
error: RHV6Fresh/Terminal/OffCarrier.lean:941:25: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  |(↑↑w).im|
in the target expression
  |rZeroHeight ↑w| = rZeroHeight ↑C.zero
...
h0 : |rZeroHeight ↑w| = rZeroHeight ↑C.zero
⊢ rZeroHeight ↑w = rZeroHeight ↑C.zero
Full error:
  Application type mismatch: The argument zZero has type TNonTrivialZetaZero but is expected to have type
    { cPoint // PIsNonTrivialZetaZero cPoint } in the application ↑zZero
```
Théorème concerné : `packet_mem_cases`, branche `Sum.inl`.
Cause : `zeroPoint` est une abréviation (`abbrev`), dépliée à l'élaboration : l'hypothèse `h0`, déclarée avec
`(zeroPoint w).im`, s'est retrouvée sous la forme `rZeroHeight ↑w` (même objet, autre présentation), de sorte que la
réécriture par `zeroPoint_im` (dont le membre gauche est `(↑↑w).im`) ne trouve plus son motif. L'« erreur complète »
rapporte en outre un conflit de coercions entre deux présentations du type des zéros non triviaux, qui a empêché la
réécriture de s'unifier.
Correction : ne plus réécrire par `zeroPoint_im` ; déclarer directement `h0 : |rZeroHeight w.1| = rZeroHeight
C.zero.1 := hσ` (acceptée par définition) et conclure par `abs_of_pos hpos` avec `hpos : 0 < rZeroHeight w.1 := w.2`.
Même traitement dans la branche conjuguée (`conj_im` puis passage par définition à `|-(rZeroHeight w.1)|`) et dans
`conjIndex_mem_packet` (`change` au lieu de `show`, puis la même séquence).
Résultat : erreur disparue à la tentative 8.

### Erreur 7.7 — `Invalid ⟨...⟩ notation` (982:12, 983:12)

Messages exacts :
```
error: RHV6Fresh/Terminal/OffCarrier.lean:982:12: Invalid `⟨...⟩` notation: The expected type `x = a ∨ x = b → False` is not an inductive type
error: RHV6Fresh/Terminal/OffCarrier.lean:983:12: Invalid `⟨...⟩` notation: The expected type `x = a ∨ x = b → False` is not an inductive type
```
Théorème concerné : `four_sdiff_two`.
Cause : le but est une conjonction dont le second membre est une négation `¬(x = a ∨ x = b)`, c'est-à-dire une
fonction vers `False`. Le constructeur anonyme `⟨p, hca, hcb⟩` a été aplati en `⟨p, ⟨hca, hcb⟩⟩`, et `⟨hca, hcb⟩` n'est
pas une preuve d'une implication.
Correction : fournir la négation comme fonction : `fun h => h.elim hca hcb`. Au passage, la tactique `push_neg`
(signalée obsolète par l'avertissement 975:4) est retirée au profit d'un traitement direct par cas (`absurd (Or.inl rfl)
h2`).
Résultat : erreur disparue à la tentative 8.

### Conséquence induite 7.8 — `sorryAx` sur `target_split_of_mirror`

Ligne d'axiomes de la tentative 7 : `[propext, sorryAx, Classical.choice, Quot.sound]` pour `target_split_of_mirror`
(qui dépend de `packet_channel_four_of_mirror`, lui-même dépendant des lemmes en échec). Trace, pas cause. Disparue à
la tentative 9.

Avertissements non bloquants relevés à la tentative 7 et traités : `show` qui change le but (837:2 → `change`),
`Set.diff_self` obsolète (1006:10 → voir 8.1), `push_neg` obsolète (975:4 → retiré).

## Tentative 8 — §5quinquies corrigé (1) (07:04) : une erreur

Source soumis : `sec5quinquies_attempt2_source.lean`. Journal : `offcarrier8.module.log`.

### Erreur 8.1 — `rewrite failed: Did not find an occurrence of the pattern channelOn ∅ ?x` (1014:22)

Message exact :
```
error: RHV6Fresh/Terminal/OffCarrier.lean:1014:22: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  channelOn ∅ ?x
in the target expression
  ... + (nontrivialZeroResidueTerm x (conjIndex C.zero) + nontrivialZeroResidueTerm x (conjIndex (mirrorMember C.zero)) +
        channelOn ⊥ x) = ...
```
Théorème concerné : `packet_channel_four_of_mirror`.
Cause : pour éliminer `{c, d} \ {c, d}`, la tentative 8 utilisait le lemme général de treillis `sdiff_self`, qui produit
l'élément bas `⊥` du treillis des parties, et non l'ensemble vide `∅`. Les deux sont égaux mais non syntaxiquement
identiques ; le lemme `channelOn_empty`, énoncé sur `∅`, ne s'applique donc pas par réécriture.
Correction : utiliser le lemme spécifique aux ensembles `Set.sdiff_self` (qui produit `∅`).
Résultat : erreur disparue à la tentative 9.

## Tentative 9 — §5quinquies corrigé (2) (07:05) : réussie

Source : `sec5quinquies_attempt3_source.lean` (= module validé). Journal : `offcarrier9.module.log`.
`Build completed successfully` ; aucune ligne `error` ; **23 lignes `#print axioms`, toutes `[propext,
Classical.choice, Quot.sound]`** ; `grep -c sorry` sur le module = 1, occurrence située dans le commentaire d'en-tête
(« Aucun `sorry` ») et non dans une preuve. Avertissements restants : longueur de ligne, `show` de lisibilité dans les
sections antérieures (§5ter, §5quater), `push_neg` obsolète en §5quater (508:2) — aucun n'affecte la validité.

## Tentative 10 — §5sexies (la cassure) : deux erreurs

Source soumis : `sec5sexies_attempt1_source.lean`. Journal : `offcarrier10.module.log`.

### Erreur 10.1 — `failed to compile definition, consider marking it as 'noncomputable'` (1080:4)

Message exact :
```
error: RHV6Fresh/Terminal/OffCarrier.lean:1080:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'fnPrimeAtRank', which is 'noncomputable'
```
Définition concernée : `meetingPred := fnPrimeAtRank (C.n + 1) - 1`.
Cause : `fnPrimeAtRank` est non calculable (énumération des premiers par choix) ; une définition à valeurs dans `ℕ` qui
en dépend doit être déclarée `noncomputable`, sinon le compilateur tente d'en produire du code exécutable.
Correction : `noncomputable def meetingPred`.
Résultat : erreur disparue à la tentative 11.

### Erreur 10.2 — `omega could not prove the goal` (1130:90)

Message exact :
```
error: RHV6Fresh/Terminal/OffCarrier.lean:1130:90: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  c ≥ 1, b ≥ 0, b - c ≥ 0, b - c ≥ 0, a ≥ 0, a - b ≥ 1
where
 a := ↑(fnPrimeAtRank C.n.succ)
 b := ↑(fnPrimeAtRank C.n)
 c := ↑(fnPrimeAtRank (C.n + 1))
```
Théorème concerné : `gap_demand_eq_break_add_rest`, hypothèse `hw`.
Cause : l'hypothèse `hlt` avait été obtenue par `thm_primeAtRank_strictMono (Nat.lt_succ_self C.n)`, dont la conclusion
s'écrit avec `C.n.succ`. `omega` traite `fnPrimeAtRank C.n.succ` et `fnPrimeAtRank (C.n + 1)` comme deux atomes
distincts (`a` et `c` dans le contre-exemple), et ne voit donc pas que `a = c`. Même famille que les erreurs 3.2 et 7.4 :
deux présentations d'un même terme.
Correction : énoncer `hlt : fnPrimeAtRank C.n < fnPrimeAtRank (C.n + 1) := thm_primeAtRank_strictMono (by omega)` avec
la forme `C.n + 1` explicite.
Résultat : erreur disparue à la tentative 11.

## Tentative 11 — §5sexies corrigé : réussie

`Build completed successfully` ; aucune ligne `error` ; **29 lignes `#print axioms`, toutes standard** ; aucun
`sorryAx`.

## Tentative 12 — §5septies (le prochain point de rencontre) : réussie du premier coup

Source : `sec5septies_attempt1_source.lean`. Journal : `offcarrier12.module.log`. `Build completed successfully` ;
aucune ligne `error` ; **33 lignes `#print axioms`, toutes standard** ; aucun `sorryAx`.

---

## Bilan des causes (12 tentatives, 4 échecs, 14 causes distinctes)

| Catégorie | Occurrences | Tentatives |
|---|---|---|
| Espace de noms non ouvert (`volume`, `integral_add`, `conj`) | 2 causes (10 lignes) | 7 |
| Atomes non syntaxiquement identiques pour `linarith`/`omega` (projection de sous-type, `succ` contre `+ 1`) | 3 | 3, 7, 10 |
| Définition à valeurs entières dépendant d'un objet non calculable, sans `noncomputable` | 1 | 10 |
| Abréviation dépliée qui défait un motif de réécriture (`zeroPoint`) | 1 | 7 |
| Lemme général de treillis (`⊥`) contre lemme spécifique aux ensembles (`∅`) | 1 | 8 |
| Égalité dans `ℕ` proposée pour un but dans `ℝ` (coercion sous `show`) | 1 | 7 |
| Théorème quantifié non instancié | 1 | 3 |
| Disposition syntaxique (`show … ⏎ rw` comme argument de terme) | 1 | 5 |
| Constructeur anonyme pour une négation (fonction) | 1 | 7 |
| `exact?` sans résultat (tentative directe de fermeture) | 5 énoncés | 0 |

Aucune des erreurs des tentatives 3, 5, 7, 8, 10 n'est une erreur mathématique : toutes sont des erreurs d'élaboration
(noms, types, formes syntaxiques) et chaque correction a conservé l'énoncé du théorème à l'identique. La seule tentative
négative sur le fond est la tentative 0 (fermeture directe), dont le résultat négatif est consigné comme tel au maître.

---

## Module `Terminal/FrequencyCap.lean` (§19.15, 2026-10-30) — tentatives 1–2 : réussies

Journal complet : `audits_compilation/frequencycap/`. Module isolé, non ajouté à `RHV6Fresh.lean`.

| Tentative | Source | Journal | Résultat |
|---|---|---|---|
| 1 | `frequencycap_attempt1_source.lean` (§1–§5 : rang ⟺ comptage, pont zeta23, plancher, plafond, `N₀ + 2W`) | `frequencycap1.module.log` | `Build completed successfully`, 0 `error`, 5 `#print axioms` standard ; 10 avertissements de style (lignes > 100 caractères dans l'en-tête), aucun sur une preuve |
| 2 | `frequencycap_attempt2_source.lean` (§6 ajouté : caps lus dans les contacts) | `frequencycap2.module.log` | `Build completed successfully`, 0 `error`, 7 `#print axioms` standard |

Aucune erreur de compilation ; aucune cause à consigner. Points vérifiés avant écriture (pour éviter les causes déjà
cataloguées) : `zetaZeroMultiplicity` et `Zeta23.zeroMult` sont définitionnellement égaux (`analyticOrderNatAt` est
`(analyticOrderAt …).toNat` dans Mathlib) ; `PIsNonTrivialZetaZero` et `Zeta23.IsNontrivialZero` sont le même
prédicat ; les deux conventions de fenêtre sont `0 < Im ≤ a` ; `Ncount_add`, `Ncount_mono`, `zerosIn_finite` existent
dans `Zeta23Port/RvM/NcountWindow.lean` et `Statement/SeamClosed.lean` ; les `.olean` du port étaient déjà construits.

---

## Module `Terminal/ThreeZeroWindow.lean` (§19.16, 2026-10-30) — tentatives 1–2 : la seconde réussie

Journal complet : `audits_compilation/threezerowindow/`. Module isolé, non ajouté à `RHV6Fresh.lean`.

| Tentative | Source | Journal | Résultat |
|---|---|---|---|
| 1 | `threezerowindow_attempt1_source.lean` | `threezerowindow1.module.log` | **Échec**, 2 erreurs d'élaboration (voir ci-dessous) ; `three_window_bracketed` et `far_member_above_unit` déjà aux axiomes standard, les 6 autres marqués `sorryAx` par propagation des erreurs |
| 2 | `threezerowindow_attempt2_source.lean` | `threezerowindow2.module.log` | `Build completed successfully`, 0 `error`, 8 `#print axioms` standard ; 14 avertissements de style (lignes > 100 caractères, `Set.mem_setOf_eq` déprécié corrigé en `Set.mem_ofPred_eq`) |

Erreurs de la tentative 1, exactes :
- `ThreeZeroWindow.lean:90:9: Unknown identifier le_or_lt` (et `rcases` échoue en cascade) — nom Mathlib courant : `le_or_gt`. Correction : nom.
- `ThreeZeroWindow.lean:303:4: linarith failed` dans `pair_two_places` : l'hypothèse `C.low` est énoncée sur `canonicalMember C.n`, l'égalité radiale sur `C.zero` ; atomes syntaxiquement différents pour `linarith`. Correction : `C.zero_low` (énoncé sur `C.zero`). Même cause que « atomes syntaxiquement identiques » déjà cataloguée.

Aucune erreur mathématique ; les énoncés des huit théorèmes sont inchangés entre les deux tentatives.

---

## Module `Terminal/OccurrenceHeightComposition.lean` (§19.17, 2026-10-30) — tentatives 1–2 : les deux réussies

Journal complet : `audits_compilation/occurrenceheightcomposition/`. Module isolé, non ajouté à `RHV6Fresh.lean`.

| Tentative | Source | Journal | Résultat |
|---|---|---|---|
| 1 | `occurrenceheightcomposition_attempt1_source.lean` (§1–§4 : injectivité de l'occurrence, cible ⟺ RH, composition aveugle sur le porteur, transport au premier partagé) | `occurrenceheightcomposition1.module.log` | `Build completed successfully`, 0 `error`, 12 `#print axioms` standard ; avertissements de style seulement (lignes > 100 caractères) |
| 2 | `occurrenceheightcomposition_attempt2_source.lean` (§5 ajouté : motif des trois raccords) | `occurrenceheightcomposition2.module.log` | `Build completed successfully`, 0 `error`, 14 `#print axioms` standard, 0 `sorryAx` ; 42 avertissements de style, aucun sur une preuve |

Aucune erreur de compilation ; aucune cause à consigner. Points vérifiés avant écriture : `thm_distinctZeroMembers_comparable` prend l'inégalité des supports (`.1 ≠ .1`) ; `thm_zeroMemberPrecedes_iff_height_radial_lex` donne « hauteur strictement plus petite, ou même hauteur et radial strictement plus petit » ; `TowerRaccord.Oriented` est un `def` que `not_le.mpr` traverse par défaut ; `card_ge_of_height_le` (FrequencyCap) prend `k` implicite ; `towerRaccord_oriented_of_height_lt` (via `raccordHierarchy_of_height_advance`) n'exige pas l'égalité des positions radiales, contrairement à `towerRaccord_oriented_of_vertical`.

---

## Module `Terminal/TransportAtSharedPrime.lean` (§19.18, 2026-10-30) — tentatives 1–2 : la seconde réussie

Journal complet : `audits_compilation/transportatsharedprime/`. Module isolé, non ajouté à `RHV6Fresh.lean`.

| Tentative | Source | Journal | Résultat |
|---|---|---|---|
| 1 | `transportatsharedprime_attempt1_source.lean` | `transportatsharedprime1.module.log` | **Échec**, 3 erreurs d'élaboration (ci-dessous) ; 18 des 21 `#print axioms` déjà standard, 3 marqués `sorryAx` par propagation (`prevMember_expectedMinimumPrime`, `detour_arithmetic_factor_ne_one`, `detour_transport_ne_onLine_chain`) |
| 2 | `transportatsharedprime_attempt2_source.lean` | `transportatsharedprime2.module.log` | `Build completed successfully`, 0 `error`, 21 `#print axioms` standard, 0 `sorryAx` ; 61 avertissements, tous de style (lignes > 100 caractères), aucun sur une preuve |

Erreurs de la tentative 1, exactes :
- `TransportAtSharedPrime.lean:133:99: unsolved goals` — but restant `expectedMinimumPrime C.prevMember = expectedMinimumPrime ⟨C.arrival.zEarlierMember, ⋯⟩` : `rw` ne replie pas la définition `prevMember`. Correction : `unfold prevMember` avant le `rw`.
- `TransportAtSharedPrime.lean:238:2: No goals to be solved` — dans `detour_transport_product`, `field_simp` ferme déjà le but ; le `ring` qui suit est de trop. Correction : suppression du `ring`.
- `TransportAtSharedPrime.lean:270:53: Tactic rewrite failed … pattern Real.exp ?x = 1 … in the target Real.exp (…) ≠ 1` — `Real.exp_eq_one_iff` ne se réécrit pas sous `≠`. Correction : `intro hEq` puis réécriture dans l'hypothèse.

Aucune erreur mathématique ; les énoncés des vingt-et-un théorèmes sont inchangés entre les deux tentatives. Jumeau déterministe E399 exécuté après la tentative 2 (voir `experiments/E399_DetourPrimeContent/README.md`).

## Module `Terminal/TransportAtSharedPrime.lean` (§19.19) — tentatives 3–4 : la quatrième réussie

Ajout de la §4 (`detour_defect_eq_memberStep_product` : le défaut du détour est le produit des deux pas de membre de la
paire, `memberStep` de `PrimalEventRaccord`). Sources exactes : `audits_compilation/transportatsharedprime/transportatsharedprime_attempt3_source.lean`,
`..._attempt4_source.lean` ; journaux `transportatsharedprime3.module.log`, `transportatsharedprime4.module.log`.

| Tentative | Résultat | Erreurs | Cause exacte | Correction |
|---|---|---|---|---|
| 3 | EXIT 1, build failed | 9 lignes `error` (7 `Unknown identifier C.…`, 1 `unsolved goals` 316:99 par propagation, 1 `Unknown constant` au `#print axioms`) | la §4 a été insérée APRÈS `end OffCarrier` (ligne 304) : la variable `C : OffCarrier` n'existe plus hors du namespace | rouvrir `namespace OffCarrier` + `variable (C : OffCarrier)` avant la §4, `end OffCarrier` avant les `#print axioms` |
| 4 | EXIT 0, `Build completed successfully (9078 jobs)` | 0 | — | — |

Tentative 4 : 22 `#print axioms`, tous `[propext, Classical.choice, Quot.sound]` ; 0 `sorryAx` ; avertissements de longueur
de ligne seulement. Aucune erreur mathématique sur les deux tentatives : la preuve (`unfold memberStep`, réécritures des
occurrences et premiers minimaux du zéro et du miroir, `rpow_neg`, `inv_rpow`, `inv_div`, `mul_rpow`, `div_mul_div_comm`,
`ring`) est passée telle quelle dès que le namespace a été rétabli.
