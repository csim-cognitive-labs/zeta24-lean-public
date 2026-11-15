# Matrice locale–globale, ancre et trois arrivées (E335, E336, 2026-10-18)

Missions de l'auteur, toutes ajoutées sans remplacement :
- correction après l'audit E334 ;
- ancre arithmétique du premier zéro ;
- certification des trois arrivées et transmission du régime ;
- conservation intégrale sous une rupture OFF.

Les acquis de 26232c48 (E333, E334) sont conservés, et E334 et E185 sont laissés intacts.

Statuts : [I] démontré en Lean ; [C] caractérisation ; [O] ouvert ; [M] mesure finie ; [A] a posteriori.

## 1. Lean (axiomes standard, importés, non composés dans la chaîne)

`Terminal/LocalGlobalGapMatrix.lean`

| Énoncé | Théorème | Statut |
|---|---|---|
| L'atome normalisé vaut `−½·Λ(n)/√n` : le poids `Λ(n)/√n` est positif, le facteur `g = −log x·e^{−log x/2}/2` est négatif. | `normalized_atom_signed`, `normalized_atom_pairing` | [I] |
| Le fond donne `−½ e^{u/2}` ; il est soustrait. | `normalized_background_pairing` | [I] |
| Jacobien : `∫ h(x)dx = ∫ h(e^u)e^u du` ; les atomes sont transportés sans jacobien. | `integral_log_transport` | [I] |
| Un mode par paire conjuguée vaut `e^{(β−1/2)u}cos(Tu)` : le facteur `−2` et le facteur `½` se compensent. | `normalized_mode_pairing` | [I] |
| Famille finie : la somme des modes est linéaire. | `normalized_modes_pairing` | [I] |
| Sur un écart premier : `D_n = S_{n,N} + R_{n,N}`. | `gap_matrix_identity` | [I] |
| Une colonne est additive ; corrections, colonnes et compléments télescopent. | `cellModulation_add`, `window_telescope_*` | [I] |
| Les transitions n'imposent rien au-delà du télescopage, pour toute position radiale. | `transitions_no_constraint_beyond_telescoping` | [I] |
| Repliement : sur une grille uniforme de pas `h`, les fréquences `T` et `T + 2πk/h` donnent les mêmes échantillons à une phase constante près. | `alias_mode_samples` | [I] |
| `T < πp/(q − p)` ⟹ moins d'un demi-tour sur l'écart. | `resolution_of_gap_bound`, `halfTurns_lt_one_of_gap_bound` | [I] |
| Lissé ⟶ brut ⟶ `J`, membre par membre ; `x√x·c̃ = m·primitive`. Le transport de la somme n'est pas écrit. | `smoothedPrimitive_hasDerivAt`, `raw_to_counting_density`, `smoothedPrimitive_eq_normalizedSmoothed` | [I], somme [O] |

`Terminal/FirstArrivalsAnchor.lean`

Le module ne dépend pas du fichier de la chaîne : les comptages sont recomposés depuis les certificats de rectangles.

| Énoncé | Théorème | Statut |
|---|---|---|
| `N(15) = 1`, `N(22) = 2`, `N(28) = 3`. | `arrivals_count_*` | [I] |
| Trois arrivées certifiées : bandes `]0,15]`, `]15,22]`, `]22,28]`, ligne, miroir annulé, aucun OFF jusqu'à 28. | `three_arrivals_certified` | [I] |
| Ancre permanente : sur la ligne, miroir annulé, plus bas membre, `0 < T₁ ≤ 15`. | `anchor_permanent` | [I] |
| Régime initial : `T₁ < T₂ < T₃`, `d₁ = d₂ = d₃ = 0`, rigidité individuelle des trois. | `initial_regime` | [I] |
| Pour les trois arrivées : modes `cos(T_j u)`, contacts de ligne, entrées de matrice sous l'enveloppe de ligne. | `initial_normalized_modes`, `initial_contacts_on_line`, `initial_gap_entries_le` | [I] |
| Arrivée suivante : la matrice est satisfaite pour toute position radiale. | `next_arrival_matrix_any_radial` | [I] |
| Pas de transmission structurelle. | `initial_regime_not_structurally_transmitted` | [I] |
| Première rupture : au-dessus de 28, `N ≥ 5` à sa hauteur, déficit `≥ 2`, colonne sous une enveloppe plus faible que la ligne. | `first_rupture_profile` | [I] |
| Interdire toute arrivée basse ⟺ RH. | `first_rupture_forbidden_iff` | [C] |
| Conservation intégrale : un remplacement est exclu sur le champ complet ; la famille authentique reconstruit pour toute position radiale. | `rupture_finite_vs_global` | [I] |

Le comptage certifie le régime initial ; il ne le transmet pas. La valeur `14,1347…` n'est pas un terme Lean.

## 2. E336 : matrice locale–globale (`experiments/E336_LocalGlobalGapMatrix/`, 21 PASS, 3 FAIL déclarés)

**Identité distributionnelle**
- Écart inférieur à `3·10⁻¹²` avec 5000 zéros.
- Les cinq variantes fausses sont détectées : signe `+½`, jacobiens, conjugués comptés deux fois, `e^{+u/2}`.

**I1–I5**
- `D_n = S_{n,N} + R_{n,N}` est tabulé pour N = 1, 10, 100, 1000, 5000 et pour E334.
- `R(5000)` est de l'ordre de `10⁻³` à `10⁻⁵`.
- Compensation : `|S|/Σ|d|` vaut entre 0,02 % et 2,3 %. Environ la moitié des modes est de signe opposé à `D_n`.
- Le saut en chaque premier est porté par `R` seul.
- L'additivité est vérifiée à `3·10⁻¹⁶`.

**Identifiabilité**
- À l'échelle I1–I5, aucune fréquence n'est identifiable : `L = 1,87`, FWHM 12,6.
- Avec la fenêtre `[2, 10⁷]`, 12 fréquences sur 13 sont identifiées.
- La classification a priori prédit 18 retrouvailles sur 18.
- Pour `p ≤ 100`, les données par écart replient `τ = 120` : c'est la cause des échecs C1–C3 d'E334.

**Question centrale**
- Les transitions n'ajoutent aucune contrainte : le rang au-delà du télescopage est nul.
- La seule contrainte effective est l'invariance des paramètres d'une fenêtre à l'autre. Elle est tenue par les modes identifiables (`ΔT < 4·10⁻³`) et violée par les modes fusionnés, d'où P4c et P4d [FAIL].
- C'est une contrainte d'identifiabilité, pas une contrainte sur `β`.
- Reproduire chaque écart individuellement demande des milliers de modes.

**Audit E334** (`AUDIT_E334_REQUALIFICATION.md`)
- C5 est reclassé en succès partiel [A] : la médiane passe, mais le maximum vaut 0,093.
- C v2 et ses contrôles C4–C6 sont [A].
- J1 était placé sous le plancher numérique.
- Les six échecs sont publiés avec leur cause : repliement pour C1–C3, résolution pour C4 et C6, plancher pour J1.
- La prédéclaration d'E334 n'est pas vérifiable dans git.

## 3. E335 : ancre et trois arrivées (`experiments/E335_FirstZeroArithmeticAnchor/`, 49 PASS, 5 FAIL déclarés)

Non-circularité 4/4 : le producteur ne lit jamais les zéros certifiés.

**Ancre**
- `T̂₁ = 14,134725141735`, à `2,4·10⁻¹³` d'E185. Il est hors de l'intervalle certifié strict (V3 FAIL) : une mesure n'est pas un certificat.
- `β̂₁` par cinq estimateurs, dont deux bruts sans normalisation : `0,4999999989` sur le champ brut, `0,49996` sur les seuls `D_n`.

**Horizons**
- Signal complet : `X = 300`.
- Corrections `D_n` : `3·10⁴`.
- Premiers sans puissances : biais de 0,033 et `β̂ = 0,485` (B2 FAIL) ; les puissances sont nécessaires.
- Grammaire seule : aucune fréquence de ζ.

**I1–I5 et contacts**
- `D_n = d₁ + R₁`. Le premier mode ne reconstruit aucun écart : `R₁` compense `d₁` avec le signe opposé sur chaque transition.
- Les contacts sont une restitution. La phase brute donne un estimateur de plus, pas une contrainte.

**Trois arrivées**
- `T₂`, `T₃` sont retrouvées à `10⁻⁸` près ; `|d_j| ≤ 1,3·10⁻⁷` en brut.
- L'absence d'OFF sous 28 est portée par le comptage Lean.
- La quatrième arrivée est mesurée à `30,4249`, `d₄ ≈ 10⁻⁸` : c'est une mesure, pas une déduction.
- Restreint à une seule classe de transition, `β̂` varie de 0,47 à 0,68 (X6 FAIL).
- Un écart isolé fixe `β₁` seulement si tout le reste est connu (X7 FAIL, seuil mal choisi).

**Rupture paramétrique** (quadruplet complet, jamais un zéro de ζ)
- (a) Non compensée : le défaut vaut environ 230 fois le résidu. C'est un défaut d'INSERTION, d'ordre `d²` seulement ; deux ON insérés au même endroit le produiraient aussi.
- (b) Compensée par 20 modes : échec, même dans les fenêtres d'ajustement (R2 FAIL).
- (c) Exacte sur un nombre fini de fenêtres : possible (rang 96/96, résidu `9·10⁻¹⁶`), mais non transportable (résidu hors fenêtres de 0,26 à 2,8).
- (d) Sur le champ complet : une insertion ou un remplacement est exclu par l'unicité ; une famille authentique contenant déjà un OFF ne l'est pas.

**Comparaison avec E185**
- E335 ne certifie ni l'existence, ni l'unicité jusqu'à 15, ni la simplicité, ni la position sur la ligne, ni l'absence de zéro plus bas.
- Ces points sont portés par E185 et par Lean (`N(15) = 1`).

## 4. Réponse à la question centrale et raccordement terminal

Les mêmes modes, sans réajustement, reproduisent chaque écart et chaque transition. Ils conservent la résultante pour TOUTE position radiale : c'est une identité, `transitions_no_constraint_beyond_telescoping`.

Les contraintes nouvelles observées sont d'identifiabilité (résolution, repliement, fusion), non de rigidité.

Aucune propriété arithmétique indépendante interdisant la première rupture n'est trouvée. Ce qui manque est une borne, depuis les seuls premiers, du reste collectif au-delà de l'arrivée, d'exposant `< 1 − β_l`. Elle a la force d'un demi-plan sans zéro ; quantifiée, c'est RH (`first_rupture_forbidden_iff`).

Une telle borne fournirait l'antécédent de `hResidualCloses`, `hWeightedCloses` ou `hAbsurdCloses`, déjà présents dans `arrival_low_contradiction`, sans toucher à ses hypothèses. But `:484` inchangé.
