# Démarche inverse : des premiers aux modes (E334, 2026-10-18)

Mission de l'auteur : partir des premiers, de leurs écarts, de la grammaire et des impulsions de comptage ; retrouver fréquences,
amplitudes, phases, contacts et `(β, T)`. Lean : `RHV6Fresh/Terminal/InversePrimeSpectral.lean` (nouveau) et
`Terminal/CountingFieldArchitecture.lean`. Expérience : `experiments/E334_InversePrimeSpectralReconstruction/` (le nom E333 était
déjà pris par l'architecture du champ de comptage). Aucune conclusion sur la fermeture n'est posée.

Statuts : [I] démontré en Lean ; [C] caractérisation ; [O] ouvert ; [M] mesure finie.

## 1. Architecture inverse

| Étape | Objet | Statut |
|---|---|---|
| Premiers, puissances | `countingWeight n = Λ(n)/log n` (`1/k` en `p^k`) | [I] `countingWeight_prime`, `countingWeight_nonneg` |
| Comptage exact | `countingJHalf` (demi-saut), `countingJLeft` (à gauche, égal hors des entiers) | [I] définitions, `countingJHalf_gap` |
| Mesure atomique | `DJ = Σ w(n) δ_n`, au sens des fonctions test `C¹` nulles aux bords | [I] `counting_distributional_derivative` |
| Écarts | `D_n = Δ(J₀ − F)`, `ΔJ₀ = 1 + Σ internes` | [I] `countingJHalf_prime_gap`, `gapCountingCorrection_prime_gap` |
| Transport `u = log x` | atome normalisé `Λ(n)/√n`, fond `e^{u/2}/2` | [I] `normalized_atom_weight`, `normalized_background_density` |
| Mode | densité normalisée = `e^{(β−1/2)u} cos(Tu)` | [I] `normalized_mode_density` |
| Identité spectrale | somme sur les zéros = signal | [O] canal `J` (`CountingExplicitFormula`, nommée) ; [I] canal lissé (`smoothedRemainder_eq_tsum_residueTerm`) |
| Unicité | une représentation détermine chaque `(β, T, m)` | [I] `cpow_series_fibre_sum_zero`, `recovers_member`, `no_intruder` (canal lissé) |
| Amplitude intrinsèque | constante ⟺ `β = 1/2` ; pour tous ⟺ RH | [C] `individualAmplitudeRigidity_iff`, `individualAmplitudeRigidity_all_iff` |
| Maillon précédent | contraintes arithmétiques ⟹ rigidité | [O] |

## 2. Correction de la normalisation

La prescription `A(u) = −(e^{u/2}u/2)[DC]` porte le mauvais signe d'exposant. Avec `x = e^u` :
`u·w(n) = Λ(n)` et `u·(e^u/u) = e^u`, donc `u·DC` est la mesure `Σ Λ(n) δ_{log n} − e^u du` (canal `ψ`). Il faut ensuite
`e^{−u/2}`, non `e^{+u/2}`, pour obtenir des atomes `Λ(n)/√n`, un fond `e^{u/2}` et des modes `e^{(β−1/2)u}cos(Tu)`. Le facteur
correct, `−u e^{−u/2}/2`, est démontré mode par mode (`normalized_mode_density`). Jacobien : les atomes sont transportés sans
jacobien (image de mesure) ; la densité du fond reçoit le facteur `e^u` (`dx = e^u du`), inclus dans `e^u/u`.

## 3. Régularité (chaque affirmation, son théorème ou son contre-exemple)

| Objet | Régularité | Justification |
|---|---|---|
| `J₀`, `J₋` | constants par morceaux, sauts `w(n)` aux puissances de premiers | définition ; `countingJHalf_gap` |
| `DJ` | mesure atomique, pas une fonction | [I] `counting_distributional_derivative` |
| `F` | lisse sur `]1, ∞[` | classique (non formalisé, `li` absent) |
| `C = J₀ − F` | lisse sur chaque intervalle ouvert sans puissance de premier ; dérivable hors d'un ensemble dénombrable | conséquence des deux lignes précédentes ; donc PAS nulle part dérivable |
| somme finie `S_N` | `C^∞` sur `]1, ∞[` | [I] `countingSum_hasDerivAt` ; ne porte aucun saut : [I] `complement_discontinuous_of_jump` |
| limite `F + S_∞` | égale `J₀` (formule explicite) | [O] `CountingExplicitFormula` |
| signal normalisé `A` | mesure (atomes `Λ(n)/√n` moins densité lisse) | [I] §2 |
| « limite nulle part dérivable » | aucun objet de ce chantier ne l'est ; la question demanderait un autre objet (par exemple une primitive d'une série lacunaire), non identifié ici | — |

## 4. Les dix questions de normalisation (réponses courtes)

1. Normalisation : `−u e^{−u/2}/2`, §2. 2. Les impulsions deviennent les atomes `Λ(n)/√n` en `u = log n`. 3. Distribution :
les atomes ; fonction : le fond et chaque mode. 4. Convergence : au sens des fonctions test (et au demi-saut ponctuellement,
mesuré E332/E333) ; démontrée nulle part pour le canal `J`. 5. Fréquences : transformée de Fourier des atomes contre une fenêtre
lisse en `u` (E334-C). 6. Coefficients : projection du signal sur `e^{iτu}` par fenêtres successives (E334-D). 7. Unicité :
démontrée pour le canal lissé (lecture du pôle, Mellin) ; transport au canal `J` non écrit. 8. Fenêtre finie : fréquences à la
résolution `2π/L` près, amplitudes avec une erreur qui croît quand la fenêtre se raccourcit (E334-J). 9. Totalité des événements :
l'identité exacte et l'unicité. 10. Bords et fond : le fond est soustrait exactement (`e^{u/2}/2`), les bords par des fenêtres nulles
aux extrémités (`counting_distributional_derivative` exige `φ(a) = φ(b) = 0`).

## 5. Audit de la chaîne terminale dans le sens inverse

| Théorème | Donnée venant des premiers | Propriété spectrale déduite | Introduit depuis les zéros |
|---|---|---|---|
| comptages 15/22/28 | aucune (ζ directement, rectangles) | ancre | — |
| `arrival_low_contradiction` | `smoothedRemainder` (premiers seuls), exposant 1 (`hGrammarAmplitude`), saut `Λ(N)` (`hEventJump`) | représentation exacte (`hReproduction`), unicité, contribution imposée | passage `p`, historique ON (`hHist`), `hBelow` |
| formes `hAbsurdCloses`, `hResidualCloses`, `hWeightedCloses` | écrites avec les premiers seuls | — | — |
| `hFrequencyCloses`, `hMeetingCloses`, `hAmplitudeCloses` | — | caractérisations de `β_l = 1/2` | lues sur l'arrivée |

Remplaçable par une reconstruction inverse : la désignation de l'arrivée par sa hauteur (fréquence) l'est (unicité) ; sa position
radiale ne l'est pas, c'est le but. Conversion manquante : du canal lissé (où l'unicité est démontrée) au canal `J` (où vivent les
impulsions) pour la somme entière ; membre par membre elle existe (`counting_modulation_eq_raw_derivative`, `normalized_mode_density`).

## 6. E334 (mesures)

Détail : `experiments/E334_InversePrimeSpectralReconstruction/README.md` ; 29 contrôles, 23 PASS, 6 FAIL déclarés.

* Non-circularité : 4/4 PASS. Aucun accès aux hauteurs publiées ni aux fonctions ζ pendant la reconstruction (pièges, crochet
  d'audit, empreintes).
* Méthode A, transformée des atomes `Λ(n)/√n` en `u`, fenêtre gaussienne, X = 1e8 : 106 fréquences sur `[8, 247]`. Validation
  faite après coup : 100/100 des premières hauteurs, erreur médiane 1,3e−8. `|β̂ − 1/2| ≤ 1,4e−8` sur les dix premières, lu sur la
  pente de phase dans une seule fenêtre. Portée : contre une fenêtre gaussienne, la formule explicite rend la transformée EXACTEMENT
  une somme de pics, un par zéro. Cette précision vérifie l'identité ; elle ne mesure pas la force d'une méthode.
* Méthode B, série de Dirichlet tronquée et lissée : 37/37 fréquences sous 118 pour σ = 0,6 et 0,75. Pour σ = 1, seulement 3 à 4
  pics.
* Méthode C, poursuite de modes sur les `D_n` : la version déclarée d'avance échoue (repliement dû aux grands écarts en `u` pour
  `p` petit). La version a posteriori (`p ≥ 1000`, `τ ≤ 60`) retrouve 9/10 fréquences et `γ̂ − 1/2 ≈ 2e−4`. Une paire proche reste
  fusionnée et la cohérence entre fenêtres est médiocre.
* Contacts : l'inversion tangentielle depuis la phase reconstruite donne `|β − 1/2| ≤ 2,6e−5`. Elle ne rend que son entrée et
  n'ajoute aucune contrainte.
* Amplitudes, 8 fenêtres successives : pentes `|d| ≤ 7e−10`. La RMS collective (0,80 à 0,93) est tenue séparée des coefficients
  individuels.
* Régularité : de 3 à 106 modes, l'erreur sup sur les écarts ouverts passe de 0,21 à 0,07. Dépassement ≈ 0,098 du saut.
* Réinjection jusqu'à 1e5 : RMS par écart de 0,753 à 0,736 seulement. La fréquence nécessaire pour résoudre un écart, `π p/g`, a
  une médiane de 2,2e3 pour `p ∈ [10³, 10⁴]` ; au-delà de 10³, aucun écart n'est à la portée de 106 modes.
* Lecture : depuis les seuls premiers, les fréquences et la position radiale des modes résolus sont retrouvées, et celle-ci vaut un
  demi à la précision de la mesure, sur un horizon fini. C'est une mesure, pas le maillon « arithmétique ⟹ rigidité ».

## 7. Obligations restantes

1. [O] Contraintes arithmétiques exactes ⟹ rigidité d'amplitude individuelle (⟺ RH quantifiée, `individualAmplitudeRigidity_all_iff`).
2. [O] Formule explicite du canal `J` (`CountingExplicitFormula`).
3. [O] Unicité spectrale transportée au canal `J`.
4. But `:484` inchangé.
