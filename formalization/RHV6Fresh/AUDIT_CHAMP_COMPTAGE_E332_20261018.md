# Audit E332 : Tours dans le champ de comptage (2026-10-18)

Mission de l'auteur : tirer d'E332 (`9d70cd7e`) toutes les conséquences mathématiques, géométriques, sémantiques et formelles.
Ce document regroupe les livrables 1 à 4 et 7 à 9 ; E333 (livrable 6) est dans `experiments/E333_CountingFieldArchitecture/` ;
le module Lean (livrable 5) est `RHV6Fresh/Terminal/CountingFieldArchitecture.lean`. Aucune conclusion sur la fermeture n'est posée.

Statuts : [I] identité démontrée en Lean ; [C] conditionnel à un énoncé nommé, non démontré ; [M] mesure finie (E332/E333) ;
[A] asymptotique classique, non formalisée ; [O] obligation ouverte.

## 1. Audit mathématique d'E332 : équations réellement utilisées

| Objet | Équation dans E332 | Statut |
|---|---|---|
| Fond | `F(x) = li(x) − log 2 + ∫_x^∞ dt/(t(t²−1) log t)` | formule de Riemann ; `F` n'est pas défini dans le dépôt (abstrait `F : ℝ → ℝ` en Lean) |
| Contribution | `b_ρ(x) = −2 Re Ei(ρ log x)`, `Ei(w) = −E₁(−w) + iπ` (Im w > 0) | branche le long de `ρ log x` ; `Ei` absent de Mathlib, primitive locale en hypothèse `hF` |
| Densité | `b_ρ'(x) = −2x^{β−1} cos(T log x)/log x` | [I] `counting_pair_hasDerivAt` |
| Somme | `S_N = Σ_{j≤N} b_{ρ_j}` par ordre de hauteur | [I] `countingSum`, `countingSum_hasDerivAt` |
| Canal | `J₀(x) = Σ_{n≤x} Λ(n)/log n`, demi-saut aux puissances de premiers | [I] `countingJHalf` (nouveau) |
| Correction d'écart | `D_n = Δ(J₀ − F)` sur `[p_n, p_{n+1}]`, `ΔJ₀ = 1 + Σ_{internes} 1/k` | [I] `countingJHalf_prime_gap`, `gapCountingCorrection_prime_gap` |
| Complément | `E_{n,N} = D_n − ΔS_N` | [I] `gapComplement`, `gapComplement_insert`, `gapComplement_add` |
| Limite | `F + S_N → J₀` en tout `x > 1` | [C] `CountingExplicitFormula` (nommée, non démontrée) ; [I] sous elle `gapComplement_tendsto_zero` |
| Gibbs | dépassement `≈ 0,0895` du saut | [A] constante `Si(π)/π − 1/2` des séries de Fourier tronquées ; [M] 0,0864–0,0898 |
| Largeur | `≈ 0,88·pπ/T_N` | [M] ; minoration démontrée plus faible : [I] `rise_width_ge` + `collectiveDensity_abs_le` |
| Pics | `S_N'` de hauteur réduite `S_N'·πx/T_N ≥ 0,6` | [M] détecteur, revérifié dans E333-F |

Conséquence : la seule équation non démontrée d'E332 est la limite (formule explicite du canal `J`). Tout le reste est identité
(Lean) ou mesure. Le canal π par zéro (seuils `2^m`) n'entre dans aucune équation conservée.

## 2. Audit géométrique

### 2.1 Fréquences
* Intrinsèque : `T`, constante en `u = log x` ([I] `logPhase_hasDerivAt` : dérivée `T/x`).
* Algébrique : `f(x) = T/(2πx)`, période `λ(x) = 2πx/T` ([I] `localFrequency_mul_localPeriod`).
* Un tour exact couvre `[x, x e^{2π/T}]` ([I] `logPhase_full_turn`), longueur `≥ λ(x)` ([I] `turn_length_ge_localPeriod`).
* Demi-tours d'un zéro sur un écart : `(T/π) log(p_{n+1}/p_n)` ([I] `halfTurnsOnGap_eq_phase_advance`), fonction de la hauteur
  et des bornes seules.
* Représentations à corriger : toute figure qui trace une oscillation de période constante sur l'axe `x` (E238 et ses dérivées
  à axe linéaire). Restent valides : les représentations en `u = log x` (E330/E331, E302 3D en `log x`), où la période est `2π/T`.

### 2.2 Amplitudes : trois niveaux
| Niveau | Objet | Module | Conversion |
|---|---|---|---|
| 1 | mode unité `e^{iTu}` | 1 ([I] `unitMode_norm`) | — |
| 2 | mode pondéré `e^{(β−1/2)u}e^{iTu}` | `e^{(β−1/2)u}` ([I] `norm_weightedResultant_singleton`) | × `e^{(β−1/2)u}` |
| 3 | densité `b'` | `≤ 2x^{β−1}/log x` ([I] `countingDensity_abs_le`) | × `−2/(√x log x)` ([I] `countingDensity_eq_weightedMode`, `densityEnvelope_eq_weightedModule`) |
| 3′ | contribution `b` | intégrale de la densité ; `b ~ −2Re(x^ρ/(ρ log x))` | [A] `Ei(w) ~ e^w/w (1 + 1/w + …)`, [M] E333-C |
| ψ | contribution brute `c = −2Re(x^ρ/ρ)` | `2x^β/‖ρ‖` | [I] `counting_modulation_eq_raw_derivative` : `c' = b'·log x` |

Aucun niveau n'est l'amplitude d'un autre : les facteurs `e^{(β−1/2)u}`, `2/(√x log x)`, `1/‖ρ‖`, `log x` séparent les niveaux.
La position radiale n'entre qu'au niveau 2 et au-delà ; le niveau 1 est aveugle à `β` par définition.

### 2.3 Taxonomie des contacts et événements
| Famille | Équation | Paramètres | Objet exact | Théorèmes |
|---|---|---|---|---|
| (C) contact de Tour | `T log x = φ + kπ`, `φ = arctan(T/β)` | `(β, T)` | `Im(x^ρ/ρ) = 0` : `c` touche son enveloppe `±2x^β/‖ρ‖` | `pairContribution_at_contact`, `abs_pairContribution_at_contact` ; densité de comptage non nulle : `countingDensity_at_contact_ne_zero` (nouveau) ; inversion `T = π/log(C_{k+1}/C_k)`, `β = T/tan(T log C_k)` (`inversion_from_consecutive_contacts`) |
| (D) extremum | `T log x = π/2 + kπ` | `T` seul | zéro de `b'` = extremum de `b` et de `c` | `countingDensity_at_extremum` (nouveau), `backgroundRelativeModulation_extremum`, `extremum_contact_offset` (`log D_k − log C_k = arctan(β/T)/T`) |
| (Z) zéro brut | `T log x = φ + π/2 + kπ` | `(β, T)` | `c = 0` | `pairContribution_at_rawSignalZero`, `rawSignalZero_contact_offset` (`π/(2T)`) (nouveaux) |
| (B) zéro de comptage | `b_ρ(x) = 0` (contact de `F + b_ρ` avec `F`) | `(β, T)` | pas de forme close (`Ei`) ; ≈ (Z) à `O(1/(T log x))` | [A] ; [M] E333-D |
| (P) événement premier | saut de `J₀` en `p^k` | `Λ` | discontinuité de la correction | `countingJHalf_prime_gap` ; aucune somme finie ne la porte : `complement_discontinuous_of_jump` (nouveau) |
| (S) pic collectif | maximum de `S_N'` | toute la famille | approximation de la mesure `dJ₀` | [M] E332, E333-F |

Ordre strict à indice égal : `C_k < D_k < Z_k` ([I] `contact_families_ordered`). Les identités tangentielles sont CONSERVÉES : elles
décrivent la famille (C), contacts de la contribution brute avec son enveloppe ; ni des extrema, ni des zéros, ni des événements.

## 3. Architecture des signaux (correspondance avec les noms demandés)

| Nom de la mission | Objet du dépôt |
|---|---|
| `ExactZeroSignal`, `RescaledZeroSignal`, `UnitCoefficientMode` | `ExactSignalArchitecture.lean` (inchangés) |
| `CountingDensity` | `countingModulationDensity` |
| `CountingContribution` | `−2 Re F_z(ρ log x)` avec primitive `F_z` (`countingSum {z}`) |
| `CollectiveCountingSum` | `countingSum` |
| `ArithmeticCountingBackground` | `F : ℝ → ℝ` abstrait (non défini) ; canal `countingJHalf` (nouveau, défini depuis `Λ`) |
| `PrimeGapWindow` | `PrimeGapInterval` (`LocalPrimeGapSynchronization`) ; paires `p < q` de premiers ici |
| `CollectiveGapCorrection` | `gapCountingCorrection` (nouveau) |
| `TruncationComplement` | `gapComplement` (nouveau) |
| `SpectralEvent` | `PrimeEvent` (`GeneratedFrequency`) ; saut de `J₀` |
| `TowerAbsoluteContact` | `contactMinusAt` |

## 4. Correspondance Tours ↔ formule explicite ↔ grammaire

| Tour | Champ de comptage | Grammaire |
|---|---|---|
| `(β, T)`, contacts (C) | `c` touche son enveloppe ; `b'` ≠ 0 en (C) | aucun lien direct |
| pas `π/T` en `log x` | demi-période de `b` et `c` ; `(T/π) log(p_{n+1}/p_n)` demi-tours par écart | bornes de l'écart |
| amplitude `x^β/‖ρ‖` | niveaux 2–3 | — |
| — | `ΔS_N` sur `[p_n, p_{n+1}]` = Σ des variations de tous les zéros sur le même écart (`gapSumIncrement_eq_sum_cells`) | `D_n = 1 + internes − ΔF` |
| — | saut porté par la limite (`complement_discontinuous_of_jump`) | événement premier |

## 5. Lean

`Terminal/CountingFieldArchitecture.lean` (nouveau, importé par la racine, non composé dans la chaîne ; 33 énoncés, axiomes
standard) ; docstrings corrigés : `OscillationResultant.lean`, `CountingFieldContacts.lean`. Commit ce9a0d6b.

## 6. E333 (mesures, 51 contrôles PASS, 0 FAIL ; zéros publiés seulement)

* A : un seul repère (`x ∈ [2, 60]`, unités de comptage, fond `F` courbe, escalier `J₀`, `F + b_j`, `F + S_N`) ; RMS de
  `F + S_N − J₀` sur la grille 0,263 / 0,105 / 0,042 (N = 3 / 100 / 1000) ; branche `Ei` contrôlée à 1e−15.
* B : `D_{k+1}/D_k = e^{π/T}` à 1e−15 ; demi-tours moyens par écart jusqu'à 1000 : 0,17 (zéro 1), 0,59 (10), 2,8 (100), 16,8 (1000) ;
  ils ne dépendent que de `g_n/p_n` (Spearman 1) : un zéro bas ne résout pas un écart, seule la hauteur le résout.
* C : `b'·log x = c'` à 1e−11 ; erreur relative de `−2Re(x^ρ/(ρ log x))` ≈ `1/(‖ρ‖ log x)`.
* D : décalages `log(D/C) = arctan(β/T)/T`, `log(Z/C) = π/(2T)` à 1e−15 ; zéros de `b` (B) décalés de (Z) de `−arg(1 + 1/(ρ log x))/T`
  à 0,1 % ; l'inversion tangentielle ne restitue `(β, T)` QUE sur (C) (sur (D) : `β = 0`, sur (Z) : `β = −T²/β`, sur (B) : β
  absurde) ; aucune attraction des premiers vers une famille (témoin de densité `1/log x`).
* E : RMS d'E332 reproduites ; écarts résolus (`g_n T_N/(π p_n) > 1`) 10 → 167/167 ; `Spearman(|E|, r)` jusqu'à −0,64 ;
  écarts à puissance interne : reste plus faible (0,0065 contre 0,0158, n = 22), observation.
* F : Gibbs théorique 0,08949, mesuré 0,0828–0,0898 ; largeur 0,867–0,891 contre 0,8916 théorique ; le premier 2 manqué par E332
  est un effet de bord de grille (168/168 en partant de 1,5) ; seuils 0,6–0,7 : premiers seuls ; 0,4–0,5 : aussi des puissances.
* G : aux 28 contacts (C) du zéro 1 : `c` touche son enveloppe (±1 alterné), `b_1' ≠ 0` (valeur réduite `β/‖ρ‖`), `b_1 ≠ 0`, aucun
  entier : objet (C) seul, conforme à `countingDensity_at_contact_ne_zero`.
* H : identités par écart (`ΔJ₀`, `ΔF`, `D_n`, classe mod 6 = transition) à 1e−13 ; moyennes de `D_n` par transition et par
  longueur publiées avec IC ; `corr(D_n, 1 − g_n/log p_n) = 0,953` découle de l'identité ; aucune loi causale.

## 7. Audit de la chaîne terminale (`DemonstrationChain.lean`)

Fichier non modifié (aucun nouvel import permis). Lecture théorème par théorème du signal utilisé :

* Comptage initial (`no_zero_at_height_fifteen…`, `upperCountWithMultiplicity_*`, rectangles 15/22/28) : ζ directement ; aucune
  représentation des Tours ; intact.
* Ancre (`anchor_*`) : unicité dans la bande + miroir ; intact.
* `first_passage_window_transmission`, `first_three_*` : canal lissé, fenêtres de contacts ; contacts = famille (C) ; intact.
* `arrival_low_contradiction` (`:484`, seul but) : contexte en canal LISSÉ (`smoothedRemainder`, `nontrivialZeroResidueTerm`) et
  canal brut (`pairAmplitude`). Faits examinés :
  - `hFrequencyCloses` (`lineContact = contactMinusAt`) : rencontre de famille (C), correcte ;
  - `hMeetingCloses` (`smoothedMeeting`) : rencontre du terme lissé, objet distinct de (C), déjà séparé au §115 ;
  - `hLowJointDeviation`, `hMirrorJointDeviation`, `hImposed*` : identités par écart du canal lissé, aucune dépendance au canal π ;
  - aucun fait du contexte n'utilise les contacts du canal π par zéro, ni une période constante en `x`, ni l'identification
    d'un contact à un événement.
  Conclusion d'audit : aucune obligation de la chaîne n'est formulée dans le repère retiré ; le canal `J` n'y figure pas.
* `off_signal_amplitude_incompatible`, `radial_conservation_anchored`, chaîne vers `riemannHypothesis_terminal` : réductions
  exactes, conditionnelles au but `:484` ; intactes.
* Raccordement possible des nouvelles identités : le module n'est pas importé par la chaîne (règle) ; ses énoncés portent sur le canal
  `J`, que la chaîne ne lit pas. Le seul pont entre les canaux est `counting_modulation_eq_raw_derivative` (`c' = b'·log x`),
  membre par membre ; aucune identité collective ne transporte une borne du canal `J` au canal lissé.

## 8. Obligations restantes (formulées sans supposer leur conclusion)

1. [O] `CountingExplicitFormula F S Fz` pour `F` de Riemann et les primitives `Ei` (formule explicite du canal `J`) : transport.
2. [O] Définition de `Ei` / `li` complexe le long de `ρ log x` dans Lean (absente de Mathlib).
3. [O] Constante de Gibbs pour la somme sur les zéros (transfert de la théorie de Fourier aux sommes de Riemann–von Mangoldt).
4. [O] Largeur `≍ πx/T_N` : seule une minoration de type Lipschitz est démontrée, plus faible d'un facteur `√x log x · T_N /(xN)`.
5. Le but `:484` est inchangé : `⊢ False` sous `hBelow`.

## 9. REX

* Corrigé : docstrings d'`OscillationResultant` (niveaux, canal π retiré) et de `CountingFieldContacts` (`Ei(ρ log x)`, pas
  `li(x^ρ)` ; fond = courbe `F`).
* Conservé : identités tangentielles, contacts (C), toutes les identités d'E330/E331, toute la chaîne.
* Démontré : module `CountingFieldArchitecture` (voir §1–§3).
* Mesuré : E333 (voir son README).
* Ouvert : §8.
