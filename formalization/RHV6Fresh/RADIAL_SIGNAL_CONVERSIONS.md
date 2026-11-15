# Signal radial exact : formules, normalisations, pertes d'information (audit radial total, 2026-10-13)

Source Lean : `RHV6Fresh/Terminal/ExactSignalArchitecture.lean` (41 théorèmes, 18 objets, axiomes standard, importé).
Contrôle numérique : `experiments/e242_exact_signal_audit/` (16 PASS, 0 FAIL).
Notations : `ρ = β + iT`, `0 < β < 1`, `T > 0`, `t = log x`, `d = β − 1/2`, `‖ρ‖ = √(β² + T²)`, `θ = arctan(T/β) = arg ρ`.

## 1. Trois représentations, trois types Lean

| Type Lean | Formule | Lien au code antérieur |
|---|---|---|
| `ExactZeroSignal` | `E_ρ(t) = e^{ρt}/ρ` | `= zeroTerm z x` en `t = log x` (`zeroTerm_eq_exactSignal`) |
| `RescaledZeroSignal` | `R_ρ(t) = e^{−t/2}E_ρ(t) = e^{(d+iT)t}/ρ` | normalisation `√x` d'E150, E163b, E180, `normalizedRadius` |
| `UnitCoefficientMode` | `U_ρ(t) = e^{(d+iT)t}` | `complexMode` d'E224–E241 (`unitMode_eval_eq_complexMode`) |

Ce sont des structures DISTINCTES : un `UnitCoefficientMode` ne peut pas être passé là où un `ExactZeroSignal` est attendu.
Conversions démontrées :

- `E = (e^{t/2}/ρ)·U` (`exact_eq_unit`) ;
- `R = U/ρ` (`rescaled_eq_unit`) ;
- `U = ρ·R` (`unit_eq_coeff_mul_rescaled`) ;
- `R = e^{−t/2}·E` (`rescaled_eq_exact`).

Régression : `E(0) = 1/ρ ≠ 1 = U(0)` dès `ρ ≠ 1` (`exactSignal_ne_unitMode_at_zero`), vrai sur tout vrai zéro (`zeroTerm_ne_unitMode`) :
une suppression silencieuse de `1/ρ` change la valeur en `t = 0`.

## 2. Formules exactes démontrées

| Objet | Formule | Théorème |
|---|---|---|
| forme polaire | `E(t) = (e^{βt}/‖ρ‖)·e^{i(Tt − θ)}` | `exactSignal_polar` (via `zeroCoeff_polar`) |
| module | `‖E‖ = x^β/‖ρ‖` | `exactSignal_norm` |
| partie réelle | `(x^β/‖ρ‖)cos(T log x − θ)` | `exactSignal_re` |
| partie imaginaire | `(x^β/‖ρ‖)sin(T log x − θ)` | `exactSignal_im` |
| dérivée | `E' = ρE` | `exactSignal_hasDerivAt` |
| courant individuel | `J = Im(ĒE') = T e^{2βt}/(β² + T²)` | `exactCurrent_eq` |
| lien au courant unitaire | `J = (T/‖ρ‖²)·e^{t}·e^{2dt}` | `exactCurrent_eq_scaled_reduced` |
| rapport | `J₂/J₁ = (T₂‖ρ₁‖²)/(T₁‖ρ₂‖²)·e^{2(d₂−d₁)t}` | `exactCurrentRatio_eq` |
| interférence | `‖E₁+E₂‖² = e^{2β₁t}/‖ρ₁‖² + e^{2β₂t}/‖ρ₂‖² + 2e^{(β₁+β₂)t}/(‖ρ₁‖‖ρ₂‖)·cos ΔΦ` | `exact_interference_normSq` |
| déphasage | `ΔΦ = (T₂ − T₁)t + θ₁ − θ₂` | `conj_mul_exactSignal` |
| courant croisé | `W₁₂ = e^{(β₁+β₂)t}/(‖ρ₁‖‖ρ₂‖)·[T₂cos ΔΦ + β₂ sin ΔΦ]` (coefficient `β₂ + iT₂`) | `exactCross_eq` |
| partie symétrique | `W₁₂ + W₂₁ = A·[(T₁+T₂)cos ΔΦ + (β₂ − β₁)sin ΔΦ]` | `exactCross_symm_eq` |
| courant collectif | `Im(conj(ΣE)·Σ ρE) = Σ_nΣ_m W_{nm}` | `exactCollectiveCurrent_eq_sum` |
| croisé exact / unitaire | `W^{exact} = Im((e^{t}/ρ̄₁)·Ū₁U₂)`, `W^{unit} = Im((ρ₂ − 1/2)·Ū₁U₂)` | `exactCross_eq_rotated_unit` |
| paire miroir, même hauteur | `W₁₂ = T e^{t}/‖ρ₁‖²` | `exact_mirror_cross_eq` |
| partie croisée miroir | `T e^{t}(1/‖ρ₊‖² + 1/‖ρ₋‖²) < 2T e^{t}/(1/4 + T²)` (`d ≠ 0`, `T² > 3/4`) | `exact_mirror_cross_lt_double` |
| contacts absolus | `C_k = exp((θ + kπ)/T)` ; deux contacts consécutifs égaux ⟹ même `(β, T)` | `exact_contacts_determine_parameters` |
| inversion | `T = π/log(C_{k+1}/C_k)`, `β = T/tan(T log C_k)` | `inversion_from_consecutive_contacts` (existant, réutilisé) |
| perte de phase | `Im U(kπ/T) = 0` pour toute `d` | `unitMode_im_zero_at` |

Conditions de branche : `θ = arctan(T/β) ∈ ]0, π/2[` pour `β > 0`, `T > 0` ; `tan(T log C_k) = T/β ≠ 0` sur tout contact
(`inversion_tan_ne_zero`). Les contacts absolus ne sont jamais remplacés par des différences de positions :
`gap_reading_height_only` lit une différence dans une même Tour, et le décalage commun qu'elle efface est `θ/T`.

## 3. Ce que chaque normalisation perd

| Passage | Facteur retiré | Contient `β` ? | Conséquence |
|---|---|---|---|
| `E → R` | `e^{t/2}` | non | aucune perte radiale (échelle commune à tous les zéros) |
| `R → U` | `1/ρ = e^{−iθ}/‖ρ‖` | oui, par `‖ρ‖ = √(β²+T²)` et `θ = arctan(T/β)` | perte d'une constante d'amplitude et de la phase initiale |

Mesures (E242) :

- **Amplitude.** `∂ log‖E‖/∂β = log x − β/‖ρ‖²` contre `log x` pour `U`. La part portée par `1/ρ` est au plus `3,6·10⁻³` de
  celle de l'exposant (`T₁`, `x = 2`), et elle décroît en `1/T²`.
- **Phase.** Les annulations de `Im U` sont en `kπ/T` pour toute `β` (`unitMode_im_zero_at`). Les contacts exacts portent `θ`.
  À `T₁`, passer de `β = 0,5` à `β = 0,3` décale `log C_0` de `1,0·10⁻³`.
- **Courants individuels.** `J^{exact}` est un multiple RÉEL POSITIF constant de `J^{unit}`. Toute égalité à deux abscisses
  est inchangée (`exactCurrentRatio_two_points_iff`) : aucune information sur `β` n'était perdue dans les tests B, C, D, E
  d'E240.
- **Courant croisé.** Le passage est une ROTATION complexe `1/ρ̄₁`, pas un facteur réel. Les annulations exactes (ON→ON,
  zéros 1→2) sont en `t = (kπ − θ₁)/(T₂ − T₁)`, contre `(k + 1/2)π/(T₂ − T₁)` en unitaire. Le décalage
  `arctan(β₁/T₁)/(T₂ − T₁)` vaut `5,1·10⁻³` en `t`.
- **Interférence.** Le mode unitaire de deux Tours ON s'annule à chaque battement (amplitudes égales à 1). L'interférence
  exacte ne s'annule jamais (`1/‖ρ₁‖ ≠ 1/‖ρ₂‖`), et le déphasage `θ₁ − θ₂` décale les minima (figure 3).
- **Paire miroir de même hauteur.** En unitaire, la partie croisée vaut `2T` pour toute `d` (`mirror_cross_current_blind`,
  aveugle). En exact, elle est strictement inférieure au double ON dès `d ≠ 0`. L'écart relatif est `−5,0·10⁻⁵` à `d = 0,1`
  et `−7,95·10⁻⁴` à `d = 0,4` (`T₁`). C'est un détecteur d'ordre `d²`, pair en `d`.

## 4. Portée

Le coefficient `1/ρ` est une fonction de `(β, T)` constante en `t`. Il ne crée donc aucune relation entre deux Tours qui ne
soit déjà une fonction de leurs paramètres : il ajoute des détecteurs, il ne fixe pas `β`. Les modules antérieurs à E224
travaillaient déjà sur `zeroTerm` ou sur `x^ρ/ρ` normalisé par `√x`, qui conserve `1/ρ`. Seuls `HarmonicRestoringLaw`,
`HarmonicCurrentTransport` et `HarmonicCrossCurrent` utilisent le mode unitaire (inventaire `e242_lean_inventory.csv`).
