# E447 — Résultats : le mécanisme de cassure sur la ligne, écrit avec les contacts (§19.69, 2026-11-07)

Pré-enregistrement : commit `fadf962e` (avant toute compilation). Ordre R-LIGNE respecté : aucun énoncé sur les OFF,
aucune contradiction cherchée.

## Compilation
* Sondes en brouillon non versionné (`E447_SCRATCH.lean`, supprimé après capture) : `attempts/probe1.txt` (6 erreurs :
  `contactRealValue_succ` existait déjà dans `ContactRealValue.lean` avec `T ≠ 0` — réutilisé ; réécriture d'Abel mal
  découpée ; `contact_of_fraction` mal réécrit ; `break_then_descent` demandait l'inégalité stricte `C_k < q` ;
  composition `abs ∘` dans la limite pondérée), `probe2.txt` (1 : `sum_range_succ` non qualifié résolu vers un autre
  lemme), `probe3.txt` (1 : même cause dans le télescopage), `probe4.txt` (0 erreur, 0 `sorry`).
* Module définitif `Terminal/BreakMechanismOnLine.lean` : **tentative 1 verte** (`attempts/build_attempt1.txt`),
  17 déclarations, axiomes standards (`propext`, `Classical.choice`, `Quot.sound`) sur les 7 énoncés imprimés ;
  `lake build RHV6Fresh` complet vert (9064 jobs). Non ajouté à `RHV6Fresh.lean` (module isolé).

## Énoncés compilés (une Tour, ses contacts, ses valeurs ; `rawDemand` ; les premiers)
| Bloc | Énoncé | Contenu |
|---|---|---|
| L1 | `demandAtContact`, `cellDemand_eq_demandAtContact`, `cellDemand_telescope` | somme des pentes d'un bloc = différence des demandes brutes aux deux contacts extrêmes |
| L2 | `valueCellSum_abel`, `valueCellSum_abel_signed` | **bilan d'Abel** : `Σ v_i D_i = v_M R_M − v_0 R_0 + (1+e^{βπ/T}) Σ v_i R_{i+1}` (toute `β`) |
| L3 | `line_contactRealValue_sq`, `line_value_sq_succ`, `line_value_sq_ratio_eq_length_ratio` | `v_k² = C_k/‖(1/2,T)‖²`, `v_{k+1}² = e^{π/T} v_k²`, rapport des carrés = rapport des abscisses |
| L4 | `contact_of_fraction`, `line_break_amplitude_exact`, `line_break_amplitude_bounds`, `line_break_price_bounds` | `C_k = x·e^{−πf/T}` ; `|v_k| = √x·e^{−πf/(2T)}/‖·‖` ; `√x·e^{−π/(2T)} < |v_k|·‖·‖ ≤ √x` ; cassure `log q` payée entre ces bornes |
| L5 | `rawDemand_prime_from_contact`, `break_then_descent` | du contact au premier : poids franchis − descente ; un seul poids : `log q − (q − C_k)` |
| L6 | `rawDemand_div_tendsto_zero`, `demandAtContact_div_tendsto_zero`, `line_weighted_demand_at_contact_small` | `R(x)/x → 0` (PNT porté) ; `R(C_k)/C_k → 0` ; `|v_k R(C_k)|/C_k^{3/2} → 0` |

## Expérience (a) — `scripts/e447a_line_break.py`, premiers ≤ 10⁷, `β = 1/2`, 7 hauteurs (log `logs/e447a_log.txt`)
| rang | T | cellules ≥ 10³ | Abel : résidu relatif max | télescopage | amplitude : erreur rel. max | violations des bornes | min/max de `|v_k|‖·‖/√q` | `e^{−π/(2T)}` |
|---|---|---|---|---|---|---|---|---|
| 1 | 14,13 | 41 | (aucun bloc de 50) | — | 2,9·10⁻¹⁵ | 0 / 100 000 | 0,8948 / 1,0000 | 0,8948 |
| 10 | 49,77 | 145 | 2,9·10⁻¹⁵ | 0 | 3,0·10⁻¹⁵ | 0 | 0,9689 / 1,0000 | 0,9689 |
| 100 | 236,5 | 692 | 4,0·10⁻¹⁵ | 0 | 3,2·10⁻¹⁵ | 0 | 0,9934 / 1,0000 | 0,9934 |
| 1 000 | 1 419 | 4 160 | 3,1·10⁻¹⁵ | 0 | 3,1·10⁻¹⁵ | 0 | 0,9989 / 1,0000 | 0,9989 |
| 10 000 | 9 878 | 28 958 | 5,0·10⁻¹⁵ | 0 | 3,4·10⁻¹⁵ | 0 | 0,9998 / 1,0000 | 0,9998 |
| 100 000 | 74 921 | 219 648 | 2,0·10⁻¹⁵ | 0 | 3,4·10⁻¹⁵ | 0 | 1,0000 / 1,0000 | 1,0000 |
| 2 000 000 | 1,13·10⁶ | 3 318 569 | 4,2·10⁻¹⁵ | 0 | 3,6·10⁻¹⁵ | 0 | 1,0000 / 1,0000 | 1,0000 |

`max |v_k R(C_k)| / C_k^{3/2}` par décade de `C_k` (et `max |R(C_k)|/C_k`, indépendant de `T` au premier ordre) :
| rang | 10³ | 10⁴ | 10⁵ | 10⁶ | `max |R|/C` 10³ → 10⁶ |
|---|---|---|---|---|---|
| 1 | 4,5·10⁻⁴ | 2,0·10⁻⁴ | 5,4·10⁻⁵ | 2,5·10⁻⁵ | 6,3·10⁻³ → 3,5·10⁻⁴ |
| 100 | 8,3·10⁻⁵ | 1,8·10⁻⁵ | 5,8·10⁻⁶ | 2,2·10⁻⁶ | 2,0·10⁻² → 5,1·10⁻⁴ |
| 10 000 | 2,2·10⁻⁶ | 6,4·10⁻⁷ | 1,5·10⁻⁷ | 5,9·10⁻⁸ | 2,1·10⁻² → 5,8·10⁻⁴ |
| 2 000 000 | 1,9·10⁻⁸ | 5,8·10⁻⁹ | 1,3·10⁻⁹ | 5,4·10⁻¹⁰ | 2,1·10⁻² → 6,1·10⁻⁴ |
(le facteur `1/‖(1/2,T)‖` explique la dépendance en `T` ; la décroissance par décade est celle de `|R|/C`).

Cassure puis descente (`break_then_descent`) sur les cellules à exactement un poids, premier : 0 cellule pour `T = 14,13`
et `49,8` (cellules plus longues que les écarts sous 10⁷), 8 pour 236,5, 427 pour 1 419, 3 809 pour 9 878, 29 010 pour
74 921, 366 644 pour 1,13·10⁶ (200 000 vérifiées) ; erreur absolue max de 1,2·10⁻¹³ à 9,3·10⁻¹⁰ (flottant sur `q ~ 10⁷`) ;
inégalité stricte `C_k < q` vraie partout.

## Jumeau (b) — `scripts/e447b_twin_mpmath.py`, mpmath 30 chiffres, sympy ≤ 10⁶ (log `logs/e447b_log.txt`)
Rangs 1, 100, 10 000 : résidus d'Abel ≤ 1,2·10⁻³⁰, erreur d'amplitude ≤ 1,4·10⁻³⁰, 0 violation, cassure-puis-descente
≤ 2,0·10⁻²⁸ sur 8 (rang 100, même compte que numpy) et 300 cellules ; `all_ok = True`.

## Verdict : A
Toutes les identités compilées sont exactes au flottant près et au jumeau ; l'encadrement de l'amplitude est atteint
exactement (le minimum observé coïncide avec `e^{−π/(2T)}` à quatre décimales) ; la demande pondérée aux contacts décroît
par décade. H1–H5 confirmées par le compilateur puis par le nombre.

## Ce que cela établit sur le mécanisme de cassure (ligne, aucune conclusion sur les OFF)
1. La cassure `log q` est payée par la Tour de la ligne avec l'amplitude exacte `√q · e^{−π f/(2T)} / ‖(1/2,T)‖`, `f` étant la
   fraction de cellule au point `q` : l'amplitude de paiement dépend de `q` par `√q` et de la position de `q` dans sa cellule
   par un facteur compris strictement entre `e^{−π/(2T)}` et 1 ; aux grandes hauteurs ce facteur est 1 à `10⁻⁶` près.
2. Le budget pondéré d'un bloc n'est pas une somme sur les cellules mais une somme sur la demande brute AUX CONTACTS,
   avec le facteur `(1 + e^{π/(2T)})` et deux termes de bord (bilan d'Abel) ; sur la ligne le carré de la valeur au contact
   est l'abscisse du contact (règle du carré).
3. Dans une cellule à un seul poids, la demande brute monte de `log q` d'un coup puis descend linéairement ; le corpus
   sait que la demande brute aux contacts est `o(C)` et que sa version pondérée est `o(C^{3/2})` (PNT porté).
