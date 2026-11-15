# E451 — Résultats (2026-11-08) : la Tour est le terme du zéro ; pont « zéro vrai → objets d'E450 » (K2a)

**Verdict A.** Module isolé `Terminal/PairBreakOfZero.lean`, import `PairBreakAtPrime` seul (sa clôture de 259 modules
contient déjà `Foundation/ZetaReflect`, `Direct/MirrorCount`, `ExplicitFormulaLink` ; aucun import nouveau). Quatorze
déclarations (onze énoncés L1–L6 et trois lemmes de positivité), **tentative de compilation 1 verte** (9093 travaux,
`attempts/build_attempt1.txt`) ; axiomes standards seuls (`attempts/axioms_attempt1.txt`) ; grep du ban : 0 occurrence ;
`lake build RHV6Fresh` complet vert (`logs/lake_build_full.txt`). Sondes : `attempts/probe1–4.txt` (probe1–2 : espaces de
noms `RHV3Lean` non ouverts ; probe3 : une réécriture `rpow_sub` appliquée au mauvais membre ; probe4 : verte).

## Énoncés compilés
* L1 `zeroMult_eq_zero_iff (hρ : ρ ≠ 1) : zeroMult ρ = 0 ↔ riemannZeta ρ ≠ 0` — **hors zéro, la Tour n'existe pas** ;
  `one_le_zeroMult_zeroPoint z : 1 ≤ zeroMult (zeroPoint z)` ; `zeroContribution_eq_zeroMult_mul` (preuve `rfl`).
* L2 `zeroMult_mirrorMember : zeroMult (zeroPoint (mirrorMember z)) = zeroMult (zeroPoint z)` ;
  `mirrorMember_ne_self_of_off (hβ : β ≠ 1/2) : mirrorMember z ≠ z`.
* L3 `zero_break_amplitude_exact z hx : |v_β(k_β(x))| = ‖zeroTerm z x‖ · e^{−βπ f/T}`.
* L4 `zero_mirror_word_difference_le_one z x`.
* L5 `zero_pair_term_product z hx : ‖zeroTerm z x‖ ‖zeroTerm z* x‖ = x/(‖ρ‖‖ρ*‖)` ; `zero_pair_weighted_product` : `m² ·` idem.
* L6 `zero_pair_term_ratio z hx : = x^{2β−1} ‖ρ*‖/‖ρ‖` ; `zero_pair_term_ratio_unbounded (hβ : 1/2 < β) K : ∀ᶠ x, K < ratio`.

## Expérience (a) — le calcul de zêta (`scripts/e451a_zeta_weight.py`, mpmath 30 chiffres, `logs/e451a_log.txt`)
| point | hauteur | module de zêta | module de la dérivée | dérivée × 10⁻⁹ |
|---|---|---|---|---|
| zéro rang 1 | 14,134725142 | 2,1·10⁻¹⁰ | 0,79 | 7,9·10⁻¹⁰ |
| zéro rang 10 | 49,773832478 | 4,6·10⁻¹⁰ | 1,42 | 1,4·10⁻⁹ |
| zéro rang 100 | 236,524229666 | 7,3·10⁻¹⁰ | 4,00 | 4,0·10⁻⁹ |
| zéro rang 1000 | 1419,422480946 | 1,2·10⁻¹¹ | 2,78 | 2,8·10⁻⁹ |
| zéro rang 10000 | 9877,782654004 | 1,3·10⁻⁸ | 8,69 | 8,7·10⁻⁹ |
| zéro rang 100000 | 74920,827498994 | 4,1·10⁻⁹ | 21,8 | 2,2·10⁻⁸ |
| contrôle milieu 1–2 | 17,578382390 | 2,32 | 1,20 | — |
| contrôle milieu 100–101 | 237,147025074 | 1,20 | 2,19 | — |
| contrôle milieu 10000–10001 | 9878,218713194 | 1,66 | 6,30 | — |

Lecture honnête : les hauteurs du fichier sont lues à neuf décimales ; aux six zéros, le module de zêta est de l'ordre de la
dérivée fois cette précision (critère consigné : au plus dix fois ce produit, satisfait partout, le pire étant le rang 10000 à
1,5 fois) ; aux trois contrôles, le module de zêta dépasse un. `all_ok = True`. Le calcul de zêta sépare donc les six Tours
de K0 (poids au moins un) des trois contrôles (poids nul : la Tour n'existe pas), ce qu'aucune statistique de contacts ne
faisait (E450, K0, H6).

## Expérience (b) — identités des termes (`scripts/e451b_zero_terms.py`, 10⁵ premiers sur 664 579, graine 451)
Vingt-quatre cas (six zéros en ligne, miroir = zéro ; trois paires OFF témoins par fréquence) : H3 erreur relative ≤ 3,5·10⁻¹⁵,
H4 zéro violation, H5 ≤ 1,4·10⁻¹⁵, H6 ≤ 1,4·10⁻¹⁵ ; rapport des modules à 10³…10⁶ : `1` en ligne ; `0,0628 / 0,0251 /
0,0100 / 0,00398` pour β = 0,3 (c'est `x^{−0,4}` ; l'inverse `x^{0,4}` pour le membre à 0,7), `0,251 / 0,158 / 0,100 /
0,0631` pour β = 0,4, `0,501 / 0,398 / 0,316 / 0,251` pour β = 0,45, identiques à toutes les fréquences. `all_ok = True`.
Ces identités ne dépendent pas de l'annulation de zêta ; seule la multiplicité en dépend, et elle n'est pas testée
numériquement (hors route : jamais de test direct des zéros ou des OFF).

## Ce que cela établit
Le chaînon manquant du §19.72 est fermé par le corpus et écrit dans la forme de la route : une Tour est le terme `x^ρ/ρ`
du point `ρ`, de poids l'ordre d'annulation de zêta en `ρ` ; ce poids vaut au moins un en un zéro vrai et exactement zéro
partout ailleurs hors du pôle ; le miroir d'un zéro OFF est une seconde Tour, distincte, de même poids, à la même fréquence.
Les objets d'E450 (cassure, mots, produit, rapport) au paramètre d'un zéro vrai sont le module de ce terme, à facteur de
cellule près ; le produit des deux modules est exactement `x/(‖ρ‖‖ρ*‖)` et le rapport exactement `x^{2β−1}‖ρ*‖/‖ρ‖`.
Aucune contradiction n'est tirée. **K2b** (à pré-enregistrer) : ce que la rencontre exacte impose aux deux termes de poids
égal au même premier, sans somme de Tours, après vérification de non-équivalence avec RH.
