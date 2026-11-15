# E427 — résultats (exécutée le 2026-11-04 ; `logs/e427{a,b,c}.log`, `data/e427{a,b,c}_results.json`)

Pré-enregistrement : `README.md` (commit d2e86049 (6331004d avant rebasage sur deux suppressions distantes sans rapport), avant exécution). Aucun critère modifié après exécution. Module Lean
compilé avant exécution : `Terminal/GrammarContactStability.lean` (trois tentatives journalisées ; la troisième corrige un
`congr 1` manquant, erreur de tactique, aucun énoncé changé).

## E427(a) — grammaire de référence exacte (entiers, 4 s)

| Mesure | Valeur | Nature |
|---|---|---|
| premiers > 3 jusqu'à 10⁸ | 5 761 453 | donnée |
| conformité classe ⟷ états (0 / 4 / 2) | 0 violation | identité (`transitionOf_cls`) |
| transitions t11 / t15 / t51 / t55 | 1 264 047 / 1 616 470 / 1 616 470 / 1 264 465 | mesure |
| bilan orienté cumulé : télescopage | 0 violation ; valeurs {−1 : 2 880 517 ; 0 : 2 880 935 ; +1 : 0} | identité (`orientedBalance_telescopes`) |
| confinement | min −1, max 0 | identité (`orientedBalance_abs_le_one`) |
| croisements, alternance, retour | 3 232 940 ; 0 ; 0 violation | identités (`exists_t51_between`, `crossings_cancel_*`) |
| maintiens entre deux croisements inverses | médiane 0, q99 5, max 15 | mesure |
| N11 − N55 cumulé | final −418, min −1 019, max 0 | mesure (non borné, biais de Chebyshev ; aucune loi) |
| identité séjours = occupation − orientation | écart max 0 | identité (`dwell_balance_eq_occupancy_minus_orientation`) |
| mots valides de douze transitions (énumération 4¹²) | 8 192 | identité (`card_validWords_twelve`) |
| mots de douze transitions réalisés par les premiers ≤ 10⁸ | 8 192 / 8 192 | mesure (aucune propriété attribuée) |
| jumeau (crible indépendant, entiers purs, ≤ 10⁶) | accord exact sur 6 comptes | jumeau |

Le bilan ne vaut jamais +1 parce que le premier premier > 3 est 5 (état 5, indicatrice 0) : bilan = 0 − indicatrice de
l'état courant. Le confinement n'affirme rien sur N11 − N55, qui atteint −1 019 (compilé : `confinement_not_dwell_equality`).

## E427(b) — niveau 1 : la grammaire reconstruite depuis les Tours (210 s)

Recalcul des canaux A (brut) et B (intégré) depuis les 2 001 052 zéros : identique bit à bit aux fichiers d'E415 (écart 0).

| Fenêtre | zéros | premiers reconstruits / vrais | états, transitions, bilans : désaccords | exact |
|---|---|---|---|---|
| W1 [3, 300] | 1 000 … 2 001 052 (A et B) | 61 / 61 | 0, 0, 0 | **oui** (10 configurations) |
| W2 [10 000, 10 060] | 1 000, 5 000 | 0 / 4 | — | non (aucun événement lu) |
| W2 | 100 000 … 2 001 052 | 4 / 4 | 0, 0, 0 | **oui** |
| W3 [100 000, 100 030] | ≤ 100 000 | 0 / 2 | — | non |
| W3 | 10⁶, 2 001 052 | 2 / 2 | 0, 0, 0 | **oui** |

Les deux états : sur W1 le seul premier reconstruit hors des deux états est 3 lui-même (rang 0 de la suite reconstruite,
exclu dans le module par `reconstructedState_goodMod6 (k ≥ 1)`) ; tous les autres premiers reconstruits sont ≡ ±1 (mod 6).

**Route par contacts authentiques** (W1, 1 000 zéros, canal brut) : 1 203 820 contacts, accumulation de chaque Tour sur ses
propres contacts dans chaque [n − ½, n + ½] ; écart maximal à la différence des valeurs aux bords 5,6·10⁻¹⁴ (relatif
3,5·10⁻¹¹) ; grammaire reconstruite exacte (61 premiers, 0 désaccord). C'est l'identité compilée
`contact_accumulation_eq_endpoint_difference` : les contacts sont le découpage de l'accumulation, pas une information
supplémentaire.

**Contrôles de séparation** (W1) :

| Famille | zéros | premiers reconstruits / vrais | hors des deux états | exact |
|---|---|---|---|---|
| mêmes hauteurs, β = 0,3 | 1 000 | 47 / 61 | seulement 3 | non (14 manqués, 12 désaccords d'états) |
| mêmes hauteurs, β = 0,3 | 2 001 052 | 32 / 61 | seulement 3 | non (29 manqués) |
| hauteurs pseudo-aléatoires de même densité, β = ½ | 1 000 | 62 / 61 | 3, 4, 6, 10, 14, 15, 18, 24, 28, … | non (28 désaccords d'états) |
| idem | 2 001 052 | 69 / 61 | 3, 8, 12, 16, 20, 26, 27, 39, 40, … | non (28 désaccords d'états) |

Distances minimales des hauteurs synthétiques aux zéros réels : 1,4·10⁻³ et 1,3·10⁻⁷ (jamais une hauteur réelle). Sur
les familles synthétiques, raccord, confinement et retour restent vrais (identités sur toute suite d'entiers), mais les
états eux-mêmes sont faux : la grammaire n'est retrouvée qu'avec les zéros authentiques.

Jumeau mpmath (30 chiffres, H = 1 000, n ∈ {3, 5, 7, 97, 101}) : écart maximal 2,3·10⁻¹³.

**Verdict niveau 1 : réussi** aux conditions pré-enregistrées (0 désaccord à troncature complète sur W1–W3 ; échec des
deux contrôles de séparation). La reconstruction est celle de la formule explicite lissée compilée (collectif des Tours) ;
elle dépend de la troncature (T_max ≳ πx, E416) ; les contacts y entrent comme découpage.

## E427(c) — niveau 2 : transport de l'équilibre aux contacts (1,3 s)

2 000 événements (5 ≤ p ≤ 17 393 ; 614 t15, 614 t51, 772 maintiens) ; 8 Tours authentiques (β = ½) et 16 Tours de
séparation (mêmes hauteurs, β = 0,3 et 0,7).

| Mesure | Valeur (toutes Tours) | Nature |
|---|---|---|
| bilan pondéré par les valeurs aux contacts contre la borne d'Abel (fenêtres 12 et 120) | 0 violation sur 1 989 + 1 881 fenêtres × 24 Tours ; rapport médian 0,28–0,54 (12), 0,09–0,49 (120) | identité (`contact_weighted_balance_abs_le`) |
| transport exact (candidat = f(orientation)) : décalage d'indice de contact Δk | faux : à orientation fixée, Δk s'étale de 41 à 162 933 (T = 1,13·10⁶) | mesure, attendu compilé |
| idem : variation de log-amplitude β·log(p'/p) | faux : étendue 0,17 / 0,12 / 0,23 par orientation | mesure, attendu compilé (`logRatio_not_determined_by_transition`) |
| idem : valeur réelle signée au contact de rencontre | faux | mesure |
| information mutuelle orientation ⟷ Δk | 0,000 (T = 14) → 0,151 bits (T ≥ 7,5·10⁴) | mesure |
| information mutuelle orientation ⟷ β·log(p'/p) | 0,149 bits, identique pour toutes les Tours | mesure |
| information mutuelle orientation ⟷ écart ; ⟷ écart mod 6 | 1,372 ; 0,962 bits | référence (`eventOrientation_of_gap`) |
| dérive d'amplitude relative neutre, segments de bilan nul / de bilan ±1, β = ½ | 100 % / 100 % (1 227 et 507 segments) | identité (`meeting_drift_eq_one_iff`) |
| idem, β = 0,3 et 0,7 | 0 % / 0 % | identité (`return_drift_eq_one_iff`) |
| jumeau mpmath (Tour du zéro 1, 10 événements) | indices identiques, écart 1,7·10⁻¹⁶ | jumeau |

Lecture. L'information mutuelle orientation ⟷ Δk croît avec la hauteur parce que Δk ≈ T·log(p'/p)/π résout l'écart dès que
T dépasse π·p : c'est l'écart (donc son résidu) qui est lu, par la fréquence seule, identiquement pour β = 0,3, 0,5, 0,7.
Aucune grandeur géométrique mesurée n'est une fonction de l'orientation. La dérive d'amplitude est neutre sur tous les
segments à β = ½ et sur aucun à β ≠ ½, que le bilan soit revenu à zéro ou non : le retour du bilan n'a aucun effet
géométrique ; la neutralité est une propriété de la ligne, pas de la grammaire.

**Verdict niveau 2 : négatif** — aucun transport de l'orientation vers une grandeur des contacts ; le seul énoncé compilé
reliant orientation et contacts est une somme d'Abel (identité valable pour tout (β, T)).

**Niveau 3 :** rien cherché, rien lu ; aucune contrainte sur β. RH non démontrée ; rien n'exclut un zéro OFF.
