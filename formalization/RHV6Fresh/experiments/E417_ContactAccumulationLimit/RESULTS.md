# E417 — résultats (exécutée le 2026-11-03, 223 s, `logs/e417.log`, `data/e417_results.json`, `data/profile_p*_H*.npy`)

## 1. Transitions du canal brut ψ̂₀_H autour d'un premier p (largeur 10–90 % du saut log p, en unités de x)

| p | H | zéros | largeur mesurée | πp/T_max | rapport | dépassement (+ / −) | rms hors 3 échelles |
|---|---|---|---|---|---|---|---|
| 101 | 10³ | 649 | 0,2615 | 0,3174 | 0,82 | +0,068 / −0,114 | — |
| 101 | 10⁴ | 10 142 | 0,0290 | 0,0317 | 0,91 | +0,089 / −0,090 | 0,048 |
| 101 | 10⁵ | 138 069 | 0,0030 | 0,0032 | 0,95 | +0,088 / −0,088 | 0,015 |
| 101 | 10⁶ | 1 747 146 | ≤ 0,005 (pas de grille) | 0,00032 | — | +0,002 / −0,002 (sous-résolu) | 0,0044 |
| 101 | γ_max | 2 001 052 | ≤ 0,005 (pas de grille) | 0,00028 | — | +0,011 / −0,011 (sous-résolu) | 0,0042 |
| 1009 | 10⁴ | 10 142 | 0,2825 | 0,3170 | 0,89 | +0,093 / −0,086 | — |
| 1009 | 10⁵ | 138 069 | 0,0290 | 0,0317 | 0,92 | +0,088 / −0,091 | 0,072 |
| 1009 | 10⁶ | 1 747 146 | ≤ 0,005 (pas de grille) | 0,0032 | — | +0,064 / −0,064 (sous-résolu) | 0,026 |
| 1009 | γ_max | 2 001 052 | ≤ 0,005 | 0,0028 | — | +0,083 / −0,083 | 0,017 |
| 10007 | 10⁵ | 138 069 | 0,2690 | 0,3144 | 0,86 | +0,082 / −0,097 | — |
| 10007 | 10⁶ | 1 747 146 | 0,0300 | 0,0314 | 0,95 | +0,089 / −0,090 | 0,097 |
| 10007 | γ_max | 2 001 052 | 0,0250 | 0,0278 | 0,90 | +0,088 / −0,091 | 0,089 |

- Lorsque la grille résout la transition (8 cas), la largeur 10–90 % vaut 0,82 à 0,95 fois πp/T_max : **l'échelle πx/T_max décrit
  la largeur observée** (vérifiée, non supposée). Les cas marqués « pas de grille » ont une transition plus fine que le pas de
  la grille (0,0025 pour 401 points) : largeur bornée par la résolution, dépassement sous-résolu ; ils ne contredisent pas
  l'échelle. Pour p = 1009 à H = 10³ et p = 10007 à H ≤ 10⁴, l'échelle dépasse la fenêtre : pas de transition.
- **Dépassement de Gibbs constant ≈ 0,09 du saut** (+0,082 à +0,093 ; −0,086 à −0,097) dès que la transition est résolue,
  indépendant de H : c'est le phénomène de Gibbs classique (≈ 8,9 %) ; il ne décroît pas avec T_max (E332, E404 confirmés).
- La cassure n'est donc jamais « reconstruite exactement » au point de saut par le canal brut tronqué : elle est localisée
  à ± πx/T_max près avec un dépassement fixe. Le canal intégré n'a pas de Gibbs (seconde différence d'une série absolument
  convergente), au prix d'une lecture aux entiers seulement.

## 2. Convergence hors / aux événements (W1, depuis E415)

| Zéros | T_max | A rms événements / hors | B rms événements / hors | B_rms·T_max | A_rms·√T_max |
|---|---|---|---|---|---|
| 1 000 | 1 419 | 0,471 / 0,238 | 0,325 / 0,152 | 300 | 11,9 |
| 5 000 | 5 448 | 0,138 / 0,070 | 0,0912 / 0,0433 | 325 | 6,8 |
| 10 000 | 9 878 | 0,068 / 0,037 | 0,0498 / 0,0235 | 321 | 4,7 |
| 100 000 | 74 921 | 0,0088 / 0,0048 | 6,6e−3 / 3,1e−3 | 323 | 1,67 |
| 1 000 000 | 600 270 | 7e−4 / 6e−4 | 8,2e−4 / 3,9e−4 | 323 | 0,48 |
| 2 001 052 | 1 132 491 | 4e−4 / 3e−4 | 4,4e−4 / 2,1e−4 | 323 | 0,36 |

- Canal intégré : erreur rms exactement proportionnelle à 1/T_max (produit constant 323 sur trois décades) ; aux événements
  l'erreur est le double de celle hors événements (la seconde différence lit un saut).
- Canal brut aux demi-entiers : décroissance plus rapide que 1/√T_max (A·√T décroît) mais moins régulière.
- **Précision nécessaire** (E416) : plus petite troncature rendant tous les écarts de W1 exacts : 1 000 zéros, pour A comme pour B.
