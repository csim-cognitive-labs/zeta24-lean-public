# E416 — résultats (exécutée le 2026-11-03, `logs/e416.log`, `data/e416_results.json`, `data/e416_W*_{A,B}_sequences.txt`)

Règle pré-enregistrée (plus proche valeur admissible), aucun seuil ajusté, premiers réels consultés après coup.

## W1 = [3, 300] : 78 événements (61 premiers + 17 puissances), 60 écarts

| Zéros | canal | événements ok / faux / manqués | premiers ok / faux / manqués | écarts exacts (préfixe) | 1re divergence | Σ|Δg| |
|---|---|---|---|---|---|---|
| 3 | A = B | 17 / 4 / 61 | 5 / 3 / 56 | 3 / 60 | rang 3 | 11 |
| 10 | A = B | 24 / 4 / 54 | 10 / 1 / 51 | 7 / 60 | rang 7 | 15 |
| 40 | A ; B | 32 / 6 / 46 ; 33 / 6 / 45 | 20 / 4 / 41 | 15 / 60 | rang 15 | 19 |
| 100 | A ; B | 48 / 8 / 30 ; 46 / 9 / 32 | 36 / 7 / 25 ; 35 / 7 / 26 | 30 / 60 | rang 30 | 74 ; 90 |
| 300 | A ; B | 73 / 4 / 5 ; 74 / 4 / 4 | 58 / 3 / 3 | 50 / 60 | rang 50 | 6 |
| ≥ 1 000 | A et B | 78 / 0 / 0 | 61 / 0 / 0 | **60 / 60** | aucune | 0 |

## W2 = [10000, 10060] (4 premiers, 3 écarts) et W3 = [100000, 100030] (2 premiers, 1 écart)

| Zéros | W2 premiers ok / faux / manqués | W2 écarts exacts | W3 premiers ok / faux / manqués | W3 écarts exacts |
|---|---|---|---|---|
| ≤ 5 000 | 0 / 0 / 4 | 0 / 3 | 0 / 0 / 2 | 0 / 1 |
| 10 000 | 0 / 2 / 4 (Σ|Δg| = 28) | 0 / 3 | 0 / 0 / 2 | 0 / 1 |
| 100 000 | 4 / 0 / 0 | 3 / 3 | 0 / 0 / 2 (1 faux événement) | 0 / 1 |
| ≥ 1 000 000 | 4 / 0 / 0 | 3 / 3 | 2 / 0 / 0 | 1 / 1 |

## Lectures
- **Niveau 4 et niveau 5 atteints à troncature finie, sur les fenêtres testées** : tous les écarts de W1 (60), W2 (3) et W3 (1)
  sont reconstruits exactement, sans que le premier suivant soit fourni, dès 1 000 zéros (W1), 100 000 (W2), 1 000 000 (W3).
  Théorèmes Lean correspondants (limite infinie) : `reconstructedPrimeGap_eq_actualGap`,
  `contact_accumulation_reconstructs_prime_gaps`.
- Ce résultat **dépend de la troncature** (il faut T_max ≳ πx) ; il n'est pas annoncé comme « reconstruction exacte » au-delà
  des fenêtres et troncatures mesurées. Il ne dépend d'aucun seuil empirique.
- Premières divergences aux petites troncatures : rang 3 (3 zéros), 7 (10), 15 (40), 30 (100), 50 (300) sur W1 : la portée
  lisible croît avec T_max.
- Évolution avec la précision : E414 montre que l'arrondi float64 est 10 ordres sous la plus petite erreur de troncature.
