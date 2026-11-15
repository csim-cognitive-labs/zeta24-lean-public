# E416 — Reconstruction indépendante des écarts premiers (pré-enregistrée le 2026-11-03)

**Question.** À partir des poids spectraux Λ̂_H(n) d'E415 (canaux A et B), sans la liste des premiers, sans les écarts,
sans correction ajustée, obtient-on la suite des événements, des premiers et des écarts ?

**Règle de lecture pré-enregistrée (sans seuil empirique).** Pour chaque n, l'ensemble admissible de Λ(n) sans donnée
arithmétique est {0, log n} ∪ {log n / k : k ≥ 2, n = m^k exactement} (test de puissance exacte sur n seul). La valeur
admissible la plus proche de Λ̂_H(n) décide : 0 → aucun événement ; log n → événement premier ; log n / k → puissance.
C'est l'opérateur arithmétique `reconstructedPrimeEvent N := Λ̂(N) = log N` de `Terminal/RawEventReconstruction.lean`
(`vonMangoldt_eq_log_iff`), rendu robuste à la troncature par le plus proche voisin. Aucun paramètre n'est ajusté.

**Mesures.** événements retrouvés / faux / manqués ; premiers retrouvés / faux / manqués ; écarts consécutifs exacts
(préfixe avant première divergence) ; somme des erreurs absolues ; première divergence ; évolution avec le nombre de
zéros ; influence de la précision (E414) ; sensibilité aux hautes fréquences (E417).

**Résultats.** `RESULTS.md`, `data/e416_results.json`, `data/e416_W*_{A,B}_sequences.txt`, `logs/e416.log`.
