# E416 — Independent reconstruction of the prime gaps (pre-registered on 2026-11-03)

> Français : [README.fr.md](README.fr.md)

**Question.** From the spectral weights Λ̂_H(n) of E415 (channels A and B), without the list of primes, without the gaps,
without fitted correction, does one obtain the sequence of events, primes and gaps?

**Pre-registered reading rule (no empirical threshold).** For each n, the admissible set of Λ(n) without arithmetic data
is {0, log n} ∪ {log n / k : k ≥ 2, n = m^k exactly} (exact-power test on n alone). The closest
admissible value to Λ̂_H(n) decides: 0 → no event; log n → prime event; log n / k → power.
This is the arithmetic operator `reconstructedPrimeEvent N := Λ̂(N) = log N` of `Terminal/RawEventReconstruction.lean`
(`vonMangoldt_eq_log_iff`), made robust to truncation by the nearest neighbor. No parameter is fitted.

**Measures.** events found / false / missed; primes found / false / missed; exact consecutive gaps
(prefix before the first divergence); sum of absolute errors; first divergence; evolution with the number of
zeros; influence of precision (E414); sensitivity to high frequencies (E417).

**Results.** `RESULTS.md`, `data/e416_results.json`, `data/e416_W*_{A,B}_sequences.txt`, `logs/e416.log`.
