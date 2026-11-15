# E415 — Reconstruction of the arithmetic weights from the spectral signal (pre-registered on 2026-11-03)

> Français : [README.fr.md](README.fr.md)

**Question.** Are the weights Λ(n) recovered from the zeros alone (and the analytic terms of the formula), without
access to arithmetic values, and with what error depending on truncation?

**Approaches compared.** A: raw channel at half-integers, Λ̂ᴬ_H(n) = ψ̂₀_H(n+½) − ψ̂₀_H(n−½) (premise `RawExplicitFormulaAt`,
not compiled). B: integrated channel, second difference Λ̂ᴮ_H(n) = ψ̂₁_H(n+1) − 2ψ̂₁_H(n) + ψ̂₁_H(n−1) (compiled theorem
`reconstructedVonMangoldt_eq`, limit `reconstructedVonMangoldt_eq_limit_contact_accumulation`). C: accumulation
by contacts with complex values (equal to D by telescoping, checked explicitly on 5000 zeros). D: direct spectral sum
(= B).

**Prohibitions.** Λ(n), the primes and the gaps enter no computation of Λ̂; they are loaded AFTER, for
validation only (`sieve_lambda`, marked VALIDATION). No method is selected based on the results.

**Results.** `RESULTS.md`, `data/e415_results.json`, `data/e415_W*_full.txt`, `data/lam{A,B}_W*.npy`, `logs/e415.log`.
