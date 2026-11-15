# E469 (Ψ3) — the asymmetry of the pair integrated over the primes — pre-registration (2026-11-13)

> Français : [README.fr.md](README.fr.md)

Module `Terminal/PairAsymmetryOverPrimes.lean` (isolated). Target H17 R3' validated by the author. Commit BEFORE compilation; two attempts.
## Strategy (rule R-Ψ)
* Target: the terms of the zero and of the mirror have the same cumulative weight over the series of the primes (⟺ line).
* Cumulative object: sum over the primes ≤ N of the logarithm of the ratio of the powers p^{1−β} and p^β = (1 − 2β) θ(N).
* Why the pointwise reading is not enough: at a prime the ratio is p^{1−2β} (E450), an identity true for every β.
* Expected signature of an off-line zero: unbounded cumulation, linear in the Chebyshev function; per prime, fraction |1 − 2β| ≤ 1 of the weight log p.
* Continuation in both outcomes: if everything compiles: write the primes side (the pair must be paid on ALL the primes) in Ψ4/Ψ6; otherwise record.
## Statements (A1–A5): see the header of the module.
## Twin (section Ψ3): exact cumulation over the primes ≤ 10^6 for β ∈ {0.3; 0.4; 0.45} against (1−2β)·θ(N) (equality to 10^-12);
linear growth in θ verified; zero at β = 1/2.
