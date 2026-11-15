# E422 — Collective sum of the real values at the contacts (pre-registered 2026-11-03)

> Français : [README.fr.md](README.fr.md)

Precise definition (fixed before execution). Family F = the first N zeros, placed on the line, with conjugates (factor 2·Re).
For a Tower ρ₀ ∈ F and one of its contacts x = C_k(ρ₀):
* own value: 2·v_k(ρ₀) = 2·(−1)^k C_k^β/|ρ₀| (real by construction, the conjugate gives the same value);
* contributions of the other Towers **evaluated at the same position x**: 2·Re(x^ρ/ρ) for ρ ∈ F ∖ {ρ₀}; these are values off
  contact in general (Im(x^ρ/ρ) ≠ 0), only the real part enters the sum (family stable under conjugation);
* collective sum S_F(x) = 2·v_k(ρ₀) + Σ_{ρ ≠ ρ₀} 2·Re(x^ρ/ρ) = Σ_{ρ ∈ F} 2·Re(x^ρ/ρ), evaluated at the contact positions.
No arithmetic function is used: the sums are compared with each other (share of the own value, sign, variation
with N), never to ψ, to the primes or to li.
Planned measures: S_F at the contacts of Towers 1, 2, 3, 100, 1000 in [100, 1000], for N ∈ {10, 100, 1,000, 10⁴, 10⁵, 2,001,052};
share |2v_k|/|S_F|; sign agreement between v_k and S_F; S_F − 2v_k (the others); phase of the other Towers at x (fraction of π);
variation of S_F between N and the next N at the same points. Control identity: S_F(C_{k+1}) − S_F(C_k) = Σ_ρ 2Re[F(C_{k+1}) − F(C_k)]
(telescoping, already compiled) is NOT re-measured.
