# E474 — Tent, memory one, integral: four hypotheses closed by TDD (2026-11-13)

> Français : [README.fr.md](README.fr.md)

Author's order: "formulate hypotheses, at least 3 or 4, and use the compiler and experiments to close them by TDD".
Starting point: E473 (§19.106) compiled the local grammar `a_{k+1} − e^{π/T} a_k = L_k`, `L_k = ε_{k+1} + e^{π/T} η_k`, and concluded
honestly that no new bounding obligation had been found. Here each hypothesis is first a TEST (numerical threshold,
pre-written), then the twin makes it pass or fail on the real primes, then the compiler closes what the twin supports.

## Strategy (R-Ψ)
Cumulative doctrine unchanged: OFF → Tower → contacts/amplitudes → price → arithmetic collective budget → contradiction. Single target
(§19.105): `arithmeticAlternatingBudget T x N / x_N^{3/2}` bounded. E473 reduced the target to the local term `L_k` over two consecutive
cells. E474 looks for the EXACT ARITHMETIC FORM of `L_k` (hypothesis 1: sum of the primes against a tent), its MEMORY STRUCTURE
(hypothesis 2: memory one), its SCALING LAW in the height (hypothesis 3) and its CONTROL BY THE DEMAND INTERIOR TO THE
CELL (hypothesis 4, integral representation). Every compiled bound has explicit antecedents; nothing is admitted; R-RH: an
antecedent of RH strength is neither an objection nor a brake, only its admission as a premise is forbidden. Never "frontier".

## The four hypotheses (pre-written tests)
**H1 — tent identity.** `L_k = Σ_{n ∈ (C_k, C_{k+2}]} Λ(n)·tent_k(n) − e^{π/T}(1+e^{π/T}) ℓ_k²/2`, where `tent_k(n) =
min(e^{π/T}(n − C_k), C_{k+2} − n)` is the continuous hat function with apex `C_{k+1}`, height `ℓ_{k+1}`. The local term is the
discrepancy of the sum of the primes against an exact hat kernel (integral of the tent = `e^{π/T}(1+e^{π/T})ℓ_k²/2`).
Twin test: residual / ℓ_k² < 1e-10 on all cells. Compilation: theorem (module 1).

**H2 — memory one.** `L_k = ε_{k+1} − e^{π/T} ε_k + e^{π/T} ℓ_k Δ_k` with `Δ_k = rawDemand C_{k+1} − rawDemand C_k` (identity, module 1).
Measurable prediction (reasoning on the zeros side, NOT compiled): the cells of Tower no. 1 are half-periods of the
dominant oscillation, hence neighbouring local terms oppose each other; for a high Tower the cells are fine relative to the low oscillations,
hence neighbouring local terms follow each other. Twin test: lag-1 autocorrelation of `L_k/C_k^{3/2}`: Tower 1 < −0.2;
Tower 1000 > +0.2; and for every Tower |corr(lag j)| decreases from j = 1 to j = 5 (not strictly, tolerance 0.05).

**H3 — scaling law in 1/T.** `T · |L_k| / C_k^{3/2} ≤ 3` on all cells of all tested Towers (zeros no. 1, 2, 3, 5,
10, 20, 50, 100, 200, 500, 1000, 2000, 5000; `10^3 ≤ C_k`, `C_{k+2} ≤ 3·10^7`). Targeted compiled explanation (module 2):
`|L_k| ≤ 2 e^{π/T} ℓ_k · M_k` where `M_k` bounds `|rawDemand|` on the two cells, and `ℓ_k = (e^{π/T} − 1) C_k` with
`T(e^{π/T} − 1) → π`: the law in 1/T ⟸ demand at scale `√x`. Twin test: inequality verified numerically on each cell
(sanity) and ratio `|L_k| / (2 e^{π/T} ℓ_k M_k)` measured (tightness).

**H4 — control interior to the cell.** `ε_k = ∫_{C_k}^{C_{k+1}} (rawDemand t − rawDemand C_k) dt` (module 2: `demandArea` IS
the integral of `rawDemand`, by the Abel summation of Mathlib); hence `|ε_k| ≤ ℓ_k · V_k` where `V_k` bounds the variation of the demand
inside the cell. Twin tests: (a) `|ε_k| / (ℓ_k √C_k) ≤ 3` and `|Δ_k| / √C_k ≤ 3` on all cells; (b) the two
parts of H2 (`ε_{k+1} − e^{π/T} ε_k` and `e^{π/T} ℓ_k Δ_k`) are of the same order: ratio of their root-mean-squares in [1/3, 3].

## Targeted conditional closure (module 2, explicit antecedent)
If `|rawDemand t| ≤ M` on the window `(C_{k₀}, C_{k₀+N+1}]`, then `(1+e^{π/T}) |A_N| ≤ M (1+e^{π/T})² C_{k₀+N}`: the budget at
the scale `x_N` is controlled by the supremum of the demand on the window, with explicit constant; alternation plays no role in it.
Reading drawn (not compiled): budget at the scale of the line ⟸ demand in `√x·(log x)²` on the window (RH strength, R-RH).
We do NOT claim that this reduction is a new obligation: it is the shortest form of the same antecedent.

## Phase A — isolated modules (never added to `RHV6Fresh.lean`), two attempts maximum each, log in `attempts/`
* Module 1 `Terminal/CellAreaTent.lean`: `tentKernel`, `localGrammarTerm_eq_tent_sum` (H1), `localGrammarTerm_eq_memory_one` (H2),
  `alternating_local_eq_exit_form` (alternating sum of the local terms written on the exit deviations and the variations of the demand),
  `tent_integral_eq`, `tentKernel_nonneg`, `tentKernel_le`.
* Module 2 `Terminal/CellAreaIntegral.lean`: `integral_psi_eq`, `demandArea_eq_integral`, `abs_demandArea_le_of_bound`,
  `exitDeviation_eq_integral`, `abs_exitDeviation_le_of_variation`, `abs_localGrammarTerm_le_of_demand_bound`, `sum_cellLength_eq`,
  `budget_le_of_demand_bound`.

## Phase B — twin `twin_e474.py` (nohup, bounded), real primes ≤ 3·10^7, real contacts (β = 1/2), cell formula (R-Ψ quater)
Outputs: `twin_results.json`, `logs_twin_run.txt`.

## Verdicts
A: H1 to 1e-10, compiled inequalities verified numerically, H2/H3/H4 all passed. B: identities conforming, at least one quantitative
threshold (H2, H3, H4) fails — recorded as is, that is the result. C: an identity (H1 or the inequality of H3) fails → definition
error, to be sought before any compilation.
