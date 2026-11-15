# E472 — arithmetic budget separated from the background, complex contribution of the pair, natural sum against rectified signs, measurement on the real primes — pre-registration (2026-11-13)

> Français : [README.fr.md](README.fr.md)

Trigger: external audit of commit `882cb391` transmitted by the author (four reservations P1–P4, recommendation "E472 in two phases").
The four reservations were VERIFIED on the sources before this pre-registration:
* P1 `alternatingCellTotal_eq_demandAreas` contains `residualBackground`: the "budget read on the primes alone" was too strong.
* P2 `pairRelativeAlternating` is a SUM OF NORMS, not the norm of the sum: it forbids cancellation by definition.
* P3 `towerAlternatingSum` multiplies by `(−1)^n` shares whose cell factor is ALREADY negative: the ratio becomes `e^{π(1+β)/T} > 0`.
  It is a sum with RECTIFIED signs, not a cancellation by alternation; the natural sum had not been compared.
* P4 `pairAsymmetryAt` is definitional; `cumulativeAsymmetry = (1−2β)θ(N)` is a geometric measurement with no compiled bridge to a residual.

## Strategy (rule R-Ψ)
* Target: lift P1–P4 in Lean (phase A) BEFORE measuring (phase B), so that the measured quantity is exactly the one the single
  target of §19.101 must bound.
* Cumulative object: the cell series of Ψ4, separated into arithmetic budget (primes alone) + budget of the background; natural sums
  and sums with rectified signs of the Towers; complex contribution of the pair.
* Why the pointwise reading is not enough: unchanged (a cell cancels with nothing).
* Expected signature of an off-line zero: growth `e^{Nπ(β−1/2)/T}` of the COMPLEX contribution of the pair (norm of the sum),
  in the rectified form AND in the natural form.
* Continuation in both outcomes: if phase A compiles, phase B measures `arithmeticAlternatingBudget` on the real primes;
  if a statement does not compile in two attempts, record it as is (statement demanded) and still measure what is defined.

## Phase A — isolated module `Terminal/ArithmeticBudgetSeparation.lean` (imports Ψ4, Ψ3, RawMeetingRemainder)
Commit BEFORE compilation; at most two attempts, logs in `attempts/`. Statements B1–B4: see the header of the module.
Expected: (B1) `alternatingCellTotal = arithmeticAlternatingBudget − backgroundAlternatingBudget`, independence from the recomposition,
background bounded by `C(e+1)/(e−1)·x_N` hence `≤ C'/x_N^{1/2}` at the scale of the line; natural budget telescoped (background at both edges).
(B2) `‖towerAlternatingSum‖ = Σ‖parts‖`; `towerNaturalSum` telescoped, bracketed: `(g−1)/(g+1)·‖rectified‖ ≤ ‖natural‖ ≤ ‖rectified‖`;
same line / mirror classification. (B3) `‖S_β + S_{1−β}‖/x_N^{3/2}` unbounded for `β < 1/2`, `w' ≠ 0`, rectified and natural forms;
with the coefficient of the recomposition if the mirror is a carrier. (B4) `pairAsymmetryAt β p = log‖part'(p)‖ − log‖part(p)‖ − const`.

## Phase B — twin `twin_e472.py` (real primes up to 3·10^7, 2 001 052 zeros, closed forms)
Launch `nohup`, log `logs_twin_run.txt`, results `twin_results.json`. Towers: zeros no. 1, 2, 3, 5, 10, 20, 100, 1000;
`x_0 = 1000`; cells up to `x_N ≤ 3·10^7`.
Pre-registered measurements:
1. Twins of definitions: `demandArea` (cumulative form against direct sum) and `demandArea_add`: relative gap < 1e-8.
2. Primes-side telescoping of the natural budget (`Nat_N = demandArea(x_0, x_N)`): relative gap < 1e-8.
3. `A_N / x_N^{3/2}` (relative alternating arithmetic budget), `Nat_N / x_N^{3/2}`, `Σ|a_n| / x_N^{3/2}`: values reported, NO bound assumed.
4. Zeros side `Z_N` (closed forms, 1M and 2M zeros): residual `A_N − Z_N` reported relative to `x_N` (expected: under the compiled bound of the background
   `C(e+1)/(e−1)`) and to `x_N^{3/2}`; truncation `(Z_N^{2M} − Z_N^{1M})/x_N^{3/2}` reported separately.
5. Tower no. 1000, artificial pair `β ∈ {0.3; 0.4; 0.45}`: complex contribution (norm of the sum) AND sum of norms, defect relative to
   the line Tower, all relative to `x_N^{3/2}` and set against the residual and the truncation (separation requested by audit §4).
6. For each Tower: `‖natural‖/‖rectified‖ ∈ [(g−1)/(g+1), 1]` (twin of B2); fraction of cell areas that alternate in sign.
Verdicts: A = points 1, 2, 6 conforming and all values of points 3–5 reported; B = a point 1, 2 or 6 non-conforming (recorded);
C = execution impossible. No value of 3–5 can by itself produce a verdict: they are measurements, not theorems.
