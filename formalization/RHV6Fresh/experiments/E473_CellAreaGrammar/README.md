# E473 — grammar of the areas between consecutive contacts: exact identity of the prime contributions, sign control, numerical stability, closure attempts — pre-registration (2026-11-13)

> Français : [README.fr.md](README.fr.md)

Trigger: decision of the author after E472 ("E472 is a better build than Ψ; launch E473 on the grammar of the areas between
consecutive contacts, priority to the exact identity of the prime contributions, to sign control and to numerical stability;
look for a truly new arithmetic obligation, not a reformulation of the final bound; really attempt closures").

## Strategy (rule R-Ψ)
* Target: write the area of the demand of a cell of a Tower (`cellArea β T k = demandArea C_k C_{k+1}`) with ONLY the primes
  crossed by the cell and the demand at the entry contact, then eliminate this demand (the entire history of the primes) by a
  recurrence between two consecutive cells: what remains is LOCAL (primes of the two cells, weighted by their distance to the
  contacts) and it is the object the arithmetic budget of E472 is made of.
* Cumulative object: the alternating arithmetic budget `arithmeticAlternatingBudget` of E472, read on the cells of a Tower (compiled bridge),
  rewritten by the recurrence as: first area + last area + alternating sum of the local terms (G3).
* Why the pointwise reading is not enough: unchanged; here the recurrence links TWO consecutive cells, the smallest unit where a
  relation between areas can exist.
* Expected signature of an off-line zero: unchanged (E472); the grammar does not modify it, it changes its reading: the bound of the
  budget is equivalent to the bound of the last area plus that of the alternating sum of the local terms (G6, conditional closure).
* Internal control not reported: the unconditional compiled closure is made at the scale `x_N^2` (PNT ported), the target is at the scale
  `x_N^{3/2}`; the difference of exponent is exactly what the primes must give.
* Continuation in both outcomes: if everything compiles, measure on the real primes the local terms and the transmission under sign
  change; if a statement does not compile in two attempts, record it as is and measure what is defined.

## Phase A — isolated module `Terminal/CellAreaGrammar.lean` (imports E472 `ArithmeticBudgetSeparation`, `BreakMechanismOnLine`)
Commit BEFORE compilation; at most two attempts, logs in `attempts/`. Statements G1–G6 (see the header of the module):
* G1 exact identity: `cellArea = cellDescentArea + cellExitWeight` (demand at the contact × length − half-square + prime weights weighted
  by the distance to the exit); `cellExitWeight + cellEntryWeight = cellWeight × cellLength`; positivity of the two weights;
  `exitDeviation = cellArea − entry demand × length`, `entryDeviation = exit demand × length − cellArea`.
* G2 local grammar: `cellArea (k+1) − e^{π/T} cellArea k = exitDeviation (k+1) + e^{π/T} entryDeviation k` (the demand at the contact,
  sole memory of the earlier primes, is ELIMINATED); sign bounds of the local term by the weights of the two cells; case without weight.
* G3 recurrence of the budget: `(1+e^{π/T}) A_{N+1} = a_0 + (−1)^N e^{π/T} a_N − Σ_{n<N} (−1)^n L_n`; bridge
  `arithmeticAlternatingBudget T (C_{k₀}) N = Σ (−1)^n cellArea (k₀+n)`.
* G4 sign control: if two consecutive areas have opposite signs, `|a_{k+1}| + e^{π/T}|a_k| ≤ |L_k|`; under alternation over
  a window, `|A_{N+1}| ≤ |a_0| + Σ |L_n|` (transmission from the local to the budget).
* G5 unconditional scale (PNT ported): `|cellArea| ≤ (1/2+ε) cellLength²` from a rank on; budget of a window
  `≤ (1/2+ε) e^{2π/T}/(e^{2π/T}−1) × (last length)²`: scale `x_N^2`.
* G6 conditional closures (EXPLICIT antecedents, nothing admitted): `(1+e^{π/T})|A_{N+1}| ≤ |a_0| + e^{π/T}|a_N| + Σ b_n` as soon as
  `|L_n| ≤ b_n`; form at the scale of the line with the geometric sum of the `C_k^{3/2}`.

## Phase B — twin `twin_e473.py` (real primes up to 3·10^7, Towers = zeros no. 1, 2, 3, 5, 10, 20, 100, 1000, β = 1/2)
Launch `nohup`, log `logs_twin_run.txt`, results `twin_results.json`. Cells `[C_k, C_{k+1}]` with `C_k ≥ 1000`,
`C_{k+2} ≤ 3·10^7`. All cell sums (weights, weighted weights) computed DIRECTLY on the integers of the cell
(`math.fsum`), the demand at the contact by cumulative ψ.
Pre-registered measurements:
1. Twin of G1: `cellExitWeight + cellEntryWeight − cellWeight × cellLength`, relative gap < 1e-10 on all cells.
2. Twin of G2: `(a_{k+1} − e^{π/T} a_k) − L_k`, relative to `cellLength_k²`, < 1e-9 on all cells.
3. Twin of G3: residual of the budget recurrence relative to `cellLength_N²`, < 1e-9 for every N.
4. Stability: `cellArea` by the cell formula (G1) against the cumulative formula of E472: relative gap reported (no threshold).
5. Measurements (no bound assumed): `|L_k|/C_k^{3/2}`, `|a_k|/C_k^{3/2}`, `|a_k|/cellLength_k²` (max and last); fraction of
   consecutive pairs of opposite signs; under alternation, `|A_{N+1}|` against `|a_0| + Σ|L_n|`; constant C measured in the antecedent
   of G6 and resulting compiled bound against measured `|A_N|/C_N^{3/2}`.
Verdicts: A = points 1–3 conforming and all values 4–5 reported; B = a point 1–3 non-conforming (recorded); C = execution impossible.
