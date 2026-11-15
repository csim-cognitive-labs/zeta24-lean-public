# E446 — The "one meeting per cell" regime is finite: pre-registration (copy of §19.68, 2026-11-07)

> Français : [README.fr.md](README.fr.md)

### 19.68 The collective budget through the authorized objects only: the "one meeting per cell" regime is finite (pre-registration of E446, 2026-11-07)

**Author's order.** "Plan, formulate hypotheses, verify with experiments, stay within the framework, produce Lean that
implements the root cause of the finding, move forward." Framework: single strategy of §19.67, authorized objects only
(one Tower, its contacts, its cells, its values; the primes, `rawDemand`, `cellWeight`, `cellPrimeWeight`,
`cellDemand`; the compiled theorems of the corpus, including `logGapsVanish_holds` and `WeakPNT''`).

**Finding to explain (E445, T2 and P6).** The price of a meeting (`x^β`, P6) beats the budget of ONE meeting (`log p`),
never the cumulative budget. **Proposed root cause (hypotheses H1–H3).**
* **H1 (finite regime).** All the statements "the meeting cell crosses exactly one prime" (`meeting_cell_primes`,
  `cellPrimeWeight_meeting`, `meeting_cellDemand`, `valuePrimeSum_eq_meetings`, `amplitudeMeetingSum`) assume that
  the gap `[p_n, p_{n+1}]` AND the next gap each contain a contact. These two hypotheses place an entire cell
  `[C_k, C_{k+1}]` inside `]p_n, p_{n+2}]`, hence `log p_{n+2} − log p_n ≥ π/T`. Now `logGapsVanish_holds` (PNT ported)
  gives `log p_{n+1} − log p_n → 0`. Hence for every Tower `(β, T)` there is a rank `N(β, T)` beyond which two
  consecutive gaps never each have a contact: the series of meetings with one prime per cell is FINITE. The price at
  `M_n` is confronted with the budget `log p` of a meeting only on a finite initial segment.
* **H2 (the exact budget of a cell is its length, to first order).** Beyond the regime, a cell contains several
  primes; its exact budget is `cellWeight = ψ(C_{k+1}) − ψ(C_k)` and, by `WeakPNT''`,
  `cellWeight/cellLength → 1`, `cellDemand/cellLength → 0`. The "collective budget" of a cell is not `log p` but the
  length of the cell, up to a remainder which is the variation of `rawDemand` over the cell.
* **H3 (the price of a Tower on its cell is negligible against this budget).** The step of a Tower `(β, T)` on its own
  cell is `|v_{k+1} − v_k| = (1 + e^{βπ/T}) C_k^β/‖ρ‖`; divided by the length `C_k (e^{π/T} − 1)` it tends to zero
  for every `0 < β < 1`, ON or OFF. P6 also holds for `β = 1/2` (`price_beats_budget_on_line`): the reading "the OFF
  price beats the budget" was not discriminating.

**E446 pre-registration (`experiments/E446_MeetingRegimeFinite/`).** Isolated module `Terminal/MeetingRegimeFinite.lean`
(imports `MeetingPriceTheorem` and `LogGapsTheorem`): F1 `meeting_cell_within_two_gaps`; F2 `log_ratio_ge_cell_of_meeting`
(`π/T ≤ log p_{n+2} − log p_n`); F3 `two_consecutive_contacts_finite` (∃ N, ∀ n ≥ N, ¬(contact in gap n ∧ contact
in gap n+1)); F4 `meeting_series_rank_bounded`, `meeting_break_rank_bounded` (the hypotheses of
`cellPrimeWeight_meeting` and of `valuePrimeSum_eq_meetings` are satisfied only at bounded rank); F5
`cellWeight_eq_psi_diff`, `contactAt_tendsto_atTop`, `cellWeight_div_cellLength_tendsto_one`; F6
`cellDemand_div_cellLength_tendsto_zero`; F7 `tower_step_div_cellLength_tendsto_zero`; F8 `price_beats_budget_on_line`;
F9 `valueNonPrimeSum`, `valuePrimeSum_balance` (weighted budget of the primes of a block = weighted demand − weighted
non-prime weights + weighted lengths, closed form B4). At most two compilation attempts, outputs kept in
`attempts/`. **Numerical experiment** (`scripts/e446a_regime.py`, primes ≤ 10⁷): for the seven real Towers and the
witness pairs `β ∈ {0.3; 0.4; 0.45}`, (a) last rank `N_obs` where two consecutive gaps each have a contact, number
of such ranks, and check of F2 on each (0 violations expected); (b) `cellWeight/cellLength` and `cellDemand/cellLength`
per decade of `C_k` (gap to 1, resp. to 0, expected to decrease); (c) step of the Tower on its cell against the length
(formula F7 to 10⁻¹², decrease expected). **Twin** (`scripts/e446b_twin_mpmath.py`, 30 digits): same ranks `N_obs`
and same ratios on a sample of cells. **Criterion**: A if F1–F9 compile and (a)–(c) conform; B if part of it
compiles; C otherwise. Predictions: `N_obs` finite for each Tower, increasing with `T`; `N_obs` larger for the
mirror `1 − β` than for `β`? (not predicted: the phase `arctan(T/β)` shifts the contacts, the condition F2 depends
only on `T` but the effective rank depends on both).

**What this changes in the strategy.** The "collective budget" step cannot be "price at `M_n` against `log p` over
the series": this series is finite. The exact collective budget of a cell is its length plus the variation of the raw
demand over the cell; the price of a Tower on its cell is negligible against it. The confrontation can only bear on
the variation of `rawDemand` over the cell (authorized object), of which the corpus knows only `o(cell)` (F6). No
compiled relation links the amplitude of a Tower to this variation: this is the open obligation, recorded without
spectral object. [WITHDRAWN by the author on 2026-11-07: see "Author's correction" at the end of the section.]
