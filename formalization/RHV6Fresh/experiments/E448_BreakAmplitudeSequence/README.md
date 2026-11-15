# E448 — The sequence of payment amplitudes of a line Tower at successive meetings (pre-registration, §19.70, 2026-11-08)

> Français : [README.fr.md](README.fr.md)

Author's order (R-LINE): as long as Lean remains to be written, do not look for the contradiction; master the break
mechanism from the line (ON zeros, `β = 1/2`). Candidate C3 of the handover of 2026-11-07, chosen in the absence of
indication from the author. Authorized objects: one Tower `(1/2, T)`, its contacts, its cells, its cell fraction `f`,
its real values at the contacts; the consecutive primes. No sum of Towers, no spectral object, no hypothesis, no
statement on `β ≠ 1/2`, no proposed obligation.

## Starting point (E447, compiled)
The break `log q` at the prime `q` is paid with the amplitude of the last contact before `q`, EXACTLY
`√q · e^{−π f(q)/(2T)} / ‖(1/2, T)‖`, where `f(q)` is the cell fraction at the point `q` (`line_break_amplitude_exact`).
The question of E448: how does this amplitude evolve from one prime to the next, and what determines the sequence?

## Hypotheses (to be decided by the compiler, then by the numbers)
* H1 (orbit of the fraction): the cell fraction at the next point is the fractional part of the fraction at the
  current point plus `T·log(y/x)/π`: `f(y) = fract(f(x) + T·log(y/x)/π)`. The sequence of fractions at consecutive
  primes is therefore an orbit of translations by `T·log(p_{n+1}/p_n)/π` modulo one, determined by the ratios of
  consecutive primes.
* H2 (amplitude step per cell): on the line, `|v_{k+1}| = e^{π/(2T)} |v_k|`; hence the payment amplitude at the point
  `y` over that at the point `x` is `e^{π (k(y) − k(x))/(2T)}`, where `k(y) − k(x)` is the cell displacement
  (`displacement_rule`: `⌊T·log(y/x)/π⌋` plus a carry read by the fraction).
* H3 (exact form of the ratio): the same ratio also equals `√(y/x) · e^{−π (f(y) − f(x))/(2T)}`; the two writings are
  compatible because `T·log(y/x)/π = (k(y) − k(x)) + (f(y) − f(x))`.
* H4 (monotonicity): from one prime to the next, the payment amplitude never decreases; it is constant exactly when
  the two primes share a cell (zero displacement); otherwise it is multiplied by at least `e^{π/(2T)}`.
* H5 (bracketing of the ratio): the ratio of amplitudes between two consecutive primes is strictly between
  `√(y/x)·e^{−π/(2T)}` and `√(y/x)·e^{π/(2T)}`.
* H6 (telescoping): over a series of `J` meetings, the product of the ratios is `e^{π (k(p_{n+J}) − k(p_n))/(2T)}`; the
  logarithm of the payment amplitude grows by exactly `π/(2T)` times the number of cells crossed.

## Planned statements (isolated module `Terminal/BreakAmplitudeSequence.lean`, import `BreakMechanismOnLine`)
L1 `cellFraction_step` (H1), `cellFraction_step_eq_fract_sum` (form with the fractional part of the displacement);
L2 `line_abs_value_succ` (`|v_{k+1}| = e^{π/(2T)}|v_k|`), `line_abs_value_add_nat`, `line_abs_value_sub`
(`|v_l| = e^{π(l−k)/(2T)}|v_k|` for `k ≤ l`);
L3 `line_break_amplitude_ratio_cells` (H2), `line_break_amplitude_ratio_exact` (H3), `displacement_eq_stagePosition_sub` (H3);
L4 `line_break_amplitude_mono` (H4), `line_break_amplitude_eq_iff_same_cell`, `line_break_amplitude_step_of_new_cell`;
L5 `line_break_amplitude_ratio_bounds` (H5); L6 `line_break_amplitude_telescope` (H6), `line_break_price_mono_of_le`
(the price `|v|·log q` does not decrease either).
At most two compilation attempts on the final module, each output kept in `attempts/`; probes in unversioned
`*_SCRATCH.lean`, deleted after capture.

## Experiment (after compilation; Odlyzko zeros, `β = 1/2`, 7 heights, primes ≤ 10⁷)
(a) orbit of the fraction: residual of `f(p_{n+1}) − fract(f(p_n) + T·log(p_{n+1}/p_n)/π)` over all consecutive primes;
(b) ratio of amplitudes: the two forms (H2 and H3) against direct computation, residuals; (c) violations of
monotonicity and of the bracketing (expected: zero); (d) number of pairs of consecutive primes that share a cell, per
decade, against the total number of pairs (finite regime of E446 seen from the sequence); (e) telescoping: logarithm
of the ratio between the first prime and the last prime of each decade against `π/(2T)` times the number of cells
crossed. mpmath deterministic twin with 30 digits on a subset (primes ≤ 10⁶ via sympy, 3 heights).
Criterion: A if all identities are exact to floating-point precision and (c) is zero; B if an identity compiles but
the number contradicts; C otherwise. No conclusion on the OFF is drawn, by order.
