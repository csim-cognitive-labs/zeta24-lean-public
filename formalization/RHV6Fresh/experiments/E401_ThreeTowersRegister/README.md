# E401 — Deterministic register of the three known Towers over the 168 prime gaps from 2 (p_n ≤ 1000)

> Français : [README.fr.md](README.fr.md)

Step G of the pre-registered plan (master document §19.24.8, author's green light on 2026-11-01). No Lean modified.

## Pre-registration (written BEFORE execution)

Objects: the first three certified zeros (T₁, T₂, T₃, real part 1/2: theorems), their Towers, the 168 gaps
`[p_n, p_{n+1}]` with `p_n ≤ 1000` (from `[2, 3]` to `[997, 1009]`).

For each gap, the register gives:
1. the contacts `C_k = exp((arctan(T/β) + kπ)/T)` of each Tower crossed by the gap (indices `k`), that is, the
   cells `J_{k,n}` that the gap cuts out;
2. the raw contribution `−2 Re (p_{n+1}^ρ − p_n^ρ)/ρ` of each Tower (= `Δ_{ρ,n}` of the text, F3 compiled) and their sum;
3. the counting contribution `−2 Re (Ei(ρ log p_{n+1}) − Ei(ρ log p_n))` and their sum;
4. the smoothed contribution `−2 Re (p_{n+1}^ρ − p_n^ρ)/(ρ(ρ+1))` (F4 compiled) and their sum;
5. ALONGSIDE, the exact demand of the gap in the compiled channel: `R(p_{n+1}) − R(p_n)` with
   `R(x) = Σ_{m<⌈x⌉} Λ(m)(1 − m/x) − [x/2 − ζ'/ζ(0) + (ζ'/ζ)(−1)/x + Σ_{j≥0} (−x^{s_j}/(s_j(s_j+1))), s_j = −2(j+1)]`,
   formula taken as is from `ZetaPerronLineIdentity` / `ZetaSmoothedZeroFormulaP5` (no other).

Twin: two implementations at 30 and 50 digits (mpmath); the zeros are recomputed (`zetazero`) and compared to the
certified values at 30 digits. No synthetic zero, no window, no average, no correlation.

Expected results, stated in advance:
- exact telescoping: for each channel, the sum of the 168 contributions of a Tower equals its contribution on `[2, 1009]`
  (identity `primeGapContribution_chain`, `gapTerm_add`);
- the sum of the three smoothed Towers equals the exact demand on NO gap (this is F8 compiled,
  `no_finite_family_at_any_meeting`); the residual gap is the tail of the omitted zeros (`localResidual_eq_tail`);
- implementation check (not a result): the residual `demand − Σ_{k≤K} smoothed` decreases when `K` goes from 3 to
  30 then 100 zeros, since the smoothed series converges absolutely; no value is read as a measurement of `β`;
- no conclusion about `β`; no contact is a prime; no comparison to an average.

The eight points of the "beginner mistakes" list (CLAUDE.md (private research repository), 2026-10-28) are checked: (1) nothing is refuted;
(2) no "failed criterion"; (3) reading at gap ends (meeting = `p_{n+1}`); (4) nothing asked of the author;
(5) no word attributed; (6) action = files + commit; (7) the demand is confronted with the sum, not with one member;
(8) no height reading from the gaps.

## Results (run of 2026-11-01, after pre-registration; 11 s at 30 digits, 13 s at 50 digits)

Files: `e401_register_dps30.txt`, `e401_register_dps50.txt` (168 lines: contacts crossed per Tower, raw /
counting / smoothed contributions per Tower and sums, exact demand, residuals after 3, 30, 100 zeros), `e401_output_dps30.txt`,
`e401_output_dps50.txt` (summaries).

- Zeros 1..3 recomputed = certified values to 1e−28, at both precisions.
- Twin: contacts crossed identical on the 168 gaps; all numeric columns identical on the 12 displayed digits
  (maximum difference 0).
- Telescoping: for each Tower and each channel, sum of the 168 contributions − contribution on `[2, 1009]` ≤ 2e−30
  (identity, as expected).
- Total exact demand on `[2, 1009]`: −0.332282131799033 (same value at both precisions).
- Number of gaps where the smoothed sum of the three Towers equals the demand to 1e−20: **0 out of 168** (as expected: F8).
- Implementation check (not a result): maximal residual `|demand − Σ_{k≤K} smoothed|` over the 168 gaps:
  0.149 (K = 3), 0.032 (K = 30), 0.013 (K = 100): decreasing with K, consistent with the absolute convergence of the smoothed
  series; it is the tail of the omitted zeros (`localResidual_eq_tail`), nothing else.
- The first eleven lines reproduce E400 (pasted text) identically on the raw channel.

No conclusion about β. No contact is a prime. No average, window or correlation was computed.
