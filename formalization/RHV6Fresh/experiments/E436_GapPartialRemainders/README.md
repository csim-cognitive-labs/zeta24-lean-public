# E436 — Partial gap remainders at the contacts: the share of a Tower over a gap cut out by its own contacts (2026-11-06)

> Français : [README.fr.md](README.fr.md)

Compilation-only experiment (no numerical measurement; no twin required). Redress plan §19.51, steps 1 to 4.
Framework (author, 2026-11-06): the intervals defined by the contacts of a Tower are PARTIAL REMAINDERS of the gaps of the
primes; they belong to the collective reconstruction of the gaps and are not directly linked to the primes.

## Written verification of the nine points (CLAUDE.md (private research repository), list of mistakes)
(1) the synchronization (`all_signals_meet`) is not called into question; (2) no "failed criterion" on the structure;
(3) nothing is read on a mixed signal: each share is the increment of the smoothed term of the member between the two bounds of
the gap; (4) no definition requested from the author; (5) no word attributed; (6) action delivered (module, commit); (7) the
pair is treated as a sum of two shares at the same frequency, and the target concerns the sum of all shares;
(8) the gaps are never linked to the height; (9) no Tower "touches" a prime: the contacts cut out the
share of the Tower over the gap, the bounds of the gap are the primes, the two edge pieces are cell fractions.

## Question posed (before any compilation)
How does the exact share of a Tower over a gap (`smoothedLocalContribution`) decompose over the contact cells of
this Tower, and what becomes of this decomposition (a) for two members of the same frequency, (b) over a series
of consecutive gaps, (c) facing the collective reconstruction and the single premise in frequency?

## Hypotheses admitted
None. Probes S4 pose a carrier `C : OffCarrier` and the compiled freeze (`outgoing_same_height`) only.

## Established results reused (Lean form checked before use)
`accumulationFrom`, `contact_accumulation_eq_endpoint_difference`, `contactAccumulation`, `contactVariation`,
`contact_partition_exact`, `contactAt_eq`, `contactAt_ratio`, `lastContactBefore`, `cellFraction`, `lastContact_le`,
`lt_contact_succ`, `log_div_lastContact`, `height_mul_log_eq`, `stagePosition`, `residueTerm_gap_eq`,
`smoothedLocalContribution`, `localArithmeticTarget`, `all_signals_meet`, `imposedShare_eq`, `meetingPoint`,
`contactAt_eq_contactMinusAt`, `contact_eq_line_mul_radial`, `mirror_contacts_coincide_iff`, `outgoing_same_height`,
`ExpectedFrequencyRisesAtMeetings`, `expectedFrequency_iff_no_shared_frequency`. No proof redone.

## Protocol
1. Pre-register (this file, commit) before the first compilation.
2. TDD probes in `GapPartialRemainders_SCRATCH.lean` (unversioned, deleted after capture; exact outputs in
   `logs/probe_attempt*.txt`).
3. Isolated module `Terminal/GapPartialRemainders.lean` (not added to `RHV6Fresh.lean`), at most two attempts
   (`logs/lean_attempt{1,2}.txt`), no hypothesis posed, no `sorry`, axioms displayed; `lake build RHV6Fresh` green.

## Planned probes and expectations (written before execution)
- **S1 — Partition.** Share of a Tower `(β, T)` over a gap = initial partial remainder (from `p_n` to the first contact in
  the gap) + whole cells + final partial remainder (from the last contact to `p_{n+1}`), as soon as the gap contains a
  contact; otherwise the share is a single partial remainder, of logarithmic length < π/T. Each edge remainder covers a cell
  fraction read by `cellFraction` at the bounds. Expected: compiles by `accumulationFrom` and `log_div_lastContact`.
- **S2 — Shared frequency.** Two Towers of the same frequency have stage positions shifted by a constant (radial part
  alone); their numbers of contacts in any gap differ by at most one. Expected: compiles by `Int.floor`.
- **S3 — Series of gaps.** The two partial remainders on either side of a meeting point exactly recompose a
  cell of the Tower; over `J` consecutive gaps, the sum of the shares is whole cells + two edge remainders.
  Expected: compiles by telescoping.
- **S4 — Target.** From the collective reconstruction on each gap, S1–S3 and the freeze of the carrier, attempt the single
  premise in frequency (`ExpectedFrequencyRisesAtMeetings`) then `False`. Expected (written before execution): goal left;
  reproduced in full, not renamed "what is missing".

## Criteria (a single category)
A compiled closure; B new unconditional reduction (the share of a Tower over a gap and over a series read
entirely in partial cell remainders, compiled); C equivalence to RH compiled; D nothing compilable. Expected: B.

## Addendum before any compilation (2026-11-06, author's second message)
The infinite sum is not a support and fills no gap; no return to spectral analysis. `all_signals_meet`
and `imposedShare_eq` are removed from the list of established results used. Objects: contact `contactAt`, value at the contact
`contactRealValue`, raw cell contribution `towerValue ρ p_{n+1} − towerValue ρ p_n` (and its real part
`towerRe`), balance at the meeting point with explicit remainder for a finite family `breakResidual`, `breakResidual_erase`.
Probes re-posed: S1 partition of the raw cell contribution by the contacts of the Tower (edge remainders = cell
fractions); S2 shared frequency (number of contacts in any gap: difference ≤ 1); S3 series (the remainders on either side
of a meeting point recompose a cell); S4 balance with remainder for the finite family containing the pair,
values at the contacts of the mirror in `C_k^{1/2+δ}` (`contactRealValue`), attempt of `False`; expected: goal left,
reproduced in full. Expected criterion: B (partition and series compiled in the raw channel).
