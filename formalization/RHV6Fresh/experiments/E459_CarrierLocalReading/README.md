# E459 — Φ3: local hypotheses H-a and H-b, classification in three headings then requirements (pre-registration, 2026-11-09)

> Français : [README.fr.md](README.fr.md)

Reference: `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.80 (Φ3), §19.83 point 3 (rule of the three headings), §19.86 (forecast from the
audit E460), §19.88. No hypothesis admitted, no axiom, no `sorry`; isolated module
`RHV6Fresh/Terminal/CarrierLocalReading.lean`, NOT added to `RHV6Fresh.lean`. No spectral theory. No off-line zero is
assumed or tested: the classification is made at the level of the Towers (pairs radial position, height), and the statements on
true zeros are equivalences or implications from RH.

Order followed, stated as is: an unversioned probe (`attempts/probe1.txt`, without error) preceded this pre-registration to establish
the classification, as the author's order requests (classify BEFORE pre-registering); the final module is compiled after this commit.

## Precise forms of the hypotheses
* **Parametric form** `SameReadingAt β T n`: the rank `n` is not in the strip of the Tower `(β, T)` (the word of the mirror and the word of
  the Tower coincide at the prime of rank `n`).
* **H-a (at rank `n`)**, on true zeros: `SameReadingAtRankOnCarriers n` — for every true zero, same reading at rank `n`. The plan
  said "at the prime of the first break"; E450 treats any shared prime: H-a is therefore posed at any fixed rank
  (and, by extension, on any FINITE set of ranks).
* **H-b**, on true zeros: `SameMeetingCellsOnCarriers` — same meeting cell for the Tower and its mirror at EVERY meeting;
  variant `SameReadingBeyondOnCarriers N` (all the meetings from rank `N` on). The meeting cell of the gap of rank `n`
  is the word at rank `n + 1` (definitional identity, to be compiled).

## Classification in three headings (established by the probe, to be compiled in the module)
| Hypothesis | (i) compiled implication | (ii) counter-model compiled at the level of the Towers | (iii) converse |
|---|---|---|---|
| H-a at rank `n` (or on a finite set of ranks) | RH ⟹ H-a | YES, outside the degenerate case: if no prime of the set is exactly on a contact of the line at height `T`, there is an open window around the line where every Tower has the same reading; in particular an off-line Tower on the low side satisfies it. Degenerate case (prime exactly on a contact of the line): the same reading at this rank FORCES the line at this height. Exact classification: "H-a at rank `n` forces the line at height `T`" ⟺ "the prime of rank `n` is exactly on a contact of the line of height `T`". | H-a ⟹ RH: OPEN, stated as such; at the level of the Towers it does not force the line (heading ii): "strictly weaker, on the Towers". |
| H-b on all the meetings (or from any rank) | RH ⟺ H-b (both directions) | none: on the Towers, same reading from a rank on ⟺ line | not applicable: EQUIVALENT, hence REFORMULATION, never posed |
| H-b restricted to a strict infinite subsequence of meetings | RH ⟹ | not established | OPEN; settling it would require knowing whether the strip meets the subsequence, a question of distribution FORBIDDEN (no density asserted); not pursued |
| H-c (weight and strip) | — | — | equivalent: closed as a reformulation in E458 (B6) |

Scope remark (§19.85): "same reading from a rank on ⟺ line" is a tail statement for the question of the MIRROR (compiled
here); it says nothing about the selection of carriers.

## Statements to compile
1. `sameReadingAt_iff`, `meetingCell_eq_towerWord`, `same_meetingCell_iff` (dictionary).
2. `floor_stable_of_continuous_not_int`, `towerWord_stable_near`: outside exact contact, the word is locally constant in the radial
   position (on both sides).
3. `sameReading_window`: window of same reading around the line on any finite set of ranks without exact contact;
   `exists_offLine_sameReading_on_finset`: counter-model on the low side (heading ii).
4. `mem_mirrorStrip_of_prime_on_line_contact`: degenerate case; `sameReadingAt_forces_line_iff`: exact classification of H-a.
5. `sameReading_beyond_iff`: on the Towers, same reading from a rank on ⟺ line.
6. `sameReadingAtRank_of_riemannHypothesis` (RH ⟹ H-a); `sameReadingBeyond_iff_riemannHypothesis`,
   `sameMeetingCells_iff_riemannHypothesis` (H-b ⟺ RH).
Limit stated in advance: the non-vacuity of the "without exact contact" branch is not compiled (it is measured by the twin); the exact
classification (statement 4) covers both branches without needing it. The degenerate case is a logical branch: it is NEVER
asserted that a prime is on a contact (§19.51).

## Forecasts written before execution
* Everything compiles (the probe passed).
* Stopping criterion of the plan (hypothesis weaker than RH, true on the controls, whose compiled requirement involves the weight):
  NOT reached — H-a is weaker on the Towers but its requirement does not involve the weight (window around the line,
  fixed by the cell fraction); H-b is a reformulation.

## Deterministic part — `e459_local_reading.py`
First 200 Odlyzko heights, primes ≤ 10⁶, controls `β ∈ {0.3; 0.4; 0.45}` (non-carrier Towers). Measurements: (a) cell fraction of
the line at the first ten ranks, for the 200 heights: smallest distance to a contact (expected: strictly positive
everywhere, non-degenerate branch); (b) EXACT half-width of the window of same reading at rank 0 and over the first ten ranks
(tangential formula), cross-checked by direct test on both sides of the edge; (c) share of controls that satisfy H-a at rank 0 and
over the first ten ranks (expected: majority at rank 0 for each control, the phase shift being small relative to the
cell; no numerical threshold is fixed); (d) first strip rank (rank where H-b breaks) for each control: expected finite for
all control Towers (already observed in E458: no empty strip). Measurement, no law, no density.

## Protocol
At most two attempts; `attempts/`; `#print axioms`; grep of the ban at zero; full `lake build RHV6Fresh` green; script once
under `nohup`, output in `logs/`.
