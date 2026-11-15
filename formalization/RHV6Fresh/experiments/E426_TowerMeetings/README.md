# E426 — Meetings between successive Towers on the real axis (pre-registered 2026-11-03)

> Français : [README.fr.md](README.fr.md)

Correction of the approach (author): E420–E425 studied the Towers separately and then their cross values, never the
**meetings** between their trajectories on the real axis. Corrected chain: Towers → real contacts → real values →
**meeting points between Towers** → succession of meetings (breaks: end of one gap, start of another) →
junction to the primes and to the gaps. No spectral projection, no OFF hypothesis, no search for a contradiction.
Reference Lean module, compiled before execution: `Terminal/TowerMeetings.lean` (isolated, 27 declarations, no `sorry`,
standard axioms; two attempts logged in `logs/lean_attempt1.log`, `logs/lean_attempt2.log`).

Lexicon: "meeting point" remains the name of the end of a prime gap (`meetingPoint`); here "meeting between
Towers" designates the three objects of the author: (A) coincidence of contacts, (B) meeting of values (same real
parts at the same abscissa), (C) collective meeting (succession / coincidence of the meetings of neighboring pairs).

## Compiled predictions that the experiment must recover up to rounding
* `unitMeeting_iff`, `slow_sin_eq_zero_iff`, `fast_sin_eq_zero_iff`: the meetings of the unit trajectories form two
  lattices in logarithmic abscissa, slow (step 2π/(T₂−T₁)) and fast (step 2π/(T₁+T₂)).
* `gap_of_slowMeetings`, `sum_of_fastMeetings`: the difference of the heights is re-read exactly from two consecutive
  slow meetings; the sum from two consecutive fast meetings.
* `slowMeetingLog_zero_pos`, `slowMeetingLog_zero_lt`: the slow meeting of index 0 is in (0, 1/(2T₁)) (stuck to x = 1).
* `contactsCoincide_not_meeting`: a coincidence of contacts is never a meeting of raw values.
* `towerMeeting_of_unitMeeting_iff`: at a point of the unit lattice, the raw meeting takes place only if the value is zero;
  hence the raw meetings are **displaced** with respect to the unit lattice (except at zero crossings).

## E426(a) — all consecutive pairs (2,001,051), analytic lattices (`scripts/e426_lattice_all.py`)
1. Verification of the compiled predictions (index 0 in (0, 1/(2T₁)): 0 violations; gap and sum re-read: relative error
   ≤ 10⁻⁹).
2. First slow meeting u₁ per height band, compared with log(T/2π): **measurement**, no pre-registered law.
3. Contacts enclosing u₁ for each Tower (preceding index, cell fraction, parity); exact coincidences of contacts
   (|fraction| < 10⁻⁹): counted, expected 0; common unit value at u₁ (identical for both Towers: difference ≤ 10⁻⁸).
4. Break (C): position of the first slow meeting of the next pair (n+1, n+2) on the slow lattice of the pair
   (n, n+1): fraction of step, 20-class histogram, exact coincidences (|d| < 10⁻⁹). **No pre-registered law.**
5. Junction: x₁ = exp(u₁); prime gap [p_j, p_{j+1}] containing x₁ (primes ≤ 10⁸, fraction of covered pairs
   recorded); position fraction within the prime gap (20-class histogram); products g·log(p_{j+1}/p_j) and g·log x₁
   (median, deciles) per band. Deterministic twin: pseudo-primes of density 1/log n, seed 20261103, same procedure.
   Reading: if the real product and the twin product have the same distribution, the observed junction is that of
   the density alone; a difference would be a measurement, not a law.

## E426(b) — raw meetings per band (`scripts/e426_raw_meetings.py`)
Bands: ranks 1–101, 100,000–100,100, 2,000,951–2,001,052. For each pair: all roots of
cos(T₁u−φ₁)/|ρ₁| − cos(T₂u−φ₂)/|ρ₂| on [0, u₁ + 3 fast steps] (grid of 8 points per fast period, bisection 48 steps;
pairs with more than 3·10⁷ roots skipped and counted). Measures: number of raw meetings against number of points of the
unit lattices (difference recorded by histogram); displacement of each root to the nearest lattice point
(fast steps; max and rms; expected decreasing with height since the moduli come closer — measurement); root nearest
to u₁: raw real values of the two Towers, contacts before/after of each Tower, unit cosine; order: number
of raw roots between u₀ and u₁ against number of fast points. Twin: mpmath 30 digits, refinement of the first 20
roots and of the root near u₁ for ranks 1, 2, 100,001, 2,001,051; criterion: float/mpmath difference ≤ 10⁻⁹·u.

Nothing here presumes a constraint on the radial position; any constraint would first be compiled. Results, including
negative ones, are published in `RESULTS.md`.
