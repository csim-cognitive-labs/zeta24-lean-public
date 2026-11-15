# E442 — Compiling the rules read in E441: exact displacement by the cell fraction, rise threshold of the meeting cells, signed prime weight of a block without contact hypothesis

> Français : [README.fr.md](README.fr.md)

Pre-registration (2026-11-07), before any compilation. Direct follow-up of E441 (§19.60) under the order "pursue as
far as possible". Spectral prohibition in force (§19.55); work order §19.53.

## Verification of the nine mistakes
1. No new hypothesis: the only pointwise hypothesis ("no contact falls on an integer") is of the same
   type as "no meeting is a contact" (E439–E441), measured 0 ambiguous cases in E441. 2. The compiler
   decides. 3. Names checked by grep (`floor_add_sub_floor`, `stagePosition_contact`, `lastContactBefore_contact`,
   `lastContactBefore_of_mem_cell`, `displacement_rule`, `meetingCell_displacement_rule`, `cellLength_meeting_le`,
   `meeting_rises_of_weight_dominates`, `meeting_falls_of_length_dominates`, `weight_dominates_below_threshold`,
   `signedPrimeSum_eq_primes_in_block` free). 4. `lake build RHV6Fresh` after any change. 5. No prime or
   OFF tested. 6. No radial position. 7. No family. 8. Isolated module. 9. Intervals = partial remainders.

## Targeted statements (isolated module `Terminal/ExactDisplacementAndThreshold.lean`, imports `MeetingSignedSeries`)
- D1 `floor_add_sub_floor`: `⌊a + d⌋ − ⌊a⌋ = ⌊d⌋ + [fract a + fract d ≥ 1]` (arithmetic of integer parts).
- D2 `displacement_rule` (R1): `lastContactBefore y − lastContactBefore x = ⌊T log(y/x)/π⌋ + [cellFraction x +
  fract(T log(y/x)/π) ≥ 1]`; `meetingCell_displacement_rule`: the same between two consecutive meetings.
- D3 `stagePosition_contact`, `lastContactBefore_contact`: the stage position of a contact is its index.
- D4 `lastContactBefore_of_mem_cell`: an integer of `Ioc ⌊C_k⌋₊ ⌊C_{k+1}⌋₊`, if it is not the contact `C_{k+1}`, has
  `k` as last contact.
- D5 `signedPrimeSum_eq_primes_in_block` (general case of E441): the signed prime weight of a block of `M` cells
  is the sum over the primes of the block of `(−1)^{cell(q) − a}·log q`, without a contact hypothesis per gap
  (pointwise hypothesis: no contact of the block is an integer).
- D6 `cellLength_meeting_le`, `meeting_rises_of_weight_dominates` (R4 low safe zone): if `p(r − 1) ≤ log p`, the
  meeting cell rises; `meeting_falls_of_length_dominates` (R4 high safe zone): if `log p + non-prime
  weights < p(1 − 1/r)`, it descends.
- D7 `weight_dominates_below_threshold`: if `x(r − 1) ≤ log x` and `1/(r − 1) ≤ p ≤ x`, then `p(r − 1) ≤ log p`
  (the threshold `x*` separates properly: everything below rises).

## Protocol and criteria
Unversioned probe, at most two attempts for the final module, logs, `#print axioms`, complete build.
A: contradiction; B: everything compiles; C: failure in two attempts. Expected: B. No new numerical experiment:
the rules were measured in E441 (0 violations), E442 compiles them.
