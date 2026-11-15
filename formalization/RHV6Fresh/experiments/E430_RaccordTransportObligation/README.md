# E430 — The transport at the shared prime written with the contacts, and the junction obligation guided by the compiler (2026-11-04)

> Français : [README.fr.md](README.fr.md)

Compilation-only experiment (no numerical measurement; no twin required since there is no numerical conclusion).
Author's request: "proceed with your plan; attempts must be made so that the Lean compiler guides you and
asks precisely what is missing; then you detail the hypotheses to produce the missing link; we
work in TDD".

Target (critique of 2026-11-04): "prove that the arithmetic obligation of the junction at the shared prime applies to the
transport defined in `TransportAtSharedPrime.lean`".

## Protocol (fixed before the first compilation)
1. Write the isolated module `Terminal/RaccordTransportObligation.lean` (not added to `RHV6Fresh.lean`):
   (a) identities: transport between two members at an abscissa, written with the last two contacts and the two
   cell fractions; pair at the shared prime; (b) definition `RaccordTransportObligation` (the detour transports
   the value of the ON chain) and what it is equivalent to; (c) identity of the break for any packet; named hypothesis
   `PairDepositOnLine` (never posed) and what it forces.
2. At most two compilation attempts, logged (`logs/lean_attempt{1,2}.txt`).
3. TDD probes in an UNversioned probe file, each probe ending with `done` so that the compiler
   prints the remaining goal (`logs/probe_attempt1.txt` keeps the exact output); the probe file is deleted
   after the capture.
4. No hypothesis posed; no `sorry` in the module; `lake build RHV6Fresh` green afterwards (`logs/lake_build_full_trimmed.txt`).

## Objects reused (never rebuilt)
`energyRatio`, `energyRatio_eq`, `zeroTerm_norm`, `zeroPoint_eq_mk`, `zeroPoint_re_pos`, `mirrorMember_ordinate`
(SuccessionInvariants, ExplicitFormulaLink, SuccessiveContactConstraints, MirrorCount); `abs_contactRealValue`,
`growth_factor_eq`, `lastContactBefore`, `cellFraction` (ContactRealValue, MeetingContactReading);
`detour_transport_product_onLine`, `onLine_chain_transport`, `detour_arithmetic_factor_ne_one`, `detourPrimeContent`,
`detourPrimeContent_eq_exp_logGaps` (TransportAtSharedPrime); `remainderIncrement_eq_packet_add_complement`,
`break_compensated_by_other_frequencies`, `break_at_meeting`, `pair_real_density_eq_cosh_line`,
`realCountingDensity_eq_zero_iff`, `densitySignChangeLog` (HeightPacket, OffCarrier, LocalPrimeGapSynchronization).

## Expected result of each probe (written before execution)
* Probe 1 (obligation from the break): the remaining goal will concern `δ` and the prime content alone; the break
  hypotheses will not be usable.
* Probe 2 (`PairDepositOnLine` from the break): the remaining goal will be the vanishing of the line density at the
  break.
* Probe 3 (packet of the pair at the step of the break): explicit identity in raw Towers, without the complement.
* Probe 4 (deposit of the complement): identity, closed by `rfl`.
