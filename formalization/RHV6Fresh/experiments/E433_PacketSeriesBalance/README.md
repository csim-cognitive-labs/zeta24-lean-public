# E433 — The balance of the pair over a series of consecutive steps: what the complement must absorb (2026-11-04)

> Français : [README.fr.md](README.fr.md)

Compilation-only experiment (no numerical measurement; no twin required). Author's request: "continue",
after E432, whose missing link is "the complement cannot absorb, over the series of steps, the integrated surplus
of the pair". Directive: work on a SERIES of gaps, never a single one; frequency before height.

## Question posed (before any compilation)
Over a window of `m` consecutive steps starting from `a ≥ 2`, what exactly is the sum of the increments of the complement
of the pair, and through which points does the pair enter?
Expected (written before execution):
1. the sum of the increments of any packet over the window telescopes into two local steps, that of the end minus that of
   the start ("collapse at the edges": the interior steps of the pair cancel exactly over the series);
2. the sum of the increments of the exact remainder over the window equals the sum of the von Mangoldt weights of the points reached
   minus the variation of the background step;
3. hence the sum of the complement over the window = arithmetic content of the window − (local step of the pair at the end −
   local step at the start); the pair enters only through the primitive of its four members evaluated at the two edges;
4. for the mirror pair (case (a)), the local step has a closed form: primitive `−m·x·Tower/(ρ+1)` of the four members;
   the norm of the mirror member of this primitive grows like `x^{2−β}/(‖ρ'‖·‖ρ'+1‖)`.

## Protocol
1. Pre-register (commit) before the first compilation.
2. TDD probes in `SeriesBalanceProbe_SCRATCH.lean` (unversioned, deleted after capture; exact outputs in
   `logs/probe_attempt*.txt`).
3. Isolated module `Terminal/PacketSeriesBalance.lean` (not added to `RHV6Fresh.lean`): points 1–4.
   If the compiler asks for more than the objects listed, record the exact goal and do not insist.
4. At most two compilation attempts for the module (`logs/lean_attempt{1,2}.txt`); no hypothesis posed;
   no `sorry`; `lake build RHV6Fresh` green afterwards.

## Planned probes
- S1: "the complement of the pair is zero on all steps of a window ⟹ False" — expected: no contradiction;
  the compiler leaves "arithmetic content of the window = difference of the local steps of the pair at the edges".
- S2: "the complement of the pair is bounded in norm on all steps from `a` ⟹ False" — expected: no
  contradiction; remaining goal = growth in `N^{1−β}` of the local step of the pair against the arithmetic content, which is
  the exponent of the remainder (known frontier, ⟺ RH).

## Objects reused
`packetIncrement`, `remainderIncrement`, `localPacket`, `remainderIncrement_eq_packet_add_complement`,
`remainderIncrement_arithmetic`, `gap_demand_sum_increments`, `packet_channel_four_of_mirror`,
`residueTerm_eq_zeroTerm`, `residueTerm_conjIndex`, `norm_zeroTerm_eq`, `mirror_multiplicity_eq`,
`Finset.sum_range_succ`.
