# E431 — Arithmetic rigidity of the phase at the breaks: the pair can deposit like the line at only one prime (2026-11-04)

> Français : [README.fr.md](README.fr.md)

Compilation-only experiment (no numerical measurement; no twin required since there is no numerical conclusion).
Author's request: "continue, improve the approach and tighten the vise". Direct follow-up of E430 (§19.45): the
weakest compiled hypothesis that survived, `PairDepositOnLine` (the pair deposits at the break like the pair on the line),
is equivalent to "the shared prime falls on a sign change of the line density". E430 had studied it at ONE
prime; the directive requires working on a SERIES of gaps.

## Question posed (before any compilation)
If the "deposit on the line" hypothesis is demanded no longer at the single shared prime but at every break of a series of
primes, what remains? Expected (written before execution): unique factorization forbids two
distinct primes from both falling on a sign change of the density of the same frequency; the hypothesis can therefore be true
only at a single prime of the whole series. What would then remain for the missing link is the absorption,
by the complement, of a nonzero surplus of the pair at all primes but at most one.

## Protocol
1. Pre-register this file (commit) before the first compilation.
2. TDD probes in an UNversioned probe file (`RaccordPhaseProbe_SCRATCH.lean`, deleted after capture), each
   probe ending with `done` so that the compiler prints the remaining goal; exact outputs in `logs/probe_attempt*.txt`.
3. Write the isolated module `Terminal/RaccordPhaseRigidity.lean` (not added to `RHV6Fresh.lean`):
   (a) the cell fraction of a Tower at a sign change of the density reads the radial position:
       `arctan(β/T)/π` (identity); under `PairDepositOnLine`, fractions of the Tower and of the mirror at the break;
   (b) the "deposit on the line" hypothesis at any prime of rank `m` (`PairDepositOnLineAt m`) and its equivalence with
       the sign change (same proof as in E430);
   (c) arithmetic rigidity: two distinct primes never both fall on a sign change of the
       density of the same frequency (unique factorization); consequence for any carrier: `PairDepositOnLineAt` is
       true at at most one rank;
   (d) attempt (single): a Tower `(β, T)` touches at most two primes (three contacts at distinct primes
       are contradictory); if the compiler asks for more than the factorization, record the goal and
       do not insist;
   (e) the surplus of the pair at a break (`pairSurplus m`), its expression `2(cosh(δ log p_m) − 1)·D_line(log p_m)`,
       and: at two distinct ranks, at least one of the surpluses is nonzero.
4. At most two compilation attempts for the module, logged (`logs/lean_attempt{1,2}.txt`).
5. No hypothesis posed; no `sorry`; `lake build RHV6Fresh` green afterwards (`logs/lake_build_full_trimmed.txt`).

## Planned probes and expected goal
- S1: from "surplus zero at every rank" derive `False` without (c) — expected: the compiler asks for two distinct
  ranks and the factorization; nothing else.
- S2: from "the complement absorbs the surplus at every rank" derive `False` — expected: open goal on the complement,
  no compiled constraint closes it (break identity for any packet, E430 probe 4).

## Objects reused (never rebuilt)
`stagePosition`, `cellFraction`, `lastContactBefore`, `mirror_stage_shift_ne_zero` (FirstExceedanceRaccord,
MeetingContactReading); `realCountingDensity`, `densitySignChangeLog`, `realCountingDensity_eq_zero_iff`
(LocalPrimeGapSynchronization); `PairDepositOnLine`, `breakLog`, `pairDepositOnLine_iff_sign_change`
(RaccordTransportObligation); `pair_real_density_eq_cosh_line`, `radialShift_pos`, `linePoint_im`, `zero_radial_eq`,
`mirror_radial_eq` (OffCarrier); `fnPrimeAtRank`, `thm_primeAtRank_isPrime`, `thm_primeAtRank_injective` (RHV3Lean);
`Real.arctan_inv_of_pos`, `Int.fract_eq_iff`, `Nat.Prime.dvd_of_dvd_pow`, `Nat.prime_dvd_prime_iff_eq` (Mathlib).

## What the experiment does not claim
No contradiction is expected: the absence of a compiled constraint on the complement remains the frontier (§19.13,
§19.44, §19.45). The vise tightens by one notch: the weakest hypothesis can be true only once over the series.
