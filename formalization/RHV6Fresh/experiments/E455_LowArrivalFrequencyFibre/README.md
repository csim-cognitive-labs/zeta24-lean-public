# E455 — K5: the fibre of the low arrival, in frequency alone (pre-registration, 2026-11-08)

> Français : [README.fr.md](README.fr.md)

Reference: `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.78. Author's question: "the frequencies of the OFF are necessarily
different from those of the ON: an OFF cannot take the occupied height of the ON nor reach the next ON".

## Audit (before compilation)
* (a) compiled for the followed ON and the history (`no_shared_frequency_of_history_onLine`); NOT compiled for a later ON of
  the same height = `NoMixedHeight` (⟸ RH, never derived).
* (b) compiled by the order (`consecutive_no_height_between`, `frequency_never_decreases`); strict only outside the mixed fibre.
* (c) compiled as a frequency REPETITION (fibre ≥ 2, `mirror_breaks_frequency_cascade`, `passage_frozen_of_low_entry`), not
  as a different value (rank bounds blind to the radial).

## Module
`RHV6Fresh/Terminal/LowArrivalFrequencyFibre.lean`, isolated, six statements M1–M6 (§19.78.3). No amplitude.

## Expected answer (recorded in advance)
No contradiction. The only open point is the mixed fibre, decided by the side of the successor of the low entry. Frontier
unchanged (single premise ⟺ RH; `NoMixedHeight` ⟸ RH).

## Protocol
At most two attempts; unversioned scratch probes, outputs captured in `attempts/`; grep of the ban before build;
full `lake build RHV6Fresh` after the green attempt.
