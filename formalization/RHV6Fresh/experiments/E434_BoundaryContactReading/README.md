# E434 — The edge effect of the pair read by the contacts (2026-11-04)

> Français : [README.fr.md](README.fr.md)

Compilation-only experiment (no numerical measurement; no twin required). Author's request: "ok continue",
after E433 (§19.48): "absorbing over the series" is one equation per window between the arithmetic content and the
edge effect of the pair. Directive: the radial reading of the contacts and the arithmetic content must face each other in one
and the same equation.

## Question posed (before any compilation)
Is the real part of the edge effect of the pair at a window edge `x` read exactly by the last contact
of each of the two members (value at the contact, growth factor over the cell fraction, cell fraction)?
Expected (written before execution):
1. the imaginary part of the Tower is also read by the last contact, as a sine of the cell fraction;
2. the real part of the integrated channel (`Tower/(ρ+1)`) is a combination of the real part and the imaginary part
   of the Tower, with weights `β+1` and `T`, over the squared norm of `ρ+1`: the integrated channel reads the cell fraction
   with its own angle delay (arctangent of `T/(β+1)`), different for the zero and for the mirror;
3. the real part of the primitive of the pair at `x` is `−2m·x` times the sum of the two integrated readings; it is
   therefore read entirely by the contacts of the two members;
4. the window balance (E433) is written in real part: arithmetic content of the window − real part of the complement
   = edge effect read by the contacts at the two edges.

## Protocol
1. Pre-register (commit) before the first compilation.
2. TDD probes in `BoundaryContactProbe_SCRATCH.lean` (unversioned, deleted after capture; exact outputs in
   `logs/probe_attempt*.txt`).
3. Isolated module `Terminal/BoundaryContactReading.lean` (not added to `RHV6Fresh.lean`): points 1–4.
   If the compiler asks for more than the objects listed, record the exact goal and do not insist.
4. At most two compilation attempts for the module (`logs/lean_attempt{1,2}.txt`); no hypothesis posed;
   no `sorry`; `lake build RHV6Fresh` green afterwards.

## Planned probe
- S1: "complement silent on the window, and both edges are contacts of the zero (cell fraction zero)
  ⟹ False" — expected: no contradiction; the compiler leaves "arithmetic content of the window = combination
  of the values at the contacts of the zero and of the readings of the mirror at the two edges".

## Objects reused
`towerRe`, `towerValue_polar`, `towerRe_from_lastContact`, `height_mul_log_eq`, `contactRealValue`, `contactAt_pos`,
`norm_mk_pos`, `integratedTower_eq_geometric_div`, `pairPrimitive`, `pair_complement_series_balance`,
`remainderIncrement_series_arithmetic`, Mathlib `Complex.div_re`, `Real.sin_add_int_mul_pi`, `Real.cos_add_int_mul_pi`.
