# E432 — The density → packet channel bridge: the surplus of the pair in the Tower channel (2026-11-04)

> Français : [README.fr.md](README.fr.md)

Compilation-only experiment (no numerical measurement; no twin required). Author's request: "ok continue",
after E431, whose probe S2 left the goal "exact remainder = packet of the pair" facing "nonzero surplus", with no compiled
bridge between the real density and the step of the smoothed channel of the packets.

## Question posed (before any compilation)
Does the step of the packet channel of the pair at the step of the break, written as the integral of its derivative (Tower terms),
carry the surplus of the pair with the same hyperbolic factor as the density, or is this surplus deformed?
Expected (written before execution): in the Tower channel, the two members are weighted by `1/ρ` (own amplitude and phase),
so that the surplus of the pair relative to the on-line twin equals the hyperbolic factor on the line
PLUS a deformation term proportional to the radial shift, of the form `(δ/ρ_L)·(Tower of the zero − Tower of the mirror)`.
Expected consequence: a sign change of the density does not cancel the surplus in the packet channel.

## Protocol
1. Pre-register (commit) before the first compilation.
2. TDD probes in `RaccordBridgeProbe_SCRATCH.lean` (unversioned, deleted after capture; exact outputs in
   `logs/probe_attempt*.txt`).
3. Isolated module `Terminal/PacketChannelBridge.lean` (not added to `RHV6Fresh.lean`):
   (a) `lineTerm` (Tower term of the line point) and the pointwise identity of the surplus of the pair in the
       Tower channel (hyperbolic factor + deformation);
   (b) derivative of the primitive of the four-member packet (case (a)): `−m·(Towers of the four members)`;
   (c) the local step of the packet on `[N, N+1]` (`N ≥ 2`) as the integral of this derivative (fundamental theorem);
   (d) if (a)–(c) pass: the surplus of the packet step relative to the on-line twin of the same multiplicities, as the
       integral of the hyperbolic factor plus the deformation.
   If the compiler asks for more than the objects listed, record the exact goal and do not insist.
4. At most two compilation attempts for the module (`logs/lean_attempt{1,2}.txt`); no hypothesis posed;
   no `sorry`; `lake build RHV6Fresh` green afterwards.

## Planned probe
- S1: "the surplus of the Tower channel vanishes at a sign change of the density" — expected: false; the
  compiler leaves a term in sine of the line phase `arctan(2T)` and the deformation.

## Objects reused
`zeroTerm`, `zeroTerm_hasDerivAt`, `explicit_term_derivative`, `residueTerm_conjIndex`, `packet_channel_four_of_mirror`,
`zeroPoint_eq_line_sub_shift`, `mirrorPoint_eq_line_add_shift`, `linePoint_im`, `channelPrimitive`, `stepAt`,
`localPacket`, `pair_gapTerm_signature` (for comparison), Mathlib `cpow_add/sub/def_of_ne_zero`, `ofReal_log`,
`integral_eq_sub_of_hasDerivAt`, `conjCLE`.
