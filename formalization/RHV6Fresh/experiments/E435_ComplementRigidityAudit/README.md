# E435 — Exhaustive audit of the rigidity of the complement at the shared prime (2026-11-04)

> Français : [README.fr.md](README.fr.md)

Compilation and audit-only experiment (no numerical measurement; no twin required). Author's mission
(2026-11-04): "determine whether the existing theorems impose on the collective complement an independent constraint
incompatible with the drift of the OFF pair and of its mirror at the arithmetic meeting point". No new measurement,
no new model, no premise equivalent to RH. Do not restart E429, do not rewrite E434, do not invent a
conservation of the transport.

## Question posed (before any compilation)
Does the exact arithmetic reconstruction at the meetings impose on the complement (`packetᶜ` of the carrier `C`, mirror
case) a rigidity already proved in the corpus that makes the drift of the OFF Tower and of its mirror impossible?

## Hypotheses admitted
Only a carrier `C : OffCarrier` (first authentic low zero, canonical on-line predecessors) and the mirror case
`h : C.outgoing.zLaterMember = (mirrorMember C.zero).1`, as in E432–E434. No other hypothesis; probes that add
one (bound, silence) must declare it and feed no theorem of the module.

## Established results reused (checked in their exact Lean form before use, see RESULTS.md §1)
`pair_complement_series_balance`, `pair_window_re_balance`, `pairPrimitive_re_from_contacts`,
`integratedTower_re_from_lastContact`, `towerIm_from_lastContact`, `packetIncrement_series_telescopes`,
`localPacket_pair_eq`, `channelPrimitive_packet_eq`, `exactRemainder_eq_packet_add_complement`,
`smoothedRemainder_eq_tsum_residueTerm`, `channel_eq_packet_add_complement`, `break_realized_by_high_frequencies`,
`norm_packetIncrement_finset_le`, `mirror_pair_exponent_le(_remainderExponent)`, `off_signature_lifts_remainderExponent`,
`infinite_complement_closes`, `acquired_exponent_not_below_mirror`, `riemannHypothesis_iff_remainderExponent_eq_half`,
`exists_offCarrier_of_not_riemannHypothesis`, `no_offCarrier_of_riemannHypothesis`, `norm_mirror_primitive_term`,
`norm_zero_primitive_term`, `inversion_height`, `inversion_radial`, `mirror_contacts_coincide_iff`,
`radial_of_contact_value_ratio`, `mirror_amplitude_ratio_tendsto`, `detour_arithmetic_factor_ne_one`,
`detour_transport_product`, `detour_defect_eq_memberStep_product`. No proof redone.

## Protocol
1. Pre-register (this file, commit) before the first compilation.
2. Exhaustive inventory (RESULTS.md §1): all theorems of the corpus bearing on the complement or its variations,
   with name, file, statement, hypotheses, domain, conditional/unconditional, dependence on RH, reach over an
   infinite family of meetings; nature (decomposition identity / upper bound / junction equality / asymptotic).
3. TDD probes in `ComplementRigidityProbe_SCRATCH.lean` (unversioned, deleted after capture; exact outputs
   in `logs/probe_attempt*.txt`).
4. Isolated module `Terminal/ComplementRigidityAudit.lean` (not added to `RHV6Fresh.lean`), at most two compilation attempts
   (`logs/lean_attempt{1,2}.txt`), no hypothesis posed, no `sorry`, axioms displayed;
   `lake build RHV6Fresh` green afterwards.

## Planned probes and expectations (written before execution)
- **S1 — Exact balance by contacts.** Real part of the complement over a window `[a, a+m]` = sum of the von
  Mangoldt weights − real variation of the background step − edge effect, the edge effect being read at the four points
  `a, a+1, a+m, a+m+1` by the contacts of the two members (signed values, cell fractions, angle delays
  kept; no modulus, no term dropped). Expected: compiles by rewriting `pair_window_re_balance` and
  `pairPrimitive_re_from_contacts`.
- **S2 — Transport to the series of meetings.** For any sequence of windows, the sum of the window sums of the
  complement is the sum of the differences of its local steps at the edges; two consecutive windows concatenate;
  the local step of the complement at any `N ≥ 2` is the exact remainder minus the step of the pair; at the level of primitives,
  complement = `x·smoothed remainder(x) − primitive of the pair(x)` for all `x > 1`. Expected: compiles with no bound; the
  series of windows carries no information beyond the pointwise sequence of the complement.
- **S3 — Independent constraint.** Application of the only rigidity theorems found: (i) pointwise lower bound
  of the break carried by the complement of the pair (instance of `break_realized_by_high_frequencies`
  on the finite family of the four members); (ii) exponent of the remainder ≥ `1/2 + δ`; (iii) no bound of the remainder below
  `1/2 + δ` is compatible with `C`; (iv) a growth bound of the complement alone at exponent `1 + θ` transfers
  to the smoothed remainder only the exponent `max(θ, 1/2 + δ)`. Expected: (i)–(iii) direct instances; (iv) an
  upper bound by the four norms of the members of the primitive.
- **S4 — OFF contradiction.** From `C`, `h` and the results of S1–S3 alone, attempt `False`. Expected (written before
  execution): no contradiction; the goal `False` remains with, in context, the exponent of the remainder ≥ `1/2 + δ` and
  the acquired exponent `1` only. Variant: complement bounded at exponent `1 + θ`, `θ < 1/2 + δ` ⟹ `False`:
  expected, the goal remains (the transfer gives the remainder at exponent `1/2 + δ`, not strictly below).

## Criteria (a single category)
A compiled closure; B new unconditional reduction of the link; C frontier equivalent to RH, equivalence
compiled; D no independent rigidity, missing property named. Expected: D, with the form C of the missing
property (`(OffCarrier → False) ↔ remainderExponent = 1/2`) compiled.
