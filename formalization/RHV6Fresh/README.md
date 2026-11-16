# RHV6Fresh: active build

> Français : [README.fr.md](README.fr.md)

A `lake` project (`lakefile.toml`, library `RHV6Fresh`, `defaultTargets = ["RHV6Fresh"]`). It depends only on `rhv3_lean` (`require`, path `../rhv3_lean`) and, through it, on Mathlib.
Toolchain: `leanprover/lean4:v4.33.0-rc2` (`lean-toolchain`). Some historical documents and experiment notes in this folder remain in French.

## Status (as of 15 November 2026)

RH is **not proved**. The last complete `lake build RHV6Fresh` log read (`experiments/E476_TentBreak/logs_lake_build_full.txt`,
14 November 2026) ends with "Build completed successfully (9064 jobs)", exit code 0, zero errors; no Lean file has changed since
(commit `14af9d52`). We did not rerun the build for this update. The former mention of a failure in
`Terminal/DemonstrationChain.lean` line 856 is outdated: on 28 October 2026 (commit `1c2ef553`) the terminal goal became the named
hypothesis "rise of the expected frequency". A green build does not prove RH: `riemannHypothesis_terminal` (same file) takes this
hypothesis, which `expectedFrequencyRises_iff_riemannHypothesis` proves equivalent to RH; it is therefore conditional. Its axioms are
`propext`, `Classical.choice`, `Quot.sound`. No declared axiom, no `sorry`, no `admit` in the sources.
`scripts/status.sh` reads `experiments/audit_semantique/main_build_error_20261005.txt`, dated 27 October 2026: it still shows a failure,
and this log is outdated until `scripts/status.sh --build` is rerun.

## Build

```bash
cd formalization/RHV6Fresh
lake build RHV6Fresh          # a single command; ~1.5 min incremental if .lake/ exists
scripts/status.sh             # prints the output of the last build (STATE, BUILD, errors, analysis)
scripts/status.sh --build     # reruns lake build RHV6Fresh, rewrites the output, then prints it
```

`status.sh` reads `experiments/audit_semantique/main_build_error_20261005.txt`; the analysis is in
`experiments/audit_semantique/main_build_error_analysis.md`, the state in `main_build_state.md`, and the
lock in `semantic_lock.md`.

## Where to read

- `RHV6Fresh.lean`: the root, which imports the chain (including `Terminal/DemonstrationChain.lean`).
- `RHV6Fresh/Foundation/ZetaReflect.lean`: port of third-party code under Apache 2.0, see `THIRD_PARTY_NOTICES.md` at the repository root.
- `RHV6Fresh/Terminal/` (393 `.lean` files): terminal chain, control and constraint modules.
- `RHV6Fresh/Zeta23Port/` (134, third-party Apache 2.0 code), `PNTPort/` (9, third-party Apache 2.0 code), `Tower/` (7), `Direct/` (7), `Voyage/` (3), `Grammar/` (2), `Foundation/` (2), `RhGapPort/` (1); 560 files in `RHV6Fresh/RHV6Fresh/`, 662 in total under `RHV6Fresh/` with the experiments (recounted with `find`, excluding `.lake`).
- `experiments/` (200 subfolders): numerical experiments and probes, outside the build graph.
- `scripts/`: `status.sh`, `goal_dependencies.py` (theorem dependency graph), `raccord_check.py` (junction check).
- `archives/`: archives of earlier master documents and audits.
- Master documents (English, current state and latest attempt): `MASTER_SEMANTIC.md`, `MASTER_MATHEMATICAL.md`, `MASTER_LEAN.md`. Full French history: `RHV6final_STRATEGIE_SEMANTIQUE.md`, `RHV6final_STRATEGIE_MATHEMATIQUE.md`, `RHV6final_STRATEGIE_LEAN.md`
  (aligned with the code after the fact; in case of conflict with a compiled theorem, the master document is corrected).
- Audit: [AUDIT_SOLUTION_20261005.md](AUDIT_SOLUTION_20261005.md); semantic audit
  [AUDIT_SEMANTIQUE_RHV6Fresh.md](AUDIT_SEMANTIQUE_RHV6Fresh.md).

## Rules

- No `sorry`, `admit` or added axiom; no premise equivalent to RH in a theorem presented as unconditional.
- A theorem that depends on a hypothesis equivalent to RH is conditional, never "proved".
- Do not move this folder or `rhv3_lean` (lake relative paths).
- Full approach and constraints: [CLAUDE.md](../../CLAUDE.md) at the root.
- Ownership: © 2026 Charles S., Soleau envelope INPI no. DSO2026044645 (15 November 2026); see `COPYRIGHT.md` and `THIRD_PARTY_NOTICES.md` at the repository root.

## Lightened default build (2026-10-27)

`lake build RHV6Fresh` no longer compiles the rectangle certificates of bands 22 and 28 (`Terminal/ZetaBox22/*`,
`Terminal/ZetaBox28/*`, 100 files, several hours of CPU, up to 6.5 GB per file). Only the first band
(`Terminal/ZetaBox/*`, `N(15) = 1`, the anchor) remains in the default build. The controls `N(22) = 2`, `N(28) = 3`,
`first_two_zeros_control`, `first_three_zeros_control`, `first_three_members_geometry`, `low_zero_after_certified_band` and the
`FirstArrivalsAnchor` module are in the optional target `RHV6FreshCertificates`
(`Terminal/FirstThreeZerosCertified.lean`): `lake build RHV6FreshCertificates`. No theorem of the chain
consumes them; the height lower bound for a low member is now `low_member_above_15`. `ZetaBox30` (never imported) is
removed from the sources (git history kept).
