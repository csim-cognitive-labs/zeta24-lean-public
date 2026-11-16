# Third-party components

> Français : [THIRD_PARTY_NOTICES.fr.md](THIRD_PARTY_NOTICES.fr.md)

The components listed here are NOT covered by the project's non-commercial licence; their Apache 2.0 permissions, including commercial ones, remain.

This repository contains or uses code and data that are not the author's work and that the copyright of [COPYRIGHT.md](COPYRIGHT.md) does not cover. The original notices are kept intact in the relevant folders. In case of doubt, the original notice of the file prevails.

## 1. Components included in the repository

| Component | Path | Exact origin | Licence | Copyright holder | Use in the project |
|---|---|---|---|---|---|
| Zeta23Port (134 `.lean` files, plus `LICENSE`, `NOTICE`, `PROVENANCE.md`) | `formalization/RHV6Fresh/RHV6Fresh/Zeta23Port/` | Copy of `anthropics/formal-math`, directory `zeta23`, revision `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (import closure of `Zeta23.Final` and `Zeta23.FinalMult`). Only imports are renamed (`Zeta23.*` becomes `RHV6Fresh.Zeta23Port.*`); the content is unchanged. One part (`FromPNTPlus/`) itself derives from PrimeNumberTheoremAnd and Mathlib, with their notices. | Apache 2.0 (`LICENSE`, `NOTICE` of the folder) | "Copyright (c) 2026 Anthropic, PBC"; for `FromPNTPlus/`: also the contributors of PrimeNumberTheoremAnd and Mathlib, according to the file headers | See section 3 |
| PNTPort (9 `.lean` files, plus `LICENSE`, `PROVENANCE.md`) | `formalization/RHV6Fresh/RHV6Fresh/PNTPort/` | Port of `AlexKontorovich/PrimeNumberTheoremAnd`, revision `127b50e33f6033e2147921167a117af96d9ba4ea` (import closure of `chebyshev_asymptotic`). Mechanical transformations listed in `PROVENANCE.md` (`blueprint` annotations removed, imports renamed, porting fixes marked `-- port :`). | Apache 2.0 (`LICENSE` of the folder) | The contributors of PrimeNumberTheoremAnd (and of Mathlib for the three `Mathlib/...` files), according to the headers | See section 3 |
| P4Port (66 files per tree) | `formalization/rh_gap_criterion/RhGapCriterion/P4Port/` and `formalization/rhv3_lean/RHV3Lean/Objects/P4Port/` | Ports of `AlexKontorovich/PrimeNumberTheoremAnd`, revision `6739793850d3eaa031e3543ed72d7f026f8080f5` (mostly in `IEANTN/` and Hadamard complex analysis) | Apache 2.0 (mention "Released under Apache 2.0 license" in the headers) | Matteo Cipollina (50 files per tree), James Sundstrom, Stefan Kebekus, Robby Sneiderman, other contributors according to the header of each file | Used by the `rh_gap_criterion` tree and by `rhv3_lean` (not compiled in the active `RHV6Fresh` build, except what `RHV3Lean` imports) |
| PerronPort | `formalization/rh_gap_criterion/RhGapCriterion/PerronPort/` and `formalization/rhv3_lean/RHV3Lean/Objects/PerronPort/` | Ports of `AlexKontorovich/PrimeNumberTheoremAnd`, revision `6739793850d3eaa031e3543ed72d7f026f8080f5` | Apache 2.0 | According to the header of each file (for example Michael Stoll, Lawrence Wu, Abby J. Goldberg, Mario Carneiro, Heather Macbeth) | Same as P4Port |
| `ZetaZeroCountingCrude.lean` | `formalization/rh_gap_criterion/RhGapCriterion/` and `formalization/rhv3_lean/RHV3Lean/Objects/` | File bearing the header "Copyright (c) 2026 Robby Sneiderman", Apache 2.0 | Apache 2.0 | Robby Sneiderman | Same as P4Port |
| Odlyzko tables | `formalization/RHV6Fresh/experiments/data/odlyzko_zeros6_2001052.txt` (and `odlyzko_zeros1_first300.txt`, `odlyzko_zeros1_first5000.txt`) | A. M. Odlyzko, "Tables of zeros of the Riemann zeta function", file `zeros6` (the first 2,001,052 zeros), `https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros6`; see `odlyzko_zeros6_2001052.PROVENANCE.md` (SHA-256 included) | No licence was granted to us by the author of the tables; use of data published by their author | Andrew Odlyzko | Experiment data. **These tables are not the property of the author of this repository** |

The files of P4Port, PerronPort and `ZetaZeroCountingCrude.lean` received no header from the author and keep their original notice. The two files `PerronPort/Audit.lean` and `PerronPort/ZetaBoundsAudit.lean` of `rh_gap_criterion` are by the author and carry the author's header.

## 2. Adapted (mixed) files

These files are the author's work but contain proofs adapted from `anthropics/formal-math` (subtree `zeta23`, file `Zeta23/ZetaReflect.lean`, Apache 2.0, Copyright (c) 2026 Anthropic, PBC). They carry the author's header with the mention "adaptations" and their original provenance, left in place.

- `formalization/RHV6Fresh/RHV6Fresh/Foundation/ZetaReflect.lean`
- `formalization/rh_gap_criterion/RiemannHypothesisProof/ZetaReflection.lean`
- `formalization/rh_gap_criterion/RiemannHypothesisProof/ZeroSymmetries.lean` (one proof, `FunctionalMirrorForZeroIsZeroNonTrivial`, adapted)

The file `rh_gap_criterion/RhGapCriterion/ScientificRebuild20260829/TrustedZetaSeamBridge.lean` mentions the architecture of `zeta23` as an idea only; it reproduces none of its code (it is its own statement) and remains a file of the author.

## 3. Use in the active build (`lake build RHV6Fresh`)

Direct importers (in `formalization/RHV6Fresh/RHV6Fresh/`, outside the ports):

- Zeta23Port: `Terminal/PrimeGrammarQuantitative.lean` (imports `RHV6Fresh.Zeta23Port.Chebyshev`) and `Terminal/FrequencyCap.lean` (imports `Zeta23Port.RvM.Statement`, `RvM.NcountWindow`, `GammaFacts.Complete`).
- PNTPort: `Terminal/LogGapsTheorem.lean` (imports `RHV6Fresh.PNTPort.Consequences`).

Transitive importers (measured on the `RHV6Fresh.*` import graph): 100 own modules reach Zeta23Port (including `RHV6Fresh.lean`); 33 own modules reach PNTPort (via `LogGapsTheorem`).

Exact chain up to `RHV6Fresh.lean` (the main library, target `RHV6Fresh`):

- `RHV6Fresh.lean` imports `RHV6Fresh.Terminal.GeneratedFrequency`, which imports `RHV6Fresh.Terminal.PrimeGrammarQuantitative`, which imports `RHV6Fresh.Zeta23Port.Chebyshev`. `RHV6Fresh.lean` also imports `PrimeGrammarQuantitative` directly.
- The import closure of `RHV6Fresh.lean` (230 modules) contains 5 Zeta23Port modules: `Chebyshev`, `Defs`, `Hypotheses`, `FromPNTPlus.Mertens`, `FromPNTPlus.EulerMaclaurin`. It contains 12 own modules that reach Zeta23Port: `PrimeGrammarQuantitative` and, above it, `GeneratedFrequency`, `CascadeContinuation`, `DemonstrationChain`, `FrequencyCascadeStability`, `GapDemandStability`, `InterlacingLink`, `LowNextZeroSignatures`, `OnRegimeStabilityPackage`, `SynchronizationMatrix`, `WindingReadingChain`.
- `FrequencyCap` and `LogGapsTheorem` are not in this closure; neither are their importers (for example `ThreeZeroWindow`, `MeetingRegimeFinite`). PNTPort is therefore not compiled by `lake build RHV6Fresh`; the library is declared with `globs = ["RHV6Fresh"]` and the PNTPort `PROVENANCE.md` says so.
- The `rhv3_lean` tree (imported by `RHV6Fresh` via `RHV3Lean.*`) contains P4Port and PerronPort; they are compiled only for the `RHV3Lean` modules reached by the import closure.

## 4. Dependencies not versioned here

- Lean 4 (`https://github.com/leanprover/lean4`), toolchain `leanprover/lean4:v4.33.0-rc2`: Apache 2.0, Copyright Lean FRO, LLC and contributors.
- Mathlib (`https://github.com/leanprover-community/mathlib4`), revision pinned in `formalization/rhv3_lean/lakefile.toml`: Apache 2.0, Copyright the Mathlib contributors.
- Mathlib dependencies (batteries, aesop, Qq, ProofWidgets4, import-graph, LeanSearchClient, plausible: Apache 2.0; Cli: MIT, Copyright (c) 2021 Marc Huisinga), fetched by Lake and not included here.

## 5. Note on names in historical audits

The names "zeta23", "Zeta23", "Zeta23Port" and "anthropics/formal-math" that appear in the audits and historical documents of this repository designate this third-party dependency (section 1) and nothing else. The author claims no right over it.
