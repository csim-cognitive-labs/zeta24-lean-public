# RHV6Fresh: Lean master document

> Condensed English master document (current state and latest module only). The complete French master with the full history is `RHV6final_STRATEGIE_LEAN.md`.

State: 15 November 2026. Author: Charles S. All paths are relative to `formalization/RHV6Fresh/` unless stated otherwise.

## 1. Status

**What the build compiles.** `lake build RHV6Fresh` (the default target) was reproduced in the public repository on 15 November 2026 and ended with "Build completed successfully (9064 jobs).", `EXIT=0`. The full log is `experiments/audit_semantique/build_public_20261115.txt`. The Mathlib dependency is pinned to revision `51e6992efd06126df61a496bebf8f49482a4e129`.

**What it does not prove.** The Riemann Hypothesis is not proved. The only theorem whose conclusion is `RiemannHypothesis` is `riemannHypothesis_terminal` in `RHV6Fresh/Terminal/DemonstrationChain.lean`. It takes as a hypothesis `ExpectedFrequencyRises`, and the same file proves `expectedFrequencyRises_iff_riemannHypothesis`: the hypothesis is equivalent to RH. The terminal theorem is therefore conditional and is declared as such; it is a compiled reduction of RH to that hypothesis, not a proof of either.

**Axioms.** `#print axioms` on both `RHV6Fresh.riemannHypothesis_terminal` and `RHV6Fresh.expectedFrequencyRises_iff_riemannHypothesis` reports exactly `[propext, Classical.choice, Quot.sound]` (the three standard Lean axioms), with no `sorryAx`. No `axiom` declaration is added anywhere in the sources.

**What the build does not compile.**
- The optional rectangle certificates for zeta at heights 22 and 28 and the checks that depend on them (target `RHV6FreshCertificates`, not rebuilt in the 15 November log).
- The isolated modules (section 5), which are compiled one by one outside the main import closure.
- The PNTPort and RhGapPort ports (section 6).

## 2. Layout of the library

Counts were recomputed on 16 November 2026 from the sources.

- Total `.lean` files under `RHV6Fresh/` (library directory): `find RHV6Fresh -name '*.lean' | wc -l` gives **560**.
- Root file `RHV6Fresh.lean`: 200 `import` lines (`grep -c '^import' RHV6Fresh.lean`). Its import closure inside the library, computed by following `import RHV6Fresh.*` lines transitively, is **230 modules** including the root (229 plus the root). The closure also reaches modules of `rhv3_lean`.
- Declarations at line start under `RHV6Fresh/` (`grep -rhE '^(theorem|lemma)'`): **22,841** theorems and lemmas, of which 20,461 under `Terminal/`; **1,345** definitions, structures, abbreviations and inductive types (`grep -rhE '^(noncomputable def|def|structure|abbrev|inductive)'`). These counts include the third-party ports and the isolated modules.

| Path under `RHV6Fresh/` | Files | Role |
|---|---|---|
| `Foundation/` | 2 | Base facts on zeta (`ZetaReflect.lean`: reflection; contains proofs adapted from third-party code, see section 6). |
| `Tower/` | 7 | The Tower of a zero: true, proper, inverted and reflected towers, canonical origin. |
| `Direct/` | 7 | Direct counting objects: mirror and state counts, reached members, raccords, pivot cell, pair towers. |
| `Voyage/` | 3 | Progression from zero to zero and fiber successor. |
| `Grammar/` | 2 | Prime grammar (`Mod6Rigidity.lean`, `ExpectedMinimum.lean`). |
| `Terminal/` | 393 (284 directly in the folder, plus `ZetaBox/` 9, `ZetaBox22/` 44, `ZetaBox28/` 56) | The terminal development: passages between consecutive zeros, regimes, engaged state, the single chain `DemonstrationChain.lean`, and all later modules. `ZetaBox22/` and `ZetaBox28/` hold the heavy rectangle certificates. |
| `Zeta23Port/` | 134 | Third-party port (Apache 2.0): Chebyshev, Riemann–von Mangoldt, Mertens, Euler–Maclaurin. |
| `PNTPort/` | 9 | Third-party port (Apache 2.0): prime number theorem consequences. |
| `RhGapPort/` | 1 | `PrimesDetermineZeros.lean`, a port of the author's own internal package `rh_gap_criterion` (absent from this public repository). |
| `Audit.lean`, `CleanTerminal.lean` | 2 | Top-level files in the library directory. |

Sibling package `../rhv3_lean/` (Lean library `RHV3Lean`, plus `Certification`): 168 `.lean` files (`find ../rhv3_lean -name '*.lean' | wc -l`). It holds the base objects used by `RHV6Fresh` through `import RHV3Lean.*`, for example `TZeroPassage` (`RHV3Lean/Objects/Passage.lean`).

Split of the library files by import closure of `RHV6Fresh.lean`: 229 library modules are in the closure (Terminal 201, Direct 7, Tower 7, Voyage 3, Grammar 2, Foundation 2, Zeta23Port 5, CleanTerminal 1, Audit 1); the other 331 files are not (Terminal 192, Zeta23Port 129, PNTPort 9, RhGapPort 1).

## 3. Build and reproduction

- Toolchain: `leanprover/lean4:v4.33.0-rc2` (`lean-toolchain` in both `RHV6Fresh/` and `rhv3_lean/`).
- Mathlib: git dependency pinned by exact revision `51e6992efd06126df61a496bebf8f49482a4e129`, declared in `../rhv3_lean/lakefile.toml`. `RHV6Fresh` reaches `rhv3_lean` by the relative path `../rhv3_lean` (`lakefile.toml`, `[[require]] name = "rhv3_lean"`). Do not move either folder.
- Lake options in `lakefile.toml`: `pp.unicode.fun = true`, `relaxedAutoImplicit = false`, `weak.linter.mathlibStandardSet = true`.
- Targets: `RHV6Fresh` (default, `globs = ["RHV6Fresh"]`) and `RHV6FreshCertificates` (optional, imports `Terminal/FirstThreeZerosCertified`; very expensive).

```bash
cd formalization/RHV6Fresh
lake update                          # resolves Mathlib and dependencies at the pinned revision
lake exe cache get                   # if available: precompiled Mathlib .olean files
lake build RHV6Fresh                 # default target
lake build RHV6FreshCertificates     # optional: certificates for rectangles 22 and 28
```

The `.lake/` directories are not versioned; without the Mathlib cache the first build is very long. There is a single build command for the main library.

## 4. The terminal chain in words

The unique chain is `RHV6Fresh/Terminal/DemonstrationChain.lean`, imported by `RHV6Fresh.lean`. Every name below was checked with `grep` in the sources.

**Base.** `RiemannHypothesis` is Mathlib's definition; `riemannHypothesis_iff_strip` (`Terminal/RiemannHypothesisDefinition.lean`) shows it equals "every zero of zeta in the open strip has real part 1/2". A zero passage `TZeroPassage` goes from one member to the next member of the canonical enumeration of zero members (defined in `rhv3_lean`); `VerticalPassage` is in `Terminal/RegimeChange.lean`, `HorizontalMirrorRealization` in `Terminal/HorizontalExclusion.lean`.

**Step 1, initial count.** `no_zero_at_height_fifteen` and `upperCountWithMultiplicity_fifteen` (`DemonstrationChain.lean`): no nontrivial zero at height 15, and the counting function gives 1 below it, so the first zero is the canonical first zero. The finite numerical lemmas rely on the certificates of `Terminal/ZetaBox/`, imported by the chain.

**Step 2, anchor.** `anchor_canonical_one`: the first canonical zero has radial position 1/2 (on the line); `anchor_mirror_eq_self`, `anchor_bottom`, `anchor_dominates_onLine` (same file).

**Step 3, the single premise.** `ExpectedFrequencyRises`, defined in `DemonstrationChain.lean` as: for every passage `p`, `rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember`. In words, the frequency of the next signal expected by the primes is strictly higher than the current one. It is the one remaining obligation and it is never stated through the radial position. Consequences under it: `horizontalMirror_excluded_of_expectedFrequency`, `authentic_engaged_cascade_forbids_insertion`, and `radius_premise`.

**Step 4, from the premise to RH.**
- `canonical_onLine_of_history_conservation` and `universal_captivity_of_all_onLine` (`Terminal/AuthenticPassageProfile.lean`): strong induction along the canonical enumeration, then universal captivity of the zeros on the line.
- `riemannHypothesis_of_captivity_onLine` (`Terminal/FirstGainPremise.lean`).
- Assembly: `riemannHypothesis_terminal (hDemand : ExpectedFrequencyRises) : RiemannHypothesis`, and `expectedFrequencyRises_iff_riemannHypothesis : ExpectedFrequencyRises ↔ RiemannHypothesis` (the reverse direction uses `passage_height_lt_of_onLine` and `thm_zeroRadialPosition_half_of_riemannHypothesis`).

**Consequences of the premise recorded in the chain** (all take `hDemand : ExpectedFrequencyRises`): `regime_persists`, `regime_conserved` (gives `PNoRegimeChange`), `height_progression`, `radial_conservation_authentic`, `radial_conservation_engaged`, `counting_extension_all`.

**Equivalences with RH that are compiled elsewhere** (each is a characterization, not a proof):
- `PNoRegimeChange` (no passage chain mixes a vertical and a horizontal passage): `noRegimeChange_iff_riemannHypothesis`, `Terminal/NoRegimeChange.lean`.
- `riemannHypothesis_iff_noLowerSide`, `Terminal/ReadingArithmetic.lean`.
- `mirror_domination_premise_iff_riemannHypothesis` and `radius_premise_iff_localRaccord_premise`, `DemonstrationChain.lean`.
- `heightProgression_of_horizontalExclusion`, `Terminal/HorizontalExclusion.lean`.
- `onLine_beta_eq_previous` (`Terminal/OnLineBetaEqPrevious.lean`): once an on-line member is reached by a vertical passage with positive height, the next real part is the same; it carries explicit hypotheses and does not produce the first on-line member.

**Arithmetic bridge.** `zeta_generated_by_primes` (`Terminal/ZetaParameters.lean`) states that the parameters of zeta are generated by the primes. `Terminal/GeneratedFrequency.lean` and `Terminal/PrimeGrammarQuantitative.lean` (the latter importing `Zeta23Port.Chebyshev`) are in the main closure.

## 5. Isolated modules and the latest module

**Rule.** Isolated modules are modules written for experiments that are not imported by `RHV6Fresh.lean`. They are never added to `RHV6Fresh.lean`, so they cannot change the main build. Each is compiled on its own and its logs are kept in the `attempts/` folder of its experiment folder. Heavy certificates are likewise outside the default target and belong to the optional target `RHV6FreshCertificates`. The 331 library files outside the import closure (section 2) comprise the third-party files not reached by the main closure and 192 `Terminal/` files, among them isolated modules such as `FrequencyCap`, `ThreeZeroWindow`, `LogGapsTheorem`, `MeetingRegimeFinite` and `TentBreakObligation`. These modules carry no hypothesis, no axiom and no `sorry`.

**Latest module: `RHV6Fresh/Terminal/TentBreakObligation.lean`** (167 lines, experiment E476, folder `experiments/E476_TentBreak/`). It imports `CellAreaTent` and `PairBreakAtPrime`, is not imported by `RHV6Fresh.lean`, and contains ten theorems, each followed by a `#print axioms` line. Compile record: attempt 1 (`attempts/build_attempt1.txt`) ended with `EXIT=1` on a single error (the pattern of `Int.fract_fract` was not found because `cellFraction` was not unfolded); attempt 2 (`attempts/build_attempt2.txt`) ended with "Build completed successfully (9109 jobs).", `EXIT=0`, and every statement reports `[propext, Classical.choice, Quot.sound]`.

Setting: for a Tower with real part `β` and height `T`, the contacts are the points `contactAt β T k`, and `cellFraction β T x` is the relative position `f` of a real `x > 0` inside its cell. `breakTentWeight β T x` is the value at `x` of the tent function of the cell containing `x`. The ten statements:

1. `breakTentWeight_eq` (H1): the tent weight equals `e^{π/T} · x · (1 − e^{−π f/T})`.
2. `breakTentWeight_prev_eq` (H1): in the tent of the previous cell, `x` lies on the descending branch, and the tent value is `x (e^{π/T} e^{−π f/T} − 1)`.
3. `breakTentWeight_nonneg`: the tent weight is nonnegative.
4. `break_amplitude_reads_tent` (H2): the amplitude paid at the last contact before `x`, `|contactRealValue β T (lastContactBefore β T x)|`, equals `x^β (1 − w/(e^{π/T} x))^β / ‖β + iT‖`, a function of the tent weight `w`.
5. `localGrammarTerm_break_split`: for an integer `q` of the double cell, the local grammar term splits into the break weight `Λ(q) · tent(q)`, plus the sum of the other terms, minus the explicit area term `e^{π/T}(1 + e^{π/T}) · (cell length)² / 2`.
6. `tent_difference_eq_sawtooth` (H3): the difference of the two tents containing `x` is the sawtooth `(1 + e^{π/T}) x − 2 C_{k+1}`, where `C_{k+1}` is the next contact.
7. `alternating_break_weight` (H3): in the alternating sum, the break at `x` in the cell of rank `j` of the window weighs `(−1)^j ((1 + e^{π/T}) x − 2 C_{k+1})`.
8. `sawtooth_pos_iff` (H3): that weight is positive exactly when `2 e^{π/T} e^{−π f/T} < 1 + e^{π/T}`, that is, when `x` is beyond the neutral point of the cell.
9. `pair_breakTentWeight_eq_iff` (H4), for `0 < β < 1`: the mirror (real part `1 − β`) gives the same `x` the same tent weight as the Tower if and only if `β = 1/2`.
10. `pair_breakTentWeight_sub` (H4): `w(1−β) − w(β) = e^{π/T} x (e^{−π f_β/T} − e^{−π f_{1−β}/T})`.

Scope: these are identities and an equivalence about weights. The module states no contradiction and does not bear on RH or on the terminal chain; it records an obligation of form (statement 9). The accompanying Python twin and its result are in `experiments/E476_TentBreak/`.

## 6. Third-party code and licensing boundaries

Project licence: proprietary, strict non-commercial ("Zeta24-Lean Research Licence", file `LICENSE`; copyright in `COPYRIGHT.md`; INPI Soleau envelope DSO2026044645). Third-party components below are under Apache 2.0, are not covered by that licence, and keep their own notices (`THIRD_PARTY_NOTICES.md`).

| Component | Location | Origin | Used by the active build `lake build RHV6Fresh`? |
|---|---|---|---|
| Zeta23Port, 134 `.lean` files | `RHV6Fresh/Zeta23Port/` | Copy of `anthropics/formal-math`, directory `zeta23`, revision `fbdc36bb` (only imports renamed). Part `FromPNTPlus/` derives from PrimeNumberTheoremAnd and Mathlib. | Yes, 5 modules in the closure: `Chebyshev`, `Defs`, `Hypotheses`, `FromPNTPlus.Mertens`, `FromPNTPlus.EulerMaclaurin`, reached through `Terminal/PrimeGrammarQuantitative.lean`. |
| PNTPort, 9 `.lean` files | `RHV6Fresh/PNTPort/` | Port of `AlexKontorovich/PrimeNumberTheoremAnd`, revision `127b50e3` | No. Imported only by `Terminal/LogGapsTheorem.lean`, which is outside the closure of `RHV6Fresh.lean`. |
| P4Port and PerronPort | `rhv3_lean/RHV3Lean/Objects/P4Port/` and `.../PerronPort/` (and the `rh_gap_criterion` tree, absent here) | Ports of PrimeNumberTheoremAnd, revision `67397938` | Only for the `RHV3Lean` modules reached by the import closure. |
| Mixed file | `RHV6Fresh/Foundation/ZetaReflect.lean` | Author's file with one proof adapted from `zeta23/ZetaReflect.lean` | Yes. |
| Odlyzko tables | `experiments/data/` | A. M. Odlyzko, zeros tables | Experiments only, not Lean. |

`RhGapPort/PrimesDetermineZeros.lean` is the author's own port, not third-party; it is outside the closure. Lean 4 and Mathlib are external dependencies (Apache 2.0), not versioned here.

## 7. Lean rules

1. No `sorry`, no `admit`, no added axiom. Check: a search of the sources for `sorry` or `admit` as tokens, and for lines starting with `axiom`, finds none in code (the words appear only in comments). Axioms are those reported by `#print axioms`.
2. The compiler decides. No statement is accepted on the strength of a text, a script or an unrun check; no fabricated output, and no compiler error replaced by a written analysis.
3. No duplicated names: `grep` for a name before declaring it.
4. `lake build RHV6Fresh` must stay green after every change; a break is fixed immediately.
5. A definitive module is pre-registered before it is compiled (statements, and the outcomes that count as success or failure).
6. Two compile attempts at most per module; each attempt and its exact output are logged in `attempts/` of the experiment folder, whatever the result.
7. Isolated modules are not added to `RHV6Fresh.lean`; heavy certificates go to `RHV6FreshCertificates`.
8. `Terminal/DemonstrationChain.lean` is never altered without the author.
9. Only one chain file and one build command: no separate targets, no probes, no branches.
10. A name removed from the code is not cited as existing; any new citation of a name is verified by `grep` against the sources.
