# zeta24-lean — Lean 4 formalization around the Riemann Hypothesis

> Français : [README.fr.md](README.fr.md)

> **Public repository: a dated export (15 November 2026) with a fresh history of the private research repository `zeta24-lean`; the selection is documented in `PUBLICATION_SCOPE.md`.** The mentions of "HEAD", commits and logs below refer to the history of the private research repository, which is not reproduced here (the cited hashes therefore cannot be found in the `git log` of this repository).

> **State as of 15 November 2026 (HEAD `4d4114c6`).**
> **The Riemann Hypothesis (RH) is NOT proved.** This repository is an open research programme, not a proof.
> **Nothing is assumed**: no axiom declaration and no `sorry` or `admit` in the project's Lean sources (pattern search run on 15 November 2026 in `formalization/RHV6Fresh/RHV6Fresh` and `formalization/rhv3_lean`, excluding `.lake`), and no premise equivalent to RH is used in a theorem presented as unconditional.
> **What the build compiles.** Build reproduced in THIS public repository on 15 November 2026 (Mathlib dependency pinned to `51e6992efd06126df61a496bebf8f49482a4e129`, Mathlib cache downloaded): `lake update`, `lake exe cache get`, `lake build RHV6Fresh` end with "Build completed successfully (9064 jobs).", `EXIT=0`, from 19:15:15 to 19:49:58 UTC. Full log: `formalization/RHV6Fresh/experiments/audit_semantique/build_public_20261115.txt`. **This green build does not prove RH**: the only theorem whose conclusion is RH, `riemannHypothesis_terminal` (`formalization/RHV6Fresh/RHV6Fresh/Terminal/DemonstrationChain.lean`), takes as a hypothesis the "rise of the expected frequency" (`ExpectedFrequencyRises`), which `expectedFrequencyRises_iff_riemannHypothesis` (same file) proves equivalent to RH. It is therefore conditional, and it is declared as such. Axioms reported by `#print axioms` in this repository (exact output): `'RHV6Fresh.riemannHypothesis_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]` and `'RHV6Fresh.expectedFrequencyRises_iff_riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]`: the three standard Lean axioms (propositional extensionality, classical choice, quotients), no `sorryAx`.
> **What the build does not compile.** The rectangle certificates for ζ at heights 22 and 28 and the checks that depend on them are outside the default target (optional target `RHV6FreshCertificates`, not rebuilt in the log above). The isolated modules written since 29 October for experiments (for example `TentBreakObligation.lean`) are not imported by the root `RHV6Fresh.lean`; they were compiled individually, each with its logs in `attempts/` of the experiment folder.
> **A documentation discrepancy to be aware of.** `formalization/RHV6Fresh/scripts/status.sh` rereads a log dated 27 October 2026 that still shows a failure; that log is stale (the terminal goal was transformed on 28 October, commit `1c2ef553`). We report the state actually observed, not the one asserted by that script.

## 1. Ownership and repository

**Project, method, texts, code and discoveries: © 2026 Charles S. INPI Soleau envelope no. DSO2026044645, filed on 15 November 2026 (kept for ten years).** Full reference: national number DSO2026044645, filed with the INPI (online procedure) on 15/11/2026 at 18:14:32 UTC.

Licence: "Zeta24-Lean Research Licence — Proprietary, Strict Non-Commercial, version 1.0" (file `LICENSE`, English text first, original French text below it; the French text prevails in case of discrepancy). Proprietary licence for strictly non-commercial use; no redistribution of modified versions; every contribution is assigned to the author (see LICENSE art. 4g). Third-party components under Apache 2.0 are not covered by this licence. GitHub displays "No license" because the licence is custom and is not recognised in its list of standard licences. The copyright and notices are in `COPYRIGHT.md` at the root; the attributions for third-party code are in `THIRD_PARTY_NOTICES.md` at the root. The ported third-party Lean code (directories `formalization/RHV6Fresh/RHV6Fresh/Zeta23Port` and `formalization/RHV6Fresh/RHV6Fresh/PNTPort`, Apache 2.0 licence) remains the property of its authors and is not covered by this copyright. Their provenances are in the `PROVENANCE.md` files of those directories (copy of the zeta23 directory of the `anthropics/formal-math` repository, revision `fbdc36bb`; port from the `AlexKontorovich/PrimeNumberTheoremAnd` repository, revision `127b50e3`). The `RhGapPort` port reuses the author's internal package `rh_gap_criterion` (present in the private research repository, absent from this public repository).

Public repository: https://github.com/csim-cognitive-labs/zeta24-lean-public (export with a fresh history). The research repository `zeta24-lean` (split off on 25 October 2026 from the `neuro-symbolic-consensus` repository) remains private.

## Why this project is public: a message of fellowship

This project is disinterested. It was not published to sell anything, to make money, or to impose anything on anyone. It is public because we believe that artificial intelligence must benefit the whole world, and first of all those who have nothing: those who have no access to the great universities, the great laboratories, the great machines. The licence of this repository forbids all commercial exploitation for one reason only: so that what we have found is never locked behind a price, and remains readable, verifiable and usable by everyone, free of charge, for learning and for research.

This research team (one man, Charles S., and the artificial intelligences that work with him) will always share the little it has with everyone. It respects all peoples, all cultures, all traditions, all religions, and every human being on earth. We are earthlings, one single family. Each of us was created, whatever name each gives to the One who created us. There is no point in fighting or killing one another. Exchanging our knowledge brings us closer, and this is how people have always moved forward.

Mathematicians, since the dawn of time, have shared their knowledge: in Babylon and in Egypt, in India and in China, in Baghdad and in Córdoba, in Africa and in the Americas, and wherever someone has passed a proof on to another. None of these pages belongs to a single people. We humbly take our place in this long chain.

Whoever you are, wherever you come from, come and break bread with us. You are all welcome in our modest home. Whether you are a mathematician, a student, simply curious, self-taught, or just passing by, a question, a careful reading or a reported error is a gift.

To each and every one of you who reads these lines: peace, fellowship and blessing. May knowledge make you freer, closer to one another, and more human.

*Honesty above all: the Riemann Hypothesis is not proved, and this repository does not claim otherwise anywhere. We are sharing work in progress, with its limits, so that others can carry it further.*

## 2. Research team

**Author's statement.** The research was conducted by Charles S. with a team of artificial-intelligence assistants: Claude (Anthropic), notably Fable 5.1; Astra and ChatGPT 6.2 (OpenAI); Gemini and NotebookLM (Google).

The assistants executed, compiled, measured and recorded under the author's direction. The author set the questions, decided the orientations and rejected the drifts; sections 19 of the semantic master document (`formalization/RHV6Fresh/RHV6final_STRATEGIE_SEMANTIQUE.md`, in French) bear witness to this: orders, rectifications and prohibitions are recorded there with their dates (for example §19.9, §19.51, §19.63, §19.67, §19.85, §19.98, §19.108). We reproduce this statement; we have not verified it beyond these written traces.

## 3. Orientation and proof discipline

**Goal.** A Lean term of type `RiemannHypothesis` obtained without any assumed premise. The research starts from the arithmetic of the primes, their gaps, and the reconstruction formula through the zeros ρ = β + iT.

**Intended causality** (author, §19.20 and §19.80 of the master document): the primes and their exact gaps produce frequencies, through collective reconstruction from all the zeros; each zero defines a "Tower" whose "contacts" mark out the real axis; the meeting at the shared prime is defined by the grammar of the primes; the aim is to find the arithmetic constraint that this reconstruction imposes on a first off-line Tower (an "OFF" zero), a constraint that its contacts and those of its mirror cannot satisfy.

**Four degrees of certainty, never to be merged**: (1) a Lean theorem recompiled without `sorryAx`, with its axioms examined; (2) a conditional theorem, with hypotheses kept and classified; (3) an algebraic identity or a definitional reduction; (4) a numerical observation (deterministic "twin"). Rewriting a goal is not a mathematical reduction.

**Hierarchy.** The compiled theorem comes first; the numerical twin is used to measure, never to conclude; in case of conflict between a text and a compiled theorem, the theorem prevails.

**Author's orders in force** (sources: `CONTRIBUTING.md`, the three master documents `RHV6final_STRATEGIE_*.md` (in French), in particular the semantic master document, handover `formalization/RHV6Fresh/HANDOVER_20261107_LIGNE.md` (in French)):
- the contacts of a Tower read the radial position β, through the compiled tangential formulas; an interval of contacts is defined by the frequency AND the amplitude (§19.63, rectified on 4 and 7 November);
- a Tower is never tied to the exact position of a prime: the intervals between contacts are partial remainders of gaps, reconstructed collectively (§19.51, 6 November);
- the useful range for the arrival is β ≤ 1/2, never "every β in the open interval (0,1)" (§19.76);
- "equivalent to RH" is not an objection; admitting such a statement as a premise remains forbidden (§19.98, 13 November);
- frequency before height: the meeting point imposes a frequency, then a height;
- before any compilation or execution: a committed pre-registration, at most two compilation attempts, a deterministic twin for every figure, nothing fabricated.

## 4. Consolidated history

The rows before 26 October are carried over from the previous README. For each recent row: **C** = compiled, **M** = measured (twin), **R** = retracted or rejected.

| Phase | Problem pursued | Gains and revisions |
|---|---|---|
| P1–P4 / KVM8, RHV2–RHV3 | Grammar of gaps and alignment of the primes with ζ; statistical controls | Protocols and validation sets; statistical controls do not replace any analytic constraint. |
| July–August 2026, `tour10*` and E44 | Geometry of Towers, radius/contact, inversion of parameters | Consecutive contacts reconstruct T and β under the branch convention. |
| August–September, `rh_gap_criterion`, RHV4/RHV5, start of RHV6 | Prime events, passages, mirrors, counting certificates | Uniqueness of the successor, symmetries, first conditional reductions. |
| September, E076–E116 | ON/OFF at the same T, progression, second Tower | The progression of T does not prove that β is invariant. |
| October, E197–E244 | Towers in the counting field, exact synchronization, fibres, energies | Distinction between counting channel, raw channel and smoothing; several obligations remain unclosed. |
| E264–E352 | Local synchronization, reconstruction, grammar | Finite checks only. The E301 audit file: **R** its conclusions are declared false by the author (§19.9, 30 October); they are not cited. |
| 22–25 October, E353–E376; E2M | Grammatical words, Dirichlet channels, radial defect; naive zero-to-transition correspondence | **R** the E2M correspondence is retracted (a numerical superposition is not a canonical map). |
| 25–28 October, separation and terminal chain | Migration; zero-free band, decomposition of dwells, finite radial rigidity (C, see §5); 27 October: lightened build | 28 October (`1c2ef553`): the terminal goal becomes the named hypothesis "rise of the expected frequency", proved equivalent to RH; the chain compiles (C) and remains conditional. |
| 28–31 October, §19 reorientation (§19.1–19.23) | Off-line zero, then carrier, then obligatory junction (raccord) | **C** canonical OFF carrier (`OffCarrier.lean`), trichotomy of the outgoing member, three-zero window, frequency cap, ported PNT and its consequences (`LogGapsTheorem.lean`, `SummitVertical.lean`). **R** E301 (§19.9); the reading "the smoothed contact is an arithmetic meeting" is declared false (§19.10). No transport conservation law in the corpus (§19.19). |
| 31 October–3 November, §19.24–19.38, E398–E426 | Contacts, per-gap contributions, accumulation of values; E398 (summit attained) | **C** geometry of the real values at contacts (`ContactRealValue.lean`), tangential inversion, meetings between Towers (`TowerMeetings.lean`). **R** the local approach with two or three zeros (§19.29, "millions of zeros are needed"). |
| 3–6 November, §19.39–19.50, E427–E435 | Constraints between Towers at contacts; grammar recovered from the zeros | **C** modules per experiment (grammar, series reading, value at meetings, transport at the shared prime). **M** level 2 negative: no transport at contacts; audit of 22 statements about the complement: no independent rigidity (E435). |
| 6 November, §19.51, E436 | Withdrawal of the route "contacts of a Tower and position of a prime" | **R** every formula tying the contact grid to an exact prime; **R** "what is missing = absorption by the complement or exponent of the remainder". **C** splitting of a gap by the contacts (partial remainders). |
| 7 November, §19.53–19.70, E437–E448 | Reconstruction of gaps by the contacts; price of the meeting; finite regime; break on the line | **C** signed balances, exact price (E445), the "one prime per meeting cell" regime is finite for every Tower (`MeetingRegimeFinite.lean`), break mechanism on the line (`BreakMechanismOnLine.lean`). **R** spectral amendment of E445 (§19.67); the obligation "amplitude and variation of the raw demand" withdrawn. |
| 8 November, §19.71, E449 | Inversion: gaps, contacts, zero | **C** the word of gaps determines the Tower (T, phase, β); the cause is the ported PNT. |
| 8 November, §19.72–19.79, E450–E456 (plan K0–K6) | OFF pair and mirror | **C** break of the pair at the shared prime, order of the zero (`PairBreakOfZero.lean`), imposition of the meeting (`PairMeetingImposition.lean`), pair read as a passage (`PairArrivalPassage.lean`). **M** shift of the contacts at the same height. **R** (rectification §19.76) the "every β" range. No contradiction obtained. |
| 8–12 November, plan Φ, §19.80–19.97, E457–E466 | The missing edge: the selection of carriers; collective channel allowed again (§19.91) | **C** mirror band described, collective recomposition, area balance of the demand over the pieces cut by the contacts. **M** lateral predictor E464/E466 (measured horizon, not a theorem). **R** (§19.85) E457 does not say "tail property": it says that no predicate on a finite window of the word characterizes the selection. No contradiction. |
| 13 November, plan Ψ, §19.98–19.101, E467–E471 | Cumulative attacks | **C** four modules, 31 statements (`MemberConstancySeries.lean`, `FiberAnnihilator.lean`, `PairAsymmetryOverPrimes.lean`, `AlternatingCellSeries.lean`): the relative share of a Tower is multiplied by a fixed factor per cell, constant exactly on the line; the pair is unbounded in cumulative terms. **M** exponents of the pair measured close to those expected. The plan did not close RH. |
| 13 November, §19.105–19.107, E472–E474 | Alternating budget; grammar of cell areas; tent | **C** separation of the arithmetic budget from the background (`ArithmeticBudgetSeparation.lean`), cell areas (`CellAreaGrammar.lean`, `CellAreaTent.lean`, `CellAreaIntegral.lean`). **M** relative budget below 0.08 over 8 Towers. **R** rectifications from an external audit: "budget read on the primes alone" too strong; "cancellation by alternation" improper. Classified **auxiliary** by the author on 14 November, with no bearing on RH (§19.108). |
| 14 November, §19.108–19.109, E475 | Active question: obligation of the exact reconstruction of a gap at the first OFF Tower, at the shared prime | Audit, no module: the five points of the strategy are already compiled objects. **M** M1 exact (the shared prime is the next prime, 2000 junctions (raccords)); M2 fails by the letter, exact law recorded; M3 sensitive, equal to the price already compiled. Verdict B: the question about the shares of a gap is empty; the pair changes only the enumeration. |
| 14 November, §19.110, E476 | Tent and break | **C** `TentBreakObligation.lean`, 10 statements, two attempts, full green build: the weight of the break in the tent, the amplitude paid reads this weight, sawtooth and neutral point, same weight for the Tower and its mirror if and only if β = 1/2. **M** identities to 1e-14 over 8 Towers; two tests failed by the letter (prediction badly written). Verdict B; the obligation is a compiled form, not a contradiction. |
| 14 November, §19.111, E477 | Alternating weights Tower minus mirror over primes with a shifted word | **M** alternating weights equal at first order, mean effect of second order in the word shift; three tests failed by the letter, one of which was a prediction wrong in nature (fluctuations). No module, **no theorem**, thread closed. Verdict B. |

Each experiment has its pre-registration (an earlier commit), its twin, its `RESULTS.md` and a verdict A, B or C; B verdicts are frequent and are not successes.

## 5. Established discoveries, measured results, frontier

**Compiled theorems** (named in words; files under `formalization/RHV6Fresh/RHV6Fresh/Terminal/`, unless stated otherwise). Sources of the statements: the semantic master document and the build logs cited in section 4.
- Zero-free band applied to the actual zeros: for a height above 3, the radial position stays within a band that widens towards one half — `ZeroFreeRegionBand.lean`. It does not separate the line from off-line positions.
- Exact identity for the grammatical dwells modulo 6: the quasi-compensation is the equidistribution of the primes between classes 1 and 5 up to one unit — `GrammarDwellDecomposition.lean`; Abel bound for the oriented channel — `GrammarWeightedG4.lean`.
- Radial rigidity of a bounded finite exponential sum — `FiniteRadialRigidity.lean` (conditional tool: the bound for the infinite signal is not established).
- The prime number theorem (Chebyshev form) is ported, and from it follow, as theorems, that the logarithmic gaps tend to zero and that the meetings sample the frequencies — `LogGapsTheorem.lean` (§19.18 onwards of the master document), third-party code in `PNTPort`.
- Canonical OFF carrier and profile of an off-line perturbation: low arrival, finite fibre, frozen outgoing step — `OffCarrier.lean`, `OnRegimeStabilityPackage.lean`.
- Frequency cascade: on the line it is strictly increasing at every rank; its strict increase everywhere is equivalent to RH — `FrequencyCascadeStability.lean` (cited in `DemonstrationChain.lean`).
- Contacts: real value at each contact, tangential inversion of (T, β), interlacing — `ContactRealValue.lean`, `TangentialInversion.lean`, `AmplitudeContact.lean`.
- The word of gaps determines the Tower (E449); the mirror has a word that is a function of the Tower's word, and the words are equal if and only if β = 1/2.
- Finite regime with one prime per meeting cell — `MeetingRegimeFinite.lean`; exact amplitude of the break on the line — `BreakMechanismOnLine.lean`.
- Cumulation: per-cell factor of the share of a Tower, constant if and only if on the line; unbounded pair — plan Ψ, four modules cited above.
- Weight of the break in the tent, and equality of the Tower/mirror weights if and only if β = 1/2 — `TentBreakObligation.lean` (isolated).
- Equivalence: the rise of the expected frequency (hypothesis of the terminal theorem) is equivalent to RH — `DemonstrationChain.lean`. This is what makes the terminal theorem conditional.

**Measured results** (deterministic twins, measurements and not proofs): folders `formalization/RHV6Fresh/experiments/E4xx_*`; Odlyzko zeros up to 2,001,052, primes up to 3·10^7. As examples: E475 (exact shared prime over 2000 junctions (raccords)), E476 (identities to 1e-14), E477 (second order in the word shift).

**Current frontier, in one sentence.** Starting from the primes alone and the exact reconstruction of a gap, we have still not obtained an arithmetic constraint that the first off-line Tower and its mirror cannot satisfy: the compiled obligations at the meeting at the shared prime are satisfied by every family, the OFF pair included, and only the constant relative amplitude and the rise of the expected frequency are violated by the pair, without being derived from the reconstruction (question Q475, `experiments/E475_SharedPrimeObligation/AUDIT_20261114.md`, §19.108–19.109).

**Explicitly rejected by the author** (not to be cited as results): the conclusions of E301 (§19.9); any tying of a Tower to the exact position of a prime (§19.51); the conclusion of a spectral study in E445 (§19.67); the "tail property" reading for E457 (§19.85); the obligation tying the OFF contradiction to the amplitude and to the variation of the raw demand (§19.68); any claim that the contacts do not read β (§19.44, §19.63); the "every β" range for the arrival (§19.76); the naive E2M correspondence.

## 6. Call to mathematicians around the world

The author opens this project and invites anyone who wishes to continue it.

**The author's observation.** Today's artificial intelligences execute, compile and measure rigorously, but do not yet know how to find discoveries, retain them and combine them with one another to close a proof. We are not at artificial general intelligence. This project is an illustration: more than five hundred Lean files in the active library, dozens of pre-registered experiments, and a central question that is still open.

**What the author asks:**
- to review the compiled theorems (list in section 5) and the statements that accompany them;
- to attack the active question Q475: what new constraint the exact reconstruction of a gap between two consecutive primes imposes on the first off-line Tower, a constraint that its contacts and those of its mirror cannot satisfy;
- to propose new arithmetic constraints at the shared prime;
- to report any error, including errors of vocabulary or of scope.

**How to contribute.** Read `CONTRIBUTING.md` and the master documents (`RHV6final_STRATEGIE_*.md`, in French), in particular the semantic master document (`formalization/RHV6Fresh/RHV6final_STRATEGIE_SEMANTIQUE.md`, in French, especially §19.98 to §19.111). Rules: no `sorry`, no `admit`, no added axiom; `lake build RHV6Fresh` must stay green; pre-register (commit) the hypotheses and thresholds before compiling or running; provide a deterministic twin for every figure; never present a conditional statement as unconditional. Open an issue or a pull request on the repository, citing the author (Charles S.). Contributions are subject to the terms of `COPYRIGHT.md`. We promise no proof.

## 7. Reproducing

**Lean build** (toolchain `leanprover/lean4:v4.33.0-rc2`, file `formalization/RHV6Fresh/lean-toolchain`). Mathlib is pinned as a git dependency, revision `51e6992efd06126df61a496bebf8f49482a4e129`, declared in `formalization/rhv3_lean/lakefile.toml`; `RHV6Fresh` reaches `rhv3_lean` by the relative path `../rhv3_lean`. `formalization/RHV6Fresh/lake-manifest.json` is the manifest regenerated by `lake update` during the verification build of 15 November 2026 (it pins Mathlib and its dependencies); the one in `rhv3_lean` is not versioned.
```bash
cd formalization/RHV6Fresh
lake update                          # résout Mathlib et ses dépendances à la révision épinglée
lake exe cache get                   # (si disponible) télécharge les .olean de Mathlib précompilés
lake build RHV6Fresh                 # cible par défaut
lake build RHV6FreshCertificates     # optionnelle : certificats de rectangles 22 et 28 (très coûteux)
```
(The comments in the code block above are in French: resolves Mathlib and its dependencies at the pinned revision; (if available) downloads the precompiled Mathlib .olean files; default target; optional: rectangle certificates 22 and 28 (very expensive).)

The `.lake/` directories are not versioned: without the cache, the first build of Mathlib is very long. Do not move `rhv3_lean` or `RHV6Fresh`. `scripts/status.sh --build` reruns the build and rewrites its log.

**Python twin** (Python 3 with numpy; dependencies specific to each script, to be read in its header):
```bash
cd formalization/RHV6Fresh/experiments/E477_ShiftedPrimesPair
nohup python3 twin_e477.py > logs_twin_run.txt 2>&1 &     # environ 15 s ; protocole borné : pas de sondage en boucle
```
(Comment in French: about 15 s; bounded protocol: no polling in a loop.)

The expected results are in `RESULTS.md` and `twin_results.json` of the same folder.

**Data.** `formalization/RHV6Fresh/experiments/data/` contains the Odlyzko zeros: `odlyzko_zeros6_2001052.txt` (36,018,936 bytes, SHA-256 `2ef7b752c2f17405222e670a61098250c8e4e09047f823f41e2b41a7b378e7c6`) and its prefixes `odlyzko_zeros1_first5000.txt`, `odlyzko_zeros1_first300.txt`. Provenance (file `odlyzko_zeros6_2001052.PROVENANCE.md`): A. M. Odlyzko, "Tables of zeros of the Riemann zeta function", file `zeros6`, https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros6, downloaded on 27 October 2026. These heights are those of known zeros on the critical line; they do not certify the absence of off-line zeros.

## 8. Layout of the public repository

```text
formalization/
  rhv3_lean/    (168 .lean)         fondations ζ, comptage, certificats ; dépendance Mathlib épinglée
  RHV6Fresh/    (586 .lean au total) build actif ; RHV6Fresh.lean et RHV6FreshCertificates.lean à la racine
    RHV6Fresh/ (560)               code de la bibliothèque
      Terminal (393)               chaîne terminale et modules de résultats (dont DemonstrationChain.lean)
      Zeta23Port (134)             code tiers (Apache 2.0), voir THIRD_PARTY_NOTICES.md
      PNTPort (9)                  code tiers (Apache 2.0), voir THIRD_PARTY_NOTICES.md
      Tower (7), Direct (7), Voyage (3), Grammar (2), Foundation (2), RhGapPort (1)
    experiments/                   expériences E400 à E477 (70 dossiers), audit_semantique/ (sans son data/), data/ (< 1 Mo, plus les zéros d'Odlyzko)
    scripts/                       status.sh, goal_dependencies.py, raccord_check.py
    audits_compilation/            journaux de compilation
    RHV6final_STRATEGIE_{SEMANTIQUE,MATHEMATIQUE,LEAN}.md   les trois maîtres
    HANDOVER_20261107_LIGNE.md     passation (§1 à §36)
    AUDIT_*.md                     audits de ce dossier
docs/ANNONCE_PUBLICATION_20261115.md   annonce de publication
README.md, COPYRIGHT.md, LICENSE, THIRD_PARTY_NOTICES.md, CONTRIBUTING.md, CITATION.cff, SECURITY.md, PUBLICATION_SCOPE.md
```
(The annotations in the tree above are in French. Translation, line by line: ζ foundations, counting, certificates; pinned Mathlib dependency / active build; `RHV6Fresh.lean` and `RHV6FreshCertificates.lean` at the root / library code / terminal chain and results modules (including `DemonstrationChain.lean`) / third-party code (Apache 2.0), see `THIRD_PARTY_NOTICES.md` (twice) / experiments E400 to E477 (70 folders), `audit_semantique/` (without its `data/`), `data/` (< 1 MB, plus the Odlyzko zeros) / compilation logs / the three master documents / handover (§1 to §36) / audits of this folder / publication announcement.)

What is not in this repository (the bases `rhv2_fresh`, `rhv4_lean`, `RHV5Fresh`, `rh_gap_criterion`, experiments earlier than E400, `research/`, `validation/`, `src/`, earlier `docs/`, the internal working log) remains in the private research repository and can be provided on request; see `PUBLICATION_SCOPE.md`.

---

# Annexes: historical inventory frozen at 26 October 2026

**The annexes describe the whole private research repository.** Folders and files cited that do not appear in this public repository (see `PUBLICATION_SCOPE.md`) are "in the private research repository". The sections below are carried over from the previous README, without updating (they describe the state as of 26 October: for example, the terminal goal they mention has since been transformed, see the banner). The experiment figures in them are those of that date; developments since then are in section 4. The E301 audit folders appear in them by name; their conclusions are rejected (section 5).

## A1. Demonstrated discoveries and limits

**Grammar modulo 6.** For primes `p>3`, the state is 1 or 5. There are four transitions `11,15,51,55`. The oriented channel `N15−N51` is a telescoping of the endpoint states and has absolute value at most 1 on a prefix. It is not an independent constraint on β. Experimental gap sequences, families and meta-patterns are not interchangeable with these four transitions.

**Dwells and character channel.** In `Terminal/GrammarDwellDecomposition.lean`, for any two-state word:
```text
N11 − N55 = (N1• − N5•) − (N15 − N51).
G11 − G55 = (W1 − W5) − (G15 − G51)   (tous poids réels).
```
(Comment in French: all weights real.)

The first weighted term is a character channel, the second an Abel sum whose total variation bounds the value. The empirical quasi-compensation of the dwells is not a uniform bound; these identities do not prove the absence of any spectral coupling.

**Towers and tangential inversion.** For `β,T>0`:
```text
φ(β,T) = arctan(T/β)
log C_k = (φ + kπ)/T,    log(C_{k+1}/C_k) = π/T
T = π/log(C⁺/C⁻),        β = T/tan(T log C⁻)  (branche vérifiée)
```
(Comment in French: branch verified.)

The contact is derived from the zero; recovering the zero from two **chosen** contacts does not establish that the primes produce those contacts. The geometric candidate `k* = floor((T log S−φ)/π)` selects the cell containing a scale `S>0`, but the theorem identifying this cell with the authentic prime passage is not established.

**Mirror and ON/OFF.** The authentic mirror of `β+iT` is `1−β+iT`. It coincides with the initial member exactly when `β=1/2`. Off the line, same T and same logarithmic width `π/T`, but different phases and amplitudes. This symmetry is static; on its own it does not prove the ON stability of the successor. A complete OFF quartet is a hypothetical experiment, not a substitution of an isolated zero in the true function ζ.

**Analytic reconstruction.** The exact individual term of the Chebyshev channel is proportional to `−x^ρ/ρ`; the counting channel `li(x)` uses appropriate contributions such as `Ei(ρ log x)`, with corrections, branch and truncation. Smoothed sums, raw terms and normalized forms must have distinct types (`ExactZeroSignal`, `RescaledZeroSignal`, `UnitCoefficientMode`), with no tacit substitutions. The infinite sum and its complement are not controlled by an experiment with 300 zeros.

**Zero-free band and rigidity.** `ZeroFreeRegionBand` reuses the unconditional zero-free region of `rhv3_lean`: for `T>3`, `A/(log T)^9 < β < 1−A/(log T)^9`. This band widens at high frequency; it does not force `β=1/2`. `FiniteRadialRigidity` proves, for a **finite and bounded** exponential sum, that positive exponents are excluded; uniform control of the infinite complement is missing. `GrammarWeightedG4` establishes bounds for the oriented channel, not for the common channel.

**Counting and first heights.** The ζ rectangle certificates establish the first zeros on the line and the absence of a low member up to height 28 in the modules concerned. A "possible OFF" beyond this threshold has a constrained mirror fibre and profile, but no terminal contradiction is obtained.

## A2. Matrix of attempted solutions

| Route | Module, TDD or series | Actual result | Terminal obstacle |
|---|---|---|---|
| Geometry of contacts | E44, TangentialInversion, E367/E374, `TDD_ContactInversion` | Exact inversion if authentic contacts are supplied | Independent selection of the contact |
| Succession / fibre / mirror | Direct/Raccords (junctions), OnRegime*, HorizontalExclusion, E208–E214 | Order identities, distinct mirror, profile of a first break | Reflected admissibility or exclusion of the OFF exit |
| Regime conservation | `DemonstrationChain`, `OnRegimeStabilityPackage`, E350–E351 | **Conditional** recurrence and constraints of a break | `β_E=1/2 ⇒ β_L=1/2` not proved |
| Domination of the first Tower | E218, former terminal premises | Conditional formulations, sometimes RH-equivalent | Independent inequality on the true remainder |
| Energy and budgets | E216, E224–E241, E324, TDD A3 | Identities or conditional coercive tools | Construct a positive energy and its arithmetic budget |
| Grammar of windows | E340–E344, E353–E363 | Words, supports and transitions computed | No bound on the collective residual |
| Signed channels, Dirichlet, Abel | GrammarDwell*, GrammarWeightedG4, paper T1/T2 | Oriented channel and correction of isolated powers | Common channel, Lean T1/T2, junction (raccord) `transitionSum` |
| Explicit formula / Mellin | E365, E372 probes, PrimePowerCorrection/Z3 envisaged | Identities and conditional criteria | Remainder `O(x^θ)` with a sufficiently small exponent |
| Finite reconstruction / projection | E308, E330–E336, E364–E376, Z1 | Limited identifiability, calibrations and counter-tests | Infinite projection and truncation under control |
| Synthetic ON/OFF | E268–E288, E347, E369, E373, E375 | OFF growth, envelope shift and phases | Authentic collective compensation not excluded |
| Affine transport law | `TDD_AuthenticTransportCore`, A1–A9 | Formal implications and two abstract counterexamples | Authentic function `F(Q,e)`, source coming from the primes |
| Independent certification | P0–P11, `ROOT_CAUSE_MASTER_MATRIX` | Partial dependency graph | First arrow primes→spectral output not constructed |

### Trials A1–A9 (authentic transport)

| Trial | Proof/counter-model | New missing data |
|---|---|---|
| A1 | `j=Ae+b`, `e=0` ⟹ `j=b` | Produce `b` without defining the defect |
| A2 | `j=F(Q,e)`, `e=0`, `F(Q,0)=0` ⟹ `j=0` | Construct `F` from arithmetic `Q` |
| A3 | `j²≤V≤Ae²`, `e=0` ⟹ `j=0` | Independent arithmetic energy |
| A4 | Strictly absorbed source with `q<1` ⟹ zero | Authentic estimate `q<1` |
| A5 | Arbitrarily small bounds for **the same** `j` ⟹ zero | Uniformly controlled remainder |
| A6 | Odd transport ⟹ fixes zero | Exact parity of the certificate, caution: `J` not odd |
| A7 | Path `0,1,0` | A zero cyclic balance is not enough |
| A8 | Mirror fibre `{−1,1}` | Fibre invariance ≠ fixed member |
| A9 | OFF successor of an ON ⟹ non-consecutive reflected | Admissibility of the reflection, already close to the lock |

These nine trials compile individually according to the logs of `authentic_transport_causality`; they close **no terminal arithmetic obligation**.

## A3. Experiment registry: documented objectives and results

The full registry of the **107 folders** of `formalization/RHV6Fresh/experiments/` (in the private research repository; the public repository contains only the selection E400–E477) is organized below by waves; the reports of each folder remain the source of details, figures and any rectifications.

| Series | Common aim | Results and reservations |
|---|---|---|
| E076–E116 (scripts directly under `experiments/`) | Phase, Towers, contacts, mirror and grammar | Geometric tests and OFF cases; inversion and progression do not supply the cause of ON. |
| E117–E196 | Energies, contacts, incidences, propagation and inversions | Several counter-tests and corrections of schemes; read the `*_output.md` files. |
| E197–E211 | Windows, fibres, li(x), collective Tower, first zero | Decomposition of contributions and diagnosis of the incoming/outgoing passage. |
| E212–E244 | ON regime, junctions, harmony and collective correction | The arithmetic junction (raccord) on the remainder remains open; finite windows not sufficient. |
| E264–E300 | Individual Towers, ON/OFF sensitivity, windows and synchronization | 51 images/PDFs in the series; finite witnesses, not RH certificates. |
| E301–E313 | Adversarial audit, 3 Towers, beats, non-compensation, modes | Separation of the exact count from truncated signals. |
| E321–E336 | Reconstruction around li(x), 3/10-zero results, inverse and anchoring | Inversion ≠ autonomous spectral identification. |
| E337–E352 | Counting plan, grammar, meetings, stability, OFF at a new height | Several leads requalified; ON conservation not established. |
| E353–E363 | Exhaustive grammar of 500,000 gaps in 100 windows | 994,971 distinct words of length 2–12 reported, 7 class compositions against 8 state paths (non-injective projection); some list endings of the `meta_graph` computation historically omitted. |
| E364–E370 (root scripts) | 36 fixed heights, exact `ψ`, frequency recovery, inverse contacts, OFF | Finite windows; `β` not identifiable from the normalized ON signal alone; no bound on the remainder. |
| E371–E376 (root scripts) | Detection, calibration, matching, inversion of contacts, synthetic quartet | Frequency peaks ≠ new zeros; error interval not certified; no proof of identifiability. |
| **E371 — Archetype B (separate folder)** | Decomposition of dwells up to `10^7` | `D=−33` at `10^6`, `D=−189` at `10^7`, maximum `|D|=362`, observation only. |
| **E372 — ClosureAttempts (separate folder)** | Six terminal-closure probes | P1 band/freeze compatible; P2 strong multiplicity absent; P3 finiteness vs infinite remainder; P4/P5 exponent gain missing; P6 junction (raccord) rule RH-equivalent. |
| **E373 — WeightedGrammarChannels (separate folder)** | 300 zeros and weights `−2Re((q^ρ−p^ρ)/ρ)`; synthetic OFF | Weighted identities confirmed; OFF variation close to a common mode; **the old figures for the direct remainder are invalidated until recomputed**, because of the powers of 2 and 3 omitted before the script was corrected. |
| E2M (24 October) | Superposition of zeros and primes | 2,001,052 ordinates; 1,912,998 height intervals without transition and 88,055 transitions on the raw axis; **causal mapping retracted**. |
| Authentic transport (25 October) | Homogeneous/affine/energy/absorption/mirror transports | A1–A9 are conditional or counter-models; zero new closure. |

The **190 direct subfolders of `research/`** archive the historical campaigns (E44, `tour10*`, retrospectives and proofs of concept). The **38 families of `validation/`** check P4/zeta, KVM8, alignments and ablations. Their original READMEs remain available and their results are not converted into theorems by this consolidation.

### Index of experiment sets

- **E197–E244**: `e197_window_comparison`, `e198_transmissions_300`, `e199_increment_matrix_fibers`, `e200_arrival_fiber_hypotheses`, `e201_first_zero_contact_comparison`, `e202_cell_passage_restitution`, `e203_transition_rigidity_raccord`, `e204_three_towers_li_field`, `e205_counting_field`, `e206_prime_gap_ledger`, `e207_collective_contact_geometry`, `e208_on_regime_anchor`, `e209_regime_transport`, `e210_first_regime_change`, `e211_on_regime_induction_probe`, `e212_archaeology`, `e213_mixed_fibers`, `e214_tower_transport`, `e215_window_collective`, `e216_energy_raccords`, `e217_missing_property_probes`, `e218_global_tower_dominance`, `e219_prime_gap_zero_dna`, `e220_counting_channel_gap_contributions`, `e221_collective_compatibility`, `e222_frequency_extraction`, `e223_global_gap_invariant`, `e224_harmonic_restoring_law`, `e225_mirror_harmonic_balance`, `e226_xi_kernel_spectral_stability`, `e227_functional_equation_restoring_constraint`, `e228_zero_mode_stability`, `e229_prime_gap_harmonic_response`, `e230_terminal_closure_challenge`, `e231_contact_sign_closure`, `e232_two_gap_charge_closure`, `e233_six_beats_closure`, `e234_grammar_noncompensation`, `e235_two_gap_determinant`, `e236_raccord_additive_rigidity`, `e237_first_off_minimal_compensation`, `e238_exact_counting_closure`, `e239_first_zero_causality`, `e240_harmonic_current`, `e241_tower_coupling`, `e242_exact_signal_audit`, `e243_gap_synchronization`, `e244_amplitude_stable_sync`. Cross-cutting folders: `e224_e230_compiler_probe`, `e231_e238_euler_product_route`, `e231_e238_lean_closure_probes`.
- **E264–E352**: `E264_E300_LocalSynchronization`, `E301_AuditContradictoire`, `E302_THREE_ON_TRUE_3D_SYNCHRONIZATION`, `E303_THREE_ON_COLLECTIVE_BEATS`, `E305_FixedGapRaccords`, `E308_PrimeOnlyRadialRigidity`, `E309_PerGapSynchronizationDistinctHeights`, `E310_PrimeMusicAmplitudeStability`, `E311_SuccessiveModeExtraction`, `E312_SignalProgressionTranslation`, `E313_ConstantAmplitudeNeed`, `E321_GeneratedFrequencyMeetingPoints`, `E322_CountingReconstructionAroundLi`, `E323_SynchronizationMatrix`, `E324_ImposedAmplitudeNonCompensation`, `E325_JointGapTriple`, `E326_GoalAudit`, `E327_PrimeQuantitativeGrammar`, `E328_ThreeZerosAroundLi`, `E329_PrimeGapWindowsThreeZeros`, `E330_ThreeZeroResultant`, `E331_TenZeroResultant`, `E332_SuccessiveSumsSameGaps`, `E333_CountingFieldArchitecture`, `E334_InversePrimeSpectralReconstruction`, `E335_FirstZeroArithmeticAnchor`, `E336_LocalGlobalGapMatrix`, `E337_CountingPlane`, `E338_PrimeToCountingPlane`, `E340_GrammarWindow`, `E341_GrammarWindowQualification`, `E342_PrimeInversionThreeZeros`, `E343_GapInverseCountingPlane`, `E344_GrammarOperator`, `E345_HarmonicCollaborationFiveZeros`, `E345_E346_STABLE_TOWERS_REBUILD`, `E346_BilateralHarmonicRaccord`, `E347_OFF_NewHeight_E345_E346`, `E348_InequalityCandidates`, `E349_TwoMeetingInversion5000Gaps`, `E350_GrammarSpectralStability`, `E351_GapDemandStability`, `E352_ProjectionOnKnownZeros`.
- **Other active registries**: `E371_ArchetypeB_Anatomy`, `E372_ClosureAttempts_ZeroFreeBand`, `E373_WeightedGrammarChannels`, `authentic_transport_causality`, `causal_advanced_validation`, `root_cause_validation`, `d1012_causal_validation`, `project_audit`, `audit_semantique`. The programmes E353–E376 are also directly under the `experiments/` folder.

## A4. Index of TDD and formal tests

**34 Lean files containing TDD in their name were identified** in the repository during the Git inventory (TDD logs and plans are not included). Active primary registry:
```text
TDD_ArithmeticCandidate.lean          TDD_ArithmeticFrequencyNecessity.lean
TDD_ArithmeticRefinement.lean         TDD_AstraDivisorMass.lean
TDD_AstraIncidenceFreedom.lean        TDD_AstraPrimeWeights.lean
TDD_CanonicalGrammarStability.lean    TDD_ContactErrorPropagation.lean
TDD_ContactInversion.lean             TDD_CriticalRemainderExponent.lean
TDD_CriticalRemainderIntegration.lean TDD_ExactFixedSpectralSignal.lean
TDD_FixedWindowGrammar.lean           TDD_FixedZeroSignal.lean
TDD_GrammarAnalyticSeparation.lean    TDD_GrammarChannelObstructions.lean
TDD_GrammarPotentialStability.lean    TDD_GrammarWeightedG4.lean
TDD_InterWindowComposition.lean       TDD_ONPhaseTransport.lean
TDD_RootCauseMirrorTransport.lean     TDD_SpectralWindowComposition.lean
TDD_ValidatedZeroMatching.lean       TDD_WindowGrammarStability.lean
authentic_transport_causality/TDD_AuthenticTransportCore.lean
authentic_transport_causality/TDD_TransportReductionAudit.lean
```
These 26 files are in `formalization/RHV6Fresh/experiments/` (the last two in the subfolder). The other 8 are in `formalization/rh_gap_criterion/` and `research/tdd_true_off_zeta_only_20260913/`: series `Round26FSFiberedPartnershipTDDRepair`, `Round27EFiberedPartnershipTDD`, `Round27GTwoBaseReflectedLaurentTDD`, `SemanticTransportClosure20260821/{FinalConditionalFirstReturnClosureTDD,ProgressiveFiberedFirstReturnClosureP2TDD,ProgressiveFiberedFirstReturnClosureP3TDD,ProgressiveFiberedFirstReturnClosureTDD}`, `TrueOffZetaOnlyTDD`.

Test categories: **arithmetic/frequency**, **grammar/windows**, **contact/inversion**, **critical remainder and integration**, **exact signals/projections**, **transport/mirror**, **causality/divisors/masses**, **historical routes of first break**. The results `project_audit/tdd_results.json`, `project_audit/README.md` and `authentic_transport_causality/BUILD_AND_AXIOMS.md` are the sources for the targeted verifications. A TDD PASS does not mean that its conditional hypothesis is true for the actual primes.

## A5. Atlas of graphs and figures

The inventory of the Git tree as of 26 October lists **450 files** with the extensions `.png`, `.svg`, `.jpg`, `.jpeg`, `.webp`, `.pdf` (some plates exist in both PNG and SVG; do not count both as independent experiments). Existence is verified by the Git tree; the physical correctness of each plot was **not** checked image by image.

| Gallery / folder under `formalization/RHV6Fresh/experiments/` | Visual files | Subject |
|---|---:|---|
| `E264_E300_LocalSynchronization/` | 51 | Towers, ON/OFF, sensitivity, contacts, compensation |
| `E302_THREE_ON_TRUE_3D_SYNCHRONIZATION/` | 18 | 3 Towers, contacts, li, gaps and reconstruction |
| `E303_THREE_ON_COLLECTIVE_BEATS/` | 18 | Beats, superposition, counting |
| `e243_gap_synchronization/` | 14 | Per-gap contributions |
| `E347_OFF_NewHeight_E345_E346/` | 13 | OFF at a new height and checks |
| `e207_collective_contact_geometry/` | 12 | Geometry of contacts |
| `e244_amplitude_stable_sync/` | 10 | Stable ON amplitude and synchronization |
| `E334_InversePrimeSpectralReconstruction/` | 9 | Inverse reconstruction |
| `E331_TenZeroResultant/` | 8 | Superposition of ten zeros |
| `authentic_transport_causality/` | 8 | **SVG diagrams**, no quantitative curves |
| `e208_on_regime_anchor/` | 8 | ON anchoring |
| `e242_exact_signal_audit/` | 8 | Audit of the exact signal |
| `E333_CountingFieldArchitecture/` | 7 | Architecture of the counting field |
| `E342_PrimeInversionThreeZeros/` | 7 | Three-zero inversion |
| `E345_E346_STABLE_TOWERS_REBUILD/` | 7 | Reconstruction of stable Towers |
| `e199_increment_matrix_fibers/` | 7 | Fibres and matrices |
| `e219_prime_gap_zero_dna/` | 7 | Grammar of gaps and signatures |
| `E345_HarmonicCollaborationFiveZeros/` | 6 | Five zeros |
| `e198_transmissions_300/` | 6 | 300 transmissions |
| `e205_counting_field/` | 6 | Counting field |
| `e209_regime_transport/` | 6 | Regime and transport |
| Other folders and direct files | Remainder up to 450 | See individual paths and READMEs |

Examples of named plots: `E264_A1_zeros_1_3_tours_individuelles`, `E268_fig_ON_vs_OFF_T1`, `E270_fig_contacts_contributions`, `E302/fig3_li_signaux`, `E303/fig7_comptage`, `e115_figA_analytic_plane_scaled`, `e115_figB_tower_log_view`, `e115_figC_normalized_axes`, `e364_e370_synchronized_views.png`, `e371_e376_reconstruction_audit.png`. Each path must be interpreted together with its campaign notice and its hypotheses. **A normalized ON Tower can be drawn with fixed amplitude; the exact counting term does not have the same envelope.** Isolated circular representations do not on their own describe the field around `li(x)`.


## A8. Exhaustive indexes (in the private research repository)

The following three registries (`docs/RH_FIGURES_ATLAS_20261026.md`, `docs/RH_EXPERIMENTS_TDD_READMES_INDEX_20261026.md`, `docs/RH_E_NUMBERED_SCRIPTS_INDEX_20261026.md`) are in the private research repository and are not published here.

## A9. Navigation map

- [Repository README](README.md) — entry point.
- [README of the RHV6Fresh build](formalization/RHV6Fresh/README.md) — commands and status.
- [Publication scope](PUBLICATION_SCOPE.md) — what is included and excluded.
- [Solution audit](formalization/RHV6Fresh/AUDIT_SOLUTION_20261005.md); [Audit of fidelity to the master documents](formalization/RHV6Fresh/AUDIT_FIDELITE_RHV6_vs_MAITRES.md).
- In the private research repository only: READMEs of the formalizations, the docs, the research, the Python code, the validations.

**Provenance and fidelity:** this synthesis results from the inventory of the `main` tree (8,698 files, 117 READMEs, 107 RHV6Fresh experiment subfolders, 450 visual documents, 34 Lean TDD files by name) and from reading the main READMEs and targeted audits. It implies **neither a rerun of the 107 campaigns, nor an individual examination of the 450 figures, nor any new certification of the build**. Divergent results must be arbitrated by the corrected experimental source, the Lean signature and the execution log, and then possibly by a rerun.
