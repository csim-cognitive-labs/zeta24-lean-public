# Composants tiers

Les composants listés ici ne sont PAS couverts par la licence non commerciale du projet ; leurs permissions Apache 2.0, y compris commerciales, demeurent.

Ce dépôt contient ou utilise du code et des données qui ne sont pas l'œuvre de l'auteur et que le copyright de [COPYRIGHT.md](COPYRIGHT.md) ne couvre pas. Les notices d'origine sont conservées intactes dans les dossiers concernés. En cas de doute, la notice d'origine du fichier prévaut.

## 1. Composants inclus dans le dépôt

| Composant | Chemin | Origine exacte | Licence | Détenteur du copyright | Usage dans le projet |
|---|---|---|---|---|---|
| Zeta23Port (134 fichiers `.lean`, plus `LICENSE`, `NOTICE`, `PROVENANCE.md`) | `formalization/RHV6Fresh/RHV6Fresh/Zeta23Port/` | Copie de `anthropics/formal-math`, répertoire `zeta23`, révision `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (clôture d'import de `Zeta23.Final` et `Zeta23.FinalMult`). Seuls les imports sont renommés (`Zeta23.*` devient `RHV6Fresh.Zeta23Port.*`), le contenu est inchangé. Une partie (`FromPNTPlus/`) dérive elle-même de PrimeNumberTheoremAnd et de Mathlib, avec leurs notices. | Apache 2.0 (`LICENSE`, `NOTICE` du dossier) | « Copyright (c) 2026 Anthropic, PBC » ; pour `FromPNTPlus/` : aussi les contributeurs de PrimeNumberTheoremAnd et de Mathlib, selon les en-têtes de fichiers | Voir la section 3 |
| PNTPort (9 fichiers `.lean`, plus `LICENSE`, `PROVENANCE.md`) | `formalization/RHV6Fresh/RHV6Fresh/PNTPort/` | Port de `AlexKontorovich/PrimeNumberTheoremAnd`, révision `127b50e33f6033e2147921167a117af96d9ba4ea` (clôture d'import de `chebyshev_asymptotic`). Transformations mécaniques listées dans `PROVENANCE.md` (annotations `blueprint` retirées, imports renommés, corrections de portage marquées `-- port :`). | Apache 2.0 (`LICENSE` du dossier) | Les contributeurs de PrimeNumberTheoremAnd (et de Mathlib pour les trois fichiers `Mathlib/...`), selon les en-têtes | Voir la section 3 |
| P4Port (66 fichiers par arbre) | `formalization/rh_gap_criterion/RhGapCriterion/P4Port/` et `formalization/rhv3_lean/RHV3Lean/Objects/P4Port/` | Ports de `AlexKontorovich/PrimeNumberTheoremAnd`, révision `6739793850d3eaa031e3543ed72d7f026f8080f5` (la plupart du temps dans `IEANTN/` et l'analyse complexe de Hadamard) | Apache 2.0 (mention « Released under Apache 2.0 license » dans les en-têtes) | Matteo Cipollina (50 fichiers par arbre), James Sundstrom, Stefan Kebekus, Robby Sneiderman, autres contributeurs selon l'en-tête de chaque fichier | Utilisé par l'arbre `rh_gap_criterion` et par `rhv3_lean` (non compilés dans le build actif `RHV6Fresh`, sauf ce que `RHV3Lean` importe) |
| PerronPort | `formalization/rh_gap_criterion/RhGapCriterion/PerronPort/` et `formalization/rhv3_lean/RHV3Lean/Objects/PerronPort/` | Ports de `AlexKontorovich/PrimeNumberTheoremAnd`, révision `6739793850d3eaa031e3543ed72d7f026f8080f5` | Apache 2.0 | Selon l'en-tête de chaque fichier (par exemple Michael Stoll, Lawrence Wu, Abby J. Goldberg, Mario Carneiro, Heather Macbeth) | Idem P4Port |
| `ZetaZeroCountingCrude.lean` | `formalization/rh_gap_criterion/RhGapCriterion/` et `formalization/rhv3_lean/RHV3Lean/Objects/` | Fichier portant l'en-tête « Copyright (c) 2026 Robby Sneiderman », Apache 2.0 | Apache 2.0 | Robby Sneiderman | Idem P4Port |
| Tables d'Odlyzko | `formalization/RHV6Fresh/experiments/data/odlyzko_zeros6_2001052.txt` (et `odlyzko_zeros1_first300.txt`, `odlyzko_zeros1_first5000.txt`) | A. M. Odlyzko, « Tables of zeros of the Riemann zeta function », fichier `zeros6` (les 2 001 052 premiers zéros), `https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros6` ; voir `odlyzko_zeros6_2001052.PROVENANCE.md` (SHA-256 inclus) | Aucune licence ne nous a été donnée par l'auteur des tables ; usage de données publiées par leur auteur | Andrew Odlyzko | Données d'expériences. **Ces tables ne sont pas la propriété de l'auteur de ce dépôt** |

Les fichiers de P4Port, de PerronPort et de `ZetaZeroCountingCrude.lean` n'ont reçu aucun en-tête de l'auteur et gardent leur notice d'origine. Les deux fichiers `PerronPort/Audit.lean` et `PerronPort/ZetaBoundsAudit.lean` de `rh_gap_criterion` sont de l'auteur et portent l'en-tête de l'auteur.

## 2. Fichiers adaptés (mixtes)

Ces fichiers sont l'œuvre de l'auteur mais contiennent des preuves adaptées de `anthropics/formal-math` (sous-arbre `zeta23`, fichier `Zeta23/ZetaReflect.lean`, Apache 2.0, Copyright (c) 2026 Anthropic, PBC). Ils portent l'en-tête de l'auteur avec la mention « adaptations » et leur provenance d'origine, laissée en place.

- `formalization/RHV6Fresh/RHV6Fresh/Foundation/ZetaReflect.lean`
- `formalization/rh_gap_criterion/RiemannHypothesisProof/ZetaReflection.lean`
- `formalization/rh_gap_criterion/RiemannHypothesisProof/ZeroSymmetries.lean` (une preuve, `FunctionalMirrorForZeroIsZeroNonTrivial`, adaptée)

Le fichier `rh_gap_criterion/RhGapCriterion/ScientificRebuild20260829/TrustedZetaSeamBridge.lean` évoque l'architecture de `zeta23` comme idée uniquement ; il n'en reproduit aucun code (c'est son propre énoncé) et reste un fichier de l'auteur.

## 3. Usage dans le build actif (`lake build RHV6Fresh`)

Importateurs directs (dans `formalization/RHV6Fresh/RHV6Fresh/`, hors ports) :

- Zeta23Port : `Terminal/PrimeGrammarQuantitative.lean` (importe `RHV6Fresh.Zeta23Port.Chebyshev`) et `Terminal/FrequencyCap.lean` (importe `Zeta23Port.RvM.Statement`, `RvM.NcountWindow`, `GammaFacts.Complete`).
- PNTPort : `Terminal/LogGapsTheorem.lean` (importe `RHV6Fresh.PNTPort.Consequences`).

Importateurs transitifs (mesurés sur le graphe d'imports `RHV6Fresh.*`) : 100 modules propres atteignent Zeta23Port (dont `RHV6Fresh.lean`) ; 33 modules propres atteignent PNTPort (via `LogGapsTheorem`).

Chaîne exacte jusqu'à `RHV6Fresh.lean` (la bibliothèque principale, cible `RHV6Fresh`) :

- `RHV6Fresh.lean` importe `RHV6Fresh.Terminal.GeneratedFrequency`, qui importe `RHV6Fresh.Terminal.PrimeGrammarQuantitative`, qui importe `RHV6Fresh.Zeta23Port.Chebyshev`. `RHV6Fresh.lean` importe aussi `PrimeGrammarQuantitative` directement.
- La fermeture d'imports de `RHV6Fresh.lean` (230 modules) contient 5 modules de Zeta23Port : `Chebyshev`, `Defs`, `Hypotheses`, `FromPNTPlus.Mertens`, `FromPNTPlus.EulerMaclaurin`. Elle contient 12 modules propres qui atteignent Zeta23Port : `PrimeGrammarQuantitative` et, au-dessus, `GeneratedFrequency`, `CascadeContinuation`, `DemonstrationChain`, `FrequencyCascadeStability`, `GapDemandStability`, `InterlacingLink`, `LowNextZeroSignatures`, `OnRegimeStabilityPackage`, `SynchronizationMatrix`, `WindingReadingChain`.
- `FrequencyCap` et `LogGapsTheorem` ne sont pas dans cette fermeture ; leurs importateurs (par exemple `ThreeZeroWindow`, `MeetingRegimeFinite`) non plus. PNTPort n'est donc pas compilé par `lake build RHV6Fresh` ; la bibliothèque est déclarée avec `globs = ["RHV6Fresh"]` et `PROVENANCE.md` de PNTPort le dit.
- Les arbres `rhv3_lean` (importé par `RHV6Fresh` via `RHV3Lean.*`) contiennent P4Port et PerronPort ; ils sont compilés seulement pour les modules `RHV3Lean` que la fermeture d'imports atteint.

## 4. Dépendances non versionnées ici

- Lean 4 (`https://github.com/leanprover/lean4`), toolchain `leanprover/lean4:v4.33.0-rc2` : Apache 2.0, Copyright Lean FRO, LLC et contributeurs.
- Mathlib (`https://github.com/leanprover-community/mathlib4`), révision épinglée dans `formalization/rhv3_lean/lakefile.toml` : Apache 2.0, Copyright les contributeurs de Mathlib.
- Dépendances de Mathlib (batteries, aesop, Qq, ProofWidgets4, import-graph, LeanSearchClient, plausible : Apache 2.0 ; Cli : MIT, Copyright (c) 2021 Marc Huisinga), récupérées par Lake et non incluses ici.

## 5. Précision sur les noms dans les audits historiques

Les noms « zeta23 », « Zeta23 », « Zeta23Port » et « anthropics/formal-math » qui apparaissent dans les audits et les documents historiques de ce dépôt désignent cette dépendance tierce (section 1) et rien d'autre. L'auteur ne revendique aucun droit sur elle.
