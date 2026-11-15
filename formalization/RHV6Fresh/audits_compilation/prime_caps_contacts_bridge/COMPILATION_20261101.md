# Journal de compilation — directive R11 (2026-11-01)

Journaux bruts locaux (`*.log`, ignorés par git) : `port_attempt1.log`, `bridge_attempt1.log`, `bridge_attempt2.log`.

| Cible | Tentative | Résultat | Erreurs exactes | Correction |
|---|---|---|---|---|
| `RHV6Fresh.Terminal.LogGapsTheorem` + `SummitVertical` après réexport des trois fichiers `PNTPort` | 1 | **EXIT=0** (Wiener 38 s, Consequences 28 s) | — | — |
| sonde de coexistence (`LogGapsTheorem` + `FrequencyCap` + `CollectiveContactRigidity`, `lake env lean`) | 1 | **EXIT=0** | — | — |
| `RHV6Fresh.Terminal.CollectiveContactRigidity` (hypothèses `hL` supprimées, import `LogGapsTheorem`) | 1 | **EXIT=0** | — | — |
| `RHV6Fresh.RhGapPort.PrimesDetermineZeros` | 1 | **EXIT=0** | — | — |
| `RHV6Fresh.Terminal.PrimeCapsContactsBridge` | 1 | **EXIT=0** | — (avertissements : `Set.mem_setOf_eq` déprécié, `push_neg` déprécié, un énoncé `rfl` de portée inutile) | nettoyage : `Set.mem_ofPred_eq`, `push Not`, énoncé `rfl` retiré |
| `RHV6Fresh.Terminal.PrimeCapsContactsBridge` | 2 | **EXIT=0** | — | — |
| `RHV6Fresh.Terminal.DemonstrationChain` (vérification chaîne) | 1 | **EXIT=0** | — | — |
| `lake build` (cible par défaut `RHV6Fresh`) | 1 | EXIT=1 | `RHV6Fresh.lean:1:0: import RHV6Fresh.Terminal.SpectralWindowProjection failed, environment already contains 'RHV6Fresh.windowProjection' from RHV6Fresh.Terminal.GapTranslationInvariance` | **préexistant, fichiers non touchés, non corrigé** (chaîne/agrégateur : question à l'auteur, voir REPORT.md §8) |

Axiomes : `#print axioms` sur 8 énoncés du port et 17 du raccordement, tous `[propext, Classical.choice, Quot.sound]`.
Sonde hors build `ProbePrimeCapsContactsBridge.lean` : une seule erreur, volontaire, `unsolved goals … ⊢ False` (EXIT=1 attendu) ;
`control_goal_closes` se ferme.
