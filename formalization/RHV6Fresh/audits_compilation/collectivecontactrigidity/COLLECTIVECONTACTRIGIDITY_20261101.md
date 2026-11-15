# Journal de compilation — `Terminal/CollectiveContactRigidity.lean` (mission R9, 2026-11-01)

Commande : `lake build RHV6Fresh.Terminal.CollectiveContactRigidity`. Journaux bruts `attempt1.log`–`attempt3.log` (locaux,
`*.log` ignorés par git). Module isolé, non ajouté à `RHV6Fresh.lean`, chaîne intacte.

| Tentative | Résultat | Erreurs exactes | Correction |
|---|---|---|---|
| 1 | EXIT=1 | `import RHV6Fresh.PNTPort.Sobolev failed, environment already contains 'CS.deriv' from RHV6Fresh.Zeta23Port.FromPNTPlus.Sobolev` | le port PNT (`LogGapsTheorem`) et le port Zeta23 (CAP via `GapContactRegimes`) ne coexistent pas dans un environnement ; import retiré ; `LogGapsVanish` passé en hypothèse explicite (énoncé `Tendsto` écrit en clair) des deux théorèmes de la section 5 |
| 2 | EXIT=1 | `:204` type mismatch (`Real.pi * (Real.pi * towerPosition …)`, double réécriture par `rw [contactPhase_eq_pi_mul_position]`) ; `:304 RHV6Fresh.tailSum has already been declared` (`FirstGainPremise.lean:858`) et cascade `:309, :317, :321, :326, :327` | `towerPosition_lt_iff` reprouvé par `Iff.trans` + `simp only` ; `tailSum`/`crowdSum` renommés `gapTailSum`/`gapCrowdSum` (résidu trivial, 3ᵉ tentative journalisée) |
| 3 | **EXIT=0** | — | — |

Axiomes (`#print axioms`, 20 énoncés) : `[propext, Classical.choice, Quot.sound]` pour tous. Aucun `sorry`, `admit`, axiome.
47 théorèmes, 7 définitions (`contactLog`, `contactPhase`, `contactsCrossed`, `PrimeGapInterval.threshold`, `gapCrowdSum`,
`gapTailSum`, `CrowdRadialRigidity` — cette dernière est un BUT nommé, jamais posé).

Sonde hors build `experiments/E402_CollectiveContacts/ProbeCollectiveContactRigidity.lean` (`lake env lean`, sortie
`ProbeCollectiveContactRigidity.out.txt`) : une seule erreur, volontaire, `unsolved goals … ⊢ False`, contexte complet
(décomposition foule/queue, terme du zéro OFF isolé, borne de queue exposant 1, miroir dans la même foule, décalage des
contacts non nul, coordonnées lues sur les contacts, domination de la densité du miroir, au plus un contact traversé, F8,
`β < 1/2`). Contrôle `control_goal_closes` fermé : le but en hypothèse ferme la conclusion (identification, pas une preuve).

## Addendum R11 (2026-11-01)
| Tentative | Résultat | Modification |
|---|---|---|
| 4 (R11) | **EXIT=0** | import `LogGapsTheorem` (conflit PNT/Zeta23 résolu par réexports dans `PNTPort/`) ; `every_zero_in_some_crowd_of_logGapsVanish (hL)` → `every_zero_in_some_crowd` ; `crowdRadialRigidity_iff_riemannHypothesis` sans hypothèse. La ligne « tentative 1 » ci-dessus décrit un contournement désormais retiré. |
