# RHV6Fresh : build actif

Projet `lake` (`lakefile.toml`, bibliothèque `RHV6Fresh`, `defaultTargets = ["RHV6Fresh"]`). Il dépend
uniquement de `rhv3_lean` (`require`, chemin `../rhv3_lean`) et, par elle, de Mathlib.
Toolchain : `leanprover/lean4:v4.33.0-rc2` (`lean-toolchain`).

## Statut (constaté le 15 novembre 2026)

RH n'est **pas démontrée**. Le dernier journal complet de `lake build RHV6Fresh` lu (`experiments/E476_TentBreak/logs_lake_build_full.txt`,
14 novembre 2026) se termine par « Build completed successfully (9064 jobs) », sortie 0, zéro erreur ; aucun fichier Lean n'a changé depuis
(commit `14af9d52`). Nous n'avons pas relancé le build pour cette mise à jour. L'ancienne mention d'un échec sur
`Terminal/DemonstrationChain.lean` ligne 856 est périmée : le 28 octobre 2026 (commit `1c2ef553`) le but terminal est devenu l'hypothèse
nommée « montée de la fréquence attendue ». Le build vert ne démontre pas RH : `riemannHypothesis_terminal` (même fichier) prend cette
hypothèse, que `expectedFrequencyRises_iff_riemannHypothesis` prouve équivalente à RH ; il est donc conditionnel. Ses axiomes sont
`propext`, `Classical.choice`, `Quot.sound`. Aucun axiome déclaré, aucun `sorry`, aucun `admit` dans les sources.
`scripts/status.sh` relit `experiments/audit_semantique/main_build_error_20261005.txt`, daté du 27 octobre 2026 : il affiche encore un échec,
ce journal est périmé tant que `scripts/status.sh --build` n'est pas relancé.

## Build

```bash
cd formalization/RHV6Fresh
lake build RHV6Fresh          # une seule commande ; ~1,5 min en incrémental si .lake/ existe
scripts/status.sh             # affiche la sortie du dernier build (ÉTAT, BUILD, erreurs, analyse)
scripts/status.sh --build     # relance lake build RHV6Fresh, réécrit la sortie, puis affiche
```

`status.sh` lit `experiments/audit_semantique/main_build_error_20261005.txt` ; l'analyse est dans
`experiments/audit_semantique/main_build_error_analysis.md`, l'état dans `main_build_state.md`, le
verrou dans `semantic_lock.md`.

## Où lire

- `RHV6Fresh.lean` : racine, qui importe la chaîne (dont `Terminal/DemonstrationChain.lean`).
- `RHV6Fresh/Foundation/ZetaReflect.lean` : port de code tiers sous Apache 2.0, voir `THIRD_PARTY_NOTICES.md` à la racine du dépôt.
- `RHV6Fresh/Terminal/` (393 fichiers `.lean`) : chaîne terminale, modules de contrôle et de contraintes.
- `RHV6Fresh/Zeta23Port/` (134, code tiers Apache 2.0), `PNTPort/` (9, code tiers Apache 2.0), `Tower/` (7), `Direct/` (7), `Voyage/` (3), `Grammar/` (2), `Foundation/` (2), `RhGapPort/` (1) ; 560 fichiers dans `RHV6Fresh/RHV6Fresh/`, 662 au total sous `RHV6Fresh/` avec les expériences (recomptés par `find`, hors `.lake`).
- `experiments/` (200 sous-dossiers) : expériences numériques et sondes, hors graphe de build.
- `scripts/` : `status.sh`, `goal_dependencies.py` (graphe de dépendances des théorèmes), `raccord_check.py`.
- `archives/` : archives de maîtres et audits antérieurs.
- Maîtres : `RHV6final_STRATEGIE_SEMANTIQUE.md`, `RHV6final_STRATEGIE_MATHEMATIQUE.md`, `RHV6final_STRATEGIE_LEAN.md`
  (alignés sur le code après coup ; en cas de conflit avec un théorème compilé, le maître est corrigé).
- Audit : [AUDIT_SOLUTION_20261005.md](AUDIT_SOLUTION_20261005.md) ; audit sémantique
  [AUDIT_SEMANTIQUE_RHV6Fresh.md](AUDIT_SEMANTIQUE_RHV6Fresh.md).

## Règles

- Aucun `sorry`, `admit` ni axiome ajouté ; aucune prémisse équivalente à RH dans un théorème présenté comme inconditionnel.
- Un théorème qui dépend d'une hypothèse équivalente à RH est conditionnel, jamais « prouvé ».
- Ne pas déplacer ce dossier ni `rhv3_lean` (chemins relatifs lake).
- Démarche complète et contraintes : [CLAUDE.md](../../CLAUDE.md) à la racine.
- Propriété : © 2026 Charles S., enveloppe Soleau INPI n° DSO2026044645 (15/11/2026) ; voir `COPYRIGHT.md` et `THIRD_PARTY_NOTICES.md` à la racine du dépôt.

## Build par défaut allégé (2026-10-27)

`lake build RHV6Fresh` ne compile plus les certificats de rectangles des bandes 22 et 28 (`Terminal/ZetaBox22/*`,
`Terminal/ZetaBox28/*`, 100 fichiers, plusieurs heures de CPU, jusqu'à 6,5 Go par fichier). Seule la première bande
(`Terminal/ZetaBox/*`, `N(15) = 1`, l'ancre) reste dans le build par défaut. Les contrôles `N(22) = 2`, `N(28) = 3`,
`first_two_zeros_control`, `first_three_zeros_control`, `first_three_members_geometry`, `low_zero_after_certified_band` et le
module `FirstArrivalsAnchor` sont dans la cible optionnelle `RHV6FreshCertificates`
(`Terminal/FirstThreeZerosCertified.lean`) : `lake build RHV6FreshCertificates`. Aucun théorème de la chaîne ne les
consomme ; la minoration de hauteur d'un membre bas est désormais `low_member_above_15`. `ZetaBox30` (jamais importé) est
supprimé des sources (historique git conservé).
