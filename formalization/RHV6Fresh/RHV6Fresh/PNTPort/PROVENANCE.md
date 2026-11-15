# PNTPort — port du théorème des nombres premiers (forme de Tchebychev) vers notre révision de Mathlib

Source : https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, révision `127b50e33f6033e2147921167a117af96d9ba4ea`
(épinglée sur Lean `v4.35.0` et Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, 2026-10-13). Licence Apache 2.0
(fichier `LICENSE` copié). Clôture d'imports, dans ce projet, du théorème `chebyshev_asymptotic : θ ~[atTop] id`
(`PrimeNumberTheoremAnd/Consequences.lean`) : neuf fichiers.

| Fichier porté | Lignes source |
|---|---|
| `Consequences.lean` | 2566 |
| `Wiener.lean` (théorème de Wiener–Ikehara) | 4385 |
| `Defs.lean` | 304 |
| `Fourier.lean` | 187 |
| `SmoothExistence.lean` | 107 |
| `Sobolev.lean` | 359 |
| `Mathlib/Algebra/Notation/Support.lean` | 13 |
| `Mathlib/Analysis/Asymptotics/Asymptotics.lean` | 41 |
| `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | 17 |

Transformations mécaniques (script, 2026-10-29) : `import Architect` retiré ; attributs `@[blueprint …]` et commandes
`blueprint_comment …` (outil LeanArchitect) retirés ; imports `PrimeNumberTheoremAnd.*` renommés `RHV6Fresh.PNTPort.*` ;
en-tête de provenance ajouté à chaque fichier. Les corrections de portage (dérive d'API entre les deux révisions de
Mathlib, 3 août → 13 octobre 2026) sont marquées par un commentaire `-- port :` dans le corps.

Cible : notre Lean `v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129` (2026-08-03). Même précédent que
`RHV6Fresh/Zeta23Port/FromPNTPlus` (port de pièces du même projet par anthropics/formal-math).

Usage prévu : `RHV6Fresh.chebyshevAsymptotic_of_isEquivalent` (`Terminal/ChebyshevAsymptoticToLogGaps.lean`) reçoit
`chebyshev_asymptotic` ; aucune autre pièce n'est consommée. Ce dossier n'est pas importé par `RHV6Fresh.lean` ni par la
chaîne. État du port : voir le maître §18.2.

Raccord R11 (2026-11-01) : `Sobolev.lean`, `Fourier.lean` et `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` sont devenus des
réexports de leurs copies identiques dans `RHV6Fresh/Zeta23Port/FromPNTPlus/` (double déclaration racine `CS`, `W1`, `e`,
`Real.tendsto_pow_log_div_pow_atTop` ; `diff` vide sur les corps). Aucun énoncé modifié ; les deux ports coexistent désormais.
