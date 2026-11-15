/-
Porté de AlexKontorovich/PrimeNumberTheoremAnd (révision 127b50e3, Apache 2.0, voir LICENSE et PROVENANCE.md),
fichier PrimeNumberTheoremAnd/Sobolev.lean.

Raccord d'intégration (directive R11, 2026-11-01) : le corps de ce fichier était, à l'en-tête près, IDENTIQUE à
`RHV6Fresh/Zeta23Port/FromPNTPlus/Sobolev.lean` (même source, même révision Mathlib cible ; `diff` vide sur les corps).
Les deux copies déclaraient `CS`, `CS.deriv`, `W1`, `W21`, `trunc` dans l'espace de noms racine, ce qui interdisait
d'importer dans un même fichier le port PNT (`LogGapsTheorem`) et les plafonds Zeta23 (`FrequencyCap`). Ce fichier
réexporte désormais la copie Zeta23 : aucune définition ni aucun théorème n'est modifié, une seule déclaration subsiste.
-/
import RHV6Fresh.Zeta23Port.FromPNTPlus.Sobolev
