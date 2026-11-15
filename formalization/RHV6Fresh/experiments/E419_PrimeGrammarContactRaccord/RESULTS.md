# E419 — résultats (exécutée le 2026-11-03, 14 s, `logs/e419.log`, `data/e419_results.json`)

| Mesure | Valeur | Lean |
|---|---|---|
| Accumulation brute par écart (2 001 052 zéros, 166 écarts p ≤ 1000) − Σ_{p<n≤q} Λ(n) | rms 0,0023, max 0,0065 | `psi_half_difference` (limite), prémisse `RawExplicitFormulaAt` |
| Indépendance du découpage (300 zéros, [101,5 ; 103,5]) : contacts propres / contacts d'une autre Tour / aucun contact | 4,4e−16 / 4,7e−16 | `contact_accumulation_partition_independent` |
| Variation de l'accumulation brute par écart sous quartet OFF (rang 2000, β = 0,3) | rms 0,051, max 0,156 ; 22,8 × le résidu de troncature | — |
| Information : valeurs par écart / paramètres de Tours | 1 valeur complexe (réelle après conjugaison) par écart / 4 002 104 | — |

## Réponse à la question centrale
**L'accumulation collective n'impose AUCUNE contrainte supplémentaire au raccord entre deux Tours successives : elle reproduit
une identité spectrale déjà connue.** Démonstration : (a) la valeur de l'accumulation sur un écart ne dépend pas du
découpage (théorème compilé + mesure 4e−16) ; elle est donc fonction des seules valeurs aux extrémités, F_ρ(q+½) − F_ρ(p+½) ;
(b) sommée sur les zéros, c'est la formule explicite sur l'écart (Σ Λ = log q pour un écart entre premiers consécutifs sans
puissance), propriété classique ; (c) une valeur par écart ne peut pas déterminer la fréquence suivante ni la position radiale
suivante (4 millions de paramètres) : la sensibilité au quartet OFF par écart (0,05) est réelle mais elle est, pour chaque
écart, une seule équation à 4 millions d'inconnues (E418 : compensable à 3e−15 par des amplitudes réelles).

## Classification des propriétés (§19 de la mission)

| Propriété | Classe | Justification |
|---|---|---|
| A. structure des intervalles de contacts | identité géométrique | `contactAt_ratio`, `contactAt_log_step` : fonction de T seul (pas) et de β (phase, en 1/T²) |
| B. entrelacement entre Tours | identité géométrique, déjà dans le corpus | `windingContact_strictAnti_height` (TowerWinding) ; aucune arithmétique |
| C. conservation des phases dans l'accumulation | identité algébrique (télescopage) | `contact_accumulation_eq_endpoint_difference` ; aucune information nouvelle |
| D. progression des fréquences | conséquence de la formule explicite + RvM | `FrequencyCap.lean` (corpus) ; projection, non lecture radiale (R12) |
| E. conditions de raccordement aux événements | conséquence de la formule explicite | `reconstructedVonMangoldt_eq`, `reconstructedPrimeEvent_iff` : contenu dans la formule lissée compilée |
| F. restrictions sur la position radiale | **formulation équivalente à RH** | la seule restriction compilée est `riemannHypothesis_of_contact_accumulation_bound`, prémisse ⟺ RH |
| G. impossibilité d'une compensation collective | **hypothèse nouvelle, non démontrée** (E418 §4 : compensation possible par amplitudes réelles) | aucune borne obtenue ; une telle borne ⟹ RH |

Aucune propriété A–E n'est une contrainte arithmétique supplémentaire ; F et G sont la cible elle-même.
