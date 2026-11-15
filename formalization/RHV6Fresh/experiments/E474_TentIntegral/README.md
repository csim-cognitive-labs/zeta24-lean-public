# E474 — Tente, mémoire un, intégrale : quatre hypothèses fermées en TDD (2026-11-13)

Ordre de l'auteur : « émets des hypothèses, au moins 3 ou 4, et aide-toi du compilateur et d'expériences pour fermer en TDD ».
Point de départ : E473 (§19.106) a compilé la grammaire locale `a_{k+1} − e^{π/T} a_k = L_k`, `L_k = ε_{k+1} + e^{π/T} η_k`, et conclu
honnêtement qu'aucune obligation nouvelle qui borne n'avait été trouvée. Ici chaque hypothèse est d'abord un TEST (seuil chiffré,
pré-écrit), puis le jumeau le fait passer ou échouer sur les premiers réels, puis le compilateur ferme ce que le jumeau soutient.

## Stratégie (R-Ψ)
Doctrine cumulative inchangée : OFF → Tour → contacts/amplitudes → prix → budget collectif arithmétique → contradiction. Cible unique
(§19.105) : `arithmeticAlternatingBudget T x N / x_N^{3/2}` borné. E473 a réduit la cible au terme local `L_k` sur deux cellules
consécutives. E474 cherche la FORME ARITHMÉTIQUE EXACTE de `L_k` (hypothèse 1 : somme des premiers contre une tente), sa STRUCTURE DE
MÉMOIRE (hypothèse 2 : mémoire un), sa LOI D'ÉCHELLE en la hauteur (hypothèse 3) et son CONTRÔLE PAR LA DEMANDE INTÉRIEURE À LA
CELLULE (hypothèse 4, représentation intégrale). Toute borne compilée a des antécédents explicites ; rien n'est admis ; R-RH : un
antécédent de force RH n'est ni une objection ni un frein, seul son admission comme prémisse est interdite. Jamais « frontière ».

## Les quatre hypothèses (tests pré-écrits)
**H1 — identité de la tente.** `L_k = Σ_{n ∈ (C_k, C_{k+2}]} Λ(n)·tente_k(n) − e^{π/T}(1+e^{π/T}) ℓ_k²/2`, où `tente_k(n) =
min(e^{π/T}(n − C_k), C_{k+2} − n)` est la fonction chapeau continue de sommet `C_{k+1}`, hauteur `ℓ_{k+1}`. Le terme local est la
discrépance de la somme des premiers contre un noyau chapeau exact (intégrale de la tente = `e^{π/T}(1+e^{π/T})ℓ_k²/2`).
Test jumeau : résidu / ℓ_k² < 1e-10 sur toutes les cellules. Compilation : théorème (module 1).

**H2 — mémoire un.** `L_k = ε_{k+1} − e^{π/T} ε_k + e^{π/T} ℓ_k Δ_k` avec `Δ_k = rawDemand C_{k+1} − rawDemand C_k` (identité, module 1).
Prédiction mesurable (raisonnement côté zéros, NON compilé) : les cellules de la Tour n°1 sont des demi-périodes de l'oscillation
dominante, donc les termes locaux voisins s'opposent ; pour une Tour haute les cellules sont fines devant les oscillations basses,
donc les termes locaux voisins se suivent. Test jumeau : autocorrélation de décalage 1 de `L_k/C_k^{3/2}` : Tour 1 < −0,2 ;
Tour 1000 > +0,2 ; et pour toute Tour |corr(décalage j)| décroît de j = 1 à j = 5 (non strictement, tolérance 0,05).

**H3 — loi d'échelle en 1/T.** `T · |L_k| / C_k^{3/2} ≤ 3` sur toutes les cellules de toutes les Tours testées (zéros n° 1, 2, 3, 5,
10, 20, 50, 100, 200, 500, 1000, 2000, 5000 ; `10^3 ≤ C_k`, `C_{k+2} ≤ 3·10^7`). Explication compilée visée (module 2) :
`|L_k| ≤ 2 e^{π/T} ℓ_k · M_k` où `M_k` majore `|rawDemand|` sur les deux cellules, et `ℓ_k = (e^{π/T} − 1) C_k` avec
`T(e^{π/T} − 1) → π` : la loi en 1/T ⟸ demande à l'échelle `√x`. Test jumeau : inégalité vérifiée numériquement sur chaque cellule
(sanité) et rapport `|L_k| / (2 e^{π/T} ℓ_k M_k)` mesuré (serrage).

**H4 — contrôle intérieur à la cellule.** `ε_k = ∫_{C_k}^{C_{k+1}} (rawDemand t − rawDemand C_k) dt` (module 2 : `demandArea` EST
l'intégrale de `rawDemand`, par la sommation d'Abel de Mathlib) ; donc `|ε_k| ≤ ℓ_k · V_k` où `V_k` majore la variation de la demande
à l'intérieur de la cellule. Tests jumeau : (a) `|ε_k| / (ℓ_k √C_k) ≤ 3` et `|Δ_k| / √C_k ≤ 3` sur toutes les cellules ; (b) les deux
parts de H2 (`ε_{k+1} − e^{π/T} ε_k` et `e^{π/T} ℓ_k Δ_k`) sont du même ordre : rapport de leurs moyennes quadratiques dans [1/3, 3].

## Clôture conditionnelle visée (module 2, antécédent explicite)
Si `|rawDemand t| ≤ M` sur la fenêtre `(C_{k₀}, C_{k₀+N+1}]`, alors `(1+e^{π/T}) |A_N| ≤ M (1+e^{π/T})² C_{k₀+N}` : le budget à
l'échelle `x_N` est contrôlé par le suprémum de la demande sur la fenêtre, avec constante explicite ; l'alternance n'y intervient pas.
Conséquence lue (non compilée) : budget à l'échelle de la ligne ⟸ demande en `√x·(log x)²` sur la fenêtre (force RH, R-RH).
On NE prétend pas que cette réduction soit une obligation nouvelle : c'est la forme la plus courte du même antécédent.

## Phase A — modules isolés (jamais ajoutés à `RHV6Fresh.lean`), deux tentatives maximum chacun, journal dans `attempts/`
* Module 1 `Terminal/CellAreaTent.lean` : `tentKernel`, `localGrammarTerm_eq_tent_sum` (H1), `localGrammarTerm_eq_memory_one` (H2),
  `alternating_local_eq_exit_form` (somme alternée des termes locaux écrite sur les déviations de sortie et les variations de demande),
  `tent_integral_eq`, `tentKernel_nonneg`, `tentKernel_le`.
* Module 2 `Terminal/CellAreaIntegral.lean` : `integral_psi_eq`, `demandArea_eq_integral`, `abs_demandArea_le_of_bound`,
  `exitDeviation_eq_integral`, `abs_exitDeviation_le_of_variation`, `abs_localGrammarTerm_le_of_demand_bound`, `sum_cellLength_eq`,
  `budget_le_of_demand_bound`.

## Phase B — jumeau `twin_e474.py` (nohup, borné), premiers réels ≤ 3·10^7, contacts réels (β = 1/2), formule de cellule (R-Ψ quater)
Sorties : `twin_results.json`, `logs_twin_run.txt`.

## Verdicts
A : H1 à 1e-10, inégalités compilées vérifiées numériquement, H2/H3/H4 tous passés. B : identités conformes, au moins un seuil
quantitatif (H2, H3, H4) échoue — consigné tel quel, c'est le résultat. C : une identité (H1 ou l'inégalité de H3) échoue → erreur
de définition, à chercher avant toute compilation.
