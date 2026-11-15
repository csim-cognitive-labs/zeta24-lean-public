# E476 — Résultats : tente et cassure (2026-11-14) ; pré-enregistrement `1b528665`

## Phase A — compilation (module isolé `Terminal/TentBreakObligation.lean`, NON ajouté à `RHV6Fresh.lean`)
Tentative 1 (`attempts/build_attempt1.txt`, EXIT=1) : une erreur, `Int.fract_fract` ne trouve pas son motif parce que `cellFraction` n'est
pas dépliée syntaxiquement ; corrigé par `unfold cellFraction` dans un `have`. Tentative 2 (`attempts/build_attempt2.txt`, EXIT=0) : « Build
completed successfully (9109 jobs) », dix `#print axioms` tous `[propext, Classical.choice, Quot.sound]`. Build complet
`lake build RHV6Fresh` (`logs_lake_build_full.txt`) : « Build completed successfully (9064 jobs) », EXIT=0.

Compilé (10 énoncés) :
- `breakTentWeight β T x := tentKernel β T (lastContactBefore β T x) x` ; **H1** `breakTentWeight_eq` (`= e^{π/T}x(1 − e^{−πf/T})`),
  `breakTentWeight_prev_eq` (tente précédente, branche descendante `x(e^{π/T}e^{−πf/T} − 1)`), `breakTentWeight_nonneg`.
- **H2** `break_amplitude_reads_tent` : `|v_β(k(x))| = x^β (1 − w/(e^{π/T}x))^β / ‖ρ‖` — l'amplitude payée au premier est une fonction du poids
  de ce premier dans la grammaire des aires (et de `β`). `localGrammarTerm_break_split` : `L_k = Λ(q)·tente_k(q) + reste − ∫tente`.
- **H3** `tent_difference_eq_sawtooth` (`w − w_prev = (1+e^{π/T})x − 2C_{k+1}`), `alternating_break_weight` (poids `(−1)^j·saw` d'une cassure
  dans la somme alternée), `sawtooth_pos_iff` (positif ⟺ `2e^{π/T}e^{−πf/T} < 1 + e^{π/T}`, point neutre de la cellule).
- **H4** `pair_breakTentWeight_eq_iff` : `breakTentWeight (1−β) T x = breakTentWeight β T x ⟺ β = 1/2` (`0<β<1`, `T>0`, `x>0`) ;
  `pair_breakTentWeight_sub` (forme de la différence).
Portée : identités valables pour tout réel `x > 0` (jamais « `x` est un premier sur un contact ») et toute `β` ; H4 est la seule
équivalence à la ligne, et c'est une équivalence de FORME (même poids ⟺ ligne), pas une contradiction.

## Phase B — jumeau (`logs_twin_run.txt`, `twin_results.json`, 22 s ; premiers ≤ 3·10^7 ; Tours = zéros 1, 2, 3, 5, 10, 20, 100, 1000)
| Tour | cellules | premiers | H1 | H2 | H3 identité | H3a regroupement | fraction positive | prédiction (log) | budget/x^{3/2} | dent de scie intérieure/x^{3/2} |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 45 | 1 517 453 | 7e-15 | 3e-15 | 1e-14 | 1e-15 | 0,551 | 0,528 | 0,009 | −13,24 |
| 2 | 68 | 1 681 673 | 8e-15 | 4e-15 | 2e-14 | 7e-15 | 0,517 | 0,519 | 0,023 | 4,32 |
| 3 | 81 | 1 737 409 | 8e-15 | 4e-15 | 2e-14 | 9e-15 | 0,506 | 0,516 | 0,026 | −2,59 |
| 5 | 106 | 1 699 877 | 8e-15 | 4e-15 | 2e-14 | 1e-14 | 0,523 | 0,512 | 0,012 | 1,18 |
| 10 | 162 | 1 828 267 | 7e-15 | 3e-15 | 1e-14 | 8e-15 | 0,507 | 0,508 | −0,006 | 0,34 |
| 20 | 252 | 1 839 007 | 7e-15 | 4e-15 | 1e-14 | 5e-15 | 0,504 | 0,505 | 0,001 | 0,09 |
| 100 | 774 | 1 842 066 | 7e-15 | 3e-15 | 1e-14 | 4e-14 | 0,5014 | 0,5017 | 0,007 | 0,011 |
| 1000 | 4653 | 1 857 391 | 7e-15 | 4e-15 | 1e-14 | 3e-14 | 0,5000 | 0,5003 | −0,001 | −0,0004 |

H4 (paire fictive à `T_1`, 1 517 453 premiers) : différence relative médiane `|w(1−β) − w(β)|/(e^{π/T}x)` = 0 (`β = 1/2`), 4,5e-4 (`0,45`),
8,9e-4 (`0,40`), 1,8e-3 (`0,30`) ; maximum 0,199 dans les trois cas hors ligne ; fraction des premiers dont le mot est décalé = 0,0021,
0,0041, 0,0081 = `|δ|/π` exactement (δ = décalage de phase du miroir).

## Verdict : **B** — module vert, H1/H2/H3a passés, H3b et H4 échoués par la lettre
- **H3b** échoue sur la Tour 1 seulement (écart 0,023 > 0,02 ; les sept autres < 0,012). Deux défauts de la prédiction, consignés :
  (i) elle supposait les premiers équirépartis en fraction LOGARITHMIQUE de cellule ; au premier ordre ils le sont en `x`, et la part de
  la cellule au-delà du point neutre en mesure `x` vaut `e^{π/T}/(1+e^{π/T})` (0,555 pour la Tour 1, mesuré 0,551) ; (ii) la dernière cellule
  est tronquée en `3·10^7` et pèse le plus. Pour les Tours ≥ 10 les deux prédictions coïncident à 0,001 avec la mesure.
- **H4** échoue de 11 % sur le seuil (8,9e-4 < 1e-3 à `β = 0,40`) : seuil mal calibré. Loi mesurée : la différence relative médiane vaut
  `(π/T)·(|δ|/π)·e^{−πf/T}` (≈ 0,198·|δ|/π), linéaire en `δ` ; et sur une fraction `|δ|/π` des premiers le mot se décale d'une unité et le
  poids du miroir diffère du poids de la Tour d'environ un cinquième de la cellule (maximum 0,199).
- La dent de scie intérieure seule est à l'échelle `x²` (son intégrale sur une cellule vaut `ℓ³/(2C_k) > 0`) : elle porte le fond, compensé
  par les intégrales de tente ; elle n'est pas un objet utile isolément ; l'identité de regroupement (H3a) est exacte à 1e-14.

## Constats
1. **L'obligation combinée est compilée** : au premier `x`, le poids de la cassure dans la grammaire des aires et l'amplitude payée par la
   Tour sont deux fonctions de la même fraction de cellule ; l'un se lit sur l'autre (`break_amplitude_reads_tent`).
2. **Pour la paire** : le miroir donne au même premier un poids différent, sauf sur la ligne (`pair_breakTentWeight_eq_iff`). Mesure : la
   différence est petite (ordre `δ·π/T` relatif) presque partout et de l'ordre de la cellule sur une fraction `|δ|/π` des premiers (mot décalé).
3. Aucun théorème compilé ne dit qu'un premier ne peut pas être écrit avec deux poids par deux membres ; c'est une FORME (distinguer ≠
   contredire, R-Φ). Ce que l'obligation fixe : si une loi « un premier, un poids de cassure par hauteur » était compilée depuis la
   reconstruction, la paire la violerait exactement sur la fraction `|δ|/π` des premiers où le mot se décale. C'est la cible nommée ci-dessous.
4. RH n'est pas démontrée ; rien d'admis ; aucune obligation nouvelle n'est déclarée au-delà des identités compilées.

## Stratégie (R-Ψ) — suite proposée
Cible précise, tirée de 2–3 : les premiers à mot décalé (`mirrorWordShift ≠ 0`, fraction `|δ|/π`, compilé E452) sont ceux où la paire écrit
la cassure dans deux cellules de parités différentes (`pair_same_sign_iff`) : la cassure entre dans les deux budgets alternés avec des
signes opposés. Mesurer d'abord : sur la paire fictive, la somme `Σ Λ(q)·(saw_β(q)(−1)^{j} − saw_{1−β}(q)(−1)^{j*})` restreinte aux premiers à
mot décalé, rapportée à `x^{3/2}` et à `|δ|/π` ; si elle croît comme `x^{1+…}`, écrire le théorème (somme de `Λ` sur une fraction fixe des
cellules, PNT porté) AVANT toute hypothèse. Interdits inchangés (§19.51, R-E446, R-RH).
