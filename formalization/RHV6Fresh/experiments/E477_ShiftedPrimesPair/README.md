# E477 — Poids alternés de la cassure, Tour moins miroir, sur les premiers à mot décalé (pré-enregistrement, 2026-11-14)

Suite ordonnée par « continues » après E476 (§19.110) : mesure proposée en fin d'E476, exécutée AVANT toute hypothèse et sans module.
Objets : `alternating_break_weight` (poids `(−1)^j·saw(q)`, `saw = (1+e^{π/T})x − 2C_{k+1}`, E476), `mirror_cellFraction` et
`mirrorWordShift` (E450/E452 : le mot du miroir est décalé d'une unité sur une fraction `|δ|/π` des réels, `δ = φ_β − φ_{1−β}`),
`pair_same_sign_iff` (même signe dans les deux budgets alternés ⟺ même mot). Aucune coïncidence contact/premier (§19.51) ; paire fictive
(aucun zéro hors ligne connu) ; contacts réels de la Tour `(β, T)` et du miroir `(1−β, T)`.

## Stratégie (R-Ψ)
Doctrine cumulative. E476 a localisé l'endroit où une loi « un premier, un poids de cassure par hauteur » serait violée par la paire :
les premiers à mot décalé, où la cassure entre dans les deux budgets alternés avec des signes opposés. Avant de chercher un théorème,
on mesure l'ordre de grandeur de cet effet en `δ` et son échelle en `x`. Calcul préalable (consigné ici pour être testé, pas admis) :
dans la bande décalée `u = 1 − f ∈ (0, |δ|/π]`, `saw_β ≈ (e^{π/T}−1)·x > 0` et `saw_{1−β} ≈ −(e^{π/T}−1)·x < 0` ; les parités diffèrent d'une
unité ; les deux poids ALTERNÉS sont donc égaux au premier ordre et leur différence est `D = (−1)^j·(2x/T)·[e^{π/T}δ − (1+e^{π/T})πu] + O((δ/T)²·x)`,
de moyenne `(δ/T)(e^{π/T}−1)·x` sur la bande. La somme restreinte par cellule serait alors du SECOND ordre en `δ` : `S_k ≈ (−1)^j·(δ²(e^{π/T}−1)/(πT))·ℓ_k·C_{k+1}`
(masse de `Λ` sur la bande `= (|δ|/π)·ℓ_k`, PNT porté). Si la mesure confirme le second ordre, il n'y a aucun théorème à écrire sur
cette restriction : la localisation d'E476 porte un effet alterné d'échelle de fond (`x²`, constante `δ²`). Si la mesure donne un premier
ordre, écrire le théorème (somme de `Λ` sur une fraction fixe des cellules) avant toute hypothèse. Rien d'admis ; R-RH.

## Hypothèses (tests pré-écrits ; paire fictive à `T_1`, `T_10`, `T_100` ; `β ∈ {0,45 ; 0,40 ; 0,30}` ; témoin `β = 1/2`)
**P1 — fraction décalée.** Masse de `Λ` des premiers à mot décalé sur les cellules complètes, rapportée à la masse totale, `= |δ|/π` à 5 %
relatif près (mesure `x`, dernière cellule tronquée exclue).
**P2 — loi du premier ordre sur les premiers décalés.** `D = alt_β − alt_{1−β}` ; médiane de `|D − D_lin|/(x|δ|/T) ≤ 0,1` avec
`D_lin = (−1)^j(2x/T)[e^{π/T}δ − (1+e^{π/T})πu]` ; et médiane de `|D|/(x|δ|/T)` dans `[0,2 ; 3]`.
**P3 — identité sur les premiers non décalés.** `alt_β − alt_{1−β} = (−1)^{j+1}·2C_{k+1}(1 − e^{−δ/T})` exactement (même mot, même parité) :
résidu relatif < 1e-10.
**P4 — ordre en `δ` de la somme restreinte, désalternée.** `R = Σ_k (−1)^{j_k} S_k / Σ_k (δ²(e^{π/T}−1)/(πT))·ℓ_k·C_{k+1}` ; `R ∈ [0,5 ; 2]` pour `T_1`
(toutes `β`), `R ∈ [0,3 ; 3]` pour `T_10` ; `T_100` rapporté sans test (moins de mille premiers décalés).
**P5 — échelle en `x`.** Somme restreinte cumulée sur un nombre pair de cellules `S_pair(X)` : `|S_pair(X)| ≤ 3·(δ²(e^{π/T}−1)²/(πT))·X²` (bornée par
les deux dernières cellules) ; pente log-log de `|S_pair|` contre `X` sur les extrémités paires `≥ 1,7` (échelle de fond, pas `x^{3/2}`).
**P6 — décision.** `R(β)` constant à 30 % près entre `β = 0,45 ; 0,40 ; 0,30` ⟹ second ordre confirmé, aucun théorème ; `R·|δ|` constant ⟹ premier
ordre, écrire le théorème. Témoin `β = 1/2` : aucun premier décalé, `D = 0`.

## Données et exécution
Jumeau `twin_e477.py` : premiers ≤ 3·10^7, cellules à `C_k ≥ 1000`, zéros d'Odlyzko ; sortie `twin_results.json`, journal `logs_twin_run.txt`.
Aucun module Lean dans cette expérience (mesure avant hypothèse) ; `attempts/` vide.

## Verdicts
A : P1–P5 passés (P6 consigné quel qu'il soit). B : un test échoue par la lettre (loi mesurée consignée). Aucun verdict ne conclut sur RH.
