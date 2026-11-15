# E476 — Tente et cassure : l'obligation du poids de la cassure (pré-enregistrement, 2026-11-14)

Ordre de l'auteur : « tu peux utiliser la méthode combinée entre ta tente et la cassure, cela crée une obligation ; continue ».
Objets combinés : la tente d'E474 (`tentKernel`, `localGrammarTerm_eq_tent_sum`) et la cassure au premier d'E447/E450
(`break_amplitude_exact` : amplitude exacte de la valeur au dernier contact avant `x`, `contact_of_fraction`, `mirror_cellFraction`).

## Stratégie (R-Ψ)
Doctrine cumulative. La cassure de la demande en un premier `q` (saut `Λ(q)`) entre dans le terme local `L_k` avec le poids
`Λ(q)·tente_k(q)` (Abel : `L_k = −∫ D·tente_k'`) ; la Tour paie en `q` l'amplitude `q^β e^{−βπf/T}/‖ρ‖`, `f` = fraction de cellule de `q`.
Les deux sont fonctions de la MÊME fraction `f`, qui est une donnée de position de `q` par rapport aux contacts (reste partiel d'écart,
§19.51 : on ne suppose jamais `q` sur un contact). L'obligation : le poids de la cassure dans la grammaire des aires est fixé par l'amplitude
payée (et `β`), et le poids que le miroir donne au MÊME premier diffère de celui de la Tour dès que `β ≠ 1/2`. On ne pose aucune
contradiction ; on écrit la forme exacte et on la mesure. Aucune somme infinie prise pour objet ; contacts ≠ premiers.

## Hypothèses (tests pré-écrits)
**H1 — poids de tente de la cassure (théorèmes).** `breakTentWeight β T x := tentKernel β T (lastContactBefore β T x) x
= e^{π/T}·x·(1 − e^{−πf/T})` (branche montante de la cellule qui contient `x`) ; tente précédente `tentKernel (k−1) x = x(e^{π/T}e^{−πf/T} − 1)`.
Jumeau : résidu relatif < 1e-10 sur tous les premiers de toutes les cellules.
**H2 — la cassure lit la tente (théorème).** `|v_β(k(x))| = x^β (1 − w/(e^{π/T}x))^β / ‖ρ‖`, `w = breakTentWeight` : l'amplitude payée par la
Tour au premier est une fonction du poids de ce premier dans sa grammaire. Jumeau : résidu relatif < 1e-10.
**H3 — dent de scie du budget alterné (théorèmes + test de regroupement).** Un premier `x` dans la cellule `k` appartient à deux tentes
(`k−1` et `k`) ; dans la somme alternée des termes locaux son poids est `(−1)^j·((1+e^{π/T})x − 2C_{k+1})`, nul au point neutre
`f₀ = (T/π)·log(2e^{π/T}/(1+e^{π/T}))`, négatif avant, positif après. Compilé : `tent_difference_eq_sawtooth`, `alternating_break_weight`,
`sawtooth_pos_iff`. Jumeau : (a) regroupement `Σ_{n<N}(−1)^n L_{k₀+n} = Σ_q Λ(q)(−1)^{j(q)} saw(q) + bords − Σ(−1)^n ∫tente` à 1e-9 relatif
(identité à compiler ensuite si elle passe) ; (b) fraction des premiers à poids positif = `1 − f₀` à 0,02 près pour les Tours à ≥ 10⁴ premiers.
**H4 — obligation de la paire (théorème).** `breakTentWeight (1−β) T x = breakTentWeight β T x ⟺ β = 1/2` (pour `0<β<1`, `T>0`, `x>0`) :
le miroir ne donne jamais au premier partagé le poids que lui donne la Tour, sauf sur la ligne. Jumeau : pour la paire fictive à `T_1`,
différence relative médiane `|w(1−β) − w(β)|/(e^{π/T}x)` < 1e-12 à `β = 1/2`, > 1e-3 à `β = 0,40`.

## Modules et données
Module isolé `RHV6Fresh/Terminal/TentBreakObligation.lean` (importe `CellAreaTent`, `PairBreakAtPrime` ; NON ajouté à `RHV6Fresh.lean`) ;
deux tentatives max (`attempts/`). Jumeau `twin_e476.py` : premiers ≤ 3·10^7, Tours = zéros n° 1, 2, 3, 5, 10, 20, 100, 1000, `β = 1/2`,
cellules à `C_k ≥ 1000`. Ordre TDD : jumeau et compilation lancés en parallèle après ce commit ; verdict sur les deux.

## Verdicts
A : H1–H4 passés et module vert. B : module vert, un test jumeau échoue par la lettre (consigné). C : module rouge après deux tentatives.
Aucun verdict ne conclut sur RH ; R-RH ; rien d'admis.
