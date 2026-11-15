# E445 — Résultats : le Théorème du Prix au point de rencontre (2026-11-07)

Pré-enregistrement : commit 7b8217ca (§19.65, README.md). Module `Terminal/MeetingPriceTheorem.lean` : deux sondes non
versionnées (`logs/probe_attempt1.txt` : 5 erreurs ponctuelles ; `logs/probe_attempt2.txt` : EXIT=0), **une seule
tentative définitive** (`logs/lean_attempt1.txt`, EXIT=0, 6 `#print axioms` standards), build complet vert
(`logs/lake_build_full_trimmed.txt`, 9064 jobs). Onze déclarations, module isolé.

## Partie compilée (une Tour, sa paire en amplitudes réelles, aucune hypothèse)
- P1 `offPrice β x = cosh((β − 1/2) log x)` ; `x^β + x^{1−β} = 2 x^{1/2} · offPrice β x` : le prix exact de la paire
  OFF contre deux Tours ON de même fréquence (points 1–2 du plan).
- P2 `offPrice_ge_one`, `offPrice_ge_quadratic`, `offPrice_unbounded` : prix `≥ 1 + ((β−1/2) log x)²/2`, non borné
  dès que `β ≠ 1/2`.
- P3 `offPrice_of_meeting_values` : le prix est identifié par deux valeurs aux rencontres (point 3).
- P4 `meeting_value_bounds` : `p^β e^{−βπ/T}/‖ρ‖ < |v_rencontre| ≤ p^β/‖ρ‖` : l'amplitude à la cellule de rencontre
  est imposée par `(β, T)` (point 4).
- P5 `valueCellSum_abs_le` : **réponse à la question §19.64** : si toutes les pentes de cellule sont bornées par `D`,
  `|valueCellSum| ≤ |v_dernière| · D · q/(q−1)`, `q = e^{βπ/T}` : le bilan pondéré d'une série de cellules de
  rencontre est borné par sa dernière cellule, avec un facteur `q/(q−1) ≈ T/(βπ)` qui lit lui aussi `β`.
- P6 `price_beats_budget` : `K log x < x^r` pour `x` assez grand : le prix bat le budget d'UNE rencontre (point 5).

## Les trois tentatives de fermeture (sources `attempts/T*.lean.txt`, sorties exactes `attempts/T*_compiler_output*.txt`)
Première passe (`*_run1.txt`) : deux identifiants écrits sans la notation `C.` (`complement_break_lower_bound`,
`complement_value_eq` vivent dans `namespace OffCarrier`), et un sous-but `0 < rexp 1` mal fermé dans T2 ; corrigés,
seconde passe ci-dessous. Dans les trois cas, **toutes les étapes du corpus compilent** ; seule l'étape de fermeture
échoue, et l'erreur dit exactement ce qui manque.

- **T1 — prix contre budget à une rencontre** (porteur OFF `C`, cas miroir). Compilent : (a) la cassure moins les
  constantes est portée par le complément de la paire à chaque rencontre (`C.complement_break_lower_bound`) ; (b) le
  prix n'est pas borné (P2) ; (c) la valeur du complément = reste exact − pas de la primitive de la paire
  (`C.complement_value_eq`) ; (d) `1/2 + δ ≤ θ*` et l'exposant acquis est `1`. **Erreur exacte** (ligne 33) :
  `` `exact?` could not close the goal `` sur l'énoncé demandé
  `∃ θ K, θ < 1/2 + C.radialShift ∧ ∀ x > 1, ‖smoothedRemainder x‖ ≤ K · x^θ`. Avec cet énoncé, `False` suit par
  `C.no_remainder_bound_below_mirror`. **Statut dans le corpus** : une borne du reste sous `1/2 + δ` en présence d'un
  porteur est exactement ce que `no_offCarrier_iff_remainderExponent_half` et
  `riemannHypothesis_iff_remainderExponent_eq_half` identifient à l'absence de porteur, c'est-à-dire à RH. Prémisse
  interdite (équivalente à RH) : non ajoutée.
- **T2 — bilan pondéré de la série du miroir contre le budget cumulé.** Compilent : amplitude du miroir `(1−β, T)` à
  sa cellule de rencontre (P4) ; budget cumulé `θ(p) ≤ log 4 · p` (Mathlib `Chebyshev.theta_le_log4_mul_x`) ;
  `p^{1−β} ≤ p`. **Erreur exacte** (ligne 26) : `linarith failed to find a contradiction` sur le but
  `log 4 · p < p^{1−β} e^{−(1−β)π/T}/‖(1−β, T)‖`, avec dans le contexte `p^{1−β} ≤ p` : **l'inégalité demandée est
  fausse**, le budget cumulé est linéaire et domine le prix du miroir pour tout `β > 0`. C'est le point 8 de
  l'auteur en forme compilée : le prix bat le budget d'une rencontre (P6), jamais le budget cumulé de la série.
- **T3 — libre.** Compilent : non-compensation interne de la paire (`mirror_pair_no_internal_compensation`), prix non
  borné, norme de la primitive de la paire `≤ K x^{1+1/2+δ}`, `1/2 + δ ≤ θ*`, cassure portée par le complément,
  transfert d'une borne du complément au reste (`max(θ, 1/2 + δ)`). **Erreur exacte** (ligne 30) :
  `` `exact?` could not close the goal `` sur l'énoncé demandé `remainderExponent < 1/2 + C.radialShift`, qui
  contredirait directement `C.remainderExponent_ge_mirror`. Le compilateur dit donc : en présence d'un porteur, le prix
  de la paire est PAYÉ par l'exposant du reste (qui monte à `1/2 + δ`), il n'est pas refusé par lui ; fermer exige
  qu'aucun porteur n'existe, ce qui est RH.

**Analyse des demandes.** Les trois tentatives convergent sur un seul énoncé manquant, sous deux formes : une borne du
reste (ou du complément) d'exposant strictement inférieur à `1/2 + δ`. Le corpus (E435, §19.50) a déjà compilé que
cet énoncé équivaut à l'absence de porteur ; le point 9 du plan (« les autres contributions ne peuvent satisfaire à la
fois le budget et le prix OFF ») est exactement cet énoncé. Il ne se dérive pas des contacts, des amplitudes, du bilan
signé ni du budget par rencontre : le budget par rencontre (`log p`) est battu, le budget cumulé (`θ(p)`, linéaire)
ne l'est pas, et rien dans le corpus ne force le complément à être plus petit que le prix à une rencontre donnée.

## Expérience chiffrée (`scripts/e445a_price_budget.py`, journal `logs/e445a_log.txt`, `data/e445a_results.json`)
Sept Tours réelles (β = ½) : P4 et P5 à **0 violation** ; le rapport du bilan pondéré à sa borne P5 vaut au plus
0,44 (rang 1) et décroît avec la fréquence (facteur `q/(q−1)` = 9,5 … 7,2·10⁵). Paires témoins `(β, 1−β)` aux mêmes
fréquences, β ∈ {0,3 ; 0,4 ; 0,45} : identité P1 à 10⁻¹⁵ ; prix à 10⁶ : 7,96 / 2,12 / 1,25 ; le miroir bat le budget
d'une rencontre `log p` dès p = 641 / 2 579 / 6 421 (rang 1), 5 813 / 33 479 / 104 173 (rang 10), 78 341 / 687 317 /
jamais avant 10⁶ (rang 100), jamais avant 10⁶ aux rangs ≥ 1000 (le facteur `1/‖ρ'‖ ≈ 1/T` retarde le prix) ; **le
miroir ne bat le budget cumulé `θ(p)` sur aucune rencontre d'aucune Tour** (rapport `θ/miroir` à 10⁶ : 892 … 5,7·10⁸).
Jumeau mpmath 30 chiffres (`scripts/e445b_twin_mpmath.py`, `data/e445b_twin.json`) : P1 à 10⁻³⁰, P5 vraie sur
suites de pentes test, `all_ok = True`.

## Verdict
Partie compilée : **B** (prix exact, non borné, identifié, imposé à la rencontre, bat le budget d'une rencontre ;
question §19.64 fermée par P5). Fermeture (point 10) : **C** — trois tentatives, toutes les étapes du corpus
compilent, l'énoncé manquant est unique et équivaut à RH dans le corpus ; aucune hypothèse ajoutée.

## Révocation (auteur, 2026-11-07, §19.67)

L'auteur annule toute conclusion issue d'une étude spectrale et maintient l'interdiction spectrale sans exception.
En conséquence : les tentatives T1 et T3 (porteur `OffCarrier`, reste lissé, complément, primitive de la paire,
exposant du reste) sont ANNULÉES avec leurs conclusions ; leurs fichiers `attempts/T1*`, `attempts/T3*` sont conservés
uniquement comme preuve d'exécution. L'analyse « les trois demandes sont un seul énoncé, une borne du reste sous
`1/2 + δ` » et la question finale sur le complément sont annulées. L'import `CollectiveCurvature` du module, inutilisé,
est retiré. Restent acquis : les onze déclarations compilées sur une Tour seule, l'expérience chiffrée (0 violation,
jumeau vrai) et le constat arithmétique de T2 (budget cumulé des premiers linéaire, Tchebychev). Stratégie unique :
zéro OFF → Tour → contacts et amplitudes → prix exact à `M_n` → budget collectif (cassure arithmétique exacte aux
rencontres) → contradiction.

