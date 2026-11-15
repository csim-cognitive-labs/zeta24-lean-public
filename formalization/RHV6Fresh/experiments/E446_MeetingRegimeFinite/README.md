# E446 — Le régime « une rencontre par cellule » est fini : pré-enregistrement (copie du §19.68, 2026-11-07)

### 19.68 Le budget collectif par les seuls objets autorisés : le régime « une rencontre par cellule » est fini (pré-enregistrement d'E446, 2026-11-07)

**Ordre de l'auteur.** « Planifie, émets des hypothèses, vérifie avec les expériences, reste dans le cadre, produis du
Lean qui implémente la cause racine du constat, avance. » Cadre : stratégie unique de §19.67, objets autorisés
seulement (une Tour, ses contacts, ses cellules, ses valeurs ; les premiers, `rawDemand`, `cellWeight`,
`cellPrimeWeight`, `cellDemand` ; les théorèmes compilés du corpus, dont `logGapsVanish_holds` et `WeakPNT''`).

**Constat à expliquer (E445, T2 et P6).** Le prix d'une rencontre (`x^β`, P6) bat le budget d'UNE rencontre (`log p`),
jamais le budget cumulé. **Cause racine proposée (hypothèses H1–H3).**
* **H1 (régime fini).** Tous les énoncés « la cellule de rencontre franchit exactement un premier » (`meeting_cell_primes`,
  `cellPrimeWeight_meeting`, `meeting_cellDemand`, `valuePrimeSum_eq_meetings`, `amplitudeMeetingSum`) supposent que
  l'écart `[p_n, p_{n+1}]` ET l'écart suivant contiennent chacun un contact. Ces deux hypothèses placent une cellule entière
  `[C_k, C_{k+1}]` dans `]p_n, p_{n+2}]`, donc `log p_{n+2} − log p_n ≥ π/T`. Or `logGapsVanish_holds` (PNT porté) donne
  `log p_{n+1} − log p_n → 0`. Donc pour toute Tour `(β, T)` il existe un rang `N(β, T)` au-delà duquel deux écarts
  consécutifs n'ont jamais chacun un contact : la série des rencontres à un premier par cellule est FINIE. Le prix à
  `M_n` n'est confronté au budget `log p` d'une rencontre que sur un segment initial fini.
* **H2 (le budget exact d'une cellule est sa longueur, au premier ordre).** Au-delà du régime, une cellule contient
  plusieurs premiers ; son budget exact est `cellWeight = ψ(C_{k+1}) − ψ(C_k)` et, par `WeakPNT''`,
  `cellWeight/cellLength → 1`, `cellDemand/cellLength → 0`. Le « budget collectif » d'une cellule n'est pas `log p`
  mais la longueur de la cellule, à un reste près qui est la variation de `rawDemand` sur la cellule.
* **H3 (le prix d'une Tour sur sa cellule est négligeable devant ce budget).** Le pas d'une Tour `(β, T)` sur sa propre
  cellule vaut `|v_{k+1} − v_k| = (1 + e^{βπ/T}) C_k^β/‖ρ‖` ; divisé par la longueur `C_k (e^{π/T} − 1)` il tend vers zéro
  pour tout `0 < β < 1`, ON ou OFF. P6 vaut aussi pour `β = 1/2` (`price_beats_budget_on_line`) : la lecture « le prix
  OFF bat le budget » n'était pas discriminante.

**Pré-enregistrement E446 (`experiments/E446_MeetingRegimeFinite/`).** Module isolé `Terminal/MeetingRegimeFinite.lean`
(importe `MeetingPriceTheorem` et `LogGapsTheorem`) : F1 `meeting_cell_within_two_gaps` ; F2 `log_ratio_ge_cell_of_meeting`
(`π/T ≤ log p_{n+2} − log p_n`) ; F3 `two_consecutive_contacts_finite` (∃ N, ∀ n ≥ N, ¬(contact dans l'écart n ∧ contact
dans l'écart n+1)) ; F4 `meeting_series_rank_bounded`, `meeting_break_rank_bounded` (les hypothèses de
`cellPrimeWeight_meeting` et de `valuePrimeSum_eq_meetings` ne sont satisfaites qu'à rang borné) ; F5
`cellWeight_eq_psi_diff`, `contactAt_tendsto_atTop`, `cellWeight_div_cellLength_tendsto_one` ; F6
`cellDemand_div_cellLength_tendsto_zero` ; F7 `tower_step_div_cellLength_tendsto_zero` ; F8 `price_beats_budget_on_line` ;
F9 `valueNonPrimeSum`, `valuePrimeSum_balance` (budget pondéré des premiers d'un bloc = demande pondérée − poids non
premiers pondérés + longueurs pondérées, forme close B4). Deux tentatives de compilation au plus, sorties conservées dans
`attempts/`. **Expérience chiffrée** (`scripts/e446a_regime.py`, premiers ≤ 10⁷) : pour les sept Tours réelles et les
paires témoins `β ∈ {0,3 ; 0,4 ; 0,45}`, (a) dernier rang `N_obs` où deux écarts consécutifs ont chacun un contact, nombre
de tels rangs, et contrôle de F2 sur chacun (0 violation attendu) ; (b) `cellWeight/cellLength` et `cellDemand/cellLength`
par décade de `C_k` (écart à 1, resp. à 0, décroissant attendu) ; (c) pas de la Tour sur sa cellule contre la longueur
(formule F7 à 10⁻¹², décroissance attendue). **Jumeau** (`scripts/e446b_twin_mpmath.py`, 30 chiffres) : mêmes rangs `N_obs`
et mêmes rapports sur un échantillon de cellules. **Critère** : A si F1–F9 compilent et (a)–(c) sont conformes ; B si une
partie compile ; C sinon. Prédictions : `N_obs` fini pour chaque Tour, croissant avec `T` ; `N_obs` plus grand pour le
miroir `1 − β` que pour `β` ? (non prédit : la phase `arctan(T/β)` décale les contacts, la condition F2 ne dépend que de `T`
mais le rang effectif dépend des deux).

**Ce que cela change dans la stratégie.** L'étape « budget collectif » ne peut pas être « prix à `M_n` contre `log p` sur
la série » : cette série est finie. Le budget collectif exact d'une cellule est sa longueur plus la variation de la
demande brute sur la cellule ; le prix d'une Tour sur sa cellule lui est négligeable. La confrontation ne peut porter que
sur la variation de `rawDemand` sur la cellule (objet autorisé), dont le corpus ne sait que `o(cellule)` (F6). Aucune
relation compilée ne lie l'amplitude d'une Tour à cette variation : c'est l'obligation ouverte, consignée sans objet
spectral. [RETIRÉE par l'auteur le 2026-11-07 : voir « Correction de l'auteur » en fin de section.]
