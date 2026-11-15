# E441 — Résultats (exécutée 2026-11-07, après le pré-enregistrement 08b1de26)

Pièces : `logs/probe_attempt1.txt` (sonde : un seul défaut, nom de lemme `Real.exp_lt_one` → `Real.exp_lt_one_iff`),
`logs/lean_attempt1.txt` (module définitif, EXIT=0, **une seule tentative**, 13 `#print axioms` standards),
`logs/lake_build_full_trimmed.txt` (`lake build RHV6Fresh` : « Build completed successfully (9064 jobs) »),
`logs/e441a_log.txt`, `logs/e441a.stdout`, `data/e441a_results.json` (expérience chiffrée, 2,3 s),
`logs/e441b_log.txt`, `logs/e441b.stdout`, `data/e441b_twin.json` (jumeau mpmath 30 chiffres, 16 s).
Aucune sortie fabriquée ; tous les nombres ci-dessous sont lus des journaux. Deux corrections de script avant la
course définitive, consignées : (i) l'indexation des séries devait commencer à la rencontre du premier écart AYANT
un contact (hypothèse `hc 0` de M3) — la première course violait M3/M7 sur 778 séries au rang 10⁵ par cette erreur
d'indexation, pas par l'énoncé ; (ii) la règle de descente sûre (e) ne vaut que sur une cellule de rencontre dont
les deux écarts voisins ont un contact (hypothèses `hI`, `hJ` de `meeting_cellDemand`).

## Module `Terminal/MeetingSignedSeries.lean` (isolé, 13 énoncés)
M1–M2 `meetingOffset`, `meetingOffset_eq`, `meetingOffset_succ`, `meetingOffset_lt_succ`, `meetingSignedSum` ;
M3 `signedPrimeSum_eq_meetings` ; M4 `series_signed_balance` ; M5 `contactAt_add_nat_eq`, `cellLength_add_nat`,
`signedLengthSum_closed_form`, `signedLengthSum_first_last` ; M6 `cellLength_lt_of_lt_meeting`, `cellLength_eq_succ`,
`meeting_mul_lt_cellLength` ; M7 `series_balance_near_meetings`. Aucune famille, aucune position radiale.

## Contrôles compilés sur les données (7 Tours : rangs 1, 100, 10³, 10⁴, 10⁵, 10⁶, 2 001 052 ; β = ½ ; 17 983 rencontres ≤ 2·10⁵)
| contrôle | résultat |
|---|---|
| encadrement `C_m ≤ p < C_{m+1}` | 0 violation (7 Tours) ; aucune rencontre n'est un contact (0 cas ambigu) |
| déplacement lu par la fréquence (`< 1`) | 0 violation |
| pente de cellule = poids − longueur | 0 violation |
| M3 poids premier signé = somme signée des rencontres | écart max 7,8·10⁻¹⁰ absolu (sommes ~10³) |
| M4 bilan signé | 0 violation |
| M5 forme close (double / mpmath 30 chiffres) | 10⁻¹⁵ … 10⁻⁶ relatif (annulation en double au rang 10⁵) / 10⁻²⁹ … 10⁻¹⁹ |
| M6 encadrement par les rencontres extrêmes | 0 violation (double et mpmath) |
| M7 bilan à une cellule près | 0 violation |
| indices de cellule de rencontre double / mpmath | 0 différence sur 69 rencontres × 7 Tours (dont les 50 plus proches d'un contact) |

Validité des hypothèses (part des écarts ayant un contact) : 0,003 (rang 1), 0,029 (10²), 0,12 (10³), 0,46 (10⁴),
0,93 (10⁵), 1,000 (10⁶ et 2 001 052). Contacts par écart : 0,003 → 223.

## Règles lues des journaux (chacune rattachée à un énoncé compilé ou déclarée mesure)
**R1 — déplacement exact de la cellule de rencontre (0 violation sur 7 × 17 982 paires).** D'une rencontre `p` à la
suivante `p'`, la cellule avance de `⌊T·log(p'/p)/π⌋`, plus un si la fraction de cellule de `p` ajoutée à la partie
fractionnaire de `T·log(p'/p)/π` atteint un. Rattachée à `stagePosition_sub` + `lastContactBefore` ; **à compiler
(E442)**. Elle rend exacte la lecture « à moins d'une unité » de `meetingCell_series_read_by_frequency`.

**R2 — règle de signe entre rencontres consécutives (mesure).** Le signe change quand le déplacement R1 est impair.
Part de changements : 0,002 (rang 1), 0,027, 0,11, 0,37, 0,52, 0,49, 0,50. La parité de l'entier le plus proche de
`T·log(p'/p)/π` ne prédit le changement qu'à 75 % (rangs ≥ 10⁴) ; celle de sa partie entière à 50 % : **la
fréquence seule ne fixe pas le signe, la fraction de cellule à la rencontre précédente le fixe (R1)**.

**R3 — descente signée exacte (compilé, `signedLengthSum_first_last`).** La somme signée des longueurs vaut
`(première cellule − (−1)^M·r·dernière cellule)/(1 + r)`, `r = e^{π/T}` ; sur les séries longues le rapport
|descente signée| / dernière cellule vaut `r/(1+r)` : 0,5553 (rang 1), 0,5033, 0,5006, 0,5001, 0,5000 (mesuré
0,50001 aux rangs 10⁶ et 2 001 052 où les séries couvrent tout l'intervalle). **La descente ne s'annule pas tout à
fait : il en reste exactement la moitié de la dernière cellule (à la première cellule près), signe `(−1)^{M+1}`.**

**R4 — seuil de montée des cellules de rencontre (sûre-zones compilées B7 + M6, 0 violation).** La cellule de
rencontre est plus courte que le poids `log p` jusqu'au seuil `x*` défini par `x*(r − 1) = log x*`, c'est-à-dire
`x* ≈ (T/π)·log x*` : plus grand `p` montant / plus petit `p` ne montant pas = 457 / 461 (x* = 458,3, rang 100),
3 709 / 3 719 (3 709,2), 32 653 / 32 687 (32 676,9) ; 100 % montent sous `x*`, 0 % au-delà de `x*·r`. Sous `x*`,
`p·(r−1) ≤ log p` suffit (compilé via `cellLength_lt_of_lt_meeting` : à compiler comme corollaire, E442) ; au-delà de
`x*·r`, `p·(1 − 1/r) > log p + poids non premiers` force la descente (`meeting_mul_lt_cellLength`, à compiler,
E442). Sur les cellules de rencontre dont les deux écarts voisins ont un contact, la part qui monte en pente
réelle (poids non premiers compris) est 0,67–0,71 aux rangs 10²–10⁴ et 1,000 aux rangs ≥ 10⁵ (tout `p ≤ 2·10⁵ < x*`).

**R5 — croissance de la somme signée des rencontres (mesure, aucun théorème).** Sur la plus longue série (jusqu'à
17 981 rencontres), |S_J| / (√J · log p) reste entre 0,25 et 2,1 (valeur finale 0,59–1,41) : **aucune croissance
linéaire en J**, les signes des rencontres se compensent comme une marche. Et |S_J| dépasse la borne de la descente
non annulée `p_{n+J+1}(r−1)` dès que `p < x*` (rapport 0,8 au rang 1 où `p = 17 > x* = 8,7` ; 12, 24, 30, 461,
2 079, 4 152 ensuite) : **le même seuil R4 sépare le régime où la descente résiduelle domine (p > x*) de celui où
seules les rencontres signées comptent (p < x*).**

**Cas général (mesure, 2 000 séries aléatoires par Tour, écarts sans contact compris).** Le poids premier signé des
cellules `[m_a, m_b)` est la somme, sur les premiers `q` avec `C_{m_a} < q ≤ ⌊C_{m_b}⌋`, de `(−1)^{m(q) − m_a}·log q`
(écart max 4·10⁻¹⁰) : les rencontres partageant une cellule portent le même signe ; les termes en plus ou en moins
par rapport à l'indexation par écarts : 47 268 (rang 1) → 0 (rangs ≥ 10⁶). **À compiler sans hypothèse (E442).**

## Verdict
**B** : tout compile en une tentative, toutes les identités à 0 violation, jumeau conforme. Rien n'est déclaré
manquant. Les règles R1, R4 (deux corollaires) et le cas général sont des énoncés à compiler (E442) ; R2, R3, R5 sont
des mesures rattachées aux énoncés compilés.
