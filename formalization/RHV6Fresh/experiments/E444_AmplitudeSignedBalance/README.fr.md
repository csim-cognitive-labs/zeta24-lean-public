> Version française conservée à titre de référence. Main language: English, see README.md.

# E444 — Le bilan signé porté par la fréquence ET l'amplitude : les contacts lisent la position radiale

Pré-enregistrement (2026-11-07), avant toute compilation et toute exécution. Suite d'E443 (§19.62) sous la
**correction de l'auteur §19.63** : les contacts retrouvent la position radiale par les formules tangentielles du
projet ; une Tour a une fréquence ET une amplitude ; l'intervalle sur l'axe réel est défini par les deux. Interdiction
spectrale en vigueur (§19.55, une seule Tour) ; ordre de travail §19.53 (on écrit le bilan, on ne chasse pas un OFF).

## Vérification des neuf erreurs
1. Aucune hypothèse nouvelle. 2. Le compilateur décide. 3. Noms vérifiés par grep (réutilisés : `contactRealValue`,
   `contactRealValue_succ`, `abs_contactRealValue_ratio`, `radial_of_contact_tangent`, `height_of_contact_log_step`,
   `cellLength_add_nat`, `meetingOffset`, `meetingOffset_eq`, `cellPrimeWeight_meeting`,
   `cellPrimeWeight_inner_eq_zero`, `lastContactBefore_of_mem_cell`, `meetingCell_displacement_lt` ; nouveaux :
   `stagePosition_sub_radial`, `towerPhase_lt_of_radial_lt`, `stagePosition_lt_of_radial_lt`,
   `radial_of_stagePosition`, `radial_of_cellFraction`, `cellLength_ratio`, `height_of_cellLength_ratio`,
   `radial_of_value_and_length_ratios`, `contactRealValue_add_nat`, `valueLengthSum`, `valueLengthSum_closed_form`,
   `valueCellSum`, `valueCellSum_eq_signed`, `valuePrimeSum`, `valuePrimeSum_eq_primes_in_block`,
   `amplitudeMeetingSum`, `valuePrimeSum_eq_meetings`, `meeting_value_step`, `meeting_value_ratio_sign`,
   `meetingOffset_lt_bertrand`). 4. `lake build RHV6Fresh` après tout changement. 5. Aucun premier ni OFF testé
   directement. 6. Position radiale : LUE par les contacts (§19.63), jamais chassée. 7. Aucune famille, une seule
   Tour. 8. Module isolé. 9. Intervalles = restes partiels.

## Question
Reprendre le bilan signé de la série (§19.60–19.62) avec les deux variables de la Tour : chaque cellule pèse par la
valeur réelle de la Tour à son contact (signe ET amplitude, `contactRealValue β T k = (−1)^k C_k^β/‖ρ‖`), et non par
son signe seul. Montrer que (i) le signe de la cellule d'un réel et la fraction de cellule lisent `β` ; (ii)
l'intervalle rend `T` par son rapport de longueurs et `β` par son rapport d'amplitudes ; (iii) le bilan des
longueurs pondéré par l'amplitude a une forme close dont la raison lit `β + 1` ; (iv) le poids premier pondéré
d'un bloc de cellules (plusieurs rencontres par cellule, au-dessus de `x*`) est la somme des rencontres pesées par
la valeur de leur cellule ; (v) entre deux rencontres consécutives, le rapport des valeurs est `(−e^{βπ/T})^{Δ}`
avec `Δ` le déplacement, borné par Bertrand : le nombre de changements de signe est `< T log 2/π + 1` et le rapport
d'amplitude lit `β`.

## Énoncés visés (module isolé `Terminal/AmplitudeSignedBalance.lean`, importe `GapsAboveThreshold` et `ContactRealValue`)
- B1 `stagePosition_sub_radial`, `towerPhase_lt_of_radial_lt`, `stagePosition_lt_of_radial_lt` : à `T` et `x` fixés,
  la position de cellule croît strictement avec `β` ; le signe de la cellule d'un réel dépend de `β`.
- B2 `radial_of_stagePosition`, `radial_of_cellFraction` : `β = T / tan(T log x − π·(cellule + fraction))`.
- B3 `cellLength_ratio`, `height_of_cellLength_ratio`, `radial_of_value_and_length_ratios` :
  `T = π/log(L_{k+1}/L_k)` et `β = log(|v_{k+1}|/|v_k|) / log(L_{k+1}/L_k)` : l'intervalle est défini par les deux.
- B4 `contactRealValue_add_nat`, `valueLengthSum_closed_form` : raison `−e^{(β+1)π/T}`.
- B5 `valueCellSum_eq_signed` : le bilan pondéré = valeur initiale × somme signée à poids géométrique `e^{βπ/T}`.
- B6 `valuePrimeSum_eq_primes_in_block`, `valuePrimeSum_eq_meetings` : rencontres pesées par leur cellule.
- B7 `meeting_value_step`, `meeting_value_ratio_sign`, `meetingOffset_lt_bertrand`.

## Expérience chiffrée (`scripts/e444a_amplitude_balance.py`, jumeau `scripts/e444b_twin_mpmath.py`)
Tours de rangs 1, 10, 100, 10³, 10⁴, 10⁵, 2·10⁶ (β = ½), rencontres jusqu'à 10⁶, Λ exact. Contrôles (0 violation
attendu) : B2 (β lu à chaque rencontre depuis la fraction de cellule), B3 (β et `T` lus sur chaque cellule), B4
(forme close), B6 (identité de bloc), B7 (rapport des valeurs et borne de Bertrand sur les changements de signe).
Mesures : **R9** part des rencontres dont le signe change quand `β` passe de ½ à `β'` ∈ {0,1 ; 0,3 ; 0,7 ; 0,9 ; 1},
contre le déplacement de phase `|arctan(T/β) − arctan(T/β')|/π` ; **R10** croissance de la somme des rencontres
pesées par l'amplitude, rapportée à la valeur de la dernière cellule ; **R11** au-dessus de `x*`, nombre de
rencontres par cellule et de changements de signe entre rencontres consécutives contre la borne de Bertrand.

## Protocole et critères
Sonde non versionnée, deux tentatives au plus pour le module définitif, journaux, `#print axioms`, build complet ;
scripts bornés (< 10 min), `nohup`, aucune sortie fabriquée. A : contradiction ; B : tout compile et 0 violation ;
C : échec en deux tentatives. Attendu : B.
