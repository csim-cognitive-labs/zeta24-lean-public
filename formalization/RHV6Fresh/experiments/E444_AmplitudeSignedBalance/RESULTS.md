# E444 — Résultats : le bilan signé porté par la fréquence ET l'amplitude (2026-11-07)

Pré-enregistrement : commit d5efbb2a (README.md). Module `Terminal/AmplitudeSignedBalance.lean` : deux sondes non
versionnées (`logs/probe_attempt1.txt` : 7 erreurs, dont un doublon de `contactRealValue_add_nat` déjà dans
`GapSlopeByContacts` ; `logs/probe_attempt2.txt` : EXIT=0), **une seule tentative définitive** (`logs/lean_attempt1.txt`,
EXIT=0, 9 `#print axioms` standards), build complet vert (`logs/lake_build_full_trimmed.txt`, 9064 jobs). Vingt
déclarations, module isolé.

## Compilé
- B1 `stagePosition_sub_radial`, `towerPhase_lt_of_radial_lt`, `stagePosition_lt_of_radial_lt` : à fréquence et point
  fixés, la position de cellule croît strictement avec la position radiale ; le signe de la cellule d'un réel dépend
  de la position radiale (par la phase `arctan(T/β)` des contacts).
- B2 `radial_of_stagePosition`, `radial_of_cellFraction` : la position radiale se lit depuis le numéro de cellule et la
  fraction de cellule d'un point quelconque (formule tangentielle).
- B3 `cellLength_ratio`, `height_of_cellLength_ratio`, `radial_of_value_and_length_ratios` : une cellule rend la fréquence
  par le rapport de deux longueurs consécutives et la position radiale par le rapport des amplitudes aux contacts
  divisé par celui des longueurs : **l'intervalle est défini par les deux variables.**
- B4 `valueLengthSum_closed_form` : la descente pondérée par la valeur de la Tour à chaque contact a une forme close de
  raison `−e^{(β+1)π/T}` : la raison lit `β + 1`, là où la forme close des signes seuls (E441) lisait `T` seul.
- B5 `valueCellSum_eq_signed` : le bilan pondéré = valeur initiale × somme signée à poids géométrique `e^{βπ/T}`.
- B6 `valuePrimeSum_eq_primes_in_block`, `valuePrimeSum_eq_meetings` : le poids premier pondéré d'un bloc (plusieurs
  rencontres par cellule, au-dessus de `x*`) et d'une série de rencontres est la somme des rencontres pesées par la
  valeur de leur cellule (signe ET amplitude).
- B7 `meeting_value_step`, `meeting_value_ratio_sign`, `radial_of_meeting_values`, `meetingOffset_lt_bertrand` :
  entre deux rencontres le rapport des valeurs est `(−e^{βπ/T})^Δ` ; le signe change selon la parité du déplacement,
  l'amplitude rend `β` exactement ; `Δ < T log 2/π + 1`.

## Expérience chiffrée (`scripts/e444a_amplitude_balance.py`, journal `logs/e444a_log.txt`, données `data/e444a_results.json`)
Sept Tours (rangs 1, 10, 100, 10³, 10⁴, 10⁵, 2·10⁶ ; β = ½), 78 497 rencontres ≤ 10⁶, Λ exact par crible.
**Contrôles B2, B3, B4, B6 (bloc et série), B7 : 0 violation sur les sept Tours**, à budgets d'erreur float64
explicites (annulation de `T log p` et sensibilité de la tangente près de `π/2` pour B2 ; erreur relative d'une
longueur `eps·C/L` amplifiée par `T/π` pour B3–B4). Corrections de script consignées : (1) plages d'indices pour la
Tour de rang 1 (63 cellules seulement) ; (2) tolérances fixes 10⁻⁸/10⁻⁹ remplacées par les budgets ci-dessus (les
« violations » de la première course aux rangs ≥ 10⁴ étaient des pertes de précision machine, confirmé par le jumeau).

**Jumeau déterministe** (`scripts/e444b_twin_mpmath.py`, 30 chiffres, 50 rencontres par Tour, `data/e444b_twin.json`) :
B2, B3, B4, B7 vrais sur les sept Tours (`all_ok = True`) ; la lecture de `β` par le rapport des amplitudes entre deux
rencontres (B7) s'écarte de ½ de moins de 5·10⁻²⁹ sur toutes les Tours ; la lecture par la fraction de cellule (B2)
reste dans le budget d'annulation (10⁻²⁸ au rang 1, 3·10⁻¹⁸ au rang 2·10⁶ pour un budget de 2·10⁻¹⁵).

## Règles lues des journaux
- **R9 (mesure, règle de signes).** Quand la position radiale passe de ½ à `β'`, la part des rencontres dont le signe
  de cellule change est le déplacement de phase `|arctan(T/½) − arctan(T/β')|/π` (en cellules) : rang 1 : 0,0087 /
  0,0090 (β' = 0,1), 0,0109 / 0,0112 (β' = 1) ; rang 10 : 0,0028 / 0,0026 ; rang 100 : 0,00066 / 0,00054 (52
  contre 42 événements) ; rang 1000 : 5 à 11 événements contre 3 à 9 attendus ; au-delà, déplacement < 10⁻⁵ cellule et
  0 à 1 événement sur 78 497. La sensibilité des signes à `β` est `|Δβ|/(πT)` par rencontre : réelle, exacte, et
  d'autant plus petite que la fréquence est grande ; c'est l'amplitude (B7) qui lit `β` sans perte à toute fréquence.
- **R10 (mesure, sans règle stable).** La somme des rencontres pesées par l'amplitude n'a pas de loi en `√J` : ses
  exposants ajustés vont de 0,7 à 4,8 selon la Tour, et son rapport à l'amplitude de la dernière rencontre fois `√J`
  va de 0,26 à 171. Elle est gouvernée par ses dernières cellules, comme la forme close B4 l'impose (poids
  géométrique de raison > 1) : c'est une quantité de dernière cellule, non de comptage.
- **R11 (mesure).** Au-dessus de `x*`, rencontres par cellule (moyenne) : 1 510 (rang 1), 516, 138, 32, 7,3, 2,1
  (rang 10⁵) ; part des rencontres consécutives dans la même cellule : 0,999 → 0,52 ; part des déplacements impairs
  (changement de signe) : 0,0006 → 0,42 ; déplacement maximal observé 1, 2, 3, 3, 5, 7 contre une borne de Bertrand
  4, 12, 53, 314, 2 180, 16 531 : la borne de Bertrand est vraie et très lâche au-dessus de `x*` ; le nombre exact de
  changements de signe entre deux rencontres reste donné par la règle R1 (§19.60), fraction de cellule comprise, donc
  lit `β`.

## Verdict
**B.** Tout compile, 0 violation, jumeau vrai. Rien n'est déclaré manquant. Une seule Tour, ses contacts, ses valeurs,
ses cellules ; aucune somme de Tours. La position radiale n'est pas chassée : elle est lue par les contacts, comme
l'auteur l'a rappelé (§19.63).
