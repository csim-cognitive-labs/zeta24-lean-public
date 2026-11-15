# E429 — Les points de rencontre gérés par les contacts : lecture radiale aux rencontres, valeur à la rencontre depuis le dernier contact, résidu de cassure à absorber sur une série (pré-enregistrée 2026-11-04)

Contexte : révision demandée par l'auteur (2026-11-04). Les contacts **ne sont pas aveugles au radial** : deux contacts
consécutifs rendent la fréquence puis la position radiale (`inversion_from_consecutive_contacts`,
`radial_of_contact_value_ratio`, `radial_of_contact_tangent`, `radial_from_amplitude_step`). E428 n'avait montré la
« fréquence seule » que pour l'entier de cellules ; cette conclusion ne s'étend pas aux contacts. E429 part de ce fait
et le confronte aux **points de rencontre** (fin d'un écart premier, §19) et aux **cassures** (dépôt exact à chaque
rencontre). Directives : série d'écarts, jamais un écart isolé ; contacts, fréquence, phase, amplitude, rencontres et
cassures au cœur ; aucune hypothèse OFF posée ; aucune contradiction anticipée ; jumeau déterministe ; critères fixés
ici, jamais modifiés après ; Tours synthétiques jamais aux hauteurs d'un zéro réel quand elles sont insérées dans la
famille authentique.

Module Lean compilé AVANT exécution : `Terminal/MeetingContactReading.lean` (isolé, non ajouté à `RHV6Fresh.lean`,
25 déclarations, aucun `sorry`, aucune hypothèse). **Trois tentatives de compilation** journalisées
(`logs/lean_attempt{1,2,3}.log`) : la limite de deux est dépassée d'une unité, déclarée ici ; la troisième ne
corrige qu'une tactique superflue (`ring` après un `field_simp` qui fermait déjà le but) et des lignes trop longues.

## Objets réutilisés (jamais reconstruits)
`stagePosition`, `cellIndexAt` (FirstExceedanceRaccord, CellRestitution) ; `contactAt`, `towerPhase`,
`accumulationFrom`, `contact_accumulation_eq_endpoint_difference` (ContactValueGeometry) ; `contactRealValue`,
`radial_of_contact_value_ratio`, `radial_of_contact_tangent`, `mirror_contacts_coincide_iff` (ContactRealValue) ;
`towerRe`, `slowMeetingLog`, `fastMeetingLog`, `unit_difference` (TowerMeetings) ; `mirrorPhaseShift`,
`mirror_stagePosition_difference`, `stagePosition_sub` (ContactSeriesReading) ; `meetingDeposit_norm`,
`mirror_deposit_ratio` (AmplitudeContact) ; `background_psi1`, `sum_integrated`, `sieve_lambda`
(`E414/scripts/contact_common.py`).

## Prédictions compilées que la mesure doit retrouver (énoncés du module)
* **P1** `lastContact_le`, `lt_contact_succ` : `C_k ≤ x < C_{k+1}`, `k = ⌊stagePosition⌋` ; `log_div_lastContact` :
  `log(x/C_k) = πf/T`, `f = fract(stagePosition) ∈ [0,1)`.
* **P2** `towerRe_from_lastContact` : `Re Tour(x) = v_k·(x/C_k)^β·cos(πf)` ; `growth_factor_eq` : `(x/C_k)^β = e^{βπf/T}`.
  La position `C_k` et la valeur `v_k` lisent `β` ; la fraction `f` lit la fréquence ; la croissance lit `β`.
* **P3** `radialReadingAt_eq` : la lecture aux deux contacts encadrant une rencontre vaut `β` ;
  `radial_of_meeting_value` : hors des zéros de la trajectoire, `β` se lit sur la valeur à la rencontre et la
  valeur au dernier contact.
* **P4** `mirror_readings_sum_one` : Tour + miroir lisent `1` ; `meetingReadingsAgree_iff_line` : coïncidence ⟺ ligne ;
  `mirror_stage_shift_ne_zero` : hors ligne, les fractions de cellule Tour/miroir sont décalées d'une constante non nulle.
* **P5** `lastContact_difference_bounds` : le nombre de contacts entre deux rencontres diffère de `T·log(q/p)/π` de
  moins d'une unité, toute `β` ; `cellIndexAt_le_lastContactBefore` : pivot ≤ dernier contact.
* **P6** `meetingValueDeposit_eq_accumulation` : dépôt sur un écart = accumulation sur les propres contacts ;
  `breakResidual_erase`, `breakResidual_erase_pair` : retirer une Tour (une paire) ajoute exactement sa valeur
  (la somme des deux) au résidu que les autres doivent déposer.

## Données
Zéros `experiments/data/odlyzko_zeros6_2001052.txt` (SHA-256 vérifiée) ; premiers par crible (entiers exacts) ;
points de rencontre = premiers de rangs 2..2001 (`5 ≤ p ≤ 17 393`), séries de longueurs 12, 120, 1 200 depuis
les ancrages 5, 541, 7 919. Tours authentiques : zéros de rangs 1, 10, 100, 1 000, 10 000, 100 000, 1 000 000,
2 001 052 (β = ½). Tours de séparation (E429(a) seulement, comparaison à même fréquence) : mêmes hauteurs,
β ∈ {0,3 ; 0,7} en paire miroir. Paires insérées dans la famille authentique (E429(b), (c)) : hauteurs synthétiques
`T_s = 17,5` et `T_s' = 23,0` (entre les zéros 1–2 et 2–3, jamais une hauteur réelle), β ∈ {0,3 ; 0,7}, et paire
témoin **en ligne** (β = ½, deux Tours) aux mêmes hauteurs synthétiques.

## E429(a) — lecture radiale et valeur aux points de rencontre (`scripts/e429a_meeting_readings.py`)
Pour chaque Tour (8 rangs × β ∈ {0,5 ; 0,3 ; 0,7}) et chaque point de rencontre `p` (2 000 événements) :
dernier contact `k`, fraction `f`, encadrement `C_k ≤ p < C_{k+1}` (P1) ; valeur directe `Re Tour(p)` contre
`v_k·(p/C_k)^β·cos(πf)` et facteur de croissance (P2) ; lecture radiale aux deux contacts encadrants, lecture
tangentielle au dernier contact, lecture sur la valeur à la rencontre quand `f > 0,05` et `|cos πf| > 0,05` (P3) ;
somme Tour + miroir, écart Tour − miroir (P4 : `0` en ligne, `1 − 2β` hors ligne) ; fractions de cellule à la
rencontre : histogramme à 10 classes par Tour, décalage Tour/miroir mesuré contre `(φ_β − φ_{1−β})/π` modulo 1 ;
nombre de contacts entre rencontres consécutives contre `T·log(q/p)/π` (P5), fraction des écarts où ce nombre
diffère entre β = 0,3 et β = ½ (information radiale du comptage, mesurée sans attente) ; pivot ≤ dernier contact
et fraction d'égalité.
Critères : (i) P1, P5, pivot : **0 violation** ; (ii) P2, P3, P4 : erreur relative ≤ 10⁻⁹ (identités) ; sinon un
énoncé compilé est contredit par la mesure et l'erreur est à localiser (jamais masquée) ; (iii) histogrammes et
fraction radiale du comptage : mesures consignées, sans attente.
Jumeau : mpmath 30 chiffres, zéros de rangs 1 et 2 001 052, β ∈ {0,5 ; 0,3}, 10 premiers points de rencontre
(`k`, `f`, valeur, lecture radiale) ; accord numpy exigé (entiers identiques, réels à 10⁻¹⁰).

## E429(b) — résidu de cassure et absorption sur une série (`scripts/e429b_break_absorption.py`)
Canal lissé exact (le seul où la cassure est calculable sans limite) : `ψ₁(x) = Σ_{n≤x} Λ(n)(x − n)` (crible,
exact) ; famille authentique `F_H` = zéros de hauteur ≤ 1 000 (β = ½, conjugués comptés), contribution de la Tour
`−2Re[x^{ρ+1}/(ρ(ρ+1))]`, fond `background_psi1`. Sur les 2 000 écarts consécutifs de la série :
1. **Résidu de troncature** par écart : `ε_j = [ψ₁(p_{j+1}) − ψ₁(p_j)] − [ψ̂₁,H(p_{j+1}) − ψ̂₁,H(p_j)]` (ligne de base,
   mesure) ; identité `breakResidual_erase` vérifiée numériquement (retirer la Tour du zéro 1 : résidu + sa valeur,
   10⁻¹⁰).
2. **Lecture radiale aux rencontres sur le canal lissé** : pour chaque Tour de `F_H` et chaque rencontre, module de
   la contribution à `p_{j+1}` sur module à `p_j` contre `(p_{j+1}/p_j)^{β+1}` (conséquence de `meetingDeposit_norm`,
   β lu = `log(rapport)/log(p_{j+1}/p_j) − 1`) : erreur ≤ 10⁻⁹ attendue (identité).
3. **Insertion** d'une paire hors ligne `(0,3 ; 0,7)` à `T_s = 17,5`, d'une seconde à `T_s' = 23,0`, et de la paire
   témoin en ligne `(½, ½)` à `T_s` : dépôt de la paire par écart `d_j` (= somme des deux valeurs, identité
   `breakResidual_erase_pair`) ; part de la paire : `|d_j|` rapporté à `|cassure exacte|` et à la somme des
   `|dépôts|` de `F_H` ; fraction des écarts où `|d_j|` dépasse la cassure exacte, pour OFF et témoin.
4. **Coût d'absorption (obligations Une et Deux)** : pondérations réelles libres `a_i` sur les Tours de `F_H`,
   système `Σ_i a_i·d_{ij} = d_j` sur les `m` premiers écarts de la série, `m ∈ {12, 120, 600, 1 200, 2 000}` ;
   solution de norme minimale (SVD, `lstsq`) ; consigné : `‖a‖₂`, `max|a_i|`, résidu relatif. **Ill-posé déclaré** :
   pour `m < |F_H|` (≈ 649) une solution exacte existe toujours ; la mesure est le **coût**, pas la possibilité.
   Témoin : même calcul pour la paire en ligne. Critère pré-enregistré pour l'obligation Deux (version locale) :
   le rapport `‖a_OFF‖₂ / ‖a_témoin‖₂` **croît** de `m = 12` à `m = 600` ; s'il ne croît pas, la lecture locale
   « le pas d'amplitude hors ligne dépasse ce qu'une famille finie en ligne absorbe » n'est pas soutenue en
   troncature et est consignée comme négative.
5. **Obligation Trois** : les deux paires hors ligne (`T_s`, `T_s'`) : rapport d'annulation
   `c_j = |A_j + B_j| / (|A_j| + |B_j|)` aux 2 000 rencontres ; fraction `c_j < 0,1` ; plus longue suite de rencontres
   consécutives à `c_j < 0,1` ; coût d'absorption de A par B seule (un scalaire libre, résidu relatif).
   Prédiction compilée confrontée : les annulations unitaires de deux Tours tombent sur les réseaux lent et rapide
   (`slowMeetingLog`, `fastMeetingLog`) ; mesure : distance (en fraction de cellule de la Tour la plus haute) des
   rencontres à `c_j < 0,1` au réseau le plus proche, contre la même distance pour toutes les rencontres.
   Critère : une « paiement mutuel » n'est déclaré que si une suite d'au moins 12 rencontres consécutives a
   `c_j < 0,1` ; attendu : aucune (les réseaux lent et rapide sont des points isolés).
Jumeau : mpmath 30 chiffres sur les 10 premiers écarts : `ψ₁` exact, dépôts des paires, un résidu `ε_j` (zéros de
hauteur ≤ 100 seulement pour le jumeau) ; accord numpy à 10⁻⁸ relatif exigé sur les dépôts, consigné sur `ε_j`.

## Verdict en trois niveaux (critères fixés)
* **Identités (P1–P6, lecture radiale aux rencontres)** : réussi ⟺ 0 violation et erreurs ≤ 10⁻⁹ ; sinon erreur
  consignée et localisée.
* **Obligation Deux (coût d'absorption)** : soutenue en troncature ⟺ critère de croissance du point 4 ; sinon négatif.
* **Obligation Trois (paiement mutuel)** : négatif attendu ⟺ aucune suite de 12 rencontres annulées ; une suite
  trouvée serait consignée sans interprétation.
* **Obligation Une** (la cassure exacte force-t-elle la coïncidence des lectures ?) : **non décidable par cette
  expérience** (famille finie, troncature) ; E429 fournit seulement les ordres de grandeur du résidu à absorber et
  le coût ; ceci est dit avant exécution.
Protocole borné : `nohup`, sortie `logs/`, résultats `data/*.json`, aucune sortie fabriquée.
