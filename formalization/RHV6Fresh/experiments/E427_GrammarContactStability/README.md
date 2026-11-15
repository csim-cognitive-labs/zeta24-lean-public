# E427 — Grammaire des écarts premiers reconstruite depuis les Tours, et stabilité des contacts (pré-enregistrée 2026-11-04)

Directive de l'auteur (deux messages du 2026-11-04). Priorité absolue corrigée : **reconstruire la grammaire des écarts
premiers depuis les Tours des zéros authentiques** (états, transitions, alternance, bilan orienté borné, retour exact),
les premiers ne servant qu'à **valider** après coup ; ensuite seulement, dire si l'équilibre grammatical correspond à une
conservation géométrique aux contacts ; enfin seulement, les contraintes sur les Tours. Aucune projection spectrale posée
comme hypothèse, aucune hypothèse OFF, aucune contradiction cherchée, aucune prémisse équivalente à RH.

Module Lean de référence, compilé AVANT exécution : `Terminal/GrammarContactStability.lean` (isolé, non ajouté à
`RHV6Fresh.lean` ; aucun `sorry`, axiomes standards ; trois tentatives journalisées `logs/lean_attempt{1,2,3}.log` —
la troisième corrige une seule erreur de comptabilité tactique (`congr 1` manquant) sur la proposition
`pathOfWord_wordOfPath`, sans changement d'énoncé ; consigné tel quel).

## Objets réutilisés (jamais reconstruits)
* Grammaire de référence : `TransitionRigidity.lean` (`PrimeTransition`, `pairTransition`, `raccord_exact`,
  `eventTransition`, `event_word_valid`, `event_gap_eq`), `Grammar/Mod6Rigidity.lean` (`state6`, `GoodMod6`, `gapClass6`),
  `GrammarDwellDecomposition.lean` (`ind1`, `orientation_telescopes`, `weighted_orientation_variation_bound`).
* Reconstruction spectrale compilée : `RawEventReconstruction.lean` (`reconstructedVonMangoldt`, `reconstructedPrimeEvent`,
  `reconstructedPsi_eq_limit_contact_accumulation`), `PrimeGapReconstruction.lean` (`reconstructedPrimeAtRank`,
  `reconstructedPrimeGap_eq_actualGap`, `contact_accumulation_reconstructs_prime_gaps`).
* Contacts authentiques : `ContactRealValue.lean` (`contactRealValue`), `FirstExceedanceRaccord.lean` (`cellIndexAt`),
  `MeetingPoint.lean` (`meetingPoint` = fin d'un écart premier, `relativeAmplitude`), `GrammarDrift.lean`
  (`meeting_drift`, `meeting_drift_eq_one_iff`), E420–E426.

## Prédictions compilées que l'expérience doit retrouver
* `orientedBalance_telescopes`, `orientedBalance_abs_le_one` : bilan orienté = indicatrice de l'état initial − indicatrice
  de l'état final ; confinement dans {−1, 0, +1}.
* `crossings_cancel_15_51`, `crossings_cancel_51_15`, `orientedBalance_dwell` : retour exact après deux croisements
  inverses, quel que soit le nombre de séjours intermédiaires ; neutralité des maintiens.
* `confinement_not_dwell_equality` : le confinement n'implique pas l'égalité des nombres de séjours.
* `card_validWords_twelve` : 8 192 mots valides de douze transitions.
* `eventOrientation_of_gap` : orientation ⟺ écart ≡ 4, 2, 0 (mod 6).
* `reconstructedState_goodMod6`, `reconstructedTransition_cls`, `reconstructedWord_valid`,
  `reconstructedBalance_abs_le_one`, `reconstructedTransition_eq_actual` : la suite reconstruite (prédicat spectral) porte
  les deux états, les quatre transitions, le raccord, le confinement ; validation rang par rang.
* `weightedBalance_abs_le`, `contact_weighted_balance_abs_le` : bilan pondéré par des valeurs réelles aux contacts borné
  par la variation totale des poids, pour toute hauteur et toute position radiale.
* `logRatio_not_determined_by_transition`, `amplitude_ratio_not_determined_by_transition` : même transition, rapports
  distincts (29 → 31 contre 113 → 127).
* `return_drift_eq_one_iff` : sur un segment de bilan nul, la dérive d'amplitude relative est neutre ⟺ β = ½.

## Données (provenance et empreintes)
* Zéros : `experiments/data/odlyzko_zeros6_2001052.txt` (2 001 052 hauteurs, SHA-256 vérifiée au chargement par
  `contact_common.load_zeros`, fichier `.sha256` à côté).
* Premiers : crible d'Ératosthène calculé dans le script (entiers exacts), aucune liste externe ; jumeau : second crible
  indépendant en entiers Python purs jusqu'à 10⁶.
* Poids spectraux d'E415 (`experiments/E415_RawEventReconstruction/data/lam{A,B}_W*.npy`) pour l'échelle de troncature ;
  les valeurs à troncature complète sont **recalculées** ici depuis les zéros (empreinte des fichiers npy consignée).

## E427(a) — grammaire de référence exacte (`scripts/e427a_grammar_reference.py`, entiers)
Premiers 5 ≤ p ≤ 10⁸ (5 761 453 premiers > 3). Mesures, toutes des **identités** attendues exactes :
1. conformité : chaque transition (état de p, état de p') a la classe (p' − p) mod 6 prescrite (0 maintien, 4 pour 1 → 5,
   2 pour 5 → 1) ; nombre de violations attendu 0 ;
2. bilan orienté cumulé ∈ {−1, 0, +1} en tout rang (0 violation attendue) ; histogramme des trois valeurs (mesure) ;
3. retour : pour chaque croisement `t15` (resp. `t51`), le bilan au croisement inverse suivant vaut 0 (0 violation
   attendue) ; distribution des longueurs de séjour entre deux croisements inverses (mesure, pas de loi) ;
4. égalité des séjours : N11 − N55 à chaque rang (mesure : non borné attendu, biais de Chebyshev ; aucune loi) ;
5. dénombrement : 8 192 mots valides de douze transitions par énumération brute des 4¹² = 16 777 216 mots (identité) ;
   nombre de mots de douze transitions **réalisés** par les premiers ≤ 10⁸ (mesure, aucune propriété attribuée).
Jumeau : second crible indépendant jusqu'à 10⁶, mêmes comptes (égalité exacte exigée).

## E427(b) — niveau 1, grammaire reconstruite depuis les Tours (`scripts/e427b_level1_reconstruction.py`)
Fenêtres W1 = [3, 300], W2 = [10 000, 10 060], W3 = [100 000, 100 030] ; troncatures H ∈ {1 000, 5 000, 100 000, 10⁶,
2 001 052}. Chaîne, sans aucune donnée arithmétique :
1. Tours des zéros (β = ½, hauteurs du fichier) → somme collective des valeurs signées (canal brut A : ψ̂₀ aux demi-entiers ;
   canal intégré B) → Λ̂(n) ; **route par contacts authentiques** (H = 1 000, W1, canal brut) : accumulation de chaque Tour
   sur ses propres contacts dans [n − ½, n + ½] (`accumulate_one`), comparée à la différence des valeurs aux bords
   (identité compilée `contact_accumulation_eq_endpoint_difference`, écart attendu ≤ 10⁻¹⁰ relatif) ;
2. règle pré-enregistrée d'E416 (valeur admissible la plus proche de {0, log n, log n / k}) → événements premiers
   reconstruits ;
3. **états reconstruits** = résidu modulo 6 de chaque premier reconstruit (lecture sur la suite reconstruite seulement) ;
   **transitions reconstruites** (états consécutifs, classe = écart reconstruit mod 6) ; validité du raccord ; alternance
   des croisements ; bilan orienté cumulé ; retour après croisements inverses — tout calculé sur la suite reconstruite ;
4. **validation (après)** : comparaison état par état, transition par transition, bilan par bilan avec la grammaire des
   vrais premiers de la fenêtre (crible). Critère de réussite du niveau 1 : à la troncature complète, 0 désaccord sur W1,
   W2, W3 (états, transitions, bilan) ; échelle de troncature consignée (désaccords attendus aux petites troncatures, E416).
5. **Contrôles de séparation** (synthétiques, jamais aux hauteurs des zéros réels) : (i) mêmes hauteurs, β = 0,3 pour toutes
   les Tours (famille déplacée) ; (ii) hauteurs pseudo-aléatoires de même densité (Riemann–von Mangoldt, graine 20261104,
   vérification qu'aucune hauteur ne coïncide avec un zéro réel à 10⁻⁹ près), β = ½. Même chaîne 1–4. Lecture : si la
   grammaire n'est retrouvée qu'avec les zéros authentiques, l'information arithmétique est dans le collectif des zéros ;
   les contacts n'en sont que le découpage.
Jumeau déterministe : Λ̂(n) à 30 chiffres (mpmath) pour n ∈ {3, 5, 7, 97, 101} et H = 1 000, écart ≤ 10⁻⁹.

## E427(c) — niveau 2, transport de l'équilibre aux contacts (`scripts/e427c_level2_contacts.py`)
Événements premiers de rangs 2 à 2 001 (5 ≤ p ≤ 17 393) ; Tours authentiques des zéros de rangs 1, 10, 100, 1 000, 10 000,
100 000, 1 000 000, 2 001 052 (β = ½) ; Tours de séparation : mêmes hauteurs, β ∈ {0,3 ; 0,7} (synthétiques).
Pour chaque Tour et chaque événement r : contact qui ouvre la cellule du point de rencontre p_{r+1} (`cellIndexAt`), sa
valeur réelle signée (`contactRealValue`), l'amplitude relative aux points de rencontre.
1. bilan pondéré Σ orientation(r)·v_r sur fenêtres glissantes de 12 et 120 événements, contre la borne d'Abel compilée
   (0 violation attendue : identité) ; rapport bilan/borne (mesure) ;
2. candidats de transport : (α) décalage d'indice de contact entre points de rencontre successifs, (β') variation de
   log-amplitude β·log(p_{r+2}/p_{r+1}) ; distributions conditionnelles à l'orientation (+1, −1, 0) ; information mutuelle
   orientation ↔ candidat, comparée à l'information mutuelle orientation ↔ écart (l'orientation est une fonction de
   l'écart mod 6 : `eventOrientation_of_gap`) ; critère pré-enregistré d'un transport : une fonction f telle que
   candidat = f(orientation) à 10⁻⁹ près pour tous les événements ; attendu (compilé) : aucun candidat ne le satisfait ;
3. correction des dérives : segments de bilan nul (croisement puis croisement inverse) contre segments de bilan non nul ;
   dérive d'amplitude relative sur chaque segment ; à β = ½ attendue exactement 1 sur TOUS les segments (identité
   `meeting_drift_eq_one_iff`), à β ≠ ½ jamais 1 ; le retour du bilan ne modifie pas la dérive (compilé
   `return_drift_eq_one_iff`) ;
4. séparation : mêmes mesures pour les Tours synthétiques ; identité des conclusions attendue.
Jumeau : valeurs aux contacts à 30 chiffres (mpmath) pour la Tour du zéro 1 et dix événements, écart ≤ 10⁻¹².

## Critères de réfutation et de réussite (fixés avant exécution)
* Niveau 1 réussi ⟺ 0 désaccord à troncature complète sur W1–W3 et contrôles de séparation en échec (grammaire non
  retrouvée depuis les familles synthétiques). Sinon : échec consigné.
* Niveau 2 : une loi de conservation géométrique n'est déclarée que si un candidat satisfait le critère de transport ;
  attendu (compilé) : aucun ; la borne d'Abel est une identité, pas une loi.
* Niveau 3 : aucune contrainte sur β n'est cherchée ni lue dans cette expérience.
Aucun critère ne sera modifié après exécution. Résultats, y compris négatifs, dans `RESULTS.md`.
