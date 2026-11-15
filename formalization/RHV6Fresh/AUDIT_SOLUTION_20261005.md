## 136. Stabilité du régime ON engagé : théorèmes causaux nouveaux, grammaire pondérée, campagne de fermeture (direction Fable, exécution Sonnet, 2026-10-25)

Mission de l'auteur (trois messages) : consolider la stabilité du régime ON engagé, trouver les théorèmes causaux qui font qu'un OFF
ne peut pas la troubler, auditer les derniers TDD, réduire prémisses et erreur de compilation, « de nombreuses tentatives » ;
puis : une seule expérience de transmission grammaticale entre deux zéros (canaux pondérés `G_ab(z_j; X)`, `O_j = G15 − G51`,
`B_j = G11 − G55`, trois configurations ON / déplacement OFF / insertion OFF) ; puis : le porteur OFF est l'asymétrie de
croissance `x^{1/2±δ}` (facteur `2x^{1/2}cosh(δ log x)`), pas `ΔT > 0` ; la progression des hauteurs sort du noyau causal.

Audit d'entrée. Build de référence réexécuté : 1 min 28, une erreur, `:854`, but `False`. Les cinq TDD du 24 octobre (G4,
potentiel, séparation analytique, masse des diviseurs, poids premiers) compilent seuls, hors build, axiomes standard ; aucun ne
touche la position radiale ; T1/T2/Y1/X1/Z1/Z3 étaient des preuves papier. Fait inconditionnel inexploité : `ZetaZeroFree`
(rhv3_lean, port PNT+) jamais importé par un module de position radiale. Le fichier des 2 001 052 zéros n'est ni dans le dépôt ni
sur la machine. Avance rapide de `main` (10 commits : scripts E2M, rétractation du chemin par étiquette de classe, plan Astra/LNA).

Lean, cinq modules nouveaux dans le build unique (51 théorèmes, axiomes standard, aucun `sorryAx`) :
1. `Terminal/ZeroFreeRegionBand.lean` : `zeroFree_radial_upper`, `zeroFree_radial_lower` (par le miroir), `zeroFree_band`
   (`T > 3 ⟹ A/log⁹T < β < 1 − A/log⁹T`, un seul `A ∈ ]0, 1/2]`), `low_member_band_of_height`, `low_member_margin_pos`,
   `tendsto_zeroFree_margin`. Classement : théorème indépendant, inconditionnel ; vrai aussi dans `ζ(s−δ)ζ(s+δ)` ; ne ferme pas.
2. `Terminal/OnRegimeStabilityPackage.lean` : `engaged_on_regime_stability` ; `fiber_top_member_high` ; `fiber_exit_from_high` ;
   `off_disturbance_profile` ; `cascade_resumes_after_fiber` ; `low_member_above_28` (depuis les certificats 15/22/28 et
   `upperCount_of_zeta_boxes`, sans la chaîne). Classement : profil DÉMONTRÉ de toute perturbation OFF ; aucune ligne n'est une
   contradiction ; le seul mode de reprise de la cascade est un départ vertical depuis un membre `β > 1/2` (caractérisation).
3. `Terminal/GrammarDwellDecomposition.lean` : `orientation_telescopes`, `orientation_abs_le_one`, `occ1_eq`, `occ5_eq`,
   `dwell_decomposition`, `dwell_balance_eq_occupancy_minus_orientation`, `dwell_balance_iff_occupancy`, puis les formes pondérées
   `weighted_occ1_eq`, `weighted_occ5_eq`, `weighted_dwell_balance`, `weighted_character_channel`,
   `weighted_orientation_eq_abel`, `weighted_orientation_abs_le`. RÉSULTAT CENTRAL pour la mission : le canal des séjours n'est
   pas une troisième quantité, `B_j = (W1 − W5)_j − O_j` pour tout système de poids ; `W1 − W5 = Σ χ₃(p_n) w_n(z_j)` est le canal du
   caractère modulo 3 (celui de `L(s, χ₃)`, déjà repéré en E350) et `O_j` est une somme d'Abel bornée par la variation des poids.
   L'Archétype B brut (`−82`) est l'équirépartition mod 6 à une unité près ; sa borne uniforme n'est PAS démontrée et serait
   fausse en général (biais de Chebyshev).
4. `Terminal/GrammarWeightedG4.lean` : `weighted_orientation_identity`, `weighted_orientation_variation_bound` (recopiés du TDD),
   `unimodal_variation_eq`, `weighted_orientation_unimodal_bound`, `massWeight_nonneg`, `massWeight_le`, `massWeight_concaveOn`,
   `log_mul_sub_unimodal_on_increasing`, `weighted_orientation_log_mul_sub_bound` (`≤ X log X`). Raccord G4 fermé ; instanciation
   sur `transitionSum` non faite.
5. `Terminal/FiniteRadialRigidity.lean` : `trig_poly_mean_square`, `mean_square_tendsto_zero_of_tendsto_zero`,
   `trig_poly_not_tendsto_zero`, `finite_exponential_sum_bounded_imp_nonpos` (Z1). Outil conditionnel.

Chaîne : `:856` (deux imports), composées `hT3`, `hBand`, `hProfile` (contraintes seules) ; `scripts/goal_dependencies.py`
retiré sur `authentic_engaged_cascade_forbids_insertion` (26 faits en contexte, 0 consommé, le but est `False`).

Numérique. E371 (anatomie, 4 s) : identité vérifiée à chaque préfixe ; `D` suit `O` (−33, −189 ; max |D| 362 à 10⁷), un seul
signe après le début ; chiffre de référence « 88 055, N15 − N51 = +1 » impossible pour un préfixe de premiers > 3 (il commence
par 5). E373 (canaux pondérés, 300 zéros, X ≤ 10⁶, poids = saut du terme brut `−2Re(x^ρ/ρ)` sur l'écart, `zeroTerm`) : identités
pondérées à 2e−14 ; borne d'Abel : max 0,056 ; paire déplacée − double ON : rapport par famille = `cosh(d log x) − 1` à 4–8 %,
IDENTIQUE dans les quatre familles à 1 % (l'asymétrie de croissance suit la masse ON de chaque famille : aucune famille
grammaticale ne la porte) ; ordre `δ²` (pente 2,006, `radialCurvature_ge_sq`) ; les trois canaux lisent `Δβ` de façon bruitée,
la pente par événement vaut `≈ d` ; collectif : 300 zéros ne reconstruisent pas le canal brut (queue dominante) ; absorption à
poids libres (contrôle, zéros fabriqués) : résidu relatif 0,89–0,985 même dans la fenêtre d'ajustement, > 1 en transport ;
contacts : fraction de transitions changées = densité des premiers (0,0046 / 0,0087 / 0,0196 pour d = 0,05 / 0,1 / 0,25).

Verdict. Les deux stabilités grammaticales transportées dans des poids se réduisent EXACTEMENT à (canal de caractère mod 3)
et (somme d'Abel bornée) : ni l'une ni l'autre ne lit la position radiale autrement qu'à travers les poids `x^{β}` eux-mêmes,
et l'asymétrie `cosh` d'une paire OFF se répartit sur les familles proportionnellement à leur masse. La flèche « double
stabilité + contacts + reconstruction ⟹ pas de séparation miroir » n'a donc aucun porteur grammatical ; le porteur analytique
(asymétrie de croissance) est le même objet que la borne du reste des premiers d'exposant `< 1 − β_l` (`radial_le_of_remainder_growth`),
acquise à l'exposant 1 seulement. Sondes de fermeture E372 : voir l'analyse du statut. RH non démontrée.

## 135. E352, projection des reconstructions d'E345 à E350 sur les zéros connus (règle de l'auteur, 2026-10-21)

Règle : à cause de l'arrêt à 5000 écarts, de la précision de calcul et du fait qu'une somme infinie n'est pas calculable en
soi, chaque résultat de reconstruction (T̂, β̂) est projeté sur le zéro connu le plus proche et arrondi à (T_n, 1/2) ; les
graphiques sont refaits. `experiments/E352_ProjectionOnKnownZeros/` (script 27 s, `projection_table.csv`, `e352_results.json`,
`E352_REPORT.md`, cinq figures ; aucun Lean modifié). 226 reconstructions zêta (E345 24, E349 36, E350 166) : 118 gardées, 108
doublons d'horizon fini (règle : premier extrait gardé ; « le plus proche en T » rejeté car il gardait pour E349 le parasite
25,006 à la place du mode dominant 25,04) ; |ΔT| médian 0,0057 = 0,009 résolution π/L ; |Δβ| médian 0,0136. Reconstructions
refaites (canal lissé, 5000 écarts, grille dense) : RMS brute / projetée / connus 1..K / projetée + queue : E349 (K = 6)
2,34e−3 / 2,18e−3 / 2,18e−3 / 6,89e−4 ; E350 variantes 5000 (K = 5) 4,57e−2 / 2,38e−3 / 2,38e−3 / 6,89e−4 ; E350 horizons 128
(K = 2) 5,38e−3 / 3,91e−3 ; E345 K = 5 2,67e−3 / 2,38e−3 ; troncature connue N = 1 … 5000 : 5,05e−3 → 6,89e−4 (plancher ≥ 300).
Demande par écart suivie à 50 % : K = 5 : 0,36, N = 5000 : 0,97 ; familles projetées = zéros connus de même rang. Témoin : brute
6,52e−3, projetée sur (T_n, 1/2) 1,49e−2 (dégradée), sur (T_n, 1/2 ± δ) 6,15e−3 (améliorée). β̂ à T_n, autres zéros connus
retirés : 0,485–0,501 (rangs 1–12). E346 : cellules admissibles projetées sur les rangs 1, 2–7. Conclusions : les fréquences
retrouvées sont celles de zêta ; la famille projetée reconstruit au moins aussi bien que la brute et exactement comme la somme
tronquée des zéros connus ; son résidu est la queue ; les écarts β̂ − 1/2 bruts étaient des erreurs de méthode ; la règle
introduit β_n = 1/2 comme donnée (contrôle témoin), donc β n'est plus une mesure après projection ; portée Lean nulle
(rangs 1–3 théorèmes, 4–5000 certificat externe ; `:854` inchangée).

## 134. E351, changement de forme de la fermeture : la stabilité réclamée par les écarts premiers, cinq formes positives, buts résiduels (2026-10-21)

Demande de l'auteur : la fermeture ne doit plus être « un OFF est incompatible » mais « les écarts premiers réclament la
stabilité de la ligne critique et rien d'autre ». `experiments/E351_GapDemandStability/E351_PLAN.md` ; module
`Terminal/GapDemandStability.lean` (35 théorèmes, 6 objets, axiomes standard, importé) ; chaîne non modifiée. Compilé : identité
de propagation de la dérive `windowDrift z a m = (β − 1/2)·gapBudget a m`, `gapBudget = log(p_{a+m}/p_a) > 0`, dérive nulle ⟺ ON,
dépendance au seul budget (pas au nombre d'écarts), dérives miroirs opposées, `mirror_word_energy_debt` = télescopage pour toute
suite positive ; cohérence de phase pour toute `β` (`coherent_peak_any_radial`) contre lecture de l'exposant par translation
(`translated_ratio_one_iff`), égalité des deux lectures (`projection_ratio_eq_window_drift`) ; découpage exact des canaux commun /
différentiel par classes (`common_channel_split`, `differential_channel_recovers_classes`), le différentiel portant `L(χ₃)` (E350) ;
`gapDemand I` = incrément du reste = somme des contributions (C126). Cinq formes positives : `WindowStable`, `DemandTransported`,
`ImposedScaleStable`, dérive non descendante, collective ; fermetures `regime_stable_of_window`, `regime_stable_of_transport`,
`regime_stable_of_imposed_scale`, `arrival_onLine_iff_drift_nonneg` (sous `arrival_drift_nonpos`, côté haut exclu) ; lois ⟺ RH sous
l'ancre (`window_stability_law_iff_riemannHypothesis`, `transport_law_iff_riemannHypothesis`,
`imposed_scale_law_iff_riemannHypothesis`), `stability_forms_agree`. Sonde hors build (`lean/ProbeE351_GapDemand.lean`) : cinq
buts résiduels, tous `β_l = 1/2` écrit sur la dérive ou l'échelle (`0 ≤ (β_l − 1/2)·gapBudget r 1` pour la forme la plus faible) ;
contrôle TDD fermé. Proposition : remplacer `authentic_engaged_cascade_forbids_insertion : ¬ HorizontalMirrorRealization p` par
un théorème ouvert positif (H4 recommandée), aval inchangé ; changement de forme, non réduction ; ce qui manque = identité lue sur
les écarts exacts imposant `β_l − 1/2 = 0`, qu'aucune identité compilée ne contient (toutes vraies pour toute `β`). Règles :
ne pas présenter un pic spectral comme une preuve de stabilité ; mesurer toute fenêtre par son budget logarithmique ; ne pas
présenter le canal différentiel comme une contrainte sur zêta sans formule explicite de `L(χ₃)`. Build réexécuté : EXIT=1, une
erreur (`:854`), 0 sorry, 0 admit.

## 133. E350, extraction spectrale et recherche de la loi arithmétique de stabilité : huit fréquences depuis les seuls premiers, aucune fenêtre grammaticale n'ajoute de contrainte (2026-10-20)

Mission en cinq axes (`experiments/E350_GrammarSpectralStability/`, module `Terminal/SpectralWindowProjection.lean`, 21 théorèmes, axiomes standard, importé). Axe A : estimateur par projections P_T(U, L) = ∫ g e^{−iTu} du du signal normalisé g = R(e^u)e^{−u/2} sur grille dense, fenêtre de Hann, x ≥ 50 ; β̂ par l'identité de translation P(U+H) = e^{(β−1/2)H}P(U) (compilée). Huit fréquences retrouvées dès 2000 écarts (à 20000 : 14,1346 ; 21,0216 ; 25,0106 ; 30,426 ; 32,938 ; 37,586 ; 40,913 ; 43,330), β̂ 0,4996 ; 0,5011 ; 0,4993 ; 0,5155 ; 0,4951 ; 0,4994 ; 0,5110 ; 0,4934 ; E349 dégénérait après cinq modes par trois biais de méthode (quadrature aux seuls événements premiers = repliement ; fenêtre rectangulaire = fuite ; borne basse x = 2). Décomposition a posteriori : l'erreur de β̂ vient à > 95 % des autres fréquences (fuite en 1/L) ; témoin lu à 0,57. Modèle d'erreur compilé (`radial_estimator_perturbation_bound`) sous une erreur relative ε explicite ; certification impossible : seule borne du complément démontrée = exposant 1 (`normalizedSignal_projection_le_exponent_one`). Axe B : retour d'état ⟺ Σ écarts ≡ 0 (6) ⟺ #AB = #BA (compilé, `window_return_iff_gap_sum_mod6`, `complete_window_criteria_agree`) ; à longueur appariée en u, aucune famille grammaticale n'améliore la lecture radiale (0,0009 / 0,0011 ; permutations p = 0,28–0,40) ; seules les fenêtres spectrales gagnent (période de battement : `beat_window_interference_vanishes`, identité analytique) ; un nombre d'écarts n'est pas une longueur spectrale ; D(W) expliqué à 63 % par cinq modes, 0,3 % par la grammaire ; aucune grandeur candidate conservée ; perturbation radiale lue comme sa valeur sur toutes les fenêtres ; paire miroir lue comme un exposant intermédiaire. Explication 1 (analytique) établie, 2 (grammaticale) réfutée à longueur appariée, 3 (loi collective indépendante) ni établie ni réfutée. Axe C : marge ~ longueur et interférence, pas grammaire (R² 0,06). Axe D : D1–D6 compilés ; D7 = `stableProjection_iff_onLine`, caractérisation du but, pas un transport. Axe E : huit réponses chiffrées ; loi en 1/K = fuite spectrale (identique dans le témoin) ; 1000–2000 écarts bien quadrés battent 5000 écarts d'E349. But `:854` inchangé, signature 2e5a657b8010, BUILD=FAIL, 0 sorry, 0 admit. RH_FOUND=FALSE.

## 132. E349, inversion exacte à deux rencontres depuis 5000 écarts premiers : la marge sur un demi-tour n'est pas infime (2026-10-20)

Plan de l'auteur (identification de β → détermination exacte → preuve universelle de l'alignement), déployé sur 5000 écarts premiers
consécutifs (précision de l'auteur : écarts, pas zéros). `experiments/E349_TwoMeetingInversion5000Gaps/` (producteur premiers seuls,
canal lissé compilé, modèle sans amplitude libre, règles E343 ; validateur a posteriori ; trois passages ; aucun Lean modifié).
Identification : cinq fréquences retrouvées (14,134 ; 21,021 ; 25,039 ; 30,423 ; 32,932), `β̂` sur l'horizon 0,501 ; 0,505 ; 0,520 ;
0,505 ; 0,498 (marge 0,001–0,02, décroissante avec l'horizon pour le premier mode : 0,037 à 128 écarts → 0,001 à 5000) ; au-delà de
cinq modes, extraction dégénérée (parasites autour de 25 à `β̂` 0,27–0,42, réduction du coût 3,5–4 % chacun, indiscernable du cinquième
vrai mode 4,8 %). Marge sur UN demi-tour (inversion exacte à deux rencontres consécutives) : médiane 0,74 ; 4,7 ; 4,4 ; 7,0 ; 10,8 ;
cause : la différence de l'avenir (non extrait + queue) sur un demi-tour vaut 25–110 % du signal propre contre 5–12 % de variation
d'enveloppe propre, amplifiée par `T/π` ; sur le premier mode, les `β̂_k` de zêta et du témoin (0,62) sont presque superposés : la
fluctuation locale est portée par les autres fréquences, communes aux deux mondes, sans information radiale. Lignes de base de `K`
demi-tours : marge en `1/K` (premier mode 0,74 → 0,05 à K = 20 ; deuxième 4,7 → 0,07 à K = 40) : `β` n'est lu que par une comparaison
d'enveloppe sur l'horizon entier = borne du complément sur l'horizon, pas une propriété locale. Témoin : membres hauts à 0,619, bas
étalés. Verdict : étapes 1–3 du plan exécutées ; étape 4 NÉGATIVE (aucune marge locale) ; étape 5 non atteignable par une propriété
d'un demi-tour ; l'alignement universel ne peut être porté que par la borne de l'avenir sur l'horizon entier (exposant 1 démontré,
exposant 1/2 ⟺ but) ; identification exacte et universelle par l'unicité, jamais exclusion. BUILD=FAIL inchangé (`:854`). RH_FOUND=FALSE.

## 131. Correction du verdict d'E346 : résultat négatif sur des tests déterminés, pas sur la nécessité de l'annulation du miroir (2026-10-20)

Audit externe collé par l'auteur (« corriges cela »). Erreur : la conclusion générale d'E346 (§128, « aucune contrainte examinée ne
réduit l'ensemble des continuations `(β, T)` », « résultat négatif publié avec contre-exemples ») et sa reprise dans CLAUDE.md,
la mémoire et la reconstruction (§129, « suspendue ») affirmaient plus que les tests. « E346 n'a pas identifié de critère discriminant
parmi ceux testés » n'implique pas « les continuations OFF satisfont toutes les contraintes arithmétiques et géométriques » ; la seconde
demanderait une démonstration de compatibilité globale jamais fournie (formule explicite du canal de comptage non compilée, aucune
borne indépendante du complément). Réfuté réellement : loi LINÉAIRE entre voisins (R² = 0,003–0,020 = contrôles), discrimination par
les 220 marges de contacts, sélection par ajustement fini sur une grille (seuil de coût 5 %, horizon 727, trois contraintes
géométriques partielles, complément non borné : une cellule admissible de la grille n'est pas une continuation admissible de zêta).
Non établi : admissibilité des continuations OFF authentiques ; impossibilité d'une loi collective reliant annulation du miroir et
stabilité de la reconstruction ; une contrainte conjointe `𝒞(apports exacts, contacts, succession canonique, fond) ≥ 0` n'a pas été
testée (observables étudiées séparément). Les neuf paires miroirs de §F sont des zéros fabriqués (archivés §130) : aucun énoncé sur
zêta, ni « gel admis » ni « gel exclu ». Sous-exploité : la position radiale est fortement visible dans les apports exacts (623/640
fenêtres, enveloppe de comptage `x^{δβ}`), faiblement dans les contacts ; manque une valeur imposée indépendante. Lean : `hImposedBreak`,
`hImposedNext`, `hGapSync` sont des identités, leur présence ne contredit pas `hFrozen` ; `imposed_contribution_eq` n'est pas une
détermination indépendante depuis les seuls premiers ; le théorème de raccordement qui en tirerait une contrainte supplémentaire
n'a été ni formulé ni prouvé. Corrections appliquées : `CORRECTION_VERDICT_20261020.md`, §6/§7/§9 et bilan du rapport, README,
producteur relancé (statuts : 9 MESURE, 1 CONTRE-EXEMPLE à la loi linéaire seulement, 1 ZÉROS FABRIQUÉS ; `results.json`,
`candidate_laws.csv`, `run_log.txt` régénérés, valeurs numériques inchangées), `CONCLUSIONS_REVISED.md` (section de correction),
CLAUDE.md, mémoire. Aucun Lean modifié ; build réexécuté, `:854` inchangé. RH_FOUND=FALSE.

## 130. Plan fusionné exécuté : assainissement, cible vérifiée, candidats d'inégalité (E348, 2026-10-20)

Contexte : challenge de la reconstruction E345/E346 (§129) puis critique externe collée par l'auteur (ChatGPT) ; plan fusionné en
sept étapes, exécuté. Aucun Lean modifié ; but `:854` inchangé ; aucune prémisse ajoutée.

1. Assainissement. Les contrôles à zéros fabriqués de la reconstruction (remplacement §9 d'E345 recalculée ; neuf paires miroirs
   §F d'E346 recalculée, `off_pairs.csv`) sont archivés dans `experiments/E345_E346_STABLE_TOWERS_REBUILD/archives_controles_fabriques/`
   et retirés des résultats validés (`CONCLUSIONS_REVISED.md`, `README.md` mis à jour).
2. Cible en une phrase, vérifiée contre le compilé (`experiments/E348_InequalityCandidates/CIBLE_VERIFIEE.md`) : à la première
   rupture, le pas sortant figé relie deux membres authentiques de même fréquence ; la reconstruction impose chaque contribution ;
   il manque une inégalité lue sur les seuls premiers interdisant deux signaux authentiques de même fréquence. Cette forme,
   quantifiée, est déjà classée ⟺ RH (`oneSignalPerFrequency_iff_riemannHypothesis`, `frequencyTaken_law_iff_riemannHypothesis`,
   `no_sameHeight_iff_riemannHypothesis`, `counting_increment_eq_iff_noOffInInterval`, `horizontalExclusion_iff_riemannHypothesis`) ;
   le pas de comptage < 2 est plus fort que RH (`count_step_iff_on_unique_simple`). Objection de la critique (« l'accroissement
   unitaire réintroduit RH ») fondée et déjà consignée (2026-10-12) ; mon étape trois initiale est retirée. La grammaire compte des
   MEMBRES, aveugle à la hauteur (`rank_step_counts_members_not_heights`) : une paire miroir = deux événements à une hauteur, aucune
   règle grammaticale violée ; l'accroissement unitaire ne peut venir que de l'analyse (principe de l'argument, certifié à 15, 22, 28).
3. Cahier des charges de l'inégalité : (i) poids exacts des premiers ; (ii) sans soustraction des zéros ; (iii) fausse dans le monde
   témoin ; (iv) ni borne du reste à exposant fixé ni comptage ; (v) non ⟺ RH quantifiée.
4–5. Candidats = les trois seules quantités mesurées séparant zêta du témoin (`e348_inequality_candidates.py`, 2 s, E311/E324 cités,
   (b) recalculé à 10^8) : (a) exposant d'amplitude par mode extrait des seuls premiers (zêta 0,500 ± 3σ, témoin ≥ 0,574, séparation
   +0,051) : ⟺ RH (`individualAmplitudeRigidity_all_iff`) ; (c) pente d'amplitude de la contribution imposée (zêta ≤ 0,0033, témoin
   ≥ 0,077) : besoin constant ⟺ ligne (`need_constant_iff_not_shifted`), loi ⟺ RH (`meeting_need_law_iff_riemannHypothesis`) ;
   (b) résidu d'écart pondéré `Σ (g_n − Λ(p_n)) p_n^{−α}` : zêta suit l'exposant `1/2 − α` (écart max 0,026 pour α < 0,9), compilé
   `zero_free_of_weighted_residual` (borné à α ⟹ tout zéro ≤ α) ; pour contredire le gel il faut α < 1 − β_l pour toute rupture :
   bande sans zéro de largeur positive dans la bande critique, hors de tout résultat inconditionnel ; le critère (iii) n'est pas
   bien posé pour un résidu d'écart (le témoin n'a pas de grammaire d'écarts propre : son exposant ≈ +0,6 est la dérive du poids
   moyen, pas une oscillation) ; seule la conclusion du théorème compilé est fausse dans le témoin.
6. Aucun candidat ne survit : rien n'est raccordé à la chaîne ; le contexte du but n'est pas allongé.
7. Verdict : le théorème manquant est, sous toutes les formes rencontrées, soit le but lui-même (⟺ RH), soit un demi-plan sans zéro
   non démontré. L'erreur de compilation ne peut être corrigée que par une démonstration ou par une hypothèse nommée et affichée ;
   l'auteur ayant retiré la précédente prémisse, aucune n'est posée sans son instruction.
Corrections à la critique externe : la Tour normalisée encode β par sa phase constante (compilé) mais identifier n'est pas
contraindre (`parameter_grid_admissible`) ; la dérivée de la paire miroir est le facteur hyperbolique déjà compilé
(`exact_mirror_cross_lt_double`, `low_pair_envelope_ge`) et conduit à chaque fois à une bande sans zéro contenant le miroir.
Collision de numéro : une session parallèle a publié `experiments/E347_OFF_NewHeight_E345_E346/` (paire miroir SYNTHÉTIQUE à la hauteur 35,5
ajoutée à la reconstruction tronquée ; « résidu requis » = identité de soustraction, aucune borne indépendante) : contrôle à zéros
fabriqués, classe archive de l'étape 1, hors résultats validés, non supprimé (décision de l'auteur) ; mon dossier est renuméroté E348.
Build : `lake build RHV6Fresh` réexécuté, EXIT=1, une erreur `:854`, 0 sorry, 0 admit, signature inchangée.

## 129. Reconstruction intégrale d'E345 et E346 sur Tours stables (2026-10-20)

Mission de l'auteur (« Trois Tours ON — amplitudes fixes, fréquences différentes et fins d'écarts premiers » : confusion
entre Tour intrinsèque, représentation normalisée, contribution exacte et effets de coordonnées) puis décision du même jour :
E345 et E346 reclassées EXPLORATOIRES NON CONCLUANTES ; données et identités conservées ; conclusions négatives suspendues ;
protocole corrigé = relations dans le système des Tours stables, puis transport démontré vers les contributions exactes.
Dossier `experiments/E345_E346_STABLE_TOWERS_REBUILD/` (archives E345/E346 inchangées).
Modèle (`MODEL_CONTRACT.md`) : `H(u) = (2/|ρ|) cos(Tu + π − arg ρ)`, `Q(u) = e^{i(Tu − arg ρ)}`, `S(x) = −2 Re Ei(ρ log x)` ;
conversions démontrées `x^ρ/ρ = (e^{βu}/|ρ|)·Q`, `−2Re(x^ρ/ρ)/√x = e^{(β−1/2)u}H`, `dS/du = −2e^{βu}cos(Tu)/u` (phase nulle
≠ phase `−arg ρ` du mode), contacts = points où `Q` est réel. Contrôles §7 passés sur les cinq zéros (|Q| − 1 ≤ 2e−16,
d arg Q/du − T ≤ 2e−10, Δlog C_k − π/T ≤ 2e−15). Audit graphique : le graphique fourni n'existe sous ce titre dans aucun
producteur ; reproduit (fig0) : la dilatation en `x` est le changement de coordonnée (période apparente `2πx/T`, multipliée par
133/217/251 entre 2 et 727 = rapport des abscisses ; période en `u` constante) ; E345 fig2 mélangeait contacts de `Q` et extrema
de `S` ; E346 A comparait l'enveloppe de la contribution exacte (44 % = `x^{δβ}`, 0,437/0,438) à la sensibilité des contacts ;
« signe de d_ij par la phase » = phase de la densité (623/640), pas de la Tour (327/640). Recalculs : toutes les valeurs
numériques d'E345/E346 identiques (41 lignes de `results_comparison.csv`) ; nouveau : relation exacte du système stable = dérive
de phase linéaire (battement `2π/ΔT`, 0,91–2,50 en `u`) ; transport des signes des modes vers les apports exacts 121–123/128 ;
identité de transport `d_ij = ∫ (e^{βu}/u)(−2cos Tu)du` (3e−15) ; paires miroirs : même fréquence, module 1 des deux membres,
phases (0,002–0,023 rad) et enveloppes (`x^β`/`x^{1−β}`, rapport 1,9–14 à 727) distinctes. Conclusions suspendues : « aucune loi
bilatérale » (non démontré ; portée = régression linéaire, R² ≤ 0,13 sur les modes), « voisins sans relation », « contacts non
discriminants » (portée = 220 marges), « stabilité ON non transmissible » (non établi). Lean : `Terminal/StableTowerSignals.lean`
(13 théorèmes, axiomes standard) : `NormalizedZeroMode`, `ContactTower`, `exact_eq_envelope_mul_normalized`,
`normalizedMode_norm`, `normalizedMode_phase_hasDerivAt`, `normalizedMode_half_turn`, `normalizedMode_im_at_contact`,
`normalizedMode_re_at_contact`, `contactTower_pitch`, `normalizedMode_radial_shift_is_constant_phase`,
`mirror_modes_same_frequency`, `density_phase_ne_mode_phase` ; toutes valides pour toute `β > 0`, aucune ne fixe `β`. Chaîne non
modifiée : `lake build RHV6Fresh` EXIT=1, une erreur `:854`, 0 sorry, 0 admit. Suite : chercher la loi dans le système stable
(`Q_i`, `C_{i,k}`, dérive de phase, pas `π/T`), démontrer son transport, la tester contre la paire miroir, sans forme ⟺ RH.
Ne pas tracer une Tour contre `x` sans avertissement de coordonnée ; ne pas attribuer une variation d'enveloppe à l'amplitude
intrinsèque ; ne pas lire un R² de régression comme absence de loi.

## 128. E346, raccordement harmonique bilatéral des Tours (2026-10-20)

Mission de l'auteur (consommation intégrale d'E345, sept expériences A–G). Dossier `experiments/E346_BilateralHarmonicRaccord/`
(producteur 33 s, non-régression à 5e−10 sur les 128 `D_j`, 640 `d_ij`, compléments et 231 contacts ; aucun Lean modifié).
A : `∂d_ij/∂β = −2 Re Δ(x^ρ/ρ)`, `∂d_ij/∂T = 2 Im Δ(x^ρ/ρ)` (identités, `countingGapTerm_radial_hasDerivAt`, 5,8e−9) ;
sensibilité radiale relative médiane des apports 5,77 (≈ log x) contre `1/(β²+T²)` pour les contacts (rapport 3609) ; pour
`δβ = −0,1` l'apport change de 44 % (amplitude seule, part de phase nulle), les contacts de `log λ ≤ 5e−4` ; sensibilité ≠
contrainte. B : relation linéaire entre voisins R² ≤ 0,020, égale aux contrôles (non voisins, permutés, synthétiques) ;
chaque `d_ij` est fonction de `(β_i, T_i, p_j, p_{j+1})` seuls. C : 220 marges bilatérales (`k ≥ 1`) ; `|δβ|` linéarisé pour
fermer la plus petite marge 50,7 ; fenêtres discriminantes 0/220 (`abs_log_radialFactor_le`, `parameter_grid_admissible`).
D : complément mesuré par fenêtres 1–16 écarts (0,45 → 0,011 par écart), différences adjacentes, aucune borne indépendante
dans le canal de comptage (`CountingExplicitFormula` nommée, enveloppe sans facteur `1/T`), borne lissée d'exposant 1 seule.
E : ensembles admissibles (seuil explicite `coût ≤ best + 0,05(base − best)`, 25 160 cellules) ; régimes I/II et III (écarts et
niveaux) : fréquence du suivant identifiée à 0,05, intervalle de `β` à `T̂` de largeur 0,10–0,125 ; hauteur qui monte, côté
haut exclu et emboîtement ne retirent AUCUNE cellule basse. F : neuf paires miroirs hors hauteurs certifiées, admises par tous
les contrats de contacts (marges 0,003–0,045), gel = fait du modèle ; insertion et remplacement = contrôles. G : huit
régularités classées, aucune ne réduit les continuations ; cible terminale = conjecture ouverte, formes quantifiées ⟺ RH.
Verdict : résultat négatif publié avec contre-exemples. BUILD=FAIL inchangé (`:854`, `⊢ False`), 0 sorry, 0 admit. RH_FOUND=FALSE.
CORRIGÉ le 2026-10-20 (§131) : ce verdict était trop fort ; voir `experiments/E346_BilateralHarmonicRaccord/CORRECTION_VERDICT_20261020.md`.

## 127. Collaboration des cinq premiers zéros sur les 128 premiers écarts, E345 (2026-10-20)

Mission de l'auteur intitulée « E304 » (nom déjà pris : théorèmes A et B) : loi de collaboration harmonieuse et stabilité du régime engagé.
`experiments/E345_HarmonicCollaborationFiveZeros/` (script 31 s, 8 PASS, 0 FAIL, 10 MESURE ; aucun Lean modifié ; rapport `E345_REPORT.md`,
audit des contrats `lean_contract_audit.md`). Canal de comptage `J0` (milieu aux sauts) autour de `li`, fond complet séparé, `S_i = −2 Re Ei(ρ_i log x)`,
abscisses brutes. Identités contrôlées : `S_i = F_i − F_{i−1}`, `d_{i,j} = S_i(p_{j+1}) − S_i(p_j)`, `D_j = 1 + sauts internes − ΔF` (128/128).
Matrice 640 apports : signe de `d_{i,j}` = `−signe cos(T_i log √(p_j p_{j+1}))` (623/640), aucune association avec la classe mod 6 (p ≥ 0,07),
31 signatures distinctes, 73 transitions ; amplitudes `|d|/enveloppe ≈ 0,55–0,59`, Z1 dominant sur 32/128 écarts seulement ; RMS du complément
0,506 → 0,446 (5 zéros) → 0,011 (5000), jamais nul. Triplets : configuration centrale = conséquence des trois couples et des bornes de l'écart
(identité), complément hors triplet ≈ `D`. Contacts : `log C_k − log Z_k = −arctan(β/T)/T` (231/231), même écart 228/231, changement de signe
de `d` à l'écart du contact 139/231 (un contact n'est pas un changement de signe), emboîtement ON 0 défaut. Inverse (premiers seuls, masqués) :
pics aveugles = hauteurs de zêta, cinq couples retrouvés (T à 1e−2, β̂ 0,508 … 0,545, profil en β plat à cet horizon), un seul minimum,
continuation engagée 4/4, contacts reconstruits à 3e−3 en log ; les cinq zéros ne prédisent pas les écarts 129–256 (RMS 0,79 ≈ 0,77).
Section 9 (remplacements HYPOTHÉTIQUES du zéro central, hauteur hors de toute hauteur publiée) : défaut 0,147 (OFF) et 0,420 (paire), c'est le
défaut d'un REMPLACEMENT (`replacement_not_reconstruct`), plus petit que le complément authentique de cinq zéros ; bornes de contacts aveugles
(`λ − 1 = 3e−4`, emboîtement dès `k = 1`). Verdict : aucune loi de raccordement bilatéral indépendante des paramètres ; la seule rigidité
démontrée est l'unicité spectrale (identification, pas exclusion) ; stabilité du régime NON établie ; but `:854` inchangé.
Règles : ne pas présenter l'organisation des signes comme une loi (lecture des phases aux abscisses premières) ; ne pas chercher sa cause
dans la grammaire mod 6 ; ne pas présenter la reconstruction depuis 128 écarts comme une contrainte ; bornes de contacts non séparatrices.

## 126. La borne du complément infini sous l'opérateur grammatical (2026-10-19)

Demande de l'auteur : « chercher une borne démontrée du complément infini (zéros au-dessus de l'arrivée). fais le. » Recherche dans le dépôt
(RHV6Fresh, rhv3_lean, Mathlib) : aucune borne uniforme en la translation ; acquis = `followingSum_norm_le_budget_linear` (exposant `1`) et
`followingSum_sqrt_iff_following_le_half` (caractérisation). Module `Terminal/GrammarTailBound.lean` FERMÉ (16 théorèmes, objets `tailSignal`,
`headSignal`, `grammarTail`, axiomes standard), importé, composé dans la chaîne (bloc VII quinquies, sept faits ; 69 faits en contexte,
0 consommé ; but `:573`, signature c0cc166f941b). Démontré : `s = tête + queue` (`signal_eq_head_add_tail`) ; tête bornée sous historique ON
(`headSignal_norm_le_of_onLine`) ; queue `≤ budget·e^{u/2}` (`tailSignal_norm_le_linear`) ; projection d'un signal majoré `≤ M L`
(`windowProjection_norm_le_of_bound`) ; `𝓛_G` majoré aux translatés `≤ 4M Σ|w|` (`classWeightedCurvatureC_norm_le_of_translates`) ;
`𝓛_G(queue) ≤ 4 Σ|w|·budget·e^{(a+Λ+L)/2}·L` (`grammarTail_norm_le_linear`), enveloppe non bornée (`grammarTail_linear_envelope_unbounded`) ;
queue bornée uniformément ⟺ tout zéro au-dessus de `H` en ligne (`tailSignal_bounded_iff`), et alors `𝓛_G(queue) ≤ 4 Σ|w|·budget·L`
(`grammarTail_uniform_of_following_onLine`). Tentative att59 (compilateur, retirée) : résidu `Re σ ≤ 1/2` pour tout `σ` au-dessus de `T_l`,
aucune contradiction. Verdict : la seule borne démontrée a l'exposant `1` (croissance de la paire elle-même) ; toute borne uniforme du
complément infini est « tous les zéros au-dessus de l'arrivée en ligne », non dérivée. Aucune avancée vers RH.

## 125. L'opérateur grammatical 𝓛_G et la borne B_G, E344 (2026-10-19)

Demande de l'auteur : « construire l'opérateur grammatical B_G (E344). Vas y. » Module `Terminal/GrammarOperator.lean` FERMÉ (23 théorèmes,
6 objets `grammarOperator`, `operatorSymbol`, `classWeightedCurvature`, `classWeightedCurvatureC`, `curvatureSymbol`, `grammarObservable`),
importé, composé dans la chaîne (bloc VII quater, neuf faits ; 62 faits en contexte, 0 consommé ; but `:551`, signature 4d198c209a93).
Opérateur : `𝓛_G = Σ_r w(classe_r) Δ²_{L_r}` sur `m` écarts consécutifs depuis `r₀`, données = trois poids, un rang, une longueur. Démontré :
symbole `σ_G(d) = Σ_r w(a_r) 2(cosh(dL_r) − 1)`, pair, nul en ligne (annulation du signal ON), `≥ Σ w (d log(1 + plancher/p))²`, `> 0` hors
ligne ; OFF ⟹ ¬B_G (`off_classWeightedCurvature_unbounded`, `class_operator_bound_closes`) ; `D_G = 𝓛_G(paire) + 𝓛_G(complément)` ;
`grammar_operator_two_lemma_closes` ; complément : famille finie ON bornée par `|s| L` à toute fréquence, `𝓛_G` d'une fonction bornée bornée
par `4M Σ|w|`. Non démontré : `B_G(D_G)`, borne de la partie infinie du complément (zéros au-dessus de l'arrivée). Six tentatives (lot 5)
jugées par le compilateur, retirées : résidus = ces deux bornes, l'intégrabilité du signal en escalier, ou réfutés dans le contexte.
E344 (`experiments/E344_GrammarOperator/`, premiers seuls, `X = 10⁷`, 6 PASS, 0 FAIL) : `D_G` de ζ borné (`|D_G| ≤ 0,07`, pente médiane
0,001), porté par les modes ON aux autres fréquences, complément après 5000 zéros publiés 200 fois plus petit ; `a^{(A)}`, `a^{(B)}` ≤ 0,006 ;
témoin `W_δ` séparé (pentes 0,033 / 0,229). `B_G` observée, non dérivée. Aucune avancée vers RH.

## 124. Cinquante-deux tentatives de clôture jugées par le compilateur ; courbure collective de la paire miroir (2026-10-19)

Demande de l'auteur : « des dizaines de tentatives au minimum, le compilateur comme juge, 1300 théorèmes compilés à combiner » ;
puis deux textes : (i) séparer trois niveaux (géométrique démontré / spectral analytique / arithmétique non démontré), remplacer
l'objet d'étude par l'observable collective des premiers `Q_w(a, T)` et son test `𝒞 = Q(a+h) − 2Q(a) + Q(a−h)`, étudier la paire
miroir collectivement (`2cosh(δu)`, courbure `δ²cosh`), ne pas supposer `𝒞 = 0` ; (ii) fermeture proposée en 30 lignes : grammaire ⟹
`B_G`, OFF ⟹ `¬B_G`, deux lemmes indépendants, aucun théorème conditionnel fabriqué.

Méthode des tentatives : chacune est insérée sur la ligne de l'obligation sous la forme `have attK : True := by (have : False := by
<tactique>); trivial`, isolée pour qu'un échec admis ne fuie pas dans la suivante (défaut constaté et corrigé dans le premier lot :
`omega` fermait trivialement par un `False` admis en amont). Quatre lots, 52 tentatives, verdicts dans `main_build_state.md` §1.
Les tactiques de recherche globale (`exact?`, `aesop`, `simp_all`, `hint`) dépassent 4 millions de heartbeats sur un contexte de
45–53 faits et font tomber le théorème entier : inutilisables.

Résultat : aucune tentative ne ferme. Classement des résidus : faux dans le contexte (réfutés par un fait en contexte, jamais posés
comme but, §116) ; antécédents ⟺ `β_l = 1/2` ; bornes de croissance d'exposant `< 1` (bande sans zéro) ; la borne `B_G` du texte.

Module `Terminal/CollectiveCurvature.lean` (24 théorèmes, 7 objets, axiomes standard, importé, composé : bloc VII ter, 53 faits,
0 consommé) : `pairMode_eq_cosh`, `cosh_secondDifference`, `windowProjection_pairMode`, `pairAmplitudeWindow_secondDifference`,
`pair_curvature_nonneg`, `pair_curvature_eq_zero_iff`, `two_cosh_sub_one_ge_sq`, `zeroPairMode_windowProjection`,
`zero_pair_curvature_eq_zero_iff`, `low_zero_pair_curvature_pos`, `pair_curvature_gap_floor` (classe de transition mod 6 dans la
signature), `zero_pair_curvature_gap_floor`, `collectiveProjection`, `collectiveCurvature`, `collectiveComplement`,
`collectiveProjection_finite_split`, `collectiveCurvature_split_pair`, `pair_curvature_closes`, `windowAmplitude_from_zero`,
`off_pair_curvature_unbounded` (OFF ⟹ ¬B_G), `pair_curvature_bound_closes`, `collective_curvature_two_lemma_closes` (ligne 26 du
texte avec `B_G` et la borne du complément en hypothèses explicites). Non compilés : patterns, familles, méta-patterns, modes T/B/O,
contacts et franchissements (E344 à faire), opérateur `𝓛_G`.

Build : BUILD=FAIL, une erreur `DemonstrationChain.lean:524:30`, `⊢ False`, signature 76c21dcc0bfc, RH_FOUND=FALSE.

## 123. E343 → proposition mathématique : invariance radiale par translation grammaticale (2026-10-19)

Texte de travail de l'auteur (30 lignes) : convertir les corrections d'E343 en une proposition sur la grammaire des écarts ; mode
isolé `e^{(β−1/2+iT)u}`, deux fenêtres translatées de `h` ⟹ rapport `e^{(β−1/2)h}`, `= 1 ⟺ β = 1/2` ; translations `h_n =
log(p_{n+1}/p_n)` produites par la grammaire ; arrivée sous un demi : rapport `< 1`, miroir `> 1` ; loi candidate (ligne 19) :
invariance de l'amplitude projetée des modes authentiques. Compilé (`Terminal/GapTranslationInvariance.lean`, 23 théorèmes, 4
objets, axiomes standard, importé, composé dans la chaîne) : `windowProjection`, `zeroMode` (partie réelle = densité de comptage
normalisée d'E334, `zeroMode_re_eq_counting_density`), `windowProjection_mode_translate` (`P_{a+h} = e^{(β−1/2)h} P_a`),
`windowAmplitude_pos`, `zeroMode_translation_invariant_iff` (⟺ ligne), `zeroMode_gap_translate` (même rapport que
`pairAmplitude_prime_step`), `low_zeroMode_gap_translate_lt`, `mirror_zeroMode_gap_translate_gt`, `mirror_pair_gap_ratios_product`,
`windowProjection_finset_sum` (somme finie seulement), `GrammaticalRadialInvariance`, `grammaticalRadialInvariance_iff`,
`single_gap_translation_invariance_closes`, `single_gap_translation_nondecrease_closes` (forme minimale : une fenêtre, un écart, une
inégalité large), `grammaticalRadialInvariance_all_iff` (⟺ RH). Chaîne : bloc VII bis (`hTranslationIff`, `hLowDrift`,
`hMirrorDrift`, `hOppositeDrifts`, `hProjectionLinear`, `hTranslationCloses`, `hLawCloses`), 45 faits, 0 consommé, but `:502`
`⊢ False`. Tentative A (compilateur juge) : `refine hTranslationCloses ⟨0, 0, 1, one_pos, ?_⟩` laisse
`‖P_0(l)‖ ≤ ‖P_{log(3/2)}(l)‖`, strictement faux dans le contexte (`hLowDrift`) : retirée (règle §116, jamais remplacer `False` par un
énoncé faux). Contrôle TDD : loi en hypothèse ⟹ corps fermé (caractérisation). Non dérivé : l'invariance depuis les sauts `1/k` et
les écarts exacts (projection du signal des premiers = toutes les composantes ; isolement = échange avec la somme infinie + borne
du complément d'exposant `< 1`). Point 4 du texte (`β̂_j(X) → 1/2`) : piste de mesure, hors build. Signature 5bd0757ab4e5. RH_FOUND=FALSE.

## 122. Matrice locale–globale, ancre et trois arrivées, E335 / E336 (2026-10-18)

Détail : `AUDIT_LOCAL_GLOBAL_ANCRE_E335_E336_20261018.md`.

- `Terminal/LocalGlobalGapMatrix.lean` FERMÉ : identité signée (atomes `−½Λ/√n`, fond, modes, jacobien), `D_n = S + R`, transitions = télescopage pour toute position radiale, repliement, raccord lissé → brut → `J` membre par membre.
- `Terminal/FirstArrivalsAnchor.lean` FERMÉ : trois arrivées certifiées par comptage, régime initial `d₁ = d₂ = d₃ = 0`, profil de la première rupture, interdiction ⟺ RH.
- E335 : 49 PASS, 5 FAIL. E336 : 21 PASS, 3 FAIL. E334 requalifié (C5 partiel a posteriori).
- Aucune contrainte indépendante trouvée ; but `:484` inchangé.
- Ne pas présenter l'invariance des paramètres entre fenêtres comme une contrainte sur `β` (c'est de l'identifiabilité).
- Ne pas présenter un défaut d'insertion paramétrique comme une exclusion d'un OFF authentique.

## 121. Démarche inverse, E334 (2026-10-18)

Détail : `AUDIT_INVERSE_E334_20261018.md`. `Terminal/InversePrimeSpectral.lean` FERMÉ. Il établit la dérivée distributionnelle
du comptage et la normalisation corrigée `−u e^{−u/2}/2` (atomes `Λ(n)/√n`, mode `e^{(β−1/2)u}cos(Tu)` exact). Il contient aussi
la caractérisation « amplitude constante ⟺ β = 1/2 » (quantifiée ⟺ RH). E334 retrouve depuis les seuls premiers 100/100 hauteurs
et β̂ = 1/2 à 1e−8 : c'est la vérification d'une identité, pas une preuve. Ne pas présenter la rigidité d'amplitude comme dérivée ;
ne pas normaliser par `e^{+u/2}`.

## 120. E332 → architecture du champ de comptage, E333 (2026-10-18)

Détail : `AUDIT_CHAMP_COMPTAGE_E332_20261018.md`. `Terminal/CountingFieldArchitecture.lean` FERMÉ (fréquences, trois niveaux
d'amplitude, taxonomie C < D < Z, champ collectif par écart, complément, saut porté par la limite seule, `J₀` au demi-saut depuis
`Λ`, formule explicite du canal `J` NOMMÉE non démontrée). E333 : 51 PASS. Chaîne non modifiée ; but `:484` inchangé. Ne pas
confondre contacts de Tour (C), extrema (D), zéros bruts (Z), zéros de comptage (B), événements (P), pics collectifs (S) ; ne pas
lire `li(x^ρ)` autrement que `Ei(ρ log x)` ; ne pas présenter `CountingExplicitFormula` comme démontrée.

## 119. E330 / E331 : la résultante des oscillations construit la correction de comptage (2026-10-17)

Mission : addition exacte des oscillations des zéros, puis égalité avec la somme des contributions.

| Statut | Énoncé |
|---|---|
| DÉMONTRÉ (Lean, `Terminal/OscillationResultant.lean`) | `Σ b_z' = −2/(√x log x)·Re Q_s(log x)` avec la résultante pondérée `Σ e^{(β−1/2)u}e^{iTu}` ; égalité centrale `S(b) = S(a) + ∫_a^b −2 Re Q(log t)/(√t log t) dt` ; amplitude-phase ; N → N + 1 ; `‖Q_N‖ ≤ N` ; ajouter un zéro retire sa contribution du complément |
| VÉRIFIÉ (E330, E331) | Ei contre intégration ≤ 3·10⁻¹⁴ (N = 3, 10, 100), 10⁻¹⁷ en mpmath |
| OBSERVÉ | pas de fréquence propre unique ; complément 0,525 → 0,437 ; dégradations locales 34 % des milieux ; premiers corrélés au signe de Re Q_N (formule explicite), non attirés par les extrema |
| CONTREDIT | complément d'une troncature fixée en `O(√x/log x)` (exposant 0,6 à 0,85 par décade) |
| CARACTÉRISATION | arrivée en mode unité (K1) : le but réécrit |
| OUVERT, force d'un demi-plan sans zéro | complément borné uniformément en N (K2, forme E329) |
| COMPLÉMENT (espace commun) | identités (1)–(4) vérifiées et compilées (`normSq_unitResultant_split`) ; fenêtres communes : produit/exigé ≈ 1/10 par écart, corrélation 0,96 par décade ; Weil avec noyau de Hann vérifiée à 6,5·10⁻¹⁰ (identité) ; amplitude 1 et phase 0 de chaque fréquence lues sur les premiers seuls, constantes entre deux fenêtres (mesure finie) |
| OBLIGATION AFFICHÉE (sonde) | `∃ u₁ < u₂, ‖Q_{l}(u₁)‖ ≤ ‖Q_{l}(u₂)‖` : poids du mode de l'arrivée non décroissant ; caractérisation pour un l, force de RH quantifiée |

But `:484` inchangé, 0 fait consommé ; aucune implication raccordée.

## 118. E328 vérifiée, E329, loi intermédiaire au poids p^−α (2026-10-17)

Mission : investigation arithmétique et raffinement itératif du but Lean.

| Statut | Énoncé |
|---|---|
| Compilé | `PrimeGrammarQuantitative` §8 : `abel_partial`, `windowResidual_bound_of_weighted`, `zero_free_of_weighted_residual`, `weighted_law_excludes_low`, `riemannHypothesis_of_weighted_residual` (axiomes standard) |
| Composé | `hWeightedCloses` dans `arrival_low_contradiction` ; but `⊢ False` inchangé (`:484`), 0 fait consommé |
| Sonde hors build | `experiments/E329_PrimeGapWindowsThreeZeros/lean/` : noyau `l`, `hZone` ; proposition ouverte minimale `∃ B, ∀ m, \|weightedResidual ((3/2 − β_l)/2) m\| ≤ B` |
| Force | Demi-plan sans zéro Re s > α (pour un `l` fixé) ; RH pour tous les α > 1/2 ; fausse à α = 1/2 (Littlewood) ; démontrée seulement à α = 1, forme logarithmique (§7) |
| Observations | E329 : demande J par écart = résidu au poids 1/log p (identité ; corrélation 0,959) ; 3 zéros 0,31 contre 0,22 au plus pour les témoins ; 5000 zéros 0,9994 ; S_α suit 1/2 − α jusqu'à 10⁸ |
| Obstruction | Aucun poids p^−α avec α < 1 n'est démontrable avec les outils présents ni connu ; même obstruction que `hAbsurdCloses` |

## 117. Grammaire quantitative des écarts premiers, réfutation du Round 8 requalifiée, E327 (2026-10-17)

Instruction de l'auteur : plan validé avec neuf corrections (module composé, pas de région sans zéro, prédiction ≠ reconstruction,
contrôles étiquetés synthétiques, termes croisés = identité, A8 algébrique seulement, fréquence étudiée explicitement, plus petit
lemme nouveau améliorant une borne, livraison distinguant compilé / observé / hypothèse / obligation).

| Énoncé | Statut | Nom |
|---|---|---|
| `R_{0,m} = p_m − ϑ(p_m) + log p_m − 2`, fenêtre | compilé, identité | `cumulativeResidual_eq`, `windowResidual_eq` |
| borne aux premiers ⟹ contrôle des cellules | compilé | `cell_control_of_rank_bound` |
| borne critique du résidu cumulé ⟹ RH | compilé, conditionnel, force de RH | `riemannHypothesis_of_cumulative_residual_bound` |
| RH ⟹ blocs d'exposant `1 + θ` | compilé, forme intégrée seule | `prime_blocks_of_riemannHypothesis` |
| transition mod 6 + écart ne fixent pas `r_n` | compilé, portée : une transition | `residual_not_function_of_transition` |
| mot de deux écarts + trois classes ne fixent pas `r_{n+1}` | compilé, portée : cette classe de profils | `residual_not_function_of_two_gap_state` |
| position + écart fixent `r_n` | compilé, tautologie (garde contre la fuite) | `gapResidual_of_position_and_gap` |
| termes croisés, fenêtres consécutives, blocs de classes | compilé, identités | `cumulativeResidual_sq`, `windowResidual_sq_split`, `cross_eq_sum_classCross` |
| modes T, B, O | compilé ; non-détermination algébrique seule | `residualMode_energy`, `modeT_not_function_of_BO` |
| compensation logarithmique bornée | compilé, SANS RH, nouveau dans le dépôt, classique (Mertens) | `logGapResidual_cumulative_bounded` |

E327 (`experiments/E327_PrimeQuantitativeGrammar/`, 10⁹, Sonnet ; observations) : route causale sans gain ; route structurelle :
compensation par termes croisés négatifs et anticorrélation des fenêtres consécutives, détruite par toute permutation (résidus,
écarts avec positions recalculées, blocs), présente ni dans Cramér ni dans Cramér mod 6 ; pics spectraux de `E(x)` mesurés sans
identification ; Cramér satisfait aussi la borne critique (non séparateur). Écart : Cramér littéral `1/log n` gardé à part, Cramér
principal `2/log n`.

Verdict : la piste « grammaire quantitative complète » est rétablie dans sa portée ; la seule loi démontrée est au poids `1/p`
(classique) ; la borne au poids 1 est la force de RH ; aucune loi intermédiaire démontrée ; but `⊢ False` inchangé, faits consommés 0.

## 116. Réduction au vrai but `False` et examen de la liaison (2026-10-17)

Demande : « comment l'erreur peut-elle être toujours au même endroit ? challenge cette construction », puis « applique A à E » avec
deux corrections (identités universelles conservées quand elles transportent ; ce qui manque est une contrainte indépendante issue des
événements premiers exacts). Constats (12 derniers builds, sonde E326) : position = en-tête du théorème ; 65 faits ajoutés, aucun
consommé ; trois reformulations équivalentes du but ; le dernier but affiché était réfutable dans son contexte. Réduction :
`arrival_low_contradiction (h₁ p hE hV hOn hHist hL hBelow) : False` (but minimal, ligne `hObligation`) ; interface
`off_signal_amplitude_incompatible` fermée par réduction ; contexte 122 → 36 ; `scripts/goal_dependencies.py` (graphe) appelé par
`status.sh`. Liaison : identité collective (toute position radiale) ≠ obligation par terme ; la contribution de `l` = courbe − passé ON
− (suite − `l`), la suite contient le miroir de `l` ; l'historique ON informe sur le passé seulement. Verdict : non circulaire, force
de RH (loi quantifiée ⟺ RH sous l'ancre). Aucune avancée vers RH.

Traçabilité des 91 renvois retirés du contexte (fait → théorème source, toujours compilé dans son module) :

| Fait retiré | Théorème source |
|---|---|
| `hNoReplacement` | `replacement_not_reconstruct` |
| `hMirrorHeight` | `(preuve locale)` |
| `hAmplitudeReadsSignal` | `radial_le_of_remainder_growth` |
| `hNeedIff` | `constantNeed_iff_onLine` |
| `hMeetingIff` | `constantNeed_meeting_points` |
| `hNeedRatio` | `need_ratio_meeting_points` |
| `hFrequencyOnly` | `frequency_only_between_constant_needs` |
| `hNeedLaw` | `constantNeed_law_iff_riemannHypothesis` |
| `hNeedHistoryLaw` | `constantNeed_history_law_iff_riemannHypothesis` |
| `hNotConstant` | `decreasing_breaks_constantNeed` |
| `hSpacing` | `frequency_of_spacing` |
| `hSpacingBlind` | `spacing_blind_to_radial` |
| `hRadialOfMeeting` | `radial_of_meeting_point` |
| `hRadialOfNeed` | `radial_of_need_ratio` |
| `hReadingsAgree` | `two_radial_readings_agree` |
| `hNeedShiftIff` | `need_constant_iff_not_shifted` |
| `hNeedMoves` | `need_change_moves_meeting_points` |
| `hVertical` | `vertical_change_contracts_spacing` |
| `hHorizontal` | `horizontal_change_shifts_and_drifts` |
| `hCoupleLock` | `couple_locked` |
| `hCoupleLockAmp` | `couple_locked_by_amplitude` |
| `hNoDiagonal` | `no_diagonal_solution` |
| `hMeetingLaw` | `meeting_need_law_iff_riemannHypothesis` |
| `hOccupiedPoints` | `occupied_signal_meeting_points` |
| `hOnOfOccupied` | `onLine_of_occupied` |
| `hNoOffOccupied` | `no_off_at_occupied_frequency` |
| `hOffUnoccupied` | `off_frequency_unoccupied` |
| `hUpperMirror` | `upper_has_lower_at_same_frequency` |
| `hOnlyLow` | `only_low_candidate` |
| `hTakenIff` | `frequencyTaken_iff_onLine` |
| `hOneSignalIff` | `oneSignalPerFrequency_iff_riemannHypothesis` |
| `hTakenLaw` | `frequencyTaken_law_iff_riemannHypothesis` |
| `hOccupiedClosure` | `riemannHypothesis_of_occupied_and_one_signal` |
| `hGenerated` | `generatedFrequency_of_zero` |
| `hArithFrequency` | `arithmeticFrequency_of_zero` |
| `hArithFrequencyIff` | `arithmeticFrequency_iff` |
| `hMeetingOf` | `(preuve locale)` |
| `hLineMeetingOf` | `(preuve locale)` |
| `hArithMeetingIff` | `arithmeticMeeting_iff_meetingOnLine` |
| `hArithBeyondIff` | `arithmetic_meeting_beyond_line_iff_low` |
| `hArithLaw` | `arithmeticMeeting_law_iff_riemannHypothesis` |
| `hRadialFromMeeting` | `radial_from_meeting` |
| `hRadialFromNeed` | `radial_from_need_ratio` |
| `hMeetingOnLineIff` | `meeting_on_line_iff` |
| `hMeetingBelowIff` | `meeting_below_iff_low` |
| `hFiberIff` | `meetingOnLine_iff_fiber_onLine` |
| `hSingleIff` | `singleSignal_iff_meetingOnLine` |
| `hDetects` | `meeting_shift_detects` |
| `hBlind` | `meeting_shift_blind` |
| `hNoBelowIff` | `noMeetingBelow_iff_riemannHypothesis` |
| `hSingleLaw` | `singleSignal_law_iff_riemannHypothesis` |
| `hIndividual` | `arithmeticMeeting_individual` |
| `hCollectiveIff` | `collectiveMeeting_iff_sum_zero` |
| `hCollectiveRest` | `collectiveMeeting_component_eq_neg_rest` |
| `hFiniteSmooth` | `finite_components_differentiableAt` |
| `hThreeIngredients` | `movement_law_three_ingredients` |
| `hImposed` | `imposed_contribution_eq` |
| `hImposedIncrement` | `imposed_contribution_increment` |
| `hImposedAmplitude` | `imposed_amplitude_change_unique` |
| `hMirrorNe` | `(preuve locale)` |
| `hMirrorAfter` | `mirror_precedes` |
| `hMirrorHigh` | `(preuve locale)` |
| `hMirrorFrequency` | `arithmeticFrequency_of_zero` |
| `hMirrorImposed` | `imposed_contribution_eq` |
| `hMirrorDrift` | `imposed_contribution_drift` |
| `hMirrorStepGrows` | `passage_entry_radial_le_half` |
| `hHighOnlyAtArrival` | `passage_entry_radial_le_half` |
| `hAvailableTooWide` | `(preuve locale)` |
| `hReadsLower` | `zero_low_meeting_reads_lower_frequency` |
| `hLineReadsOwn` | `line_meeting_reads_own_frequency` |
| `hJointForm` | `residueTerm_joint` |
| `hSmoothedMeetings` | `smoothedMeeting_eq_contact` |
| `hSmoothedReal` | `residueTerm_real_at_smoothedMeeting` |
| `hSmoothedMeetingIff` | `smoothedMeeting_line_iff` |
| `hMinimalCloses` | `mirror_not_faster_closes` |
| `hMinimalSame` | `onScale_iff_mirror_not_faster` |
| `hMinimalLaw` | `notFaster_law_iff_riemannHypothesis` |
| `hEnvelopeChannel` | `gapEnvelope_eq_raw` |
| `hShortGapOneMeeting` | `at_most_one_meeting_in_short_gap` |
| `hTw` | `(preuve locale)` |
| `hVerticalShift` | `verticalMeetingShift_neg` |
| `hExpectedInward` | `expected_meeting_moves_inward` |
| `hDecomposed` | `meeting_shift_decomposed` |
| `hCompensationIff` | `meeting_compensation_iff` |
| `hCompensationLow` | `meeting_compensation_requires_low` |
| `hCompensationRealizable` | `exists_compensating_frequency` |
| `hExpectedIff` | `expected_meeting_iff_radial_shift_zero` |
| `hRadialPosIff` | `radialMeetingShift_pos_iff` |
| `hRadialZeroIff` | `radialMeetingShift_eq_zero_iff` |
| `hCompensationCloses` | `compensation_law_closes` |
| `hNoShiftLaw` | `no_radial_shift_law_iff_riemannHypothesis` |

## 115. Synchronisation conjointe sur chaque écart premier : fréquence, rencontres, amplitude (2026-10-17)

Demande : « la synchronisation doit porter sur trois éléments indissociables : la fréquence, les points de rencontre et l'amplitude,
pour chaque Tour et chaque écart premier » ; « composer, identifier la seule implication manquante, la minimiser, tenter de la
démontrer ». Constat : les trois paramètres étaient compilés séparément ; les rencontres étaient brutes, la loi par écart lissée.
Compilé (`Terminal/GeneratedFrequency.lean` §12, 27 théorèmes, axiomes standard) : `point_polar`, `cpow_polar`, `smoothingPhase`,
`jointTerm`, `memberJoint`, `residueTerm_joint`, `jointTerm_step`, `memberJoint_gap_step`, `jointTerm_real_at_meeting`,
`smoothedMeeting`, `residueTerm_real_at_smoothedMeeting`, `smoothedMeeting_eq_contact`, `smoothedMeeting_spacing`,
`smoothingPhase_low_gt_line`, `smoothingPhase_high_lt_line`, `smoothedMeeting_line_iff`, `prime_gap_joint_synchronization`,
`imposed_joint_gap`, `primeGap_log_telescope`, `primeGap_log_unbounded`, `low_joint_deviation_every_gap`,
`mirror_joint_deviation_every_gap`, `ImposedNotFasterAtGap`, `ImposedOnScaleAtGap`, `imposedNotFasterAtGap_iff`,
`imposedOnScaleAtGap_iff`, `mirror_not_faster_closes`, `onScale_iff_mirror_not_faster`, `notFaster_law_iff_riemannHypothesis`.
Composé en contexte de `off_signal_amplitude_incompatible` (douze faits, aucun nouveau but). Implication manquante minimale : sur un
écart, la contribution imposée au miroir ne grandit pas plus vite que l'échelle commune ; quantifiée ⟺ RH ; tentative non fermée
(identité en β ; pas de borne indépendante par écart). E325 (`experiments/E325_JointGapTriple/`, x ≤ 10^6) : identité par écart PASS,
β lu par l'enveloppe médian 0,508, rencontre lissée insensible (FAIL d'accord, attendu par la sensibilité ~2/T), écart par écart la
contribution de ligne reproduit le zéro publié. Ne pas présenter la forme conjointe comme une contrainte nouvelle : c'est une
réécriture exacte ; ne pas lire les rencontres brutes comme rencontres du terme lissé. Build : une erreur, `:419`, but inchangé,
signature d0dc2fe10ff5.

Revue contre le prompt de mission (même jour) : (1) matrice complétée (`gapPhase`, `gapEnvelope`, `gap_entry_joint`,
`gapEnvelope_eq_raw`, `at_most_one_meeting_in_short_gap`, `matrixCell_eq_gap_entry`) ; (2) la « forme minimale » n'est PAS une
réduction : elle équivaut à `β_w ≥ 1/2` (identité `e^{β L_n}`) et contient `othersSum` ; seule forme écrite avec les premiers seuls :
`hAbsurdCloses` ; (3) deux références distinctes dans le désaccord conjoint ; (4) trois fermetures alternatives par lecture
(`hMeetingCloses`, `hFrequencyCloses`, `hAmplitudeCloses`), demande de l'auteur « en cas de doute, tenter le Lean avec plusieurs
solutions ». E325 relue à la précision disponible : enveloppe 0,51 (arrondie), rencontre indéterminée (erreur de hauteur ≫
sensibilité), pas un désaccord. Non-circularité :

| Question | Réponse pour le §12 |
|---|---|
| Donnée des premiers seuls | reste lissé `smoothedRemainder`, pas logarithmiques `L_n` |
| Apport de la formule explicite | somme sur tous les vrais zéros (`smoothedRemainder_eq_tsum_residueTerm`) |
| Propriété d'une Tour | forme polaire, loi par écart, rencontres lissées |
| Somme → Tour | exact : imposée = somme − part fixe des autres ; aucune borne de terme tirée d'une borne de somme |
| Fréquence attendue | référence géométrique, paramètre ; jamais un vrai zéro |
| Contacts | propres (bruts et lissés) ; aucun lien démontré avec un premier |
| Canal | lissé partout ; conversion vers le brut démontrée |
| Conclusion plus forte que les prémisses ? | non ; les formes de fermeture équivalent à la conclusion pour ce zéro |
| Statut vis-à-vis de RH | identités : vraies pour toute position radiale ; formes de fermeture quantifiées : ⟺ RH |
| Vraie paire miroir OFF | toutes les identités restent vraies : c'est l'obstacle |

Build : une erreur, `:419`, but inchangé, signature 887c8ef2758d.

## 114. Zêta est une somme : deux lectures de la fréquence de chaque terme (2026-10-16)

Demande : « démontrer que les zéros hors de la ligne doivent nécessairement avoir une hauteur au-dessus de la hauteur attendue si
β < 1/2, donc grandissent forcément trop vite par rapport à la fréquence attendue ; zêta est une somme, il faut y revenir et compiler
cela ». Compilé (`Terminal/GeneratedFrequency.lean` §11, axiomes standard) : `arctan_low_gt_line`, `low_meeting_reads_lower_frequency`
(`0 < Re p < 1/2`, `Im p > 0`, rencontre de `p` = rencontre de la ligne à la fréquence `T'` ⟹ `T' < Im p`), `line_meeting_reads_own_frequency`
(injectivité de la rencontre de la ligne en la fréquence), `phase_gap_unbounded` (`T' < T ⟹ ∀ M, ∃ x > 1, M < (T − T') log x`),
`zero_low_meeting_reads_lower_frequency` (instance). Composé en contexte de `off_signal_amplitude_incompatible` : `hReadsLower`,
`hLineReadsOwn`. Chiffres de contrôle (calcul précédent, deuxième zéro 21,022) : un point sous un demi qui partage la rencontre de la
ligne à 21,022 est entre 21,022 et 21,345 ; c'est le même énoncé lu à l'envers. Portée : caractérisation (désaccord des deux lectures ⟺
sous un demi, accord ⟺ ligne) ; la contradiction demande que la courbe des premiers impose l'accord à chaque terme, ce qui est le lock.
Build : une erreur, `:419`, but inchangé, signature ee67387810f9.

## 113. Raisonnement par l'absurde, côté miroir (2026-10-16)

Demande de l'auteur : « la preuve par l'absurde est la meilleure, elle est factuelle et valide à l'infini sur tout l'horizon » ; puis,
sur la proposition « rendre explicites le miroir et son amplitude croissante, tenter la contradiction contre ce que les écarts exacts
imposent à tous les signaux » : « EXACTEMENT, écris tout cela avec force détail ».

1. Forme. `off_signal_amplitude_incompatible` est déjà une preuve par l'absurde : supposition `hDecr` (signal d'amplitude décroissante à
   la fréquence du zéro suivant, donc `hZone : β_w < 1/2`), conclusion `False`. Aucun nouveau but n'est créé.
2. Le miroir (ajouté, fermé) : `hMirrorNe` (`mirrorMember_ne`), `hMirrorAfter` (`mirror_precedes`), `hMirrorHigh`
   (`mirrorMember_radial`), `hMirrorFrequency` (`arithmeticFrequency_of_zero`), `hMirrorImposed` (`imposed_contribution_eq`),
   `hMirrorDrift` (`imposed_contribution_drift`), `hMirrorStepGrows` (facteur `exp((β_{w*} − 1/2)L_r) ≥ 1`, `thm_primeGapLogRatio_pos`) ;
   `hMirrorGrow` existait déjà.
3. Ce qui ne contredit pas : `hHighOnlyAtArrival` (`passage_entry_radial_le_half`) exclut le côté haut seulement à l'arrivée d'un
   passage qui monte ; le miroir est rangé après `w`, il n'est pas cette arrivée. « β > 1/2 déjà exclu » n'est donc pas global ; l'employer
   contre le miroir serait circulaire. Liste fixée par les premiers, non-compensation, reproduction exacte : vraies pour toute position.
4. Contradiction cherchée (fermée) : `hAbsurdCloses : (∃ θ C, θ < 1 − β_w ∧ ∀ x > 1, ‖R(x)‖ ≤ C x^θ) → False`, par
   `radial_le_of_remainder_growth` appliqué au miroir (même contenu que `mirror_closes_of_remainder_growth`, recomposé sans import).
5. Disponible : `hStripFromPrimes` (`radial_strip_from_primes`), `hAvailableTooWide : 1 − β_w ≤ 1` ; seul l'exposant `1` est démontré
   depuis les poids des premiers (`smoothedRemainder_linear_growth`) ; il ne contredit pas le miroir.
6. Fait manquant, unique : abaisser, depuis les écarts exacts, l'exposant de croissance des signaux de la courbe des premiers sous
   `1 − β_w` ; vu du côté des premiers : aucun signal ne grandit plus vite que l'échelle commune (lock). Pour ce seul miroir l'énoncé
   est local à `w` ; sous toutes ses formes globales (tout `w`) il a la force de RH.
7. Build : une erreur, `:419`, but inchangé, contexte allongé, signature 8a298a4f3a22, axiomes standard ; lock inchangé.

## 112. Non-compensation et amplitude imposée ; mission « intégration terminale » vérifiée ; E324 (2026-10-16)

Contexte : plan corrigé par l'auteur (« aucun nouveau but ; garder l'amplitude ; ne pas revenir à RH » ; « le reste ne peut pas absorber
la dérive : nous avons un théorème compilé de non-compensation »). Mission collée vérifiée : les 28 théorèmes cités existent sous leurs
noms ; le contexte du but contient déjà `hZone : β_w < 1/2` ; aucune réécriture du dernier pas n'a été faite (refusée par l'auteur).
Erreur corrigée : la phrase « le reste peut absorber la dérive quelle que soit la position radiale » contredit les théorèmes de
non-compensation (le reste = les vrais zéros, points fixes). Lean (`GeneratedFrequency.lean` §10, 6 théorèmes + `othersSum`, axiomes
standard) : contribution imposée, forme incrémentale, unicité par remplacement et par changement d'amplitude, dérive par écart
`e^{(β−1/2)L_r}`. Composés en contexte ; but `:419` inchangé, signature b0c813d0bf34. Verdict : présence et unicité acquises, valeur
non dérivée ; la contribution imposée est le terme propre de `w`, sa dérive sous un demi est conforme à `hDecr`. Manque : minoration
d'ordre `√x` de (reste − part fixe des autres) depuis les écarts exacts. E324 : 9 PASS, exposant 0,4997–0,5003 aux vingt premières
fréquences, besoin constant, témoin à 0,077–0,081 ; mesure finie. RH_FOUND=FALSE.

## 111. Loi de compensation entre déplacement vertical et déplacement radial (texte collé par l'auteur, 2026-10-16)

Programme collé : (1) la progression des premiers impose la fréquence suivante et son point de rencontre attendu ; (2) un changement de
hauteur modifie la géométrie de la Tour ; (3) un changement de position radiale déplace ses contacts et modifie son amplitude ; (4) montrer
que les deux déplacements ne peuvent pas se compenser tout en conservant la rencontre arithmétique attendue ; (5) si l'impossibilité est
déjà compilée indépendamment, elle ferme le but. Consignes : aucune normalisation (aveugle à β) ; fournir au compilateur ce qu'il attend,
quitte à tenter un terme.

Compilé (`Terminal/GeneratedFrequency.lean` §9 ; module à 55 théorèmes, 16 objets, axiomes standard ; abscisses brutes) : `verticalMeetingShift`,
`radialMeetingShift`, `arithmeticRadialShift` ; `arctan_div_strictAnti` (valeur moyenne appliquée deux fois) ; `verticalMeetingShift_neg`,
`expected_meeting_moves_inward` (point 2) ; `radialMeetingShift_pos_iff`, `radialMeetingShift_eq_zero_iff` (point 3) ;
`meeting_shift_decomposed` (décomposition exacte) ; `meeting_compensation_iff`, `meeting_compensation_requires_low`,
`meeting_compensation_realizable`, `exists_compensating_frequency` (point 4, forme « conserver la rencontre du départ » : compensation
possible, c'est le cas bas, et réalisable pour la fonction de rencontre : l'impossibilité est FAUSSE sous cette forme) ;
`expected_meeting_iff_radial_shift_zero`, `arithmeticRadialShift_zeroPoint`, `arithmeticMeeting_iff_radial_shift_zero` (point 4, forme
« conserver la rencontre attendue à la nouvelle fréquence » : équivaut au but) ; `compensation_law_closes` ;
`no_radial_shift_law_iff_riemannHypothesis` (quantifiée ⟺ RH). Point 5 : l'inventaire du §110 (addendum) reste valable, aucune
impossibilité indépendante compilée.

Chaîne : loi composée en contexte ; but réécrit sans perte `⊢ arithmeticRadialShift (Rep.point i) = 0` (déplacement radial de rencontre
nul pour tout signal des premiers de fréquence `T_w`), signature 4ae9f8496acf. Terme tenté : aucune hypothèse du contexte ne donne ce déplacement
(`hDecr` ne porte que sur `w`). Conclusion : les déplacements sont compilés ; la compensation d'une montée par une descente radiale
conserve la rencontre du départ et n'est pas impossible ; ce qui ne peut pas être compensé est la rencontre attendue à la nouvelle
fréquence, et cette impossibilité est le but. Ce que le compilateur attend : la raison, lue sur les écarts exacts, pour laquelle le signal
engendré à la fréquence du zéro suivant a sa rencontre à la position attendue. RH_FOUND=FALSE.

## 110. Trois objets distincts : rencontre propre, rencontre collective, événement premier (texte de support collé, 2026-10-16)

Texte collé par l'auteur (« il y a peut-être ENCORE un problème méthodologique dans tes livraisons ; déduis-en les actions ») :
trois graphiques (Weierstrass, `ψ(x) − x` contre vingt zéros, trois Tours ON), une superposition commune `F(u) = Σ A_n(u) cos(T_n u + φ_n)`,
et une distinction `C_n` (rencontre propre de la Tour `n`), `R` (rencontre du signal collectif avec le fond), `P` (événement arithmétique
exact) ; erreur de méthode potentielle : `ArithmeticMeeting` est défini par `meetingOf (Rep.point i)`, rencontre individuelle, et ne
mesure pas les intersections du reste total avec son fond ; les contraintes aux événements premiers appartiennent à la somme infinie.

**Vérification** (code et expériences). (1) `ArithmeticMeeting T c := ∀ Rep i, w_i ≠ 0 → |Im p_i| = T → meetingOf (p_i) = c` : rencontre
propre de chaque composante, exact. (2) E322 Q4 : « déplacement `Δu` des rencontres de chaque fréquence (zéros de la contribution
bande-passée contre le modèle de ligne) égal à celui du contrôle ON » ; E321 : translation lue sur une lecture calibrée sur un contrôle
ON : les deux lisent une contribution filtrée du signal collectif, non la rencontre propre d'une composante ; l'égalité au contrôle
ON (`|Δu_ζ − Δu_ON| ≤ 3σ`) est une égalité entre deux lectures filtrées, elle ne porte pas le but. (3) Le besoin constant de E313/E321 est
lu sur ces mêmes contributions filtrées ; des amplitudes propres constantes ne donnent pas une amplitude collective constante
(interférences de phase) : la phrase ne vaut pas pour la somme. (4) E323 : aucune ligne fermée par vingt colonnes ni par cinq mille,
chaque ligne portée par la queue : les singularités appartiennent à la somme infinie.

**Lean** (`Terminal/GeneratedFrequency.lean` §7 ; 37 théorèmes, 13 objets, axiomes standard ; import ajouté
`RHV3Lean.Objects.ZetaSmoothedUnsmoothingP5` dans le module, aucun import nouveau dans la chaîne) :

| Objet / théorème | Énoncé | Portée |
|---|---|---|
| `arithmeticMeeting_individual` | `ArithmeticMeeting T c ⟺ ∀ Rep i, w_i ≠ 0 → |Im p_i| = T → meetingOf p_i = c` | `Iff.rfl` : le but est la rencontre propre de chaque composante |
| `CollectiveMeeting x` | `smoothedRemainder x = 0` | rencontre du signal collectif des premiers avec son fond |
| `collectiveMeeting_iff_sum_zero` | `CollectiveMeeting x ⟺ Σ_i w_i f_x(p_i) = 0` (`x > 1`, toute `Rep`) | relation sur toutes les composantes à la fois |
| `collectiveMeeting_representation_free` | la somme s'annule dans `R₁` ⟺ dans `R₂` | identité |
| `PrimeSignalRepresentation.summable_components` | sommabilité des composantes en `x > 1` | par `summable_profiles` |
| `collectiveMeeting_component_eq_neg_rest` | à une rencontre collective, `w_i f_x(p_i) = −Σ_{j ≠ i} w_j f_x(p_j)` | la relation porte sur la somme, aucune rencontre propre fixée |
| `PrimeEvent n`, `primeEvent_iff_isPrimePow` | `Λ(n) ≠ 0 ⟺ n` puissance de premier | événement arithmétique exact |
| `psi_natCast_eq_sum_range` | `ψ(N) = Σ_{n ≤ N} Λ(n)` | identité |
| `arithmetic_primitive_step` | `P(N + h) = P(N) + h·ψ(N)`, `0 < h ≤ 1`, `P(x) = x·S(x)` | primitive arithmétique affine par morceaux |
| `arithmetic_primitive_slope_jump` | `(P(N+h) − P(N))/h − (P(N) − P(N−h))/h = Λ(N)`, `N ≥ 1`, `0 < h < 1` | saut de pente exact |
| `primeEvent_slope_jump_ne_zero` | saut `≠ 0` aux événements premiers | — |
| `finite_components_differentiableAt` | toute somme finie `Σ_{i ∈ s} w_i f_y(p_i)` est dérivable en `x > 0` | aucune sous-somme finie ne porte un saut de pente |

**Chaîne** : énoncé, hypothèses et but inchangés ; docstring et commentaire RESTE réécrits ; en contexte `hIndividual`, `hCollectiveIff`,
`hCollectiveRest`, `hEventJump`, `hFiniteSmooth` ; but `:419`, signature ceb3039e6ad7.

**Ce que la correction ne fait pas** : elle n'écrit pas la contrainte que les événements `P` imposent simultanément aux rencontres propres
`C_n` et à leur résultante `R` ; c'est la flèche manquante ; sa forme quantifiée a la force de RH. Aucune mesure actuelle ne lit la
rencontre propre d'une composante depuis les premiers seuls sans calibration ON. Lock inchangé.

**Addendum, second texte collé (même jour) : les trois ingrédients de la loi de mouvement cherchée.** Proposition à rechercher :
« passage vertical depuis ON + fréquence authentique suivante + rigidité `M^Z = M` ⟹ impossibilité d'une arrivée sous `1/2` », prouvée
sans `radial_conservation_anchored`, RH ni le théorème ouvert. Inventaire (grep sur toutes les conclusions `rZeroRadialPosition
p.zLaterMember = 1/2`, `1/2 ≤ …`, `= rZeroRadialPosition p.zEarlierMember`) : `amplitudeStableSync_closes` (suppose `AmplitudeStableSync`),
`engaged_step_closes_of_symmetric_arrival` (suppose `TowerSymmetric` de l'arrivée), `engaged_persists_to_infinity` (`hOnly`),
`window_transmission` (`hSep`), `count_step_invariant_suffices` (pas de comptage `< 2`), `conservation_of_riemannHypothesis`,
`heightOnly_of_riemannHypothesis`, `noRegimeChange_no_radial_displacement` (RH / `PNoRegimeChange`), `vertical_exhausts_iff_arrival_onLine`,
`amplitudeStableSync_iff` (caractérisations), la chaîne elle-même (conditionnelle au théorème ouvert). Aucun ne conclut depuis les trois
ingrédients seuls : l'exclusion n'est pas compilée indépendamment. Compilé (`movement_law_three_ingredients`, §8) : sur tout passage
vertical depuis ON les trois ingrédients sont acquis avec une conclusion muette sur la position radiale de l'arrivée ; la liaison vaut sur
tout passage (`passage_prime_tower_bond`) et sur le passage de même hauteur (`sameHeight_satisfies_both_rigidities`) ; toute position dans
`]0, 1/2]` satisfait les obligations de contact (`parameter_grid_admissible`). Conclusion : les trois ingrédients ne peuvent pas porter
seuls l'exclusion ; la loi de mouvement indépendante cherchée doit lire autre chose (poids exacts et reconstruction, hors de la seule
succession). Rien n'est reconstruit, aucune loi n'est posée. En contexte de la chaîne : `hThreeIngredients`.

## 109. Réimplémentation des objets « fréquence engendrée » et « rencontre » depuis le reste des premiers (texte d'audit collé, 2026-10-16)

Texte collé par l'auteur (« réimplémente correctement les erreurs qu'a commises Opus ») : un audit externe de la dernière pièce,
vérifié sur le dépôt par son auteur, et vérifié ici dans le code avant toute modification.

**Constats, tous exacts** : `GeneratedFrequency T := ∃ z : TrueZero, rZeroHeight z.1 = T` part d'un zéro déjà donné, ce n'est pas un
objet calculé depuis les écarts premiers ; `MeetingOnLine T` exige déjà que tous les zéros de hauteur `T` aient la rencontre de la
ligne, c'est la propriété cherchée ; `generatedFrequency_of_zero` est `⟨z, rfl⟩` ; le dernier pas de la chaîne
(`frequencyTaken_of_meeting_on_line`) réclame `contactMinusAt w 0 = lineContact T_w 0`, c'est-à-dire `β_w = 1/2` ; le texte du module
annonçait pourtant « tout y part de la courbe des premiers ». Le canal `J` n'est pas formalisé et les sommes finies ne ferment pas les
sauts (E323). Les expériences E321–E323 et les théorèmes géométriques ne sont pas réfutés : ils n'apportaient pas la flèche à la chaîne.

**Correction** (`Terminal/GeneratedFrequency.lean`, 26 théorèmes, 11 objets, axiomes standard ; noms antérieurs conservés) :
- objets écrits depuis le reste des premiers `smoothedRemainder` et rien d'autre : `PrimeSignalRepresentation ι` (points distincts,
  `Re ≤ 1`, hors de `0` et `−1`, localement finie, poids absolument sommables, `Σ weight · x^point/(point(point+1)) = smoothedRemainder x`
  pour tout `x > 1`) ; `toSpectral`, `toPrime` (par `smoothedRemainder_eq_tsum_residueTerm`) ; `primeTrueRepresentation` ;
  `ArithmeticFrequency T := ∀ Rep, ∃ i, weight i ≠ 0 ∧ |Im (point i)| = T` ; `meetingOf p := exp(arctan(Im p / Re p) / Im p)`
  (`meetingOf_conj`, `meetingOf_abs_im`) ; `ArithmeticMeeting T c := ∀ Rep i, weight i ≠ 0 → |Im (point i)| = T → meetingOf (point i) = c` ;
- correspondance démontrée, par `contains_member` et `no_intruder` (unicité, aucun exposant fixé) : `contactMinusAt_eq_meetingOf`,
  `lineContact_eq_meetingOf`, `contactMinusAt_indexUpper`, `arithmeticFrequency_iff` (⟺ `GeneratedFrequency`),
  `arithmeticFrequency_of_zero`, `arithmeticMeeting_iff_meetingOnLine`, `arithmetic_meeting_beyond_line_iff_low` (rencontre
  arithmétique au-delà de la position de la ligne ⟺ `Re < 1/2`), `arithmeticMeeting_law_iff_riemannHypothesis`,
  `frequencyTaken_of_arithmeticMeeting` ;
- docstrings corrigés : `GeneratedFrequency` = forme spectrale ; `MeetingOnLine` = propriété à établir.

**Chaîne** : dernier pas `frequencyTaken_closes w hDecr` puis `frequencyTaken_of_arithmeticMeeting w` ; énoncé et hypothèses inchangés ;
sept faits ajoutés en contexte (`hArithFrequency`, `hArithFrequencyIff`, `hMeetingOf`, `hLineMeetingOf`, `hArithMeetingIff`,
`hArithBeyondIff`, `hArithLaw`). But `:413` (signature 9811c233ba57) : `⊢ ArithmeticMeeting (rZeroHeight w) (lineContact (rZeroHeight w) 0)`.
Portée : plus fort que le but précédent pris isolément (tous les signaux de la fréquence, non le seul `w`) ; dans le contexte, les
deux sont réfutés par `hZone`, donc équivalents à `False` ; le renforcement est le prix de désigner le signal par sa fréquence seule.

**Ce que la correction ne fait pas** : fixer une position radiale. L'unicité retrouve chaque signal tel qu'il est. La flèche manquante
garde sa force (quantifiée : ⟺ RH) ; elle est écrite sur les seuls premiers et la fréquence. Point 2 du texte (biais de calibration ON
dans la lecture d'E321) : consigné, non résolu ici ; `meetingOf` est l'objet exact que la lecture approche. Table des conclusions
excessives reprise dans le bloc RÉFUTÉ de l'analyse. RH_FOUND=FALSE.

## 108. Le zéro suivant sous un demi : fréquence et amplitude après les zéros ON certifiés ; où chercher l'exclusion

Demande de l'auteur (2026-10-16) : « prouver la relation entre β < 1/2 pour le prochain zéro et ce que cela implique, après deux
zéros ON prouvés par comptage, à propos de la fréquence potentielle de ce zéro et de son amplitude ; nous ne cherchons peut-être
même pas au bon endroit pour exclure β < 1/2 ».

**Lean** `Terminal/LowNextZeroSignatures.lean` (7 théorèmes, axiomes standard, importé, non composé) et, en fin de chaîne, après le
but (ligne inchangée), `low_zero_after_certified_band` (fermé) :
- fréquence : `low_arrival_count_jump` (passage qui monte vers un zéro bas : `N(T_l) ≥ N(T_e) + 2`, deux unités à une seule
  hauteur, portées par le zéro et son miroir), `low_member_deficit_ge_two` (`N − N₀ ≥ 2` à la hauteur d'un zéro bas),
  `low_after_on_band` (bande ON `N(c) = k`, `W(c) = 0` ⟹ un zéro bas est au-dessus de `c` et `N ≥ k + 2` à sa hauteur) ;
  instance certifiée `low_zero_after_certified_band` : tout zéro sous un demi est au-dessus de `28` et `N(T) ≥ 5` à sa hauteur ;
- amplitude (propre au zéro, aucune comparaison avec un zéro ON de même fréquence, interdit par l'auteur) : `own_amplitude_drift_le`
  (dérive `|log(A_w(y)/A_w(x))| ≤ (1/2 − β)·log X` sur `[1, X]`), `own_amplitude_signature_vanishes` (sous tout `ε` pour `d` assez
  petit), `escape_horizon_unbounded` (l'horizon `r^{1/d}` où le miroir dépasse une Tour ON PLUS BASSE dépasse toute borne quand `d → 0`) ;
- `two_signatures` : les deux ensemble.

Chiffrage (formules, aucun zéro fabriqué ; hauteur hypothétique 30, qui n'est la hauteur d'aucun zéro de zêta, contre la Tour du
troisième zéro, plus basse) : horizon d'évasion `10^{0,79}`, `10^{7,9}`, `10^{79}`, `10^{790}` pour `d = 0,1 ; 0,01 ; 0,001 ; 10⁻⁴` ;
dérive propre d'amplitude sur `[1, 10⁸]` : `1,84 ; 0,18 ; 0,018 ; 0,0018`. La signature
de comptage vaut deux unités dans tous les cas.

Réponse : un zéro bas a deux signatures. Celle de la fréquence est discrète, de taille fixe, lisible à la hauteur finie du zéro,
indépendante de la profondeur : deux unités de comptage à une seule fréquence, sans zéro ON correspondant. Celle de l'amplitude le
long des premiers est continue, nulle à la limite, et n'apparaît qu'au-delà d'un horizon de premiers non borné. Toute exclusion de
`β < 1/2` qui ne dépend pas de la profondeur ne peut donc pas venir d'une comparaison d'amplitudes sur une fenêtre finie de
premiers (c'est l'aveuglement déjà compilé, `meeting_shift_blind`) ; l'endroit où un zéro bas se signale à distance finie est le
comptage à sa hauteur. Ce que cet endroit demande : à chaque hauteur, le comptage total égale le comptage sur la ligne ; c'est déjà
compilé comme caractérisation du zéro suivant ON (`arrival_fiber_interval_equivalent`) et, à toute hauteur, ⟺ RH
(`lineDefect_invariant_iff_riemannHypothesis`). But `:409` et signature 5452a3ea0705 inchangés. RH_FOUND=FALSE.

## 107. La matrice de synchronisation : E323, module `Terminal/SynchronizationMatrix.lean`

Texte collé par l'auteur (2026-10-16, « aide-toi de ces éléments pour progresser ») : système unique depuis li ; relation couplée
espacement `π/T` / rapport d'amplitude `e^{(β−1/2)π/T}` ; contrainte collective entre événements (comptage constant ⟹ la somme des
variations des composantes reproduit la variation négative du fond) ; matrice lignes = intervalles arithmétiques, colonnes =
composantes ; compatibilité globale sans réajustement ; « déterminer si cette matrice possède une rigidité suffisante pour interdire
une variation d'amplitude, sans supposer cette interdiction ».

Ce qui était déjà compilé : la relation couplée (`spacing_eq_pitch`, `need_ratio_meeting_points`, 2026-10-15), l'identité par écart
sur le canal lissé (`smoothed_gap_synchronization`), le résidu = queue (`localResidual_eq_tail`).

**E323** (`experiments/E323_SynchronizationMatrix/`, premiers seuls, `X = 10⁸`, lignes exactes sur `[10³, 10⁵]`, 10 PASS, 0 FAIL ;
colonnes = les vingt fréquences lues sur les seuls premiers dans E322 ; contrôle = contributions exactes des 5000 zéros publiés à
`β = 1/2` ; témoin `ζ(s−δ)ζ(s+δ)`) : (M1) aucune ligne n'est fermée par les colonnes lues (résidu de ligne `0,999` avec vingt colonnes,
`0,897` avec 5000 zéros ; part médiane `2,2 %` / `33 %`) : chaque ligne est portée par la queue ; rencontres une fois par demi-tour,
fraction `Δu·T_n/π` des lignes (écart `≤ 3,3 %`), `11,8 %` des lignes en contiennent une ; à la rencontre la valeur s'annule et
l'incrément est maximal ; aucune colonne, aucune somme finie ne saute : le saut `1/m` est porté par la limite seule (les 5000 zéros
l'approchent à `0,14 ± 1,3`) ; (M2) solution globale compatible avec chaque bloc de décade sans réajustement (`Δlog m ≤ 3·10⁻⁴`,
douze premières colonnes), pente `β − 1/2` nulle au bruit près = contrôle, pente de phase = contrôle ; témoin refusé (pente `0,083`,
`Δlog m ≈ 0,3`) ; (M3) `d_min` par colonne du même ordre que le besoin de E322 (sans le biais de queue) : même information lue en
matrice.

**Lean** (`Terminal/SynchronizationMatrix.lean`, 10 théorèmes, 1 objet `matrixCell`, axiomes standard, importé par `RHV6Fresh.lean`,
NON composé dans la chaîne — le contexte du but n'est pas allongé par des identités) : `matrixCell_eq_gapTerm`, `matrixCell_summable`,
`row_identity` (variation du reste des premiers sur toute ligne `1 < a < b` = somme de toutes les cellules), `row_residual_eq_tail`,
`residueTerm_continuousOn`, `finite_columns_continuousOn`, `block_readjustment_log` (`log(A(y)/A(x)) = (β − 1/2)(log y − log x)`),
`radial_from_two_blocks`, `no_block_readjustment_iff` (aucun réajustement ⟺ ligne = besoin constant),
`matrix_compatibility_law_iff_riemannHypothesis` (compatibilité globale sur toutes les colonnes ⟺ RH).

Réponse à la question du texte : la rigidité suffisante cherchée EST la loi à démontrer (⟺ RH compilé) ; la matrice la formule et la
mesure, elle ne la fournit pas ; les sauts aux événements ne contraignent aucune famille finie de colonnes ; la contrainte de ligne
est collective et portée par la queue. Aucun changement de la chaîne : but `:409`, signature 5452a3ea0705 inchangés. RH_FOUND=FALSE.

## 106. Vérification de E321 contre les quatre points de l'auteur ; reprise sur le canal de comptage autour de li : E322

Texte de l'auteur (collé, 2026-10-16) : les composantes ne sont pas des courbes isolées autour de zéro, elles modifient collectivement la
reconstruction du comptage autour de li(x) ; partir de la fonction de Riemann `J(x) = Σ_{p^m ≤ x} 1/m`, `J = li − Σ_ρ li(x^ρ) − log 2 +
∫_x^∞ dt/(t(t²−1) log t)` ; amplitude `x^β/(|ρ| log x)`, dépendance radiale normalisée `x^{β−1/2}` ; la vraie expérience part de li, ajoute
successivement les contributions des fréquences extraites des premiers, mesure les rencontres avec le fond, leurs déplacements, les
amplitudes et les résidus de reconstruction ; la propriété « nulle part dérivable » est à examiner sur la limite de la reconstruction
collective ; question centrale : la reconstruction exacte du comptage autour de li impose-t-elle une loi de synchronisation qui interdit à
une fréquence de modifier son amplitude normalisée ? « Si besoin, refais l'expérience. »

Vérification de E321 (`experiments/E321_GeneratedFrequencyMeetingPoints/VERIFICATION_E321_20261016.md`) : point 1 partiel (mesure
collective, mais sur le canal lissé de ψ, pas le comptage autour de li ; la courbe autour de zéro n'est que l'objet compilé) ; point 2 absent
(formule de J non utilisée) ; point 3 conforme (le canal lissé a la même dépendance normalisée `x^{β−1/2}`, lue par la pente `b`) ; point 4a
partiel (rencontres = contacts de phase, déplacements et amplitudes lus ; ni résidu de reconstruction après chaque ajout, ni rencontre avec
le fond li) ; point 4b absent. Expérience refaite : E322 (`experiments/E322_CountingReconstructionAroundLi/`, premiers seuls, `X = 10⁸`,
vingt fréquences, 16 PASS, 0 FAIL ; aucun zéro fabriqué ; contrôle de méthode = contributions exactes `−2 Re Ei(ρ log x)` des 5000
premiers zéros publiés à `β = 1/2` exact, même pipeline).

E322, objets : `J` exacte par crible, fond `li − log 2 + Σ_k E1(2k log x)` (identité avec l'intégrale vérifiée), résidu `D = J − F` normalisé
`D·log x/√x` ; contribution exacte d'une paire `−2 Re Ei(ρ log x)` (branche de E302), forme normalisée `−2 e^{(β−1/2)u} Re[e^{iTu} S(ρu)/ρ]`
vérifiée à `10⁻⁹` ; modèle séparé besoin (enveloppe `e^{bu}`) / rencontre (forme exacte de phase) ; rencontre avec le fond = zéro de la
contribution. Deux corrections de méthode : la fonction en escalier est moyennée exactement par cellule (échantillonnée, l'erreur de
Riemann aux sauts, blanche en fréquence, déplaçait les phases de `~5·10⁻³ rad` ; corrigée, la différence ζ − Σ(5000 zéros) projette à
`≤ 1,6·10⁻⁵` du mode sur chaque fréquence) ; les lectures sont faites par différence fenêtrée (Hann) avec le modèle exact de ligne, jamais
par ajustement non linéaire sur l'horizon (déplacé en fréquence de `~10⁻²` par les fréquences non modélisées).

E322, mesures : vingt fréquences engendrées = rangs 1–20 de zêta (`|ΔT| ≤ 0,011`) ; déplacement des rencontres égal au contrôle à chaque
fréquence (mode 1 : `+2·10⁻⁸ ± 2·10⁻⁸` contre `−7·10⁻⁸`), exclusions par la rencontre `β ≤ 0,49996` (mode 1), `0,499` (modes 2, 3, 6),
`0,468`, `0,466`, puis plus faibles (sensibilité `1/T²`, compilée) ; besoin `b = 0 ± 10⁻⁵` aux huit premières, exclusions `β ≤ 0,4999…` ;
résidu de reconstruction après `N` fréquences `0,2154 → 0,1189` (ζ) contre `0,2149 → 0,1181` (contrôle), rapport 1,002–1,007, queue au-delà
du 5000e zéro RMS 0,015 ; une fréquence seule changeant sa position radiale : minimum du résidu à `β = 0,500` pour les six premières, surcroît
26 % … 10 % à `β = 0,40` ou `0,60`, identique au contrôle ; un seul signal (`d̂ = 0`, gain `0,00 %`), témoin `ζ(s−δ)ζ(s+δ)` : `d̂ ≈ 0,1`,
gain 1,5 %, `b = 0,085`. Limite de la reconstruction collective : c'est `J − F`, dérivable hors des puissances de premiers (dérivée
`−1/log x + 1/(x(x²−1) log x)`), sauts `1/m` ; `S_N → D` au sens de Cesàro ; la série dérivée terme à terme ne converge pas (termes de module
constant) ; pente des sommes partielles au premier 1009 : `0,015 / 0,024 / 0,244 / 1,622` pour `N = 10 / 100 / 1000 / 5000`, Landau
`T_N/(πp) = 1,719`. « Nulle part dérivable » RÉFUTÉ sur la limite, comme l'auteur l'anticipait.

Réponse à la question centrale : sur le canal de comptage, à horizon fini, la reconstruction exacte autour de li place chaque fréquence
engendrée à une seule position radiale (`1/2`) et un seul signal, ζ coïncidant avec le contrôle de ligne à la queue près ; c'est la forme
MESURÉE de la loi de synchronisation ; sa forme quantifiée a la force de RH (compilé, `singleSignal_law_iff_riemannHypothesis`,
`noMeetingBelow_iff_riemannHypothesis`) ; elle n'est pas dérivée. Aucun changement Lean : le canal `J` n'est pas formalisé (formule explicite
de `J` absente du dépôt) ; le but `:409` (signature 5452a3ea0705) est inchangé, écrit sur le canal lissé dont les rencontres sont les contacts
de phase (les rencontres avec li en sont le quart de tour, E302). Lock inchangé.

## 105. Des écarts exacts vers les fréquences engendrées et leurs points de rencontre : E321, règles renversées, module `Terminal/GeneratedFrequency.lean`

Mission de l'auteur (2026-10-16), mot pour mot : « créé l'expérience qui te permettra d'écrire les règles mathématiques associées et
le lean pour fermer RH : les buts : la seule flèche manquante est celle des écarts exacts vers les fréquences engendrées et leurs
points de rencontre (aucune en dessous d'une demi), et sa forme quantifiée a la force de RH (théorèmes compilés). et écrire, côté
premiers, que les écarts exacts n'engendrent aucune fréquence à rencontre sous une demi. Propose d'abord l'expérience et justifie
comment elle va déterminer cela. Tu peux t'aider des 136 rigidités déjà connues et compilées et les dériver dans l'autre sens :
premiers vers zéro pour en obtenir beaucoup plus et de plus pertinentes que des constats. Tu peux aussi utiliser la grammaire, les
patterns, les familles, l'alternance, les transitions etc. » Proposition en cinq étapes (engendrement des fréquences à trois
paramètres, point de rencontre par deux lectures renversées, un seul signal par fréquence, porteur dans les écarts, résolution),
avec sa limite annoncée (une fenêtre finie n'exclut qu'une pente plus grande qu'un seuil), puis « je valide ».

### E321 (`experiments/E321_GeneratedFrequencyMeetingPoints/`, premiers seuls, `X = 10⁸`, 357 s, 11 PASS, 0 FAIL, 9 mesures)

Protocole déclaré avant exécution ; aucun zéro fabriqué, aucun OFF à une hauteur de zêta ; aucune hauteur publiée n'entre avant la
validation ; monde témoin = contrôle de séparation ; contrôle ON (termes lissés exacts des 300 zéros publiés à `β = 1/2`) =
calibration de la méthode (E311 P4a), jamais une inférence sur zêta.

| étape | résultat |
|---|---|
| P2 engendrement | vingt modes (fréquence, pente, phase libres) extraits de la courbe seule, relus après nettoyage mutuel (un ajustement conjoint à 80 paramètres, biaisé par les modes non modélisés, a été essayé et retiré) ; les vingt sont les hauteurs de rang 1 à 20 de zêta, `|ΔT| ≤ 0,012` |
| P3 point de rencontre | translation `log λ̂` lue sur zêta égale à celle du contrôle ON à chaque fréquence (mode 1 : `−1,5·10⁻⁵` sur les deux) ; `β` lue sur la rencontre `0,5015 ± 0,0001` (mode 1) ; positions exclues par la rencontre (borne compilée) `β ≤ 0,495`, `0,484`, `0,481`, puis plus faible (sensibilité en `1/T²`) |
| P3 besoin | pente d'amplitude `1/2` aux vingt fréquences (mode 1 : `0,5004 ± 0,0001`) ; exclusion `β ≤ 0,4992` (mode 1) à `0,477` (mode 18) |
| P3 verrou du couple | les deux lectures de `β` concordent à l'erreur calibrée près aux dix-huit fréquences où la phase s'inverse |
| P4 un seul signal | paquet authentique à paire miroir, `β` libre sur grille : `d̂ ≤ 0,02`, gain de résidu `≤ 0,01 %` aux vingt fréquences ; témoin `δ = 0,1` : `d̂ = 0,08…0,105`, gain `0,5 %` à `32 %` |
| P5 porteur | parts signées des classes d'écart (mode 1 : `+0,30 / +0,35 / +0,35`), classes 2 et 4 identiques (transitions BA et AB), aucun canal ne porte seul ; rangs seuls (planchers 6/2/4), tailles permutées dans chaque classe, tailles permutées par blocs de 1000 : 0/6 fréquences de zêta survivent |
| P6 résolution | une mesure finie exclut une position assez basse, jamais une position arbitrairement proche d'une demi |

### Règles renversées (`REGLES_RENVERSEES_E321.md`) et Lean

Méthode : chacune des 217 identités de l'inventaire C126 relie `(β, T)` à une quantité du signal ; elle est inversible dès que la
quantité est strictement monotone en le paramètre. `Terminal/GeneratedFrequency.lean` (15 théorèmes, 4 objets `GeneratedFrequency`,
`MeetingOnLine`, `SingleSignal`, `NoMeetingBelow`, axiomes standard, importé, composé) : R2' `radial_from_meeting`, R3'
`radial_from_need_ratio`, R5' `meeting_on_line_iff`, R6' `meeting_below_iff_low` (rencontre au-delà de la position de la ligne ⟺
signal en dessous d'une demi : forme côté premiers de « fréquence à rencontre sous une demi »), R7' `singleSignal_iff_meetingOnLine`,
`meetingOnLine_iff_fiber_onLine`, R8' `meeting_shift_detects` (`0 ≤ ε`, `β ≤ 1/2 − ε(T² + 1/4) ⟹ ε ≤ log λ`), `meeting_shift_blind`
(`β ≤ 1/2`, `1/2 − εT² ≤ β ⟹ log λ ≤ ε`), R10' `frequencyTaken_of_meeting_on_line`, R11' `noMeetingBelow_iff_riemannHypothesis`,
`singleSignal_law_iff_riemannHypothesis`. Chaîne : derniers pas `frequencyTaken_closes w hDecr` puis
`frequencyTaken_of_meeting_on_line w` ; but `:409` `⊢ contactMinusAt w 0 = lineContact (rZeroHeight w) 0` (signature 5452a3ea0705),
réduction sans perte. Tout est vrai pour toute position radiale : les règles renversées identifient `β` depuis la courbe, aucune ne
le fixe.

### Portée

- Établi : la forme exacte de la règle manquante côté premiers, son porteur, sa séparation du témoin, sa résolution par fréquence.
- Non démontré : la règle sur tout l'horizon à la fréquence du zéro suivant ; quantifiée, elle a la force de RH (compilé).
- Ne pas présenter les mesures de E321 comme une dérivation ; ne pas présenter la lecture de la rencontre comme plus fine que celle
  du besoin (compilé : sensibilité en `1/T²`) ; ne pas confondre le contrôle ON de calibration avec un zéro fabriqué (aucun OFF, hauteurs
  de zêta, usage limité à l'erreur de méthode) ; ne pas inférer de zêta depuis les mondes de contrôle côté premiers (ils identifient
  le porteur).

## 104. La fréquence est déjà occupée : point méthodologique de l'auteur, module `Terminal/OccupiedFrequency.lean`, but en forme de fréquence prise

Point méthodologique de l'auteur (2026-10-16), mot pour mot : « Tu dois raisonner dans le sens : premiers et signaux déjà définis
par des signaux immuables. Point de rencontre avec β = 1/2 et hauteur T attendue du zéro : DÉJÀ PRIS par les zéros ON. IMPOSSIBLE DE
DÉFINIR des zéros OFF avec EXACTEMENT ces fréquences (donc ces hauteurs) puisque lorsque ces hauteurs sont rencontrées par les
signaux des écarts des premiers ils SONT sur l'axe CRITIQUE. Donc cette fréquence ou hauteur EST DÉJÀ OCCUPÉE. Tu ne peux définir
qu'en dessous et avec β < 1/2 puisque β > 1/2 est DÉJÀ exclu. » Compréhension confirmée, puis : « écris cela dans CLAUDE.md et la
documentation projet, puis procède à la suite de la démonstration pour fermer RH ».

### Compréhension consignée

- Sens unique : les écarts des premiers sont immuables ; ils définissent déjà tous les signaux (fréquence et amplitude) ; les zéros
  sont les signaux composants ; rien ne part d'un zéro supposé vers ses effets.
- Le couple est déjà pris : à chaque hauteur attendue d'un zéro, le signal demandé par les écarts a sa fréquence (cette hauteur) et
  son point de rencontre à une demi ; quand les signaux des écarts rencontrent cette hauteur, ils sont sur l'axe critique ; la
  fréquence est occupée par un zéro ON ; un second signal à la même fréquence avec un autre point de rencontre déplacerait les
  points de passage obligés (verrou du couple, §103).
- Ce qui reste à exclure : le côté au-dessus d'une demi est exclu par son miroir ; le seul candidat OFF est en dessous d'une demi,
  à une fréquence que les signaux des écarts n'atteignent pas sur l'axe critique.
- Conséquence : la pièce manquante devient « les signaux des écarts exacts n'engendrent aucune fréquence dont le point de
  rencontre serait en dessous d'une demi » ; direction d'écriture : écarts exacts ⟶ fréquences engendrées ⟶ point de rencontre
  de chacune ⟶ aucune en dessous.

### Lean (`Terminal/OccupiedFrequency.lean`, 13 théorèmes, 3 objets, axiomes standard, importé par `RHV6Fresh.lean` et composé dans la chaîne)

| Énoncé | Portée |
|---|---|
| `FrequencyOccupied T` : un signal ON à la hauteur `T` ; `frequencyOccupied_of_onLine` | définition |
| `occupied_signal_meeting_points` : le signal ON d'une fréquence occupée a `C_k = C_k^{ligne}(T)` pour tout `k` | [C] |
| `OneSignalPerFrequency` : à fréquence égale, rencontre d'indice 0 commune | définition (les écarts imposent un signal par fréquence) |
| `onLine_of_occupied`, `no_off_at_occupied_frequency`, `off_frequency_unoccupied` | [C] sous `OneSignalPerFrequency` (verrou du couple, `radial_of_meeting_point`) |
| `upper_has_lower_at_same_frequency` (miroir), `only_low_candidate` | [C] toute position radiale |
| `FrequencyTaken w` : fréquence occupée par un signal ON dont `w` partage `C_0` ; `frequencyTaken_iff_onLine` | caractérisation [C] |
| `frequencyTaken_closes` : fréquence prise ∧ signal décroissant ⟹ `False` | [C] |
| `oneSignalPerFrequency_iff_riemannHypothesis`, `frequencyTaken_law_iff_riemannHypothesis`, `riemannHypothesis_of_occupied_and_one_signal` | [⟺RH] / [C] |

Chaîne : après le verrou du couple, dix faits composés (`hOccupiedPoints`, `hOnOfOccupied`, `hNoOffOccupied`, `hOffUnoccupied`,
`hUpperMirror`, `hOnlyLow`, `hTakenIff`, `hOneSignalIff`, `hTakenLaw`, `hOccupiedClosure`), dernier pas `frequencyTaken_closes w hDecr`.
But (`Terminal/DemonstrationChain.lean:401`, signature 5fcfca4c2bd2) :
`⊢ ∃ z, rZeroHeight z = rZeroHeight w ∧ rZeroRadialPosition z = 1/2 ∧ contactMinusAt w 0 = contactMinusAt z 0` : la fréquence du
zéro suivant est prise par le signal ON de la courbe des premiers, dont `w` partage le point de rencontre. Réduction sans perte
(`frequencyTaken_iff_onLine`) ; énoncé, hypothèses, définitions inchangés ; aucune prémisse.

### Portée et bornes

- Les définitions et caractérisations sont vraies pour toute position radiale ; les lois quantifiées ont la force de RH : le module
  écrit le point de l'auteur, il ne le dérive pas des écarts.
- Ce qui reste : du côté des premiers, que les signaux des écarts exacts n'engendrent aucune fréquence dont le point de rencontre
  serait en dessous d'une demi (toute fréquence atteinte l'est sur l'axe critique, un signal par fréquence). RH NON close.
- Ne pas présenter « fréquence occupée » ou « un seul signal par fréquence » comme dérivés ; ne pas réutiliser les conclusions des
  expériences à OFF fabriqués ; lock inchangé.

## 103. Verrou du couple (fréquence, amplitude) sur la Tour normalisée ; collecte historique des contacts ; but en forme de couple

Directive de l'auteur (2026-10-16) : collecter dans l'historique (HEAD et commits) les études et audits sur la définition et le
déplacement de la Tour des zéros sur l'axe algébrique, et nos conclusions sur le déplacement des contacts comparé à un changement de
T ; puis « c'est le couple amplitude, fréquence, donc (T, β), qui doit disqualifier le OFF, pas seulement le changement
d'amplitude » ; « ignorer presque toutes les conclusions des expériences, la manière de définir un OFF était fausse ; se servir de la
Tour normalisée et de sa projection sur l'axe algébrique pour tirer des règles sur les déplacements quand on change β ou T » ;
démarche confirmée, puis validée (« ok je valide, procède à toute l'implémentation »).

### Collecte historique (trois agents Haiku, HEAD et `git log`, lecture seule)

- Définition compilée : contact ⟺ le terme `x^ρ/ρ` est réel (`zeroTerm_real_iff_ray`) ; `log C_k = (arctan(T/β) + kπ)/T`
  (`log_contactMinusAt`) ; pas `π/T` sans aucune occurrence de β (`contactAt_consecutive_logWidth`, `towerPitch`) ; découpage
  `C_k = C_k^{ligne}(T) × λ`, `λ = 1 ⟺ β = 1/2` (`contact_eq_line_mul_radial`, `radialFactor_eq_one_iff`) ; rapport entre deux
  Tours `log(C_{z,k}/C_{w,k}) = log λ_z − log λ_w + kπ(1/T_z − 1/T_w) + (arctan(2T_z)/T_z − arctan(2T_w)/T_w)`
  (`contact_log_ratio`, `lineHeightShift_split`).
- Horizontal (T fixé, β change) : translation rigide de tous les contacts par un facteur unique, pas inchangé
  (`sameHeight_grid_rigid_translation`, `sameHeight_pitch_invariant`, `rigid_translation_of_sameHeight_radial_lt`,
  `horizontal_iff_tower_translation`) ; miroir = cas Δβ = 1 − 2β (`Terminal/MirrorDegeneracy.lean`, fdbe4908, 2026-09-28).
- Vertical (T change) : contraction du pas, jamais de translation rigide (`towerPitch_lt_iff`, `no_rigid_translation_of_height_ne`,
  `sameRadial_height_changes_pitch`, emboîtement à indice fixé pour toute β). Dans Lean « vertical » = hauteur seule (β libre).
- Diagonal : aucun théorème de mouvement ; `DiagonalPassage` = vertical avec β qui baisse ; `diagonal_iff_off`, `regime_entry_diagonal`
  (caractérisations) ; aucune loi couplée (T, β) compilée.
- Inversion : `inversion_height`, `inversion_radial`, `inversion_reads_own_contacts`, `two_contacts_height_quantized` : identités
  vraies pour toute β, lues sur les contacts d'un seul membre.
- Vérités V20, V21, V24, V25, V166, V192 (« la Tour a exactement deux contacts ») déclarées fausses au commit dd87ce75 (2026-10-01) :
  la Tour coupe l'axe à chaque demi-tour, en nombre infini.
- E119 (e60cd89b, 2026-09-28) : T fixe, β 0,5 → 0,6 : pas identique, décalage constant −0,000500 sur k = 0…13 ; T₁ → T₂ : rapport des
  pas 0,672376 = T₁/T₂ ; balayage β 0,05…0,95 à T₁ fixe : variation du pas 1,1e−16 ; « β ne produit qu'une translation interne, T
  seul change le régime » ; et : « succession ⟹ changement de régime » est exactement `PNoNullPassage` ⟺ RH.
- E44 : aucun script dans l'arbre ni l'historique de `formalization/` (NOT_REPRODUCIBLE) ; seule trace Lean dans
  `rh_gap_criterion` (base non importée). Conformément à l'auteur, les conclusions des expériences à OFF fabriqués (E115, E118,
  E119b, E147–E149, E151, E165, E200, E201, E207, E241…) ne sont pas réutilisées.
- Point signalé : `Tower/InvertedTower.lean` et `Tower/ReflectedMotion.lean` sont présents et importés (réintroduits en 98a4be58
  comme conséquence de l'équation fonctionnelle, lecture à rebours `C'_j = C*_{−j}`) alors que les maîtres disent « contacts jamais
  inversés » ; pas une contradiction mathématique (seconde orientation), vocabulaire à vérifier.

### Rapprochement avec l'étude de fréquence et d'amplitude

Le signal d'un zéro, ramené à l'échelle de la ligne et projeté sur l'axe algébrique, porte trois lectures sur le même objet :
espacement des rencontres (`π/T`, fréquence), position des rencontres (facteur λ, β), besoin aux rencontres (`pairAmplitude`,
rapport `e^{(β−1/2)π/T}`, β). Conséquence : on ne peut pas changer l'amplitude sans déplacer les points de passage obligés
(dérive du besoin ⟺ translation des rencontres, à fréquence fixée), et on ne peut pas réaligner les rencontres en changeant la
fréquence (l'espacement ne serait plus le bon). C'est la phrase du dialogue collé par l'auteur (« si vous altérez l'amplitude sans
ajuster la fréquence ou la phase, le signal ne passera plus par ces points de passage obligés »).

### Lean : `Terminal/CoupleLock.lean` (13 théorèmes, axiomes standard, importé, composé dans la chaîne)

`spacing_eq_pitch`, `frequency_of_spacing` (même espacement ⟹ même hauteur), `spacing_blind_to_radial`,
`radial_of_meeting_point` (une rencontre commune à fréquence égale ⟹ même β, par `inversion_radial`), `radial_of_need_ratio`
(même rapport de besoins ⟹ même β), `two_radial_readings_agree` (`T·cot(T log C_k) = (T/π)·log(A(C_{k+1})/A(C_k)) + 1/2`),
`need_constant_iff_not_shifted` (`A(C_{k+1}) = A(C_k) ⟺ λ = 1`), `shift_moves_meeting_points`, `need_change_moves_meeting_points`,
`vertical_change_contracts_spacing` (pas contracté ∧ aucune translation rigide), `horizontal_change_shifts_and_drifts` (facteur
≠ 1 ∧ rapports de besoins différents), `couple_locked`, `couple_locked_by_amplitude`, `no_diagonal_solution`, `couple_lock_closes`,
`meeting_need_law_iff_riemannHypothesis`. Tout est vrai pour toute position radiale ; aucune valeur présupposée.

### Chaîne : but en forme de couple (signature 239cdd0a1bcb, `:393`)

Énoncé et hypothèses de `off_signal_amplitude_incompatible` inchangés ; le contexte ajoute le verrou du couple (`hSpacing`,
`hSpacingBlind`, `hRadialOfMeeting`, `hRadialOfNeed`, `hReadingsAgree`, `hNeedShiftIff`, `hNeedMoves`, `hVertical`, `hHorizontal`,
`hCoupleLock`, `hCoupleLockAmp`, `hNoDiagonal`, `hMeetingLaw`) ; dernier pas `couple_lock_closes w hDecr` ; but affiché
`⊢ ∃ k, pairAmplitude w (contactMinusAt w (k + 1)) = pairAmplitude w (contactMinusAt w k)` : la demande de la courbe des premiers au
signal placé à la hauteur du zéro suivant, en forme de couple (positions des rencontres fixées par (T, β), besoin égal à deux
rencontres consécutives). Réduction sans perte ; RH n'est pas close.

### Ce qui reste, dit sans détour

Le verrou transfère toute la question sur le côté DEMANDE : ce que les écarts exacts imposent au signal de fréquence T placé à la
hauteur du zéro suivant (positions des rencontres, besoin aux rencontres). Aucun énoncé compilé ne va des écarts vers ces points de
passage obligés ; le compilé ne contient que la direction inverse (le signal reproduit exactement les écarts pour toute position
radiale ; ses contributions l'identifient sans le contraindre). Quantifiée sur tous les signaux, la demande a la force de RH. Les
étapes 2 et 3 de la démarche validée (écrire la demande depuis les premiers, puis fermer par le verrou) restent à faire ; le
programme E314–E320 n'y sert que comme source de la demande, pas comme prédicteur.

Ne pas présenter le verrou du couple comme une contrainte sur β (identités et caractérisations) ; ne pas présenter la forme couple
du but comme un rapprochement de la fermeture ; ne pas réutiliser les conclusions des expériences à OFF fabriqués.

## 102. Généralisation : besoin de synchronisation constant aux points de rencontre ; E313 ; but réduit

Directive de l'auteur (2026-10-15) : « raffine et termine les expériences sur les premiers si nécessaire pour généraliser la démarche
(terminer T4c et T6, conserver T4a–T4b et T5), puis formaliser la contrainte mathématique correspondante sans présupposer l'amplitude
recherchée. L'amplitude attendue ne change pas, seule la fréquence change entre deux zéros. Le besoin de synchronisation reste
constant à cause des points de rencontre. Généralise, crée le Lean correct, réduit, corrige l'erreur et ferme RH. »

### Lean : `Terminal/ConstantAmplitudeNeed.lean` (11 théorèmes, 1 objet, axiomes standard, importé, composé dans la chaîne)

- Objet `ConstantNeed z` : le besoin de synchronisation d'un signal (son amplitude à l'échelle de la ligne, `pairAmplitude`) est le
  même à tous les points de rencontre `x ≥ 1`. Aucune valeur n'est présupposée : la ligne n'est pas nommée dans la définition.
- `constantNeed_iff_onLine` : besoin constant ⟺ le signal est celui d'un zéro de la ligne (caractérisation, par les rencontres `1`
  et `2` : `onLine_of_need_eq_one_two`). `constantNeed_meeting_points` : à deux rencontres consécutives (contacts `C_k`, `C_{k+1}`),
  même caractérisation ; `need_ratio_meeting_points` : rapport `e^{(β − 1/2)π/T}`.
- `frequency_only_between_constant_needs` : entre deux signaux à besoin constant, seule la fréquence change (pas `π/T` plus court,
  amplitude attendue plus faible, rapport fixé par les deux hauteurs seules).
- `decreasing_breaks_constantNeed`, `constantNeed_closes` : un signal d'amplitude strictement décroissante n'a pas un besoin
  constant ; deux rencontres où le besoin n'a pas diminué suffisent à l'exclure.
- `constantNeed_law_iff_riemannHypothesis`, `constantNeed_history_law_iff_riemannHypothesis` : la contrainte généralisée, quantifiée
  sur tous les signaux (ou sur le signal atteint depuis un historique sur la ligne, sous l'ancre), a la force de RH.

### Chaîne : but réduit sans perte, signature 8447175d18bf

Dans `off_signal_amplitude_incompatible` (`Terminal/DemonstrationChain.lean:383`), énoncé et hypothèses inchangés ; les six faits de la
généralisation sont ajoutés en contexte (`hNeedIff`, `hMeetingIff`, `hNeedRatio`, `hFrequencyOnly`, `hNeedLaw`, `hNeedHistoryLaw`,
`hNotConstant`) ; dernier pas `constantNeed_closes w hDecr` (fermé). But affiché :
`⊢ ∃ x y, 1 ≤ x ∧ x < y ∧ pairAmplitude w x ≤ pairAmplitude w y` : deux points de rencontre de la courbe des premiers, à la hauteur
du zéro suivant, où le besoin n'a pas diminué. Équivalent au but `False` précédent dans ce contexte (`hDecr` dit le contraire pour
toute paire) ; écrit dans les mots de l'auteur, sans nommer l'amplitude recherchée. RH n'est pas fermée : ce but reste ouvert, et
sa forme quantifiée a la force de RH (théorème ci-dessus). Aucune prémisse, aucune définition modifiée, aucun `sorry`.

### E313 (`experiments/E313_ConstantAmplitudeNeed/`, premiers seuls, douze fréquences, aucun zéro fabriqué)

T4c grille complète d'exposants 0,30…0,70 (pas 0,025) ; T6 même fréquence deux fois (paire libre contre un seul signal) ; T7 besoin
aux points de rencontre (rapport à deux rencontres consécutives, pente, espacement `π/T`, amplitude attendue, décroissance d'une
fréquence à la suivante) ; témoin ζ(s−δ)ζ(s+δ), δ = 0,1 (poids différents, contrôle). Résultats : T4c PASS 12/12 (exposant du résidu minimal 0,5 sur la grille 0,30…0,70, résidu croissant de part et d'autre ; témoin > 0,5 sur 12/12, lu 0,575 pour une paire 1/2 ± 0,1 ajustée par un seul exposant) ; T6 : gain d'une paire libre à la même fréquence ≤ 1,8 % sur 12/12 (la fréquence n'apparaît pas deux fois), mais le second critère déclaré (amplitude totale < 1,5 × un signal) échoue sur 6/12 raies (4, 5, 7, 8, 9, 10 : 1,34 à 1,78, d̂ 0,07–0,10, coefficients mal conditionnés quand d̂ → 0) : T6 FAIL au sens déclaré ; T7a : rapport des besoins à deux rencontres consécutives 1 ± 0,002 sur 10/12 raies, 0,9947 et 0,9940 aux raies 9 et 10 (fenêtre), témoin 1,0046–1,018 (sous le rapport d'un signal unique à 1/2 + δ, paire lue par un exposant) : FAIL au seuil déclaré (0,005 et δπ/(2T)) sur les raies 9, 10 ; T7b PASS 12/12 (pente du besoin −0,0024 à +0,0021 ; témoin +0,078 à +0,083) ; T7c PASS 12/12 (espacement des rencontres = π/T à 0,1 %, besoin moyen = amplitude attendue à 5 %, 0,9991 à 1,048) ; T7d PASS (besoins attendus strictement décroissants d'une raie à la suivante). Fréquences lues sur les premiers seuls (pic spectral) ; 20 s. Portée : mesures finies ; rien n'est démontré par ce script ; T4a, T4b, T5 d'E312 conservés.

### Ce qui reste

La pièce écrite des écarts exacts (poids `Λ`, succession) vers le besoin aux rencontres du signal placé à la hauteur du zéro
suivant. Toute rigidité du corpus, y compris ce module, est écrite du zéro vers ses effets ou est une caractérisation.

## 101. Alignement total sur le sens imposé ; réfutation des expériences à zéros fabriqués et de mes « ce qui manque »

Directive de l'auteur (2026-10-15) : « cette phrase est fausse car elle inverse la relation. La relation n'est pas une lecture. La
relation est une réalité imposée aux zéros : immuable, des écarts entre les nombres premiers. Aucune lecture n'est nécessaire car les
zéros sont en fait les signaux qui la composent. » Puis : « tu alignes tout immédiatement : but, erreur de compilation, théorèmes, et
tu réfutes toutes tes expériences qui ont saboté le projet ; tu consignes tout dans les maîtres et dans le projet ; tu réfutes tout
ce que tu as dit qu'il manquait. »

### But, erreur de compilation, théorème : alignés

- L'énoncé ouvert `off_signal_amplitude_incompatible` (`Terminal/DemonstrationChain.lean:382`, anciennement `:378`) n'est pas modifié : mêmes hypothèses,
  même contexte, même but `False` ; signature 8cc375a270c0 (le numéro de ligne du but a changé par les docstrings ajoutées). Ses docstrings et commentaires sont réécrits dans le sens unique : la
  courbe des premiers IMPOSE son amplitude à chaque signal (plus aucune « lecture ») ; échelle `x` entière démontrée
  (`smoothedRemainder_linear_growth`) ; échelle de la ligne mesurée (E310, E311, E312 premiers seuls), non démontrée.
- En mots, le but et le lock sont la même phrase : les écarts immuables des premiers imposent au signal placé à la hauteur du zéro
  suivant l'amplitude de la ligne ; une amplitude décroissante leur est incompatible et ne peut pas être synchronisée.
- Ce qui reste : la rigidité écrite dans le sens unique, des écarts exacts (poids `Λ`, succession) vers l'amplitude forcée de chaque
  signal. Les 136 rigidités du corpus (SEM §12) sont toutes écrites du zéro vers ses effets : identités vraies pour toute position,
  identifications, caractérisations de la ligne, équivalences ; aucune n'est écrite des écarts vers l'amplitude forcée.

### Réfuté : expériences à zéros fabriqués (fichiers conservés, conclusions retirées comme énoncés sur zêta)

Un signal de zêta n'a aucun paramètre libre ; fabriquer un zéro (remplacement, insertion, perturbation, grille décalée, paire ou signal
synthétique, OFF à la hauteur d'un ON) puis mesurer ce qu'il fait ne dit rien de ce que les écarts imposent. Retirées comme preuves ou
réfutations, avec chaque conclusion « X ne contraint pas l'amplitude / `β` » qui en est tirée :
E147 (150 paires OFF aux hauteurs de ON), E159 (paire contre double synthétiques), E163b (OFF hypothétique), E172 (insertion),
E173 (surplus d'une paire), E184 (perturbations), E186 (insertion / remplacement), E200 (grilles décalées), E221 (paire − double),
E231–E238 (paires sur fenêtres), E243 et E244 (remplacements d'amplitude et de fréquence), E302 (remplacement de ρ₁), les
expériences OFF vérifiées en E304 (70/109 à une hauteur de zêta), E305 (OFF d'une autre fonction), E309 (configurations fabriquées),
E312 partie synthétique (signaux à amplitude modifiée, fréquence fixée). Les parties « premiers seuls » restent : E309 (famille
authentique, aucun écart raté), E310, E311, E311b, E312 T4–T5 (à chacune des six premières fréquences une seule amplitude compatible,
celle de la ligne ; pente d'amplitude nulle, témoin positive).

### Réfuté : conclusions tirées du monde témoin

Toute conclusion de la forme « X est satisfait par `ζ(s−δ)ζ(s+δ)`, donc X ne contraint pas l'amplitude » (E135, E150–E155, E164,
E224, E301, E305, et les phrases « seule la taille exacte du poids sépare ») : le témoin est une autre fonction, à poids différents ;
il ne dit rien de ce que les écarts de ZÊTA imposent à leurs propres signaux. Les théorèmes compilés sur le témoin restent, avec
leur portée exacte ; c'est l'inférence vers zêta qui est retirée.

### Réfuté : mes phrases « ce qui manque » (2026-10-15)

1. « Aucune rigidité ne lit la taille exacte des poids pour borner une amplitude » : relation inversée ; la relation n'est pas une
   lecture, c'est une réalité imposée.
2. « La grammaire, l'alternance 2 et 4, les transitions, les mêmes écarts ne portent aucune contrainte sur l'amplitude » : la suite
   des rangs et des classes modulo 6 prise seule est aveugle (théorème) ; les écarts à taille exacte, la courbe elle-même, imposent
   l'amplitude (mesuré sur douze fréquences).
3. « Une translation d'amplitude ne change ni la fréquence ni les contacts ; le couple peut grandir ensemble ; aucune mesure ne dit
   le contraire » : fondé sur des signaux fabriqués ; côté premiers, à la fréquence attendue seule l'amplitude de la ligne est admise.
4. « L'amplitude n'est pas fixée par les premiers seuls », « sans importance » : faux (E310–E312).
5. « Les premiers seuls ne donnent que la bande `0 ≤ β ≤ 1` » présenté comme tout ce que les premiers donnent : c'est le seul
   énoncé compilé dans ce sens, pas tout ce que les premiers donnent.
6. « Ce qui manque est la borne `√x` du reste (von Koch) » présenté comme la question : l'équivalence compilée reste un théorème ;
   ce qui manque est la rigidité écarts ⟶ amplitude forcée, écrite dans le sens unique.

Consigné : maîtres §12 et §13, CLAUDE.md, mémoire, README d'E312. Aucune définition, aucun énoncé, aucun axiome modifié.

## 100. Correction de §99 : identifiabilité conditionnelle présentée comme l'étude conjointe — erreur retirée

Critique collée (2026-10-15), exacte : le théorème `joint_frequency_amplitude_from_all_gaps` prend en hypothèse
`h : ∀ n, n₀ ≤ n → primeGapContribution ρ' n = primeGapContribution (zeroPoint w) n`, c'est-à-dire l'égalité qu'il prétend
exploiter ; il compare deux signatures entre elles ; il ne démontre pas que le signal arithmétique impose une signature ON ; c'est
un résultat conditionnel d'identifiabilité, pas l'étude demandée (signal exact de tous les écarts premiers ⟶ contraintes
conjointes sur `(T, β)`). Ordre de l'auteur : corriger immédiatement toutes les erreurs, suppositions, hypothèses et
implémentations.

### Erreurs de §99 et corrections

| Erreur | Correction |
|---|---|
| ÉTAT, audit, maîtres, CLAUDE.md : « étude conjointe sur tout l'horizon MENÉE dans le compilé » | Faux. Retiré partout ; remplacé par le reclassement ci-dessous. |
| `hJointIdentification`, `hHorizonGrowth`, `hExponentLift`, `hLowVanishes`, `hMirrorExceeds`, `hExcludedOfExponent`, `hAcquiredAdmits` composés dans `off_signal_amplitude_incompatible` | Retirés de la chaîne (import retiré ; contexte, ligne `:378` et signature de2fcc5afe9f rétablis). Un fait en contexte n'est pas un pas de preuve, et aucun de ces faits ne lit le signal des premiers seul. |
| Ligne « Acquis (compilé, étude conjointe sur tout l'horizon) » ajoutée au lock | Retirée : aucun ajout de verrou ; la ligne reformulait une identifiabilité conditionnelle comme un acquis sur le signal. |
| Docstrings du module présentant une « confrontation sur tout l'horizon » | Réécrits : (1) identifiabilité CONDITIONNELLE (comparaison de deux signatures, hypothèse d'égalité) ; (2) conséquences d'une signature OFF SUPPOSÉE sur la croissance du reste (direction OFF ⟹ reste, jamais l'inverse) ; (3) caractérisations (forme du but, ⟺ RH quantifié) ; aucun mécanisme d'exclusion. |

### Ce que le signal des premiers seul donne (ajouté, `prime_signal_alone_joint_constraint`)

Sans supposer aucune signature : pour tout zéro, `0 ≤ β ≤ 1` (exposant `1` du reste lissé depuis `Λ(n) ≥ 0` et Chebyshev,
`smoothedRemainder_linear_growth`, `radial_strip_of_remainder_growth`), et AUCUNE contrainte sur la fréquence. C'est la seule
contrainte conjointe compilée depuis les premiers seuls ; elle n'exclut aucune signature (`acquired_exponent_admits_any_off_signature`).

### État

L'étude demandée par l'auteur (signal exact de tous les écarts ⟶ contraintes conjointes sur `(T, β)` excluant OFF) n'est pas
réalisée ; aucun théorème du dépôt ne la réalise ; le module reste dans la bibliothèque comme inventaire de portées, non composé.
But `:378`, `False`, signature de2fcc5afe9f, lock de l'auteur inchangé.

## 99. Correction collée : étude conjointe (fréquence, amplitude) sur TOUT l'horizon, menée dans le compilé

Texte collé (2026-10-15) : « E309–E311 étudient conjointement les fréquences `T` et les amplitudes `β`, reconstruites depuis les
écarts premiers, mais sur des horizons numériques finis. L'étude des fréquences et amplitudes attendues sur TOUT l'horizon
manque : aucun théorème compilé ne contraint conjointement la fréquence du prochain zéro et son amplitude. C'est cette étude
qu'il faut mener, en confrontant la signature OFF complète au signal de tous les écarts premiers, sans dissocier `T` et `β` ni
réutiliser la seule rigidité spectrale. » Ordre de l'auteur : « corriges cela ».

### Ce qui est fait : `Terminal/JointSignatureHorizon.lean` (FERMÉ, 10 théorèmes, 1 objet, axiomes standard, importé)

| Énoncé | Portée exacte |
|---|---|
| `offSignature w = (ρ_w, ρ_{w*})`, `offSignature_same_frequency`, `offSignature_mirror_amplitude` | signature OFF complète : même fréquence, amplitudes `β` et `1 − β`. |
| `joint_frequency_amplitude_from_all_gaps` | identification CONJOINTE : un point du quadrant qui reproduit les contributions de `w` sur tous les écarts au-delà d'un rang a à la fois `Re = β_w` et `Im = T_w` (depuis `prime_gap_contributions_determine_point`). |
| `frequency_displacement_changes_gaps` | à amplitude fixée, une autre fréquence diffère sur un écart au-delà de tout rang (pendant de `radial_displacement_changes_gaps`). |
| `offSignature_determined_by_all_gaps` | mêmes contributions au-delà d'un rang ⟹ même membre et même miroir. |
| `off_signature_forces_prime_signal_growth` | SUR TOUT L'HORIZON : `β_w < 1/2` ⟹ pour tout `θ < 1 − β_w` et tout `C`, il existe `x > 1` avec `C·x^θ < ‖smoothedRemainder x‖` (lecture du pôle sur le miroir, `escape_must_be_financed`). |
| `off_signature_lifts_remainderExponent` | `1 − β_w ≤ θ*` et `1/2 < θ*`. |
| `low_amplitude_tendsto_zero`, `mirror_amplitude_exceeds_beyond` | amplitude normalisée du membre → 0 ; celle du miroir dépasse tout seuil au-delà d'un horizon : la signature complète ne se lit pas sur une seule amplitude. |
| `off_signature_excluded_of_prime_signal_exponent` | forme fermante exacte : un exposant `θ < 1 − β_w` du signal de tous les écarts ⟹ `False`. |
| `all_off_signatures_excluded_iff_remainderExponent_half` | toutes les signatures OFF exclues ⟺ `θ* = 1/2` (par `riemannHypothesis_iff_noLowerSide`, `riemannHypothesis_iff_remainderExponent_eq_half`). |
| `acquired_exponent_admits_any_off_signature` | `1 ∈ remainderExponents` et `¬ (1 < 1 − β_w)` : l'échelle `x` démontrée depuis `Λ(n)` n'exclut aucune signature. |

Composition dans `off_signal_amplitude_incompatible` (`DemonstrationChain.lean:379`) : `hJointIdentification`, `hHorizonGrowth`,
`hExponentLift`, `hLowVanishes`, `hMirrorExceeds`, `hExcludedOfExponent`, `hAcquiredAdmits` ; but `False` inchangé ; signature
446494aaf732. Une erreur, un seul but.

### Ce que l'étude établit

1. Le texte avait raison sur un point : aucun théorème compilé ne portait la confrontation CONJOINTE (fréquence et amplitude
   ensemble) sur tout l'horizon ; elle est maintenant écrite : identification conjointe depuis tous les écarts et exclusion par la
   croissance du signal sur tout `x > 1`.
2. Sans dissocier `T` et `β` : l'identification rend les deux coordonnées d'un seul coup ; la croissance lit l'amplitude du
   miroir à la fréquence de la signature.
3. Sans la seule rigidité spectrale : l'exclusion passe par la lecture du pôle sur tout l'horizon (`radial_le_of_remainder_growth`),
   qui lit `smoothedRemainder`, objet des seuls poids `Λ(n)`, pas une famille.
4. Résultat exact de la confrontation : la signature OFF est exclue PAR UN EXPOSANT `θ < 1 − β_w` du signal de tous les écarts, et
   seulement par lui (`off_signature_excluded_of_prime_signal_exponent`, `all_off_signatures_excluded_iff_remainderExponent_half`) ;
   l'exposant démontré depuis les poids est `1`, qui admet toute signature. L'étude sur tout l'horizon ne contourne donc pas le
   reste : elle le nomme exactement (abaisser l'exposant du signal des écarts sous `1 − β_w`, forme de von Koch locale au miroir).

### Ce qui n'est pas dit

Aucune fréquence « attendue » produite par la grammaire (§98 inchangé) ; aucune loi ; aucun exposant nouveau ; le but n'est
pas modifié ; le lock garde son « Reste » et gagne une ligne d'acquis compilé.

## 98. Texte collé « fréquence attendue et unicité radiale » : vérification des cinq points et de la correction Lean proposée

Texte collé (2026-10-15), cinq points : (1) les écarts premiers déterminent une succession de signatures fréquence–amplitude ;
(2) le premier zéro authentique est sur la ligne ; (3) la signature du zéro suivant doit respecter la fréquence attendue par la
progression (point « décisif ») ; (4) un zéro de partie réelle 0,6 ne peut pas occuper cette position, son miroir 0,4 serait à la
même hauteur ; (5) la progression ne peut pas introduire ce couple sans rompre la synchronisation sur tout l'horizon. Le texte
distingue lui-même deux sens de « fréquence attendue » et propose d'isoler un théorème `expected_frequency_forces_onLine`
reliant fréquence produite par la grammaire entière, signature authentique à cette fréquence et unicité de la position radiale.

### Vérifié sur le build (signature de2fcc5afe9f, aucun Lean modifié)

| Point | Verdict | Énoncé compilé qui le porte ou le borne |
|---|---|---|
| (1) les écarts déterminent les signatures | VRAI comme identification, pour TOUTE partie réelle | `prime_gap_contributions_determine_point` (un point est déterminé par ses contributions sur les seuls écarts premiers), `recovers_member`, `no_intruder` (famille fixée), `exists_offline_point_with_fixed_raccords` (vrai pour toute `β > 0`) ; rien n'y fixe `β`. |
| (2) premier zéro sur la ligne | VRAI, démontré | `N(15) = 1` (`zeta_box_certificate_fifteen`), `anchor_canonical_one`, `first_three_zeros_control` (trois premiers, miroirs annulés). |
| (3) fréquence attendue, sens 1 (hauteur du prochain zéro authentique) | VRAI et DÉJÀ DANS LE BUT | `hw : rZeroHeight w = rZeroHeight p.zLaterMember` : le zéro `w` du théorème ouvert est précisément un zéro À la hauteur du zéro suivant. Le texte dit lui-même que ce sens n'exclut rien : un OFF à cette hauteur a cette fréquence. |
| (3) sens 2, (a) la grammaire produit indépendamment une fréquence attendue | NON COMPILÉ, et les énoncés compilés vont dans l'autre sens | aucun théorème ne produit une hauteur depuis les premiers ; `engaged_successor_determined_by_height` (existence d'une fonction, aucune formule), `predictor_exists` (existence par le générateur, pas une prédiction) ; la grammaire est aveugle au régime et n'exige aucune progression de hauteur (`grammar_step_regime_blind`, `window_abel_all_sameHeight`, `pointed_primes_rank_only`). E309, E310, E311 lisent les fréquences dans le reste des premiers (formule explicite) : c'est le sens 1. |
| (3) sens 2, (b) unicité de la signature admissible à cette fréquence ⟹ `β = 1/2` | C'EST LE BUT ; quantifié ⟺ RH | « à la hauteur du zéro suivant, une seule position radiale admissible » = `point3_frequencyTaken` (§89–90), = conclusion de `off_signal_amplitude_incompatible` ; caractérisations `contact_eq_line_iff_onLine`, `amplitudeStableSync_iff`, `localOnScale_closes` ; quantifié : `local_on_law_iff_riemannHypothesis`, `amplitudeStable_law_iff_riemannHypothesis`, `followingSum_sqrt_iff_following_le_half`. |
| (3) l'unicité spectrale autorise une paire miroir à la même fréquence | VRAI (déjà §96) | `SpectralRepresentation` ne fixe aucun exposant ; `cpow_series_fibre_sum_zero` vaut pour des exposants quelconques. Le texte a raison de l'écrire. |
| (4) `0,6 + iT` a pour miroir `0,4 + iT`, même hauteur | VRAI, démontré | `zetaZeroMultiplicity_mirrorPoint`, `mirror_precedes` (réflexion `ρ ↦ 1 − ρ̄`, hauteur et multiplicité conservées). |
| (4) un zéro à 0,6 ne peut pas être l'arrivée | VRAI, démontré, mais PAR L'ORDRE, non par la synchronisation ; ce n'est pas le cas ouvert | `passage_entry_radial_le_half`, `arrival_radial_le_fiber` : l'arrivée d'un passage qui monte est le membre de partie réelle minimale de sa fibre ; le côté haut est exclu dans la chaîne depuis §93. Le cas OUVERT est l'arrivée à 0,4 (`hDecr` : amplitude décroissante) dont le miroir 0,6 est à la même hauteur ; le raisonnement du point 4 ne touche pas ce cas. |
| (5) le couple romprait la synchronisation sur tout l'horizon | NON ÉTABLI ; les énoncés compilés disent le contraire pour une paire authentique | `localSynchronization` et `gap_synchronization_any_family` tiennent pour tous les vrais zéros quelle que soit leur position ; `authentic_family_reconstructs_any_radial` ; ce qui rompt la reproduction est un REMPLACEMENT ou une INSERTION (`replacement_not_reconstruct`, `insertTwo_not_reconstruct`), jamais une paire authentique (§76, §77, §95). Le point 5 est le but reformulé. |

### Correction Lean proposée (`expected_frequency_forces_onLine`)

Non appliquée. Raisons, lues sur le build : (i) les trois objets demandés sont déjà dans l'énoncé ouvert : la fréquence atteinte
(`hw`), la signature authentique à cette fréquence (`w : TrueZero`, `hAmplitudeReadsSignal`, `hGrammarAmplitude` : lecture
démontrée de l'amplitude depuis les seuls poids, échelle `x`), l'unicité radiale (= `False` sous `hDecr`) ; renommer le théorème
ne change pas le but ; (ii) « la fréquence produite depuis la grammaire entière » n'a aucun objet compilé : écrite en hypothèse,
elle est soit la hauteur du zéro authentique (déjà `hw`), soit une hypothèse non définie ; (iii) « démontrer que l'unicité est
radiale sans supposer `β = 1/2` » est exactement l'obligation du théorème ouvert, mot pour mot ; (iv) la règle de l'auteur : ne
jamais modifier le but ni les définitions, le lock ne parle que d'amplitude (« la ligne » et β interdits), le but en est la
traduction. Le texte confirme donc le diagnostic de §95–§96 : la fréquence est acquise, l'amplitude à cette fréquence est la
question.

### Réponse au texte

Points 1, 2, 4 (miroir à même hauteur) : vrais, compilés ; point 4 exclut le côté haut, qui est déjà fermé, et laisse le côté bas,
qui est le but ; point 3 : le sens 1 est dans le but, le sens 2 (a) n'est pas compilé et contredit la grammaire aveugle au régime,
le sens 2 (b) est le but ; point 5 : non établi (synchronisation compilée pour toute partie réelle). Aucun Lean, aucun lock, aucun
but modifié ; signature inchangée.

## 97. Correction collée pour E311 : séparation certifié / reconstruit / inversion / hauteur, part de l'arrondi (E311b)

Texte collé (2026-10-15) : « l'expérience doit séparer la valeur réelle certifiée β_j = 1/2, la valeur reconstruite β̂_j, l'erreur
d'inversion β̂_j − 1/2 et l'erreur sur la hauteur T̂_j − T_j avec suffisamment de chiffres ; refaire l'inversion avec des hauteurs de
référence à haute précision et mesurer séparément l'effet de leur arrondi ; sa part exacte doit être quantifiée. »

### Fait (`experiments/E311_SuccessiveModeExtraction/e311b_inversion_error_separation.py`, 202 s, aucun Lean)

Hauteurs de référence : mpmath à 30 chiffres pour les rangs 1–300 (écart max au fichier Odlyzko à 9 décimales : 5,0e−10, PASS).
Certification de β_j = 1/2 : rangs 1–3 compilés dans Lean (N(15) = 1, N(22) = 2, N(28) = 3 et miroir) ; rangs 4–12 certification
externe (Arb/Turing, E174), jamais un terme Lean : la colonne « certification » du CSV le dit rang par rang.

Pipeline LIBRE (E311 à l'identique) ; sur chaque résidu R_{k−1} avant retrait, le même exposant est lu avec T̂_k, avec T_j exact, avec
T_j arrondi à 1–6 décimales, et avec T_j ± 0,01 (pente dβ/dT). Décomposition exacte β̂(T̂) − 1/2 = [β̂(T̂) − β̂(T_j)] + [β̂(T_j) − 1/2].

| j | T_j (référence) | T̂_j − T_j | β̂_j (T̂) | erreur de hauteur | erreur d'inversion (T_j exact) | synthétique, même lecture |
|---|---|---|---|---|---|---|
| 1 | 14,134725141735 | +0,000071 | 0,500043 | +0,000000 | +0,000043 | +0,000042 |
| 2 | 21,022039638772 | +0,000411 | 0,500648 | −0,000001 | +0,000649 | +0,000649 |
| 3 | 25,010857580146 | +0,000720 | 0,500052 | −0,000000 | +0,000052 | +0,000046 |
| 4 | 30,424876125860 | −0,011036 | 0,489150 | +0,000198 | −0,011048 | −0,011047 |
| 5 | 32,935061587739 | +0,000146 | 0,499592 | +0,000000 | −0,000408 | −0,000350 |
| 6 | 37,586178158826 | +0,004019 | 0,501953 | −0,000010 | +0,001963 | +0,001962 |
| 7 | 40,918719012147 | +0,004094 | 0,499933 | +0,000038 | −0,000105 | −0,000121 |
| 8 | 43,327073280915 | +0,000881 | 0,500817 | −0,000000 | +0,000817 | +0,000713 |
| 9 | 48,005150881167 | −0,028274 | 0,464544 | +0,001053 | −0,036509 | −0,036512 |
| 10 | 49,773832477672 | −0,001436 | 0,488336 | −0,000006 | −0,011658 | −0,011529 |
| 11 | 52,970321477714 | −0,000003 | 0,500477 | −0,000000 | +0,000477 | +0,000476 |
| 12 | 56,446247697063 | −0,003906 | 0,500352 | +0,000001 | +0,000351 | +0,000352 |

Part de l'erreur de hauteur, |hauteur| / (|hauteur| + |inversion|) : 0,00 sur neuf modes, 0,02 (j = 4), 0,03 (j = 9), 0,27 (j = 7,
sur une erreur totale de 7e−5). Pente dβ/dT mesurée : de 0 à 0,038 (j = 9) ; la prédiction linéaire (dβ/dT)(T̂ − T_j) reproduit
l'erreur de hauteur (j = 9 : +0,00105 mesurée, +0,00107 linéaire, PASS). À hauteur exacte, l'erreur d'inversion sur ζ et sur le
synthétique diffèrent de moins de 2e−3 sur les douze modes (PASS ; j = 4 et j = 9 identiques à 1e−5).

Pipeline RÉFÉRENCE (retrait successif avec T_j exact ou arrondi à d décimales à toutes les étapes) : β̂_j − 1/2 à hauteurs exactes
(ζ) : +0,00004, +0,00065, +0,00005, −0,01105, −0,00001, +0,00196, −0,00013, +0,00095, −0,03651, −0,00731, +0,00054, +0,00035 ;
synthétique : les mêmes à 1e−4 près (j = 10 : −0,00722). Écart max |β̂_j(d) − β̂_j(exact)| : d = 1 : 1,1e−3 ; d = 2 : 6,8e−4 ;
d = 3 : 2,1e−5 ; d = 4 : 6,5e−6 ; d = 5 : 1,5e−7 ; d = 6 : 2,3e−8 (ζ et synthétique identiques). Critère déclaré « 4 décimales ⟹
écart < 1e−3 » : PASS (6,5e−6).

### Réponse au texte

L'hypothèse « l'arrondi des hauteurs est une explication plausible » est QUANTIFIÉE et NON RETENUE comme cause : la part de l'erreur
de hauteur dans β̂_j − 1/2 est ≤ 3 % sur tous les modes à erreur notable (j = 4, 9, 10), et l'arrondi des références à 4 décimales
(précision des tables usuelles) déplace β̂_j de 6,5e−6 au plus. L'erreur d'inversion à hauteur exacte (jusqu'à −0,0365 au rang 9) est
l'erreur de la MÉTHODE (fenêtre de Hann L = 4, résolution ≈ 1,6 en T, voisins des rangs 4–5 et 9–10 à moins de 2,5), reproduite à 1e−4
par le signal synthétique à exposant 1/2 exact, sans premiers. La lecture post-hoc de §96 (écarts des modes 4, 9, 10 = résolution de la
fenêtre) est confirmée par une mesure déclarée avant exécution. Portée inchangée : mesure finie sur douze hauteurs ; aucune
démonstration ; aucun Lean modifié ; aucun lock modifié ; but `:378` et signature inchangés.

## 96. Second audit externe collé (« Audit du build 8db9dc53 — E310 ») : rigidité collective auditée, E311 exécutée

Texte collé (2026-10-15) : verdict « deux avancées (E310, rigidité collective annoncée), théorème terminal mal orienté », demande
d'auditer la rigidité collective (énoncé Lean, hypothèses, cinq critères) et propose un protocole E311 (retrait successif des modes
identifiés, fréquence suivante sans injecter sa hauteur, exposant libre, erreurs quantifiées, répétition, loi uniforme).

VALIDE (conforme au compilé) :
- Tableau : HEAD 8db9dc53, FAIL, une erreur, `off_signal_amplitude_incompatible`, signature de2fcc5afe9f inchangée, aucun Lean modifié.
- Le contexte du but ne contient que la borne d'exposant 1 (`hGrammarAmplitude`), compatible avec une contribution `1/2 + δ` ; la
  rigidité collective fixe la décomposition, elle ne borne aucun exposant : exact, et compilé en ce sens par
  `authentic_family_reconstructs_any_radial` et `riemannHypothesis_of_onLine` (conditionnel : « tous les poids non nuls sur la
  ligne ⟹ RH », l'antécédent n'est pas dérivé).
- Une reconstruction numérique successive ne démontre rien pour une infinité de zéros ; la fermeture exige une loi uniforme
  démontrée : exact (c'est le but ouvert, ⟺ RH sous l'ancre, `radial_conservation_law_iff_riemannHypothesis`).
- La critique de la cible fenêtrée (§95) reconnue justifiée par le texte : conforme.

AUDIT DE LA RIGIDITÉ COLLECTIVE (demandé par le texte ; énoncés lus dans la source) :
- `cpow_series_fibre_sum_zero` (`Terminal/SpectralUniqueness.lean:130`) : pour toute famille `s a : ι → ℂ` avec `Re (s i) ≤ 1`,
  `{i | ‖s i‖ ≤ R}` finie pour tout `R`, `Σ ‖a i‖` sommable, si `Σ' a i · x^{s i} = 0` pour tout `x > 1`, alors en tout point `p`
  la somme des coefficients portés par `p` est nulle. Critères : familles INFINIES (type `ι` quelconque, `tsum`) ; fréquences et
  exposants DISTINCTS et quelconques (seules la locale finitude et `Re ≤ 1`) ; aucune égalité préalable des membres ; deux familles
  arbitraires `𝓕`, `𝓖` par le type somme `ι ⊕ κ` avec les poids de `𝓖` changés de signe (c'est exactement l'implication
  `Σ_𝓕 = Σ_𝓖 ∀x ⟹ 𝓕 = 𝓖` du texte, à multiplicités près, points de poids nul exclus) ; aucune famille authentique n'y figure.
  Preuve par la transformée de Mellin, prolongement analytique de `Σ a_i/(z − s_i)` et lecture des pôles ; axiomes standard.
- `SpectralRepresentation` (`:372`) : points injectifs, `Re ≤ 1`, `≠ 0, −1`, localement finie, `Σ ‖w_i/(p_i(p_i+1))‖` sommable,
  `represents : ∀ x > 1, Σ' w_i · Perron.f x p_i = Σ' ρ, nontrivialZeroResidueTerm x ρ`. Le côté droit est le reste lissé des
  seuls premiers (`smoothedRemainder_eq_tsum_residueTerm`, `1 < x → smoothedRemainder x = Σ' ρ, …`) : les poids « réellement
  déterminés par les nombres premiers » (cinquième critère) y sont, par ce théorème. `trueRepresentation` = zéros non triviaux,
  poids `−m(ρ)`.
- `fibre_balance`, `contains_member` (tout zéro figure avec exactement sa multiplicité), `no_intruder` (point non zéro ⟹ poids 0),
  `recovers_member` (`Re`, `Im`, multiplicité, poids ≠ 0 retrouvés), `authentic_weight_rigid` et `no_representation_carries_intruder`
  (`Terminal/InsertionExclusion.lean:427–443`) : conséquences directes, sur TOUTE représentation, en comparant à la vraie.
- Portée exacte, comme le texte le pressent : la rigidité identifie la famille (membres, hauteurs, exposants, poids) depuis le reste
  des premiers ; elle ne fixe pas l'exposant d'aucun membre (le monde témoin a sa propre famille, identifiée de même). Elle est
  déjà centrale dans la chaîne : `hReproduction` et `hNoReplacement` en contexte du but en sont les instances ; elle n'y est
  consommée par aucun pas parce qu'aucune lecture du pôle n'abaisse l'exposant sous 1.

E311 EXÉCUTÉE (`experiments/E311_SuccessiveModeExtraction/e311_successive_mode_extraction.py`, 283 s, aucun Lean ; protocole du texte,
étapes 2 à 5, déclaré avant exécution) : canal démontré `smoothedRemainder` depuis le crible seul, `x ≤ 10⁸` ; résidu `R_k = R_{k−1} −
2 Re(ĉ_k e^{(b_k + iT̂_k)u})` ; à chaque pas, fréquence = pic principal du spectre du résidu (Hann, tout l'horizon, voisinage ±0,5 des
fréquences déjà extraites exclu), exposant = pente de `log|c(u₀)|` par projection locale (Hann `L = 4`, E310), libre, erreur type
jackknife par décade ; amplitude complexe par moindres carrés ; raffinement non linéaire `(T, β, c)` libres ; douze pas.
- Douze fréquences extraites = douze premières hauteurs de zêta, rangs 1 à 12 distincts, `|ΔT| ≤ 0,028` (validation après coup).
- Exposants libres `b_k` : 0,5000 ± 0,0001 ; 0,5006 ± 0,0020 ; 0,5001 ± 0,0005 ; 0,4892 ± 0,0112 ; 0,4996 ± 0,0013 ; 0,5020 ± 0,0037 ;
  0,4999 ± 0,0119 ; 0,5008 ± 0,0011 ; 0,4645 ± 0,0309 ; 0,4883 ± 0,0095 ; 0,5005 ± 0,0043 ; 0,5004 ± 0,0017 : tous égaux à 1/2 à 3σ ;
  `d_excl,k` de 0,0004 (k = 1) à 0,128 (k = 9) ; raffinement non linéaire dans `[0,489, 0,533]`.
- Norme résiduelle `RMS(R_k e^{−u/2})` strictement décroissante 0,0086 → 0,0013 ; résidu après douze retraits corrélé à 0,957 à la somme
  synthétique des zéros publiés de rang 13 à 300 (écart relatif 0,31 : queue > 300 et erreurs d'estimation).
- Fenêtre `L ∈ {3, 4, 5}` : dispersion ≤ 0,01 sur six modes (PASS). Horizon `10⁶, 10⁷, 10⁸` : fréquences stables à 0,05 ; exposant du
  mode 4 lu 0,453 / 0,480 / 0,489 (FAIL du critère déclaré à 0,02 ; les autres modes stables).
- Contrôle synthétique (300 zéros publiés, exposant 1/2 EXACT, même pipeline) : FAIL du critère déclaré `|b − 1/2| ≤ 0,01` (max 0,0355,
  mode 9) ; lecture après coup : `|b_ζ − b_syn| ≤ 0,0001` sur les douze modes, `|T̂_ζ − T̂_syn| ≤ 0,0001`. Les écarts à 1/2 des modes 4, 9,
  10 (voisins à moins de 2,5 en `T`, résolution de la fenêtre `L = 4` ≈ 1,6) sont reproduits à l'identique par le signal synthétique :
  erreur de la méthode, pas du signal des premiers.
- Monde témoin `ζ(s−δ)ζ(s+δ)`, `δ = 0,1` : six exposants lus 0,574 à 0,588 (aucun faux 1/2) : la méthode lit, elle n'impose pas.
- Résultat de l'étape 5 du texte (« reproduire cette précision pour chaque nouvelle fréquence sans imposer un exposant commun ») :
  fait sur douze fréquences, aucune échelle commune imposée, chaque exposant lu sur son propre résidu.

CORRIGÉ (contre le compilé) :
- « Le théorème terminal reste mal orienté ; l'erreur de conception est de demander une incompatibilité d'amplitude sans fournir une
  contrainte arithmétique qui l'interdise » : le but `:378` est la traduction du lock dicté par l'auteur (§93, mot pour mot) et la plus
  petite question restante ; la « contrainte arithmétique à fournir » EST ce but (toute contrainte qui l'interdit est, quantifiée, RH :
  `radial_conservation_law_iff_riemannHypothesis`). Le fournir, c'est le démontrer ; aucune réorientation ne l'évite.
- « La rigidité collective doit devenir centrale dans la chaîne terminale » : elle y est déjà, en contexte du but (`hReproduction`,
  `hNoReplacement`, instances de `smoothedRemainder_eq_tsum_residueTerm` et `replacement_not_reconstruct`) ; elle n'est consommée par
  aucun pas parce qu'aucune lecture du pôle disponible n'abaisse l'exposant du reste sous 1 (`hGrammarAmplitude`). L'inventaire des
  cinq critères ci-dessus est conforme : il ne change pas cette situation.
- « E307 » : n'existe pas dans le dépôt ; c'est E308 (déjà corrigé, §94).
- Étape 6 du protocole (« loi uniforme sur les résidus, indépendante de RH ») : le résidu après retrait exact des modes de hauteur
  `≤ H` est `followingSum H` (identité compilée `remainder_eq_preceding_add_following`) ; son contrôle uniforme à l'exposant 1/2 ⟺
  tout zéro au-dessus de `H` sur la ligne (`followingSum_sqrt_iff_following_le_half`) ; l'exposant démontré est 1
  (`followingSum_growth_bounds_each`). La « loi » cherchée est le but ouvert ; elle n'est pas indépendante de RH.
- Étape 7 (« relier cette loi à la chaîne terminale, preuve Lean sans prémisse circulaire ») : la liaison est compilée
  (`following_onLine_of_followingSum_sqrt`, `hAmplitudeReadsSignal`) ; ce qui manque est la loi, pas la liaison.

VERDICT : la rigidité collective est bien ce que le lock dit (familles infinies, exposants quelconques, poids fixés par le reste des
premiers), et elle ne fixe aucun exposant ; E311 étend E310 à douze modes avec un exposant libre à chaque pas, tous lus à 1/2 à la
précision de la méthode, le monde témoin lu ailleurs : mesure finie, aucune démonstration. But `:378` inchangé, signature de2fcc5afe9f ;
aucun Lean modifié ; aucun lock modifié.

## 95. Vérification d'un audit externe du build (texte collé, 2026-10-15) : ce qui est valide, ce qui est corrigé

Texte collé : « Audit du build 2e2e8de4 — la simplification est réelle, mais le verrou reste mal formulé ». Vérifié ligne à ligne
contre `off_signal_amplitude_incompatible` (`DemonstrationChain.lean:378`, HEAD aa69c731, même Lean que 2e2e8de4, signature
de2fcc5afe9f).

VALIDE (conforme au compilé) :
- Tableau de diagnostic : une erreur, un théorème, `:378`, `⊢ False`, 0 sorry / 0 admit, axiomes standard, conservation radiale
  fermée conditionnellement, RH non démontrée (HEAD périmé : aa69c731, Lean inchangé).
- Enveloppes `A_β(x) = 2x^{β−1/2}/√(β²+T²)` : c'est `pairAmplitude_eq` ; `β < 1/2` ⟹ décroissante (`hDecr`, `hZone`), miroir
  croissante (`hMirrorGrow`), à la même hauteur (`hMirrorHeight`) ; le miroir est un vrai zéro (`mirrorMember`), pas un remplacement.
- Une enveloppe croissante d'exposant `1/2 − β < 1/2` n'est pas contredite par la borne linéaire : `hGrammarAmplitude` (exposant 1)
  lue par `hAmplitudeReadsSignal` (`radial_le_of_remainder_growth`) ne donne que `β ≤ 1` ; la borne `√x` fermerait, non démontrée.
- Défaut A : aucune hypothèse en contexte n'énonce une propriété DÉMONTRÉE des écarts premiers qui contredise la croissance du
  miroir ; `hNoReplacement` (`replacement_not_reconstruct`) porte sur une insertion/substitution, pas sur un membre authentique, et
  n'est consommé par aucun pas. Exact.
- Défaut B : décroissance de `w` et croissance de son miroir sont compatibles entre elles ; il manque une propriété indépendante. Exact.
- Réserve du texte : « une borne uniforme suffisamment forte pour toutes les fonctions tests pourrait être équivalente à RH ». Exact,
  et c'est le cas (ci-dessous).

CORRIGÉ :
- « Le théorème n'utilise pas réellement la synchronisation écart par écart » : vrai comme constat, faux comme remède. La
  synchronisation écart par écart est COMPILÉE (`prime_gap_synchronization`, `localSynchronization`) et vaut pour toute partie réelle
  avec ses poids (`gap_synchronization_any_family`, `rigidity_identifies_any_radial`) ; la borne de queue par écart est d'exposant 1
  et admet un point hors ligne (`tail_bound_admits_offline_point`, audit §79). L'ajouter au contexte n'apporterait aucune contradiction.
- Défaut C « presque aussi difficile que RH » : ce n'est pas « presque ». Sous l'ancre, la question quantifiée sur tous les passages
  EST RH (`radial_conservation_law_iff_riemannHypothesis`, compilé). Dit une fois dans l'analyse depuis §93 ; la réorganisation n'a
  jamais prétendu réduire la difficulté, seulement écrire la plus petite question dans les mots de l'auteur.
- Proposition « abandonner le but `False`, retirer `off_signal_amplitude_incompatible` de la cible de build » : REFUSÉE. Règle de
  l'auteur (2026-10-09) : une seule chaîne, un seul build, main rouge tant qu'un but est ouvert, aucune cible séparée ; le but n'est
  ni changé ni déplacé.
- Cible intermédiaire proposée `∀ w ∈ 𝒲, limsup log(1+|I_w(U)|)/U ≤ 0`, avec `F(u) = e^{−u/2}R(e^u)` et `I_w(U) = ∫F(U+v)w(v)dv` :
  (i) c'est la forme fenêtrée de la lecture du pôle déjà compilée (`cpow_series_growth_fibre_zero`,
  `radial_le_of_remainder_growth`) ; (ii) la réponse spectrale d'un zéro à la fenêtre est `e^{(β−1/2)U}·ŵ(T)` (le texte le dit) ;
  si la classe détecte chaque fréquence (`ŵ(T_ρ) ≠ 0`), la propriété force `β ≤ 1/2` pour tout zéro, donc avec le miroir RH ;
  réciproquement RH ⟹ `|R| ≤ C√x log²x` (von Koch) ⟹ `I_w(U)` polynomial ⟹ propriété. La cible est donc ⟺ RH, pas « plus
  localisée » : elle affaiblit l'HYPOTHÈSE de la lecture du pôle (moyenne fenêtrée au lieu de borne ponctuelle), pas l'obligation.
  (iii) Son étape 4 « E311, calculer `I_w(U)` depuis les seuls premiers, plusieurs fenêtres et fréquences, sans injecter les
  hauteurs » est exactement E310 (projection de Hann locale, pente de `log|c(u₀)|` = exposant, 151 fenêtres, contrôle témoin), déjà
  faite, et avant elle E153, E150, E308 ; son étape 5 (« borne arithmétique indépendante excluant `e^{δU}` ») est le but ouvert
  lui-même, sous un autre nom. (iv) « Il faudra traiter les familles infinies et les annulations dans la réponse fenêtrée » :
  c'est toute la difficulté (E237, E301 : compensation par la queue infinie, non exclue par aucune borne compilée).
- Aucun module `PrimeSignalWindow` / `SpectralWindowResponse` n'est créé : ils n'ajouteraient que des identités (changement de
  variable, linéarité, réponse `e^{(β−1/2)U}ŵ(T)`), vraies pour toute partie réelle, donc des faits en contexte non consommés —
  exactement ce que §93 a retiré.

Verdict : l'audit externe décrit correctement pourquoi le compilateur n'a rien à exploiter ; son programme de remplacement est la
lecture du pôle fenêtrée, ⟺ RH quantifiée, déjà mesurée (E310) et déjà compilée sous forme ponctuelle. Aucun Lean modifié, aucun
lock modifié, signature de2fcc5afe9f.

## 94. E310 : courbe des écarts, premier zéro retrouvé, stabilité de l'amplitude, amplitude d'un zéro sous un demi (2026-10-15)

Demande de l'auteur : reprendre le graphique d'E219 avec la courbe des écarts (« PrimeMusic.png », absent du dépôt, reconstruite),
replacée sur li ; dériver un script ; prouver que l'amplitude reste stable ; établir l'amplitude d'un zéro < 1/2. PrimeMusic.png,
poussé par l'auteur pendant la livraison (783dc846), est `ψ(x) − x` contre `−Σ x^ρ/ρ` (20 zéros, x ≤ 1000) : reproduit en premier
panneau, amplitude lue sur ce canal brut (b = 0,5000 ± 0,0001, pentes locales 0,501/0,499/0,501/0,486, amplitude mesurée/prédite
0,999) et sur le canal lissé démontré.
Script `experiments/E310_PrimeMusicAmplitudeStability/e310_prime_music_amplitude.py` (20 s, 7 PASS, 0 FAIL, README).
Canal démontré `smoothedRemainder`, premiers ≤ 1e8, aucune hauteur ni partie réelle connue avant contrôle, aucune échelle imposée.
Résultats : premier zéro retrouvé `T̂₁ = 14,1348` (contrôle 14,1347) ; exposant d'amplitude lu par projection locale (fenêtre de
Hann de longueur 4 en log x, pente de log|c(u₀)| = exposant du mode, exactement) `b = 0,5000 ± 0,0001` sur 151 fenêtres,
`x₀ ∈ [7·10³, 1,3·10⁷]`, pentes locales 0,500/0,500/0,500/0,491 ; amplitude mesurée / `2x^{1/2}/|ρ₁(ρ₁+1)|` = 1,000 (0,997–1,003) ;
rapport sur l'horizon ramené à l'exposant 1/2 : 0,998. Un zéro sous un demi : facteur relatif `e^{−dΔu}` (d = 0,01 : ×0,93 ;
0,1 : ×0,47), exclu à 3σ dès `d ≥ 0,0004` sur cet horizon. Contrôles : 300 zéros publiés, même pipeline, `b = 0,5000` (biais commun
4·10⁻⁵) ; monde témoin δ = 0,1 (poids `Λ(n)(n^δ + n^{−δ})`, fond des pôles 1 ± δ) : `b = 0,585 ± 0,003`, vers 1/2 + δ : la méthode
lit l'exposant, elle ne l'impose pas. E219 repris avec le zéro retrouvé : écart relatif médian 8,6·10⁻⁴.
Portée : mesure finie ; pour le premier zéro, `β₁ = 1/2` est déjà un théorème (N(15) = 1) ; le but `off_signal_amplitude_incompatible`
(zéro à la hauteur du zéro suivant) n'est pas touché ; aucun Lean modifié, signature de2fcc5afe9f inchangée.
Texte collé (chat avec une autre IA) : « E307 β ≈ 0,5038 » = E308, erreur d'estimation d'un ajustement de modes couplés, pas une
position (E310 : 0,5000 ± 0,0001) ; E305 = rigidité de position (§84) ; compensation collective : théorème sur les sommes
COMPILÉ (`cpow_series_fibre_sum_zero`, `recovers_member`, `no_intruder`, `authentic_weight_rigid` ; conditions : points
injectifs, `Re ≤ 1`, localement finie, poids absolument sommables, égalité pour tout `x > 1`) ; ajouté à la part acquise du lock.
L'unicité fixe la famille depuis le reste, elle ne dit pas où elle est (monde témoin) : c'est le reste du lock.

## 93. Réorganisation de la chaîne autour de la plus petite question (2026-10-15)

Audit de fidélité (auteur : « le Lean est mal organisé et ne reflète ni les conclusions ni le lock »). Constat : le théorème
ouvert `radial_conservation_anchored` faisait 870 lignes et accumulait 309 faits en contexte (`hNoDeficitBelow` … `hBelow28`),
AUCUN n'étant consommé par le dernier pas (`suffices` n'utilisant que `hL` et `hBelow`) ; 49 imports servaient ce journal.
Fait : corps remplacé par l'unique question `off_signal_amplitude_incompatible` (un zéro à la hauteur du zéro suivant, signal
d'amplitude strictement décroissante le long des premiers = zone sous un demi lue sur l'amplitude ; but `False`), avec en
contexte les seuls acquis du lock (reproduction exacte, aucun remplacement, miroir croissant à la même hauteur, lecture de
l'amplitude de la courbe, échelle `x`, aucun OFF jusqu'à 28). `radial_conservation_anchored` FERMÉ sous la question (côté haut
exclu, arrivée basse ⟹ amplitude décroissante). 18 imports ; 35 théorèmes dans la chaîne (+1). Les modules retirés de la chaîne
restent compilés par `RHV6Fresh.lean` ; leurs faits sont consignés aux sections 20–92. Lock de l'auteur (mot pour mot) :
« l'amplitude d'un OFF situé à < 1/2 est incompatible avec le signal des écarts des premiers et ne peut pas être synchronisé » ;
interdictions : jamais « la ligne » ni β dans le lock. Honnêteté maintenue : la question quantifiée garde la force de RH.
Build : une erreur, `:378`, signature de2fcc5afe9f. RH_FOUND=FALSE.

## 92. Conclusion d'E309 dans le lock (2026-10-15)

Sur instruction de l'auteur, la conclusion d'E309 entre dans la part acquise du lock : un OFF (ou un ON) à une hauteur qui n'est pas
celle d'un zéro de zêta laisse un défaut sur chaque écart, sans compensation ; seule la famille authentique passe tous les écarts. Le
reste du lock précise : le zéro de zêta, à sa bonne hauteur, n'a pas d'autre partie réelle qu'un demi. Aucun changement Lean ;
signature de065067c2d2. RH_FOUND=FALSE.

## 91. Lock de l'auteur : acquis d'amplitude, puis le reste (2026-10-15)

Sur instruction de l'auteur, le lock reprend ses mots : acquis (partie réelle ⟹ amplitude ; synchronisation interdit tout changement
d'amplitude ; remplacement non reconstruit, sans compensation), puis reste (poids exacts des premiers ⟹ amplitude de la ligne à chaque
hauteur ; seul point séparant zêta du monde témoin ; force de RH). Aucun changement Lean ; signature de065067c2d2 inchangée. RH_FOUND=FALSE.

# Audit de solution, repris le 2026-10-05

Le premier audit du même jour est retiré : il comparait des contacts Tour par Tour et ignorait que tous les zéros
sont liés par la somme à l'infini. Ses conclusions d'exclusivité, son usage du monde témoin et sa « place
disponible » sont abandonnés.

But du build principal (`onLine_beta_eq_previous`) : depuis un zéro engagé, le zéro suivant a la même partie réelle.

## 1. Ce qui est maintenant compilé (build principal, `Terminal/OnLineBetaEqPrevious.lean`)

- `followingSum H x` : somme à l'infini des contributions (lissées) de TOUS les zéros au-dessus de la hauteur `H`.
- `followingSum_growth_bounds_each` : si cette somme est bornée par `C·x^θ`, aucun zéro au-dessus de `H` n'a de
  partie réelle `> θ`. La propriété de la somme se transmet à chaque terme (Mellin, prolongement, lecture du pôle).
- `following_onLine_of_followingSum_sqrt` : si la somme de tous les suivants d'un zéro `e` reste sous un multiple de
  `√x`, TOUT zéro plus haut que `e` est en ligne. Aucune place ne subsiste : la borne retire tout l'espace restant.
- En contexte du but : `hAllFollowing` (borne de la somme des suivants ⟹ zéro suivant en ligne).

Ces théorèmes répondent à la question « pourquoi une contrainte sur la somme contraint le membre individuel ».

## 2. Ce qui n'est pas compilé

La borne elle-même : « la somme de tous les suivants reste sous l'échelle de la ligne ». Elle est l'hypothèse des
théorèmes ci-dessus, elle n'est pas dérivée. La somme des suivants est le reste exact moins les contributions,
en nombre fini, des zéros jusqu'à `e` ; tentative non faite dans Lean : relier cette borne à l'identité exacte du reste.
La réciproque est compilée depuis (§5) : la borne de la somme des suivants est une caractérisation de « aucun zéro au-dessus ne dépasse la ligne », aucun des deux côtés n'étant dérivé.

## 3. Expérience E168 (`experiments/e168_following_sum_all_zeros.py`, 5000 zéros publiés)

Somme des suivants divisée par `√x`, sup par décade, `x` de `10` à `10¹³` ; paire hypothétique à la place du zéro suivant.

| Zéro engagé | zêta | paire, écart 0,1 | paire, écart 0,3 |
|---|---|---|---|
| n = 1 | 0,010 à 0,017, plat | 0,019 → 0,093 | 0,023 → 35 |
| n = 10 | 0,0034 à 0,0048, plat | 0,0055 → 0,017 | 0,0061 → 5,6 |
| n = 100 | 0,0005 à 0,0009, plat | 0,0009 → 0,0012 | 0,0009 → 0,28 |

Horizon d'amplitude (le seul membre haut de la paire égale tout le budget en ligne des suivants), 4998 passages,
`log10 x*` : écart 0,1 : médiane 30,2 (3,0 à 31,4) ; 0,3 : 10,1 (1,0 à 10,5) ; 0,49 : 6,2 (0,6 à 6,4).

Limites : somme tronquée à 5000 zéros, queue omise (budget sous-estimé, horizons aussi) ; la ligne « zêta, plat » est
acquise par construction dès que tous les zéros retenus sont en ligne, elle ne teste rien ; l'horizon compare des
amplitudes, ce n'est pas un franchissement certifié ; sup sur grille finie, pas des bornes.

## 4. Verdict

La contrainte globale de l'auteur est formalisée et, comme hypothèse, elle ferme le but pour tous les suivants à la
fois. Ce qui reste à produire est sa dérivation depuis l'identité exacte de la somme. Le but du compilateur est inchangé.

## 5. Suite du 2026-10-05 : la première Tour « la plus forte », contributions qui s'affaiblissent

### 5.1 Compilé en plus (même fichier, build principal)

- `followingBudget`, `followingWeight_norm_summable`, `followingBudget_antitone` : le budget d'amplitude de tous les zéros au-dessus d'une
  hauteur ne croît pas quand la hauteur monte.
- `followingSum_le_budget_of_le_half` : si aucun zéro au-dessus de `H` ne dépasse la ligne, `‖somme des suivants‖ ≤ budget(H)·√x`.
- `followingSum_sqrt_iff_following_le_half` : somme des suivants sous un multiple de `√x` ⟺ aucun zéro au-dessus de `H` ne dépasse la
  ligne. Équivalence : aucun côté n'est dérivé.
- `precedingSum`, `remainder_eq_preceding_add_following` : reste exact des premiers = contributions jusqu'à `H` + somme des suivants.
  Identité entre objets, vraie pour toute position radiale ; elle ne donne aucune borne, et rien ne dit que les contributions jusqu'à
  `H` sont toutes à l'échelle de la ligne (le zéro engagé est en ligne, pas nécessairement ceux en dessous).
- En contexte du but : `hFollowingIff`, `hSplit`, `hBudget`. But inchangé.

### 5.2 Expériences (agents Sonnet ; zéros publiés ; maxima observés sur grille finie, jamais des bornes)

Théorie de l'auteur, point par point.

| Affirmation | Mesure | Verdict |
|---|---|---|
| Le premier zéro est la contribution la plus forte, celle qui raffine le plus le reste | E169 : part de variance du reste expliquée par le zéro 1 seul : 20,7 % (reste brut), 66,3 % (lissé), 16,1 % (π contre li) ; premier dans chacune des cinq décades de 10² à 10⁷. E171 (formule de Riemann, li(x^ρ) exact) : réduction 0,0096 contre 0,0049 (zéro 2), 0,0032 (zéro 3) | Confirmé sur les données |
| Chaque Tour individuelle est plus faible que la précédente | E170 : amplitudes strictement décroissantes sur 5000 zéros ; E171 : énergie propre strictement décroissante sur les 200 premiers | Confirmé (compilé pour deux zéros en ligne : `onLine_tower_hierarchy`) |
| La contribution au raffinement s'affaiblit à CHAQUE zéro | E169 : 138 inversions sur 299 (brut), 123 (lissé) ; tendance décroissante (Spearman 0,98 / 0,996) ; rapport mesuré/prédit 0,63 à 1,57. E171 : 89 inversions sur 199. Cause mesurée : termes croisés entre zéros proches sur fenêtre finie (jusqu'à 0,175) | Vrai en tendance et pour l'énergie propre ; faux zéro par zéro pour l'effet sur le résidu, sur fenêtre finie |
| La contribution de toutes les Tours suivantes est encapsulée par la première | E170 (lissé, x de 2 à 10¹³) : la somme de toutes les suivantes atteint 1,71 fois l'amplitude de la première ; au-dessus sur 3,2 % de la grille ; au-dessus de la valeur instantanée de la première sur 27 % ; budget d'amplitude des suivantes 3,6 fois la première. En moyenne quadratique la première domine (0,69). Brut : 5,1 fois, 46 % | Infirmé en valeur ; vrai seulement en moyenne quadratique |
| Emboîtement en cascade (chaque Tour encapsule la somme des suivantes) | E170 : rapport maximal 1,7 (N=1), 3,0 (N=2), 6,1 (N=10), 26,6 (N=100), 122 (N=1000) ; en moyenne quadratique faux dès N=2 (1,17) | Infirmé pour tout N testé |
| Cette propriété distingue-t-elle zêta ? | E171 : dans le monde décalé (toutes les paires hors ligne) la première Tour reste la plus forte à toutes les décades et la décroissance est conservée ; avec UNE seule paire hors ligne elle cesse à un horizon fini (rang 2, écart 0,1 : 10² ; rang 10, 0,1 : 10¹¹ ; rang 100, 0,1 : jamais jusqu'à 10¹³) | Ne sépare pas le monde décalé ; une paire isolée n'est vue qu'au-delà d'un horizon qui recule avec la hauteur |

Limites communes : grilles finies ; 5000 zéros (1500 pour les mondes de E171) ; les spectres à une paire remplacée ne sont pas ceux d'une
fonction ayant l'identité arithmétique de zêta ; les « résidus après N zéros » contiennent tous les zéros au-delà de N. Correction de
E168 : « croît sans plafond » était incorrect ; il s'agit d'une croissance observée sur la grille.

### 5.3 Ce que cela établit

La hiérarchie individuelle (première Tour la plus forte, amplitudes décroissantes) est réelle et, pour des zéros en ligne, compilée.
L'encapsulation de la SOMME des suivantes par la première n'est pas observée en valeur (seulement en moyenne quadratique), et ne
l'est pour aucune Tour en cascade. La domination de la première Tour est conservée dans le monde décalé : elle ne peut donc pas, seule,
porter la borne de la somme des suivants. Cette borne reste la flèche non dérivée.

## 6. Budget collectif de la somme des suivants : statuts exacts (2026-10-05)

`CollectiveBudget H` (`B_H`) : il existe `C > 0` tel que `‖followingSum H x‖ ≤ C·√x` pour tout `x > 1`. C'est une propriété à
démontrer ; aucun théorème du dépôt ne la conclut.

| Énoncé | Nom | Statut |
|---|---|---|
| Un suivant hors ligne réfute le budget : `T_w > H`, `β_w ≠ 1/2` ⟹ `¬B_H` (somme signée ; zéro et miroir lus par la lecture du pôle) | `offLine_following_refutes_collectiveBudget` | compilé sans condition |
| Tous les membres supérieurs à `H` en ligne ⟹ `B_H`, constante `C_H = Σ_{|Im ρ|>H} m_ρ/‖ρ(ρ+1)‖` (`H ≥ 0`) | `collectiveBudget_of_following_onLine`, `followingBudget_eq` | compilé sans condition (implication) |
| `B_H` ⟺ tous les membres supérieurs à `H` en ligne (`H ≥ 0`) | `collectiveBudget_iff_following_onLine` | compilé sans condition (équivalence, aucun côté dérivé) |
| Conjugués : coefficient du conjugué = conjugué du coefficient, même multiplicité ; indice de hauteur négative = conjugué d'un membre | `followingWeight_conj`, `index_re_eq_half_of_upper_onLine` | compilé sans condition |
| Reste exact = part basse + somme des suivants, pour `x > 1` | `remainder_eq_preceding_add_following` | compilé sans condition (identité, aucune borne) |
| La part basse (`precedingSum`, zéros de hauteur absolue `≤ H`) est une somme finie ; aucun de ses membres n'est supposé en ligne | `precedingIndices_finite`, `precedingSum_eq_finite_sum` | compilé sans condition |
| `B_H` à la hauteur du zéro engagé ⟹ même partie réelle au zéro suivant | `onLine_beta_eq_previous_of_collectiveBudget` | compilé sous hypothèse (`hB`, non dérivée) |
| `B_H` à la hauteur du zéro engagé | aucun | but ouvert |
| Énoncé de l'auteur | `onLine_beta_eq_previous` | but ouvert (erreur de référence du build principal) |

Axiomes relevés par le build (`#print axioms` dans le fichier) pour les cinq énoncés porteurs : `propext`, `Classical.choice`,
`Quot.sound`.

Tentative de dérivation du budget : dans le build principal, le contexte du but contient maintenant la fermeture conditionnelle
(`hBudgetCloses`), l'équivalence (`hBudgetIff`), la réfutation par un suivant hors ligne (`hOffRefutes`), l'identité de
décomposition (`hSplit`) et la finitude de la part basse (`hLowFinite`). Aucun de ces faits ne produit `B_H` : l'identité exprime la
somme des suivants comme reste exact moins une somme finie, et la seule borne compilée du reste exact est linéaire
(`smoothedRemainder_linear_growth`) ; la part basse n'est pas à l'échelle de la ligne tant que ses membres ne sont pas en ligne.
Par l'équivalence, dériver `B_H` à la hauteur du zéro engagé, c'est dériver que tous les zéros plus hauts sont en ligne. Aucune
sonde séparée n'est créée (règle de l'auteur) : le but et son contexte sont ceux du build principal.

Première flèche non démontrée : depuis l'identité arithmétique exacte, la somme signée de tous les zéros suivants reste
uniformément sous un multiple de `√x`.

## 7. Réduction au cas bas et impacts comparés sous la ligne / au-dessus (2026-10-05)

Pour le successeur immédiat du zéro engagé, le côté haut est exclu (`passage_entry_radial_le_half`, portée : le membre atteint par ce
passage, pas son miroir). Le build principal est réduit au seul cas restant : `hBelow : β_l < 1/2`, but `⊢ False`.

| Lecture | Sous la ligne (successeur) | Au-dessus (son miroir, même hauteur) | Bilan de la paire | Nom |
|---|---|---|---|---|
| Dérive radiale de la tangente | strictement vers l'intérieur | strictement vers l'extérieur | signes opposés | `pointCurve_tangent_radial_sign` |
| Facteur de demi-tour (dilatation) | `< 1` | `> 1` | produit exactement `1` : compensation exacte | `mirror_pair_halfTurn_factor_product` |
| Résidu tangentiel (phase) | `< 0` (retard) | `> 0` (avance) | somme strictement `< 0` : pas de compensation | `changeResidueAt_mirror_sum_neg`, `mirror_pair_changeResidue_sum_neg` |
| Contacts | reculés (facteur `> 1`) | avancés (facteur `< 1`) | produit des facteurs `> 1` ; produit des contacts `>` carré du contact de ligne | `mirror_pair_radialFactor_product_gt_one`, `mirror_pair_contacts_beyond_line` |
| Progression | tout passage qui quitte le successeur garde la hauteur | atteint à hauteur gardée | la hauteur est tenue sur la paire | `vertical_arrival_characterizes` |
| Somme des suivants | lu par la somme signée | lu par la somme signée, au-dessus de l'échelle de la ligne | budget collectif réfuté | `offLine_following_refutes_collectiveBudget` |

Tous compilés sans condition, axiomes `propext`, `Classical.choice`, `Quot.sound`. Portée : ce sont des fonctions de la partie réelle et
de la hauteur seules, vraies pour toute paire miroir de tout monde ; ils ne se contredisent pas entre eux. Le but `False` reste ouvert :
il manque une contrainte effectivement dérivée du zéro engagé et du reste exact que le miroir haut contredirait.

## 8. Route « premier OFF, captivité renouvelée au premier passage de même hauteur » (2026-10-05)

Le théorème principal est déjà la configuration du premier OFF : le prédécesseur est en ligne, le passage avance en hauteur, le
successeur est supposé strictement sous la ligne (`hBelow`), tout passage qui le quitte garde la hauteur (`hBelowKeepsHeight`).

TDD : « les contraintes arithmétiques exactes imposent-elles la captivité au raccord suivant sur ce premier passage de même
hauteur ? » Réponse compilée, en contexte du but (`hFirstHorizontal`), dès la hauteur 2 : la transition première exacte y existe
avec tous ses champs (`sameHeight_exactPrimeTransition_reversed`) ; la captivité locale y est FAUSSE par calcul, l'énergie au premier
partagé est strictement renversée (`sameHeight_local_budget_refuted`) ; elle équivaut à la grille du successeur non translatée
(`renewed_captivity_iff_no_translation`). Statut : la captivité n'est pas « indérivable faute de données », elle est réfutée par les
données mêmes du passage. La dériver dans le cas bas revient à dériver `False` : c'est le but affiché, pas une obligation nouvelle.
Hypothèse manquante : aucune donnée du raccord (rang, premier partagé, poids, transport) ne distingue ce passage d'un passage
permis ; il faudrait un fait qui ne soit pas une fonction des deux membres du passage.


## 9. Les deux zéros suivants : premier zéro bas, second zéro de même hauteur (auteur, 2026-10-05 ; corrigé après revue le même jour)

Énoncé de l'auteur testé : « le premier zéro OFF est toujours transparent ; seul le second le trahit : sens inversé des contacts,
même Tour réutilisée ». Fenêtre `e → l → s → b`, jamais le seul zéro suivant.

Compilé (axiomes `propext`, `Classical.choice`, `Quot.sound`), en contexte du but (`hFirstTransparent`, `hSecondZero`, et la fenêtre
INSTANCIÉE : `s`, `hSecondHeight`, `hSecondConsecutive`, `hSecondWindow`, le second zéro existant par `exists_fiberSuccessor`) :

| Fait | Nom |
|---|---|
| Premier zéro bas, au raccord qui l'atteint (hauteur ≥ 2) : transition première exacte entière, captivité tenue | `translated_arrival_complete_and_captive` |
| Le passage qui quitte le premier garde la hauteur ; le second est strictement à droite | `vertical_arrival_characterizes`, `horizontalPassage_radial_lt` |
| Le second est au plus à la position réfléchie du premier : `β_l < β_s ≤ 1 − β_l`, `T_s = T_l`. NON démontré : qu'il est le miroir, qu'il est au-dessus de la ligne (un membre peut être intercalé) | `second_zero_radial_le_mirror` |
| La Tour du second est une Tour DISTINCTE : même intervalle logarithmique, contacts translatés, tous en deçà (pas « la même Tour ») | `sameHeight_successor_translates_inward` |
| La Tour du second dépasse celle du premier en des premiers arbitrairement grands | `horizontal_escape_at_prime` |
| SOUS CONDITION que le passage quittant le second avance en hauteur : second strictement au-dessus de la ligne ; rayon normalisé du premier décroissant, du second croissant ; le zéro atteint ensuite ne dépasse pas la ligne | `junction_horizontal_vertical`, `pair_radius_senses_inverted`, `passage_entry_radial_le_half` |
| Réunion | `second_zero_window` |

`hNoBudget` signifie seulement : cas bas ⟹ négation du budget collectif. La notion de budget n'est pas réfutée ; pour conclure il faut
une contrainte ACQUISE incompatible avec cette conséquence.

E172 corrigée (`experiments/e172_second_off_zero_window.py`, 4 s, 300 zéros publiés, x ≤ 10⁷, fenêtres de 4, 6, 12 zéros, départs 1, 10,
50, 100, 200). Corrections : premier partagé = `p_min(départ) = Occ(arrivée)` (était décalé d'un rang) ; variante S3 ajoutée (second
seul à la MÊME hauteur que le premier seul) ; conclusions sur la fenêtre et sur le poids exact réécrites.

- Raccord qui atteint le premier : du côté < 1 comme un zéro en ligne (0/15 renversé), valeur différente (médianes 0,75 ; 0,57 ; 0,19 contre 0,99).
- Raccord premier → second : renversé 15/15 (médianes 1,7306 ; 2,9950 ; 26,8661 pour β = 0,45 ; 0,4 ; 0,2) ; jumeaux en ligne : 1,0000.
- Décalages des contacts du premier et du second : signes opposés, grandeurs proches mais non exactement égales (écart relatif 2·10⁻⁶ à 1,4·10⁻⁵, l'arctangente n'est pas linéaire). Exposants de dérive radiale opposés pour une paire miroir ; amplitudes non égales.
- Sens de traversée au contact : identique pour tous (dérivée en logarithme de l'abscisse ; en abscisse, même signe, facteur positif).
- Fenêtre : le produit cumulé des rapports DÉPEND de la longueur (médiane OFF 1,667 ; 0,951 ; 0,879 pour 4, 6, 12 membres ; réel 0,973 ; 0,954 ; 0,882), les rapports des passages conservés ne changent pas. Ce n'est pas une loi de compensation : le produit multiplie des rapports lus à des premiers différents. L'indépendance du résidu à la fenêtre est construite (seules deux positions sont modifiées) ; l'effet collectif d'une fenêtre longue n'est pas testé.
- À la même hauteur (P contre S3), effet relatif au niveau de troncature : premier seul 0,44 ; 0,70 ; 1,05, second seul 0,81 ; 2,37 ; 50,4 (x ≤ 10⁷) ; le premier est plat en x, le second grandit (β = 0,2 : 4,4 ; 14,9 ; 50,4). Le contraste tient au côté, pas à la hauteur. Le premier seul reste mesurable.
- Monde témoin (paire à une même hauteur) : même contraste (0,21 contre 0,73).
- Le côté premiers LIT les poids exacts (reste calculé depuis `Λ(n)`). Ce qui n'est pas certifié : que le spectre hypothétique modifié reproduise l'identité arithmétique exacte ; l'écart mesure une perturbation sur grille finie, il ne démontre pas l'impossibilité d'une compensation par la queue au-delà du 300e zéro.

Statut : le but `False` reste ouvert. Les théorèmes décrivent les conséquences du cas bas ; aucun n'est une contrainte acquise que ces
conséquences contredisent.

## 10. Audit de E118, E163b, E172 contre le cas bas ouvert (2026-10-05)

Question : les observations de E118, E163b et E172 fournissent-elles une contrainte arithmétique démontrable qui contredit le cas bas
(`hBelow : rZeroRadialPosition p.zLaterMember < 1 / 2 ⊢ False`) ? Réponse : non. Détail ci-dessous ; rien de ce qui précède n'est effacé,
les corrections sont consignées ici.

### 10.1 Portée exacte des hypothèses du but (vérifiée dans le code)

| Hypothèse | Ce qu'elle dit exactement | Ce qu'elle ne dit pas |
|---|---|---|
| `hLe` | `β ≤ 1/2` pour LE membre atteint par CE passage où la hauteur avance (`passage_entry_radial_le_half p hHeightAdvances` : il est le premier de sa fibre de hauteur) | Rien sur son miroir ni sur aucun autre zéro. Le miroir haut n'est pas interdit par `hLe` : il n'est pas atteint par un passage où la hauteur avance. |
| `hSecondConsecutive` | `PZeroMembersConsecutive l s` : `s` est le successeur immédiat de `l = p.zLaterMember` (aucun membre entre eux), obtenu par `exists_fiberSuccessor` ; `hSecondHeight` : même hauteur | Pas que `s` est le miroir de `l`. |
| `hSecondWindow` | passage `l → s` de même hauteur ; `β_l < β_s ≤ 1 − β_l` ; même intervalle logarithmique ; contacts de `s` tous en deçà ; dépassement de la Tour de `l` par celle de `s` en des premiers arbitrairement grands ; et, SI un passage quittant `s` avance en hauteur, `β_s > 1/2` | Une borne sur `β_s`, pas une identification au miroir ; `β_s > 1/2` seulement sous condition. |
| `hBudget` | `Antitone followingBudget` : la somme des MODULES des poids au-dessus de `H` ne croît pas avec `H`. Définition et monotonie. | Ce n'est pas le budget collectif. `CollectiveBudget H` (borne `C√x`, `C > 0`, de la somme SIGNÉE) n'est en contexte que comme antécédent (`hBudgetCloses`, `hBudgetIff`) et sous négation (`hNoBudget`). |
| `hFirstHorizontal` | pour tout passage `q` quittant `l`, dès la hauteur 2 : `¬ LocalCaptivity q`, c'est-à-dire que la Tour du membre atteint par `q` dépasse celle de `l` au premier attendu de `l` | Aucune captivité n'est affirmée en contexte pour ce raccord. |

Graphe des dépendances. Acquis sans le cas bas : faits du zéro engagé (`hOnE`, `hOriginSymE`, `hMirrorE`, `hHalfTurnE`), faits vrais pour
toute partie réelle (`hRoom`, `hNest`, `hPrimeGaps`, `hPairMidpoint`, `hHalfTurn`, `hSharedPrime`, `hRank`, `hNextPrime`, `hStepIff`,
`hTransport`, `hSplit`, `hBudget`, `hLowFinite`, `hLe`). Conditionnels (antécédent non acquis) : `hAllFollowing`, `hFollowingIff`,
`hBudgetCloses`, `hBudgetIff`, `hOffRefutes`. Conséquences de `hBelow` : `hMirrorRadial`, `hMirrorHigh`, `hMirrorHeight`,
`hBelowKeepsHeight`, `hNoBudget`, `hTangential`, `hContacts`, `hDilations`, `hPairExact`, `hContactSign`, `hFirstHorizontal`,
`hFirstTransparent`, `hSecondZero`, `s`, `hSecondHeight`, `hSecondConsecutive`, `hSecondWindow`. Dérivations essayées pour obtenir une
contradiction : (1) `hNoBudget` contre un budget acquis : aucun théorème du dépôt ne conclut `CollectiveBudget` sans supposer tous les
suivants en ligne (`collectiveBudget_of_following_onLine`) ; (2) `hFirstHorizontal` contre une captivité acquise : les seuls théorèmes
concluant `LocalCaptivity` supposent que la hauteur avance, or le passage `l → s` garde la hauteur ; (3) `hLe` appliqué à `s` ou au
miroir : inapplicable, ils ne sont pas atteints par un passage où la hauteur avance ; (4) fibre de hauteur : `l`, `s`, le miroir de `l`
et le miroir de `s` sont à la même hauteur avec des parties réelles compatibles (`β_l < β_s ≤ 1 − β_l`), aucune relation d'ordre
n'est violée. Aucune de ces dérivations n'aboutit.

### 10.2 Reproduction des graphiques et corrections

Commandes : `python3 experiments/e118_full_stage_energy_series_published.py`, `python3 experiments/e163b_three_zeros_on_off_towers.py`,
`python3 experiments/e172_second_off_zero_window.py`, `python3 experiments/e173_off_surplus_audit.py` (24 s, 16 contrôles exécutés).
E118 et E163b se rejouent à l'identique (aucune différence de sortie).

| Expérience | Objet des courbes | Constat de l'audit |
|---|---|---|
| E118 | terme BRUT `x^ρ/ρ`, non normalisé, contribution individuelle, aux contacts PROPRES de chaque Tour ; `φ = arg(β+iT)`, `C_k = exp((φ+kπ)/T)`, `A(k) = C_k^β/‖β+iT‖` | Valeurs reproduites (T = 14,134725) : 0,074649949 ; 0,202954660 ; 0,075421923 ; 0,250461521. Signe au contact `(−1)^k` vérifié et compilé (`zeroTerm_re_at_contact`). Corrections de lecture : les deux courbes sont à des abscisses différentes ; à abscisse commune l'égalité a lieu en `x* = 1,002752` et l'amplitude OFF dépasse dès `k = 0` (le texte dit `k ≥ 1`) ; la grandeur « énergie signée » est `Re(x^ρ/ρ)`, son surplus ALTERNE, seul le surplus d'amplitude est positif. |
| E163b | terme BRUT ramené à `√x`, normalisation propre `‖ρ_ON(T_n)‖` (ou commune `‖ρ_1‖`), individuel et demi-somme de la paire, abscisse commune `u = log x` | Le script calcule la demi-somme avec `1/ρ₊` et `1/ρ₋` et mesure l'écart à `cosh(du)` : 1,5e−4 ; 6,9e−5 ; 4,9e−5 (reproduit), non nul dès `u = 0`. `cosh` n'est exact que sans les dénominateurs. Identité exacte compilée : `‖paire‖² = ‖terme‖² + ‖miroir‖² + 2·Re(x/(ρ(1−ρ)))`, terme croisé `> 0` (`mirror_pair_normSq`, `mirror_cross_re_pos`). |
| E172 | rapports d'énergie BRUTS au premier partagé ; reste LISSE pour le côté premiers | Index audités contre Lean (`Nat.nth Prime 0 = 2`, `Occ(n) = PRIMES[n−1]`, `p_min(n) = PRIMES[n]`, premier partagé du passage `n → n+1` = `PRIMES[n]`) : les trois accès du script sont `PRIMES[n]`. Avant correction 1,7292 ; 2,9900 ; 26,7321 ; après 1,7306 ; 2,9950 ; 26,8661 : aucun côté de 1 ne change. |

### 10.3 Mesures nouvelles (E173, `experiments/e173_off_surplus_audit_output.md`)

- Abscisse commune : identité `‖F_β‖/‖F_{1/2}‖ = ‖1/2+iT‖/‖β+iT‖·x^{β−1/2}` à 1e−14 ; égalité miroir haut / ON de même hauteur en
  `x*` (1,0028 à T_1 ; 1,0000019 à T_300), vérifiée des deux côtés. Miroir haut du successeur contre le zéro ENGAGÉ (hauteurs
  différentes) : égalité en `x** = (‖ρ_w‖/‖ρ_e‖)^{1/d}` ; au premier du raccord suivant le miroir haut dépasse le zéro engagé dans
  10 cas sur 12, pas pour `n = 1`, `d = 0,05` et `0,1` (`x** = 2788` et `52,8` contre le premier 5). Dépassement individuel ÉTABLI,
  jamais INTERDIT par un énoncé démontré.
- Somme collective signée (terme LISSE, celui de `followingSum`), zéro engagé `n = 10`, 5000 zéros, `x ≤ 10¹⁰` : maximum observé de la
  référence 0,00491 (somme des modules 0,01867) ; paire hypothétique `d = 0,1` au successeur : maximum 0,00573 ; 0,00632 ; 0,00917 pour
  les horizons 10⁴, 10⁷, 10¹⁰ ; `d = 0,02` : 0,00555 aux deux horizons (déplacement d'un pic, 0,13 % de la grille au-dessus de la
  référence) ; paire à T_1000 : effet 9e−6. Troncature : écart 300 → 5000 zéros 3,9e−4 ; queue au-delà non certifiée. Précision :
  flottant contre 30 chiffres 7e−17.
- Lien avec les premiers (reste LISSE exact calculé depuis les poids `Λ`) : résidu de reconstruction `≤ 4,3e−5·√M` aux raccords avec
  5000 zéros ; l'effet d'une paire `d = 0,1` au zéro suivant vaut 45 fois ce résidu pour `n = 1`, 3 fois pour `n = 100`, 0,2 fois pour
  `n = 1000`. C'est une vérification de zéros déjà connus en ligne sur une plage finie. Le même contrôle sur le reste BRUT a un résidu
  cent fois plus grand (autre objet, convergence conditionnelle) : aucune borne n'est transportée de l'un à l'autre.

### 10.4 Recherche d'un résultat indépendant de RH

Aucun théorème du dépôt ne conclut, sans supposer la conclusion : le budget collectif à la hauteur du zéro engagé ; la captivité au
raccord qui quitte le membre bas ; une autre propriété que la fenêtre instanciée contredit. `remainder_eq_preceding_add_following` est
une identité ; `collectiveBudget_iff_following_onLine` est une équivalence dont aucun côté n'est acquis.

### 10.5 Compilé dans cet audit (`Terminal/MirrorPairExactSum.lean`, importé par le build principal)

`zeroTerm_re_at_contact`, `zeroPoint_mirrorMember`, `mirror_cross_term`, `mirror_pair_normSq`, `mirror_cross_re_pos`,
`mirror_pair_no_internal_compensation` (axiomes `propext`, `Classical.choice`, `Quot.sound`). En contexte du but : `hPairExact` (la
paire du successeur dépasse chacun de ses deux membres en tout point), `hContactSign` (signe alterné du miroir haut à ses contacts).
Portée : termes BRUTS, paire isolée. Non compilé : le même énoncé pour les termes lissés ; tout énoncé sur la somme avec les autres zéros.

### 10.6 Verdict

- A. Le surplus OFF est correctement calculé comme surplus d'AMPLITUDE (formules, dénominateurs, index vérifiés ; E172 déjà corrigée).
  Sa lecture était trop forte en trois endroits : « énergie » pour une partie réelle qui alterne, comparaison à abscisses différentes
  dans E118, `cosh` sans les dénominateurs dans le libellé de E163b.
- B. Aucun théorème n'exclut une compensation collective à distance finie. Compilé : aucune compensation à l'intérieur de la paire
  (termes bruts) ; et, à l'infini, un suivant hors ligne interdit toute borne en `√x` de la somme. Ce dernier énoncé donne `hNoBudget`
  dans le cas bas ; il ne fournit pas le budget.
- C. La fenêtre instanciée ne contredit aucune hypothèse acquise.
- D. Flèche manquante, inchangée : une borne ACQUISE, sans supposer la position du zéro atteint, de la somme signée de tous les zéros
  au-dessus du zéro engagé par un multiple de `√x` (ou la captivité au raccord qui quitte le zéro atteint, équivalente à la
  conclusion elle-même). Elle doit lire les poids exacts : elle est fausse dans le monde témoin.

## 11. Comptage certifié, Zeta 23, reste exact : ce qui interdit, ce qui détecte, ce qui reste indéterminé (2026-10-05)

Suite de §10 (demande collée du même jour). Sources épinglées : RHV6Fresh à partir de `c6f01105` ; zeta23 =
`anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (toolchain `leanprover/lean4:v4.33.0-rc2`, Mathlib
`51e6992efd06126df61a496bebf8f49482a4e129`), lu, NON intégré à RHV6Fresh ; python-flint 0.9.0 (FLINT/Arb), mpmath 1.3.0 ; hauteurs
`experiments/data/odlyzko_zeros1_first{300,5000}.txt` (table zeros1 d'Odlyzko, 9 décimales, précision annoncée 3e−9 ; sha256 dans
la sortie E174).

### 11.1 Portée de l'exclusion du côté haut (inventaire complet, lecture du code)

Tous les théorèmes qui concluent `β ≤ 1/2` sans hypothèse équivalente à RH se ramènent à `passage_entry_radial_le_half`
(`Terminal/RaccordDetector.lean:53`, hypothèse : la hauteur avance STRICTEMENT sur le passage ; conclusion : l'ARRIVÉE de ce
passage) : `vertical_regime`, `vertical_passage_concurs`, `engaged_step_all_constraints`, `engaged_step_combined`,
`engaged_nested_translation_window`, `engaged_progression`, `engaged_arrival_onLine_iff_radial_floor`, `arrival_radial_ge_one`,
`radial_b`, la sous-clause de `second_zero_window`. Mécanisme commun : un miroir de partie réelle `> 1/2` s'intercalerait entre les
deux membres consécutifs. L'ordre des membres est lexicographique (hauteur, puis partie réelle :
`thm_zeroMemberPrecedes_iff_height_radial_lex`, `rhv3_lean/.../ZeroGapGrammar.lean:99`) et le membre bas précède son miroir
(`mirror_precedes`, `Direct/MirrorCount.lean:135`) : tout passage qui ATTEINT le miroir est de même hauteur, donc aucun de ces
théorèmes ne s'applique au miroir. Les formes universelles (`radial_le_of_remainder_growth`, `mirror_pair_exponent_le` avec
`θ = 1/2`, `underLineScale_exponent_le`, `followingSum_sqrt_iff_following_le_half`, `prisonAtInfinity_exponent_le`,
`inside_field_forces_line`, `prisoner_exponent_le`, `persistent_exponent_le`) ont une hypothèse équivalente à RH ou non dérivée
(borne en `√x`, budget collectif, prison ou champ du premier zéro avec une amorce non compilée). Aucune conclusion `1/2 < β → False`
n'existe. Le seul énoncé universel inconditionnel est l'inverse, `off_lowerSide` : tout membre hors ligne, ou son miroir, est sous
la ligne. Verdict : l'exclusion est LOCALE (arrivée d'un passage où la hauteur avance) ; la composition avec la réflexion ne ferme
rien, puisque la réflexion envoie le membre bas sur un membre atteint à hauteur égale.

### 11.2 Ce que zeta23 démontre (énoncé → information → absence → rapport au but)

| Composant (fichier:ligne, rév. `fbdc36bb`) | Information apportée | Information absente | Rapport au but |
|---|---|---|---|
| `two_thirds_simple_on_critical_line` (`Challenge.lean:142`) : `∀ ε>0, ∃ T₀, ∀ T ≥ T₀, (2/3 − ε)·Ncount T (2T) ≤ N0simple T (2T)` ; variantes cumulatives `(0,T]` | proportion asymptotique de zéros SIMPLES sur la ligne (numérateur : points distincts ; dénominateur : avec multiplicité) | aucun zéro individuel ; `T₀` non explicite ; jusqu'à environ 1/3 de la masse sans contrôle | n'exclut aucune paire ; ne porte ni sur le premier zéro ni sur une fenêtre |
| `two_thirds_on_critical_line`, `five_sixths_distinct` (l.131-158) | proportion de points distincts sur la ligne ; proportion de points distincts | idem | idem |
| constantes de Montgomery–Taylor (l.163-186) : `2 − 1/c₁*` (≈ 0,6725) pour N0star et N0simple, `(3 − 1/c₁*)/2` (≈ 0,836) pour Ndist | proportion asymptotique sur des fenêtres `[T, 2T]` ou `(0, T]` | ≈ 67,25 % n'est PAS un préfixe de zéros ordonnés ; les zéros non couverts ne sont pas déclarés hors ligne | aucune |
| Fenêtre finie, premier zéro, liste exhaustive | aucune (recherche « gram, turing, platt, 14.13, odlyzko » : rien ; tout énoncé est `∃ T₀, ∀ T ≥ T₀`) | — | zeta23 ne certifie ni le premier zéro ni une fenêtre ; rien ne lui est attribué ici |
| Côté premiers : formule explicite de Weil `EF_lit_zetaZeroConfig` (`Zeta23/WeilEF/Main.lean:270`, inconditionnelle), `Λ` via `−ζ'/ζ = Σ Λ n^{−s}` ; traces de la matrice de Gram de bande `λ < 1` bornées par Chebyshev–Mertens (ΣΛ, ΣΛ², ΣΛ²/n), Montgomery–Vaughan (terme hors diagonale `PPOffDiag` : couples de premiers `n ≠ m`, PAS des zéros hors ligne) et Stirling | des bornes de traces de formes quadratiques construites sur les poids exacts | aucune information de signe sur un zéro donné | même famille d'objets que le reste exact de RHV6 (formule explicite, poids exacts) ; bornes en moyenne, pas en un point |
| Bilan zéros (`ZeroSide.lean:140-145`, `posIndex_blockA_le`, `rank_trace_mult_k_le`, `hatAz_mult2`) : une paire `{ρ, 1 − ρ̄}` de même ordonnée coûte autant qu'elle pèse (contribution nette 0, déduction de la lecture) ; un zéro simple en ligne laisse 1, seule quantité minorée | la proportion vient d'un excédent des zéros simples en ligne | aucune pénalité nette d'une paire hors ligne | c'est la perte qui donne une proportion et non une exclusion |
| `lemmaR_tight_two` (`ZeroSide/TightMult.lean:114`) : le certificat ne peut pas séparer un zéro double en ligne d'une paire hors ligne de profondeur tendant vers 0, et aucune inégalité ne consommant que ces quantités ne l'améliore | limite démontrée de la méthode | — | toute voie qui ne lit que ces quantités est aveugle au cas bas |
| `zeta_local_zero_count` (`RvM/LocalCount.lean:266`) : `∃ A₀ ≥ 1, ∀ t, Ncount t (t+1) ≤ A₀ log(|t|+3)` ; `rvM_main` (Riemann–von Mangoldt, `RvM/MainTerm.lean:482`) | majorations du nombre de zéros par bande de hauteur 1 | aucune position radiale ; `A₀` non explicite | majore le nombre de membres d'une fibre, ne le réduit pas à un |
| `zeta_reflect_zero`, `zeta_mult_reflect` (`ZetaReflect.lean:278, 314`, déjà portés dans RHV6Fresh) | réflexion et multiplicité égale | — | utilisés (multiplicité égale : le facteur commun `c` de 11.6) |

Aucune hypothèse non déchargée dans les 17 énoncés de tête (`paperInputs_zeta`, `AUDIT.md` : axiomes standard) ; seule exception,
hors des énoncés de tête : `PairCeiling` sous l'hypothèse affichée `EnclOK`. Information NOUVELLE pour notre but : aucune
contrainte sur un zéro donné ; une information de méthode, démontrée : les bornes de traces sur les poids exacts sont aveugles à la
différence paire hors ligne / zéro double en ligne.

### 11.3 Exhaustivité des 300 (et 5000) premiers zéros : certifiée sous la coupure (E174)

Méthode, indépendante de RH : (i) signe de la fonction réelle `Z(t) = e^{iθ(t)} ζ(1/2+it)` en arithmétique d'intervalles (Arb,
128 bits) aux points séparateurs `10`, milieux des hauteurs publiées, `T_cut = (γ_N + γ_{N+1})/2` ; chaque changement de signe
certifié donne un zéro d'ordre impair SUR la ligne ; (ii) comptage total `N(T_cut)` avec multiplicité dans toute la bande
`0 < Re < 1`, `0 < Im ≤ T_cut`, par `arb.zeta_nzeros` (méthode de Turing). Résultats : N = 300, `T_cut = 543,0857` : 300
changements de signe certifiés, `N(T_cut) = 300` exactement ; N = 5000, `T_cut = 5448,3852` : 5000 et 5000. `Z(T_cut) ≠ 0`
certifié ; aucun zéro sous `Im = 10`. Donc sous `T_cut`, les N zéros sont tous simples et sur la ligne, et la liste est
exhaustive : aucun zéro hors ligne, aucun zéro multiple, aucun zéro omis. Les hauteurs d'Odlyzko servent seulement de points
d'échantillonnage (écart aux zéros isolés par Arb ≤ 2,9e−9). Portée : résultat FINI, calcul d'intervalles hors Lean, rien au-delà
de `T_cut`.

### 11.4 Marge d'insertion (A) et marge de détection (B)

A. Comptage (sous `T_cut`) : ajout d'une paire → total N+2, changements N ; remplacement d'un zéro en ligne par une paire → N+1,
N−1 ; déplacement conservant le total (deux zéros en ligne fusionnés en une paire) → N, N−2 ; zéro rendu double → N, N−2. Toutes
contredisent « total = changements = N » : interdites sous `T_cut`. Au-delà : rien.

B. Reste exact (objet LISSÉ `A(x) = Σ_{n<x} Λ(n)(1 − n/x) − fond`, formule explicite `A = −Σ_ρ m x^ρ/(ρ(ρ+1))`, termes triviaux et
constantes dans le fond, `A` continu). Erreur CERTIFIÉE de la reconstruction par les N zéros certifiés : la queue au-dessus de
`T_cut` n'est connue que par `0 < β < 1`, d'où `|A − R_N| ≤ x·ε_N`, `ε_N = Σ_{γ>T_cut} 2m/|ρ(ρ+1)|`, majoré par sommation
partielle et la borne de Rosser (1941) : `ε_300 ≤ 3,22e−3`, `ε_5000 ≤ 4,54e−4`. Détection garantie d'une perturbation `Q` :
`|A − R_N − Q| > x·ε_N` en un `x`. Mesuré (x ≤ 10⁷, 4000 points) :
- la détection garantie a lieu aux PETITES abscisses, pour des perturbations BASSES : avec N = 5000, jusqu'à `T ≈ 76` (ajout),
  `≈ 53` (remplacement), `≈ 79` (déplacement), pratiquement indépendamment de `d` (y compris `d = 0`, zéro double) ; avec N = 300,
  jusqu'à `T ≈ 25, 14, 33`. Elle lit le nombre et la position des termes bas, pas la partie réelle ; ces hauteurs sont déjà
  exclues par le comptage (seconde lecture, indépendante, par les premiers) ; arithmétique flottante contrôlée (mpmath, écart
  2e−13), pas en intervalles ;
- au-delà de `T_cut` (paires à `T_cut + 1`, `+ 100`, `+ 10⁴`, `d` jusqu'à 0,45) : aucune détection garantie ;
- détection NUMÉRIQUE (rapport à un résidu OBSERVÉ, non certifié) : parmi `d ∈ {0,02 ; 0,1 ; 0,3}`, `d = 0,02` suffit jusqu'à
  `n = 100`, `d = 0,3` à `n = 1000` et `4999` ; le rapport dépend de la troncature (remplacement, n = 10, d = 0,1 : 25 ; 81,8 ; 470
  pour N = 300, 1000, 5000) : aucune valeur de certificat. Les rapports 45 / 3 / 0,2 de E173 §6 sont
  de ce type : écarts numériques, non certifiés.
Aucune « marge de manœuvre OFF » universelle n'est déduite d'une grille finie.

### 11.5 Obligations précédentes (§10)

| Obligation | Statut |
|---|---|
| Indexation des premiers partagés et attendus (E172 ; `Occ(n) = PRIMES[n−1]`, `p_min(n) = PRIMES[n]`) | terminé (§10.2) |
| Contacts propres contre abscisse commune (E118) | corrigé : légendes du script et figures (`e118_*_corrige.png`, sortie `*_output_corrige.md`), versions antérieures conservées |
| Normalisation propre contre normalisation commune (E163b) | vérifié (deux panneaux nommés) ; inchangé |
| Signes alternés contre amplitudes | corrigé (« énergie signée » → partie réelle au contact propre, `(−1)^k` × amplitude) ; compilé `zeroTerm_re_at_contact` |
| Dénominateurs exacts des paires (E163b) | corrigé : légendes « cosh(du) » marquées « forme sans dénominateurs, écart mesuré » (`e163b_*_corrige.png`) ; compilé `mirror_pair_normSq` |
| Dépendance des produits cumulés à la longueur des fenêtres (E172) | terminé (§9, sans valeur de loi de compensation) |
| Sensibilité à la troncature et à la résolution | terminé (E173 §5e-5f, E174 §3b) |
| Signature de « la paire dépasse chaque membre en tout point » | vérifiée : NORME (stricte), tout `x > 0` (axe positif entier, `0 < x < 1` compris), tout zéro supérieur (`T > 0`), `0 < β < 1` tiré des théorèmes ; termes bruts |
| Fait analogue pour les termes lissés | compilé (11.6) |
| Énoncé collectif (paire + autres zéros) | ouvert ; aucun transfert de borne |

### 11.6 Compilé (`Terminal/MirrorPairExactSum.lean`, build principal)

`mirror_cross_term_smoothed` (produit du terme lissé par le conjugué du terme lissé miroir `= x/(w(w+2))`, `w = ρ(1−ρ)`),
`mirror_cross_re_pos_smoothed` (partie réelle `> 0` pour tout zéro supérieur et tout `x > 0`),
`mirror_pair_no_internal_compensation_smoothed` (pour tout facteur commun `c ≠ 0`, en pratique `−m`, la norme de la paire lissée
dépasse strictement celle de chacun de ses membres) ; axiomes `propext, Classical.choice, Quot.sound`. Mis en contexte du but :
`hPairSmoothed`. Non formalisé : la certification numérique du comptage (calcul Arb hors Lean) et la détection par le reste.

### 11.7 Recherche de la flèche : chaînes de dépendances et premier antécédent non démontré

| Piste | Chaîne | Premier antécédent non démontré |
|---|---|---|
| Budget collectif | budget au-dessus du zéro engagé → tous les suivants en ligne (`collectiveBudget_iff_following_onLine`) → contredit `hBelow` | le budget lui-même (pour toute hauteur : équivalent à « tous les membres au-dessus en ligne ») |
| Captivité au raccord sortant | captivité du passage qui quitte le membre bas → grille non translatée (`renewed_captivity_iff_no_translation`) → contredit `hFirstHorizontal` | la captivité sur un passage de même hauteur (calculée FAUSSE dès la hauteur 2 dans le cas bas) : équivalente à la conclusion |
| Comptage dans la fibre | une seule annulation à la hauteur du successeur → pas de miroir distinct → contredit `hMirrorHigh` | l'unicité du membre dans la fibre à une hauteur quelconque (certifiée sous `T_cut` seulement, numériquement ; pour toute hauteur ⟺ RH, `riemannHypothesis_iff_fibres_singleton`) |
| Forme utilisée par zeta23 (formule explicite de Weil, traces de Gram) | bornes de traces → proportion ≥ 2/3 | aucune chaîne vers une exclusion : la méthode est démontrée aveugle paire / double (`lemmaR_tight_two`) ; la positivité de la forme de Weil pour toutes les fonctions test (critère de Weil, littérature, non compilé) équivaut à RH |

Aucune de ces pistes n'est « l'unique voie » ; aucune n'est acquise.

### 11.8 Verdict

1. L'exclusion `β > 1/2` est LOCALE : arrivée d'un passage où la hauteur avance strictement ; elle ne s'applique pas au miroir.
2. Les 300 (et 5000) premiers zéros forment une liste exhaustive certifiée sous leur coupure (comptage total = changements de signe),
   par calcul d'intervalles hors Lean ; rien au-delà.
3. Interdites par le comptage sous la coupure : ajout d'une paire, remplacement d'un zéro en ligne par une paire, déplacement
   conservant le total, zéro rendu double. Au-delà : aucune.
4. Détectables par le reste exact avec erreur garantie (majorant inconditionnel de la queue) : les seules perturbations basses
   (jusqu'à `T ≈ 53–79` avec 5000 zéros certifiés), déjà exclues par le comptage ; au-delà de la coupure, aucune.
5. Zeta23 n'apporte aucune contrainte sur un zéro donné ; il apporte une limite démontrée : les bornes de traces sur les poids
   exacts ne séparent pas une paire hors ligne d'un zéro double en ligne.
6. Aucune flèche ne ferme. Restent non démontrés, chacun comme premier antécédent de sa chaîne : le budget collectif au-dessus du
   zéro engagé, l'unicité du membre dans la fibre de hauteur du successeur, la captivité au raccord sortant (équivalente à la
   conclusion).

## 12. Fenêtres de 12, 24 et 36 transitions ; corrections de E174 (2026-10-05)

Point de départ : rapport `e961c04f`, signature 9957235d9c1c, but `hBelow → False`. Les §10 et §11 sont conservés tels quels ; ce
paragraphe corrige leurs conclusions là où elles étaient trop fortes. Scripts : `experiments/e174b_certified_tail_and_detection.py`
(1 min, 7 contrôles, python-flint/Arb), `experiments/e175_windows_12_24_36.py` (3 s, 16 contrôles, numpy) ; données
`data/e174b_detected_indices.csv`, `data/e175_windows_<N>_m<m>.csv` (une ligne par fenêtre).

### 12.1 Corrections de E174

| Conclusion de E174 (§11.4) | Correction |
|---|---|
| `ε_N` « certifié » par quadrature mpmath × 1.000001 | Le facteur n'est pas une preuve d'erreur. Remplacé par une formule fermée (sommation partielle, Rosser 1941, intégrales exactes, `log log t ≤ log log T + log(t/T)/log T`), évaluée en Arb : `ε_300 ≤ 3,2219025360e−3`, `ε_5000 ≤ 4,5392781993e−4` (≥ la quadrature, écart relatif 5e−6 et 2e−7). Seul ingrédient non démontré ici : le théorème de Rosser (littérature). |
| Détections « garanties » en arithmétique flottante | Recertifiées en intervalles Arb sur toutes les quantités : somme des premiers, fond (`ζ'/ζ(−1)` par série Arb, série triviale tronquée avec reste majoré), zéros (boules `acb.zeta_zeros`), termes hypothétiques, `ε_N`. Tous les criblages positifs sont recertifiés (0 échec). |
| « Seuil » de détection (dernier indice détecté parmi `n < 160`) | Examen complet `1 ≤ n ≤ N − 1`. Ensembles certifiés, N = 5000 : ajout 1–19 (d = 0 ; 0,1), 1–20 (0,3) ; remplacement 1–11, 1–12 ; déplacement 1–12, 14–18, 21 (d = 0 ; 0,1), 1–18, 21, 25 (0,3). Le déplacement n'est PAS un segment initial : aucun seuil. N = 300 : déplacement 1–3, 5. |
| « Aucune détection au-delà de la coupure » | Test NON CONCLUANT (flottant, grille) ; ne signifie ni existence ni « compensation possible ». |
| `lemmaR_tight_two` : « méthode aveugle paire / double » | Portée exacte : égalité, sur des matrices explicites, de la quantité `4·tr − ‖·‖²` de SON certificat (trace, norme de Frobenius, indice positif) : un zéro double en ligne et un bloc de paire serrée y ont le même poids `4`. Obstacle pour les quantités de ce certificat, pas impossibilité pour une méthode enrichie. |
| Unicité et simplicité | Deux propriétés : simplicité = multiplicité 1 (violée par un zéro double, un seul point) ; unicité du point dans la fibre = au plus un zéro par hauteur (violée par une paire, deux points simples). Le certificat de comptage donne les deux sous `T_cut`, comme deux conclusions distinctes. Le rang du code (`nZeroSourceIndex`) compte des POINTS ; `N(T)` compte avec multiplicité. |

Les certifications de comptage (Arb, §11.3) et les calculs de détection (criblage flottant, recertification Arb ponctuelle) restent
dans deux sections séparées des sorties.

### 12.2 Fenêtres : définitions et index

`m` transitions = `m + 1` membres `n, …, n + m` = `m + 1` occurrences. Membre `k` (1-based) : `nZeroSourceIndex = k − 1`,
`Occ(k) = fnPrimeAtRank(k − 1)`, `expectedMinimumPrime(k) = fnPrimeSuccessor(k − 1) = Occ(k + 1)` (contrôlé sur 4999 raccords).
Contacts et cellules produits depuis `(β, T)` seuls (`C_k = exp((arctan(T/β) + kπ)/T)`, règle du pivot vérifiée sur tous les
membres). `ΔΘ_j = phaseIncrement = T_j log(p_{r+1}/p_r)` ; `J = interTowerExcess = (T_l − T_e) log(p_{r+2}/p_{r+1})` ; `raccordShift` ;
registre de chaîne, Abel et identité de `J` vérifiés sur toutes les fenêtres (résidus ≤ 3e−11). Fenêtres : 288/276/264 (N = 300),
4988/4976/4964 (N = 5000) pour m = 12/24/36.

### 12.3 Progression première minimale

Compilé (`Terminal/WindowProgression.lean`, 16 théorèmes, axiomes standard) : `g_j + g_{j+1} ≥ 6` pour premiers consécutifs `> 3`
(aucune alternance stricte : 688 écarts 2, 682 écarts 4, 3668 écarts ≥ 6 jusqu'au rang 5041) ; `m` pair `p_{n+m} − p_n ≥ 3m`, impair
`≥ 3m − 1` ; `L(n,m) ≥ log(1 + 3m/p_n)` ; classe d'écart mod 6 = transition de résidus (`2 : 5 → 1`, `4 : 1 → 5`, `0` : même résidu).
Observé (garanti / minimum observé) : m = 12 : 36 / 42 ; m = 24 : 72 / 98 ; m = 36 : 108 / 162. Fenêtres à classes 2/4 strictement
alternées : 16 sur 4986 pour m = 12, aucune pour 24 et 36.

### 12.4 Hauteur et phase

Écart de hauteur total (N = 5000) : m = 12 : 10,30 / 12,24 / 45,21 (min / médiane / max) ; m = 24 : 21,25 / 24,40 / 74,67 ; m = 36 :
32,26 / 36,59 / 102,09 ; hauteurs distinctes toujours `m + 1`, `H = 0` (certifié sous `T_cut`). Rapporté à la densité moyenne
`2πm/log(T/2π)` : médiane 0,99–1,00 au-dessus de T = 100, plus bas en dessous (0,84–0,92) ; c'est une valeur moyenne, pas une borne.

| Lien | Statut |
|---|---|
| progression première `≥ 3m`, plancher logarithmique | théorème |
| `ΔΘ_j > 0` à hauteur constante | théorème (`sameHeight_phase_progress`) ; progression de PHASE |
| `Σ ΔΘ ≥ c·log(1 + 3m/p_0)` pour toute hauteur minimale `c` | théorème (`chain_phase_window_floor`) |
| registre, Abel, `J` | identités, vraies pour toute suite de hauteurs |
| progression de hauteur exigée par les premiers | AUCUNE : la suite constante satisfait l'identité (`window_abel_all_sameHeight`) |
| densité moyenne de hauteur | résultat expérimental |
| bornes de comptage (12.6) | littérature (Rosser), non compilé |
| « en régime ON, les écarts ne sont atteints que par la hauteur » | obligation ouverte |

### 12.5 Insertions hypothétiques (configurations, pas spectres de zêta)

Rangs et premiers réaffectés après tri lexicographique ; aucune ancienne correspondance conservée. Ajout isolé (d = 0,1) au milieu
d'une fenêtre : `H = 1`, déficit de hauteur 3,31 / 2,99 / 2,02 (n = 100 ; m = 12/24/36), 2,38 / 1,89 / 2,43 (n = 3000). Trois
ajouts : déficit 6,8 à 9,8 selon la répartition (groupés ou répartis, une partie poussée hors de la fenêtre). Déplacement (comptage
avec multiplicité conservé) : `H = 1` ou `3`, déficit nul (extrémités inchangées). Progression première de la fenêtre inchangée
dans tous les cas ; Abel exact dans tous les cas. `d → 0` : `H` et déficit indépendants de `d > 0` ; raccord du passage de même
hauteur `∝ d` (7,8e−4 à d = 0,1 ; 7,8e−9 à d = 1e−6) ; somme des raccords indépendante de `d` (télescopage des termes radiaux
intérieurs) ; à `d = 0` la paire est UN point double (rang + 1 au lieu de + 2) : discontinuité du compte des points, pas du
comptage avec multiplicité. Aucune quantité du registre ne fixe un déficit maximal ni un écart minimal `d`.

### 12.6 Contrat A / B / C

Sur les mêmes objets (m + 1 points d'une fenêtre), avec `E(t) = 0,137 log t + 0,443 log log t + 1,588` (Rosser 1941, littérature) :
A (progression minimale) `b − a ≥ 2π(m + 1 − E(a) − E(b))/log(b/2π)` ; B (compensation maximale d'un passage vertical)
`b − a ≤ 2π(E(a) + E(b))/log(a/2π)` ; fibre `≤ K = ⌊2E(T)⌋` points. Les fenêtres certifiées respectent A et B. D'où, démontré
modulo Rosser : `H ≤ (m + 1) − ⌈(m + 1)/K⌉` et `(m − H)·B ≥ A`. À T = 5448 : K = 7, H ≤ 11 / 21 / 31 pour m = 12 / 24 / 36 ; à
T = 10¹⁰ : K = 12. C'est une LIMITATION DE FRÉQUENCE ; elle exclut une fibre de plus de K points, pas des insertions répétées dans
des fibres distinctes, jamais une paire isolée (`H = 1`). Zeta23 compilé (`zeta_local_zero_count_explicit`) : `K ≤ 5,4·10⁸ log(T + 3)`,
même nature, plus faible. Aucune borne n'est compilée dans RHV6Fresh.

### 12.7 Zeta 23

Comptage : bornes locales (`zeta_local_zero_count`, `_explicit`) et asymptotique de `N(T, 2T)` (`rvM_main`, conditionnelle aux faits
Γ dans son énoncé) : limitation de fréquence, pas d'information sur un zéro donné. Traces et multiplicité : proportions asymptotiques
(2/3 simples en ligne ; 0,6725 ; 5/6 distincts) sur `[T, 2T]`, `T ≥ T₀(ε)` non explicite : aucune fenêtre de 12 à 36 transitions,
aucun préfixe ordonné. Ce que les fenêtres portent et que le certificat serré de `lemmaR_tight_two` ne voit pas : l'ORDRE des
membres et leur rang (donc l'occurrence première et la position radiale dans la Tour), la position radiale `β` elle-même (le
certificat ne voit que des multiplicités et des blocs), le compte des POINTS distinct du comptage avec multiplicité (discontinuité
en `d = 0`, 12.5). Aucune de ces informations ne fournit, ici, une borne sur la compensation cumulée.

### 12.8 Verdict

- Progression minimale démontrée : PREMIÈRE (`p_{n+m} − p_n ≥ 3m`, `m` pair ; plancher logarithmique) et de PHASE
  (`Σ ΔΘ ≥ c·log(1 + 3m/p_0)`), compilées. De HAUTEUR : aucune par l'identité d'Abel et les bornes premières PRISES SEULES (compilé : la suite constante satisfait le
  registre ; portée corrigée au §13.6 : ce n'est pas une réfutation de toute combinaison de contraintes) ;
  par le comptage, `T_{n+m} − T_n ≥ 2π(m + 1 − 2E)/log(T/2π)` (Rosser, non compilé).
- Compensation maximale démontrée : par passage vertical, `≤ 2π(E(a) + E(b))/log(a/2π)` (Rosser, non compilé) ; rien dans Lean.
- Passages de même hauteur réellement exclus : tous sous `T_cut` (certificat Arb, hors Lean) ; au-delà, seulement les fibres de plus
  de `⌊2E(T)⌋` points (Rosser) ; dans Lean, aucun.
- Paire isolée : non traitée par l'exclusion (H = 1 toujours permis au-delà de `T_cut`).
- Flèche ouverte : un fait acquis, sans supposer la position du zéro atteint, que la présence du successeur strictement sous la
  ligne contredirait ; les fenêtres n'en fournissent pas (leurs faits premiers et de phase sont vrais pour toute suite de hauteurs
  et toute position radiale).

## 13. Inversion tangentielle autour de 2 et 3 ; amorce certifiée des trois premiers zéros ; audit du rapport §12 (2026-10-05)

Script : `experiments/e176_tangential_inversion_2_3.py` (python-flint/Arb, numpy ; 15 contrôles ; quelques secondes ; venv avec
python-flint), sortie `e176_tangential_inversion_2_3_output.md`, données `data/e176_scan_cells.csv` (102 bandes),
`data/e176_prime_contact_windows.csv`, `data/e176_zeros_filters.csv`, `data/e176_first_three_zeros_certificate.csv`. Lean :
`Terminal/TangentialInversion.lean` (12 théorèmes, axiomes standard), `hInversion` en contexte du but.

### 13.1 Définitions du dépôt
Phase `φ = arctan(T/β)` ; `C_k = exp((φ + kπ)/T)` (`contactMinusAt z k`, `contactPlusAt z k = C_{k+1}`) ; cellule `(C_k, C_{k+1}]`,
`k = ⌈(T log q − φ)/π⌉ − 1` (`pivotCoordinate`) ; `pivotCell z` = cellule de `p_min(z) = p_{n(z)+1}` ; `occurrence z = p_{n(z)}` ;
`countedPrime` = dernier premier `≤ C⁺`. `authenticContact` n'existe pas dans le code courant. Trois relations distinctes :
premier DANS une cellule (toujours vrai, une seule cellule, `every_real_in_unique_cell`) ; premier ÉGAL à un contact (une
équation, `contact_eq_iff_phase`) ; premier associé par le RANG (fonction du rang seul).

### 13.2 Balayage, inversion, filtres
| contrainte | candidats avant | après | ce qu'elle élimine | statut Lean |
|---|---|---|---|---|
| domaine `0 < β < 1`, `0 < T ≤ 240` (grille 199 × 24000) | -- | 4 776 000 | -- | -- |
| géométrique : 2 et 3 dans des cellules `k = 0..50` | 4 776 000 | 2 893 453 | `T < 2,26` (`C_0 ≥ q`) ou `k > 50` (`T > 147,27` pour 3) ; aucune β | `every_real_in_unique_cell` [C] |
| sélection canonique (règle du pivot) | 2 893 453 | 2 893 453 | rien (cellule unique) | `pivotCoordinate_unique` [C] |
| correspondance première : cellule de 3 dans `]2, 5[` | 2 893 453 | 2 826 897 | cellules qui contiennent 2 ou atteignent 5 | rang → premier [C] ; fenêtre [N] |
| `ζ(β + iT) = 0` (Turing + Backlund + changements de signe, Arb) | région | 102 points `(1/2, T_n)` | tout hors des zéros | hors Lean |
| ζ = 0 et cellule de 3 dans `]2, 5[` | 102 | 51 (rangs 1 à 51) | les zéros dont la cellule de 3 sort de `k ≤ 50` | [N] |

Premier égal à un contact : `β ∈ ]0,1[` ⟺ `arctan T < T log q − jπ < π/2`, fenêtre mince (mesure 2,18 sous `T = 240` pour 2,
1,26 pour 3). 2 et 3 tous deux contacts : `T = mπ/log 1,5` ; toutes les branches valides sous 240 donnent `β > 1` ; aucun zéro.
Inversion : 400 allers-retours exacts en Arb (branche et contact indexé recontrôlés) ; un décalage d'indice garde `β` et `T` mais
change le contact d'un facteur `e^{±π/T}` ; hors branche, `β < 0`. Un premier seulement encadré laisse une région 2D.

### 13.3 Amorce : certificat externe, indépendant de RH
Coupures 14, 17, 23, 28 : `N = 0, 1, 2, 3` (bande critique, multiplicité) par Turing (`arb.zeta_nzeros`) ET par Backlund
(Re ζ certifié > 0 sur `[1/2, 2]`, `|S| < 1/2`, `θ/π + 1` = 0,43247 ; 0,86277 ; 1,96473 ; 3,07813). Changements de signe certifiés de
`Z` : `T_1 ∈ [14,1347251417347 ± 1,2e−14]`, `T_2 ∈ [21,0220396387716 ± 4,8e−14]`, `T_3 ∈ [25,0108575801457 ± 1,8e−14]`. D'où, sous
28 : chacun simple et sur la ligne, aucun zéro hors ligne avant ni entre, aucun autre zéro à leurs hauteurs. Une petite valeur
`|ζ(1/2 + 14,134725 i)| ≈ 1,1e−7` n'est pas un certificat. Certificat EXTERNE (Arb), pas une preuve Lean.
Question d'amorce : les contraintes autour de 2 et 3 RECONNAISSENT une cellule compatible ; elles ne sélectionnent pas le premier
zéro (51 zéros et une région 2D les satisfont ; 2 et 3 ne sont pas des contacts du premier zéro ; à la hauteur `T_1`, aucun
`β ∈ ]0,1[` n'en ferait des contacts). « 3 est le pivot » suppose le rang 0, c'est-à-dire le comptage : circulaire si utilisé avant.
Zeta 23 : `zeta_local_zero_count_explicit` est un majorant local (≈ 1,5·10⁹ en `t = 14`), la forme quadratique (`lemmaR_tight_two`)
ne donne que des proportions sur `[T, 2T]` au-delà d'un seuil non explicite : aucun certificat local supplémentaire.

### 13.4 Engagement et transmission
Existence du premier ON : certifiée (13.3). Engagement : l'inversion rend `(β, T)` ; aucune autre grandeur de Tour n'est acquise
(position de `p_min` dans sa cellule : 0,054 à 0,998 sur les rangs 1 à 15, non conservée ; fenêtre de branche : vraie pour toute
`β` de la bande). Conservation : aucune loi de transport ; l'inversion d'un membre ne lit que ses contacts
(`inversion_reads_own_contacts`) ; deux racines successives ne sont pas une racine déplacée. Exclusion du prochain OFF : sous la
coupure par le comptage ; au-delà, ouverte (but du build). L'amorce ne démontre pas la transmission au-delà de `T_3`.

### 13.5 Bornes de Rosser, dérivées
Théorème 19 (1941, cité, ni Lean ni Arb) : `T ≥ 2`, `|N(T) − F(T)| < E(T)`, `N` avec multiplicité. Fibre : `N(T₀+0) − N(T₀−0) ≤ 2E(T₀)`
(⌊2E⌋ = 5, 6, 7 à `T` = 100, 543, 5448, Arb). A : `m + 1 ≤ N(b+0) − N(a−0)` ⟹ `b − a ≥ 2π(m + 1 − E(a) − E(b))/log(b/2π)`
(`a ≥ 2`, `b > 2π`). B : intervalle sans zéro, `a > 2π` ⟹ `b − a ≤ 2π(E(a) + E(b))/log(a/2π)` (13,15 ; 9,20 ; 6,91 ; observé sur
`[0,8T, T]` : 3,68 ; 2,89 ; 2,28). Statuts : démontré (Rosser + algèbre) ; certifié (colonnes Arb) ; observé.

### 13.6 Corrections du rapport précédent
- « Progression de hauteur réfutée » : `window_abel_all_sameHeight` réfute seulement la déduction depuis l'identité d'Abel et les
  bornes premières seules ; il ne réfute pas une combinaison avec d'autres contraintes (comptage, ordre, poids exacts).
- « 0 criblages flottants positifs recertifiés » était une erreur de rédaction : 173 criblages flottants positifs, 173 recertifiés
  en Arb, 0 échec ; certificats effectifs (boules `|A − R_N − Q|(x*)`, `x* ε_N`, borne inférieure de la marge, minimum 5,1e−6 > 0)
  dans `data/e174b_detected_indices.csv`.
- L'espace restant et l'engagement du régime restent ouverts ; E175 ne les traite pas.

## 14. Décroissance des intervalles, prédicteur sans fuite, fenêtre OFF conjointe, raréfaction première (2026-10-05)

Sources : `experiments/e177_interval_decay_and_off_window.py` (6 s, 12 contrôles PASS ; sorties `e177_*_output.md`,
`data/e177_cells_5000.csv`, `data/e177_windows.csv`, `data/e177_predictor.csv`, `data/e177_off_window_configurations.csv`) ;
`Terminal/WindowFeasibility.lean` (11 théorèmes, axiomes standard, en contexte du but : `hPhaseBand`).

### 14.1 Mesures retrouvées
E093 (8 zéros, largeur `exp(π/T)`), E112 (phase par événement, 300/5000), E113, E151, E165, E085. Aucune expérience intitulée
« décroissance des intervalles » sur 300 zéros n'a été trouvée ; la mesure est refaite (300 puis 5000).

### 14.2 Grandeurs séparées
`ℓ = log(C⁺/C⁻) = π/T` (écart relatif 4e−12) ; largeur ordinaire `C_k(e^{π/T} − 1)` CROISSANTE avec l'indice canonique ;
`log C_k = kπ/T` (rétrécissement, hauteur) `+ φ/T` (translation, phase, seule entrée de `β` dans les contacts) ; rayon
`p^β/|ρ|` (partie réelle et coefficient), absent des contacts. Contacts de même indice ordonnés avec les deux voisins sur 5000.

### 14.3 « Laisser la place »
Tableau des quantificateurs dans la sortie §2 : aucun théorème d'enroulement ne donne une contraction uniforme par passage ; la
contraction du pas est exactement le rapport des hauteurs (`towerPitch_ratio`). Nouveau : emboîtement à tout indice dès
`ΔT·(π + arctan T) ≥ 1`, toutes parties réelles (`windingContact_nested_of_gap`) ; seuil explicite `2kA ≥ T_e`
(`contact_nested_of_height_gap`).

### 14.4 Comptage (Rosser 1941, cité, non compilé)
Inversion : `T_n ∈ [L_n, U_n]` pour les 5000 rangs (rang avec multiplicité ; rang du dépôt ≤ ; égaux sous la coupure certifiée),
largeur ≈ 4E espacements. Fenêtres : contraction garantie seulement pour `m ≥ m*(T)` (4 à `T = 14`, 7 à 5448, 10 à 10⁸) ; aucune
pour `m = 1`.

### 14.5 Prédicteur sans fuite
R et RB (démontrés sous Rosser) : couverture 100 % ; ajustement (rangs 2..2500 → 2501..5000) : 89,4 % à 90 %, 98,4 % à 99 %,
sans valeur de preuve. Phase : région `]arctan T_lo, π/2[`, `β ∈ ]0, 1[` ; aucune entrée autorisée ne fixe `β = 1/2`.
Sensibilité : erreur sur `β` ≈ 12·T² × erreur relative des contacts (indice 5).

### 14.6 Faisabilité conjointe de la fenêtre ON → bas → miroir → suivant
Le membre bas est le minimum de sa fibre, le miroir le maximum ; la consécutivité bas → miroir n'est PAS dérivée (fibre à deux
points) ; intercalation traitée. Pour TOUT `d ∈ ]0, 1/2[` (théorème, pas grille) : contacts, pas, écart de phase miroir
`∈ ]0, 1/T[`, emboîtements avec les deux voisins dès l'écart de hauteur `≥ 1/(π + arctan T)`. Numérique, extrémités de
l'intervalle de phase : emboîtement pour `d → 0` sur 4996/4996 positions dans les trois configurations ; Rosser + comptage ON
certifié : ajout et intercalation exclus aux positions 1..13 seulement, remplacement jamais. Région conjointe NON VIDE ; seule
la liste certifiée exacte (E174, externe, sous la coupure) la vide, pour tout `d > 0`. Contrainte manquante : un fait acquis
qui interdise un passage de même hauteur depuis le membre bas.

### 14.7 Fenêtres 12/24/36 et raréfaction première
Avec une paire insérée, aucune fenêtre ne viole la borne de comptage (marge minimale 2,9) : les voisins compensent. Raréfaction :
écart moyen divergent (littérature), suites sans premier de toute longueur (compilé), `p_{n+m} − p_n ≥ 3m` (compilé, vérifié à
2·10⁷), plancher logarithmique → 0. Elle n'entre dans les Tours que par la phase `T log(p'/p)`, positive à hauteur constante ;
elle n'interdit pas le passage de même hauteur et n'en borne pas la fréquence ; la fréquence est bornée par le comptage seul
(au plus ⌊2E⌋ points par hauteur).


## 15. Les cent trente-six rigidités contre le renouvellement de la contraction (2026-10-05)

Flèche de référence (auteur, mot pour mot) : « Depuis un zéro ON engagé, dériver des contraintes acquises de succession, de raccord et d'enroulement que le passage quittant le membre atteint doit lui aussi monter — sans supposer ce membre ON. » Fermeture déjà disponible ensuite : « Un membre atteint par un passage qui monte et quitté par un passage qui monte est ON. »
(compilé : `junction_vertical_vertical`, rigidité 44). Le facteur de translation égal à un est une caractérisation
équivalente du résultat, pas une hypothèse à introduire ; il ne remplace pas la cible.

Test appliqué à chaque rigidité du maître sémantique §12 (numérotation 1–136 ; la demande en cite 125, la liste en
compte 136, toutes sont classées) : sur la fenêtre « zéro engagé → membre atteint → membre suivant », la rigidité
a-t-elle pour conclusion, seule ou composée avec d'autres de sa classe, que le second passage monte ?

| Classe | Rigidités | Ce qu'elles lisent | Tient à hauteur gardée ? | Porte le renouvellement ? |
|---|---|---|---|---|
| Zéros, ordre, ligne | 1–8 | bande, quatre zéros, miroir, fonction réelle, rang + 1, successeur unique | oui (7 : la hauteur « ne recule pas ») | non ; 6 ne lit que l'intérieur strict d'un passage |
| Tour d'un membre | 9–25 | fonctions de la partie réelle et de la hauteur du membre seul | oui, pour toute partie réelle | non ; 15–17, 23, 25 sont des certificats (lisent la partie réelle, ne la fixent pas) |
| Grammaire première | 26–41, 95–97 | fonctions du rang seul | oui (le rang avance à hauteur gardée) | non (38 : aveugles à la partie réelle) |
| Passages, régimes, raccords | 42–60, 128–131 | régime, raccord, transport, captivité locale | oui : le raccord existe entier à hauteur gardée, transport renversé | 44 est la FERMETURE (suppose le second passage qui monte) ; 48 suppose le membre ON ; 51, 131 : la captivité au second raccord est fausse à hauteur gardée, mais aucun énoncé ne l'exige |
| Formule explicite, unicité | 61–74 | identités collectives, toute position radiale | oui | non ; piste collective mise de côté par l'auteur |
| Marche, taille, exposant | 75–82, 86–94, 127 | réponse collective, croissance du reste | oui avec exposant un ; la taille critique équivaut à la cible | non dérivé ; piste mise de côté |
| Fenêtre, paire contre double, symétries, trajectoire | 98, 105–109, 111–113, 115–117, 119–126 | lectures et certificats d'une paire donnée | oui (105–106 décrivent précisément cette fenêtre) | non |
| Mesures | 37 (partie), 83–85, 99–101, 110, 114, 118 | numérique | — | corrélations mesurées, pas des théorèmes |
| zeta23 | 102–104 | proportions asymptotiques | — | aucun énoncé local |
| Témoins, caractérisations | 132–136 | garde-fous | — | 135–136 : équivalences à la cible |

Résultat : aucune des 136 n'a pour conclusion le second passage qui monte sans supposer le membre atteint ON (48) ou ce
passage lui-même (44). Pour les combinaisons, deux appuis compilés, de portée différente :
- contrats qui ne lisent que parties réelles et hauteurs des trois membres : `renewal_not_forced_by_parameters`
  (`Terminal/OnCrossReadings.lean`) les satisfait tous, pour tout écart à la ligne, à hauteur gardée (première
  contraction, fenêtre de phase, facteur de translation, miroir, contacts en deçà, emboîtement à l'infini, enveloppe du rayon) ;
- contrats de symétrie et d'ordre sans les premiers : `regimeWitness_regime_changes` (un zéro en ligne, puis deux jumeaux).
Ce que ces deux appuis ne couvrent PAS : les combinaisons qui lisent ensemble les positions des premiers ET les poids
exacts (classes « formule explicite » et « taille »). Elles ne sont réfutées par aucun théorème ; c'est la seule
classe d'où le renouvellement pourrait venir, et c'est la piste collective mise de côté.

Trois formulations corrigées (revue de l'auteur) : « un seul paramètre libre » vaut pour la translation des contacts à
hauteur DONNÉE, la hauteur suivante n'est pas déterminée ; « aucune limite basse » signifie : aucune borne radiale
strictement positive, uniforme jusqu'à l'infini, n'est acquise pour un membre bas — des bornes sur un domaine fini ou
aux raccords existent (`radius_step_between_contacts`, valeur exacte en tout point) ; « aucun contrat ne fixe le
facteur » est remplacé par le tableau ci-dessus, avec sa partie non couverte.

## 16. Le passage sortant `q`, travaillé directement ; les deux limites de l'anneau corrigées (2026-10-06)

Cible conservée (auteur) : trois passages consécutifs, `o` atteint `e` ON et monte, `p` quitte `e` et atteint `l`, `q` quitte
`l` et atteint `s`. Acquis : `p` monte, `β_l ≤ 1/2`. Flèche : `q` monte, sans supposer `l` ON ; fermeture par
`junction_vertical_vertical`. Théorème `renewed_height_advance` (`Terminal/OnLineBetaEqPrevious.lean`) : un but `False`, sous
`¬ VerticalPassage q`, `HorizontalPassage q`, `β_l < 1/2`. `onLine_beta_eq_previous` compile en dépendant de ce théorème.

### 16.1 Tableau des théorèmes pertinents (signature exacte, hypothèses, conclusion, domaine, usage dans la preuve)

Usage : **composé** (une étape de la preuve en dépend), **instancié** (nommé dans le contexte, utilisé par aucune étape),
**conditionnel** (antécédent non acquis, précisé). Domaine : ce sur quoi porte l'énoncé.

| Théorème (fichier) | Hypothèses | Conclusion | Domaine | Usage |
|---|---|---|---|---|
| `engaged_regime_kept` (RegimeTrigger) | `p.zLaterMember = q.zEarlierMember`, `VerticalPassage p`, `β_l = 1/2` | `VerticalPassage q ∧ ¬ HorizontalPassage q` | membre ON atteint en montant | composé (donne `p` monte depuis `o`, `e`) |
| `passage_height_le` (InterTowerExcess) | `p : TZeroPassage` | `T_e ≤ T_l` | tout passage | composé (égalité des hauteurs sous `¬ VerticalPassage q`) |
| `passage_entry_radial_le_half` (RaccordDetector) | `T_e < T_l` | `β_l ≤ 1/2` | arrivée d'un passage qui monte | composé (`hLe`) |
| `junction_vertical_vertical` (RegimeChange) | jonction, `VerticalPassage p`, `VerticalPassage q` | `β_l = 1/2` | membre entre deux passages qui montent | composé (fermeture `hCloses` ; dans l'énoncé principal) |
| `junction_vertical_horizontal` (RegimeChange) | jonction, `VerticalPassage p`, `HorizontalPassage q` | `β_l < 1/2` | entrée en régime horizontal | composé (`hBelow`) |
| `vertical_arrival_characterizes` (RegimeTrigger) | jonction, `VerticalPassage p` | `(VerticalPassage q ↔ β_l = 1/2) ∧ (HorizontalPassage q ↔ β_l < 1/2)` | `q` donné | instancié (caractérise, ne construit pas) |
| `exists_fiberSuccessor` (Voyage/FiberSuccessor) | `β_z < 1/2` | `∃ z'`, même hauteur, consécutif | membre bas | composé (existence de `q` dans l'énoncé principal) |
| `second_zero_radial_le_mirror` (OnLineBetaEqPrevious) | `HorizontalPassage q`, `β_l < 1/2` | `β_s ≤ 1 − β_l` | second membre d'une hauteur | instancié |
| `second_zero_mirror_or_le_half` (OnLineBetaEqPrevious, NOUVEAU) | `HorizontalPassage q`, `β_l < 1/2` | `β_s ≤ 1/2 ∨ s = l*` | second membre d'une hauteur | instancié (composition consécutivité + réflexion) |
| `eventIndex_succ_of_passage`, `expectedMinimumPrime_eq_laterOccurrence` (Grammar/ExpectedMinimum) | `0 < T` | rang + 1 ; `p_min(l) = Occ(s)` | tout passage | instancié (fonctions du rang) |
| `sameHeight_satisfies_both_rigidities` (DoubleRigidity) | `0 < T_e, T_l`, `HorizontalPassage` | occurrence, `Λ(M) = log M`, écarts, pas, registre, `φ_s < φ_l`, énergie renversée (`T ≥ 2`), `¬ TowerPrisoner` | passage de même hauteur | instancié |
| `engaged_event_restriction` (OnCrossReadings) | `0 < T_e, T_l`, `T_e < T_l`, `β_l ≤ 1/2` | rang + 1, premier partagé, pas contracté, fenêtre de phase, `λ ∈ [1, e^{1/(2T_l²)}[`, contacts = ligne × `λ` | arrivée d'un passage engagé | instancié |
| `sameHeight_successor_translates_inward` (EngagedNoTranslation) | `0 < T`, `HorizontalPassage q` | pas égal, contacts de `s` en deçà, `WindingNested l s` | passage de même hauteur | instancié |
| `vertical_iff_pitch_contracts` (RegimeTower) | `0 < T_e, T_l` | `VerticalPassage q ↔ pas contracté` | tout passage | composé (`hNoContraction` = négation du but) |
| `no_translation_iff_next_winds` (EngagedNoTranslation) | jonction, `VerticalPassage p`, hauteurs `> 0` | pas de `q` contracté `↔ λ_l = 1` | pas engagé puis pas suivant | instancié (équivalence, aucun côté acquis) |
| `radialFactor_eq_one_iff`, `radialFactor_gt_one_iff` (DiagonalPassage) | `z : TrueZero` | `λ = 1 ↔ β = 1/2` ; `1 < λ ↔ β < 1/2` | toute Tour | composé (`hLambda`) / instancié |
| `sameHeight_grid_rigid_translation` (MirrorDegeneracy) | `T_z = T_w` | `C_k(w) = C_k(z)·e^{(φ_w−φ_z)/T}` | deux Tours de même hauteur | instancié |
| `inversion_radial` (TangentialInversion) | `z`, `k` | `T·cot(T log C_k) = β` | toute Tour | instancié (identité) |
| `normalizedRadius_onLine` (OnRadialRing) | `β = 1/2`, `x > 0` | `r_z(x) = r(T)` | Tour ON | instancié (`hRingTop`, limite haute acquise) |
| `onLine_ring_iff` (OnRadialRing, NOUVEAU) | `β_e = β_l = 1/2`, `T_e < T_l`, `β_w = 1/2`, `x > 0` | cercles, `r(T_l) < r(T_e)`, `r(T_l) ≤ r_w ≤ r(T_e) ↔ T_e ≤ T_w ≤ T_l` | MEMBRES ON | conditionnel (`hRingIff`, antécédent `β_l = 1/2` = conclusion) |
| `onLine_ring_floor_pos` (OnRadialRing, NOUVEAU) | `β_w = 1/2`, `T_w ≤ T_l`, `x > 0` | `0 < r(T_l) ≤ r_w(x)` | Tours ON sous une hauteur finie | instancié (`hRingFloor` ; ne porte pas sur `l`) |
| `radius_envelope_of_le_half` (OnCrossReadings) | `β_l ≤ 1/2`, `x ≥ 1` | `r_l(x) ≤ 1/‖ρ_l‖ < 1/T_l` | `x ≥ 1` | instancié (`hEnvelope`, acquis) |
| `radius_floor_on_finite_domain` (OnCrossReadings, NOUVEAU) | `β_l ≤ 1/2`, `1 ≤ x ≤ X` | `0 < X^{β_l−1/2}/‖ρ_l‖ ≤ r_l(x)` | domaine fini | instancié (`hFiniteFloor`, acquis) |
| `radius_dominated_iff_gap` (OnCrossReadings, NOUVEAU) | `β_l ≤ 1/2` | `(∀ x ≥ 1, r_l(x) ≤ r(T_e)) ↔ T_e² + 1/4 ≤ β_l² + T_l²` | `x ≥ 1` | instancié (`hDominatedIff` ; condition d'écart explicite, non dérivée) |
| `radius_dominated_axis_iff` (OnCrossReadings, NOUVEAU) | `β_e = 1/2` | `(∀ x > 0, r_l(x) ≤ r(T_e)) ↔ β_l = 1/2 ∧ ‖ρ_e‖ ≤ ‖ρ_l‖` | tout l'axe | composé (`hNotAxisDominated`) |
| `low_member_not_dominated_on_axis` (OnCrossReadings, NOUVEAU) | `β_l < 1/2`, `R` | `∃ x ∈ ]0,1[, R < r_l(x)` | voisinage de zéro | instancié (`hAxisBlowUp`) |
| `low_case_pair_leaves_ring` (OnCrossReadings) | `β_l < 1/2`, `Te`, `U` | au-delà d'une abscisse : `r_l < r(U)`, `r(Te) < r_{l*}` | `x ≥ X` | instancié (conséquence du cas bas) |
| `vertical_arrival_onLine_iff_fibre_singleton` (RegimeTrigger) | `VerticalPassage p` | `β_l = 1/2 ↔ fibre(T_l) = {l}` | fibre de la hauteur atteinte | composé (`hFibreNotSingleton`) |
| `horizontalPassage_radial_lt` (RegimeChange) | `HorizontalPassage q` | `β_l < β_s` | passage de même hauteur | composé (`hFibreTwo`) |
| `mirror_takes_room_below` (TowerTwoSidedRoom) | `β_z < 1/2` | `z ≺ z*`, contacts de `z*` en deçà, même pas | membre bas et son miroir | instancié |
| `thm_zeroHeightFiber_finite` (rhv3_lean) | `T` | fibre finie | toute hauteur | instancié (aucun cardinal borné) |
| `second_zero_window` (OnLineBetaEqPrevious) | jonction, `VerticalPassage p`, `β_l < 1/2`, hauteurs `> 0` | fenêtre des deux zéros suivants | `l`, `s` | instancié |
| `primeAtRank_even_window_ge` (WindowProgression) | `3 < p_n` | `p_n + 6k ≤ p_{n+2k}` | rangs | instancié (progression première) |
| `sameHeight_phase_progress` (WindowProgression) | `T_e = T_l` | `ΔT = 0 ∧ 0 < ΔΘ` | même hauteur | instancié |
| `local_captivity_computed` (LocalRaccordCaptivity) | hauteurs `> 0`, `2 ≤ T_e` | captivité `↔` budget ; captivité `↔ T_e < T_l` | raccord, `T ≥ 2` | conditionnel (`hCaptivityIff` : captivité ⟺ le but) |
| `sameHeight_local_budget_refuted` (LocalRaccordCaptivity) | `HorizontalPassage`, `2 ≤ T` | budget renversé, `¬ LocalCaptivity` | raccord de même hauteur | instancié (`hCaptivityFalse`) |
| `sameHeight_breaks_hierarchy` (TowerHierarchy) | `HorizontalPassage` | pas égal, énergie renversée (`T ≥ 2`), `¬ RaccordHierarchy` | raccord de même hauteur | instancié |
| `engaged_step_of_next_hierarchy` (TowerHierarchy) | `o` vertical, `β_e = 1/2`, jonctions, `RaccordHierarchy q` | `β_l = 1/2 ∧ VerticalPassage p` | hiérarchie au raccord suivant | conditionnel (`hHierarchyCloses`, antécédent = le but) |
| `horizontal_escape_at_prime` (PersistentCapture) | hauteurs `> 0`, `HorizontalPassage` | `∃ M` premier `≥ N`, Tour de `s` au-dessus de celle de `l` en `M` | premiers arbitrairement grands | instancié |
| `winding_to_infinity_iff_riemannHypothesis` (EngagedNoTranslation) | — | contraction à tous les pas `↔ RH` | tous les passages | instancié (⟺ RH, non acquis) |
| `renewal_not_forced_by_parameters` (OnCrossReadings) | `0 < T_e < T`, `0 < d < 1/2` | tous les contrats de paramètres à hauteur gardée | paramètres `(1/2, T_e), (1/2 ∓ d, T)` | instancié sur `(T_e, T_l, 1/2 − β_l)` (`hParameters`) |
| `offLine_following_refutes_collectiveBudget` (OnLineBetaEqPrevious) | `H < T_w`, `β_w ≠ 1/2` | `¬ CollectiveBudget H` | somme des suivants | instancié (piste mise de côté) |
| `whole_tower_inside_iff`, `off_tower_not_inside_line_tower` (SymmetricWinding) | — / `β_z = 1/2`, `β_w ≠ 1/2` | domination sur l'axe `↔` même `β` et supports ordonnés ; une Tour hors ligne dépasse toute Tour en ligne en un point | tout l'axe | composés via `radius_dominated_axis_iff` |
| `lower_member_prisoner` (FirstTowerHorizon) | `β_{z₁} = 1/2`, `β_w ≤ 1/2`, `‖ρ_{z₁}‖ ≤ ‖ρ_w‖` | `InsideField z₁ w` (`x ≥ 1`) | `x ≥ 1` | non utilisé : sa condition `‖ρ_e‖ ≤ ‖ρ_l‖` est exactement celle de `radius_dominated_iff_norm` |
| `onLine_tower_hierarchy` (TowerHierarchy) | `β_z = β_w = 1/2`, `T_z < T_w` | Tour de `w` sous celle de `z` partout, rapport constant, pas plus petit | deux Tours ON | non utilisé : suppose `w` ON |
| `towerRoom_squeeze`, `tower_room_two_sided` (TowerTwoSidedRoom, EngagedNoTranslation) | `TowerRoom l` / `WindingNested e l`, `WindingNested l b`, `k ≥ 1` | ordre des contacts `1 < C_k(b) < C_k(l) < C_k(e)` | abscisses des contacts | non utilisés : ordre des CONTACTS, pas une borne radiale |

### 16.2 Les deux limites de l'anneau, corrigées

Quatre objets distincts : le rayon normalisé `r_z(x) = ‖x^ρ/ρ‖/√x` ; les abscisses des contacts `C_k(z)` ; les intervalles
logarithmiques `π/T` entre contacts ; les bornes au raccord partagé (`exitCost`, `raccordAvailable`, énergie en `M`). Un ordre de
contacts (`WindingNested`, `towerRoom_squeeze`) n'est pas une borne radiale.

Anneau exact (membres ON) : `r(T_l) ≤ r(T_w) ≤ r(T_e) ⟺ T_e ≤ T_w ≤ T_l` (`onLine_ring_iff`). Il classe un membre ON donné ; il ne
choisit pas le prochain zéro.

Limite basse. Locale : entre deux hauteurs ON finies, `r(T_l) > 0` minore toute Tour ON (`onLine_ring_floor_pos`) ; la limite
globale nulle (`onRadius_lt_of_height`) ne la supprime pas (conclusions antérieures corrigées). Pour le membre atteint `l` : la
limite basse de l'anneau est `hRingIff`, fonction de « `l` ON » : conditionnelle, inutilisable pour prouver `l` ON. Autres bornes
acquises sur `l`, sans le supposer ON : plancher `X^{β_l−1/2}/‖ρ_l‖ > 0` sur `1 ≤ x ≤ X` (`radius_floor_on_finite_domain`) ; valeur
exacte aux contacts du zéro engagé (`radius_step_between_contacts`) ; aucun plancher uniforme à l'infini si `β_l < 1/2`
(`low_member_radius_below`).

Limite haute. Acquis : `r_e(x) = r(T_e)` (`hRingTop`) ; `r_l(x) ≤ 1/‖ρ_l‖ < 1/T_l` sur `x ≥ 1` (`hEnvelope`). Domination de `l` par
`r(T_e)` sur `x ≥ 1` : ⟺ `T_e² + 1/4 ≤ β_l² + T_l²` (`radius_dominated_iff_gap`) ; cette condition d'écart est conservée
explicitement ; pour `l` ON elle découle de `T_e < T_l` ; pour `l` bas aucun énoncé du dépôt ne la fournit (sa dérivation n'est pas
faite ; il n'est pas établi qu'elle soit impossible). Sur tout l'axe positif : domination ⟺ `β_l = 1/2 ∧ ‖ρ_e‖ ≤ ‖ρ_l‖`
(`radius_dominated_axis_iff`) ; un membre bas dépasse tout seuil près de zéro (`low_member_not_dominated_on_axis`).

### 16.3 Confrontation de l'égalité des hauteurs aux contraintes acquises

Sous `¬ VerticalPassage q` : `T_l = T_s` (`passage_height_le`), `β_l < 1/2`, `λ_l > 1`. Obligations acquises au raccord `l → s`
confrontées : contraction obligatoire (`winding_to_infinity_iff_riemannHypothesis`, ⟺ RH, non acquise ; au pas `q` elle est le
but) ; captivité (`local_captivity_computed` : ⟺ `T_l < T_s`, le but ; fausse par calcul sur `q`) ; restriction de phase (acquise
pour `l` via `p` ; aucune pour `s`, non atteint par un passage qui monte ; `φ_s < φ_l` est une conséquence) ; structure de la
fibre (finie ; contient `l`, `s`, `l*` ; composition nouvelle : `β_s ≤ 1/2 ∨ s = l*` ; aucun cardinal borné par un énoncé
compilé ; « fibre réduite à un point » ⟺ `l` ON). Aucun fait acquis n'interdit l'égalité : chaque contrainte en contexte est une
identité, une conséquence du cas bas, ou une équivalence dont l'antécédent est le but. Dépendance manquante : un énoncé démontré,
faux sur « `e` ON ; `l`, `s` consécutifs à `T_l > T_e`, `β_l < 1/2` », non fonction des seuls `(β, T)` (`hParameters`). Non
établi : qu'aucune combinaison ne puisse fonctionner.

## 17. Les deux obligations du TDD d'enroulement, identification exacte du reste, routes et raccord résiduel (2026-10-06)

Correctif de l'auteur : une seule prémisse d'enroulement, reliée à l'obligation acquise de reproduction arithmétique exacte ; aucune autre
prémisse ; aucune sonde, aucune cible dédiée : un seul build, `lake build RHV6Fresh` (auteur, 2026-10-06). Modules : `Terminal/WholeWindingObligation.lean` (8 théorèmes) et `Terminal/RemainderRepresentation.lean`
(23 théorèmes, 5 objets ; section « reste » déplacée hors de `OnLineBetaEqPrevious.lean`), tous deux dans le build principal et compilés comme
unique build (EXIT=0 ; l'ancienne cible dédiée est supprimée, auteur, 2026-10-06). Verdict de l'époque : fermeture conditionnelle vérifiée ; fermeture sans prémisse toujours ouverte.

| objet | définition effective | domaine | statut |
|---|---|---|---|
| `zeroTerm z x` | `x^ρ/ρ`, terme BRUT (la Tour d'un membre) | `x > 0` | démontré (définition) |
| `nontrivialZeroResidueTerm x ρ` | `−m_ρ · x^ρ/(ρ(ρ+1))`, terme LISSÉ d'un indice | tout `x` | démontré |
| lissé ↔ brut | `residueTerm_eq_zeroTerm` : lissé `= −m ·` brut `/(ρ + 1)`, membre par membre | tout `x` | démontré |
| `smoothedVonMangoldtSum x` | `Σ_{n<x} Λ(n)(1 − n/x)` | tout `x` | démontré |
| `smoothedZeroBackground x` | `x/2 − ζ'/ζ(0) + ζ'/ζ(−1)/x + Σ` termes des zéros triviaux | `x ≠ 0` | démontré |
| `smoothedRemainder x` | `smoothedVonMangoldtSum − smoothedZeroBackground` (premiers seuls) | identité pour `x > 1` | démontré |
| identité de représentation | `smoothedRemainder x = ∑' ρ, nontrivialZeroResidueTerm x ρ` (convergence absolue) | `x > 1` | démontré (`smoothedRemainder_eq_tsum_residueTerm`) |
| `exactRemainder N` | `ψ(N) −` pas du fond (escalier non lissé) ; `= spectralRemainder N` | `N ≥ 2` | démontré (`arithmetic_eq_spectral`) |
| `psiRecoveredFromZeros` | `ψ(x)` reconstruite depuis les zéros | `x ≥ 2` | démontré (`liaison_analytic`) |
| `precedingSum H x` | somme FINIE des termes lissés de hauteur absolue `≤ H` | tout `x` | démontré (`precedingSum_eq_finite_sum`) |
| `followingSum H x` | somme à l'infini des termes lissés de hauteur absolue `> H` | sommable `x > 1` | démontré |
| `li(x) − π(x)` | aucun objet du dépôt ; aucun théorème de liaison avec `smoothedRemainder` | — | ABSENT : identification interdite |

| énoncé | statut |
|---|---|
| prémisse `W` (domination entière sur tout passage, tout `x > 0`) ⟹ RH | conditionnel fermé (`riemannHypothesis_of_whole_winding_all_passages`) |
| `W` ⟹ bloquée par le haut par le zéro précédent, par le bas par le zéro suivant | démontré (`two_sided_blocking_of_whole_winding`, conséquence) |
| ordre éventuel des contacts sur tout passage | démontré, toute position radiale ; ne suffit pas à fixer `β` |
| ordre éventuel ⟹ domination entière, sur tout passage | ⟺ RH, non dérivé |
| `‖followingSum T_e x‖ ≤ C√x` ⟹ `W` au-dessus de `e` | conditionnel (`whole_winding_above_of_followingSum_sqrt`), borne non dérivée |
| `‖smoothedRemainder x‖ ≤ C√x` ⟹ `W` partout | conditionnel (`whole_winding_all_passages_of_remainder_sqrt_growth`), borne non dérivée |
| `W` ⟺ `∃ C, ∀ x > 1, ‖smoothedRemainder x‖ ≤ C√x` | démontré (équivalence ; chaque côté ⟺ RH) |
| identité de représentation ⟹ borne `√x` | OUVERT ; antécédent théorème, donc ⟺ RH ; posé nulle part en hypothèse |
| constante `|A(x)||ρ₁|/√x ≤ 0,32` par décade, somme signée des suivants observée | observation numérique (E164, E170, E173), rien de certifié au-delà |
| flèche de renouvellement (`renewed_height_advance`, but `False`) | ouvert ; verrou en vigueur |

Paramètres effectivement utilisés dans la fermeture conditionnelle : partie réelle et hauteur (`whole_tower_inside_iff`), réflexion
(`mirrorMember`, même hauteur, à droite), succession de fibre (`exists_fiberSuccessor`, `horizontalPassage_radial_lt`), non-décroissance de la
hauteur (`passage_height_le`), caractérisation de RH (`riemannHypothesis_iff_noLowerSide`). Instanciés sans rôle dans cette fermeture : contacts,
inversion tangentielle, intervalles logarithmiques, rayons et anneaux, rang, premier partagé, premier attendu (ils restent dans le contexte du but
du build principal). Les contacts sont produits depuis la partie réelle et la hauteur ; aucun premier n'entre dans leur producteur.

## 18. Lecture conjointe des paramètres, flèche composée sous l'unique prémisse, premier raccord non démontré (2026-10-06)

Orientation de l'auteur : obligations conjointes de reproduction arithmétique, de fréquence et d'amplitude ; l'enroulement en conséquence ; une
seule prémisse ; aucune erreur dans le statut. Module `Terminal/JointParameterReading.lean` (38 théorèmes, 3 objets), dans le build principal et
dans l'unique build. `lake build RHV6Fresh` : EXIT=0 ; `renewed_height_advance` et `onLine_beta_eq_previous` portent la prémisse `hWind`.

| classe | contenu | théorème(s) | statut |
|---|---|---|---|
| paramètres indépendants | `β = rZeroRadialPosition`, `T = rZeroHeight` | données de `TrueZero` | démontré (structure) |
| dérivés | `φ = arctan(T/β)`, `C_k = e^{(φ+kπ)/T}`, `ℓ = π/T`, fréquence `T` en `u = log x`, `x^β/√(β²+T²)`, `A(x) = x^{β−1/2}/√(β²+T²)` | `towerMotion_phase`, `contactMinusAt_eq_exp`, `towerPitch`, `pointCurve_hasDerivAt`, `zeroTerm_norm`, `normalizedRadius_eq` | démontré |
| relations conjointes | `log C_{k+1} − log C_k = ℓ` ; `A = x^{β−1/2}ℓ/√(π²+β²ℓ²)` ; `A(y)/A(x) = (y/x)^{β−1/2}` ; `A(C_{k+1})/A(C_k) = e^{(β−1/2)ℓ}` ; croisé `T_l/T_e`, `e^{(β_l−1/2)π/T_e}` | `contact_log_step`, `normalizedRadius_eq_pitch`, `normalizedRadius_ratio`, `normalizedRadius_own_contact_step`, `joint_cross_reading` | démontré, toute position radiale |
| distances ordinaires | `C_{k+1} − C_k = C_k(e^ℓ − 1)`, strictement croissant en `k` | `contact_ordinary_gap_eq`, `contact_ordinary_gap_strictMono` | démontré (≠ contraction du pas entre Tours) |
| ON seulement | `A(x) = ℓ/√(π² + ℓ²/4)` ; réciproque `A(C_{k+1}) = A(C_k) ↔ β = 1/2` | `normalizedRadius_onLine_pitch`, `own_contact_amplitude_flat_iff` | conséquence de ON ; caractérisation |
| structurelles acquises | réflexion, ordre, succession, rang, raccord premier, domaines | `mirrorMember_radial`, `thm_zeroMemberPrecedes_iff_height_radial_lex`, `exists_fiberSuccessor`, `eventIndex_succ_of_passage`, `expectedMinimumPrime_eq_laterOccurrence` | démontré |
| obligation arithmétique | `smoothedRemainder x = Σ' lissés` (`x > 1`) ; `= F_z·brut_z + Σ_{autres ≤ H} + followingSum` | `smoothedRemainder_eq_tsum_residueTerm`, `remainder_eq_member_add_others` | démontré, identité, aucune borne |
| facteur de lissage | `F = −m/(ρ+1)` ; `‖F‖`, `Re F`, `Im F > 0` ; au contact brut `Im(lissé) ≠ 0` | `smoothingFactor_*`, `residueTerm_at_own_contact`, `residueTerm_re_at_own_contact`, `residueTerm_im_at_own_contact_ne_zero` | démontré : les contacts bruts ne sont pas ceux du lissé |
| dérivée de comptage | `d/dy F(ρ log y) = ρ·zeroTerm/(y log y)` pour toute primitive locale de `e^w/w` | `counting_contribution_hasDerivAt` | démontré (`Ei` absent de Mathlib : primitive en hypothèse) |
| canaux | `π(p_{n+1}) − π(p_n) = 1` ; `Λ(p) = log p` ; `Λ(p^{k+1}) = log p` ; `R(p_{n+1}) − R(p_n) = 1 − ∫ dt/log t` | `primeCounting_step`, `psi_jump_at_prime`, `psi_jump_at_prime_power`, `countingDeficit_step` | démontré ; liaison `R ↔ smoothedRemainder` : MANQUE |
| fenêtres | `A(p_{n+m})/A(p_n) = (p_{n+m}/p_n)^{β−1/2}` ; sous la ligne `≤ (1+3m/p_n)^{β−1/2} < 1` | `window_amplitude_ratio`, `window_amplitude_decay_of_low` | démontré ; borne sur une Tour, jamais par passage |
| inversion | `tan ≠ 0` ; restitution `T`, `β` ; encadrement `λ ≥ 1`, `λ = 1 ↔ ON` ; prédiction | `inversion_tan_ne_zero`, `inversion_from_consecutive_contacts`, `unknown_contact_bracket` | démontré / démontré / NON dérivée |
| conséquences ON | contraction des intervalles, rayon décroissant, domination individuelle | `onLine_passage_vertical_signature`, `vertical_iff_pitch_contracts`, `onRadius_strictAnti`, `onLine_tower_hierarchy` | démontré sous ON |
| progression de hauteur | premier passage depuis le ON engagé ; renouvellement | `engaged_regime_kept` ; `renewed_height_advance` | acquis ; conditionnel à la prémisse |
| sous la prémisse | `β_l = 1/2`, amplitude plate, pas contracté, rayon conservé, `q` monte, `β_l = β_e`, RH | `joint_reading_of_whole_winding`, `renewed_height_advance_of_whole_winding`, `renewed_height_advance`, `onLine_beta_eq_previous`, `riemannHypothesis_of_whole_winding_all_passages` | conditionnel |
| obligation recherchée | identité de représentation ⟹ `∀ z k, A(C_{k+1}) ≤ A(C_k)` (⟹ prémisse par réflexion) | `whole_winding_of_own_contact_amplitude_nonincreasing` (caractérisation) | OUVERT : premier raccord non démontré |

Chaîne : reproduction exacte à toutes les résolutions → restriction conjointe (OUVERT) → conservation (`own_contact_amplitude_flat_iff`) →
renouvellement (`engaged_regime_kept`) → enroulement (`whole_winding_iff_onLine`). Expériences à leur portée (observations) : E150, E165, E171
(1c : pics à `≤ 0,05 π/T_N` médian pour `N ≥ 100`, largeur `≈ 1,2 π/T_N`, premiers isolés de `[20, 3000]`), E137bis, E154, E155, E174b, E176,
E177. Aucune mesure finie ne donne une borne uniforme ; aucune impossibilité conclue ; ni « l'identité impose déjà l'enroulement », ni « elle ne
le pourra jamais ». RH_FOUND=FALSE.


## 19. L'unique prémisse minimale : premier gain collectif maximal à tout rang ; fermeture depuis la domination individuelle ; raccord ouvert (2026-10-06)

Directive de l'auteur : « unique prémisse : le premier zéro apporte le plus grand gain dans la reconstruction collective du reste ; conserver
exactement cette signification ; minimiser la prémisse au strict minimum ; aucune progression en hauteur dans la prémisse ». Module
`Terminal/FirstGainPremise.lean` (33 théorèmes, 7 objets), dans l'unique build ; `lake build RHV6Fresh` EXIT=0 ; signature
du statut d6a8d4a393a4. L'ancienne prémisse `hWind` (enroulement entier sur tout passage) n'est plus une prémisse.

| classe | contenu | théorème(s) | statut |
|---|---|---|---|
| paramètres et contacts | `ρ_n = β_n + iT_n`, `φ_n = arctan(T_n/β_n)`, `C_{n,k} = e^{(φ_n+kπ)/T_n}` | `towerMotion_phase`, `contactMinusAt` | démontré |
| contribution brute regroupée | `c_n(x) = −2 Re(x^{ρ_n}/ρ_n) = −2x^{β_n} cos(T_n log x − φ_n)/√(β_n²+T_n²)` | `pairContribution_eq_neg_pair`, `pairContribution_eq` | démontré |
| contacts = phases d'amplitude maximale | `c_n(C_{n,k}) = −2(−1)^k C_{n,k}^{β_n}/√(β_n²+T_n²)` ; `|c_n| ≤ 2‖x^ρ/ρ‖`, égalité aux contacts | `pairContribution_at_contact`, `abs_pairContribution_le`, `abs_pairContribution_at_contact` | démontré |
| amplitude normalisée | `A_n(x) = 2x^{β_n−1/2}/√(β_n²+T_n²)` ; ON `2/√(1/4+T_n²)` | `pairAmplitude_eq`, `pairAmplitude_onLine` | démontré |
| relation amplitude–contacts | `W_n = log(C_{n,k+1}/C_{n,k}) = π/T_n` ; ON `A_n = 2W_n/√(π²+W_n²/4)` | `contact_interval_eq`, `pairAmplitude_onLine_contact_interval` | démontré (ON) |
| hauteur ↑ ⟹ intervalle ↓, amplitude ↓ | `T_z < T_w ⟹ W_w < W_z` ; ON `A_w < A_z` : domination individuelle du premier parmi les ON | `contact_interval_lt_of_height`, `pairAmplitude_onLine_lt_of_height` | démontré |
| gain collectif | `r_{n−1} = R − Σ_{j<n} c_j` ; `D_n = ‖r_{n−1}‖² − ‖r_{n−1} − c_n‖² = ‖r_{n−1}‖² − ‖r_n‖² = 2⟨r_{n−1}, c_n⟩ − ‖c_n‖²` | `partialRemainder_succ`, `collectiveGain_eq_energy_drop`, `collectiveGain_eq` | démontré (tout `V` préhilbertien réel) |
| relation collective | sous `R = Σ_{j≥1} c_j` : `r_{n−1} = c_n + Σ_{j>n} c_j`, `D_n = ‖c_n‖² + 2⟨Σ_{j>n} c_j, c_n⟩` | `partialRemainder_hasSum`, `partialRemainder_eq_add_following`, `collectiveGain_collective` | démontré sous `HasSum` |
| PRÉMISSE | `∀ n ≥ 1, D_n ≤ D_1` (`hGain`), aucune hauteur, aucune domination, aucune décroissance des gains | hypothèse explicite | non dérivée |
| sous la prémisse | relation collective bornée par le rang 1 ; `‖c_n‖² ≤ D_1 − 2⟨Σ_{j>n} c_j, c_n⟩` ; interaction ≥ celle du rang 1 ⟹ `‖c_n‖ ≤ ‖c_1‖` (lecture) ; instance zéros | `firstGain_collective_relation`, `firstGain_amplitude_bound`, `norm_le_first_of_interaction`, `firstGain_zero_relation` | conditionnel à `hGain` |
| premier zéro | rang 1 = index zéro-source nul ⟺ aucun membre supérieur en dessous | `first_zero_index_zero_iff` | démontré |
| fermeture | `Dom := ∀ w, ∀ x > 0, A_w ≤ A_{z₁} ⟹ RH` ; ON + `x ≥ 1` ⟹ RH ; premier zéro : `Dom ↔ RH` ; `Dom ⟹ W` | `riemannHypothesis_of_individual_domination`, `_onLine`, `individual_domination_iff_riemannHypothesis`, `whole_winding_all_passages_of_individual_domination` | démontré (hypothèse = conclusion du raccord) |
| conditionnels à `Dom` | passage sortant monte ; même partie réelle au zéro suivant | `renewed_height_advance`, `onLine_beta_eq_previous` | conditionnel |
| RACCORD OUVERT | `hGain ⟹ Dom` | aucun (posé nulle part) | non démontré |

Manque exact du raccord : contrôle du terme d'interaction `2⟨Σ_{j>n} c_j, c_n⟩` à chaque rang depuis la prémisse (la prémisse borne amplitude +
interaction, pas l'amplitude seule) ; passage du support de mesure fixé (vecteurs sur `xs`) à tout l'horizon `x > 0` ; représentation `HasSum` des
contributions BRUTES regroupées, non dérivée de `smoothedRemainder_eq_tsum_residueTerm` (termes LISSÉS). Expériences à leur portée : E165 (amplitude
lue à la fréquence de chaque Tour strictement décroissante, `n ≤ 12`), E169/E171 (premier zéro = 66 % de la variance du reste lissé), E170 (somme des
suivantes jusqu'à 1,71 fois la première, domination en moyenne quadratique seulement) : observations, aucune borne uniforme. Ne pas présenter
`norm_le_first_of_interaction` comme une dérivation (son hypothèse d'interaction est la pièce manquante) ; ne pas confondre les contributions
brutes `c_n` et les termes lissés ; ne pas écrire que la prémisse impose déjà la domination ni qu'elle ne le pourra jamais.

## 20. Corrections de l'auteur sur l'instance de la prémisse : normalisation, énumération canonique, reste exact, représentation, raccord, ancre (2026-10-06)

Directive de l'auteur, six points, « conserve le build principal vert et les résultats déjà démontrés ». `lake build RHV6Fresh` EXIT=0, aucune
erreur, aucun `sorry`, axiomes standard ; signature du statut 39e3e6d9be79. Modules : `Terminal/FirstGainPremise.lean` (52 théorèmes, 18 objets),
`Terminal/CanonicalEnumeration.lean` (nouveau, 31 théorèmes, 7 objets). La prémisse `hGain : ∀ n ≥ 1, D_n ≤ D_1` est inchangée ; ni positivité des
gains, ni décroissance successive, ni domination individuelle ne lui sont ajoutées.

| point | contenu | théorème(s) | statut |
|---|---|---|---|
| 1 normalisation | `normalizedPairContribution = pairContribution/√x` ; `|c/√x| ≤ A`, égalité aux contacts ; `normalizedSupportContribution` seule contribution de l'instance ; `∀ i, 1 < xs i` ; énergie `≤ Σ A(x_i)²` ; reste normalisé par `√x` | `abs_normalizedPairContribution_le`, `abs_normalizedPairContribution_at_contact`, `normalizedSupportContribution_normSq`, `normalizedSupportContribution_normSq_le` | démontré |
| 2 énumération canonique | zéros en nombre infini ; tout entier est un index zéro-source ; `canonicalMember n` d'index `n` ; `canonicalZero n = canonicalMember (n−1)` : rang 1 = index 0, rang `n+1` = index `n` ; tout membre supérieur apparaît ; aucun répété ; ordre respecté ; consécutifs ; rang 1 = ancre `hFirst` ; `ExplicitIndex ≃ ℕ × Bool` | `explicitIndex_infinite`, `trueZero_infinite`, `exists_index_eq`, `canonicalMember_index`, `canonicalZero_one_index`, `canonicalZero_succ_index`, `canonicalZero_surjective`, `canonicalZero_injOn`, `canonicalZero_precedes_iff`, `canonicalZero_consecutive`, `canonicalZero_one_bottom`, `indexEquiv` | démontré |
| 2 multiplicités | coefficient `zetaZeroMultiplicity` dans `canonicalContributions` ; simplicité non supposée | `canonicalContributions` | convention de l'identité retenue |
| 3 reste exact | `chebyshevMidpoint x = (ψ(x) + ψ(x⁻))/2`, `rawBackground`, `rawRemainder`, `normalizedRawRemainderVector xs` = `R` de l'instance | définitions | démontré (définitions) |
| 3 identités sans convergence | `D_n = ‖c_n‖² + 2⟨r_n, c_n⟩`, `r_n = R − Σ_{j≤n} c_j` ; relation collective sous `hGain` ; lecture par l'interaction | `collectiveGain_eq_own_add_interaction`, `firstGain_relation`, `norm_le_first_of_interaction_ordered`, `firstGain_canonical`, `canonical_norm_le_first_of_interaction` | démontré / conditionnel à `hGain` |
| 3 représentation ordonnée | sommes partielles → `R` ⟹ `r_N → 0`, `r_n = lim Σ_{n<j≤N} c_j` ; `HasSum ⟹` ordonnée ; sous `HasSum`, `r_n = Σ_{j>n} c_j` | `partialRemainder_tendsto_zero`, `following_partial_sums_tendsto`, `ordered_of_hasSum`, `partialRemainder_succ_eq_following` | démontré |
| 3 représentation du canal BRUT | `R(x)/√x = Σ_n m_n c_n(x)/√x` dans l'ordre canonique | aucun (la base nomme `PM9aMidpointIdentity` sans la prouver ; Mathlib ne la contient pas) | NON démontré, posé nulle part |
| 3 représentation du canal LISSÉ | `Re(smoothedRemainder)/√x = Σ_n 2·Re(−m_n x^{ρ_n}/(ρ_n(ρ_n+1)))/√x`, `HasSum`, ordre canonique, membre et conjugué regroupés ; relation collective sous `hGain` | `residueTerm_conjIndex`, `normalizedSmoothedPairContribution_hasSum`, `smoothedCanonical_hasSum`, `firstGain_smoothed_collective` | démontré |
| 3 passage lissé → brut | facteur `−m/(ρ+1)` membre par membre, amplitude changée, phase tournée ; convergence non transportée | `normalizedSmoothedPairContribution_eq`, `smoothingFactor_norm`, `residueTerm_im_at_own_contact_ne_zero` | démontré (identité) / NON dérivé (convergence) |
| 4 raccord | conclusion visée `∀ w, InsideField (canonicalZero 1) w ⟺ ∀ w, ∀ x ≥ 1, A_w ≤ A_{z₁}` ; contrôle de l'interaction ; support fixé → `x ≥ 1` | `insideField_iff_pairAmplitude` (pont) ; aucun pour le contrôle et le passage | NON démontré, posé nulle part |
| 5 ancre ON | `rZeroRadialPosition (canonicalZero 1).1 = 1/2` | aucun terme Lean (dépôt, rhv3_lean, zeta23) ; lien à `hFirst` : `canonicalZero_one_bottom` | obligation explicite |
| 5 composition | `riemannHypothesis_of_first_field` (ancre + champ ⟹ RH) reste composable ; aucun théorème terminal ne prend `hGain` pour conclure RH | — | non composé (raccord et ancre indisponibles) |
| 6 build | EXIT=0, 0 `sorry`, 0 `admit`, axiomes standard ; `RH_FOUND=FALSE` | statut | vert |

Audit adversarial contre la directive : (a) la contribution normalisée est la seule utilisée dans l'instance (`canonicalContributions` ne lit que
`normalizedSupportContribution`) ; (b) les quantificateurs de la prémisse ne sont pas renforcés (un seul support fixé, aucune quantification sur les
supports) ; (c) aucun théorème ne prend `InsideField` ou le contrôle de l'interaction en hypothèse pour les dériver ; les théorèmes de lecture
(`norm_le_first_of_interaction_ordered`, `canonical_norm_le_first_of_interaction`) prennent l'interaction en hypothèse et concluent une inégalité
d'énergie sur le support, jamais `InsideField` ; (d) `hWind`, une borne `√x` et la non-croissance aux contacts ne remplacent pas la prémisse ;
(e) l'identité lissée n'est pas transportée aux contributions brutes : les deux canaux ont leurs objets distincts et le facteur de passage est
nommé ; (f) `RH_FOUND=FALSE`. Ce que cette correction n'apporte pas : la représentation du canal brut, le contrôle de l'interaction, le passage du
support à l'horizon, l'ancre ON ; ne pas présenter la représentation lissée comme la représentation brute ; ne pas présenter `firstGain_canonical`
comme une dérivation du raccord.

## 21. Route unique « premier gain maximal ⟹ domination individuelle ⟹ RH » : décomposition exacte du gain, phases, queues, grammaire compilée (2026-10-06)

Directive de l'auteur en dix points, puis complément grammatical le même jour : « ajoute progressivement les résultats sans modifier la prémisse,
sans supprimer de preuve et sans casser le build principal ; ne traite que cette route ». `lake build RHV6Fresh` EXIT=0, aucune erreur, aucun `sorry`,
axiomes standard ; signature 2bf8272229d5. Module `Terminal/FirstGainPremise.lean` : 102 théorèmes, 25 objets (52 et 18 avant). Prémisse inchangée
(`hGain`, instance `canonicalContributions xs` / `normalizedRawRemainderVector xs`, support `∀ i, 1 < xs i`) ; aucune domination ponctuelle, décroissance,
positivité, condition d'interaction ni obligation d'enroulement ajoutée. Lock court : « Déduire du premier gain collectif maximal que chaque
contribution reste dans le champ du premier zéro. »

| raccord | contenu | théorème(s) | statut |
|---|---|---|---|
| décomposition exacte | `E_n = ‖c_n‖²`, `I_n = ⟨r_n, c_n⟩` ; `D_n = E_n + 2I_n` ; `D_1 − D_n = (E_1 − E_n) − 2(I_n − I_1)` ; `E_n − E_1 = 2(I_1 − I_n) − (D_1 − D_n)` | `ownEnergy`, `interaction`, `collectiveGain_eq_ownEnergy_add_interaction`, `gain_margin_eq`, `ownEnergy_diff_eq` | compilé |
| sous la prémisse | `E_n − E_1 ≤ 2(I_1 − I_n)` | `ownEnergy_diff_le_of_gain`, `canonical_ownEnergy_diff_le` | compilé (conditionnel à `hGain`) |
| contrôle requis identifié | `E_n ≤ E_1 ⟺ 2(I_1 − I_n) ≤ D_1 − D_n` ; `‖c_n‖ ≤ ‖c_1‖ ⟺ …` ; instance canonique | `ownEnergy_le_first_iff`, `norm_le_first_iff_interaction_margin`, `canonical_norm_le_first_iff` | compilé (équivalence ; la borne elle-même : ouverte) |
| interprétation corrigée | `I_1 ≤ I_n` est suffisant, pas nécessaire ; mesuré : `I_n < I_1` aux rangs 3, 4 (brut, 16 premiers), rangs 2..15 (lissé) | `interaction_margin_of_interaction_ordered`, `canonical_norm_le_first_of_interaction` (conservé) | compilé (conditionnel) |
| produit de phases | `c_z c_w = (a_z a_w/2)[cos((T_z−T_w)u − (φ_z−φ_w)) + cos((T_z+T_w)u − (φ_z+φ_w))]`, toute position radiale ; normalisé ; `⟨c_n, c_j⟩` sur le support | `pairEnvelope`, `memberPhase`, `pairContribution_eq_envelope_cos`, `pairContribution_mul`, `normalizedPairContribution_mul`, `canonical_inner_eq_phase_sum` | compilé |
| queue finie | `⟨Q_{n,N}, c_n⟩ = Σ ⟨c_j, c_n⟩` ; `I_n = ⟨Q_{n,N}, c_n⟩ + ⟨r_N, c_n⟩` ; ordonnée : `⟨Q_{n,N}, c_n⟩ → I_n` ; lissé : série `HasSum` | `tailSum`, `inner_tailSum`, `partialRemainder_eq_tailSum_add`, `interaction_eq_tail_add`, `interaction_tendsto_of_ordered`, `interaction_hasSum`, `smoothedCanonical_interaction_hasSum` | compilé |
| ON à portée exacte | multiplicité égale ⟹ `m_w A_w < m_z A_z` si `T_z < T_w` ; `A(C_{k+1})/A(C_k) = e^{(β−1/2)π/T}` | `canonical_multiplicity_pos`, `canonicalContributions_apply`, `weighted_amplitude_onLine_lt_of_height`, `pairAmplitude_own_contact_step` | compilé |
| phases relatives | `(T_z−T_w) log(y/x)` ; raccord `(T_z−T_w) L_k` ; fenêtre `(T_z−T_w) log(p_{n+m}/p_n)` ; plancher `|T_z−T_w| log(1+3m/p_n) ≤ |Σ|` | `relative_phase_diff`, `relative_phaseIncrement`, `relative_phase_window_sum`, `relative_phase_window_ge`, `canonical_relative_phase_step` | compilé ; `relative_phase_window_ge` contient l'écart des hauteurs en facteur : il mesure son effet, il ne produit pas cet écart |
| grammaire réutilisée | `GoodMod6`, `state6`, `gapClass6`, `gapClass6_eq_{zero,two,four}_iff`, `gapClass6_mem`, `primeGapClass6_alternates` (Mod6Rigidity) ; `nPrimeGap`, `rPrimeGapLogRatio`, `fnPrimeAtRank`, `fnPrimeSuccessor` (rhv3_lean) ; `phaseIncrement`, `phaseIncrement_eq_height_mul_ratio` ; `stateIndicator`, `abMinusBa`, `prime_ab_ba_channel_lock` (GrammarWordLoad) ; `primeGapLogRatio_window_sum`, `primeWindow_log_ge`, `primeAtRank_window_ge_three_mul`, `window_abel_all_sameHeight` (WindowProgression) ; `alternating_two_step_gap`, `pure_step_demand_magnitude` (non reliés ici) | signatures relevées | existants |
| événement → paramètres | `g_r = 6m_r + a_r`, `a_r ∈ {0,2,4}`, transitions `AA/BB/AB/BA`, alternance ; `L_r = log(1 + (6m_r + a_r)/p_r)` ; `Δθ_{n,r} = T_n L_r` ; `B` : `e^{β L_r}`, `B²` : `e^{2β L_r}` ; `A` : `e^{(β−1/2) L_r}` ; ON : `1` | `gapMagnitude`, `eventClass`, `primeGap_eq_magnitude_class`, `eventClass_mem`, `eventClass_transitions`, `eventClass_alternates`, `primeGapLogRatio_eq_log_one_add`, `phaseIncrement_eq_height_mul_logRatio`, `rawAmplitude_prime_step`, `rawEnergy_prime_step`, `pairAmplitude_prime_step`, `onLine_prime_step` | compilé |
| mots et canaux | `Σ Δθ = T_n log(p_b/p_a)` ; sommes par classes `0/2/4`, maintiens par état ; `|#AB − #BA| ≤ 1` ; arguments avançant de `(T_n ∓ T_j) L_r` | `phaseIncrement_window_sum`, `window_sum_by_classes`, `window_class_zero_by_state`, `window_channel_lock`, `beat_arguments_prime_step` | compilé |
| liaison des supports | tout support de premiers est admissible ; produit scalaire par phases sur un support de premiers | `primeSupport_admissible`, `canonical_inner_primeSupport` | compilé pour des premiers sélectionnés par une fonction arbitraire ; ne démontre PAS le transport depuis le support fixé de la prémisse |
| identité d'Abel à hauteur constante | une constante réelle satisfait l'identité télescopique de toute fenêtre | `constant_height_window_abel` (= `window_abel_all_sameHeight` ; ex-`primes_force_no_height_progression`, renommé sur revue de l'auteur, 2026-10-06) | compilé ; NE justifie PAS « les premiers n'exigent aucune progression de hauteur » : aucune suite de vrais zéros construite, aucun reste reproduit, prémisse non utilisée |
| chaîne canaux → borne des interactions → contrainte de hauteur | — | — | NON DÉMONTRÉ |
| borne arithmétique sur les interactions | borne démontrée sur `Σ cos(…)`, puis sur `I_n` | — | OUVERT |
| énergie propre | `E_n ≤ E_1` sur le support depuis `hGain` | — (équivalence `canonical_norm_le_first_iff`) | OUVERT |
| domination ponctuelle | `∀ w, InsideField (canonicalZero 1) w` | — (`insideField_iff_pairAmplitude`) | OUVERT |
| ancre ON | `β(canonicalZero 1) = 1/2` | — (`canonicalZero_one_bottom` = lien à `hFirst`) | OUVERT, aucune certification extérieure transformée en terme |
| RH depuis la prémisse | — | `riemannHypothesis_of_first_field` composable, non composé | OUVERT ; `RH_FOUND=FALSE` |

Mesures (E178, `experiments/e178_gain_decomposition_prime_support.py`, 2 s ; E179, `experiments/e179_grammar_windows_12_24_36.py`, 1 s ; supports et
fenêtres fixés avant calcul ; zéros publiés d'Odlyzko, `β = 1/2`, multiplicité 1) : identités `D = E + 2I`, marge, excès vérifiées à `≤ 2·10⁻¹⁵` ;
premier gain maximal dans les deux canaux sur 16, 100, 300 premiers et pour 15, 100, 300 membres ; canal brut, 16 premiers : `I_n < I_1` aux rangs 3 et 4
exactement (reproduit) ; canal lissé, 16 premiers : rangs 2..15 (reproduit) ; brut, 100 premiers : aucun rang ; brut et lissé, 300 premiers : tous les
rangs ; `E_n ≤ E_1` partout (donc `2(I_1 − I_n) ≤ D_1 − D_n` partout, numériquement) ; `Σ D_n = ‖R‖² − ‖r_K‖²` ; queue finie `⟨Q_{n,N}, c_n⟩ → I_n` (brut
16 premiers, `N = 5000` : écart `≤ 3·10⁻⁵`) ; raccords canoniques `Occ(n) = p_{n−1}`, `p_min(n) = p_n`, `Δθ_n`, `W_n`, phases relatives tabulés ; aucun
contact propre ne coïncide avec un premier du support ; fenêtres 12/24/36 : classes dans `{0,2,4}`, alternance jamais violée, `g = 6m + a`, plancher
`log(1 + 3W/p_a)` satisfait 24/24, 12/12, 8/8, `|#AB − #BA| ≤ 1` partout, contributions de fenêtre à `E_1`, `I_1`, `D_1` et stabilité en queue spectrale
tabulées ; contraction `W_{n+1}/W_n = T_n/T_{n+1}` et amplitude ON tabulées. Audit : aucune sélection rétrospective (blocs consécutifs depuis `p = 5`) ;
mesures sur le support des premiers séparées de E169 (grille logarithmique) ; une borne observée reste numérique ; la validité numérique du contrôle
requis n'est pas une démonstration. Ce que cette étape n'apporte pas : la borne analytique sur les sommes oscillantes, l'énergie propre bornée, la
domination ponctuelle, l'ancre, toute contrainte de hauteur ; ne pas présenter `ownEnergy_le_first_iff` comme la démonstration du contrôle ; ne pas
appeler « accélération » une sollicitation sans énoncé sur sa variation ; ne pas présenter l'identité à hauteur constante comme preuve de hausse.

Revue de l'auteur (2026-10-06) sur cette section : lectures algébriques compilées, chaîne causale non démontrée. Points vérifiés : prémisse conservée ; décomposition du gain et des interactions implémentée ; contributions en amplitudes et phases implémentées ; grammaire, transitions et sollicitations réutilisées ; canaux → borne des interactions → contrainte de hauteur NON démontré ; gain maximal → domination individuelle NON démontré. Corrections appliquées : `primes_force_no_height_progression` renommé `constant_height_window_abel` (une constante réelle satisfait une identité télescopique ; aucune suite de vrais zéros, aucun reste reproduit, prémisse inutilisée) ; portée de `canonical_inner_primeSupport` (premiers choisis par une fonction arbitraire, pas le transport depuis le support fixé) ; portée de `relative_phase_window_ge` (l'écart des hauteurs est en facteur, mesuré, non produit). Le lock reste exactement la phrase courte ; les obligations (représentation brute, interactions, transport du support, ancre ON, raccord) sont dans le bloc `DÉPENDANCES DU RACCORD` du statut, séparé du lock. Bilan : progrès de formalisation, raccord analytique ouvert.

E180 (2026-10-06, demande de l'auteur, `experiments/e180_zero_contributions_plate.py`, 39 s, 31 contrôles PASS, aucun zéro synthétique, aucun changement Lean) : planche « Contributions des zéros et reconstruction du reste arithmétique » (`e180_zero_contributions_plate_full.png`, agrandissement des quinze premiers raccords `e180_zero_contributions_plate_zoom15.png`, données `data/e180_*.csv`). Deux canaux séparés : canal J de comptage (`J₀` au milieu des sauts, cible `R_J = J₀ − li + log 2 − ∫_x^∞ dt/(t(t²−1)log t) = −Σ_ρ li(x^ρ)`, sommes tronquées `S_N = −2 Σ_{n≤N} Re Ei(ρ_n log x)`, branche principale, `Im(ρu) > 0`, coupure non franchie ; erreurs sur `x ∈ [2, 10⁴]` : RMS 0,80 / 0,73 / 0,58 / 0,32 / 0,22 pour N = 1 / 3 / 15 / 100 / 300, RMS de `R_J` 0,92 ; `S_300 − S_100` max 1,22) et canal brut normalisé (`c_n = −2 Re(x^ρ/ρ)/√x`, enveloppes `A_n = 2/|ρ_n|`, contacts `log C_{n,k} = (φ_n + kπ)/T_n`, `W_n = π/T_n`, événements `g_r = 6m_r + a_r`, `L_r`, `Δθ_{n,r} = T_n L_r` = avance de phase, quatre transitions, fenêtres 12/24/36 depuis le rang 2 : plancher et verrou `|#AB − #BA| ≤ 1` vérifiés sur tous les blocs jusqu'à 10⁴). Gains sur le support fixé 16 premiers (valeurs de E178 reproduites) : `D_n ≤ D_1` observé sur 16/100/300 premiers ; `I_n < I_1` aux rangs 3, 4 (16 premiers), à aucun rang (100), à tous les rangs 2..300 (300) ; part médiane normalisée de l'énergie propre dans `D_1 − D_n` : 0,765 (canal brut, rangs 2..15). Portée : identités démontrées (décomposition, contacts, dérivée de Ei, formule explicite), observations numériques (gain maximal, erreurs, part propre), raccord ouvert (gain maximal ⟹ domination ponctuelle). Les gains du canal brut n'expliquent pas les erreurs du canal de comptage ; aucun théorème ni la prémisse n'est modifié.

Réduction de la prémisse (2026-10-06, demande de l'auteur : « enlève ou réduit la prémisse, voici déjà la preuve que le premier zéro est le plus fort sur la ligne » ; `Terminal/FirstGainPremise.lean` section 14, 16 théorèmes ajoutés, 118 au total, 25 objets ; `lake build RHV6Fresh` EXIT=0, axiomes standard ; signature 06d460d7051f). Compilé depuis les formules de l'auteur : `pairAmplitude_onLine_le_of_height` (ON, `T_z ≤ T_w ⟹ A_w ≤ A_z`, forme large de `pairAmplitude_onLine_lt_of_height`) ; `canonicalZero_height_mono` ; `canonical_onLine_amplitude_le_first` et `canonical_onLine_insideField` (premier membre canonique en ligne, rang `n` en ligne ⟹ `A_n ≤ A_1` et rang dans le champ) ; `pairAmplitude_ratio`, `pairAmplitude_ratio_onLine_first` (`A_w/A_1 = x^{β_w − 1/2}·‖ρ₁‖/‖ρ_w‖`, toute position radiale) ; `abs_normalizedSmoothedPairContribution_le`, `_onLine_le`, `smoothed_onLine_envelope_anti` (enveloppe lissée, ON `2m/(√(1/4+T²)√(9/4+T²))`, décroissante). Prémisse RÉDUITE `hGainRes : ∀ n ≥ 1, ¬ InsideField (canonicalZero 1) (canonicalZero n) → D_n ≤ D_1` : `gain_restricted_of_gain` (`hGain ⟹ hGainRes`), `gain_restricted_vacuous_onLine` (aux rangs en ligne, sous l'ancre ON, l'antécédent est faux : la prémisse n'y demande rien), `not_onLine_of_not_insideField`, porteurs `canonical_ownEnergy_diff_le_of_restricted`, `canonical_norm_le_first_of_interaction_restricted`, `riemannHypothesis_of_restricted_gain_link` (composition : ancre ON + prémisse réduite + raccord `hLink` en hypothèse ⟹ RH) ; `riemannHypothesis_of_canonical_insideField` (ancre ON + chaque rang dans le champ ⟹ RH, par `canonicalZero_surjective`). Portée exacte : la domination individuelle du premier est un théorème parmi les membres EN LIGNE seulement, et sous l'ancre ON (aucun terme Lean) ; le gain collectif `D_n ≤ D_1` n'est dérivé nulle part, pas même en ligne (l'interaction `I_n` reste à borner, texte de l'auteur) ; la prémisse n'est pas retirée parce que sa suppression ferait de la conclusion du raccord (⟺ RH) la seule hypothèse ; la prémisse réduite ne suppose aucun membre hors du champ (un rang hors du champ n'est pas en ligne, `not_onLine_of_not_insideField`, mais l'énoncé est vide s'il n'y en a aucun) ; `scripts/status.sh` : PREMISE (réduite), PREMISE_CARRIERS (hGainRes), FULL_GAIN_CARRIERS (ancienne forme), PREMISE_REDUCTION, OPEN_LINK en rangs canoniques, POINTWISE_DOMINATION_PROVED = en ligne OUI / hors du champ NON, ligne du tableau des dépendances mise à jour. Lock inchangé.

Quatre corrections de l'auteur (2026-10-07 ; `Terminal/FirstGainPremise.lean` section 15, 12 théorèmes ajoutés, 130 au total, 25 objets ; `lake build RHV6Fresh` EXIT=0, axiomes standard ; signature 3fca380ece44). (1) `riemannHypothesis_of_restricted_gain_link` reçoit l'ancre ON, la prémisse réduite et `hLink` (le raccord) ; son corps applique `hLink` : composition, pas « la prémisse seule entraîne RH » (docstring, statut, maîtres corrigés). (2) La réduction affaiblit la prémisse (`gain_restricted_of_gain`), elle ne la démontre pas ; la domination des enveloppes ON et le gain collectif maximal sont distincts ; `gain_restricted_of_all_onLine` (tous les rangs ON ⟹ prémisse réduite vide, pour tout support), `riemannHypothesis_of_all_canonical_onLine` (ce cas est RH) : les observations entièrement ON (E178, E180) ne testent pas les rangs où la prémisse réduite s'applique. (3) Multiplicités : `canonical_onLine_weighted_le_first` (`m_n ≤ m_1 ⟹ m_n A_n ≤ m_1 A_1`, ON), `canonical_normSq_le_envelope` (`‖c_n‖² ≤ m_n² Σ A_n²`, sans prémisse), `canonical_onLine_envelope_le_first` (ON, `m_n ≤ m_1`) ; `weighted_amplitude_onLine_lt_of_height` exigeait déjà l'égalité ; la phrase « le premier domine toutes les contributions ON » vaut par unité de multiplicité. (4) Support : `norm_eq_zero_of_fin_zero`, `collectiveGain_support_empty`, `gain_of_support_empty`, `gain_restricted_of_support_empty` (support vide ⟹ prémisse automatique) ; les trois porteurs exigent `0 < m` ; non vide ne donne pas le transport vers toutes les abscisses. Cible d'interdiction de compensation `E_n > E_1 ⟹ 2(I_1 − I_n) < E_n − E_1` : `compensation_bound_incompatible` (avec la borne sous la prémisse ⟹ `E_n ≤ E_1`), `compensation_target_iff_ownEnergy_le` (sous la borne, équivalence), `canonical_ownEnergy_le_first_of_no_compensation` (instance, nouveau porteur de la prémisse réduite, support fixé) ; non dérivée ; hypothèse d'aucune fermeture vers RH. `scripts/status.sh` : PREMISE (support non vide), PREMISE_REDUCTION (affaiblissement, multiplicités, vacuité ON), OPEN_LINK (composition), COMPENSATION_TARGET (nouvelle ligne), INDIVIDUAL_ENERGY_BOUND_PROVED, POINTWISE_DOMINATION_PROVED (par unité de multiplicité ; pondérée sous `m_n ≤ m_1`), VERDICT, ligne du tableau des dépendances « interdiction quantitative de compensation ». Lock inchangé.

Cible de captivité sur tout l'horizon et couplage rétrécissement–fréquence–amplitude (2026-10-07 ; `Terminal/FirstGainPremise.lean` sections 16 et 17, 16 théorèmes ajoutés, 146 au total, 25 objets ; `lake build RHV6Fresh` EXIT=0, axiomes standard ; signature 33d944cd61ba ; lock de l'auteur : « Établir que la reconstruction collective impose la captivité de toutes les Tours dans le champ du premier zéro ON. »). Portées vérifiées : `canonical_onLine_amplitude_le_first` et `canonical_onLine_insideField` = domination NON pondérée parmi les ON sous l'ancre ON ; `canonicalContributions` porte les multiplicités ; `hGainRes` = prémisse de gain collectif, support non vide ; `riemannHypothesis_of_restricted_gain_link` = composition recevant le raccord. Compilé : `captivity_log_iff_insideField`, `captivity_iff_insideField`, `firstField_constant_onLine`, `riemannHypothesis_of_captivity_onLine`, `interaction_abs_le_tail_add_residual`, `gain_excess_iff`, `normalizedPairContribution_mul_sameHeight`, `canonical_insideField_of_gain_excess`, `not_insideField_iff_exists_exceedance`, `exceedance_persists`, `exceedance_detected_on_support`, `onLine_coupling_ratios`, `onLine_amplitude_ratio_between`, `window_cells_eq`, `window_cells_ratio`. Comptage `N(T)` : aucun théorème asymptotique dans le build (KadiriZeroCounting : finitude, bornes par ordre). E181 (`experiments/e181_complete_interaction_nested_supports.py`, 16 contrôles, 7 mesures) : D_n ≤ D_1 et E_n ≤ E_1 sur 12 combinaisons membres × support et sur supports entiers ; 2(I_1 − I_n) > 0 renforce le premier à tous les rangs ≤ 15 sur 300 premiers ; résidu ⟨r_300, c_n⟩ médian 5 %, jusqu'à 69 % ; convention du saut à gauche sur 16 premiers renverse D_n ≤ D_1 (11 rangs) ; quatre canaux : découpage exact, aucune borne. E182 (`experiments/e182_coupling_pitch_frequency_amplitude.py`, 10 contrôles, 10 mesures) : rapports W, f, A entre passages = fonctions des hauteurs (identités vérifiées) ; variation du rapport de fréquence > 1 sur 149/298 (aucune accélération observée comme loi) ; L_r croît sur 589/1228 événements ; annulation médiane 1,000 sur les fenêtres de battement < 1/2 demi-tour (1688/2618), 0,131 au-delà de 4 demi-tours ; obligation exacte manquante : borne uniforme des sommes `Σ cos((T_n − T_1) log p − Δφ)` sur des plages de fenêtres d'horizon logarithmique ≥ π/|T_n − T_1|. Rien n'est dérivé vers la captivité.

Chaînes de 3, 4, 10, 12 Tours et variations obligatoires mod 6 (2026-10-08 ; `Terminal/FirstGainPremise.lean` sections 18 et 19, 19 théorèmes ajoutés, 165 au total, 26 objets ; `lake build RHV6Fresh` EXIT=0, axiomes standard ; signature f1e6aafcbf9a ; lock de l'auteur : « Démontrer que la compensation nécessaire pour sortir du champ du premier est incompatible avec la reconstruction arithmétique complète. »). Compilé : `chain_gain_telescope`, `interaction_eq_chain_add_external_add_residual`, `interaction_tail_decomposition_truncation_invariant`, `masked_gain_requires_interaction`, `masked_gain_requires_residual`, `canonical_masked_exceedance_requires_residual`, `cumulative_height_eq_sum_steps`, `cumulative_height_pos_of_strict`, `cumulative_pos_not_strict_witness`, `pitch_chain_telescope`, `classFloor`, `nPrimeGap_pos`, `primeGap_ge_classFloor`, `primeGapLogRatio_ge_classFloor`, `log_classFloor_nonneg`, `relative_phaseIncrement_abs_ge_classFloor`, `sum_phaseIncrement_ge_classFloor` (classe ⟺ transition : `Grammar/Mod6Rigidity.lean`, déjà compilé). E183 (`experiments/e183_tower_chains_joint_constraints.py`, 69 contrôles PASS, 33 mesures, données `data/e183_*.csv`, figure) : 298/297/291/289 chaînes ; chaque pas ΔT > 0 (min 0,418) ; Σ ΔT/s(T) min 1,16 / 2,09 / 7,98 / 9,86 (minima de grille) ; 57 % des pas sous l'échelle moyenne ; contacts par cellule ∈ {⌊T_{j+1}/T_j⌋, +1}, recouvrement 1,000 ; rapport de fréquence croissant à chaque passage 149/298 (L = 3), 0/291 (L = 10) ; parts médianes interne/externe/résidu 0,26/0,43/0,22 (L = 3) à 0,41/0,31/0,21 (L = 12) ; X_j ≤ 0 partout (antécédent faux) ; marge min D_1 − D_j 0,049 / 0,445 / 2,460 (16/100/300 premiers ; corrigées le 2026-10-08 : l'ancien affichage 0,101 / 0,838 / 3,643 donnait −min(D_j − D_1), la plus grande marge, avec le rang de la plus petite ; contrôle de cohérence valeur/rang ajouté, 69 contrôles), 0 violation, 0 changement de signe entre supports ; treize contraintes mod 6 vérifiées, planchers atteints AA 156/238, BB 143/233, AB 204/378, BA 202/378 ; réalisé / Σ planchers par classe médiane ≈ 1,96 par fenêtre ; annulation médiane 1,000 sous 1/2 demi-tour (5951 cas), 0,163 au-delà de 4 (99 cas). Règles candidates non intégrées : séparation normalisée minimale (observation), obligation d'excès (reçue en hypothèse seulement), borne uniforme des sommes oscillantes (manquante). Rien n'est dérivé vers la captivité.

Retrait exact du premier membre, borne démontrée de la queue lissée, compensation nécessaire contre majoration acquise (2026-10-08, directive de l'auteur en huit points ; `Terminal/FirstGainPremise.lean` section 20, 21 théorèmes ajoutés, 186 au total, 26 objets ; `lake build RHV6Fresh` EXIT=0, axiomes standard ; signature f1e6aafcbf9a inchangée, aucun nouveau porteur de la prémisse ; lock de l'auteur : « Prouver que les contraintes arithmétiques et les interactions complètes empêchent toute contribution de dépasser le champ du premier zéro tout en maintenant la reconstruction exacte sur tout l'horizon. »). Compilé : `signed_removal_bounds`, `signed_removal_truncated_bounds`, `signed_margins_sum`, `signed_interval_subset_symmetric`, `signed_interval_not_abs_witness`, `first_removed_eq`, `first_removed_eq_tail_add_residual`, `first_removed_norm_le`, `first_removed_norm_ge`, `collectiveGain_one_eq`, `collectiveGain_one_congr`, `normalizedSmoothedRemainder_abs_le_sqrt`, `smoothed_first_removed_signed_bounds`, `smoothed_first_removed_hasSum`, `smoothed_first_removed_vector_hasSum`, `normalizedSmoothedPairContribution_abs_summable`, `smoothed_residual_abs_le_tsum`, `smoothed_term_abs_le_sqrt`, `chain_interaction_telescope`, `masked_gain_iff_interaction`, `masked_exceedance_le_acquired_bound`. Tableau des bornes (E184 §0) : seule borne démontrée du reste, canal lissé, `‖A(x)‖ ≤ Cx` pour `x > 1`, constante explicitée `C ≈ 11,35` ; aucune borne dans le canal brut (représentation non acquise) ni dans le canal de comptage ; bornes conditionnelles à `β ≤ 1/2` non utilisées ; aucun transport entre canaux. E184 (`experiments/e184_first_removal_collective_mechanics.py`, 41 contrôles PASS, 34 mesures, `data/e184_*.csv`, deux figures avec zooms) : représentation lissée vérifiée (`|ε̃_300| ≤ 3,8·10⁻⁴`, `|ε̃_5000| ≤ 3,7·10⁻⁵`, résidus par différence), borne démontrée tenue avec un facteur ≥ 946, borne de queue calculable sur les zéros 301–5000 (`2,7·10⁻³√x`, au-delà non calculable sans `N(T)`), enveloppe de grille dépassée de `6,8·10⁻⁵` par le raffinement adaptatif (maximum échantillonné ≠ supremum), canal brut : résidu médian 11 % de `|R|`, convention du milieu minimisant le résidu ; chaînes dans `S` : compensation interne médiane 0,43 / 0,39 / 0,23 / 0,21 (L = 3/4/10/12), part de `S` expliquée ≤ 0,54 ; fenêtres de 12/24/36 : `‖S‖/‖c_1‖ ≈ 1,7`, `‖ε_300‖/‖S‖ ≈ 0,25` ; grammaire : planchers compilés vérifiés sur 1248 événements, sommes oscillantes de fenêtre non bornées par la grammaire, hauteurs égales absentes (doublon synthétique) ; masquage : rangs `E_n > D_1` 1/300 (16 et 100 premiers), 0/300 (300 et 1229), nécessaire/acquis ≤ 0,06 ; perturbations HYPOTHÉTIQUES (paire miroir `β = 1/2 ± d`, 50 cas × 4 supports) : 0 violation de `D'_j ≤ D_1`, gain négatif du membre perturbé dans 37 à 46 cas sur 50, `‖r'_300‖/‖r_300‖` jusqu'à 18–29, repondération des membres retenus insuffisante sur 1229 points (résidu de projection 0,36–0,88). Lecture : la prémisse seule ne lit pas une sortie du champ, le défaut de reconstruction la lit ; inégalité exacte encore nécessaire : `Σ_{n<j≤N}|⟨c_j,c_n⟩| + ‖r_N‖‖c_n‖ < (E_n − D_1)/2` à tout rang hors du champ. Aucune nouvelle contrainte démontrée ne réduit le raccord ouvert.

Réduction de la prémisse par le miroir (2026-10-08, auteur : « avance sur la réduction de la prémisse ; prouver que les zéros sont liés par leurs contraintes et captifs du premier » ; `Terminal/FirstGainPremise.lean` section 21, 22 théorèmes ajoutés, 208 au total, 26 objets ; `lake build RHV6Fresh` EXIT=0, axiomes standard ; signature 482c48ff20b1, nouveaux porteurs `riemannHypothesis_of_upper_gain_link`, `upper_gain_requires_interaction` ; lock inchangé). Compilé : `upper_not_insideField`, `small_support_not_insideField`, `not_insideField_iff_upper_or_small`, `small_support_band`, `small_support_height_lt`, `lower_captive_of_height`, `lower_captive_of_height_margin`, `mirror_pair_captive_iff_lower`, `mirror_pair_exactly_one_captive`, `canonical_small_support_band`, `canonical_lower_captive_of_margin`, `exists_canonical_mirror_rank`, `band_rank_mirror_upper`, `no_upper_canonical_iff_riemannHypothesis`, `upper_insideField_iff_no_upper`, `riemannHypothesis_of_upper_canonical_insideField`, `gain_upper_of_restricted`, `restricted_bites_iff`, `gain_upper_of_riemannHypothesis`, `riemannHypothesis_of_upper_gain_link`, `upper_gain_link_iff_refutation`, `upper_gain_requires_interaction`. Contenu : sous l'ancre ON, hors du champ ⟺ rang haut ∨ support plus petit que le premier ; la seconde branche est une bande fine (membre bas, `T₁ < T_n < T₁ + 1/(8T₁)`) dont chaque miroir est un rang haut ; tout membre bas au-delà de la marge est captif par la hauteur seule ; exactement un captif par paire miroir hors ligne de hauteur ≥ ‖ρ₁‖ ; aucun rang haut ⟺ RH ; la prémisse n'a à être posée qu'aux rangs hauts (`hGainUp`), impliquée par `hGainRes` et par RH ; le raccord ouvert est réduit aux rangs hauts et prend sa forme exacte : sous `hGainUp`, aucun rang n'est haut (`D_n ≤ D_1` à un rang haut contredit par la reconstruction). Non dérivé : ce raccord. Lecture : E184 (perturbations hypothétiques satisfaisant `D'_j ≤ D_1` sur supports finis) montre que la contradiction doit lire la reconstruction exacte des vrais zéros, non la seule inégalité de gain sur un support fixé. Progrès : réduction démontrée du raccord ouvert (bande fine et rangs bas retirés ; forme exacte) ; le raccord lui-même reste ouvert.

Tentative de fermeture SANS la prémisse (2026-10-08, auteur : « que reste-t-il pour clore RH en enlevant notre prémisse ; l'erreur précise de compilation ») : section 22, `riemannHypothesis_without_premise` (hypothèse : ancre ON seule), 209 théorèmes ; `lake build RHV6Fresh` EXIT=1, `FirstGainPremise.lean:2875:82: unsolved goals`, contexte `h₁ n hn hUp hNot hHorizon k hk hMirror hRec hBound hFirst`, but `⊢ False` ; signature f460aa4c1435 ; analyse dans `experiments/audit_semantique/main_build_error_analysis.md`. Manque selon le compilateur : un théorème concluant contre `hUp` depuis l'ancre et la reconstruction ; aucun du dépôt n'a cette forme (reconstruction vraie pour toute position radiale ; borne `C√x` aveugle à la position radiale ; la borne contredisant l'horizon exact est la croissance critique, ⟺ RH). — SUITE (2026-10-08, directive en huit points de l'auteur, depuis 59c21a63) : la tentative est conservée mot pour mot dans la cible TDD séparée `RHV6FreshTDD` (`RHV6FreshTDD/WithoutPremise.lean`, non importée par `RHV6Fresh`, sortie complète `experiments/audit_semantique/tdd_build_output.txt`, analyse `tdd_build_analysis.md`, signature TDD e83e6a7fa3b9) ; build principal VERT (EXIT=0, signature 482c48ff20b1 inchangée). Théorèmes fermés : section 22 « transmission du défaut » (18 théorèmes, objet `insertTwo` ; 227 théorèmes, 27 objets) : `r'_k = r_k − Δ`, `I'_k = I_k − ⟨Δ, c_k⟩`, `D'_k = D_k − 2⟨Δ, c_k⟩` ; insertion de deux membres distincts aux rangs `p, p + 1`, rangs `≥ p` décalés de deux (`insertTwo_*_shift`), `D'_1` invariant, gains insérés, télescopage, résidu `→ −Δ` (`insertTwo_residual_tendsto`), masquage après insertion (`insertTwo_masked_iff`). Tentative composée `riemannHypothesis_without_premise_composed` (`RHV6FreshTDD/WithoutPremiseComposed.lean:37`) : succession, dépassement persistant, horizon, contacts, grammaire, retrait du premier, reconstruction, interaction en série, queue, `β_n ≤ θ*` ; premier but réellement restant : `∃ θ < β_n, ∃ C, ∀ x > 1, ‖smoothedRemainder x‖ ≤ C x^θ` ; acquis le plus proche : exposant `1` (`smoothedRemainder_linear_growth`) ; écart : abaisser l'exposant sous `β_n` depuis les poids premiers. Route « ancre seule » inventoriée (25 théorèmes, maître Lean §12) : aucun ne conclut depuis l'ancre seule. E184 corrigée (deux membres distincts insérés, rangs décalés, rang central `a + 1`, identités vérifiées sur 200 cas, 42 contrôles PASS). E185 : ancre certifiée hors Lean (Arb, 4 contrôles PASS), dépendance réelle, non compilée. — SUITE 2 (directive en six points, relecture E181–E185, borne racine-log signée, 2026-10-08) : ancre STRUCTURELLEMENT DÉDUITE sous `hU : ∃! w, T_w ≤ 15` (`Terminal/AnchorStructure.lean`, 22 théorèmes : `anchor_of_unique_band`, `anchor_of_count_one` depuis le comptage `upperCountWithMultiplicity 15 = 1`, conventions aux frontières, `mem_upperWindow_iff`) ; certification analytique du comptage NON vérifiée par Lean (TDD `AnchorCounting`, lemme manquant : principe de l'argument certifié + vérificateur d'intégrale) ; INSERTION dans une famille complète EXCLUE par unicité de la limite (`Terminal/InsertionExclusion.lean`, 33 théorèmes ; instance lissée point par point et par coordonnée ; paire hypothétique non identiquement nulle par unicité spectrale, même hauteur comprise ; aveugle à `β`, n'exclut pas un membre OFF authentique) ; COMPLÉMENT MODIFIÉ : obligation exacte `−Δ` et rigidité spectrale (aucun intrus, multiplicités fixes) ; l'unicité ne fixe pas `β_n` (TDD `ComplementRigidity`) ; borne `√x log x` signée compilée, instance lissée conditionnelle ; CAPTIVITÉ UNIVERSELLE toujours ouverte (TDD `UniformTail` : contrôle conjoint uniforme partie finie + queue, exposant `< β_n`) ; E186 (8 contrôles PASS, 18 mesures) : défaut d'insertion commun paire / contrôle ON, déformation propre `Δ_pair − Δ_ON`, compensation des chaînes 0,43 → 0,21 conservée, fenêtres de battement, ajustement non transportable, multiplicités admissibles sans effet ; E181 et E182 corrigées (troncature ; aucune impossibilité d'amélioration). Build principal VERT (signature 482c48ff20b1) ; TDD FAIL (signature 4b50050c327d, cinq buts). — SUITE 3 (directive en sept points, auteur, 2026-10-08, depuis 2b09d74b) : contour de l'ancre CORRIGÉ (`Terminal/AnchorContour.lean`, 27 théorèmes : ξ₁ entière sur `[−1,2]×[0,T]`, zéros et multiplicités identifiés, raccord exact, frontière hors de `(0,1)`, Cauchy) et terme `N(15) = 1` composé dans la TDD depuis quatre lemmes manquants (ζ ≠ 0 sur `(0,1)`, principe de l'argument, valeur certifiée, aucun zéro à la hauteur 15) ; renforcement `‖P_H‖ + ‖S_H‖` retiré de la cible TDD (but sur la somme) ; borne racine-log : aucune source acquise dans aucun canal, règle de normalisation compilée, rien en prémisse ; captivité universelle COMPOSÉE (TDD `UniversalCaptivity`, unique lemme ouvert `upper_member_refuted`, but `False` au membre haut) ; E186 corrigée (les ajustements entiers modifient des multiplicités, défaut hors support ≈ ‖Δ‖, recherche non exhaustive) ; E187 (identités ON, contacts, interaction invariante, grammaire entière, chaînes × fenêtres × battements, hauteur commune). Build principal VERT (signature 482c48ff20b1) ; TDD FAIL (signature c9f44222034d, neuf buts triés). État remplacé le 2026-10-09 par la section 23 : ces tentatives sont retirées de la cible de travail et consignées ici.

## 23. Deux obligations, une seule chaîne : certification du comptage et contradiction du dépassement (2026-10-09)

Directive de l'auteur (depuis fca2fa3c, main seulement) : centraliser les obligations ouvertes dans une seule cible de travail, retirer les tentatives redondantes en conservant leur historique, terminer les lemmes de certification, composer le comptage égal à un, poursuivre la contradiction du dépassement, ne jamais présenter un théorème dépendant d'un lemme en erreur comme compilé.

**Fermé dans le build principal** (axiomes standard). Lemme (1), `Terminal/ZetaRealSegment.lean` : `ζ(σ) ≠ 0` pour `0 < σ < 1`, par `RHV3Lean.thm_noRealZetaZeroInOpenUnitSegment` (déjà dans la base : borne de Mellin explicite `‖Λ₀(σ)‖ < 4 ≤ 1/σ + 1/(1−σ)` ; l'inventaire antérieur qui le déclarait absent de rhv3_lean était faux et est corrigé partout). Lemme (2), `Terminal/ArgumentPrinciple.lean` (28 théorèmes, 1 objet) : `rectBoundaryIntegral_inv_sub` (`∮ dz/(z−a) = 2πi` sur un rectangle contenant `a`, primitives `log(z−a)` sur trois côtés et `log(−(z−a))` sur le côté gauche, `arg(−v) = arg v ∓ π`), `rectSidesIntegrable_of_continuousOn`, `rectBoundaryIntegral_add/_const_mul/_congr/_sum`, `exists_entire_div_pow` (division par `(z−ρ)^m` via la factorisation locale de Mathlib, extension par `Function.update`), `exists_entire_factorization` (induction sur le `Finset` des zéros), `logDeriv_factorization`, `argument_principle_rect` (`∮ f'/f = 2πi Σ ord_ρ f` pour `f` entière sans zéro au bord), `completedEntire_analyticOrderAt_ne_top`, `completedEntire_argument_principle` (`(2πi)⁻¹ ∮ ξ₁'/ξ₁ = Σ_{fenêtre ouverte} zetaZeroMultiplicity ρ`).

**Cible de travail** `RHV6FreshTDD/Chain.lean` (un seul fichier : lake ne construit pas un module qui importe un module en erreur, donc chaque théorème composé est élaboré dans le fichier des buts ouverts). Obligation 1 : (a) `completedEntire_rect_integral_fifteen`, but `⊢ (2πi)⁻¹ ∮ ξ₁'/ξ₁ = 1` ; (b) `no_zero_at_height_fifteen`, but `⊢ False` depuis `ξ₁(ρ) = 0`, `Im ρ = 15`. Puis, composés et conditionnels : `rect_boundary_nonvanishing_fifteen`, `upperCountWithMultiplicity_fifteen`, `anchor_canonical_one`, `anchor_mirror_eq_self`, `anchor_bottom` (inconditionnel : `canonicalZero_one_bottom`), `anchor_dominates_onLine`. Obligation 2 : `upper_member_refuted`, but `⊢ False` au membre haut sous l'ancre (contexte inchangé : dépassement, persistance, détection, champ constant, horizon, reconstruction exacte lissée, miroir bas, paire non nulle, exclusion d'insertion). Chaîne : `universal_captivity` → `universal_captivity_anchored` → `all_upper_onLine` (`inside_field_forces_line`) → `riemannHypothesis_terminal` (`riemannHypothesis_of_captivity_onLine`) → `regime_conserved` (`noRegimeChange_iff_riemannHypothesis`) → `height_progression` (`allVertical_of_noRegimeChange`). Signature TDD 53a8e76db7d4 (trois buts). Les deux lemmes numériques exigent un évaluateur certifié de `ξ₁'/ξ₁` en intervalles sur les quatre côtés ; E185 reste un certificat externe, jamais un axiome.

**Retirées de la cible de travail, consignées ici avec leur dernier but** (code : commits 5ee7914d à fca2fa3c) : `riemannHypothesis_without_premise` (`WithoutPremise.lean:24`, ancre accordée, rang haut supposé, but `⊢ False`) ; `riemannHypothesis_without_premise_composed` (`WithoutPremiseComposed.lean:37`, but `⊢ ∃ θ < β_n, ∃ C, ∀ x > 1, ‖smoothedRemainder x‖ ≤ C x^θ`, acquis le plus proche exposant `1`) ; `admissible_exponent_below_upper` (`UniformTail.lean:34`, but `⊢ ∃ θ < β_n, ∃ C, ∀ x > 1, ‖precedingSum H x + followingSum H x‖ ≤ C x^θ`, cible sur la somme, renforcement `‖P_H‖ + ‖S_H‖` retiré) ; `onLine_of_complement_rigidity` (`ComplementRigidity.lean:21`, but `⊢ β_n = 1/2` : la rigidité retrouve `β_n`, elle ne le fixe pas). Aucune n'est une preuve ni une impossibilité ; leurs énoncés mathématiques restent dans le maître mathématique avec leur statut.

**Borne racine-log** : aucun théorème `|R| ≤ C√x log x` dans aucun canal du dépôt ; la seule borne acquise est linéaire dans le canal lissé (`smoothedRemainder_linear_growth`), transportée au canal normalisé en `|R̃| ≤ C√x` ; le retrait signé reste un résultat conditionnel (`SQRT_LOG_SIGNED`). Statut réécrit sans empilement (signature principale 1f3e427d829a ; prémisse et porteurs inchangés). Lock inchangé.

## 24. Route du déficit de comptage : saturation certifiée et inégalité de prolongement (2026-10-09)

Directive de l'auteur (deux messages collés, après la livraison « deux obligations ») : la démonstration à prolonger est celle d'un déficit de comptage nécessairement nul ; `N(T) = N₀(T) + 2W(T)` par réflexion, `W ≥ 0` croissant, `W = 0` sur la région certifiée ; obligation exacte `∀ H < T < U, N₀(U) − N₀(T) ≥ N(U) − N(T)` ; même obligation lue dans la géométrie (domination universelle du champ ⟹ `β ≤ 1/2`, miroir ⟹ `β = 1/2`) ; « utilise un TDD sur cette voie, laisse le compilateur nous aider » ; implémenter sur main, dans la cible de travail unique, build principal vert, prémisse inchangée, différences entières, ne pas confondre comptage ON et changements de signe, distinguer identité de comptage manquante / certification initiale manquante / interdiction d'apparition du déficit manquante.

**Fermé dans le build principal** (`Terminal/CountingDeficit.lean`, 27 théorèmes, 5 objets, axiomes standard ; `lake build RHV6Fresh` EXIT=0, signature 1f3e427d829a inchangée car la prémisse et ses porteurs ne changent pas) : `onCount`, `lowCount`, `highCount` sur la fenêtre fermée `upperWindow T` ; `upperCount_eq_on_add_low_add_high` ; `mirrorPoint_nontrivial`, `zetaZeroMultiplicity_mirrorPoint` (`m_{1−ρ̄} = m_ρ` par `zetaZeroMultiplicity_conj` et `zetaZeroMultiplicity_zetaReflect`, rhv3_lean), `mirrorPoint_mem_upperWindow`, `lowCount_eq_highCount` (`Finset.sum_nbij'`) ; `upperCount_eq_on_add_two_low`, `onCount_le_upperCount`, `zeroCountDeficit`, `zeroCountDeficit_eq`, `zeroCountDeficit_nonneg`, `lowCount_mono`, `zeroCountDeficit_mono`, `one_le_lowCount_of_low`, `lowCount_eq_zero_iff`, `saturation_iff_lowCount_zero`, `saturation_of_count_one` ; `CountingExtension H` (différences entières), `countingDeficit_le_of_extension`, `lowCount_eq_zero_of_saturation_extension`, `noLowerSide_of_counting`, `noOff_of_counting`, `riemannHypothesis_of_counting` (fermeture conditionnelle : vérifie que l'obligation SUFFIT), `extension_of_riemannHypothesis` (RH ⟹ prolongement) ; `extension_violated_iff`, `exists_contact_ge`, `upper_member_exceeds_at_contact`, `extension_of_no_upper`, `no_upper_of_extension`.

**Cible de travail** `RHV6FreshTDD/Chain.lean` (18 théorèmes, 3 buts, signature TDD b6bcd10a7ab2, `lake build RHV6FreshTDD` EXIT=1). Obligation 1 inchangée : (a) `completedEntire_rect_integral_fifteen` (ligne 66), (b) `no_zero_at_height_fifteen` (ligne 71) ; `saturation_fifteen := saturation_of_count_one upperCountWithMultiplicity_fifteen` et `zeroCountDeficit_fifteen` composés conditionnellement. Obligation 2 : `counting_extension_fifteen (h₁) (hSat) : CountingExtension 15` (ligne 143), TDD actif ; après `extension_violated_iff` le but est `⊢ False` avec en contexte `z` bas de hauteur `> 15`, son miroir `w` haut (`hUp`, `hwHeight`, `hwMult`, `hCount`), rang canonique (`n hn hwn hT`), sortie du champ et abscisse de dépassement (`hNotIn x₀ hx₀ hEx`), persistance (`hPersist`), contact authentique (`k hk hContact`), lecture par tout support (`hDetected`), champ constant (`hField`), horizon exact (`hHorizon`), reconstruction exacte lissée (`hRec`), interaction complète bornée par queue et résidu (`hInter`), planchers grammaticaux (`hGrammar`, `hPhase`), paire hypothétique non nulle (`hPairNonZero`), exclusion d'insertion (`hNoInsert`). Chaîne conditionnelle : `no_lower_member`, `all_upper_onLine`, `zeroCountDeficit_all`, `riemannHypothesis_terminal`, `universal_captivity_anchored` (conséquence), `regime_conserved`, `height_progression`.

**Retirés de la cible de travail** (code : commit 3674c407) : `upper_member_refuted` (ligne 119, but `⊢ False` au membre haut sous l'ancre, contexte `hUp hT hNot x₀ hx₀ hEx hPersist hDetected hField hHorizon hRec hMirrorLow hMirrorHeight hPairNonZero hNoInsert`), `universal_captivity`, `riemannHypothesis_of_universal_captivity`. Ils ne sont pas perdus : sous l'ancre, `CountingExtension H` ⟺ aucun membre haut (`extension_of_no_upper`, `no_upper_of_extension`), donc le but de `counting_extension_fifteen` est le même raccord, enrichi du comptage, du miroir de même multiplicité et du contact de dépassement.

**Trois distinctions** : (1) identité de comptage manquante : AUCUNE (partition, réflexion, `N = N₀ + 2W`, monotonie, saturation, fermeture conditionnelle, toutes compilées) ; (2) certification initiale manquante : obligation 1 (deux lemmes numériques ; E185 certificat externe, jamais axiome) ; (3) interdiction d'apparition du déficit manquante : obligation 2 (`counting_extension_fifteen`). Écart exact pour (3) : une inégalité démontrée, uniforme en l'abscisse, qui lise ensemble la contribution du membre haut, son complément et le reste exact ; rien dans le contexte n'est encore mis en contradiction. Aucune loi d'espacement, aucune borne racine-log, aucune conservation du régime introduite. Prémisse inchangée, lock inchangé.

## 25. Conservation du régime ON au passage authentique (2026-10-09)

Directive de l'auteur (collée) : réorienter immédiatement vers la conservation du régime ON au passage authentique ; cible
`VerticalPassage(o) ∧ o.zLater = p.zEarlier ∧ β_{p.zEarlier} = 1/2 ⟹ β_{p.zLater} = β_{p.zEarlier}`, sans supposer le prochain
membre ON ; types et signatures canoniques du dépôt ; engagement = définition actuelle ; ni conservation radiale, ni enroulement
entier, ni captivité universelle en hypothèse ; le déficit de comptage reste un contrôle et une fermeture disponible ; les
insertions synthétiques ne sont pas la preuve ; composer miroir, contacts, enveloppe, succession/rang/raccord, sollicitations
premières, reconstruction exacte et interactions ; réutiliser `psiRecoveredFromZeros_eq_psi`,
`smoothed_formula_recovers_weighted_prime_count`, `thm_localZeroDensity_le_log` (commit 51cf3728),
`weighted_zetaZeroMultiplicity_imagSquare_summable` ; TDD : rétablir le théorème, appliquer `engaged_regime_kept`, construire
l'expression commune, chercher le couplage ON du suivant, composer la poursuite et la fermeture, livrer le but exact.

**Fermé dans le build principal** (`Terminal/AuthenticPassageProfile.lean`, 14 théorèmes, 1 objet, axiomes standard ;
`lake build RHV6Fresh` EXIT=0, signature 1f3e427d829a inchangée) : `mirror_fixed_iff_onLine`, `engaged_mirror_annulled`,
`authentic_contacts`, `envelope_coupling`, `prime_event_solicitations`, `exact_reconstruction_profile`,
`arithmetic_recovery_profile`, `zero_weight_summable`, `engaged_passage_profile`, `bottom_exit_vertical`, `canonicalPassage`,
`canonical_onLine_of_conservation`, `riemannHypothesis_of_anchor_and_conservation`, `conservation_of_riemannHypothesis`,
`engaged_law_of_vertical_law`. Réutilisations vérifiées : `psiRecoveredFromZeros_eq_psi` et
`smoothed_formula_recovers_weighted_prime_count` (rhv3_lean, `ZetaSmoothedUnsmoothingP5`, `…ArithmeticBridge`),
`weighted_zetaZeroMultiplicity_imagSquare_summable` (rhv3_lean, `ZetaZeroHeightSummability`) : exploitées ;
`thm_localZeroDensity_le_log` : présent dans `rhv2_fresh/RHV2Fresh/Zeta/LocalZeroDensity.lean` (commit 51cf3728), hors du
périmètre d'import de RHV6Fresh (rhv3_lean seul, auteur 2026-10-02), non réutilisé ; aucun équivalent dans rhv3_lean.

**Cible de travail** `RHV6FreshTDD/Chain.lean` (18 théorèmes, 3 buts, signature TDD 84211412694e) : obligation 1 inchangée ;
obligation 2 = `radial_conservation_authentic` (forme canonique : `p` monte, départ ON de hauteur positive), forme de
l'auteur `radial_conservation_engaged` par `engaged_regime_kept` ; but `⊢ False` sous `β_l < 1/2`, contexte `p hE hV hOn hL
hMirror hFixed hLe hSucc hBond hContacts hEnvelope hEvents hCouplingIff h hBelow hLambda s hsH hCons hq hNoRenew hTranslate
hSecond hRenewIff hRec hArith hSummable hAlternate` ; chaîne `conservation_law`, `canonical_all_onLine`,
`riemannHypothesis_terminal`, `all_upper_onLine`, `regime_persists`, `regime_conserved`, `height_progression`,
`counting_extension_all`, conditionnelle.

**Retirés de la cible** (code : commit précédent 8d6ee8ac) : `counting_extension_fifteen` (ligne 143, but `⊢ False`, contexte
`h₁ hSat hNot z hz15 hLow w hw hUp hwHeight hwMult hCount n hn hwn hT hNotIn x₀ hx₀ hEx hPersist k hk hContact hDetected hField
hHorizon hRec hInter hGrammar hPhase hPairNonZero hNoInsert`), `saturation_fifteen`, `zeroCountDeficit_fifteen`,
`no_lower_member`, `zeroCountDeficit_all` (`universal_captivity_anchored` réintroduit ensuite comme conséquence de la récurrence canonique). La fermeture du déficit de comptage reste dans le
build principal (`riemannHypothesis_of_counting`) ; sous l'ancre le prolongement équivaut à l'absence de membre haut, et il
découle de la chaîne (`counting_extension_all`).

**Écart exact** : une inégalité ou une identité démontrée, lue sur les poids premiers et la reconstruction exacte, qui impose
`λ = 1` (couplage ON) au membre atteint ; elle doit être fausse sur « `e` ON ; `l`, `s` consécutifs à la même hauteur,
`β_l < 1/2` ». Toutes les identités du profil valent pour toute position radiale de l'arrivée. Contrôles numériques : E183 et
E187 (chaînes authentiques de 3/4/10/12 Tours avec complément complet, fenêtres 12/24/36, sollicitations, phases, enveloppes)
cités, non rejoués ; aucune mesure ne remplace une preuve universelle. Lock (auteur, 2026-10-09) : « Depuis un zéro ON engagé, prouver que les obligations du passage authentique et de la reconstruction arithmétique exacte maintiennent l'annulation du miroir : le prochain membre conserve la même partie réelle et la progression se poursuit par la hauteur. »

**Second message de l'auteur (2026-10-09)** : « conserve explicitement le premier membre canonique dans chaque raccord étudié »
(hauteur minimale et statut ON fixent son enveloppe ; domination sur les enveloppes ON par unité de multiplicité ; contribution
signée dans la reconstruction exacte, retrait, restitution du reste résiduel par toutes les suivantes ; phases et contacts
conservés dans les interactions sans supprimer le complément infini ; ne pas supposer la captivité universelle : conséquence à
démontrer puis à utiliser). Fermé (17 théorèmes au total dans `AuthenticPassageProfile`) : `anchor_constraints_at_passage`,
`universal_captivity_of_all_onLine`, `riemannHypothesis_via_captivity_of_conservation`. Cible de travail (21 théorèmes, 3 buts,
signature TDD bad7b0e2dacb) : `radial_conservation_anchored` (ancre en hypothèse explicite, contraintes de l'ancre composées
avant le profil du passage ; but `⊢ False` inchangé en nature) ; `radial_conservation_authentic` en découle sous
`anchor_canonical_one` ; chaîne : tout membre ON par récurrence (sans passer par RH) → `universal_captivity_anchored`
(conséquence) → `riemannHypothesis_terminal` par `riemannHypothesis_of_captivity_onLine`. Le premier membre est présent avec
son enveloppe fixée, sa domination ON et son retrait signé ; aucune de ces contraintes ne fixe la position radiale de l'arrivée.

**Troisième message de l'auteur (2026-10-09)** : « il y a forcément un lien entre deux zéros ON ; le premier zéro ne peut être
qu'ON et annule le miroir ; le prochain zéro ne peut pas être OFF à cause de son miroir qui serait le premier à être considéré ;
dans aucun cas le régime engagé ne change ; inutile d'insérer un OFF ; prolonge ces raisonnements ». Fermé (section 9 de
`AuthenticPassageProfile`, 26 théorèmes au total, axiomes standard) : `high_member_mirror_low_precedes`, `second_member_not_high`
(côté haut exclu par le miroir ; côté bas = cible), `canonical_vertical_of_history`, `exists_first_regime_break` (¬RH ⟹ premier
rang hors ligne, BAS, prédécesseurs ON ; par l'absurde, aucune insertion), `riemannHypothesis_iff_no_first_regime_break`,
`first_regime_break_profile` (sous l'ancre : passage qui monte depuis un membre ON, tout prédécesseur ON, `W(T) = 0` et
`N = N₀` sous la hauteur d'arrivée, `W(T_l) ≥ 1`, miroir après), `canonical_onLine_of_history_conservation` (récurrence forte),
`riemannHypothesis_of_anchor_and_history_conservation` (FERMETURE RENFORCÉE : la loi n'a à être démontrée qu'avec tout
l'historique ON en hypothèse), `history_conservation_of_conservation`. Cible de travail : `radial_conservation_anchored` reçoit
`hHist` (légitime par la fermeture renforcée) et dérive en contexte le déficit nul sous l'arrivée, le miroir après l'arrivée et le
déficit ≥ 1 à sa hauteur ; `conservation_law` en forme renforcée ; `canonical_all_onLine` par récurrence forte,
`canonical_all_vertical` ; `radial_conservation_authentic` et `radial_conservation_engaged` deviennent des conséquences de la
chaîne. But `⊢ False` inchangé en nature : l'historique ON, le déficit nul en dessous et le miroir après ne contredisent pas une
arrivée basse ; l'écart exact est le même. Texte collé par l'auteur (à considérer « avec prudence ») : il recouvre
`Terminal/CountingDeficit.lean` (`N = N₀ + 2W`, `W` monotone, saturation, `W(T) = 0 ⟺` aucun membre bas) ; son « hypothèse A »
(un OFF ajouterait +2 au-delà de `N(T)`) est circulaire, `N(T)` compte tous les zéros ; son « hypothèse B » (on ne peut pas
effacer des changements de signe) confond `N₀` (multiplicité analytique des zéros ON) et les changements de signe de `Z` ; la
saturation `N₀ = N` est certifiée sur une région finie seulement. Aucune de ces phrases n'est une dérivation ; aucune n'entre en
hypothèse. Prémisse inchangée, lock inchangé.

## 26. Chaîne unique intégrée dans le build principal, cible séparée supprimée (2026-10-09)

Directive de l'auteur (collée) : intégrer la démonstration entière dans une seule chaîne Lean importée par `RHV6Fresh.lean`, sur main,
rien à part ; déplacer la chaîne active de `RHV6FreshTDD/Chain.lean` dans un module de la cible principale, supprimer la cible TDD et
ses imports, conserver tous les lemmes acquis ; chaîne = comptage initial → premier zéro ON → conservation du régime au passage
authentique avec historique ON → tous les membres ON → RH ; conserver explicitement les contraintes du premier zéro, les contacts, la
reconstruction exacte, les interactions complètes et le résidu ; aucune prémisse ; buts non fermés réels, aucun `sorry`, `admit`, axiome
ou contournement ; une seule commande `lake build RHV6Fresh` ; livrer la sortie exacte du compilateur ; aligner les documents ; afficher
BUILD=FAIL s'il échoue. Second ordre du même message : la livraison se réduit à l'erreur de compilation et à son analyse, rien après.

**Fait** : `RHV6Fresh/Terminal/DemonstrationChain.lean` (21 théorèmes, contenu de l'ancienne cible déplacé mot pour mot, docstring
réécrite), importé par `RHV6Fresh.lean` après `Terminal/AuthenticPassageProfile` ; `RHV6FreshTDD/` supprimé, entrée `[[lean_lib]]`
retirée du lakefile, `tdd_build_output.txt` et `tdd_build_analysis.md` supprimés (historique git : commits 5ee7914d à 02370e57, audit
§22–25) ; `scripts/status.sh` réécrit : HEAD, BUILD, SORRY/ADMIT, AXIOMS, puis chaque erreur triée par fichier et ligne avec la signature
du théorème lue dans la source, le contexte complet et le but tels que Lean les écrit, puis l'analyse
(`main_build_error_analysis.md`, signature 5493b432ae44) ; rien après.

**Résultat** : `lake build RHV6Fresh` EXIT=1, BUILD=FAIL, trois erreurs `unsolved goals` : `DemonstrationChain.lean:61`
(`completedEntire_rect_integral_fifteen`, contexte `hCauchy`), `:66` (`no_zero_at_height_fifteen`, contexte `ρ hρ h15 hξ`, but `False`),
`:139` (`radial_conservation_anchored`, but `False` sous `β_l < 1/2` avec l'historique ON, le déficit nul en dessous, les contraintes du
premier zéro, le profil du passage, le miroir après, le déficit ≥ 1, `λ > 1`, le passage sortant de même hauteur, la reconstruction exacte,
les interactions complètes et le résidu, le canal arithmétique). Aucun `sorry`, aucun `admit`, axiomes relevés standard sur les modules
fermés. Tout théorème de la chaîne est conditionnel ; aucun terme terminal. Rien n'est fabriqué : ce sont les buts des preuves inachevées.

## 27. Correction de configuration : seconde bibliothèque `RHV6Demonstration` retirée (2026-10-09)

Retour de l'auteur (« récupère tes erreurs ») après la livraison §26 : une incohérence de configuration subsistait, la bibliothèque
`RHV6Demonstration` (racine `RHV6Demonstration.lean`, onze théorèmes de la règle du pivot, 2026-09-22, importait `RHV6Fresh` entier)
restait déclarée dans `lakefile.toml` et dans `defaultTargets`, contrairement à la règle « aucune cible séparée ».

**Fait** : fichier déplacé mot pour mot (git rename) dans `RHV6Fresh/Terminal/DemonstrationWithoutRH.lean`, imports explicites
(`Tower/CanonicalOrigin`, `Direct/PivotCell`, `Direct/PairTowers`, `Direct/Reached`, `Voyage/Progression`, `Grammar/ExpectedMinimum`),
docstring corrigée (les fichiers qu'elle citait pour le raccord à RH sont retirés du code), importé par `RHV6Fresh.lean` après
`Terminal/DemonstrationChain` ; hors de la chaîne active. Lakefile : `[[lean_lib]] RHV6Demonstration` retirée,
`defaultTargets = ["RHV6Fresh"]`. Le module compile seul (axiomes standard) ; `lake build RHV6Fresh` réexécuté : EXIT=1, trois buts
inchangés (`DemonstrationChain.lean:61`, `:66`, `:139`), signature 5493b432ae44. Aucun changement dans la chaîne.

Non traités (hors de cette correction, aucun énoncé Lean) : « retrait explicite de deux membres certifiés » et « borne quantitative issue
du comptage local » mentionnés par la relecture externe ; aucun théorème du dépôt ne les porte, ils ne sont pas présentés comme acquis.

## 28. Travail sur les trois obligations de la chaîne unique (2026-10-09)

Directive de l'auteur (trois obligations, corps de la chaîne principale, signatures conservées). Fait : (b) `eulerMaclaurinMain`, `zeta_sub_eulerMaclaurinMain_le`, `zeta_ne_zero_of_eulerMaclaurinMain` fermés (axiomes standard, réutilisent `Zeta0EqZeta` et `ZetaBnd_aux1b` de rhv3_lean) ; `no_zero_at_height_fifteen` réduit par réflexion et encadrement à N = 10000 à l'inégalité finie `‖σ+15i‖·10000^{−σ}/σ < ‖main_10000(σ+15i)‖`, `1/2 ≤ σ < 1` (contrôle mpmath : erreur ≤ 0,301, `min |ζ| = 0,6697`, non certifié). (a) `hCauchy` retiré (intégrande `ξ₁`, pas `ξ₁'/ξ₁`) ; contexte `hBd`, `hAP` ; le but équivaut au comptage. (c) contexte complété (inversions tangentielles, amplitude–résolution, retrait signé) ; but `False` inchangé. Non fait, et pourquoi : arithmétique d'intervalles démontrée pour `log`, `cos`, `sin` (≈ 10⁴ termes, uniformément en `σ`), évaluateur certifié de `Γ` complexe pour l'enroulement, obligation démontrée du passage authentique contredisant `β_l < 1/2`. `lake build RHV6Fresh` EXIT=1, trois buts (`DemonstrationChain.lean:92`, `:132`, `:190`), signature 8491bc1a7175. Statut habituel rétabli (SEMANTIC LOCK, explication, progrès, reste à faire, prémisses et suppositions, réfuté dans les maîtres et la démarche).

## 29. Deux premiers zéros, pas de comptage, relecture de l'auteur (2026-10-09)

Relecture collée de l'auteur : progrès validé sur l'ancre (encadrement d'Euler–Maclaurin, réflexion, retrait de `hCauchy`), pas sur la conservation ; documentation imparfaitement alignée (anciennes lignes d'erreur, mentions de la cible séparée) ; conclusion trop exclusive (« le comptage exige un évaluateur complexe complet » : méthode envisagée, pas nécessité démontrée) ; pour la transmission, « ajouter des identités au contexte ne suffit pas ». Second texte collé : récurrence forte sans circularité, verrou `λ_arrivée = 1`, deux leviers (retrait des deux premiers zéros certifiés ; comptage logarithmique local pour borner le complément infini).

Fait, FERMÉ (axiomes standard), `Terminal/CountingDeficit.lean` §6 (13 théorèmes) : `onCount_mono` ; parité `N ≡ N₀ (mod 2)` ; `all_onLine_of_lowCount_zero` (`W(T) = 0 ⟹` tout membre de hauteur `≤ T` est ON ; côté haut exclu par son miroir bas et de même hauteur) ; pas de comptage `lowCount_eq_zero_of_count_step` (`T ≤ U`, `W(T) = 0`, `N(U) < N(T) + 2 ⟹ W(U) = 0`) ; `extension_of_lowCount_zero` ; deux premières bandes : `N(15) = 1 ∧ N(22) = 2 ⟹ W(22) = 0`, les deux premiers membres canoniques ON et miroirs annulés (`first_two_canonical_onLine`), `15 < T₂ ≤ 22` (`canonicalZero_two_height_gt`, `canonicalZero_two_height_le` : le premier est simple, donc la fenêtre `22` contient un second point, `exists_second_point`). Chaîne : `first_two_zeros_control` (hypothèse explicite `N(22) = 2`, conditionnel à (a), (b) par l'ancre, hors de la récurrence). Docstring de (a) et analyse : « méthode envisagée (non la seule possible) ». Commentaires périmés corrigés dans `AnchorContour`, `AnchorStructure`, `AuthenticPassageProfile`.

Portée exacte : le pas de comptage certifie des bandes finies à partir de deux valeurs comptées (numériques, jamais admises) ; il ne dérive pas le prolongement à toute hauteur (`CountingExtension` ⟺ RH) : la phrase « un OFF ajouterait +2 » reste circulaire comme dérivation de RH et devient un théorème entre deux comptages donnés. Les deux leviers du second texte : le retrait des deux premiers membres est une identité (déjà disponible par `smoothed_first_removed_hasSum` itéré) qui n'apporte aucune borne ; le comptage logarithmique local (`N(t, t+1] ≤ …`) n'a aucun théorème dans le périmètre d'import (rhv3_lean), `thm_localZeroDensity_le_log` est hors périmètre ; aucun des deux n'a été ajouté au contexte de (c), conformément à la relecture. Build réexécuté : EXIT=1, trois buts inchangés (`:92`, `:132`, `:190`), signature 8491bc1a7175.

## 30. Interdiction levée : réduction de [3] à la borne du reste des premiers (2026-10-09)

Auteur : « je lève l'interdiction qui te bloque et je préfère des tentatives et des erreurs de compilation précises des hypothèses. » Fait, dans le corps de `radial_conservation_anchored` : (i) session parallèle (d3082a43) : coût de la première rupture `N(T_e) + 2 ≤ N(T_l)` (`hRuptureCost`, depuis `hNoDeficitBelow`, `onCount_mono`, `N = N₀ + 2W`, `hDeficitAtArrival`) et sa forme fermante `hCountStepCloses` ; (ii) lecture du pôle (`following_onLine_of_followingSum_sqrt`) sous le budget `√x` de `followingSum T_e` ⟹ `β_l = 1/2`, contradiction ; historique ON ⟹ tout membre de hauteur `≤ T_e` ON ⟹ partie finie bornée par `precedingBudget T_e · √x` (NOUVEAU, fermé : `precedingWeight`, `precedingBudget`, `precedingSum_le_budget_of_onLine`, `explicitIndex_upper_readings`) ; découpe exacte `R = P + F` ⟹ borne du reste ⟹ borne des suivants (`followingSum_sqrt_of_remainder_sqrt`, fermé). But affiché : `∃ C, ∀ x > 1, ‖smoothedRemainder x‖ ≤ C·x^{1/2}`. Portée : équivalent à RH (`riemannHypothesis_iff_remainder_sqrt_growth`), réduction sans perte sous l'historique ON ; aucune hypothèse ajoutée ; le but n'est plus `False` mais l'énoncé arithmétique exact qui manque, sans aucun zéro ; sa forme en comptage `N(T_l) < N(T_e) + 2` est le prolongement du comptage sur un pas. Acquis : exposant 1 (`smoothedRemainder_linear_growth`). Leviers de l'auteur mesurés contre ce but : retrait des deux premiers membres absorbé dans la partie finie ; comptage logarithmique local sans effet sur l'exposant. Fusion : rebase sur d3082a43 (conflit dans le corps résolu en conservant les deux réductions, le `suffices` parallèle devenu `hCountStepCloses`). Build réexécuté : EXIT=1, trois buts (`:92`, `:132`, `:279`), signature 5b07b1870d8e.


## 31. Piste du fond : progression de `li` et modulation par cellule (2026-10-09)

Auteur (trois textes collés) : mesurer, entre deux contacts `C_k`, `C_{k+1}`, la progression du fond `Δli_k = ∫ dt/log t` et la variation `Δb_{ρ,k} = −2∫ t^{β−1}cos(T log t)/log t dt` ; confronter fond, contraction des cellules, premier zéro et compensation complète des suivants ; hypothèse : « les variations arithmétiques exactes, rapportées à la progression du fond, empêchent durablement les compensations collectives de masquer une contribution dépassant le champ du premier zéro ».

Compilé, FERMÉ (`Terminal/BackgroundModulation.lean`, 17 théorèmes, 5 objets, axiomes standard, importé par `RHV6Fresh.lean`) : dérivée de `b_ρ` (`counting_pair_hasDerivAt`, primitive locale de `e^w/w` en hypothèse, `Ei` absent de Mathlib) ; rapportée à `li'`, la modulation EST la dérivée de la contribution brute `c = −2Re(x^ρ/ρ)` du canal `ψ` (`counting_modulation_eq_raw_derivative`) ; enveloppe relative au fond `2x^{β−1} → 0` pour tout zéro (`background_envelope_tendsto_zero`, aveugle au régime) ; échelle ON `−2x^{β−1/2}cos`, plate ⟺ ON (`onScale_envelope_flat_iff`, caractérisation) ; extrema `D_k`, décalage `log(D_k/C_k) = arctan(β/T)/T`, ON `arctan(1/(2T))/T` (`extremum_contact_offset[_onLine]`) ; borne de cellule `|Δb_{ρ,k}| ≤ 2C_k^{β−1}Δli_k` (`cellModulation_abs_le_at_contacts`, individuelle).

E188 (`experiments/e188_background_cells_modulation.py`, 34 s, 37 PASS, 0 FAIL ; un contrôle de cumul de `∫_x^∞ dt/(t(t²−1)log t)` échouait d'abord par arrondi de sommation (1,2e−13), corrigé en sommant depuis la queue (5,6e−17), tolérance inchangée) : formules 1a–1e vérifiées (erreurs ≤ 1e−13) ; contre-vérification indépendante à 30 chiffres (premier zéro, `x = 100`, cellule `k = 30`). Cellules (15/100/300 zéros, `X = 1e6`, 408 647 cellules) : rapport `|Δb|/(2C_k^{β−1}Δli)` maximal 0,636 (≈ 2/π) ; pentes ζ fond −0,500, échelle ON 0,000 ; `W_δ` (δ = 0,1 ; 0,25) fond `δ − 1/2 < 0` (ne sépare pas), échelle ON `±δ` (sépare). Événements premiers (`J` avec puissances, `p ≤ 1e6`) : le résidu RMS des incréments passe de 0,753 (N = 1) à 0,714 (N = 300) sur `p ≤ 1e5` : un saut unité n'est pas résolu par 300 zéros (troncature, non bornée). Fenêtres 12/24/36 : `|premier| > |demande|` sur 1,4–2,2 % des fenêtres, masquage au sens défini 0,3–0,7 %, verrou `|#AB − #BA| ≤ 1` partout. Retrait signé : intervalle `[−B − b_1, B − b_1]` tenu ; `|S| ≤ B − |b_1|` violée 14/4000 (forme fausse confirmée).

Relation manquante identifiée : `dJ = dψ/log t` ; par sommation partielle, `J − li` et `ψ − x` ont le même exposant de croissance. L'hypothèse de l'auteur, prise collectivement à l'échelle ON, est donc la croissance critique `θ* = 1/2` (⟺ RH), c'est-à-dire le but [3] (`∃ C, ∀ x > 1, ‖smoothedRemainder x‖ ≤ C√x`) ; la normalisation par le fond ne la rend pas plus faible et ne sépare pas le monde témoin. Aucun but fermé ; build réexécuté : trois buts inchangés, signature 5b07b1870d8e. Retrait du fichier résiduel `RHV6FreshTDD.lean` (cible supprimée le même jour ; il importait un module inexistant, non compilé).

## 32. Étages `k = n` et attendu du membre suivant (2026-10-10)

Compilé, FERMÉ (`Terminal/StageCell.lean`, axiomes standard ; 39 théorèmes et 6 objets nouveaux, 5 théorèmes et 2 objets de la partie finie déplacés depuis `DemonstrationChain.lean`) : contacts d'étage (`contactMinusAt_eq_exp_stage`, `contactMinusAt_succ_eq_exp_stage`, `stageLogStart_pos`) ; `L_k = li(C_{k+1}) − li(C_k)` (`integral_expDiv_eq_cellBackground`, `stageBackground_eq_cellBackground`) ; bornes avant / traversant / après `v = 1` et `L ≥ e·W` (`stageBackground_before`, `_crossing`, `_after`, `_ge`, `stage_cases`) ; `L/W ≥ e^u/u` après 1, sans décroissance supposée ; `D_k ∈ ]C_k, C_{k+1}[` (`modulationExtremum_mem_cell`) ; `|Δb| ≤ 2e^{(β−1)u}L` (`stageModulation_abs_le`) ; rapports `L/a`, `L/a²` (`stage_ratios_ge`) ; étage canonique (`canonical_stage`) ; attendu `F_{]H,H']} = R − P_H − Q_{H'}` (`expected_next_fiber`, `_increment`) ; queue `‖Q_H‖ ≤ budget(H)·x`, `budget → 0` (`followingSum_norm_le_budget_linear`, `followingBudget_tendsto_zero`) ; enveloppe admissible d'exposant 1 (`expected_next_fiber_bound`) ; lecture locale (`nextFiber_growth_bounds_each`, `nextFiber_onLine_of_sqrt`, `expected_sqrt_iff_remainder_sub_tail_sqrt`).

Chaîne : `radial_conservation_anchored` (`:191`) compose l'attendu, la queue, l'enveloppe et les étages de l'arrivée ; le but devient `∃ C, ∀ x > 1, ‖R(x) − Q_{T_l}(x)‖ ≤ C√x`, LOCAL (plus faible que la borne du reste entier, ⟺ RH), mais équivalent sous l'historique à « la fibre de `T_l` est ON » : forme exacte de la conclusion locale, non une dérivation. Inégalité précise manquante : borner `R − Q_{T_l}` à l'échelle `√x`, soit par des bornes séparées de `R` (premiers) et de `Q_{T_l}` meilleures que l'exposant 1, soit par une corrélation démontrée entre les deux. Canal `J` : formule explicite absente, obligation de transport explicite, rien importé.

E189 (`experiments/e189_stage_cells_expected_next.py`, 108 s, 19 PASS, 0 FAIL ; script délégué, vérifié) : bornes Lean vérifiées sur 300 étages (32 avant, 3 traversants, 265 après) ; `L/W` ∈ [2,72 ; 3,57], 215 hausses / 84 baisses ; `u_n` non monotone (57 baisses sur 299) ; étages de 3 et 4 Tours toujours chevauchants ; formule explicite de `J` vérifiée en signe (x ≤ 500, résidu 9e−3) ; `ΔQ − Δb_n` porté par les suivants ; intervalles depuis l'historique seul : seule la borne supérieure triviale `u_n < (π/2 + nπ)/T_{n−1}` ; le balayage ne localise pas `T_n` (couverture 14/299 au seuil de la queue ; seuils plus larges non historiques) ; inversion tangentielle : `β` non borné sur 243/255 boîtes. Observations sur un nombre fini de zéros publiés.

## 33. Relecture d'E189 : prédicteur lié, seuils démontrés, singularité de l'inversion (2026-10-10)

Relecture de l'auteur (quatre défauts vérifiés d'E189 : balayage à `β = 1/2` fixé ; critère sans la queue ; seuils lus sur les membres futurs ; rectangle de combinaisons indépendantes de contacts ; plus une erreur de rédaction dans `beta_box` : `β = T cot θ` est singulière aux ZÉROS de la tangente, nulle à ses pôles). Compilé, FERMÉ (axiomes standard) : `Terminal/StageCell.lean` §6 (8 théorèmes : `followingSum_term_summable`, `tail_window_increment_bound`, `tail_history_cut_bound`, `tail_joint_functional_bound`, `expected_next_fiber_joint`, `expected_next_fiber_window_bound`, `followingBudget_pos_of_above`, `fixed_cut_budget_not_sqrt`) ; `Terminal/TangentialInversion.lean` (2 théorèmes : `inversion_sin_cos_ne_zero`, `inversion_radial_cos_div_sin`). Chaîne : `radial_conservation_anchored` compose `hWindow`, `hHistoryCut`, `hJoint`, `hFixedCut`, `hInversionSingular` ; but [3] inchangé en nature (`∃ C, ∀ x > 1, ‖R(x) − Q_{T_l}(x)‖ ≤ C√x`), signature 3a299cda6675. Portée exacte rappelée : `followingBudget → 0` est une limite en la coupure ; à coupure fixée, `budget·x` n'est jamais `C√x` (`fixed_cut_budget_not_sqrt`).

E189 CORRIGÉE (`experiments/e189_stage_cells_expected_next.py`, 39 s, 26 PASS, 0 FAIL ; Tâches 1–3 inchangées ; Tâches 4–5 remplacées ; `data/e189_linked_predictor.csv`, `data/e189_j_channel_next.csv` ; anciens `e189_admissible.csv`, `e189_trivial_intervals.csv` supprimés) : prédicteur lié dans le canal lissé (seule représentation démontrée) : attendu `Y = R − P_{T_{n−1}}` depuis l'historique ON, candidat `(β, T, m = 1)` avec miroir pour `β < 1/2`, fenêtres de l'historique seul (cellule d'étage du membre engagé, 12/24/36 événements premiers ancrés au plus grand premier `≤ C⁻_{n−1}`), critère `|Y − F| ≤ S_up(T)·x` à tous les points, `S_up(T) = 4∫_T^∞ N_up(t)/t³ dt` (Rosser 1941, externe), jamais un zéro futur dans la construction. Résultats (299 rangs) : couverture du vrai `(1/2, T_n)` 299/299 à toutes les configurations ; AUCUNE réduction (19000/19000 paires, largeur `T` = toute la plage de 10, `β` de 0,05 à 0,5 ; réduction 1,0000 par fenêtre ajoutée) ; `τ_cert / nécessaire` médian 431,6 (cellule seule) → 21,8 (36 événements) à 300 zéros (12,1 à 15, 17,8 à 100) ; queue mesurée ≤ 0,10 de `τ_cert` ; budget mesuré à 5000 zéros = 0,52–0,65 de `S_up` ; résidu au-delà de 5000 ≤ 0,027 de sa borne ; filtre conjoint par différences : 0 exclusion de plus que le point par point (inégalité triangulaire), `M_sup` échantillonné `= M_triv` au quatrième chiffre ; inversion des paires admissibles exacte (1e−43 en 50 chiffres ; 1,3e−8 en double précision par conditionnement `T log C⁻ ≈ nπ`), phase dans `]arctan T, π/2[` sur toutes les paires ; contrôle ON séparé identique. Canal `J` : identité `Y_r = ΔF_r + ΔQ_après,r` vérifiée au résidu près (mesure), `|ΔQ_après|/|ΔF|` médian 2,0 (cellule), 1,8 / 4,2 / 3,0 (12/24/36), aucun seuil démontré, aucun balayage. Verdict : la borne démontrée d'exposant 1 ne localise pas la fibre suivante ; l'expérience initiale montrait l'échec d'un critère tronqué, pas l'impossibilité du prédicteur (phrase retirée des réfutations) ; l'inégalité exacte restante : une borne démontrée de `Q_{T_l}` (coupure fixée) d'exposant `< 1`, ou une valeur démontrée de `M` strictement sous `Σ|λ_r| x_r` (répartition des hauteurs de la queue).

## 34. Couche grammaticale finie sur un petit ensemble de Tours (2026-10-10)

Directive de l'auteur (depuis 12ac7412) : ensembles de trois et quatre membres canoniques consécutifs, fenêtres de 12/24/36 événements, canaux de transition séparés, magnitudes, ordre, `Δli_r` exact, identité `Y_r = ΔR_r − ΔH_r = ΔF_r + ΔQ_r`, complément borné par les théorèmes acquis, cinq hypothèses à critère quantitatif, séparation « écart imposé par une rupture > compensation maximale démontrée du complément » à dériver des deux côtés. Compilé, FERMÉ (`Terminal/FiniteGrammarLayer.lean`, 11 théorèmes, axiomes standard) : `event_identity`, `window_identity` (télescopage, `window_increments_telescope`), `window_complement_bound` (`‖Σ ΔQ_r‖ ≤ budget(H')(x_0 + x_m)`), `rupture_discriminable` (`2τ < ‖F₁ − F₂‖ ⟹ ¬(‖Y − F₁‖ ≤ τ ∧ ‖Y − F₂‖ ≤ τ)`), `true_fiber_excludes_alternative` (+ `_joint` via `expected_next_fiber_joint`), `low_pair_envelope_eq` / `_ge` (`x^{−d} + x^{d} = 2 + κ ≥ 2 + (d log x)²`), `rupture_window_curvature_floor` (`κ(p_{n+m}/p_n, d) ≥ (d log(1 + 3m/p_n))²`, `m` pair, par `primeAtRank_window_ge_three_mul`), `separation_excludes_profile` (profil admissible ⟹ à moins de `2·budget·x` de la fibre vraie). Chaîne : `hWindowIdentity`, `hComplementWindow`, `hDiscriminable`, `hRuptureFloor`, `hLowEnvelope` en contexte de `radial_conservation_anchored` ; trois buts `:94`, `:134`, `:192`, signature 32dc308d2855. Contrainte grammaticale effectivement ajoutée : le plancher de courbure par fenêtre (`rupture_window_curvature_floor`) ; gain démontré sur les enveloppes admissibles : NUL tant que la borne du complément reste d'exposant 1 ; utilisation dans le but terminal : la séparation est écrite (`separation_excludes_profile`), son antécédent « le profil ON de l'arrivée est admissible » n'est dérivé nulle part (= but [3]).

E190 (`experiments/e190_finite_grammar_layer.py`, 37 s, 14 PASS, 0 FAIL ; figures `e190_fig1..4`, CSV `e190_channels/rupture_gap/admissible`) : grammaire par fenêtre vérifiée sur 897 fenêtres (comptages AA/BB/AB/BA, `|#AB − #BA| ≤ 1`, alternance, `g = 6M + a`, `ΣL_r`, `ΣΔli_r = li(p_fin) − li(p_0)`, `ΣΔθ`, `ΣΔlog A` à 4e−16) ; identité `Y = F_vrai + Q + résidu` pour `g = 1, 3, 4` et par événement (résidu ≤ 0,027 de sa borne) ; `τ ≥ |Q|` partout (max 0,10) ; fait triangulaire : les lectures 2–5 n'excluent aucun candidat de plus que le ponctuel (0 sur 44 551 filtres) ; `M_need ≤ M_triv` partout (ρ max 0,102) ; couverture 299/299 sous toutes les lectures ; `κ_plancher ≤ κ_réel` sur toutes les fenêtres. Verdicts : H1 POSITIF sur la mesure (ρ médian par canal AA 5,6e−4, AB 3,9e−4, BA 6,1e−4, BB 3,6e−4 contre global 6,8e−3 ; canaux < global sur 299/299 rangs à m = 12), NON TESTABLE comme exclusion sous la borne démontrée ; H2 NÉGATIF (préfixes 8,5e−3 ≥ canaux 4,8e−4 : l'ordre complet n'ajoute rien aux canaux) ; H3 NON TESTABLE (19000/19000 couples sous toutes les lectures, largeur `T` 9,99 ; ensembles HYPOTHÉTIQUES à `ε = 0,5` : 19000 / 1640 / 1640 / 1589 / 7, couverture 1,00 / 0,94 / 0,94 / 0,94 / 0,66 : oracle, non certificat, non emboîté) ; H4 NÉGATIF (signal/borne 1e−4–3,5e−4 ; signal/complément 0,19–0,53 par canal contre 0,06 global, sans sens certifié) ; H5 NÉGATIF (`G/(2τ)` à `d = 0,2` : médiane 5,8e−4, max 1,85e−2, sup dense 4,3e−2 ; à `d = 0,45` max 3,0e−2 ; aucun point avec `G > 2τ` ; `κ_plancher/κ_nécessaire ≈ 5e−5`). La borne démontrée dépasse le besoin d'un facteur 100 à 1000. Premier but exact restant : une borne DÉMONTRÉE du complément `Q_{T_l}` à coupure fixée d'exposant `< 1` (ou `M < Σ|λ_r| x_r` démontré par la répartition des hauteurs de la queue), seule réduction possible du but [3] par cette couche ; les lectures par canaux ne feraient gagner qu'un facteur mesuré ≈ 10 sur `ρ`, insuffisant seul (facteur 100–1000 requis).


## 35. Ancre : récupération d'E176 et raccord à la chaîne (2026-10-10)

Demande de l'auteur : récupérer E176, ses certificats, les théorèmes d'ancrage, les raccorder à la chaîne unique. Constat
vérifié : E176 (commit 02bd2b09, 2026-10-05) est un certificat EXTERNE (Arb ; Turing et Backlund ; N(14) = 0, N(15) = 1,
N(17) = 1, N(23) = 2, N(28) = 3 ; changements de signe de Z sur [14, 17], [17, 23], [23, 28]) ; sa sortie écrit « aucune
preuve Lean » ; aucun commit de l'historique ne contient de vérification Lean de ces comptages. Termes d'ancrage Lean réutilisés
sans modification : `anchor_of_count_one`, `completedEntire_argument_principle`, `upperCount_closed_eq_open_of_no_boundary`,
`zeta_ne_zero_of_eulerMaclaurinMain`, `completedEntire_real_ne_zero`, CountingDeficit §6, `certified_three_onRadii`. Nouveau,
fermé : CountingDeficit §7 (5 théorèmes : `upperWindow_mono`, `upperCount_ge_of_canonical_le`, `canonical_in_band_of_count_step`,
`first_three_canonical_onLine`, `upperCount_band_eq`) ; chaîne : `upperCount_zero`, `first_three_zeros_control` (N(23), N(28) en
hypothèse du contrôle, hors de la récurrence). La coupure 15 de l'ancre est une coupure certifiée d'E176 : aucun transport requis.
Vérificateur manquant, obligation précise : (V1) `∀ σ ∈ [1/2, 2], 0 < Re ζ(σ + 15i)` dans Lean (ferme [1]) ; (V2)
`θ(15)/π + 1 ∈ ]1/2, 3/2[` par Stirling complexe à reste explicite et réduction de l'intégrale de bord à `θ/π + 1 + S` avec
`|S| < 1/2` sous (V1) (ferme [2]). Trois buts inchangés.

## 36. Une seule erreur : le cas β < 1/2 au membre suivant (2026-10-10)

Directive de l'auteur : la seule erreur de la chaîne est au membre qui suit le zéro engagé, cas `β < 1/2` (le côté haut est
exclu, `hLe`). Fait : l'ancre est portée par l'hypothèse nommée `hE176 : upperCountWithMultiplicity 15 = 1` (comptage certifié
par E176, externe) dans tous les théorèmes qui en dépendent ; les anciens buts (a), (b) deviennent des théorèmes fermés sous
leurs certificats (`no_zero_at_height_fifteen hFin`, `rect_boundary_nonvanishing_fifteen hFin`,
`upperCountWithMultiplicity_fifteen_of_certificates hFin hInt`), sans suppression du travail de réduction ; la dernière
réduction de [3] (`apply hFiberCloses`) est retirée du corps : le but affiché est `False` sous `hBelow : β_l < 1/2`, les
fermetures disponibles restant en contexte. Build : une erreur, `DemonstrationChain.lean:199`, signature 2202311e0156. Terme
final : `riemannHypothesis_terminal : hE176 → RiemannHypothesis`. Lock réécrit en conséquence.

## 37. Réalignement sur les acquis historiques (2026-10-10)

Directive de l'auteur en neuf points. Recherche : commits ca45d39e (anneau ON), 1ab93109 (deux premiers zéros), 02bd2b09
(E176, Python/Arb, CSV), 095fe286 (réduction de la prémisse), 2ef65b58 (bandes d'E176), leurs parents, toutes les branches,
`git log -S` sur les fichiers `.lean` (`upperCountWithMultiplicity 15`, `Backlund`, arithmétique d'intervalles) et les bases
rhv3_lean, rhv2_fresh, RHV5Fresh, rhv5_lean, rhv4_lean, rh_gap_criterion : AUCUN terme Lean ne certifie une valeur de
comptage ; `CanonicalT1`/`CanonicalT2` (rhv3_lean) ne sont pas numériques. Conséquences dans la chaîne
(`Terminal/DemonstrationChain.lean`, 31 théorèmes) : le paramètre `hE176` (5bb69b5f) est retiré, les signatures historiques
de 2ef65b58 sont rétablies (`anchor_canonical_one`, `riemannHypothesis_terminal : RiemannHypothesis`, …) ; les vérifications
du certificat sont deux buts ouverts dans la bibliothèque : (V1) `eulerMaclaurin_fifteen_certificate` (`:121`), (V2)
`completedEntire_rect_integral_fifteen` (`:155`) ; les réductions fermées sont conservées
(`no_zero_at_height_fifteen_of_certificate`, `upperCountWithMultiplicity_fifteen_of_certificates`). Composés : `canonical_onLine_step`
(fermé) et `first_three_members_geometry` (conditionnel). Transmission (`:238`) : contexte complété par `towerSymmetric_iff_onLine`,
`engaged_step_mirror_annulled_iff`, `tower_two_symmetries`, `engaged_step_all_constraints`, `rescaledTower_eq`,
`tower_central_invariant_iff`, `symmetric_winding_iff_onLine`, `whole_winding_iff_onLine`, `off_tower_not_inside_line_tower`,
`vertical_arrival_characterizes`, `regime_entry_diagonal`, `vertical_arrival_onLine_iff_fibre_singleton`,
`engaged_event_restriction`, `consecutive_ring_interior_empty`, `radius_envelope_of_le_half`, `radius_dominated_iff_gap`,
`low_member_not_dominated_on_axis`, `low_case_pair_leaves_ring`, `low_radius_decreases_between_contacts`,
`radius_step_eq_one_iff`, `normalizedRadius_onLine`, `onLine_ring_floor_pos`, `prisonAtInfinity_of_le_half`,
`not_insideField_iff_upper_or_small`, `lower_captive_of_height_margin` ; aucune ne contredit `hBelow`. Annexe A recomptée :
132 fichiers, 2101 théorèmes (l'ancien total 2123 n'était pas reproductible). Build : `lake build RHV6Fresh` EXIT=1, trois buts
(`:121`, `:155`, `:238`), journal `experiments/audit_semantique/main_build_error_20261005.txt`.

## 38. Attaque par le début, puis à rebours (2026-10-10)

Début : (V1) FERMÉ dans Lean. `zeta_sub_eulerMaclaurinMain_le_fine` (annulation par intervalle unité, `Terminal/EulerMaclaurinFine.lean`)
ramène N de 10000 à 10 ; `em10_fifteen_certificate` (`Terminal/EulerMaclaurinTenCertificate.lean`, 339 lemmes générés par
`experiments/e191_em10_certificate_generator.py`, constantes revérifiées par norm_num, seize sous-intervalles, marge 0,031,
axiomes standard) ⟹ `no_zero_at_height_fifteen`. (V2) réduit sans Γ : `Terminal/BoxCount.lean` (élimination de Γ, côtés),
`Terminal/BoxAnchor.lean` (`upperWindowOpen_count_of_zeta_boxes`) ; but restant `zeta_box_certificate_fifteen` (`:165`,
quatre faits sur ζ ; numérique : min |ζ| 0,22 et 0,18, enroulements 1 et 0). À rebours : la transmission (`:261`) se ferme par
`hCountStepCloses` dès un comptage local de la fibre d'arrivée, certifiable hauteur par hauteur par la même méthode de
rectangles, jamais uniformément. Build : EXIT=1, deux buts, signature 2c4392b77902.

## 39. Dominance du premier zéro et étages de captivité (2026-10-10)

Directive de l'auteur : définir la dominance du premier zéro et l'utiliser pour la captivité des zéros à venir (symétrie autour
de l'origine, contacts à l'intérieur, intervalles réduits, fréquences accrues, rayons diminués), par étapes qui se renforcent.
`Terminal/FirstZeroDominance.lean` FERMÉ (17 théorèmes, objet `DominanceStage`, axiomes standard) : étage entre zéros ON,
renforcement strict, composition, captivité, dominance du premier sous l'ancre sur tout zéro ON, étages canoniques consécutifs,
partie cinématique acquise sur tout pas qui monte, violation par une arrivée basse (symétrie, rayon près de l'origine, miroir
hors du champ du premier), fermeture du pas par l'étage de l'arrivée ou par la captivité de son miroir. Composé dans
`radial_conservation_anchored` ; but inchangé en nature (`False` sous `β_l < 1/2`) : l'étage force la ligne, sa dérivation
pour l'arrivée est le but. Build : EXIT=1, deux buts (`:166`, `:262`), signature a04170dcdea5.

## 40. Captivités sans supposer l'arrivée ON (correction de l'auteur, 2026-10-10)

Correction : la phrase « la dominance n'est démontrée que sur les zéros ON » (§39, analyse, lock) était fausse. Builds retrouvés :
43d5fbfd `RegimeCapture` (captivité par le premier partagé et encadrement du premier attendu par les contacts de la cellule ;
fichier retiré en fb8b2508, ménage de treize fichiers, code récupérable), e586d8dd `LocalRaccordCaptivity` (captivité
énergétique au raccord, passage qui monte, hauteur ≥ 2), 9aecca85 `FirstTowerHorizon` (domination par le premier zéro ON, toute
position radiale, jusqu'à un horizon borné ; membre ou miroir dans le champ sous condition de hauteur), 70c35dc0
`WholeWindingObligation` (enroulement des contacts à l'infini sur tout passage), 0cb8cd68 `FirstGainPremise` (domination
individuelle sous gain collectif et contrôle d'interaction explicites). `Terminal/CaptivityWithoutOn.lean` FERMÉ (4 théorèmes,
axiomes standard) : `regime_captive_of_prime` restauré (partie inconditionnelle ; les `def P…` de 43d5fbfd ne sont pas
restaurées), `support_ge_first_of_height`, `arrival_insideField_of_support` (pas qui monte + support ⟹ arrivée dans le champ du
premier sur `x ≥ 1`), `captivity_without_on_arrival` ; composés dans `radial_conservation_anchored` (`hCaptiveNoOn`,
`hGainDomination`). Portée : ces captivités valent pour un membre bas et ne contredisent pas `hBelow` ; seuls l'étage complet et
la captivité du miroir équivalent à l'arrivée ON. Build : EXIT=1, deux buts (`:167`, `:263`), signature 22f560e47efe.

## 41. Certificat (V2) de l'ancre fermé (auteur, 2026-10-10 : « attaque le but 1 »)

- Modules : `Terminal/ZetaBoxGeneric.lean` (développement d'ordre un, interpolation, positivité par morceau, découpage des côtés, raccords) ; `Terminal/ZetaBoxNumeric.lean` (e^{−iθ} certifié, puissances, minorations par terme, queue, constante de reste) ; `Terminal/ZetaBox/*` générés par `experiments/e192_zeta_box_certificate_generator.py`.
- Certification : 117 morceaux pour B₁, 76 pour B₂, N ≤ 40 ; constantes rationnelles revérifiées par `norm_num` et `decide`.
- Enroulements : ζ fait 0 tour sur B₁ et −1 sur B₂ ; `∮_{B₁} = 2πi` et `∮_{B₂} = 0`.
- Le terme `ZB.Cert.zeta_box_certificate` ne dépend que des axiomes standard.
- Conséquences : `zeta_box_certificate_fifteen` est fermé. Avec (V1), N(15) = 1 et le premier zéro ON sont démontrés sans hypothèse.
- `lake build RHV6Fresh` : EXIT=1, une seule erreur, la transmission `DemonstrationChain.lean:263` ; signature 8f06168053ed.

## 42. Lecture conjointe de la fibre d'arrivée (auteur, 2026-10-11 : « attaque immédiatement la fonctionnelle conjointe »)

- Module : `Terminal/JointComparison.lean` (5 théorèmes, objet `fiberBudget`, axiomes standard).
- Démontré séparément : majoration indépendante de l'attendu `Σλ(R − P)` (exposant 1, historique ON), compensation du complément entier `budget(T_l)·M`, plafond du signal `fiberBudget·Σ|λ|x`.
- Fermeture : signal > majoration + compensation ⟹ contradiction. Condition nécessaire avec la borne d'exposant 1 : `C < fiberBudget`.
- Non démontré : minoration du signal signé de la fibre ; majoration de `Σλ_r R(x_r)` meilleure que `C·Σ|λ|x`.
- Le plancher de courbure porte sur une enveloppe ; il n'est pas utilisé comme minoration du signal.
- `lake build RHV6Fresh` : EXIT=1, une seule erreur `DemonstrationChain.lean:264`, but = l'inégalité stricte ; signature b7a010412f02.

## 43. Première rupture et son miroir dans un groupe fini de suivants (auteur, 2026-10-11)

- Module : `Terminal/MirrorGroupNonCompensation.lean` (5 théorèmes, axiomes standard).
- Historique ON retiré exactement (`R − P_{T_e} = G + Q_{H''}`), groupe `]T_e, H'']` fini, queue conservée.
- Non-compensation sensible au miroir : `β* = 1 − β_l > 1/2` dans le groupe ⟹ aucune borne `C·x^θ`, `θ < 1 − β_l`, du groupe (lecture du pôle).
- Fermeture : borne `C·x^θ`, `θ < 1 − β_l`, de `R − Q_{H''}` ⟹ contradiction ; ni progression verticale après l'arrivée, ni budget « borne moins amplitude du premier ».
- Non démontré : cette borne (démontrée à l'exposant 1 seulement) ; minoration quantitative du signal signé en abscisses finies. La grammaire borne phases et fenêtres, pas la taille de `R` ; aucune fenêtre de premiers identifiée à un groupe de zéros.
- `lake build RHV6Fresh` : EXIT=1, une seule erreur `DemonstrationChain.lean:265`.
- Correction (même jour) : `R − Q_{H''} = P_{H''}` (`remainder_sub_tail_eq_preceding`) ; l'ancien but bornait une somme finie contenant le miroir, faux sous `β_l < 1/2`, et non indépendant. La phrase « plus faible que √x » est retirée. Le but devient `∃ θ < 1 − β_l, C, ‖R‖ ≤ C·x^θ` (`mirror_closes_of_remainder_growth`), écrit sur les premiers seuls ; seul l'exposant 1 est démontré.

## 44. Revue : raffiner le manque arithmétique (auteur, 2026-10-11, trois prompts)

- Approche corrigée : `mirror_closes_of_remainder_growth` n'utilisait ni historique, ni contacts, ni grammaire, et son seuil dépend du membre supposé hors ligne ; il reste en contexte, il n'est plus le but.
- Prompt 1, `Terminal/PrimeBlockDecomposition.lean` (10 théorèmes) : blocs aux entiers + couverture, constantes explicites ; blocs d'exposant 1 démontrés.
- Prompt 2, `Terminal/PrimeTransitionDecomposition.lean` (11 théorèmes) : premiers / puissances (puissances démontrées sous tout exposant `> 1/2`), quatre transitions + bord exacts, majoration unilatérale par les états (densité 1/3), aucune minoration.
- Prompt 3 : seuil `1 − β_l` du miroir ; but réduit au terme signé des premiers `|primePart N − N²/2| ≤ C N^{1+θ}` ; minoration quantitative du signal signé non démontrée.
- `lake build RHV6Fresh` : EXIT=1, une seule erreur `DemonstrationChain.lean:266`.
- Ajout (avec Sonnet) : `primeMass_blocks_of_prime_blocks`, `prime_blocks_zero_free_strip` (blocs d'exposant `1 + θ` ⟹ tout zéro sous `max θ (1/2)`). Recherche : rien dans Mathlib, rhv3_lean, RHV6Fresh au-delà de Chebyshev ; `classicalZeroFree` est une définition inutilisée. Signature 09c112041f90.

## 45. Cycle de challenge (Fable, 2026-10-11)

- Sens réciproque démontré : `remainder_growth_of_zero_free`, `prime_blocks_of_zero_free` ; caractérisation `prime_blocks_iff_zero_free` (`θ > 1/2`) et forme future sous historique ON `prime_blocks_iff_future_zero_free` ; en contexte `hPastOn`, `hBlocksIff`, `hFutureIff`.
- Verdict : le but `:266` est exactement « tout zéro de hauteur `≥ T_l` sous `θ` », plus fort que l'exclusion du miroir ; la route de la lecture du pôle n'a pas de forme intermédiaire ; aucune autre liaison `Λ → β` compilée. Signature 5c914288ae9b.

## §46. Correctif : retour au but arithmétique sur `primePart` (auteur, 2026-10-11)

- La construction de la constante par `hFutureIff` est retirée ; `hFutureIff` reste en contexte. L'exposant `θ = 3/4 − β_l/2` et ses deux inégalités sont conservés.
- `PrimeTransitionDecomposition` §5 est fermé (axiomes standard) :
  - `boundaryPart_le` : le bord `{2, 3}` est dans `[0, 2N log 3]`.
  - `sum_transitionSum_eq` : la somme des transitions est la somme explicite sur les premiers `3 < p < N`.
  - `transitions_upper_acquired` et `transitions_lower_acquired` : les deux côtés signés, à l'exposant `1 + 1`.
  - `prime_blocks_of_transition_bounds` : la composition, de constante `C + 2 log 3`.
- But `:266` : `∃ C, ∀ N ≥ 2`, avec `Σ_{3<p<N} Λ(p)(N − p) − N²/2 ≤ C·N^{1+θ}` et `N²/2 − Σ ≤ C·N^{1+θ}`.
- Aucune estimation auparavant ouverte n'est démontrée. Signature 416e8210ead7.


## §47. Cellules et fenêtres de l'erreur signée (auteur, 2026-10-11)

`Terminal/PrimeCellError.lean` (22 théorèmes, 5 objets `primeTail`, `goalError`, `cellTheta`, `tailWeight`, `cellIncrement`,
axiomes standard). Conventions : `S(N) = Σ_{3<p<N} Λ(p)(N − p)` (`p < N` strict), `ϑ₃(M) = Σ_{3<p≤M} log p` (`M` inclus),
`p_k = nth Prime k`. Démontré : pas exact (`goalError_succ`), somme (`goalError_eq_sum`, `goalError_sub_eq_sum`), constance
de `ϑ₃` sur une cellule (`not_prime_between`, `cellTheta_on_cell`), identité de cellule avec bord partiel
(`goalError_in_cell`, `goalError_cell`), fenêtres (`goalError_window`, `goalError_window_profile` : longueur `≥ 3m`,
`|#AB − #BA| ≤ 1` ; `goalError_windows_12_24_36`), accumulation (`goalError_windows_accumulate`, `goalError_initial`,
`goalError_cumulative`), séparation premiers/bord/puissances (`primeMass_goal_split`), composition
(`goal_sides_of_cell_control`, signes séparés, constante `C + 1/2`). But `:267` : contrôle interne des cellules
`∃ C ≥ 0, ∀ M ≥ 1, ϑ₃(M) − M ≤ C M^θ ∧ M − ϑ₃(M) ≤ C M^θ`. E194 : identités vérifiées ; fenêtres 12/24/36 toutes
négatives jusqu'à 2·10⁶, aucune compensation entre fenêtres ; `E/N^{3/2}` −1,14 → −0,75 ; `sup|ϑ₃ − M|/√M = 2,07`
(observations). Signature c8afdff52190.

## §48. Voie locale par fenêtre de contacts acquis (auteur, 2026-10-11)

`Terminal/LocalWindowTransmission.lean` (11 théorèmes, 4 objets `contactWindow`, `historyRemoved`, `groupSignal`,
`windowMargin`, axiomes standard) et `first_passage_window_transmission` (chaîne, fermé). Fenêtre de contacts acquis du
départ ; retrait signé de l'historique ON (événements premiers exacts, majoration locale) ; identité exacte avec le groupe
d'arrivée et le complément entier ; marge admissible démontrée ; lemme de transmission réutilisable ; portée : séparation
exacte impossible (`window_separation_not_exact`). Voie globale conservée en contexte (`hGlobalRoute`). But `:268` :
séparation locale. E195 : sur la première fenêtre, signal bas hypothétique ≤ 0,195 de la marge ponctuelle (tout β_l) ;
le gain exige un `M` démontré `< Σ|λ|x` sur les profils de la queue. Signature 60791e0f2b68.

## §49. Consolidation 22/28 et expérience « RH retirée » (auteur, 2026-10-11)

Consolidation : `N(22) = 2`, `N(28) = 3` démontrés dans Lean (axiomes standard) par les rectangles de ζ aux hauteurs 22 et
28 (générateur `experiments/e196_zeta_box_height_generator.py`, méthode d'E192, côtés découpés en fichiers ; `Terminal/ZetaBox22/*`,
`Terminal/ZetaBox28/*`, troncatures `N ≤ 120` à 28) et `Terminal/BoxCountHeight.lean` (5 théorèmes). `first_two_zeros_control`,
`first_three_zeros_control` (coupures 15, 22, 28 ; 22 remplace la coupure 23 d'E176), `first_three_members_geometry` : FERMÉS sans
hypothèse. Expérience demandée (modifications temporaires de `DemonstrationChain.lean`, restaurées) : (B) fermeture arrêtée à
`∀ w, β_w = 1/2`, aucune occurrence de `RiemannHypothesis` ; (A) cible terminale = définition écrite par nous (bande ouverte).
Les deux : une seule erreur, `:272`, bloc d'erreur identique (empreinte 12a2a0d76c97), termes terminaux dépendant de
`sorryAx`. Le but ouvert ne contient pas RH ; `riemannHypothesis_iff_strip` (fermé) montre que la définition de Mathlib est la
définition classique : l'erreur n'est pas une erreur de définition, et redéfinir RH ne la supprime pas. Signature 12a2a0d76c97.

## §50. Retrait des trois contributions certifiées et estimation du retrait (auteur, 2026-10-11)

Directive : conserver la conclusion de transmission, retirer uniquement la recherche de séparation (le raccord « signal
contre retrait exact + marge » ne produit aucune contrainte nouvelle, `window_separation_not_exact`), retirer ensemble les trois
contributions certifiées, composer les cas fermés jusqu'à 28, construire une estimation arithmétique du retrait et démontrer son
incompatibilité avec la rupture, sans domination universelle ni séparation. Fait : `Terminal/CertifiedRemoval.lean` (9 théorèmes,
objets `certifiedPart`, `certifiedRemoved`, axiomes standard) ; dans `radial_conservation_anchored` : cas `T_l ≤ 28` fermés par
`first_three_zeros_control` (contrôles déplacés avant la transmission), troisième membre canonique dans l'historique
(`consecutive_no_height_between`), identités du retrait certifié en contexte, fermeture par `certified_estimate_incompatible`.
But restant (`DemonstrationChain.lean:382`) : l'estimation `∃ θ < 1 − β_l, C, ∀ fenêtre d'événements premiers,
‖Σλ_r (R − P_28)(x_r)‖ ≤ C·Σ|λ_r| x_r^θ`. Portée : elle contient les fenêtres à un point (`certified_estimate_pointwise`) ;
c'est une croissance du reste privé de la part certifiée sur tout `x > 1`, de même nature que la voie globale. Signature
a72cedc37aa2.

## §51. Comparaison de fenêtres de zéros (auteur, 2026-10-11 ; E197)

Étude : `experiments/e197_window_comparison.py` (12 s ; `experiments/e197_window_comparison/` : résumé, points, premiers,
membres, cinq figures, sortie) et recalcul indépendant `experiments/e197_independent_check.py` (mpmath, écrit séparément).
Liste unique de 5000 zéros d'Odlyzko (numériques ; membres 1–3 seuls certifiés dans Lean) ; positions début (1), suite du
préfixe certifié (4), milieu (2483), fin (4965) ; 12, 24, 36 membres. Fenêtre de premiers construite depuis les contacts (cellule
de la Tour du premier membre contenant son occurrence, cellule de la Tour du dernier contenant son premier partagé), 13 à 39
premiers. Canal lissé ; `H = R − P_hist = G + K`, `K = Σ_{au-dessus, ≤ 5000} + ε`. Observations : identités exactes à 1,6e−15 ;
cellules conformes 36/36 ; `|#AB − #BA| ≤ 1` ; déplacement entre Tours ≈ 3,0–3,4 cellules (hauteur et rang) ; enveloppe du groupe
3,5e−2 → 7,8e−6 → 2,4e−6 ; part du groupe 0,98–1,00 → 0,05–0,20 ; `max |R − P_28|/√x` 0,0101 / 0,0025 / 0,0050 ; à la fin, le
complément est entièrement dans le résidu de troncature ; la forme démontrée `budget·x` est lâche d'un facteur jusqu'à 2,5·10⁴
(valeur du budget estimée). Lean : `Terminal/WindowComparison.lean` (8 théorèmes, axiomes standard) ; transmission lue à
`H_w = max T_e 28` (`hHistOnW`, `hWindowShift`, `hWindowChain`, `hCertGroupOn`, `hArrivalChain`), fermeture par
`certified_estimate_of_history_estimate` puis `certified_estimate_incompatible`. But restant (`DemonstrationChain.lean:383`) :
`∃ θ < 1 − β_l, C, ∀ fenêtre, ‖Σλ_r (R − P_{H_w})(x_r)‖ ≤ C·Σ|λ_r| x_r^θ` (groupe d'arrivée + complément ; équivalent au précédent
sous l'historique ON ; contient les fenêtres à un point). Propriété candidate observée (`θ = 1/2`), non démontrée. Signature
e9ea6a0c98ac.

## §52. Trois cents premiers zéros : transmissions, fenêtres, familles (auteur, 2026-10-11 ; E198)

Étude : `experiments/e198_transmissions_300.py` (50 s ; `experiments/e198_transmissions_300/` : transmissions, fenêtres,
familles, familles × tiers, comparaison, fenêtres détaillées, six figures, sortie ; 11 contrôles PASS, 0 FAIL, haute précision
≤ 1,7e−12). Périmètre : 299 transmissions `n → n+1`, 831 fenêtres complètes de 12/24/36 membres ; zéros 301–5000 pour le seul
contrôle du complément (N = 300, 600, 1000, 2000, 5000). Canal lissé (Lean) et canal de comptage (li aux abscisses, π et J aux trois
conventions, `li(x^ρ) := Ei(ρ log x)` branche principale) séparés, aucun transport. Acquis vérifiés : identités à ≤ 8,3e−16 ;
signe du groupe en `M` = `cos(T_l log M + arg(−1/(ρ(ρ+1))))` (phase du LISSÉ ; phase brute : corrélation −0,03) ; contact brut
= `(β+1)/|ρ+1|` de l'enveloppe lissée. Observations : `|ΔP_e|/|ΔR|` médian 0,994, `|ΔG + ΔK|/|ΔR|` 0,054 ; `|K(M)|` ≈ 6–9 fois
l'enveloppe de `l` ; part du groupe 0,71 → 0,56 → 0,39 (24 membres) ; familles AA 55, AB 97, BA 96, BB 49, exceptionnelles 2
(2 → 3, 3 → 5), aucun signe de famille ; `Δli ≈ Δπ` à ±1 ; résidu `ε_N` décroissant en N (5,8e−5 → 1,7e−6), résidu par différence,
pas une borne. Lean : `Terminal/TransmissionIncrements.lean` (6 théorèmes, axiomes standard) composé (`hTransIncr`,
`hRemovalIncr`). Propriété à démontrer : `‖ΔQ_H‖ ≤ C(√a + √b)` (forme incrémentale du but à `θ = 1/2`) ; acquis `budget(H)(a + b)`.
But restant inchangé (`DemonstrationChain.lean:384`). Signature d8257b4accb9.

## §53. Exposant du retrait (auteur, 2026-10-11 : « démontre le retrait d'exposant »)

Lean : `Terminal/RemovalExponent.lean` (6 théorèmes, axiomes standard, aucune prémisse). Retrait de l'historique = queue
`Σλ_r Q_H(x_r)` sur toute fenêtre (`historyRemoved_eq_tail`) ; bande sans zéro au-dessus de `H` à l'exposant `θ` ⟹ estimation
du retrait d'exposant `θ`, constante `budget(H)` (`removal_estimate_of_zero_free_above`) ; réciproque par lecture du pôle
(`zero_free_above_of_removal_estimate`) ; caractérisation `removal_estimate_iff_zero_free_above` : l'exposant du retrait est
exactement la borne des parties réelles des zéros au-dessus de `H` ; `removal_estimate_reads_arrival` : `H < T_z` ⟹
`max(β_z, 1 − β_z) ≤ θ`. Composé (`hRemovalTail`, `hRemovalExpIff`, `hRemovalReadsArrival`) ; but réduit sans perte à
`∃ θ < 1 − β_l, ∀ σ, H_w < |Im σ| → Re σ ≤ θ` (`DemonstrationChain.lean:384`). Portée : la bande contient le miroir de l'arrivée,
le but est la contradiction elle-même écrite sur l'exposant ; aucun exposant `< 1` n'est démontré (seul `budget·x`) ; aucune
région sans zéro connue (hors Lean) ne donne de bande `θ < 1`. Signature 1f7117bb003d.

## §54. Cible de la transmission rétablie, correspondance par fenêtres, matrice des incréments, E199 (auteur, 2026-10-11)

Correction : le dernier bloc de `radial_conservation_anchored` (`suffices hEst` : estimation du retrait sur toute famille
d'abscisses, supports à un point compris, donc borne globale de croissance ; puis `suffices hStrip` : bande sans zéro au-dessus
de `H_w`) imposait une condition suffisante choisie comme dernier pas. Les deux sont retirées comme sous-buts et conservées en
contexte comme lemmes disponibles (`hEstCloses`, `hStripCloses`, preuves inchangées). Signature, conclusion, ancre, comptages à
15, 22, 28, cas `T_l ≤ 28` fermés : inchangés. But affiché : `⊢ False` sous `hBelow` (build : commit c9f68c23, signature
f685bc8baedf).

Lean, trois modules fermés (29 théorèmes, 3 objets, axiomes standard, aucune prémisse), composés dans la transmission :
`Terminal/WindowCorrespondence.lean` (portage de la correspondance à deux côtés de rhv4_lean, prouvée depuis rhv3_lean :
`M^Z = M = p_index` sur toute fenêtre canonique, succession, ordre, consécutivité, raccord disjoint de fenêtres adjacentes,
fibres contiguës / finies / complétées aux bords / stables par le miroir, groupe fini et complément signé ; `FiberedMZEqM` non
réintroduit) ; `Terminal/IncrementMatrix.lean` (matrice des incréments, deux télescopages, colonnes = incréments du reste,
indices de compensation, instance historique / groupe / complément) ; `Terminal/AmplitudePhase.lean` (forme polaire, incrément
général avec variation d'enveloppe, bornes, produit de sinus, spécialisation ON sous `β = 1/2` en hypothèse, correction de
normalisation, encadrement de `Δli` entre premiers).

Raccord tenté. Propriétés candidates examinées sur la fibre complète de l'arrivée (qui contient l'arrivée et son miroir,
`hArrivalFiber`) : (a) borne du signal du groupe fini à un exposant `< 1 − β_l` : fausse sous `hBelow` (le miroir n'est
compensé par aucun membre fini, `mirror_group_not_compensated`), donc non dérivable ; (b) borne du complément après la fibre
complète : sa composition avec le cas bas exige encore une lecture de `R` lui-même, car l'identité `R = historique + groupe +
complément` n'a que `R` comme lecture indépendante des zéros, et l'historique ON est borné (`precedingSum_le_budget_of_onLine`) ;
(c) inégalités de la matrice et relations amplitude–phase : vraies pour toute position radiale. Aucune n'a été posée comme
sous-but : aucune n'est à la fois justifiée par les fenêtres et fausse sous la première rupture.

E199 (`experiments/e199_increment_matrix_fibers.py`, 5 s, 19 PASS, 0 FAIL ; 7 figures, 8 CSV) : télescopages à 5e−16 (N =
300, 5000, complément exact) ; identités amplitude–phase à 1e−12 (β = 0,35 / 0,65 en tests algébriques) ; extrema du lissé
décalés de ≈ 0,5 cellule des contacts bruts ; `Δli` encadré sur 378 colonnes sans violation ; `χ_H` 0,10 (36 début) à 0,999
(12 fin), `η` médian 0,23–0,75, 47/378 colonnes `η < 0,1`, `η` croît avec la magnitude de l'écart (Spearman 0,22) ;
sensibilité N = 300 → 5000 : `χ_H` stable, `η` médian bouge ≤ 0,1. Observations, ON numérique, aucun intervalle certifié.

`lake build RHV6Fresh` : EXIT=1, une erreur, `DemonstrationChain.lean:387`, `⊢ False` sous `hBelow`. Signature 773304e5f236.



## §55. Compensation sur une fenêtre grammaticale authentique (auteur, 2026-10-11)

Tentative de l'auteur avec ses sept corrections (phases propres et non communes, fibre complète, somme signée filtrée,
retrait développé par les poids premiers, coefficients à dépendance explicite, identité d'abord, aucune clause
d'impossibilité générale). `Terminal/GrammarWindowSeparation.lean` FERMÉ (27 théorèmes, 7 objets, axiomes standard),
composé dans `radial_conservation_anchored`.

| Énoncé | Nature | Portée |
|---|---|---|
| `window_same_quantity`, `separation_contradiction` | identité | `L(Y − F) = L(Q)` ; vérification de composition, aucune estimation |
| `filtered_vonMangoldt`, `historyRemoved_filtered_primes` | identité | retrait = poids premiers filtrés − fond − historique, sans borne substituée |
| `groupSignal_eq_tsum_fiber`, `groupSignal_split`, `upper_term_eq`, `lower_term_eq` | identité | fibre complète, coefficients propres, moitiés supérieure / conjuguée |
| `hFibHeights` (chaîne) | démontré | passage consécutif : toute la fibre `]max(T_e,28), T_l]` à la hauteur `T_l` |
| `upper_weight_re_nonneg`, `upper_fiber_minoration` | estimation démontrée | moitié supérieure sans annulation, `≥ Re w_l Σ g_r p_r^{β_l}` |
| `matched_window_closes` | composition | `‖L(Y)‖ + marge + ‖conjuguée‖ < minoration ⟹ False` |
| `matched_separation_requires` | condition nécessaire | marge triangulaire ⟹ exige `budget(T_l) < ‖w_l‖` |

Obligation ouverte, précise : (i) majoration de `Σ_r λ_r Q_{T_l}(p_r)` meilleure que `budget(T_l)Σ g_r p_r` (contrôle
de la somme oscillante complète du complément) ; (ii) majoration de la moitié conjuguée
`Σ_σ w_σ Σ_r g_r p_r^{β_σ} p_r^{−2iT_l}` et de `L(Y)` (poids premiers filtrés) sous la minoration supérieure. La
composition est fermée. L'échec de la marge triangulaire ne démontre pas qu'aucune minoration exploitable n'existe.

`lake build RHV6Fresh` : EXIT=1, une erreur, `DemonstrationChain.lean:388`, `⊢ False` sous `hBelow`. Signature 7777c0686b34.

## §56. Fenêtre grammaticale : ordre correctif en dix points (auteur, 2026-10-11)

La séparation de §55 est une condition SUFFISANTE NON DÉMONTRÉE, pas une solution acquise (commentaires et maîtres
corrigés). `Terminal/GrammarWindowEstimate.lean` FERMÉ (36 théorèmes, 2 objets, axiomes standard), composé et APPLIQUÉ
dans `radial_conservation_anchored`.

| Énoncé | Nature | Portée |
|---|---|---|
| `window_closes_of_bounds`, `window_closes_triangular` | composition | majoration explicite `B_Q` du complément ; triangulaire = cas particulier, non imposé |
| `group_re_ge`, `removal_sub_group_le` | trois objets | partie réelle supérieure ≠ groupe complet (`≥ U − B_L`) ≠ retrait − groupe (`= L(Q) ≤ B_Q`) |
| `arrival_mirror_fiber` | démontré | miroir dans la fibre : distinct, `1 − ρ̄_l`, hauteur `T_l`, `Re = 1 − β_l`, multiplicité, coefficient |
| `upper_fiber_finset_minoration`, `arrival_mirror_minoration` | estimation démontrée | partie réelle supérieure `≥` paire arrivée + miroir ; autres membres `≥ 0` dans la série |
| `hSharedPrime`, `hRankL`, `hP3` (chaîne) | démontré | fenêtre au premier partagé `p_{n₀} = p_min(e) = Occ(l)`, `n₀ ≥ 3`, `p_{n₀} > 3` |
| `gapWeights_magnitude_class`, `gapWeights_ge_classFloor`, `passage_window_alternation`, `gapWeights_sum`, `gapWeights_sum_ge_three_mul`, `weighted_window_floor`, `passage_pair_minoration_floor` | composé | écarts, classes, planchers, alternance, télescopage, `≥ 3m`, composés avec la minoration de la paire |
| `filtered_series_norm_le`, `complement_filtered_le(_margin)`, `history_filtered_le`, `lower_half_le`, `lower_half_term_norm` | estimation démontrée | bornes filtrées, oscillation gardée sur la fenêtre ; `B_Q ≤` marge |
| `complement_phase_development`, `complement_window_residual_split`, `historyRemoved_le_primeSide` | identité / borne | phases propres du complément, résidu conservé ; retrait = part première exacte − historique |
| `passage_window_reduction` | réduction démontrée | appliquée dans la preuve terminale ; antécédent = but résiduel |

But résiduel (non démontré, aucune hypothèse ajoutée) : `∃ m, ‖Σ_{n<p_{n₀+m}} Λ(n)Φ_λ(n) − L(fond)‖ + B_P + B_Q + B_L <
Re w_l Σ_r g_r p_r^{β_l} + Re w_{l*} Σ_r g_r p_r^{1−β_l}`. Échec de CETTE tentative ; il n'établit ni la vérité de
l'inégalité, ni que les acquis suffisent, ni l'impossibilité d'une autre composition.

`lake build RHV6Fresh` : EXIT=1, une erreur, `DemonstrationChain.lean:389`. Signature fc4edfc9b559.

## §57. Comparaison signée sur la fenêtre du passage (auteur, 2026-10-11)

La réduction de §56 prenait la norme de la part première, de l'historique filtré et de la moitié conjuguée : ces trois
opérations perdent les compensations exactes. `Terminal/SignedWindowComparison.lean` FERMÉ (11 théorèmes, axiomes
standard), composé et APPLIQUÉ dans `radial_conservation_anchored` ; `passage_window_reduction` conservée en contexte
(`hNormReduction`).

| Énoncé | Nature | Portée |
|---|---|---|
| `removal_re_eq` | identité | `Re L(Y) = Σ_{n<N} Λ(n)·Re Φ_λ(n) − Re L(fond) − Re L(P_H)`, poids premiers exacts, tout signé |
| `cpow_neg_I_re`, `primeFilter_re_phaseMatched` | identité | filtre accordé : `Re Φ_λ(n) = Σ_{r : n < p_r} g_r cos(T_l log p_r)(1 − n/p_r)` |
| `history_filtered_series` | identité | historique filtré signé, coefficients propres `w_σ^H` |
| `lower_re_tsum`, `lower_re_term` | identité | moitié conjuguée, partie réelle terme à terme, coefficient propre, fréquence `2T_l` |
| `window_closes_signed` | composition | `Re L(Y) − Re(conjuguée) + B_Q < U ≤ Re(supérieure)` ⟹ `False` |
| `signed_of_norm_separation` | comparaison | la séparation en normes implique la comparaison signée (au plus aussi exigeante) |
| `passage_window_reduction_signed` | réduction démontrée | appliquée ; antécédent = but résiduel |
| `signed_comparison_lhs_ge`, `passage_signed_comparison_reversed` | portée démontrée | pour TOUTE fenêtre, membre de gauche `= Re(supérieure) + Re L(Q) + B_Q ≥ U` : le but équivaut à `False` dans le contexte |

But résiduel (non démontré, aucune hypothèse ajoutée) : `∃ m, Σ_{n<p_{n₀+m}} Λ(n)·Re Φ_λ(n) − Re L(fond) − Re L(P_H) −
Re(conjuguée) + B_Q < Re w_l Σ_r g_r p_r^{β_l} + Re w_{l*} Σ_r g_r p_r^{1−β_l}`. Étape 7 : poids premiers, cosinus, écarts,
classes, alternance, planchers et `3m` en contexte ; aucun ne majore la somme signée de von Mangoldt filtrée ; aucune
valeur expérimentale utilisée. Résultat démontré : la comparaison est renversée pour toute fenêtre (`hComparisonReversed`) ;
elle équivaut à `False`, comme la séparation en normes de §56 qui l'implique. Une composition par fenêtre seule ne peut pas
fermer ; il faut un fait démontré incompatible avec `hBelow`. Échec de CETTE tentative.

`lake build RHV6Fresh` : EXIT=1, une erreur, `DemonstrationChain.lean:390`. Signature 34f88125eea4.

## §58. Réalignement : conservation du régime engagé, contradiction directe (auteur, 2026-10-12)

La piste de compensation imposée est retirée comme dernier pas de la transmission : `passage_window_reduction_signed` n'est
plus appliquée en fin de `radial_conservation_anchored` ; aucune séparation en normes, comparaison signée ni estimation
globale n'est un sous-but. Leurs lemmes restent fermés et disponibles en contexte (`hNormReduction`, `hSignedCloses`,
`hComparisonReversed`, `hEstCloses`, `hStripCloses`) ; leur échec comme réduction terminale ne réfute pas leurs énoncés.

Contradiction directe rétablie sous la première rupture supposée (historique ON, départ ON, passage consécutif qui monte,
`hBelow`). Réunis en contexte, sans théorème nouveau :

| Bloc | Contenu | Portée |
|---|---|---|
| `hRuptureConsequences` | miroir qui suit, distinct, même hauteur, partie réelle `1 − β_l`, même multiplicité, dans la fibre ; `λ > 1` ; rayon normalisé décroissant entre contacts du départ, facteur de pas `≠ 1` ; `q : l → s` de même hauteur, contacts translatés en deçà ; `s` au plus en ligne ou miroir exact | conséquences de `hBelow` ; consécutivité immédiate du miroir NON supposée |
| `hPassageObligations` | anneau ON intérieur vide ; rang + 1, premier partagé, pas contracté, fenêtre de phase, `1 ≤ λ < e^{1/(2T_l²)}`, contacts = ligne × λ ; cinématique de l'étage ; `p_{n₀} = Occ(l)` ; alternance ; télescopage des écarts ; fibre `]max(T_e,28), T_l]` à hauteur `T_l` | toutes valables pour toute arrivée `β_l ≤ 1/2` ; reconstruction exacte (`hRec`, `hArith`, identités de fenêtre) vraie pour toute position radiale |

Confrontations tentées : aucune obligation, dans sa portée, ne contredit une conséquence de la rupture (consécutivité
contre fibre à deux points à la hauteur `T_l` ; rang + 1 et premier partagé vrais sur le passage de même hauteur ; fenêtre de
`λ` sans `λ = 1` ; cinématique d'étage toute position radiale ; grammaire fonction du rang ; lecture du pôle sous borne non
dérivée). Verrou : « Depuis un historique sur la ligne critique, établir que les obligations du prochain passage maintiennent
l'annulation du miroir, de sorte que la progression se poursuive uniquement par la hauteur. »

`lake build RHV6Fresh` : EXIT=1, une erreur, `DemonstrationChain.lean:390`, `⊢ False`. Signature 6273523f4654.

## §59. Contrôle TDD : `λ_l = 1` suffit (auteur, 2026-10-12)

Hypothèse de test temporaire `∀ hL', radialFactor ⟨p.zLaterMember, hL'⟩ = 1` ajoutée à `radial_conservation_anchored`,
composée avec `hLambda : 1 < λ_l` par `linarith` : l'erreur `:390` disparaît ; seule erreur restante, l'appelant
`conservation_law` (il ne peut pas fournir l'hypothèse). Fermeture conditionnelle de contrôle, non une preuve de RH.
Hypothèse retirée ; le corps se termine par `refine absurd ?_ (ne_of_gt hLambda)`. Obligation exacte :
`⊢ radialFactor ⟨p.zLaterMember, hL⟩ = 1` depuis `h₁`, `hE`, `hV`, `hOn`, `hHist`. Acquis : `1 ≤ λ_l < e^{1/(2T_l²)}`
(`engaged_event_restriction`) ; `λ = 1 ⟺ β = 1/2` (caractérisation). `lake build RHV6Fresh` : EXIT=1, une erreur `:390`,
signature ccb0025b531c.

## §60. Composition de comptage, pas réduit à la fibre (auteur, 2026-10-12)

Dans `radial_conservation_anchored` : `hLambdaOfCount` (fermé) compose `hWe : W(T_e) = 0` (historique ON),
`lowCount_eq_zero_of_count_step`, `all_onLine_of_lowCount_zero` (réflexion) et `radialFactor_eq_one_iff` : le pas
`N(T_l) < N(T_e) + 2` donne `λ_l = 1`, contre `hLambda`. Sous-but exact : `⊢ N(T_l) < N(T_e) + 2`, non supposé. Attaque
(fermée, axiomes standard) : `fiberCountWithMultiplicity`, `passage_count_step_eq_fiber` (`N(T_l) = N(T_e) + fibre(T_l)`, la
consécutivité excluant les hauteurs strictement entre), `passage_count_step_lt_two_iff` (pas sous deux ⟺ fibre = un point
simple), `two_le_fiberCount_of_low` (membre bas + miroir : fibre ≥ 2). Portée : la consécutivité ne borne ni les autres points
ni les multiplicités de la fibre ; sous la rupture le sous-but est la négation de `hRuptureCost`. Certifications 15/22/28
conservées (cas `T_l ≤ 28` fermé). `lake build RHV6Fresh` : EXIT=1, une erreur `:452`, signature cccc2682edec.

## §61. Trois hypothèses de travail sur la fibre d'arrivée : portée compilée, E200 (auteur, 2026-10-12)

`Terminal/ArrivalFiberHypotheses.lean` (15 théorèmes, objets `paramFactor`, `fiberPoints` ; `fiberCountWithMultiplicity`,
`passage_count_step_eq_fiber`, `passage_count_step_lt_two_iff`, `two_le_fiberCount_of_low` déplacés depuis la chaîne, inchangés),
composé en contexte de `radial_conservation_anchored`. H1 (unicité de la grille par les contacts) : `λ = e^{(arctan(T/β) − arctan 2T)/T}`
(`radialFactor_eq_arctan`) ; toute `β ∈ ]0,1/2]` satisfait fenêtre de phase, `1 ≤ λ < e^{1/(2T²)}`, contacts = ligne × λ
(`parameter_grid_admissible`) ; deux grilles décalées de même hauteur : même pas, translation rigide, chacune admissible, coïncidence ⟺
même `β` (`shifted_grids_same_obligations`) ; grille de ligne ⟺ `β_l = 1/2` (`arrival_grid_unique_iff_onLine`) ; inversion
`β = T cot(arctan 2T + kπ + T log λ)` (`inversion_restores_shift`). Verdict : H1 ⟺ but ; les obligations calculent la translation sans
l'interdire. H2 (transport du comptage premier) : `rank_step_counts_members_not_heights` (passage de même hauteur parti d'un membre bas,
rang + 1, premier partagé, horizontal) ; `fiber_card_ge_two_of_low` ; `count_step_eq_fiber_card_of_simple`. Verdict : une unité
d'événement premier = un membre, aveugle à la hauteur. H3 (multiplicité) : `fiberCount_lt_two_iff` ; `onLine_double_breaks_count_step`
(double ON : `λ = 1`, pas ≥ 2) ; `count_step_iff_on_unique_simple` (sous `W(T_e) = 0`, pas < 2 ⟺ ON ∧ unique à sa hauteur ∧ simple).
Verdict : le sous-but de comptage est strictement plus fort que `λ = 1` ; simplicité non nécessaire à RH. E200
(`experiments/e200_arrival_fiber_hypotheses.py`, 3 s, 48 PASS, 4 figures, 5 CSV) : 300 × 7 grilles, 0 violation, même seuil
d'emboîtement, inversion 1e−12, translation ≤ 0,0074 cellule, `π/2 − arctan 2T < 1/(2T)` (T₁ : 0,035359 < 0,035374), `β = 0,4` = 0,20 de
la largeur de fenêtre ; 5000 passages : emboîtement `k ≥ 1` violé 5/35000 (β ≤ 0,2, `dT < 0,1`) ; `ΔN = 1` et rang + 1 sur 4999/4999,
écart de hauteur min 0,0433 ; paire insérée : + 2 / + 2, grammaire identique après réindexation ; témoin `W_0,25` : obligations 299/299,
+ 2 par hauteur ; quatre cas (simple ON, double ON, paire, bas seul impossible) ; double ON contre paire `d = 0,1` : même comptage 2,
rapport `cosh(d log x)` (1,10 dès `x ≈ 85` à T₁). `lake build RHV6Fresh` : EXIT=1, une erreur `:391`, but inchangé
`⊢ N(T_l) < N(T_e) + 2`, signature 193bbe414e9e.

## §62. Comparaison directe de l'arrivée au premier zéro par les contacts : identité, déplacement radial, E201 (auteur, 2026-10-12)

Directive : « travaille sur cette hypothèse ; fais les expériences nécessaires ; enlève toute notion de marge disponible, il n'y en a pas ;
on parle du déplacement radial ». Identité de l'auteur : `log(C_{l,k}/C_{1,k}) = log λ_l + (arctan(2T_l) + kπ)/T_l − (arctan(2T₁) + kπ)/T₁`.
`Terminal/FirstZeroContactComparison.lean` (28 théorèmes, objet `lineHeightShift`, axiomes standard), composé en contexte de
`radial_conservation_anchored` (`hT₁le`, `hT₁lt`, `hFirstComparison`, `hUpperOneOnly`, `hUpperOneOnlyEngaged`, `hFactorLeOfContact`).
Identité : `contact_log_ratio` (forme générale `log λ_z − log λ_w + heightShift`), `contact_log_ratio_onLine` (vers un membre en ligne) ;
`log λ ≥ 0` pour `β ≤ 1/2` (`log_radialFactor_nonneg`). Terme de hauteur : `lineHeightShift_split` (part d'indice `kπ(1/T − 1/T₁)` + part
de phase), `lineHeightShift_strictAnti_index`, `lineHeightShift_neg` (sous `1/2 ≤ arctan(2T₁) + kπ`), `_of_one_le`, `_of_nonneg`.
Signe : `contact_lt_iff_factor`, `contact_le_iff_factor`. Borne supérieure : `factor_le_one_of_contact_le` (comparaison ⟹ `λ ≤ 1` seulement
si `heightShift ≥ 0`), `onLine_of_contact_le` (avec la borne inférieure acquise : `λ = 1`), `onLine_fails_strict_comparison` (l'arrivée en
ligne viole la comparaison stricte à ces indices), `index_neg_of_heightShift_nonneg`, `contact_lt_one_of_neg`, composés
`upper_bound_one_only_below_one` (`T₁ ≥ 1/2` : `k < 0`, contact `< 1`), `upper_bound_one_only_nonpos_index` (`k ≤ 0`). Ordre acquis sans
contrainte : `param_grid_lt_line_iff`, `contact_order_of_window` (la fenêtre seule entraîne l'ordre dès `1/(2T²) ≤ −heightShift`),
`exists_shifted_grid_of_gap` (construction `β = T cot(arctan 2T + η)`, `η = min(T·gap, π/2 − arctan 2T)/2`),
`exists_shifted_grid_nested_in_first` (tout `k ≥ 0`), `exists_shifted_grid_windingNested` (tout `k ≥ 1`),
`windingNested_realized_by_shifted_grid`, `passage_first_zero_comparison`. Verdict compilé : la comparaison directe calcule le déplacement
radial et le borne par `−heightShift > 0` à tout indice `k ≥ 1` ; la borne supérieure un ne se lit qu'aux indices `≤ 0` (contacts sous `1`),
où le régime conservé lui-même ne satisfait pas la comparaison : aucune borne supérieure égale à un ne vient des contacts.
E201 (`experiments/e201_first_zero_contact_comparison.py`, 2 s, 19 PASS, 2 figures, 4 CSV) : identité à 7e−15 (300 passages × 7 grilles ×
261 indices, vers `z₁` et vers `e`) ; `heightShift` décroissant, max sur `k ≥ 0` −3,5e−2 ; racine `k_c ∈ [−0,489, −0,481]` (vers `z₁`) et
`[−0,500, −0,481]` (vers `e`) sur 4999 ; aux indices `k ≤ k_c` : contacts `< 1`, arrivée ON avec `C_l ≥ C_1` ; borne composée de `log λ_l`
(fenêtre, ordre vers `z₁` à `k ≥ 0` et `k ≥ 1`, ordre vers `e` à `k ≥ 0` et `k ≥ 1`) : min 2,48e−9 (n = 4766), médiane 5,4e−8, liante =
fenêtre 4914/4999, ordre vers `e` à `k = 0` 85/4999 (`dT < 0,318`) ; `g₀(z₁)/fenêtre ≥ 31` ; borne composée ≥ plus grand déplacement
réalisable sur 4914/4999 (toute `β ∈ ]0,1/2]` admise), `β_min` max 0,432 ; 7 grilles emboîtées dans `z₁` à tout `k ≥ 0` sur 4999/4999 ;
grille du théorème (`β ≈ 1/4`) emboîtée ; violations vers `e` à `k ≥ 1` : 5 (β ≤ 0,2), lecture du signe exacte sur chacune ; témoin
`W_δ` (`δ = 0,05/0,1/0,25`) : bas et haut emboîtés dans `z₁` à tout `k ≥ 0` ; déplacement radial / écart vers `z₁` ≤ 4,9e−7 (médianes).
`lake build RHV6Fresh` : EXIT=1, une erreur `:392` (ligne décalée par l'import), but inchangé `⊢ N(T_l) < N(T_e) + 2`, signature d51da38127e7.

## §63. Restitution arithmétique des cellules et des passages, campagne E202 (auteur, 2026-10-12)

Ordre : capitaliser sur E190, E198, E199, E200, E201 ; chercher une obligation acquise que toute première rupture violerait, sans la
supposer ; retirer le comptage sous deux comme dernier sous-but imposé (il exige la simplicité), le conserver comme outil.

Lean. Dernier sous-but remplacé par la cible : `⊢ radialFactor ⟨p.zLaterMember, hL⟩ = 1` (`refine absurd ?_ (ne_of_gt hLambda)`) ;
`hLambdaOfCount`, `hStepFiber`, `hStepIff`, `hCountIff`, `hDoubleOn` restent en contexte. `Terminal/CellRestitution.lean` FERMÉ
(20 théorèmes, `cellIndexAt`, `cellCharge`, axiomes standard). Identités démontrées : `cellCharge_add`, `cellCharge_translate`,
`mirrorPairTerm_zero`. Contraintes démontrées : `arrival_cell_shift` (indice de ligne ou moins un pour `β ≤ 1/2`),
`arrival_cell_unchanged_iff` (seuil exact `−D/π`), `small_translation_cells_blind` (détecteur à seuil), `pair_tendsto_double`,
`pair_sub_simple_tendsto`, `onTerm_ne_zero` (saut d'ordre zéro depuis un point simple, déformation continue depuis un double).
Composé en contexte (`hCellRestitution`, `passage_restitution_scope`). Premier sous-but non fermé : `radialFactor l = 1` ; dépendance
manquante : un énoncé démontré, indépendant de la restitution, faux sur une arrivée translatée.

E202 (21 PASS, 93 s ; statuts certifié Lean / numérique ON / synthétique séparés ; canaux pondéré, lissé, comptage séparés) :
T1 charges = incréments du côté premier (lissé 4,7e−10) ; résidu relatif médian lissé 1,0e−3, pondéré et comptage 7,1e−2 (aucune
borne de queue dans ces deux canaux) ; vérification INDÉPENDANTE dans le lissé : `|ε_5000| ≤ TB(5000)·x`, TB par Rosser (1941) et
liste complète, rapport ≤ 7,9e−3 ; télescopage exact sur 897 fenêtres d'événements 12/24/36 (7–35 cellules). T2 décalage d'au plus
un rang vers le bas (2093 cas) ; variation de charge = charge des bords ; 9/11063 événements susceptibles de changer de cellule pour
une `β ∈ ]0,1/2]`, `M` jamais ; le défaut d'un profil déplacé contre les vrais premiers est le défaut d'insertion compilé. T3 AA 3939,
BB 3603, alternance AB/BA stricte ; charges, magnitudes, avances : premiers et `T_l` seuls ; lecture accordée β = 1/2 contre 0,4 :
variation 2,1e−4 (lecture, pas obligation). T4 raccord exact 299/299, sans omission ni double comptage. T5 fenêtres consécutives
recouvertes exactement sur la cellule de `M` dans la Tour intermédiaire ; composition jusqu'à 20 passages : aucune contrainte
cumulative sur `λ`. T6 pentes `log λ` 1, membre 1, paire − double 2, paire − simple 0 ; aucun indice de la fenêtre test ne change
pour aucune `β` (position minimale 2,4e−2 > décalage maximal 5,0e−4). T7 portées : membre / fibre / somme des suivants. T8 inversion
exacte (6,4e−7), branche `]0, π/2[`, `|dβ/d log C| ≈ T²`. T9 retrait signé des trois membres certifiés : enveloppe 297/297, ordre
`k = 1` 297/297, contributions signées de signe variable, gain `≤` gain du premier 258/297 ; aucune ne lit `λ_l`. T10 signal d'un
membre au-dessus de la borne démontrée du complément : 1/43 à toute coupure. T11 Hardy `Z` : aucun changement de signe intérieur,
un extremum intérieur 299/299, `N(T_300) = 300`.
Verdict : aucune obligation acquise, indépendante de la restitution, n'est violée par une première rupture ; seul le pas de comptage
(saut paire contre simple) sépare, et il exige la simplicité. `lake build RHV6Fresh` : EXIT=1, une erreur `:393`,
`⊢ radialFactor ⟨p.zLaterMember, hL⟩ = 1`, signature 133488d40d2c.

## §64. Défaut de comptage sur la ligne, étude directe de zêta (auteur, 2026-10-12)

Relecture des rectangles 15/22/28 : `box_order_sum` (principe de l'argument sur `ξ₁`) donne la somme des ordres dans
`B₁ = [σ₀, 2] × [−t₁, T]` ; `B₂ = [1 − σ₀, 2] × [−t₁, T]` d'intégrale nulle exclut `Re ≥ 1 − σ₀` (`box_strip_mem`) ; le miroir range
tout zéro de la bande dans `B₁` ; la ligne n'est confrontée au comptage que par `N = N₀ + 2W` (parité). Lemmes analytiques
réutilisables : `argument_principle_rect`, `box_order_sum`, `box_strip_mem`, `box_no_lower_zero`, `upperWindowOpen_count_of_boxes_K`,
`no_zero_at_height_of_top`, `upperCount_of_zeta_boxes`, `rectBoundaryIntegral_completedEntire_eq_zetaFactor` ; évaluations numériques :
`ZetaBox/*`, `ZetaBox22/*`, `ZetaBox28/*` (interpolation certifiée d'Euler–Maclaurin, raccords d'un quart de tour).
`Terminal/LineCountingDefect.lean` (25 théorèmes, axiomes standard) : `δ = ΔN − ΔN₀ = 2ΔW` ; pair, `≥ 0` ; `≥ 2` sous la rupture ;
`δ = 0 ⟹ λ_l = 1` (conditionnel, composé) ; `ΔN < 2 ⟹ δ = 0` ; rectangle d'enroulement nul vide ; rectangles de droite `σ' → 1/2⁺` ⟹
`δ = 0` ; `ΔN₀ ≥` nombre de changements de signe ; Turing local ; aucun changement de signe dans `[T_e, T_l]` ; forme fibre. Premier
raccord analytique ouvert : `fibre(T_l) = m_ζ(1/2 + iT_l)·[Λ(1/2 + iT_l) = 0]`, soit `δ(T_e, T_l) = 0` (équivalent sous l'historique
ON à l'arrivée ON : la composition n'est pas une démonstration).

## §65. Rigidité des transitions au raccord entre Tours, E203 (auteur, 2026-10-12)

`Terminal/TransitionRigidity.lean` (19 théorèmes, 11 objets, axiomes standard ; réutilise `Mod6Rigidity`, `eventClass`,
`primeGap_eq_magnitude_class`, `expectedMinimumPrime_eq_laterOccurrence`, `eventIndex_succ_of_passage`, `arrival_cell_shift`) : raccord
exact, classification, alternance, magnitude libre, raccord des événements et du passage (index vérifié : `Occ(z) = p_n`,
`p_min(z) = p_{n+1}`, `n = nZeroSourceIndex z`), lecture de cellule décalée d'au plus un. Liaison TDD « une première rupture radiale
force une violation de la rigidité dans la lecture authentique » : réfutée dans cette lecture (`rupture_keeps_transition_rigidity`) ;
son sous-but serait `¬ AllowedNext (eventTransition n) (eventTransition (n+1))`, contredit par `event_raccord`. E203 (15 PASS) : mot
grammatical complet (extrémités, transitions, magnitudes, premiers partagés) ; raccord 299/299 et 4999/4999 ; alternance dans les
groupes de 2, 3, 4, 10, 12 membres et les 897 fenêtres 12/24/36 ; L1 (indices ON conservés) et L2 (indices recalculés) séparées ; profils
synthétiques bas et miroirs, 7 + 7 valeurs : déplacements 4186/4186, changements de cellule L2 4/4186, extrémité hors cellule ON (L1)
4/4186, violation d'obligation 0 ; `M` ne change de cellule pour aucune `β ∈ ]0, 1/2]` (dps 50, marge minimale 2,1e−3) ; charges
pondérées indépendantes de `β`, reste lissé, contributions signées et complément par différence (t5). Obligations testées : extrémité
commune, composabilité, pas d'index un, écart d'indices à un près, décalage de cellule d'au plus un. Aucune violation : aucun
théorème acquis contredit. `lake build RHV6Fresh` : EXIT=1, une erreur `:395`, `⊢ radialFactor ⟨p.zLaterMember, hL⟩ = 1`, signature
3c5716aeccc6.

## §66. Les trois premières Tours dans le champ de comptage autour de li, E204 (auteur, 2026-10-12)

Correction de représentation : les cercles centrés en zéro (E163b, E088c/d, E180 2b) représentent le terme complexe isolé `x^ρ/ρ`
normalisé ; exacts pour cet objet, ils ne montrent ni le fond ni la reconstruction collective. E204
(`experiments/e204_three_towers_li_field.py`, 158 s, 5000 zéros d'Odlyzko, zéros 1–3 ON démontrés dans Lean) trace le champ du canal de
comptage : fond `F = li − log 2 + ∫_x^∞`, `F + b_1`, `F + b_1 + b_2`, `F + b_1 + b_2 + b_3` (`b_n = −2 Re Ei(ρ_n log x)`), `J₀` exact,
`π` seul, complément `R_J − S_3` (RMS 1,56) et troncature `R_J − S_5000` (RMS 0,20) sur `[2, 10⁵]`. Contacts de chaque zéro (table
`e204_contacts.csv`) : `C_k` (Tour), `D_k` (extremum, aveugle à `β`), `X_k` (racine de `b_n`, contact avec l'axe `li`), étage `k`, `li(D_k)`,
`b_n(D_k)`, enveloppe, `L_k`, `Δb_k` ; 48 / 71 / 85 étages ; `X_k ∈ ]D_{k−1}, D_k[` ; identités de restitution (`T` par deux extrema,
`β` par l'inversion au contact, `β = 1/2` racine unique au contact `X_k`) à 8e−13 près ; bornes Lean `C_k < D_k < C_{k+1}` et
`|Δb_k| ≤ 2C_k^{β−1}L_k` vérifiées 204/204. Domination : enveloppes `2√x/(|ρ_n| log x)` ordonnées, `b_2`, `b_3` sous l'enveloppe du
premier en tout point de la grille, énergies 0,897 / 0,393 / 0,284. Restes propagés (`r_{n−1} = R_J − S_{n−1}`, premiers + zéros
précédents seulement) aux extrema du zéro `n` : signe commun 38/48, 48/71, 63/85 (escalier exact), corrélations 0,63 / 0,48 / 0,23, part
médiane de la contribution propre 0,55 / 0,46 / 0,42 : le reste propagé porte la contribution du zéro suivant en majorité, avec un
complément du même ordre ; ajustement `(β, T)` sur `r_{n−1}` : `T` = 14,136 / 21,024 / 25,010, `β` = 0,50 (grille 0,01), part expliquée
0,23 / 0,13 / 0,11 (observations). `Terminal/CountingFieldContacts.lean` (8 théorèmes, `lineExtremumOffset`, axiomes standard) :
pas des extrema `π/T`, `T` restitué, extrema aveugles à `β`, `β = T tan(Tδ)`, `log λ = δ_ligne − δ`, `λ = 1 ⟺ δ = δ_ligne`, `β < 1/2 ⟹
δ < δ_ligne` ; composé (`hCountingField`, `hCountingOffset`). Inventaire des relations compilées contacts ↔ fond `li` ↔ grammaire et des
manques : `e204_output.md`. `lake build RHV6Fresh` : EXIT=1, une erreur `:396`, `⊢ radialFactor ⟨p.zLaterMember, hL⟩ = 1`, signature
1431084db57f.

## §67. Registre d'un écart de premiers : enveloppe de chaque contribution, contacts sur li, partage du reste, E206 (auteur, 2026-10-12)

Questions de l'auteur : relier les contacts sur `li` à leur contribution à l'enveloppe des écarts ; relier le reste d'un écart laissé au
zéro suivant au reste déjà comblé par les zéros précédents et par ceux qui le suivent. `Terminal/PrimeGapLedger.lean` (13 théorèmes,
objet `gapCountingEnvelope`, axiomes standard) : `|Δb_ρ| ≤ 2p_n^{β−1}Δli_n ≤ 2p_n^{β−1}g_n/log p_n` sur tout écart, enveloppe lue par
magnitude et classe (`gapCountingEnvelope_grammar`), plancher de classe, sous la ligne au plus l'enveloppe de ligne
(`gap_envelope_le_onLine_of_low`) ; registre de l'écart dans le canal `ψ` lissé (`prime_gap_ledger` : déjà comblé + fibre suivante +
au-dessus, attendu de la fibre = reste − passé − futur), bornes d'exposant 1 seulement (`prime_gap_ledger_bounds`), télescopage
(`prime_gap_ledger_window`), déficit `π − li₂` encadré (`countingDeficit_gap_bounds`) ; composé dans la transmission (`hGapLedger`,
`hGapEnvelopeLow`). E206 (`experiments/e206_prime_gap_ledger.py`, 116 s, 41 PASS, 0 FAIL ; README avec figures) : enveloppe vérifiée sur
9591 écarts × 5000 zéros (rapport max 1,0000) ; `|Δb_n|/env ≈ |cos(T_n log p_n)|` (corrélation 0,99) : 0,99 sur les écarts qui contiennent
un contact `X_k` avec l'axe `li`, 0,02 sur ceux qui contiennent un extremum `D_k` ; le reste non comblé par le passé est dominé par
`1 − g/log p` (saut du comptage moins le fond), porté par les zéros au-dessus ; à l'intérieur de l'écart `|ΔQ|/|Δb_n| ≈ 0,71√p_n` ; signes
communs reste non comblé / zéro suivant 0,48–0,51 par écart, 0,50–0,58 par fenêtre de 36 ; paire hypothétique `1/2 ± d` (jamais un vrai
zéro) : défaut au-dessus de `|ΔQ|` sur 1 % (`d = 0,1`) et 9 % (`d = 0,25`) des écarts, le membre haut sort de l'enveloppe de ligne. Portée :
la part du zéro suivant sur un écart est noyée sous celle des zéros au-dessus ; seule une borne du complément la ferait lire, acquise à
l'exposant 1 seulement. `lake build RHV6Fresh` : EXIT=1, une erreur `:397`, `⊢ radialFactor ⟨p.zLaterMember, hL⟩ = 1`, signature f55031efd778.

## §68. Géométrie des contacts dans le champ collectif, sensibilité radiale, identifiabilité, E207 (2026-10-13)

Mission : produire E207, identifier la première obligation réellement manquante, construire le Lean démontrable.
`Terminal/ContactSensitivity.lean` (17 théorèmes, objets `contactOffset`, `ReducedContactSystem`, axiomes standard) : accroissements
de `arctan` (`arctan_sub_bounds`) ; sensibilité du décalage `(β' − β)/(T² + B²) ≤ δ(β') − δ(β) ≤ (β' − β)/T²`, identifiabilité exacte à
`T` donné (`contactOffset_injOn`) ; taille du facteur radial `(1/2 − β)/(T² + 1/4) ≤ log λ ≤ (1/2 − β)/T²` sous la ligne,
`|log λ| ≤ |β − 1/2|/T²` ; lecture à `ε` près séparante si `2ε < (1/2 − β)/(T² + 1/4)` (`offset_reading_separates`), aveugle si
`(1/2 − β)/T² ≤ 2ε` (`offset_reading_blind`) ; contre-modèle : le système réduit des obligations de contact est satisfait par toute
`β ∈ ]0, 1/2]` (`reducedContactSystem_not_identifying`) ; composé (`hContactGeometry`). Les neuf théorèmes demandés existent et sont
réutilisés, non recréés. E207 (`experiments/e207_collective_contact_geometry/`, 6 min, 33 PASS, 0 FAIL ; README avec six figures PNG et
SVG, rapport mathématique, journal) : canaux `J` et `π` séparés, Möbius exact ; `X_k ≠ C_k` ; contact individuel retrouvé dans le reste
propagé exact 40/49, 50/72, 66/86 contre témoin 29/49, 44/72, 56/86 ; restitution aveugle des trois premières hauteurs à ≤ 3,6e−3 ;
région compatible `β ∈ [0,45 ; 0,53]` pour un complément 1 % au-dessus de l'observé (aucune borne démontrée dans le canal `J`) ;
paire `1/2 ± d` substituée à `ρ₁` reproduit `J₀` à `10⁻¹²` avec complément redéfini. Première implication non prouvée : historique ON
∧ passage qui monte ⟹ `λ_l = 1` ; quantité qui la fermerait : lecture du décalage de l'arrivée dans le champ collectif à précision
`< (1/2 − β_l)/(2(T_l² + 1/4))`, qui exige une borne du complément d'exposant `< 1 − β_l` (bande sans zéro au-dessus de `T_l`,
`prime_blocks_iff_future_zero_free`), de même nature que RH ; transport manquant : formule explicite du canal `J` (`Ei` absente de
Mathlib). Relecture Codex non disponible. `lake build RHV6Fresh` : EXIT=1, une erreur `:398`, `⊢ radialFactor ⟨p.zLaterMember, hL⟩ = 1`,
signature 1402b737cf7b.

## §69. Induction du régime ON : parité des fibres, premier niveau de défaut, trois sondes, invariant suffisant, E208–E211 (2026-10-13)

Mission : expliquer positivement la permanence du régime ON (premier zéro, deuxième zéro, transmission), découvrir une loi de
permanence ou établir rigoureusement pourquoi les invariants disponibles ne la démontrent pas. Audit initial : HEAD 76865690, arbre
propre, une erreur `:398`, signature 1402b737cf7b. Matrice des théorèmes existants (rapport `experiments/e208_e211_rapport_mathematique.md`
§2) : premier zéro ON (`anchor_canonical_one`, fermé), trois premiers ON (`first_three_zeros_control`, fermé), symétrie miroir
(`mirror_fixed_iff_onLine`, fermé), passage vertical (`engaged_regime_kept`, `canonical_vertical_of_history`, fermés), comptage total
(`passage_count_step_eq_fiber`, fermé, aveugle au côté), comptage ON (`onFiberCount_eq`, fermé, lecture ponctuelle), conservation
radiale (`radial_conservation_anchored`, OUVERT). Réutilisés, non recréés : les théorèmes d'ancrage, le point fixe du miroir, le déficit
(`zeroCountDeficit_nonneg`, `_mono`), le premier changement de régime (`exists_first_regime_break`, `first_regime_break_profile`).
`Terminal/OnRegimeInduction.lean` FERMÉ (17 théorèmes, objets `lowFiberCount`, `highFiberCount`, axiomes standard, importé par
`RHV6Fresh.lean`, composé dans la transmission : `hRegimeProbes`, `hFiberParity`, `hLowFiber`) : partition radiale et bijection miroir
sur toute famille finie stable (`sum_split_radial`, `sum_low_eq_sum_high`) ; parité de la fibre `fibre(T) − fibre_ON(T) = 2·fibre_BASSE(T)`
(`offLine_fiber_contribution_even`) ; `fibre_BASSE(T) = 0 ⟺` tout membre de hauteur `T` ON ; `D(T) = 0 ⟺` tout membre sous `T` ON
(`zeroDefect_eq_zero_iff_noOffBelow`) ; `ΔD(T, U) = 0 ⟺` aucun hors ligne dans `]T, U]` (`counting_increment_eq_iff_noOffInInterval`) ;
premier niveau de défaut : `D = 0` dessous, `D ≥ 2` à la hauteur, miroir distinct de même hauteur et multiplicité, `fibre_BASSE ≥ 1`,
`fibre ≥ 2` (`first_off_level_has_mirror_pair`) ; équivalence des trois sondes sous l'historique ON : `β_l = 1/2 ⟺ ΔD(T_e, T_l) = 0 ⟺
mirror(l) = l`, `ΔD = 0 ⟺ fibre_BASSE(T_l) = 0` (`regime_probes_equivalent`) ; schéma d'induction par invariant suffisant
(`on_regime_induction_of_independent_invariant`) ; instances : pas de comptage `< 2` (`count_step_invariant_suffices`, exige simplicité et
unicité : plus fort que RH), `ΔD = 0` (`lineDefect_invariant_suffices`) ; `ΔD = 0` quantifié sur les passages d'historique ON ⟺ RH
(`lineDefect_invariant_iff_riemannHypothesis`) : ce n'est pas une loi plus faible.
E208 (`experiments/e208_on_regime_anchor/`, 8 min, 10 PASS, 0 FAIL ; quatre figures PNG/SVG, registre CSV, JSON) : 300 changements de
signe de `Z` aux hauteurs publiées (écart ≤ 5e−10), `N(milieu_n) = n` par Turing (mpmath), `D = 0` sur 300 rangs, coupures
`N(14, 15, 17, 22, 23, 28) = 0, 1, 1, 2, 2, 3` (Lean pour 15/22/28, Arb E176 sinon), `|S(T)|` dépasse 1 (max 1,14) sous `T_300`,
loi de Gram violée 7/299. Lecture : sous 28, `D = 0` par la PARITÉ du pas de comptage (chaque pas vaut un, une rupture coûte deux), jamais
par une lecture de `N₀`. E209 (`experiments/e209_regime_transport/`, 8 PASS, 0 FAIL ; trois figures, CSV des 299 passages) : R1
`ΔN = ΔN₀(signes) = 1` 299/299 (observation, ⟺ ON ∧ simple), R2 `Δθ/π ∈ ]0, 2[` sur 299 mais violée sur 999 (Gram), R3 `|ΔS| < 1`, R4
contacts emboîtés et pas contracté (théorème, toute `β`), R5 `M^Z = M`, `EV + 1` (théorème), R6 classe mod 6 décorrélée de `Δθ/π` et `ΔS`
(|corr| 0,12). Aucune relation définie sans `β` n'est une loi démontrable indépendamment de RH. E210 (`experiments/e210_first_regime_change/`,
5 PASS, 0 FAIL ; deux figures, tables) : conséquences C1–C9 d'un premier défaut toutes rapportées à un théorème Lean (paire miroir,
saut pair, fibre, `ΔN = fibre`, `ΔN₀ = m_ζ`, argument aveugle au côté, ON double ≡ paire OFF pour `ΔN`, départ ON qui monte, `λ > 1`
encadré) ; C10 (loi indépendante interdisant la première apparition) seule NON DÉMONTRÉE ; saut `+2` de `S` sans changement de signe
exclu par aucune borne démontrée ; rectangles de droite `[σ', 2] × ]T_e, T_l]` d'enroulement nul sur 40 cas (`σ' → 0,51`) : lecture
exacte de l'obligation, pas une dérivation. E211 (`experiments/e211_on_regime_induction_probe/`, sonde `OnRegimeInductionProbe.lean`
HORS du graphe de build, compilée par `lake env lean`, trois `unsolved goals`, journal) : buts résiduels `False` sous `hBelow` /
« tout membre de la fibre `T_l` est ON » / `ρ_l = 1 − ρ̄_l`, démontrés équivalents ; plus faible proposition suffisante `ΔD(T_e, T_l) = 0`,
équivalente à RH quantifiée ; contre-modèle `β = 1/4` (`reducedContactSystem_not_identifying`) ; H1 : commuter avec l'involution ne
conserve pas les points fixes, l'hypothèse manquante est la loi elle-même ; H2 : argument, Riemann–von Mangoldt, Turing comptent `N`,
aveugles au côté, `S` non bornée ; H3 : portée réelle = parité, ne sépare pas ON double / paire OFF ; H4 : aucun opérateur construit,
critères de Li/Weil absents du périmètre. Verdict : FIRST_ZERO_ANCHOR=PROVED, MIRROR_FIXED_POINT=PROVED, ON_REGIME_INDUCTION=NOT_PROVED,
INDEPENDENT_INVARIANT=NOT_PROVED, FIRST_UNSOLVED_LEAN_GOAL = `DemonstrationChain.lean:399`, `⊢ radialFactor ⟨p.zLaterMember, hL⟩ = 1`,
MISSING_MATHEMATICAL_PROPERTY = lecture de `N₀` indépendante de la position des zéros (fibre d'arrivée sans membre bas),
PROPERTY_EQUIVALENT_TO_RH=TRUE, LAKE_BUILD=FAIL, RH_FOUND=FALSE. Annexe A recomptée : 276 fichiers, 18169 théorèmes, 438 objets.
`lake build RHV6Fresh` : EXIT=1, une erreur `:399`, signature 643740d74406.

## §70. Audit archéologique, challenge d'E208–E211, transport du régime ON, E212–E217 (2026-10-13)

Mission « audit archéologique intégral, challenge et recherche de la loi de permanence ON » ; document de référence de l'auteur
`experiments/HISTORICAL_AUDIT_ON_REGIME_E212_20261013.md` (commit dcc25340) conservé et enrichi. `Terminal/RegimeTransportAudit.lean`
FERMÉ (13 théorèmes, axiomes standard, importé ; `DemonstrationChain.lean` inchangé) : l'arrivée d'un passage qui monte est le membre de
partie réelle minimale de sa fibre (`arrival_radial_le_fiber`), basse dans une fibre mixte (`mixed_fiber_arrival_low`) ; sans
historique : arrivée ON ⟺ fibre ON ⟺ aucun hors ligne dans `]T_e, T_l]` ⟺ `ΔD = 0` ⟺ `fibre_BASSE = 0`
(`arrival_fiber_interval_equivalent`) ; inclusion dans une Tour ON : `x ≥ 1` ⟺ `β ≤ 1/2` ∧ support, `0 < x ≤ 1` ⟺ `β ≥ 1/2` ∧ support
(`inside_large_iff`, `inside_small_iff`, `passage_inclusion_split`), premiers ⟺ `x = 2` (`inside_primes_iff_at_two`) ; égalité des rapports
de normes en deux abscisses ⟺ même `β` (`transport_ratio_eq_at_two_points_iff`) ; égalités de normes d'E116 ⟺ même `β` et même module,
fausses sur tout passage qui monte (`raccord_norm_equalities_iff`, `raccord_norm_equalities_false_of_vertical`). E212 : archéologie
(`experiments/e212_archaeology/`, 42 entrées, tout l'historique par `git log --all -S`, aucune recompilation en worktree : PARTIEL) et
matrice de fidélité (13 points, aucune infidélité, réserves : classement intra-fibre conventionnel, `zetaReflect` homonyme, `mirrorPoint`
paramétrique, `psi_jump_at_prime` = `Λ(p) = log p` seulement, canaux brut et `J` non formalisés). E213 (modèle fini, 42 PASS), E214
(domaines, 8 PASS), E215 (fenêtre E158, 7 PASS), E216 (raccords, 4 PASS), E217 (sondes hors build : A, B, D ⟶ `β_l = 1/2`, C fermée par
le classement, C′ et E ouvertes). Verdict : HISTORY_AUDIT=PARTIAL, FABLE_EQUIVALENCE_AUDITED=PASS, MIXED_FIBER_MODEL=ACCEPTED,
GLOBAL_TOWER_TRANSPORT=NOT_PROVED, COUNTING_SATURATION_TRANSPORT=NOT_PROVED, ENERGY_RACCORD=NOT_PROVED, E158_NEW_CONSTRAINT=NOT_PROVED,
INDEPENDENT_INVARIANT=aucun, PROPERTY_EQUIVALENT_TO_RH=TRUE, LAKE_BUILD=FAIL, RH_FOUND=FALSE. Annexe A : 277 fichiers, 18182 théorèmes,
438 objets. `lake build RHV6Fresh` : EXIT=1, une erreur `:399`, signature 643740d74406.

## §71. Compatibilité globale des zéros avec tous les écarts premiers, E218–E223 (2026-10-13)

Mission « loi de compatibilité globale des zéros avec tous les écarts des nombres premiers ». `Terminal/GlobalGapSignature.lean`
FERMÉ (16 théorèmes, 2 objets `signatureGap`, `gapVariation`, axiomes standard, importé ; `DemonstrationChain.lean` inchangé) :
variation d'une signature sur un écart `(b^s − a^s)/s = ∫_a^b t^{s−1}` (`signatureGap_eq_integral`), jamais nulle
(`signatureGap_ne_zero`), enveloppe `(b^σ − a^σ)/σ` (`signatureGap_norm_le`), télescopage (`gapVariation_telescope`), vacuité de la
contrainte des écarts pour tout `s` (`gap_signature_constraint_vacuous`), décalage radial = repondération `t^d`
(`radial_shift_integrand`, `signatureGap_shift_norm_le`), membre bas sous une Tour ON ⟺ `‖ρ_z‖/‖ρ_{w'}‖ ≤ x^δ`
(`lower_member_below_iff`), profil de croisement d'une paire (`mirror_pair_crossing_profile`), hiérarchie ON
(`onLine_amplitude_hierarchy`), relation amplitude–fréquence pour toute `β` (`amplitude_frequency_relation_all_beta`). E218 (9 PASS :
hiérarchie sur 4999 passages, seuils de croisement en 60/100 chiffres, frontière `d log x = log(T/T₁)`), E219 (19 PASS : 324
signatures × 9591 écarts, erreur de l'approximation `≤ |ρ−1|g/(2p)` non uniforme en `T`), E220 (10 PASS : canal `J` par écart,
identité vérifiée à 1,8e−15, attribution collective), E221 (5 PASS : défaut `d²`, horizons, compensation libre sur fenêtre),
E222 (5 PASS : extraction en `log x`, identifie sans borner), E223 (sondes hors build `experiments/e223_global_gap_invariant/`, quatre
buts). Verdict : E218_DOMINANCE_ON=PROVED, E218_OFF_CROSSING=PROVED_CONDITIONAL, E219_GAP_SIGNATURE=PROVED_IDENTITIES_NO_CONSTRAINT,
E220_COUNTING_RECONSTRUCTION=IDENTITY_VERIFIED_COLLECTIVE, E221_COLLECTIVE_COMPENSATION=H2_NOT_EXCLUDED, E222_FREQUENCY_EXTRACTION=
IDENTIFIES_NOT_BOUNDS, E223_LEAN_INVARIANT=IDENTITIES_PROVED, GLOBAL_COMPATIBILITY_PROPERTY=aucune, PROPERTY_INDEPENDENT_OF_RH=FALSE,
PROPERTY_PROVED_FOR_ZETA=FALSE, PROPERTY_FORCES_BETA_HALF=FALSE, LAKE_BUILD=FAIL, RH_FOUND=FALSE. Annexe A : 278 fichiers, 18198
théorèmes, 440 objets. `lake build RHV6Fresh` : EXIT=1, une erreur `:399`, signature 643740d74406.


## §72. Fermeture expérimentale du but `:399` par stabilité harmonique, structure de ξ et contre-modèles, E224–E230 (2026-10-13)

Mission « fermeture expérimentale du but Lean 399 ». Diagnostic du compilateur en quatorze points
(`experiments/e224_e230_compiler_diagnostic.md`) : le but `radialFactor ⟨p.zLaterMember, hL⟩ = 1` est posé par
`refine absurd ?_ (ne_of_gt hLambda)` sous `hBelow`, il équivaut donc à `False` dans son contexte ; sonde hors build
`experiments/e224_e230_compiler_probe/GoalDiagnostic.lean` : variantes A/B/C non fermées volontairement, `variantA_iff_B`,
`variantB_iff_original`, `variantB_iff_C`, `control_hMissing_closes`, `control_intermediate_energy_closes` fermés (témoins : pas des
preuves). `Terminal/HarmonicRestoringLaw.lean` FERMÉ (23 théorèmes, 5 objets `harmonicMode`, `harmonicCompanion`, `harmonicEnergy`,
`complexMode`, `shiftedCompleted`, axiomes standard, importé ; `DemonstrationChain.lean` inchangé) : `harmonicMode_ode`,
`harmonicEnergy_eq`, `harmonicEnergy_hasDerivAt`, `harmonicEnergy_flat_iff`, `harmonicEnergy_deriv_sign`, `mirrorMode_add`,
`mirrorMode_sub`, `mirrorMode_add_norm`, `mirrorMode_add_norm_eq_two_iff`, `complexMode_bounded_iff`, `zeroTerm_normalized_mode`,
`zero_mode_ode_all_beta`, `harmonicEnergy_flat_iff_radialFactor`, `zero_mode_bounded_iff_radialFactor` (caractérisations),
`shiftedCompleted_one_sub`, `shiftedCompleted_zero_shift` (contre-modèle de l'équation fonctionnelle). Six sondes de fermeture
(`experiments/e230_terminal_closure_challenge/Closure{A..F}*.lean`), chacune avec exactement le but `:399`. E224 (4 PASS : énergie
arithmétique de ζ stationnaire, de `W_{0,1}` croissante à la pente de la paire `δ⟨tanh δu⟩ = 0,0714`), E225 (7 PASS : terme croisé
constant `> 0`, croissance `cosh` des deux côtés, insertion non compensée, remplacement compensé localement), E226 (10 PASS : noyau
de Riemann vérifié à 3e−31, `Φ > 0` pair décroissant, contre-modèles `e^{−u²}(1 + ½cos 6u)`, `K_δ`), E227 (7 PASS : force radiale
`Re ξ'/ξ = Σ (σ − β)/|s − ρ|²`, `> 0` sur la grille pour ζ, `−17,8` sous le zéro décalé de `F_δ`), E228 (8 PASS : seule
l'autoadjonction sépare ; construction de Hilbert–Pólya circulaire), E229 (5 PASS : réponse sur 78 497 écarts = détecteur exact de
`d`). Rapport `experiments/e224_e230_rapport_mathematique.md`. Verdict : formes amont équivalentes à RH (Lagarias, Sondow–Dumitrescu,
Jensen–Pólya) ou réfutées par `W_δ` ; FIRST_INDEPENDENT_UNPROVED_GOAL = `:399` sans forme intermédiaire indépendante de RH ;
RADIAL_CONSERVATION_PROVED=FALSE ; LAKE_BUILD=FAIL ; RH_FOUND=FALSE. Annexe A : 279 fichiers, 18221 théorèmes, 445 objets.
`lake build RHV6Fresh` : EXIT=1, une erreur `:399`, signature 643740d74406.


## §73. Fermetures par fenêtres finies, battements, grammaire des écarts et non-compensation, E231–E238 (2026-10-13)

Mission « huit fermetures du but Lean 399 ». Question : une première rupture OFF viole-t-elle une propriété de fenêtre finie
indépendante de la reconstruction arithmétique ? Les candidates sont : deux écarts exacts, contacts, battements, charge,
complément authentique.

`Terminal/TwoGapWindow.lean` est FERMÉ : 15 théorèmes, 3 objets (`gapPairSignal`, `gapPairDeformation`, `twoGapDet`), axiomes
standard, importé ; `DemonstrationChain.lean` est inchangé. Théorèmes :
- intégrande de la paire `pair_integrand_re` ;
- `gapPairDeformation_eq_sub` (`D_d = G_d − G_0`), `gapPairDeformation_even`, `gapPairDeformation_zero` ;
- signe opposé à `cos(T log x)` par segment : `gapPairDeformation_nonpos_of_cos_nonneg`, `_nonneg_of_cos_nonpos`,
  `_neg_of_cos_pos` ;
- charge : `windowChargeLog_ne_zero` (`q² ≠ pr`), `windowCharge_log_eq_zero_iff` ;
- déterminant : `twoGapDet_self`, `twoGapDet_swap`, `twoGap_reading_swap_blind` ;
- battements : `mirror_beat_modulus` (exposant 1 pour toute `d`), `pair_modulus_sum` ;
- Gram : `weighted_gram_nonneg`.

Neuf sondes hors build (`experiments/e231_e238_lean_closure_probes/`). Chacune laisse exactement le but `:399` ; celle de l'E232 le
réécrit en « charge nulle ».

Expériences, toutes avec README et figure :

| Exp. | PASS | Résultat | Verdict |
|---|---|---|---|
| E231 | 6 | 53 712 segments, signe fixé par la phase | REFUTED |
| E232 | 9 | 148 931 triplets, `L` lu par `c₂ − c₁` à corrélation 0,99995, aucune donnée ne contient `d` | REFUTED |
| E233 | 7 | parité exacte, ordre `d²`, complément authentique non vérifié | DIAGNOSTIC |
| E234 | 3 | `C_auth` démontré contient le complément, rapport ≤ 0,12 | REFUTED |
| E235 | 7 | déterminant impair, non nul, observation de rang 1 | DIAGNOSTIC |
| E236 | 5 | renversement central = caractérisation | CIRCULAR |
| E237 | 5 | compensation sur fenêtre `U = 2` à poids libres, échec hors fenêtre ; global ⟺ borne du reste | REFUTED (fenêtre) / CIRCULAR (global) |
| E238 | 5 | détection seulement contre une troncature non certifiée | DIAGNOSTIC |
| Route eulérienne | 6 | Gram positif pour `W_δ`, non PSD à `σ = 0,75` | REFUTED |

Rapports :
- `experiments/e231_e238_rapport_mathematique.md` ;
- `experiments/e231_e238_compiler_diagnostic.md` ;
- `experiments/e231_e238_countermodels.md` (CM1–CM9).

Verdict : NEW_INDEPENDENT_INVARIANT = aucun. FIRST_UNPROVED_ARROW = borne indépendante des zéros du complément d'exposant
`< 1/2 + d` (bande sans zéro). GOAL_399_CLOSED = FALSE, RADIAL_CONSERVATION_PROVED = FALSE, RH_FOUND = FALSE.

Annexe A : 280 fichiers, 18236 théorèmes, 448 objets. `lake build RHV6Fresh` : EXIT=1, une erreur `:399`, signature
643740d74406.


## §74. Causalité harmonique, premier zéro et transmission du régime ON, E239–E241 (2026-10-13)

Mission consolidée E239–E241. Question : les contacts et l'enroulement des Tours authentiques imposent-ils une interaction
harmonique qui transmet la croissance radiale du premier zéro aux suivants ? Réponse : non, testé dans Lean.

`Terminal/HarmonicCurrentTransport.lean` FERMÉ (18 théorèmes, 5 objets `harmonicCurrent`, `crossCurrent`, `reducedCurrent`,
`currentRatio`, `zeroDepth`) et `Terminal/HarmonicCrossCurrent.lean` FERMÉ (15 théorèmes, 1 objet `collectiveCurrent`), axiomes
standard, importés ; `DemonstrationChain.lean` inchangé. Résultats :
- courant `J = Im(ū u') = T e^{2dt}` (`harmonicCurrent_eq`), `K = ‖u‖²`, `Q = e^{2(d₂ − d₁)t}` (`currentRatio_eq`) ;
- tests B, C, D ⟺ `d₁ = d₂` (`currentRatio_eq_one_iff`, `currentRatio_two_points_iff`, `currentRatio_const_iff`) ;
- test A : contre-modèle `winding_admissible_current_free` ;
- test E : `two_point_current_transport_iff_radialFactor`, `contact_current_transport_iff` (⟺ but) ;
- courant croisé `crossCurrent_eq`, partie symétrique `crossCurrent_symm_eq`, collectif `collectiveCurrent_eq_sum` ;
- paire miroir : `mirror_cross_current_blind` (`2T` pour toute `d`), `mirror_pair_current_eq` (`4T cosh²`),
  `cross_current_mirror_eq_double` ;
- `currentRatio_eq_tower_ratio_sq`, `two_point_current_iff_norm_ratio` : le transport du courant est l'égalité d'E216.

Trois sondes hors build (`experiments/e239_first_zero_causality/ProbeE239_FirstZero`,
`e240_harmonic_current/ProbeE240_TwoContactCurrent`, `e241_tower_coupling/ProbeE241_Coupling`) : une erreur chacune, le but ;
E240 le réécrit en `Q(log C_0) = Q(log C_1)`.

| Exp. | PASS | Résultat | Verdict |
|---|---|---|---|
| E239 | 13 | Ξ, Fourier, argument, comptage, premier zéro simple ; part dépendante de la fenêtre | FIRST_ZERO_CAUSE = Ξ entière, aucune cause locale |
| E240 | 7 | identité du courant ; A contre-modèle ; B/C/D caractérisations ; E ⟺ but | HARMONIC_CURRENT_IDENTITY = PROVED ; transport CIRCULAR |
| E241 | 9 | croisé, collectif, cinq configurations, différence paire en `d`, inventaire de 23 théorèmes, CM12 | CROSS_CURRENT_IDENTITY = PROVED ; couplage : aucun |

Rapports : `experiments/e239_e241_rapport_mathematique.md`, `e239_e241_compiler_diagnostic.md`, `e239_e241_countermodels.md`
(CM10–CM13). Contrôle E158–E238 : le courant croisé réécrit `pair_modulus_sum`, `mirror_beat_modulus`, l'énergie harmonique et
l'égalité des rapports de normes d'E216 ; aucune relation nouvelle.

Verdict : CONTACT_PHASE_LOCK = REFUTED, CONTACT_AMPLITUDE_LOCK = CIRCULAR, TWO_CONTACT_CURRENT_TRANSPORT = CIRCULAR,
AUTHENTIC_TOWER_COUPLING = aucun, FIRST_OFF_EXCLUDED = FALSE, GOAL_399_CLOSED = FALSE, FIRST_UNPROVED_ARROW = borne
indépendante des zéros du complément d'exposant `< 1/2 + d`, RH_FOUND = FALSE.

Annexe A : 282 fichiers, 18269 théorèmes, 454 objets. `lake build RHV6Fresh` : EXIT=1, une erreur `:399`, signature
643740d74406.

## §75. Audit radial total : signal exact `x^ρ/ρ` contre représentations normalisées, E242 (2026-10-13)

Question : les représentations normalisées (modes unitaires, différences de phases, courants réduits, observables
collectives) ont-elles masqué une information sur `β` ? Réponse : le coefficient `1/ρ` porte `β` par `‖ρ‖` et par
`θ = arctan(T/β)`, mais c'est une constante en `t`. Il ne change aucune caractérisation, corrige deux interprétations et
n'apporte aucune contrainte indépendante.

`Terminal/ExactSignalArchitecture.lean` FERMÉ (41 théorèmes, 18 objets, axiomes standard, importé ; chaîne non modifiée) :
- trois types distincts `ExactZeroSignal`, `RescaledZeroSignal`, `UnitCoefficientMode`, et leurs conversions ;
- forme polaire `exactSignal_polar` ;
- courant exact `exactCurrent_eq` (multiple réel du courant unitaire ; tests inchangés : `exactCurrentRatio_two_points_iff`,
  `exact_current_transport_iff_radialFactor`) ;
- interférence `exact_interference_normSq` ;
- croisé `exactCross_eq`, `exactCross_symm_eq` ; collectif `exactCollectiveCurrent_eq_sum` ;
- rotation `exactCross_eq_rotated_unit` ;
- correction miroir `exact_mirror_cross_eq`, `exact_mirror_cross_lt_double` ;
- contacts `exact_contacts_determine_parameters` ;
- perte de phase `unitMode_im_zero_at` ;
- régression `zeroTerm_ne_unitMode`.

Portée ajoutée au docstring de `HarmonicCrossCurrent` (énoncés unitaires).

E242 (16 PASS) :
- inventaire Lean : 614 occurrences, mode unitaire dans 3 fichiers, aucun importé par la chaîne ;
- inventaire des 172 scripts : 170 UNCHANGED, 2 CORRECTED (E240 : constante ; E241 : aveuglement miroir propre au mode
  unitaire) ;
- E44, E96–E100 et les sondes E116 sont NOT_REPRODUCIBLE ; le résultat d'E116 est compilé (type E) ;
- quatre scénarios tenus ; combinaison 4.4 sur 1 075 cas, 0 violation ;
- quatre figures.

Sonde hors build `ProbeE242_ExactCurrent` : une erreur, le but réécrit en égalité des courants exacts.

Documents : `AUDIT_RADIAL_TOTAL_20261013.md` (contrats classés A–E ; type D : certificats de comptage 15/22/28 seuls),
`RADIAL_SIGNAL_CONVERSIONS.md`, `EXPERIMENTS_RADIAL_CORRECTION_INDEX.md`, `CLOSURE_ROUTES_RADIAL_REASSESSMENT.md`.

Verdict :
- EXACT_SIGNAL_ARCHITECTURE = PASS ;
- RADIAL_INFORMATION_PRESERVED = PASS ;
- INDEPENDENT_CLOSURE_CONSTRAINT = NOT_PROVED ;
- RADIAL_CONSERVATION_PROVED = NOT_PROVED.

Annexe A : 283 fichiers, 18310 théorèmes, 472 objets. `lake build RHV6Fresh` : EXIT=1, une erreur `:399`, signature
643740d74406.

## §76. Synchronisation des Tours sur chaque écart premier, E243 (2026-10-13)

Demande de l'auteur : structure imposée (amplitude commune, fréquences et phases distinctes), aucune normalisation ; trouver la
loi d'interférence qui reproduit la correction de chaque écart premier, et l'utiliser pour fermer `:399`.

Lean : `Terminal/GapSynchronization.lean` (13 théorèmes, 3 objets `gapTerm`, `gapCenter`, `gapHalfWidth`), importé, chaîne non
modifiée :
- `gapTerm_eq`, `gapTerm_sinh`, `unitGapTerm_sinc`, `gapTerm_onLine`, `gapTerm_eq_cpow` (contribution exacte à un écart) ;
- `density_norm`, `common_amplitude_iff`, `common_amplitude_mirror_iff` (amplitude commune ⟺ même `β`) ;
- `residueTerm_gap_eq`, `smoothed_gap_synchronization`, `prime_gap_synchronization` (loi par écart, tous les vrais zéros) ;
- `gap_sum_linear`, `gapTerm_shift`.

Sonde hors build `ProbeE243_GapSync` : une erreur, même but. Contrôle TDD `probe_ProbeE243_control` : amplitude commune de
l'arrivée en hypothèse ⟹ corps fermé (caractérisation). Argument du miroir OFF de même hauteur : règle de verticalité démontrée
au seul départ d'un membre en ligne (`engaged_regime_kept`) ; sur tout passage ⟺ RH (`no_sameHeight_iff_riemannHypothesis`).

E243 (8 PASS, 1 MESURE, 1 DIAGNOSTIC) : loi par écart ψ 3,1 %, J 1,3 % ; superposition linéaire (R² 0,85) contre battements
(R² 0,10) ; contacts non porteurs ; peigne de Dirac `Λ(n)` en `log n` et biais de Landau retrouvés ; même loi dans `W_δ` ;
ajustement fini exact, non transportable.

Verdict : loi démontrée et vérifiée ; elle vaut pour toute partie réelle avec les poids correspondants ; l'amplitude commune
des densités caractérise la ligne et n'en découle pas ; INDEPENDENT_CLOSURE_CONSTRAINT = NOT_PROVED. Annexe A : 284 fichiers,
18323 théorèmes, 475 objets. `lake build RHV6Fresh` : EXIT=1, une erreur `:399`, signature 643740d74406.

## §77. Synchronisation à amplitude stable, fréquences seules ; audit externe d'E243, E244 (2026-10-13)

Demande de l'auteur : « le but 399 est soit mal implémenté soit doit être modifié pour accepter la nouvelle information : les zéros
sont reliés par une synchronisation nécessaire, impossible à obtenir par des changements d'amplitude ; la synchronisation avec le zéro
initial n'est possible qu'avec une amplitude stable et seulement des changements de fréquences » ; audit externe collé : garder `:399`
inchangé, ne jamais supposer l'amplitude commune de l'arrivée, vrais coefficients de ζ, contre-modèle `β = 1/4`, reclasser les
verdicts d'E243.

Implémentation du but : `radial_conservation_anchored` est la traduction exacte du verrou (historique ON, départ ON, passage
consécutif qui monte ⟹ même partie réelle), aucune définition n'est modifiée ; « modifier le but pour accepter l'information »
serait ajouter une prémisse (interdit) ; l'information est écrite comme contrat et son rapport au but est démontré.

Lean : `Terminal/AmplitudeStableSynchronization.lean` (14 théorèmes, 2 objets), importé, chaîne non modifiée :
- `AmplitudeStableSync p` ⟺ rapport des densités de module 1 (`frequency_only_iff`) ⟺ `β_l = β_e` (`amplitudeStableSync_iff`) ;
- départ ON + contrat ⟹ `radialFactor = 1` (`amplitudeStableSync_closes`) ;
- contrat quantifié sur les passages qui montent depuis un membre ON (avec ou sans historique) ⟺ RH sous l'ancre
  (`amplitudeStable_law_iff_riemannHypothesis`, `amplitudeStable_history_law_iff_riemannHypothesis`) ;
- remplacement d'un point `ρ` par `ρ' ≠ ρ` (coefficient recalculé, autres contributions conservées) : défaut non identiquement nul,
  non-reconstruction (`replacement_defect_not_identically_zero`, `replacement_not_reconstruct`) ; instances amplitude `ρ + δ`
  (`amplitude_change_not_reconstruct`) et fréquence `ρ + iδ` (`frequency_change_not_reconstruct`) ;
- `authentic_family_reconstructs_any_radial` (représentation exacte sans position).

Sonde hors build `ProbeE244_AmplitudeStable` : même but ; contrôle TDD : contrat en hypothèse ⟹ corps fermé.

E244 (Sonnet, 10 clés, 5 figures) : loi par écart (erreur relative médiane 1,6e−3) ; remplacement d'un zéro (k = 2, 10, 100) :
amplitude `β = 1/4`, fréquence `T + ΔT`, paire miroir ; défaut par écart ≥ 13 fois l'erreur de la loi dans tous les cas ; par unité de
déplacement, le changement de fréquence donne un défaut environ deux fois plus grand ; compensation hypothétique du défaut d'amplitude
par K zéros voisins : fréquence seule ajuste la fenêtre à 3,5e−6, amplitude seule à 4,6e−5, coefficients libres à 1e−13, aucune famille
ne transporte sur les 36 écarts suivants (résidus médians 1,53 / 3,34 / 3,04) ; contre-modèle `β_l = 1/4` à `T_2` : tous les contrats
réduits satisfaits (phase, `λ = 1,000566`, contacts, emboîtement), défaut arithmétique du remplacement 0,66 du `|C_n|` médian ;
reclassement : intensité quadratique R² 1e−4 contre 0,80 pour la somme linéaire (QUADRATIC_INTENSITY_AS_DIRECT_CORRECTION = REFUTED,
les battements ne sont pas réfutés comme structure) ; contacts stratifiés par hauteur : +0,549 contre +0,631 ± 0,032 (NOT_SPECIFIC).

Verdict : l'énoncé de l'auteur est un contrat équivalent au but et à RH ; ce qui est démontré en plus est l'exclusion de tout
remplacement, sans distinction amplitude / fréquence ; « seules les fréquences compensent » n'est pas corroboré ; le vrai membre atteint
reconstruit par théorème quelle que soit sa partie réelle. INDEPENDENT_CLOSURE_CONSTRAINT = NOT_PROVED. Annexe A : 285 fichiers,
18337 théorèmes, 477 objets. `lake build RHV6Fresh` : EXIT=1, une erreur `:399`, signature 643740d74406.

## 78. Synchronisation locale des 300 zéros sur chaque écart premier, C126, rigidité radiale, E264–E300 (2026-10-14)

Mission (adressée à Opus, exécutée par Fable) : contrainte C126, matrice des contributions, reconstruction écart par écart, première arrivée
OFF, rigidité et identifiabilité, contacts, campagne E271–E290, formalisation Lean, audit des « 125 contraintes », intégration au but
`:399`. Correction de l'auteur en cours de mission : contribution exacte `C_j(a,b) = −2∫_a^b t^{β_j−1}cos(T_j log t)/log t dt`, contributions
partielles dans l'écart, densité locale, changements de signe `x_{j,k} = exp((π/2+kπ)/T_j)`, sommation symétrique, aucun transfert de
résidu ; puis audit prioritaire « la contribution locale n'est pas aveugle à β » (distinguer détecter, retrouver, prouver β).

Lean (`Terminal/LocalPrimeGapSynchronization.lean`, 43 théorèmes, 14 objets, axiomes standard, importé ; chaîne non modifiée) :
écart premier `PrimeGapInterval` ; contribution locale `countingGapTerm ρ a b = ∫_a^b e^{ρt}/t dt`, forme réelle de l'auteur
(`zeroLocalContribution_eq_real_integral`), télescopage, enveloppe, dérivée par rapport à la borne = densité, signe marginal = cosinus de
la phase, zéros de la densité (hauteur seule) et décalage au contact de phase `−arctan(β/T)/T`, facteur hyperbolique de la paire miroir ;
canal lissé : synchronisation locale sur CHAQUE écart (`localSynchronization`), résidu d'une troncature finie = queue infinie
(`localResidual_eq_tail`), tautologie de la décomposition finie ; rigidité (`local_contribution_rigidity`, `gapTerm_rigidity`), valable pour
toute `β` (`rigidity_identifies_any_radial`) ; sensibilité radiale `∂_β C = gapTerm` par dérivation sous l'intégrale
(`countingGapTerm_radial_hasDerivAt`, forme fermée `zeroLocalContribution_radial_derivative`), théorème A de l'auteur
(`density_radial_injective`), inversion à deux points (`radial_inversion_two_points`) ; lecture ON des contributions locales ⟺ `β = 1/2`
(`localOnScale_iff`), ferme le but depuis un départ ON (`localOnScale_closes`), quantifiée ⟺ RH sous l'ancre
(`local_on_law_iff_riemannHypothesis`). Sonde hors build `ProbeE264_LocalSync` : même but ; contrôle TDD : la lecture ON en hypothèse ferme.
Réponse à l'audit prioritaire : seuls les points de changement de signe de la densité sont indépendants de `β` ; la contribution, la
densité et l'enveloppe en dépendent explicitement ; la première formulation « rigidité aveugle à β » voulait dire « identifie toute β »,
théorème renommé.

Numérique (deux agents, ≈ 5 min ; 28 figures) : matrice 300 × 1000 (référence 5000 × 5000), précision 8e−14, formule de l'auteur = Ei à
2e−29 ; aucun écart dominé par une Tour (0/1000), annulation `|Σ|/Σ|C|` 0,05 ; reste de troncature médian canal J 1,3e−2 (300 écarts, 5000
zéros), 4,5e−2 (1000), canal lissé 3,4e−5 ; seule la convention milieu des sauts est cohérente ; aucun résidu transféré (1e−14) ; trois
familles de points disjointes (`x_k`, `C_k`, `X_k`), décalage `−arctan(β/T)/T` à 3e−15 ; identité hyperbolique 6e−14 ; ΔC ≠ 0 sur 100 % des
écarts dès `d = 0,01`, aucune contradiction ; jacobien de rang 2 dès deux écarts, inversion de `(β, T)` exacte pour β = 1/2, 0,25, 0,4 ;
`∂C/∂β` fermé = différence finie (1,5e−9), annulations oscillatoires 0,4 % ; depuis le signal total à famille inconnue : ajustements faux
sur fenêtre finie, sept hypothèses nécessaires ; 0 faux positif sur 300 ON ; monde témoin `W_δ` : loi locale tenue avec ses poids (0,0025,
identique à ζ) ; contacts ↔ premiers : hasard. Audit des contraintes : le nombre 125 n'existe nulle part (SEM §12 : 136 rigidités
numérotées, écart déjà consigné §15, 2026-10-05) ; inventaire R1–R136 + C126, 348 noms vérifiés ; C126 = lecture locale de la formule
explicite et de l'unicité spectrale, aucune information indépendante ; une trentaine de modules E208–E244 sans entrée numérotée.

Verdict : C126_LOCAL_IDENTITIES = PROVED (toute β) ; RADIAL_SENSITIVITY = PROVED ; INDIVIDUAL_RADIAL_IDENTIFIABILITY (théorème A) = PROVED ;
RADIAL_CONSERVATION_AT_PASSAGE (théorème B) = NOT_PROVED (⟺ but) ; OFF_MATHEMATICAL_CONTRADICTION = NONE ; INDEPENDENT_CLOSURE_CONSTRAINT =
NOT_PROVED ; RH_FOUND = FALSE. Annexe A : 286 fichiers, 18380 théorèmes, 491 objets. `lake build RHV6Fresh` : EXIT=1, une erreur `:399`,
signature 643740d74406.

## 79. Audit contradictoire de la synchronisation locale, de la queue et des rigidités, E301 (2026-10-14)

Mission (« OPUS — audit contradictoire total ») : identifier les erreurs structurelles qui empêchent la synchronisation locale de contraindre
le premier passage OFF ; auditer `localSynchronization`, `localResidual_eq_tail`, les rigidités R1–R136 et C126, les définitions et modèles
réduits, le but `:399` (contradiction avec `hLowFiber` seulement depuis une propriété authentique, sans `LocalOnScale`, `AmplitudeStableSync`
ni égalité de normes en hypothèse), l'expérience numérique (trois expériences séparées). Rapport :
`experiments/E301_AuditContradictoire/RAPPORT_AUDIT_CONTRADICTOIRE_E301.md`.

Lean (`Terminal/SynchronizationAudit.lean`, 8 théorèmes, 1 objet, axiomes standard, importé ; chaîne non modifiée) :
`gap_synchronization_any_family` (synchronisation par écart pour toute famille), `localSynchronization_from_explicit_formula` (seule entrée
propre à ζ : formule explicite lissée), `residual_eq_tail_any_family` et `localResidual_eq_tail_of_sync` (la queue est un fait générique),
`localHeightResidual`, `localHeightResidual_eq_tail_increment`, `localHeightResidual_bound` (`‖résidu_H(I_n)‖ ≤ budget(H)(p_n + p_{n+1})`,
uniforme en l'écart, sans RH), `tail_bound_any_family` et `tail_bound_admits_offline_point` (non discriminante). Docstrings corrigés dans
`LocalPrimeGapSynchronization.lean` (aucun énoncé modifié) : reconstruction du canal de comptage non formalisée ; rigidité sur un continu de
bornes, pas sur les seuls écarts premiers ; troisième composant de `c126_holds_any_radial` = trichotomie.

Graphe : méta-programme `DepGraph.lean` (types et dépendances de PREUVE transitives de 336 théorèmes porteurs ; `value? (allowOpaque :=
true)` nécessaire, sinon seuls les types sont lus) ; 358 arêtes entre rigidités ; classement des théorèmes : 217 identités universelles, 19
identifiabilités, 19 caractérisations de `β = 1/2`, 15 équivalences avec RH, 19 conditionnels, 20 contraintes sans RH, 6 contre-modèles,
21 définitions ou conséquences de RH ; doublons R32 ≡ R50, R83 ≡ R93, porteur partagé R34/R37 ; cycles au niveau des rigidités = effets de
regroupement (le graphe des théorèmes est acyclique) ; colonne « Dép. RH » de l'inventaire C126 = preuve sans RH, pas contrainte (note
ajoutée). Sondes `:399` hors build (`ProbeE301_Goal399.lean`) : comptage (`N(T_e) + 2 ≤ N(T_l)`), symétrie (miroir `> 1/2`), produit
eulérien (`β_l > 0`), formule explicite (queue d'exposant 1, paire admise), progression (`β_l ≤ 1/2`) : cinq `False` ouverts ; conjonction
satisfaite par `β = 1/4` (`probe_consistency`, fermé). Numérique (canal lissé, `e301_audit_numerique.py`) : F1 résidu médian 3,4e−5,
1000/1000 écarts sous la borne démontrée ; F2 (queue figée) détecte OFF 73–99,6 %, double ON 63–98 %, ON décalé 11–80 % : non
discriminant ; F3 (queue variable bornée) compensation admissible, rapport ≤ 0,073 : non discriminant sous la borne démontrée.

Verdict : SYNCHRONIZATION_INDEPENDENT_CONSTRAINT = NONE ; TAIL_INDEPENDENT_CONSTRAINT = NONE ; UNIFORM_TAIL_BOUND = PROVED (exposant 1,
non discriminant) ; INDEPENDENT_IMPLICATION_TO_OFF_CONTRADICTION = NOT_FOUND ; RH_FOUND = FALSE. Annexe A : 287 fichiers, 18388 théorèmes,
492 objets. `lake build RHV6Fresh` : EXIT=1, une erreur `:399`, signature 643740d74406.

## 80. Trois Tours ON, contacts, fond li, écarts premiers, synchronisation, E302 (2026-10-14)

Mandat « reconstruction intégrale des trois Tours ON, synchronisation première et validation géométrique 3D », phase ON uniquement.
Aucun fichier Lean modifié. `experiments/E302_THREE_ON_TRUE_3D_SYNCHRONIZATION/` (`three_on_3d.py`, 82 contrôles PASS ; nom E207 proposé
déjà pris). Zéros recalculés à 40 chiffres, dans les boules Arb d'E176, ON démontrés dans Lean (`first_three_zeros_control`). Tour
retenue = `zeroTerm` (`x^ρ/ρ`, départ `1/ρ`, pôle de rotation à l'origine) ; `Γ_ρ = ρ + q − q(1)` d'E205 = convention. Aucune
intersection spatiale entre Tours (rapport des rayons `|ρ_b|/|ρ_a|` constant). Contacts : phase (forme close), extrema, li (individuel
`Re Ei(ρ log x) = 0`, couverture exacte par morceaux monotones ; collectif), comptage π, alignements de phase ; inversion `(T, β)` aux
seuls contacts de phase. Reconstruction : RMS J 0,687 → 0,522 (3 zéros) → 0,031 (5000). Synchronisations : S4 formule explicite
sélective en hauteur (aucun des 400 triplets aléatoires) ; S3b résonance `Σ p^{−iT_j} − ∫ ≈ −li(√x)` ; S5 intersection avec li =
contact de phase + quart de tour asymptotiquement ; S3a premiers non attirés par les contacts (KS contre le fond). Rigidités : 89 PASS,
0 FAIL, 26 non applicables, 21 non vérifiables. Verdict : GEOMETRY_ON = RECONSTRUCTED ; ADDITIONAL_GEOMETRIC_SYNCHRONIZATION = NOT_FOUND ;
VERIFIED_SYNCHRONIZATION = EXPLICIT_FORMULA (lit T, pas β) ; OFF_PHASE = NOT_STARTED (accord de l'auteur requis). `lake build RHV6Fresh` :
EXIT=1, une erreur `:399`, signature 643740d74406.

Correction de l'auteur (2026-10-14, même section) : la synchronisation doit être présente sur chaque écart premier et redémarrer à chaque
premier ; S4 la mesurait globalement. `per_gap_synchronization.py` (11 PASS) : signal exact du canal J, `β` conservé (`t^{β−1}`, quadrature
à 8·10⁻¹⁵, `∂Δb/∂β ≠ 0` sur 168/168 écarts) ; famille ON (5000 zéros) : signe suivi sur 100 % des écarts, résidus des 168 intérieurs et
168 sauts sous l'échelle de troncature de Gibbs, décroissants de 1000 à 5000 zéros dans chaque bande ; ρ₁ remplacé par `1/2 ± d` (poids ½) :
défaut non nul sur 168/168 écarts et sauts, ordre `d²`, croissant en x. Portée : remplacement dans la famille authentique
(`replacement_not_reconstruct`), pas zéro hors ligne authentique ; `:399` inchangé. Phrase « aucune relation ne lit la partie réelle »
retirée (fausse) ; aucune ne fixe `β = 1/2`. Figure 8.

## 81. Synchronisation collective des trois premières Tours ON, E303 (2026-10-14)

Mandat « battements collectifs des trois Tours ON et reconstruction des écarts premiers », phase ON seulement, but `:399` hors critère. Correction de l'auteur en cours d'expérience : synchronisation = superposition des trois contributions + interférences de phase, pas alignement de contacts ; zéros conjugués = partenaires qui rendent chaque contribution réelle, comptés une seule fois ; énergie à deux échelles (différences et sommes). Première version (canal « contacts `Im Q_N = 0` » de la somme complexe sans conjugués, `|Q_N|²` comme seul battement) ARRÊTÉE et reconstruite, non publiée. `experiments/E303_THREE_ON_COLLECTIVE_BEATS/` : `e303_collective_beats.py` (19 contrôles PASS, 3 min), signal réel `S_N = Σ 2 Re q_j`, comptage `C_N = Σ −2 Re Ei(ρ_j log x)` ; six canaux d'événements ; hiérarchie 1 → 2 → 3 (déplacements ≈ 15 % puis ≈ 9–14 % d'un intervalle) ; obstruction de Jensen `O(log X)` événements (S₃ = 0 : 50 ≤ 437 < 1229) ; aucun canal plus proche des premiers que 200 triplets témoins après correction (seul rang brut < 5 % : `C₃ = 0` en validation, 0,045 > 0,05/12) ; fenêtres de la première Tour : signe suivi 73 %, corrélation 0,62, témoins 50 %, −0,01 (contribution propre de Z1 ≈ 0 sur ses fenêtres, portée par Z2 et Z3) ; par écart 52 % ; prédicteur `π_N = n − 1/2` : 0,89 → 0,41 (x ≤ 100), 10,7 → 8,0 (≤ 10⁴), 0/200 témoins aussi bons ; écart suivant non amélioré au-delà de 100. Module Lean expérimental hors build `lean/BeatsE303.lean` (9 théorèmes, axiomes standard). Verdict : A OUI (démontré), B OUI, C exacte NON (démontré), approchée NON (mesuré), D OUI à l'échelle des fenêtres de la première Tour et pour la position moyenne des premiers, NON pour l'écart individuel. Aucune conclusion sur `β` ni sur RH ; `lake build RHV6Fresh` : EXIT=1, une erreur `:399`, signature 643740d74406.

## 82. Audit du projet et du but `:399` : les 136 rigidités dans l'ordre du but, inventaire des pistes, trois pistes retenues (2026-10-15)

Demande de l'auteur : « audit sur le projet et sur le but 399 ; relister les 136 rigidités dans un ordre en rapport avec le but ;
déterminer les trois meilleures pistes de fermeture (mathématiques, géométriques, énergétiques…) avec chances, avantages, inconvénients ».
Document : `AUDIT_PISTES_BUT399_20261015.md`. Aucun fichier Lean modifié ; build réexécuté : une erreur, `:399`, signature 643740d74406.

Résultats : (1) nature du but, compilée : la loi de conservation à historique ON quantifiée ⟺ RH, sa négation = premier changement de
régime ; fermer `:399` sans hypothèse ajoutée = démontrer RH ; (2) les 136 rigidités relues en dix paliers T0–T9 par proximité au but
(T0 : 15 réécritures du but ; T1 : 9 contraintes indépendantes, conjonction satisfaite par `β_l = 1/4` ; T2 : 7 fermetures conditionnelles ;
T3–T7 : 91 identités/détecteurs vrais pour toute `β` ; T8 : 11 observations ; T9 : 3 témoins) ; (3) inventaire de 17 familles de pistes
(géométriques G1–G3, grammaire A1, arithmétiques A2–A3, énergétiques E1–E3, spectrale S1, synchronisation S2, comptage C1–C2, premier zéro P1,
reconstruction R1–R2, externes X1–X2), chacune avec compilé et obstruction : toutes aboutissent à l'une de trois formes ⟺ RH (borne du reste
d'exposant `< 1`, captivité universelle, `N₀ = N` à toute hauteur) ; (4) tableau de douze pistes classées ; retenues : comptage sur la ligne
(≈ 3 %, rendement 100 % à hauteur finie par le générateur de boîtes), borne critique du reste depuis `Λ(n)` (≈ 2 %, seule couche séparant ζ
des témoins), positivité de la formule explicite sur les noyaux du cadre (≈ 2 %) ; chance nulle compilée pour géométrie, grammaire, spectrale
et synchronisation (contre-modèles `parameter_grid_admissible`, `winding_admissible_current_free`, `reducedContactSystem_not_identifying`,
`rigidity_identifies_any_radial`, `tail_bound_any_family`). Condition commune : un ingrédient faux dans `ζ(s−δ)ζ(s+δ)`. RH_FOUND=FALSE.

## 83. Théorèmes A et B de l'auteur : saut collectif à l'événement premier, contacts partagés, condition de ligne ; vérification des expériences OFF, E304 (2026-10-15)

Objections de l'auteur, vérifiées script par script : (1) hauteur de l'OFF hypothétique dans les 109 scripts E094–E303 qui en construisent un :
70 à la hauteur d'un ON de ζ (remplacement ou fibre doublée), 23 mondes témoins entiers (hauteurs de ζ, aucun ON), 16 à hauteur nouvelle
(milieu `(T_j + T_{j+1})/2`, ON conservés), 11 sans hauteur ; fibre mixte explicite dans E117, E118, E127, E177 INTERC, E242. Objection
FONDÉE : toute configuration OFF numérique du dépôt est un remplacement ou une insertion dans la famille vraie, jamais un OFF authentique ;
(2) normalisation de la quantité comparée (88 scripts) : 19 brutes, 26 par `√x` (`x^{β−1/2}` conservé), 16 rapports `x^{Δβ}`, 24 lectures
sans normalisation dont 5 sans `β` (E102, E104 classes mod 6 ; E112 ; E231 signe ; E270 racines de densité), 3 aveugles par division par
l'énergie ou l'enveloppe propre (E154 `Tr`, E187 §6, E284 (i)), toutes annoncées comme telles. Objection « 100 % aveuglées » NON soutenue ;
la division par `√x` est la lecture la plus sensible à `β` du dépôt (`rescaled_amplitude_flat_iff`).

Programme de l'auteur (texte collé) : théorème A, raccord grammatical contraignant dérivé des poids exacts et de la reconstruction
collective ; théorème B, incompatibilité radiale pour une arrivée authentique à `β' < 1/2`, `T'` libre, tous les autres zéros présents.
Écrit et compilé : `Terminal/GrammaticalRaccordJump.lean` (13 théorèmes, axiomes standard, importé par `RHV6Fresh.lean` ; chaîne non modifiée).

| Théorème | Énoncé | Statut |
|---|---|---|
| `psi_step`, `psi_step_at_prime_event` | `ψ(N+1) − ψ(N) = Λ(N+1)` ; `ψ(p) − ψ(p−1) = log p` au premier `p = p_n`, `n ≥ 1` | FERMÉ |
| `collective_jump_at_prime_event` (A) | `R_spectral(p) − R_spectral(p−1) = log p − (Δ²fond)` : la contribution collective de TOUS les zéros à la marche `p` est le poids exact moins la seconde différence du fond | FERMÉ, identité |
| `complement_forced_at_prime_event` | pour toute partie `S` d'indices, le complément au saut est fixé par le saut, le fond et `S` | FERMÉ, identité |
| `collective_jump_at_arrival_occurrence` | A à l'occurrence `Occ(l) = p_{n_l}` du membre atteint | FERMÉ |
| `shared_consecutive_contacts_same_height`, `_same_member` | deux Tours partageant deux contacts consécutifs : même `T`, puis même `β` (tangente lue directement, aucune branche) | FERMÉ |
| `distinct_heights_no_shared_consecutive_contacts` | deux Tours de hauteurs distinctes (ON comprises) ne partagent jamais deux contacts consécutifs | FERMÉ |
| `contact_eq_line_iff_onLine` (B, forme exacte) | un contact de l'arrivée = contact de ligne de sa hauteur ⟺ arrivée ON | FERMÉ, caractérisation du but |
| `grammar_contacts_admit_any_radial` | toute `β ∈ ]0, 1/2]` satisfait les obligations de contact connues (= `parameter_grid_admissible`) | FERMÉ |

Portée. A est une identité vraie pour la famille authentique telle qu'elle est, sans hypothèse radiale : c'est l'unique entrée des poids
exacts `Λ(p) = log p` dans la famille des zéros, et elle ne borne rien. « Les contacts doivent être les mêmes » est impossible entre
zéros distincts (texte collé §2 confirmé par théorème). B sous sa forme « condition de contact ou de phase » est une caractérisation du but
`radialFactor = 1` : la grammaire ne l'impose pas (contre-modèle `β = 1/4` sur toutes les obligations de contact). Sonde hors build
`experiments/e304_grammatical_raccord_probe/ProbeE304_GrammaticalRaccord.lean` (hypothèses de `:399` ; A, complément forcé sur le paquet de
hauteur de l'arrivée, B exact, contacts partagés, admissibilité en contexte) : but `radialFactor ⟨p.zLaterMember, hL⟩ = 1` inchangé ;
contrôle TDD : la condition de ligne sur UN contact en hypothèse ferme le corps.

Réponse au message de l'auteur (« si les contacts doivent être les mêmes et que la progression ne peut pas être la même, ce n'est pas une
reformulation de RH et le but 399 peut être changé pour ces deux éléments ») : les deux éléments sont compilés et chacun est une réécriture
du but, non un autre but : (1) contacts de l'arrivée = contacts de ligne ⟺ `radialFactor = 1` (`contact_eq_line_iff_onLine`) ; (2) le
passage parti du ON ne change que la hauteur ⟺ arrivée ON (`heightOnly_step`, `vertical_arrival_onLine_iff_fibre_singleton`). Quantifiés sur
les passages d'historique ON, l'un et l'autre sont ⟺ RH (`riemannHypothesis_iff_no_first_regime_break`). Le but `:399` n'est pas modifié.
Reste à faire : une inégalité DÉMONTRÉE sur les poids exacts, fausse dans `ζ(s−δ)ζ(s+δ)`, bornant le complément au saut d'exposant
`< 1 − β_l`. Build réexécuté : EXIT=1, une erreur (`:399`), signature 643740d74406 inchangée.

Seconde livraison E304 (même jour, instruction de l'auteur : « réintègre la sonde dans la ligne principale avec tous les théorèmes ;
réduis au maximum le but 399 à quelque chose qui n'équivaut pas à RH ») : sonde supprimée, tous ses théorèmes composés dans
`radial_conservation_anchored` (`hIdxPos`, `hJumpA`, `hContactIff`, `hShared`, `hNoShared`, `hAdmit`) ; dernier pas remplacé : théorème A
à l'occurrence `Occ(l)` + découpage paquet de hauteur / complément ⟹ `ΔL_S = J − ΔL_{Sᶜ}` ⟹ `‖ΔL_S‖ ≤ ‖J‖ + ‖ΔL_{Sᶜ}‖` (`hForcedOcc`,
`hTriangle`) ; `suffices` : séparation stricte `‖J‖ + ‖ΔL_{Sᶜ}‖ < ‖ΔL_S‖` à ce seul événement. But `:400`, signature 29bba26d88ce.
Nature : condition SUFFISANTE, un passage, un premier, non ⟺ RH ; non dérivée ; vérité inconnue (une compensation déterminée du complément à
un point n'est pas exclue : E184, E186, E221, E301). La règle du 2026-10-12 (§58, « ne plus imposer une voie suffisante comme dernier pas »)
est levée par cette instruction ; l'ancien dernier pas (`refine absurd ?_ (ne_of_gt hLambda)`) reste dans l'historique git. Texte de
l'auteur (zéros déterminés par ζ, contributions et premiers déterminés, formule explicite = identité, annulations déterminées ;
fermeture = incompatibilité avec une propriété indépendante de la grammaire, jamais par OFF fabriqués) : conforme au compilé ; la
propriété indépendante manquante est la borne du complément à l'événement `Occ(l)`, strictement sous l'excès de la paire miroir.


## 84. Raccords fixés par les deux bornes de chaque écart premier, E305 (2026-10-15)

Énoncé de l'auteur : contribution d'un zéro à `[p_n, p_{n+1}]` fixée par les deux bornes, tous les intervalles soumis simultanément aux
mêmes lois ; « zéros authentiques et contributions fixes + grammaire exacte des écarts ⟹ raccords obligatoires non déplaçables ».
Lean : `Terminal/FixedGapRaccords.lean` (16 théorèmes, 5 objets, axiomes standard, importé ; chaîne non modifiée) : primitive aux deux
bornes, télescopage, détermination d'un point de quadrant ouvert par ses contributions sur les seuls écarts premiers au-delà de tout rang
(`prime_gap_contributions_determine_point` ; ferme la lacune signalée par E301 dans `local_contribution_rigidity`), déplacement radial lu au-
delà de tout rang, validité pour toute `β > 0` (`exists_offline_point_with_fixed_raccords`), lecture de ligne ⟺ ON (caractérisation),
`NoMixedHeight` écrite (impliquée par RH, non dérivée), profil d'une arrivée basse sans contradiction (`low_arrival_fixed_raccords_profile`).
E305 (`experiments/E305_FixedGapRaccords/`) : protocole sans biais déclaré (aucune insertion ni remplacement, aucune normalisation, OFF
authentiques de Davenport–Heilbronn à leur propre hauteur, reconstruction aveugle) ; T1, T2, T4 PASS ; T3 FAIL déclaré (grille de départ
trop courte pour ζ n°100), amendement T3b PASS 12/12 (≤ 2e−13) ; T5 dominance du premier ON en enveloppe sur 100 % des écarts, contribution
réelle la plus grande sur 65,6 % ; T6 hauteurs OFF de Davenport–Heilbronn distinctes de toute hauteur ON (1,47–1,95), non transféré à ζ.
Liste des hypothèses avec statut : bloc ÉTAT (`main_build_state.md`). Verdict : la proposition encadrée est vraie et compilée ; elle
identifie, elle ne contraint pas `β`. Build : EXIT=1, une erreur (`:400`), signature 29bba26d88ce.


## 85. Rigidité radiale depuis les seuls premiers, E308 (2026-10-15)

Correction de la chaîne : la séparation stricte `‖J‖ + ‖ΔL_{Sᶜ}‖ < ‖ΔL_S‖` posée à E304 comme dernier pas (§83) était FAUSSE dans son
contexte : l'identité `ΔL_S + ΔL_{Sᶜ} = J` qui la motivait impose `‖ΔL_S‖ ≤ ‖J‖ + ‖ΔL_{Sᶜ}‖` (`hTriangle`). Le but `:400` équivalait donc à
`False` ; « vérité inconnue » (§83) est retiré. Sous-but supprimé, réfutation gardée en contexte (`hSepRefuted`), but `⊢ False` (`:401`).
Lean : `Terminal/PrimeOnlyRadialRigidity.lean` (8 théorèmes, axiomes standard, importé) : `strict_separation_impossible(_sub)`,
`rigidity_does_not_equalize_radial`, `fixedRaccords_any_assignment` (la rigidité E305 identifie, n'égalise pas), `proportional_profiles_iff`
(loi d'échelle commune ⟺ exposant commun), `critical_envelope_law`, `common_exponent_ratio`, `radial_conservation_law_iff_riemannHypothesis`
(sous l'ancre, loi ⟺ RH). E307 cité par le prompt de l'auteur est absent du dépôt (aucun fichier, aucun commit) ; E308 le reproduit.
E308 (`experiments/E308_PrimeOnlyRadialRigidity/`) : détection depuis les seuls premiers (spectre de `Λ(n) n^{−σ}` moins le pôle, quatre
`σ`), 13 fréquences communes = hauteurs des 13 premiers zéros à 0,01 près (X = 1e5, 1e6, 1e7) ; ajustements A (exposants libres),
B (exposant commun), C (`β = 1/2`) ; E308 pondéré par `e^{−u}` dominé par les petites abscisses (déclaré) ; amendement E308b (pondérations
`x^{−θ}`, θ = 1/2, 3/4, 1, fenêtres `[X/1000, X/10]`, prédiction `[X/10, X]`) : `β₁ ∈ [0,488 ; 0,528]` (écart-type d'ajustement
0,005–0,008), exposant commun B ∈ [0,478 ; 0,522], C jamais plus mauvais que B hors échantillon à 0,01 près ; modes élevés de A instables
(β de 0 à 1) par troncature. Observations ; aucune ne borne un zéro au-delà des 13 modes. Chaîne : la première implication non démontrée
reste la conservation au premier changement supposé de régime (⟺ RH sous l'ancre). RH_FOUND=FALSE.

## 86. Argument de l'auteur sur l'amplitude des premiers, réduction du but (2026-10-15)

Argument de l'auteur, écrit tel quel dans `radial_conservation_anchored` (aucune définition ni RH modifiée, aucun module ajouté) :
premiers, poids et grammaire immuables ; reproduction exacte (`smoothedRemainder_eq_tsum_residueTerm`) ; vrais zéros = points fixes
(`replacement_not_reconstruct`) ; l'amplitude de la courbe des premiers borne la partie réelle de chaque zéro et de son miroir
(`radial_le_of_remainder_growth`) ; premier zéro ON (`anchor_canonical_one`) ; contrainte grammaticale de l'amplitude démontrée à
l'échelle linéaire (`smoothedRemainder_linear_growth`). Réduction sur instruction de l'auteur : `suffices` l'amplitude de la courbe
des premiers est celle de la ligne ; le miroir de l'arrivée basse la contredit (fermé). But affiché à `:402` : `∃ C, ∀ x > 1,
‖smoothedRemainder x‖ ≤ C·x^{1/2}`, écrit avec les seuls premiers, sans zéro. Portée : condition suffisante, équivalente à RH
(`riemannHypothesis_iff_remainder_sqrt_growth`) ; exposant 1 seul démontré ; non réfuté par le contexte. Écart unique : de
l'échelle linéaire à l'échelle de la racine carrée depuis les poids exacts. Signature 74296e1185c1. Demande suivante de l'auteur :
reprendre l'étude de synchronisation sans aucun OFF placé à la hauteur d'un ON. RH_FOUND=FALSE.

## 87. Synchronisation écart par écart refaite sans OFF à la hauteur d'un ON, E309 (2026-10-15)

`experiments/E309_PerGapSynchronizationDistinctHeights/` (35 PASS, 1 FAIL déclaré ; aucun Lean modifié). Signal exact du canal J,
demande des premiers sur chaque écart et à chaque saut, `x ≤ 1000` et `x ≤ 10 000`. Famille authentique (5000 zéros ON) : aucun écart
ni saut hors de l'échelle de troncature (0/168, 0/1229). Configurations fabriquées, toutes à des hauteurs distinctes de ζ (insertion
ON, insertion de paire OFF, déplacement du premier zéro), sans compensation : défaut non nul sur chaque écart ; visible au-delà de la
troncature sur 6 à 61 écarts (`x ≤ 1000`) ; un ON fabriqué rate comme un OFF fabriqué. Conforme au compilé (synchronisation locale
exacte, insertion et remplacement exclus). Remarque de l'auteur : l'OFF devrait se placer entre le premier et le deuxième zéro.
Compilé : tout zéro de hauteur au plus 28 est ON, donc cette région ne contient aucun OFF. « OFF jamais à la hauteur d'un ON » est appliqué
comme règle de protocole, ce n'est pas un théorème (fibre mixte non exclue). FAIL déclaré : décroissance du résidu médian avec N sur
`x ≤ 10 000`. Inventaire des expériences antérieures à OFF de même hauteur : `e309_inventaire_off_meme_hauteur.csv`, retirées comme
preuves. RH_FOUND=FALSE.

## 88. But restreint à l'amplitude du miroir de l'arrivée (2026-10-15)

Revue de l'auteur (« ce n'est pas le but dont nous avions parlé, il était plus restreint ») : la réduction du §86 demandait la borne
en `√x` du reste (⟺ RH), plus que nécessaire. Remplacée par `suffices ∃ θ < 1 − β_l, ∃ C, ∀ x > 1, ‖smoothedRemainder x‖ ≤ C·x^θ` :
amplitude de la courbe des premiers sous celle du miroir de l'arrivée basse, fermeture par `radial_le_of_remainder_growth` appliqué
au miroir. Strictement plus faible que `√x` ; équivaut à une bande sans zéro au-dessus de `θ` contenant le miroir ; exposant 1 seul
démontré. Signature 1060775ff1e6. RH_FOUND=FALSE.

## 89. Refus du but d'amplitude, portage de zeta23, trois points de l'auteur (2026-10-15)

Refus de l'auteur : aucun but équivalent à RH ; le sous-but d'amplitude (§86, §88) est retiré, son implication reste en contexte
(`hAmpCloses`, reste brut, sans normalisation). zeta23 porté (`RHV6Fresh/Zeta23Port/`, anthropics/formal-math@fbdc36bb, clôtures de
`Zeta23.Final` et `Zeta23.FinalMult`, 134 fichiers ; 278 déclarations PNT+ en double retirées au profit de
`RHV3Lean.Objects.PerronPort` ; `EulerMaclaurin` converti hors système de modules) : `hTwoThirds`, `hTwoThirdsSimple` en contexte.
Réduction en trois points de l'auteur : (1) premier zéro ON avec amplitude et fréquence, fermé (`hPoint1`) ; (2) même point exclu
(`hPlace`), aucun OFF sous 28 (`hBelow28`), « aucun OFF à la hauteur d'un ON » ouvert (`case point2_sameHeight`) ; (3) « un ON à la
hauteur de l'arrivée » ouvert (`case point3_frequencyTaken`) ; (2) ∧ (3) ⟹ contradiction, fermé. Objection de l'auteur : « le ON
progresse uniquement par la hauteur » ; compilé : `engaged_regime_kept` (le passage suivant monte, aucune conclusion radiale),
`engaged_passage_height_only` (exige les deux miroirs annulés : arrivée ON en hypothèse) ; leur combinaison suppose la conclusion.
Signature 72a8636dcda1. RH_FOUND=FALSE.

## 90. Un seul point (2026-10-15)

Sur instruction de l'auteur (« un seul suffit »), les deux cas du §89 sont fusionnés : `suffices ∀ w, T_w = T_l → β_w = 1/2` (à la
hauteur du zéro suivant, tout zéro est ON), fermeture par le zéro suivant lui-même. Côté haut, premier zéro et régime engagé déjà
acquis. Ce point contient l'énoncé « le zéro suivant est ON » ; pris à chaque passage il donne RH. Lock réécrit. Signature de065067c2d2. RH_FOUND=FALSE.
