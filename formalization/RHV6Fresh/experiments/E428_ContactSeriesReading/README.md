# E428 — Lecture des transitions par la progression complète des contacts sur une série d'écarts, raccord individuel–collectif et information radiale du miroir (pré-enregistrée 2026-11-04)

Plan : §19.42 (proposition), §19.42.5 (obligations A–D de l'auteur), §19.42.6 (quatre corrections de l'auteur,
feu vert conditionnel). Directives : série d'écarts, jamais un écart isolé ; ne pas réduire l'étude à la seule
fréquence ; aucune hypothèse OFF, aucune borne posée, aucune contradiction anticipée ; les premiers ne servent qu'à
valider après coup ; prédictions compilées avant mesure ; jumeau déterministe ; critères fixés ici, non modifiés après.

Module Lean de référence, compilé AVANT exécution : `Terminal/ContactSeriesReading.lean` (isolé, non ajouté à
`RHV6Fresh.lean` ; aucun `sorry` ; deux tentatives au plus, chacune journalisée `logs/lean_attempt{1,2}.log`).

## Objets réutilisés (jamais reconstruits)
`cellIndexAt`, `stagePosition`, `cellIndexAt_eq_ceil` (CellRestitution, FirstExceedanceRaccord) ; `contactAt`,
`contactAt_ratio`, `accumulationFrom`, `contact_accumulation_eq_endpoint_difference` (ContactValueGeometry) ;
`contactRealValue` (ContactRealValue) ; `truncatedStep`, `truncatedStep_eq`, `lowFrequencies`, `integratedTowerTerm`,
`reconstructedVonMangoldt_eq_limit_contact_accumulation` (RawEventReconstruction) ; `complexMode`, `mirrorMode_add`,
`mirrorMode_sub`, `mirrorMode_add_norm`, `mirrorMode_add_norm_ge` (HarmonicRestoringLaw) ;
`inversion_from_consecutive_contacts` (JointParameterReading) ; `transitionOf_cls`, `eventOrientation_of_gap`
(TransitionRigidity, GrammarContactStability) ; `logRatio_not_determined_by_transition` (GrammarContactStability).

## Prédictions compilées que la mesure doit retrouver (énoncés du module)
* **A0** `truncatedStep_eq_sum_individual` : pas tronqué = fond + somme finie (sur `lowFrequencies H`) des
  contributions individuelles ; `individual_contribution_eq_own_contact_accumulation` : chaque contribution est
  l'accumulation de sa propre Tour sur ses propres contacts, quels que soient `(β, T, k₀, n)` ;
  `collective_eq_individual_add_rest` : collectif = une Tour + le reste (garde-fou : jamais une Tour seule) ;
  `reconstructedVonMangoldt_eq_limit_of_individual_sums` : la limite en `H` de ces sommes est `Λ̂(N)` (même
  troncature, même lissage, même limite que le théorème compilé).
* **A1** `seriesShift_telescopes` : les décalages d'indices consécutifs d'une série se somment en le décalage total.
* **A2** `cellIndex_difference_bounds` : `|Δk − T·log(q'/q)/π| < 1` pour tout `(β, T > 0)` ;
  `log_ratio_bracket` : `|log(q'/q) − hΔk| < h`, `h = π/T`.
* **A3 corrigé** `estimate_brackets` : `q̂e^{−h} < q < q̂e^{h}` ; `certified_rounding` : `q̂(e^h − 1) < ½ ⟹ |q − q̂| < ½` ;
  `certified_unique_integer` : un seul entier à moins de ½ de `q̂`. La certification ne lit que `(p, T, Δk)`.
  `old_threshold_not_certifying` : contre-exemple où `q(e^h − 1) < ½` mais `q̂(e^h − 1) ≥ ½` (ancien seuil du plan).
* **A4** `mirror_series_amplitude_difference` : sur une série, amplitude du miroir − amplitude de la Tour =
  `(1 − 2β)·log(q/p)`, nulle ⟺ `β = ½` (identité ; aucune loi posée).
* **C corrigé** `mirror_contact_log_ratio` : `log(C_k(β)/C_k(1−β)) = (φ_β − φ_{1−β})/T` ;
  `mirrorPhaseShift_eq_zero_iff` : nul ⟺ `β = ½` ; `mirror_stagePosition_difference` : constante en `q` ;
  `mirror_series_shift_difference_le_one` : les différences d'indices de la Tour et du miroir sur une même série
  diffèrent d'au plus une unité (à vérifier en mesure, jamais présumées égales) ;
  `mirrorMode_sub_norm` : `‖v₊ − v₋‖ = 2|sinh(dt)|` (pas de plancher : la minoration ≥ 2 ne porte que sur la somme).

## Données
Zéros `experiments/data/odlyzko_zeros6_2001052.txt` (SHA-256 vérifiée par `contact_common.load_zeros`) ; premiers par
crible dans le script (entiers exacts) ; Tours authentiques des zéros de rangs 1, 10, 100, 1 000, 10 000, 100 000,
1 000 000, 2 001 052 (β = ½) ; Tours de séparation : mêmes hauteurs, β ∈ {0,3 ; 0,7} (synthétiques, toujours en paire
miroir, jamais aux hauteurs d'un autre zéro réel).

## E428(a) — lecture certifiée par série (`scripts/e428a_series_reading.py`)
Ancrages r ∈ {2, 100, 1000} (p_r = 5, 541, 7 919) ; séries m ∈ {12, 120, 1200} ; toutes les Tours ci-dessus.
Pour chaque (Tour, r, m) et chaque j ≤ m : Δk_j = k(p_{r+j}) − k(p_r) lu dans la Tour ; `q̂_j = p_r·exp(πΔk_j/T)` ;
certification `q̂_j(e^h − 1) < ½` ; entier lu = arrondi de `q̂_j` ; mot de transitions de la série lue (classe mod 6 des
écarts lus, orientation). Validation après : comparaison aux vrais premiers et au vrai mot.
Critères : (i) **0 lecture certifiée fausse** (réfutation d'un énoncé compilé sinon : erreur à localiser) ;
(ii) nombre de lectures certifiées, nombre de lectures exactes non certifiées (consignées, jamais revendiquées) ;
(iii) comparaison ancien seuil / seuil corrigé : nombre de cas où l'ancien certifierait à tort ;
(iv) à même hauteur, β = 0,3 / 0,5 / 0,7 : fraction des Δk_j distincts (information radiale des indices, obligation C) ;
le mot lu certifié est attendu identique (il est fonction du premier lu, unique) même quand Δk diffère.
Jumeau : mpmath 30 chiffres, Tour du zéro 1 et du zéro 2 001 052, ancrage 2, j ≤ 12.

## E428(b) — miroir, raccord individuel–collectif, recherche d'une loi sur série (`scripts/e428b_mirror_series.py`)
Événements r = 2..2001 (5 ≤ p ≤ 17 393), mêmes Tours en paires (β, 1 − β).
1. **C** : décalage de phase `(φ_β − φ_{1−β})/π` ; indices absolus Tour/miroir à chaque p (fraction d'inégalité,
   différence ∈ {⌊s⌋, ⌈s⌉} où s = décalage/π) ; différences sur séries depuis chaque ancrage : écart Tour/miroir
   dans {−1, 0, +1} (0 violation attendue), fraction non nulle (mesure) ; log-rapport des contacts contre la formule ;
   norme de la somme miroir `2cosh(dt)` et de la différence `2|sinh(dt)|` aux abscisses `t = log p` (identités).
2. **A0** : pour N ∈ {5, 7, 11, 101, 1009}, H = 1 000 : pas collectif tronqué (somme sur les zéros de hauteur ≤ H) contre
   somme des contributions individuelles (identité, écart attendu ≤ 10⁻¹⁰ relatif) ; contribution d'une Tour seule
   contre le collectif (jamais égale : garde-fou).
3. **A4, recherche d'une loi** : fenêtres glissantes de 12 événements (1 989 fenêtres, mots de 12 transitions) ;
   candidats sur la série : amplitude totale `β·log(p_{fin}/p_début)`, somme des valeurs signées aux contacts de
   rencontre, somme orientée pondérée, nombre d'écarts Tour/miroir d'indices non nuls dans la fenêtre, différence
   d'amplitude Tour/miroir. Critère pré-enregistré d'une loi : à mot identique (fenêtres partageant le même mot de 12
   transitions, groupes d'au moins 2 fenêtres), étendue du candidat ≤ 10⁻⁹ pour tous les groupes. Attendu (compilé
   `logRatio_not_determined_by_transition`) : aucun candidat de longueur ne le satisfait ; le candidat « écarts
   d'indices Tour/miroir » est mesuré sans attente.
Jumeau : mpmath 30 chiffres sur 10 événements pour la paire (0,3 ; 0,7) à la hauteur du zéro 1.

## Verdict en trois niveaux (critères fixés)
* **A0 / A1–A3** : réussi ⟺ énoncés compilés et 0 lecture certifiée fausse ; sinon erreur consignée.
* **C** : réussi ⟺ 0 violation de l'écart {−1, 0, +1} ; la fraction non nulle est l'information radiale mesurée.
* **A4 / B** : une loi n'est déclarée que si le critère de mot est satisfait ; attendu : aucune pour les candidats
  de longueur ; résultat du candidat miroir consigné tel quel.
* **D** : non exécuté ici ; frontière inchangée sauf si A4 fournit une loi (alors seulement, étape suivante).
Aucun critère ne sera modifié après exécution. Résultats, y compris négatifs, dans `RESULTS.md`.
