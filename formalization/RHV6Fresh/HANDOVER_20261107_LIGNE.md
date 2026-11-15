# Hand-over pour la reprise du 2026-11-08 — RHV6Fresh, mécanisme de cassure sur la ligne

Rédigé le 2026-11-07 au soir, pour moi-même. Tout est commité et poussé sur `main` (voir le dernier commit du dépôt).

## 1. Ordres de l'auteur en vigueur (à relire avant d'écrire une ligne)
* **[LEVÉ pour le fil OFF le 2026-11-08, §8 ci-dessous]** **R-LIGNE (2026-11-07)** : tant qu'il reste du Lean à écrire, NE PAS CHERCHER LA CONTRADICTION. Maîtriser parfaitement le
  mécanisme de cassure depuis la ligne (zéros ON, `β = 1/2`) avant toute déduction sur les OFF. Aucune section « ce qui casse
  hors ligne », aucune « obligation ouverte » proposée de mon chef.
* **Obligation « amplitude ↔ variation de `rawDemand` » RETIRÉE** par l'auteur (§19.68, correction) : ne jamais y lier la
  contradiction OFF.
* **[LEVÉ par l'auteur le 2026-11-09, §19 ci-dessous et maître §19.91 — conservé pour l'historique]** **Ban spectral total** (§19.55/§19.67) : jamais `OffCarrier`, `smoothedRemainder`, `remainderExponent`, complément, `familyRe`,
  sommes de Tours, formule explicite, `CollectiveCurvature`. Grep avant tout commit :
  `grep -nE "smoothedRemainder|remainderExponent|OffCarrier|complement|familyRe|CollectiveCurvature" <module>`.
* **Troisième ordre (§19.63)** : les contacts lisent `β` ; une Tour a une fréquence ET une amplitude ; tout bilan signé utilise
  `contactRealValue`. Ne jamais écrire « aveugle à β » ni « ne dépend que de la fréquence ».
* Règles de travail inchangées : pré-enregistrer (commit) avant compilation et exécution ; grep des noms avant d'écrire ;
  module isolé non ajouté à `RHV6Fresh.lean` ; deux tentatives de compilation max sur le module définitif, sondes en
  `*_SCRATCH.lean` non versionné supprimé après capture, chaque sortie dans `attempts/` ; `lake build RHV6Fresh` vert ; jumeau
  déterministe pour tout chiffre ; rapports à l'auteur en mots français, sans formule ; commit + push directs.

## 2. Où en est la chaîne (ligne seulement)
Fil E436 → E447, tous compilés, objets : une Tour, ses contacts `C_k`, ses cellules, ses valeurs `v_k = (−1)^k C_k^β/‖(β,T)‖`,
la demande brute `rawDemand = ψ − id`, les premiers et leurs poids.
* E436–E438 : découpage d'un écart par les contacts (restes partiels), la cassure `log p` toujours dans la dernière pièce.
* E439–E443 : signe de la cellule de rencontre, bilans signés, série des rencontres, seuils.
* E444–E445 : bilan pondéré par la valeur au contact ; prix de rencontre.
* E446 (§19.68, `MeetingRegimeFinite.lean`) : le régime « un premier par cellule de rencontre » est FINI pour toute Tour (PNT
  porté) ; budget exact d'une cellule = sa longueur ; pas d'une Tour `o(cellule)` ; P6 non discriminant.
* **E447 (§19.69, `BreakMechanismOnLine.lean`, 17 déclarations, vert tentative 1, verdict A)** :
  - `demandAtContact`, `cellDemand_telescope` ;
  - `valueCellSum_abel`, `valueCellSum_abel_signed` : `Σ v_i D_i = v_M R_M − v_0 R_0 + (1+e^{βπ/T}) Σ v_i R_{i+1}` ;
  - `line_contactRealValue_sq`, `line_value_sq_succ`, `line_value_sq_ratio_eq_length_ratio` ;
  - `contact_of_fraction`, `line_break_amplitude_exact` (`|v_{k(x)}| = √x·e^{−πf/(2T)}/‖(1/2,T)‖`), `line_break_amplitude_bounds`,
    `line_break_price_bounds` ;
  - `rawDemand_prime_from_contact`, `break_then_descent` (hypothèse STRICTE `C_k < q`) ;
  - `rawDemand_div_tendsto_zero`, `demandAtContact_div_tendsto_zero`, `line_weighted_demand_at_contact_small`.

## 3. Pièges rencontrés aujourd'hui (pour ne pas les repayer)
* `contactRealValue_succ` existe déjà (`ContactRealValue.lean`, hypothèse `T ≠ 0`) : passer `hT.ne'`.
* `sum_range_succ` NON qualifié se résout vers un autre lemme dans ce corpus : écrire `Finset.sum_range_succ`.
* Limites composées : après `Tendsto.congr`, faire `simp only [Function.comp_apply]` avant toute réécriture d'`abs`.
* `Nat.floor_lt (ha : 0 ≤ a) : ⌊a⌋₊ < n ↔ a < n` ; `abs_neg_one_zpow` ; `Real.rpow_natCast` + `Real.rpow_mul` pour `(x^{1/2})² = x`.
* Scripts : ne pas nommer le `Logger` `log` dans un script mpmath (masque `mpmath.log`).
* Convention des expériences : zéros via `E414_ContactValueAccumulation/scripts/contact_common.py`, rangs
  `[1,10,100,1000,10000,100000,2000000]`, premiers ≤ 10⁷ (numpy), jumeau mpmath 30 chiffres, logs copiés en `_log.txt`.

## 4. Candidats pour demain (ligne seulement ; AUCUN n'est engagé, l'auteur tranche)
C1. **Bilan d'Abel sur une série d'écarts entiers** : bords aux premiers (`p_n`, `p_{n+J}`) plutôt qu'aux contacts, en combinant
    `valueCellSum_abel` avec le découpage par contacts (`gap_demand_eq_pieces`, restes partiels) ; objectif : exprimer le budget
    pondéré d'une série d'écarts par les valeurs aux rencontres et la demande brute aux premiers (`rawDemand p = ψ(p) − p`).
C2. **Part des poids non premiers dans la cassure d'une cellule** : `cellNonPrimeWeight` borné par `ψ − θ` existe
    (`cellNonPrimeWeight_le_psi_sub_theta`, `_le_sqrt`) ; écrire la version pondérée par `v_k` et sa taille relative à `log q`.
C3. **Fraction de cellule `f` aux rencontres successives d'une même Tour** : `line_break_amplitude_exact` donne l'amplitude
    de paiement par `f` ; relier `f(p_{n+1}) − f(p_n)` à `T·log(p_{n+1}/p_n)/π` modulo 1 (règle de déplacement
    `displacement_rule` d'E442) : la suite des amplitudes de paiement d'une Tour de la ligne est déterminée par la suite des
    rapports de premiers consécutifs.
C4. **Télescopage pondéré sur la série des rencontres à grand `x`** : au-delà du rang fini d'E446, les cellules contiennent
    plusieurs premiers ; écrire le budget pondéré d'une cellule comme somme sur SES premiers avec le même `v_k` (identité
    `valuePrimeSum_eq_primes_in_block` restreinte à une cellule) et la descente `−v_k·cellLength`.
Dans tous les cas : pré-enregistrement §19.70 + `experiments/E448_*/README.md`, commit, sondes, module, build, expérience,
jumeau, RESULTS, mise à jour §19.70, mémoire, commit, push. Rapport en mots.

## 5. État des dépôts
* `zeta24-lean` : arbre propre après le commit de clôture ; `lake build RHV6Fresh` vert (9064 jobs).
* `NeuroSymbolicModel` : inchangé (aucun fichier Riemann n'y est écrit, règle du dépôt).
* Mémoire Claude (`-opt-NeuroSymbolicModel/memory/`) : fiches `feedback_master_break_on_line_first`,
  `feedback_no_amplitude_rawdemand_obligation`, `rhv6_break_mechanism_on_line_19_69` ajoutées, index à jour.

## 6. Prompt de redémarrage (à coller demain)
Voir la fin du rapport de clôture du 2026-11-07 ; copie ci-dessous.

> Reprends RHV6Fresh depuis `formalization/RHV6Fresh/HANDOVER_20261107_LIGNE.md`. Ordres en vigueur : R-LIGNE (pas de
> recherche de contradiction tant que du Lean reste à écrire ; maîtriser le mécanisme de cassure sur la ligne, zéros ON
> seulement), ban spectral total, troisième ordre (les contacts lisent β, fréquence ET amplitude), obligation « amplitude ↔
> variation de rawDemand » retirée. Poursuis le fil E447 (§19.69) : choisis parmi les candidats C1–C4 du hand-over (ou
> celui que j'indique), pré-enregistre §19.70 + E448 (commit avant compilation), grep des noms, sondes en SCRATCH, module isolé
> `Terminal/*.lean` en deux tentatives max, `lake build RHV6Fresh` vert, expérience bornée + jumeau mpmath, RESULTS, document
> maître, mémoire, commit et push sur main. Rapport en mots français, sans formule, sans conclusion sur les OFF.

## 7. État au soir du 2026-11-08 (ajout)
* **E448 (§19.70, `Terminal/BreakAmplitudeSequence.lean`, 17 déclarations, verdict A)** : candidat C3 exécuté — orbite de la
  fraction de cellule, amplitude de paiement × `e^{π/(2T)}` par cellule franchie, constance ⟺ même cellule, encadrement,
  télescopage. Candidats C1, C2, C4 restent non engagés.
* **Nouvelle priorité de l'auteur (2026-11-08)** : chemin inverse écarts → contacts → zéro. **E449 (§19.71,
  `Terminal/ContactsFromGapsInversion.lean`, 21 déclarations, vert tentative 1)** : formule tangentielle depuis deux contacts
  (`tower_of_two_contacts`), encadrement de la phase par chaque premier (`phase_bracket`), fréquence par la pente du mot
  (`word_slope_tendsto`), cause (`cellFraction_primes_small_and_near_one`, par `logGapsVanish_holds`), **le mot détermine la
  Tour** (`tower_eq_of_same_word`). Expérience : six zéros et trois contrôles non-zéros reconstruits pareillement ; `β` lu par
  la position seule n'est utilisable qu'à petite hauteur (`β = T/tan φ`, amplification par `T`) : la lecture exacte de `β`
  passe par l'amplitude (troisième ordre). H6 consignée : à cette étape rien ne distingue le mot d'un zéro.
* Pièges du jour : `push_neg` déprécié (écrire `push Not`) ; `tendsto_const_nhds` demande `(x := …)` dans un `.sub` ;
  `ring` après `field_simp` échoue souvent par « No goals ». Les avertissements de longueur de ligne sont ceux du corpus entier.
* Suite possible (à l'ordre de l'auteur) : ce que les AMPLITUDES (valeurs aux contacts, `contactRealValue`) ajoutent au mot
  pour lire `β` exactement depuis les cassures ; ou reprendre C1/C2/C4.

## 8. Passage aux OFF (soir du 2026-11-08, §19.72)
* **Décision de l'auteur** : connaissance préalable des cassures suffisante ; R-LIGNE levée pour le fil OFF. Stratégie et plan
  K0–K3 consignés au §19.72, avec la réserve en tête : rien de compilé ne dit ce qui fait d'une Tour un zéro (H6 d'E449,
  K0 d'E450), donc toute contradiction devra consommer la rencontre exacte (P1–P5) et le Théorème du Prix.
* **E450 (K0 + K1, `Terminal/PairBreakAtPrime.lean`, 12 déclarations, vert tentative 1, verdict A)** : amplitude exacte de la
  cassure pour tout `β`, deux mots décalés d'au plus une cellule (`mirror_cellFraction`, `mirror_word_difference_le_one`),
  produit de type ligne (`pair_break_product`), somme encadrée par le prix d'E445, rapport des membres `≈ p^{1−2β}` non
  borné (`pair_break_ratio_unbounded`). K0 : rien ne distingue les zéros des contrôles sur la ligne.
* **Prochaine étape : K2.** Interdits déjà établis : comparaison « amplitude contre budget » (T2 d'E445 : le budget cumulé
  domine le miroir ; E446 : la longueur de cellule domine toute amplitude `β < 1`) ; lien à « amplitude ↔ variation de
  rawDemand » (R-E446) ; absorption sur famille finie (§19.44) ; prémisse équivalente à RH (vérifier avant de poser).
  Piste K2 : la séparation non bornée des deux membres contre ce que la rencontre exacte impose aux deux au même premier.
* Piège du jour : `linarith` ne reconnaît pas `−a/π` comme `−(a/π)` ; `rw [neg_div] at h` d'abord.

## 9. Le chaînon « une Tour est un zéro » (soir du 2026-11-08, §19.73, E451)

* Ordre de l'auteur vérifié : la Tour est le terme `x^ρ/ρ` du point `ρ`, de poids l'ordre d'annulation de zêta en `ρ`
  (`zeroContribution_eq_mul_zeroTerm`, `rfl`) ; poids ≥ 1 en un zéro (`one_le_zeroMult`), **nul hors zéro**
  (`zeroMult_eq_zero_iff`, E451) ; contacts = points réels du terme (`zeroTerm_real_iff_ray`, `contactAt_eq_contactMinusAt`) ;
  miroir de même poids (`upperMirror_multiplicity`). « Remonter au calcul de zêta » = ordre d'annulation au point, pas une somme.
* Le ban spectral porte sur l'usage et la citation ; la clôture d'imports de `PairBreakAtPrime` (259 modules) contient déjà
  `OffCarrier`, `ExplicitFormulaLink`, `ZetaReflect` : aucun import nouveau n'a été nécessaire.
* `Terminal/PairBreakOfZero.lean` (isolé, 14 déclarations, tentative 1 verte) : objets d'E450 au paramètre d'un zéro vrai =
  module du terme × facteur de cellule ; produit des modules `x/(‖ρ‖‖ρ*‖)` ; rapport `x^{2β−1}‖ρ*‖/‖ρ‖` non borné.
* E451 (a) : le calcul de zêta (mpmath) sépare les six Tours de K0 (|ζ| ~ 10⁻¹⁰) des trois contrôles (|ζ| > 1) ; (b) 24 cas,
  identités à 10⁻¹⁵. Verdict A.
* Prochaine étape : K2b (ce que la rencontre exacte impose aux deux termes de même poids au même premier), à pré-enregistrer
  après vérification de non-équivalence avec RH ; pas de « amplitude contre budget » ; pas de somme de Tours.
* Pièges : ouvrir `RHV3Lean` pour `rZeroRadialPosition`, `rZeroHeight`, `nZeroMultiplicity`, `cZeroContribution` (qui vit
  dans `rhv3_lean`, pas `RHV2Fresh`) ; `Real.rpow_sub` réécrit la première occurrence : la cibler par `conv_rhs`.

## 10. K2b : ce que la rencontre impose aux deux termes au même premier (soir du 2026-11-08, §19.74, E452)
* Direction validée par l'auteur ; vérification de non-équivalence consignée AVANT pré-enregistrement (§19.74.2) : K2b ne
  pose aucune hypothèse, tous ses énoncés valent pour toute `β` ; il fixe une forme, pas une contradiction.
* `Terminal/PairMeetingImposition.lean` (isolé, 23 déclarations, tentative 1 verte, 0 avertissement) : `mirrorWordShift`,
  mot exact du miroir, fenêtre de même mot fixée par `β`, même signe ⟺ même mot, `|v + v*| = | |v| + (−1)^s |v*| |`,
  non-compensation au-delà d'un rang (points, rencontres, zéro vrai), poids commun amplificateur, ligne `2v`.
* E452 : 24 couples × 10⁵ premiers, 0 violation ; jumeau mpmath 240 cas, 0 violation ; part des mots décalés ≈ `|δ|/π`
  (observation, aucune loi posée). Verdict A.
* Suite : K3 (inversion de la paire contre E449) ; forme à vérifier pour non-équivalence avec RH avant pré-enregistrement.
* Pièges Lean : `| |a| + b |` ne se parse pas (écrire `abs (…)`) ; `(−1)^(1:ℤ) = −1` (le cas `s = 1` est le cas décalé,
  pas le cas commun) ; nommer `(T := T)` quand `pair_value_sum_ge` ne peut inférer `T`.

## 11. K3 : l'inversion d'E449 appliquée au mot du miroir (soir du 2026-11-08, §19.75, E453)

* Direction validée par l'auteur (« continues avec K3 »). Non-équivalence avec RH vérifiée et consignée AVANT le
  pré-enregistrement (§19.75.2) : aucune hypothèse, théorèmes pour toute `β ∈ (0,1)` ; le risque « unicité de la rencontre »
  (§19.72) évité, seul E449 L5 est utilisé. Réponse attendue consignée d'avance, puis compilée.
* Module isolé `Terminal/PairWordInversion.lean` (imports `PairMeetingImposition` + `ContactsFromGapsInversion`), 12
  déclarations, tentative 1 verte, 0 avertissement, axiomes standards, build complet vert. Pièges : `rw [div_add_div …]` ne
  trouve pas son motif après `abs_le` → écrire d'abord l'identité close `k/log x − T/π = −(φ + πf)/(π log x)` puis `abs_div`,
  `abs_add_le` ; pour « au-delà de tout rang » composer E449 L4 avec `tendsto_add_atTop_nat N` et `Nat.add_right_comm`.
* Expériences : encadrement de la pente 0 violation (24 × 664 579), polygone d'E449 sur le mot du miroir contient le vrai
  point (24/24), mots identiques sur la ligne, distincts hors ligne (comptes croissants par décade) ; l'inversion tangentielle
  en doubles est MAL CONDITIONNÉE aux hautes fréquences (erreur ≈ `T·log p·ε`, 3,7 au rang 10⁵) ; contrôle post-hoc à 60
  chiffres : `3,5·10⁻⁴⁵`. Trois critères pré-écrits violés et expliqués → verdict B. Leçon : ne jamais pré-écrire un seuil
  absolu sur `β = T/tan φ` en doubles ; pré-écrire le jumeau à ≥ 60 chiffres pour les rangs ≥ 10³ ; ne pas écrire « > 0 par
  décade » pour une propriété « au-delà de tout rang » sans taux.
* Réponse : deux Tours lisibles, le mot du miroir est fonction du mot de la Tour, AUCUNE contradiction. Plan K0–K3 fermé
  sans hypothèse de contradiction ; décision à l'auteur.

### 11bis. Rectification de l'auteur : l'arrivée est au plus à un demi (soir du 2026-11-08, §19.76)

* L'auteur récuse « théorème pour toute `β ∈ (0,1)` » comme plage de K2b/K3 : le régime certifié démarre à ON et `β > 1/2`
  est exclu pour une arrivée. Vérifié : `passage_entry_radial_le_half` (ordre seul, sans hypothèse), `first_passage_no_shared_frequency`,
  `later_le_half_of_history_onLine`, `arrival_onLine_or_low`. **Ne plus écrire « pour toute β entre zéro et un » comme
  plage de la route OFF** : l'objet est l'arrivée, `β ≤ 1/2` ; « hors ligne » se lit `β < 1/2` ; le miroir porte `1−β > 1/2`.
* Section L7 de `PairWordInversion.lean` (5 énoncés, tentative 2 verte) : `arrival_pair_words_dichotomy` est la forme à citer.
* Piège : rien n'empêche d'énoncer les théorèmes sur `(0,1)`, mais le texte doit nommer la plage utile, sinon il suggère un
  cas `β > 1/2` à traiter qui n'existe pas pour une arrivée.


## 12. K4 : la paire lue comme passage depuis l'arrivée basse (soir du 2026-11-08, §19.77, E454)

* Feu vert de l'auteur après K3. Texte externe (« modèle de causalité complet ») audité en §19.77.1 : rien ajouté (étapes 5–6 =
  cases 5–6 du schéma §19.58, prémisse « reste ON borné » circulaire §19.21, vocabulaire spectral interdit) ; une rectification
  de §19.58 : « amplitude relative constante aux rencontres ⟺ ligne » EST compilée (MeetingPoint §9) mais comme lecture.
* Non-équivalence vérifiée AVANT pré-enregistrement (§19.77.3) : aucune hypothèse ; conditions = cas sur un passage donné.
* Module isolé `Terminal/PairArrivalPassage.lean` (import `PairWordInversion`), 12 déclarations, tentative 1 verte, 0
  avertissement, axiomes standards, build complet vert. Forme compilée du passage OFF : arrivée hors ligne basse ; passage de
  sortie gelé, plus à droite, borné par le miroir ; arrivée = membre faible ; même pente de mot ; tout passage gelé a un membre
  bas à sa hauteur ; dichotomie sous historique ON. `low_entry_not_expected` : un membre d'entrée bas contredit la prémisse
  unique (⟺ RH). AUCUNE contradiction ; décision à l'auteur.
* Pièges : `passage_height_le` existe déjà (InterTowerExcess) — grep avant d'écrire ; les axiomes se lisent sur les lignes
  `info: …PairArrivalPassage.lean…depends on axioms`, pas en début de ligne ; `tendsto_rpow_neg_atTop` puis `funext; congr 1; ring`
  pour passer de `x^(−y)` à `x^(2β−1)`.

## 13. K5 : la fibre de l'arrivée basse, en fréquence seule (soir du 2026-11-08, §19.78, E455)

* Question de l'auteur : « les fréquences des OFF sont forcément différentes de celles des ON ; un OFF ne peut prendre la hauteur
  d'un ON occupée ni atteindre le prochain ON » ; remarque : trop d'amplitudes dans K4.
* Audit §19.78.2 : (a) compilé vers le bas (historique), OUVERT vers le haut = `NoMixedHeight` (FixedGapRaccords, ⟸ RH) ;
  (b) compilé par l'ordre (`consecutive_no_height_between`, `frequency_never_decreases`) ; (c) compilé comme répétition de
  fréquence, pas comme valeur différente (bornes de rang aveugles au radial, §19.15).
* Module isolé `Terminal/LowArrivalFrequencyFibre.lean`, 6 décl. M1–M6, verte à la première tentative, aucune amplitude.
  Point neuf : le côté du successeur d'une entrée basse décide de la fibre mixte (M2–M4).
* Pièges : M1 n'a pas besoin de l'hypothèse basse (linter) ; `NoMixedHeight` est une `def` Prop, s'applique directement
  `h l w hw.symm hOn`.
* AUCUNE contradiction ; décision à l'auteur.

## 14. K6 : le décalage des contacts à même hauteur, audit du texte « modulo 6 », causalité ON/OFF (soir du 2026-11-08, §19.79, E456)
* Questions de l'auteur : « si on affecte β, T en souffre » à même hauteur visée ; « les OFF nécessaires aux grandes hauteurs pour la
  cassure » ; texte collé sur les transitions mod 6 ; « la distribution est-elle gaussienne ? ».
* Compilé (`Terminal/SameHeightContactShift.lean`, isolé, M0–M5) : aucun contact partagé à même hauteur ; rencontre commune ⟹ hauteurs
  différentes ; décalage < demi-cellule ; pas aveugle à β. La phrase « hautes fréquences ⟹ cassure » vient du canal interdit (E404/E408) ;
  sa forme autorisée est `log_ratio_ge_cell_of_meeting` + `two_consecutive_contacts_finite`, pour toute Tour.
* Mesuré : effectifs du texte exacts sur 5 000 écarts mais cadre faux ; archétypes faux ; pas gaussien à douze (binomiale biaisée,
  sous-dispersée) ; β ne change que la phase (Jaccard 0,992), T change tout (0,24) ; le résidu mod 6 n'est lu par aucune Tour.
* Pièges : (1) l'uniforme sur 8 192 mots donne 2·C(12,c) profils, pas C(12,c) — facteur 2 ; (2) la composition mod 6 des écarts
  touchés diffère de celle de tous les écarts par la LONGUEUR des écarts, pas par β ; (3) ne pas citer E404/E408 (spectral).
* Commits : 33c36e43 (pré-enregistrement), puis module + résultats.

## 15. Arête manquante, plan Φ et mise en cohérence de `CLAUDE.md` (soir du 2026-11-08, §19.80–19.81)

* Lecture causale validée par l'auteur : premiers = cause commune (grammaire, mots) ; mot → Tour ; miroir = seconde lecture du même
  mot ; RH ⟺ tout mot porteur égale son miroir ; nœud non lu = poids `zeroMult` ; arête manquante = sélection des porteurs.
* Plan Φ (§19.80, E457–E460) PROPOSÉ, non exécuté : Φ0 nommer (R1 porteurs auto-miroirs, R2 hauteur injective sur les porteurs, R3 prix
  radialement aveugle sur les porteurs — trois équivalences à compiler, les deux sens) ; Φ1 théorème d'isolement (aucun préfixe fini du
  mot ne décide le porteur ; ingrédients : zéros isolés, `stagePosition` croissante en T) ; Φ2 dichotomie de la bande ; Φ3 hypothèses
  locales H-a/H-b (classer contre RH AVANT pré-enregistrement) ; Φ4 audit du poids sans théorie spectrale. Attendre l'accord de l'auteur.
* `CLAUDE.md` : section 1bis de préséance insérée, marqueurs `[DÉPASSÉ]`/`[LEVÉ]`/`[REFORMULÉ]`, bannières « INVENTAIRE HISTORIQUE »,
  règle R-Φ ajoutée ; rien n'est effacé. Piège : ne pas appliquer les consignes de §5 (i)–(iii) de `CLAUDE.md` (main rouge, status.sh,
  verrou) — elles sont dépassées ; ne pas écrire « contact aveugle au radial » (seul le pas l'est).

## 16. Soirée du 2026-11-08 : plan Φ validé et exécuté (E457), remarques externes, audit Φ4 en cours

* **Validation** : l'auteur a validé le plan Φ (§19.80) et ordonné d'exécuter chaque proposition (§19.82).
* **E457 (Φ0 + Φ1) — verdict A, commit bb1e65a0** : `Terminal/CarrierSelection.lean` (isolé, 22 déclarations, 1 tentative, axiomes standard,
  ban 0, build complet vert). R1/R2/R3/R3' ⟺ RH (jamais posées) ; R2 ⟹ `NoMixedHeight` ; théorème d'isolement : tout zéro vrai a, à même
  hauteur et aussi près qu'on veut à droite, une Tour non porteuse de même mot sur tout ensemble fini de rangs ; aucun prédicat à fenêtre
  finie ne sépare les porteurs. K0 et A4 sont des théorèmes ; route des fenêtres finies fermée ; l'arête est une propriété de QUEUE du mot [RECTIFIÉ §19.85, 2026-11-09 : « propriété de queue » n'est PAS démontré ; seul l'est : aucune sélection fondée exclusivement sur une fenêtre finie du mot].
  Jumeau 800/800 (`experiments/E457_CarrierSelection/RESULTS.md`).
* **Remarques externes (§19.83)** : « premier sur un contact » réglé par la direction β croissant ; définition du prix tenue (offPrice d'E445 +
  normalisation) ; pour E459, classement en trois rubriques (implication compilée / contre-modèle compilé au niveau des Tours / réciproque
  ouverte) ; priorité à Φ4 retenue.
* **Φ4 (E460) EN COURS** : inventaire §19.84 collecté ; reste à relire `PrimeWeightResponse`, `BoxAnchor`, `ZetaRealSegment`, certificats de boîte,
  puis écrire `experiments/E460_WeightAudit/AUDIT_POIDS.md` et conclure.
* **À faire ensuite, dans l'ordre** : (1) conclure E460 (audit, aucun module sauf si l'audit exhibe un énoncé ponctuel compilable) ;
  (2) E458 `MirrorStrip.lean` (B1–B4, §19.80 Φ2 ; jumeau : effectif de bande et encadrement B4 sur contrôles ; INTERDIT d'affirmer une
  densité) ; (3) E459 `CarrierLocalReading.lean` (H-a, H-b) avec classement en trois rubriques AVANT pré-enregistrement ; H-c consignée
  comme reformulation. Chaque étape : pré-enregistrement commité, deux tentatives, `attempts/`, `#print axioms`, grep du ban, build complet.
* **Interdits inchangés** : aucune théorie spectrale ni citation d'E404/E408 ; « aveugle à β » interdit pour les contacts (seul le pas l'est) ;
  jamais de test direct des premiers ou d'OFF ; `DemonstrationChain.lean` intact ; modules isolés non ajoutés à `RHV6Fresh.lean`.

### Prompt de reprise (à coller demain)
« Reprends RHV6Fresh au point du hand-over §16 (HANDOVER_20261107_LIGNE.md) et du maître sémantique §19.80–19.84. Dépôt /opt/zeta24-lean,
paquet formalization/RHV6Fresh, build `lake build RHV6Fresh` vert à bb1e65a0. Ordre : (1) termine l'audit Φ4/E460 (§19.84 : relire
PrimeWeightResponse, BoxAnchor, ZetaRealSegment, certificats de boîte ; écrire experiments/E460_WeightAudit/AUDIT_POIDS.md ; conclure en
mots) ; (2) pré-enregistre puis exécute E458 MirrorStrip.lean (B1–B4) ; (3) classe H-a et H-b en trois rubriques (implication compilée,
contre-modèle compilé sur les Tours, réciproque ouverte), puis pré-enregistre et exécute E459. Règles : CLAUDE.md section 1bis (préséance),
bannissement spectral total, troisième ordre sur les contacts, aucune hypothèse admise, deux tentatives par module, modules isolés,
pré-enregistrement commité avant compilation, jumeau déterministe borné sous nohup, rapport en mots français, commit et push après chaque
étape, consigner immédiatement au maître sémantique et au hand-over. »

## 17. Reprise du 2026-11-09 : rectification de portée d'E457, audit E460 conclu

* **Rectification (§19.85, réserve transmise par l'auteur)** : ne plus écrire « l'arête est une propriété de queue du mot ». Seule
  formulation démontrée : la sélection des porteurs ne peut pas être caractérisée par un prédicat portant exclusivement sur une fenêtre
  finie du mot ; une condition locale enrichie d'une information indépendante du mot n'est pas exclue. Marqueurs posés au maître
  (§19.80, 19.82, 19.83, 19.84) et au §16 ci-dessus ; `RESULTS.md` d'E457 et en-tête de `CarrierSelection.lean` corrigés (commentaire
  seul, module recompilé vert).
* **E460 conclu (§19.86, `experiments/E460_WeightAudit/AUDIT_POIDS.md`)** : aucun énoncé ne lit le poids aux contacts d'une Tour ; un seul
  mécanisme porteur de poids sélectionne et force la ligne, le comptage de fibre lu sur un contour, dont la forme uniforme est RH et
  simplicité (jamais posée) ; aucune condition arithmétique indépendante dans le corpus ; aucun module.
* **Suite** : E458 (B1–B4 + B5 poids de fibre ↔ bande), puis E459 (classement H-a/H-b en trois rubriques).
* **E458 (Φ2) — verdict A** : `Terminal/MirrorStrip.lean` (isolé, 20 déclarations, 1 tentative, axiomes standard, ban 0, build complet vert) ;
  B0–B6 compilés (§19.87) ; jumeau conforme ; la géométrie de la bande ne porte pas la sélection ; H-c close comme reformulation.
* **E459 (Φ3) — verdict A, critère d'arrêt NON atteint** : `Terminal/CarrierLocalReading.lean` (isolé, 17 déclarations, 1 tentative,
  axiomes standard, ban 0, build complet vert) ; classement en trois rubriques (§19.88) : H-a plus faible sur les Tours (fenêtre autour
  de la ligne, contre-modèle compilé) mais presque vide et sans poids ; H-b ⟺ RH et H-c ⟺ RH : reformulations jamais posées.
* **Plan Φ exécuté en entier (§19.89)** : aucune contradiction, frontière inchangée ; l'arête exige une information indépendante du mot
  d'une Tour, faisant intervenir le poids, lue sur les premiers ; le corpus n'en a pas. **Décision de route à l'auteur** ; aucune des
  trois pistes nommées en §19.89 n'est engagée. Ne rien lancer sans son ordre.
* **Invariants rappelés** : ne jamais écrire « propriété de queue » pour E457 (§19.85) ; ne jamais poser une reformulation de RH comme
  prémisse ; aucune densité de la bande ; jamais « un premier est sur un contact » (la branche dégénérée d'E459 est logique).

## 18. Proposition de l'auteur du 2026-11-09 : la totalité des contacts et la relation aux premiers (§19.90, E461, Φ5)

* **Proposition** : « totalité des contacts d'une Tour = même rythme, même phase, même fréquence, même relation aux premiers ⟹ c'est un
  zéro ». Elle ne contredit ni le plan ni E457 (fenêtre finie contre totalité) ; elle précise la piste (1) de §19.89.
* **Acquis** : le mot total détermine la Tour, donc la sélection est lisible sur le mot total (lecteur existant, unique sur les mots de
  Tours, jamais à fenêtre finie) — à fixer par E461, module isolé `Terminal/CarrierTotalWord.lean`, pré-enregistré.
* **Ouvert, seulement nommé** : définir la « réalisation arithmétique » sans le poids ni l'annulation de zêta. « Réalisation ⟺ zéro »
  caractérise tous les porteurs (ligne et hors ligne) : pas une reformulation de RH, n'exclut seule aucun zéro hors ligne.
* **E461 — verdict A** : `Terminal/CarrierTotalWord.lean` (isolé, 7 théorèmes, 1 tentative, axiomes standard, ban 0, build complet vert).
  La proposition est vraie au sens de l'existence ; l'obligation ouverte est la définition indépendante du lecteur. Rien n'est posé ;
  ne rien lancer de plus sans l'ordre de l'auteur. Invariant : refuser toute « réalisation » qui redit le poids.

## 19. Ordre du 2026-11-09 : interdiction du collectif LEVÉE (§19.91)

* **Ordre de l'auteur** : « enlève cette interdiction elle n'a pas de sens. Le collectif est important. » L'interdiction spectrale totale n'est plus en vigueur ; le collectif (sommes de Tours, formule
  explicite, reste, complément) est de nouveau autorisé ; grep de bannissement abandonné. Les autres ordres restent en vigueur.
* **Proposition précisée** : une Tour qui a le même mot total que la Tour d'un zéro EST ce zéro — théorème (T8, T9 ajoutés à
  `CarrierTotalWord.lean`). Ouvert : le critère sans zéro de référence ; piste nommée = présence dans la recomposition collective.

## 20. E462 (Φ6) : réalisation arithmétique d'une Tour par la recomposition des premiers (§19.92)

* **Ordre** : l'auteur valide la piste collective (« je valide continues », 2026-11-09).
* **E462 — verdict A** : `Terminal/ArithmeticRealization.lean` (isolé, 11 théorèmes, 1 tentative, axiomes standard, build complet vert).
  Réalisée (poids non nul dans une recomposition du signal lissé des premiers) ⟺ porteuse ⟺ zêta s'annule ; il existe ⟺ pour toute ;
  lecteur du mot total défini sans le poids, égal à celui d'E461.
* **Limites** : n'exclut aucun zéro hors ligne (« réalisée ⟹ sur la ligne » ⟺ RH, compilé, jamais prémisse) ; collectif, pas cellule par
  cellule ; fond fixe avec deux constantes de zêta ; raccord de `SpectralUniqueness.lean`, pas d'analyse nouvelle.
* **Suite possible, non engagée** : (a) version à constantes libres du fond ; (b) lire la recomposition sur les cellules d'une Tour
  (pont entre le collectif et le mot) ; ne rien lancer sans l'ordre de l'auteur.

## 21. E463 (Φ7) : la recomposition lue sur les cellules d'une Tour (§19.93) ; E464 expérience latérale (§19.94)

* **E463 — verdict A** : `Terminal/RecompositionOnCells.lean` (isolé, 14 théorèmes, 1 tentative, axiomes standard, build complet vert).
  Part d'une Tour sur ses cellules : signe alterné, amplitude multipliée par un facteur fixe (fréquence et position radiale) ; non nulle
  sur chaque cellule ⟺ porteuse ; bilan collectif sur toute pièce. N'exclut aucun zéro hors ligne ; la part d'une seule Tour n'est pas
  lue sur les premiers de sa cellule.
* **E464** : prédicteur de premiers par les Tours, ordonné par l'auteur, HORS route de preuve ; voir `experiments/E464_PrimePredictor/`.

## 22. E465 (Φ8) : le bilan collectif en aires de la demande sur les pièces découpées par les contacts (§19.95)

* **E465 — verdict A** : `Terminal/CollectiveSlopeOnPieces.lean` (isolé, 4 définitions, 19 théorèmes, 1 tentative, axiomes standard,
  build complet vert, jumeau à 50 chiffres conforme). Total des parts sur une pièce = aire de la demande brute moins variation du fond
  résiduel ; la rencontre change la pente, sans saut ; aucun poids premier dans l'aire de son propre écart ; découpage de l'aire d'un
  écart par les contacts ; sur une cellule de contacts, terme de la Tour = sa part d'E463.
* **Garde-fous** : S11 juxtapose part et aire, ne les compare pas (R-E446) ; rien n'exclut un zéro hors ligne.
* **Leçons du prédicteur (E464)** : cellule plus courte qu'un pas d'entier pour isoler un poids (fini pour chaque Tour) ; rencontre du
  second ordre dans le signal recomposé ; plus de seuil numérique annoncé sans étalonnage.

## 23. Point d'étape du 2026-11-09 au soir (§19.96)

* **Fait** : plan Φ complet (E457–E460), puis Φ5–Φ8 (E461, E462, E463, E465) ; E464 latérale close. Tout compilé à la première
  tentative depuis E462, build vert, tout poussé.
* **État** : des deux côtés tout est écrit (part alternée de chaque Tour ; aire de la demande brute), l'égalité ne vaut que pour le
  total ; rien ne distingue la ligne du hors-ligne.
* **Manque** : l'arête (pourquoi une Tour hors ligne ne figure pas : c'est RH) ; isoler une Tour dans le total sur ses cellules ;
  fond à constantes libres ; maîtres mathématique et Lean arrêtés au 2026-10-25 (note de renvoi posée).
* **Suite proposée, non engagée** : Φ9 annulateur de fibre sur les cellules (deux totaux consécutifs éliminent une Tour, trois la paire
  Tour + miroir) ; classer contre RH avant de poser ; attendre l'ordre de l'auteur.
* **Cohérence** : marqueurs `[LEVÉ]` / `[DÉPASSÉ]` ajoutés dans `CLAUDE.md` §1bis, deux bandeaux, R-Φ ; §1 de ce hand-over annoté.

## 24. Prompt de reprise (à coller à la prochaine session)

« Reprends RHV6Fresh au point du hand-over §29 (`HANDOVER_20261107_LIGNE.md`) et du maître sémantique §19.100–19.101 (plan Ψ exécuté ; règles R-RH et R-Ψ en vigueur). Dépôt
/opt/zeta24-lean, branche main, paquet formalization/RHV6Fresh, `lake build RHV6Fresh` vert. Lis d'abord `CLAUDE.md` §1bis (préséance)
et les règles R-Φ à R-Φ septies. État : la part d'une Tour dans la recomposition des premiers est écrite sur ses cellules (E463), le
total sur toute pièce est une aire de la demande brute découpée par les contacts (E465) ; rien n'exclut un zéro hors ligne. Tâche
proposée, à ne lancer que sur mon ordre : Φ9, annulateur de fibre sur les cellules (éliminer une Tour par deux totaux consécutifs, la
paire Tour + miroir par trois ; écrire l'identité « combinaison d'aires = contribution des autres hauteurs » ; la classer contre RH en
trois rubriques AVANT de la poser). Règles : le collectif est autorisé (§19.91) ; troisième ordre (les contacts lisent la position
radiale) ; jamais « la Tour touche un premier » ; jamais lier la contradiction à « amplitude contre variation de la demande » ; aucune
hypothèse admise, aucune reformulation de RH en prémisse ; module isolé non ajouté à `RHV6Fresh.lean` ; grep des noms avant d'écrire ;
pré-enregistrement commité avec le module définitif AVANT toute compilation, aucune sonde ; deux tentatives au plus, consignées dans
`attempts/` ; `#print axioms` ; build complet vert ; jumeau déterministe borné sous nohup ; consigner aussitôt au maître sémantique, au
hand-over et à `CLAUDE.md` ; rapport en mots français sans formule ; commit et push directs sur main. »

## 25. E466 : audit externe du prédicteur et confrontation de quatre canaux (§19.97, 2026-11-12)

Audit externe transmis par l'auteur, accepté comme cahier des charges (points A–E, consignés §19.97). Rectification : « horizon hors de
portée pour une raison de théorème » RETIRÉ ; dire « échelle de résolution de la méthode, mesurée ». E466 pré-enregistré (`8f975ee3`)
puis exécuté : E464 reproduit à 3·10^-14 ; sur les fenêtres où la cellule la plus fine est ≤ 1, le canal sans Fejér est exact (351/351,
seuil fixe 0,75, deux familles, cinq fenêtres inédites) là où E464 manquait 91 premiers ; horizon de marge positive 0,83 → 1,39 ;
seconde différence du signal intégré sans gain de résolution ; grammaire modulo 6 sans effet ; contacts = résolution seulement
(abstention R2 juste). Verdict A. Négatif consigné : aucune information discriminante des contacts hors la résolution. Expérience
latérale ; frontière inchangée. Réponse à la contestation « rien ne distingue un hors-ligne » : §19.97 (le corpus distingue, compilé
cinq fois ; distinguer n'est pas contredire ; stabilité à formuler par l'auteur, à classer, à compiler ; outil = Φ9).

## 26. Ordre de l'auteur du 2026-11-13 : « ⟺ RH » n'est plus un argument (§19.98, règle R-RH)

Ne plus jamais rapporter qu'une cible est équivalente à RH comme objection, frein ou frontière : c'est évident, nous résolvons RH
directement. Seul reste interdit d'ADMETTRE une telle cible comme hypothèse (prémisse, axiome, `sorry`). Le prompt de reprise §24 se lit
avec cette règle ; la phrase « la classer contre RH en trois rubriques AVANT de la poser » y devient un contrôle interne non rapporté.

## 27. Audit des hypothèses écartées au motif « ⟺ RH » (2026-11-13, §19.99)

`AUDIT_HYPOTHESES_EQUIV_RH_20261113.md` : 24 énoncés ; 14 rejetés à tort comme cibles (rouverts), 5 attaqués mais rapportés comme
« frontière » (compte rendu corrigé), 5 relevant de l'auteur (H23 à trancher). Cible recommandée : H3 constance par membre, via Φ9.
Ne plus écrire « frontière inchangée (⟺ RH) » nulle part.

## 28. Plan Ψ, attaques cumulatives (§19.100, 2026-11-13)

`PLAN_PSI_ATTAQUES_CUMULEES_20261113.md`. H23 abandonnée (auteur) ; H3 et H17 R3' validées ; H15 rouverte en série, R-E446 gardée au sens
ponctuel. Six causes racines (RC1–RC6), six attaques Ψ1–Ψ6, ordre Ψ1 → Ψ2 → Ψ3 (+Ψ5) → Ψ4 → Ψ6. Prochaine action : Ψ1,
`MemberConstancySeries.lean` (dérive cumulée en forme close), pré-enregistrée avec section « Stratégie » (règle R-Ψ).

## 29. Plan Ψ exécuté (E467–E471, §19.101, 2026-11-13)

Quatre modules isolés verts (31 énoncés, axiomes standard), build complet vert, jumeau conforme. Établi : dérive cumulée en forme close
(part relative × e^{π(β−1/2)/T} par cellule ; asymétrie cumulée = (1−2β)θ(N) ; somme alternée géométrique, bornée sur la ligne, divergente
pour le miroir) ; annulateur de fibre (Tour et paire retirées du total sur leurs cellules, M2 levée) ; budget alterné des premiers = somme
des sommes alternées des membres. Cible unique restante, en série, sur les premiers seuls : le budget alterné B_N reste à l'échelle de la
ligne (force de RH, attendu). Prochaine attaque proposée : E472 (mesure de B_N sur les premiers réels) puis lemme d'annulation entre
cellules consécutives. Règles : R-RH (équivalence à RH jamais une objection), R-Ψ (série, section Stratégie), écart « trois tentatives »
consigné pour E467.

## 30. Audit externe du build Ψ ; E472 exécuté (§19.105, 2026-11-13)

Quatre réserves de l'audit vérifiées exactes (fond dans le budget ; somme de normes ; signes rectifiés, non alternance ; Ψ3
définitionnel) et levées en Lean par `ArithmeticBudgetSeparation.lean` (isolé, 18 énoncés, axiomes standard, 2 tentatives) :
budget arithmétique (premiers seuls, indépendant de la recomposition) séparé du fond (fond à l'échelle `x_N`, s'efface à l'échelle de la
ligne) ; somme naturelle télescopée encadrée par la somme à signes rectifiés ; contribution COMPLEXE de la paire non bornée (deux formes,
coefficient de la recomposition si miroir porteur) ; pont géométrique de Ψ3 aux termes de fibre, aucun pont arithmétique. Phase B
sur premiers réels (3·10^7, 2M zéros) : `A_N/x_N^{3/2} < 0,08` sur 8 Tours, résidu à l'échelle `x_N`, troncature `≤ 10^{-7}`, paire
artificielle séparée du résidu et de la troncature ; verdict B (seuil flottant du télescopage). Cible unique réécrite sur
`arithmeticAlternatingBudget`. Reprise : §30 / §19.105 ; prochaine attaque = lemme d'annulation entre aires de cellules consécutives
lu sur les premiers (Bertrand seul ne le donne pas).

## 31. E473 exécuté : grammaire des aires entre contacts consécutifs (§19.106, 2026-11-13)

Ordre de l'auteur après E472. Module isolé `CellAreaGrammar.lean` (18 énoncés, axiomes standard, 2 tentatives, build complet vert),
jumeau sur les contacts réels de 8 Tours (verdict A). Compilé : G1 identité exacte des contributions premières d'une cellule ; G2
grammaire locale `a_{k+1} − e^{π/T} a_k = ε_{k+1} + e^{π/T} η_k` (demande au contact ÉLIMINÉE) ; G3 récurrence du budget (première
aire + dernière aire + somme alternée des termes locaux), pont avec `arithmeticAlternatingBudget` ; G4 transmission sous changement de
signe ; G5 échelle inconditionnelle `x_N^2` (PNT porté) ; G6 clôtures conditionnelles à antécédents explicites. Mesuré : termes locaux
≤ 0,07 à l'échelle de la ligne, 50 % de changements de signe sur les contacts réels de la Tour 1 (rectifie E472 : 100 % venait du
découpage `x₀ = 1000`), formule cumulée instable jusqu'à 3,6e-4 (utiliser la formule de cellule). Aucune obligation nouvelle qui borne ;
réduction exacte de la cible au terme local et à une aire. Reprise : §31 / §19.106 ; prochaine attaque = lecture de `L_k` comme somme
des premiers de deux cellules contre une dent de scie explicite, corrélation `L_k`/`L_{k+1}` mesurée AVANT pré-enregistrement.

## 32. E474 exécuté : quatre hypothèses fermées en TDD (§19.107, 2026-11-13)

Ordre de l'auteur : hypothèses (≥ 3–4) fermées par compilateur et expériences en TDD. Pré-enregistrement `3a1943de` (tests à seuils
écrits avant toute compilation), jumeau d'abord (13 Tours, zéros 1 à 5000, premiers ≤ 3·10^7, 109 s), puis deux modules isolés :
`CellAreaTent.lean` (10 énoncés) et `CellAreaIntegral.lean` (14 énoncés), axiomes standard, deux tentatives chacun, build complet vert.
Compilé : H1 le terme local est la somme des premiers de deux cellules contre un chapeau continu moins son intégrale
(`localGrammarTerm_eq_tent_sum`) ; H2 mémoire un `L_k = ε_{k+1} − e^{π/T}ε_k + e^{π/T}ℓ_kΔ_k` et forme de sortie de la somme alternée ;
H3 `|L_k| ≤ 2e^{π/T}ℓ_k M` (la loi en 1/T est la longueur de cellule) ; H4 **l'aire de la demande est l'intégrale de `rawDemand`**
(sommation d'Abel de Mathlib), `ε_k = ∫(D − D(C_k))`, bornes par suprémum et variation intérieure ; budget d'une fenêtre
`≤ M(1+e^{π/T})² x_N` sans alternance. Mesuré : H1/H2 identités à 1e-11 ; H3 passé (T·|L|/C^{3/2} ≤ 2,07) ; H4 passé (ε/(ℓ√x) ≤ 0,70,
Δ/√x ≤ 1,0) ; H2 autocorrélation ÉCHOUÉE par la lettre (signe prédit confirmé, −0,38 Tour 1 → +0,10 Tour 1000 ; amplitude > 0,2 non
atteinte) → verdict B. Fait neuf (mesure) : les deux parts de la mémoire un sont presque opposées (corr −0,998 → −0,62), d'où un terme
local très inférieur à sa borne par la demande (serrage médian 0,025–0,13). Aucune obligation nouvelle qui borne ; réduction la plus
courte : budget ⟸ demande en `√x(log x)²` sur la fenêtre (force RH, R-RH). Reprise : §32 / §19.107 ; prochaine mesure = décomposer
`L_k` côté zéros (part propre de la Tour annulée par le chapeau ?) avant tout pré-enregistrement.

## 33. Décision de l'auteur : E475 abandonnée, E473–E474 auxiliaires, retour à la rencontre au premier partagé (§19.108, 2026-11-14)

Ordre : classer E473–E474 comme auxiliaires (aucune portée vers RH), abandonner l'E475 « tente côté zéros », chercher la contrainte
nouvelle que la reconstruction exacte d'un écart impose à la première Tour OFF à la rencontre au premier partagé, que ses contacts et
ceux de son miroir ne peuvent satisfaire ; jamais de coïncidence contact/premier ; rencontre définie par la grammaire des premiers
(`PrimeGapInterval`, `meetingPoint`, `TowerRaccord.M`, `imposedShare`, `all_signals_meet`), pas par un triangle. Exécuté : audit
`experiments/E475_SharedPrimeObligation/AUDIT_20261114.md` (aucun module) : tableau O1–O7 ; toutes les obligations dérivées de la
reconstruction (O1–O5) sont satisfaites par la paire ; les deux qu'elle viole (O6 amplitude relative constante, O7 fréquence attendue)
ne sont pas dérivées de la reconstruction ; la contrainte cherchée = chaînon O1 ⟹ O6 par membre (P5 de l'auteur, §19.21.1), question
précise Q475 ; obstacle de forme `authentic_family_reconstructs_any_radial` (utiliser les données arithmétiques du raccord, pas la seule
identité). Reprise : §33 / §19.108 ; prochaine étape = mesures M1–M3 de l'audit §4, puis pré-enregistrement d'E475 reformulée.

## 34. E475 exécutée : mesures M1–M3 au premier partagé, verdict B (§19.109, 2026-11-14)

Pré-enregistrement `f7172ad5`, jumeau 0,1 s, aucun module. M1 exact (premier partagé = `p_{n+1}` sur 2000 raccords). M2 : rapport des
parts imposées des deux membres sur le transport = `(‖ρ_e+1‖/‖ρ_l+1‖)·(Φ_l/Φ_e)` exactement (identité ; dix premiers 0,096–2,10 ; médiane 1) ;
test 1e-6 échoué. M3 : sensibilité radiale = prix O5. Constat : Q475 sur les parts est vide ; la paire ne modifie que l'énumération (deux
index, deux occurrences consécutives à une hauteur). Reprise : §34 / §19.109 ; décision de l'auteur attendue sur la formulation suivante
(obligation sur deux écarts consécutifs et trois membres, forme O7), aucun pré-enregistrement sans elle.

## 35. E476 exécutée : tente et cassure, obligation du poids de la cassure (§19.110, 2026-11-14)

Ordre : combiner tente (E474) et cassure (E447/E450). Pré-enregistrement `1b528665` ; module isolé `TentBreakObligation.lean` (10 énoncés,
axiomes standard, 2 tentatives, build complet vert) ; jumeau 22 s, 8 Tours. Compilé : poids de la cassure `w = e^{π/T}x(1 − e^{−πf/T})`
dans la grammaire des aires, amplitude payée `= x^β(1 − w/(e^{π/T}x))^β/‖ρ‖` (`break_amplitude_reads_tent`), poids alterné en dent de scie
nulle au point neutre, **`pair_breakTentWeight_eq_iff` : même poids pour la Tour et le miroir ⟺ ligne**. Mesuré : identités 1e-14 ; H3b
échoue par la lettre (Tour 1, prédiction en mauvaise mesure) ; H4 échoue de 11 % sur seuil (loi `(π/T)(|δ|/π)`, maximum 0,2 sur la fraction
`|δ|/π` à mot décalé). Verdict B. L'obligation est une forme (deux poids pour un premier), pas une contradiction. Reprise : §35 / §19.110 ;
prochaine mesure = somme alternée Tour moins miroir sur les premiers à mot décalé, échelle en `x`, avant toute hypothèse.

## 36. E477 exécutée : poids alternés Tour moins miroir sur les premiers à mot décalé, verdict B, aucun théorème (§19.111, 2026-11-14)

Pré-enregistrement `67feec44`, jumeau 15 s, aucun module. Sur les premiers à mot décalé, les deux poids alternés sont égaux au premier ordre
(la parité compense le signe) ; différence du premier ordre en `δ` à signe variable ; somme restreinte désalternée du SECOND ordre en `δ`
(prédiction confirmée à 1,16–1,31 sur la Tour 1) ; somme cumulée dominée par les fluctuations (pentes 1,43–1,88, ≤ 3e-3·x^{3/2}). Sur les
non décalés, identité du premier ordre, alternée. P1 échoue par la même erreur de mesure qu'E476/H3b (loi corrigée
`(1 − e^{−δ/T})/(1 − e^{−π/T})`, 0,1–0,6 %) ; P3 plancher flottant ; P5 prédiction fausse en nature (fluctuation). Décision pré-écrite :
aucun théorème à écrire. Fil tente-et-cassure (E474 → E476 → E477) mesuré jusqu'au bout, sans piste de fermeture. Reprise : §36 / §19.111 ;
retour à Q475 (§19.108, §33–34), forme O7, décision de l'auteur attendue ; aucun pré-enregistrement sans elle.
