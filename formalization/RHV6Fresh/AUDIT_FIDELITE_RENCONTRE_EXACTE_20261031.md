# Audit de fidélité et de cohérence : la rencontre exacte (2026-10-31)

Objet : confronter tout le Lean (`RHV6Fresh/Terminal/`, 221 fichiers) et tous les `.md` du dossier (maître
`RHV6final_STRATEGIE_SEMANTIQUE.md`, audits, README d'expériences) aux cinq principes de la contreproposition de
l'auteur, et au graphique `experiments/riemann_graphique.png` (commit 8c655ef7). Lecture seule : aucun fichier Lean n'a été
modifié, aucune compilation n'a été lancée. Les lignes du maître sont celles de la version d7920949 (2917 lignes).

## 0. Les cinq principes audités (texte de l'auteur, reformulé en mots)

* **P1. Exactitude à la rencontre.** Au point de rencontre, fin de l'écart premier, la totalité des contributions des zéros
  reconstruit exactement la grandeur arithmétique. Le défaut de reconstruction est nul. Aucune marge, aucune « rencontre
  ratée », aucune erreur à rattraper.
* **P2. La décomposition est une identité.** Écrire « total = paire OFF + autres zéros » n'introduit aucun défaut. Les
  « autres zéros » ne sont ni une erreur tolérée ni une réserve qui répare quoi que ce soit. Et l'égalité exacte de la
  totalité ne démontre pas que chaque zéro fournit individuellement une quantité déterminée par l'écart : cela demande une
  relation supplémentaire.
* **P3. Liaison permanente.** La formule explicite lie les zéros aux premiers sur tout le domaine, inconditionnellement,
  avec les vrais zéros quelle que soit leur position radiale. Les rencontres géométriques du projet (contacts des Tours,
  événements premiers canoniques) sont une structure supplémentaire dont il faut vérifier qu'elle est fidèle à la formule.
* **P4. Raisonnements proscrits.** Chercher un résidu acceptable à la rencontre ; traiter les autres fréquences comme
  réserve ; déclarer OFF compatible parce qu'on peut écrire « cible moins OFF » ; prendre une identité de décomposition pour
  une preuve de compatibilité. Et, à l'inverse : l'absence de défaut global n'exclut pas un zéro OFF.
* **P5. Cible, non démontrée.** Reconstruction exacte, contacts authentiques, succession canonique, premier partagé,
  ensemble, impliquent-ils une contrainte sur la position radiale, à savoir un demi ? Non démontré.

## 1. Analyse du graphique `riemann_graphique.png`

Quatre panneaux et un encart.

**Panneau 1, « Reconstruction 100 % exacte ».** Escalier de la fonction de Tchebychev avec marches aux premiers 2, 3, 5, 7,
11, 13 et somme spectrale touchant le coin de chaque marche, défaut annoté nul à chaque premier.

* Fidèle à P1 sur le fond : l'égalité exacte à chaque fin d'écart est compilée (`localSynchronization`,
  `all_signals_meet`, `exactness_is_a_demand`).
* Trois écarts de fidélité de dessin. L'escalier dessiné omet les puissances de premiers (4, 8, 9), qui portent une cassure
  dans le corpus (`gap_demand_eq_break_add_rest`, §19.13 C1). Le canal compilé est le canal lissé (poids « un moins n sur
  x »), où la somme est continue et où la cassure est adoucie ; le contact « au coin » est une image du canal de comptage,
  qui n'est pas formalisé (§19.20.3). L'axe est annoncé logarithmique mais tracé linéaire. Aucune de ces trois choses
  n'affecte le principe ; elles affectent la lecture.

**Panneau 2, « Bilan exact, impasse spectrale OFF ».** Total fixe, paire OFF divergeant vers plus l'infini, « reste exigé »
descendant vers moins l'infini, « plafond physique » égal à la somme des amplitudes, zone inaccessible.

* Ce panneau n'est pas fidèle au corpus, sur quatre points.
  1. **Ce qui diverge.** Le théorème cité (`pairRelativeAmplitude_unbounded`) dit : l'amplitude relative de la paire, module
     rapporté à la racine du point, n'est bornée à aucune borne le long des rencontres. Il ne dit ni « contribution OFF
     vers plus l'infini » en valeur signée, ni « limite » ; il est en norme et en « pour toute borne, une rencontre la
     dépasse ».
  2. **Le total n'est pas « fixe ».** Le total est la demande, dont le niveau relatif aux rencontres n'a aucune borne
     compilée : « demande bornée aux rencontres » est une hypothèse nommée (`DemandBoundedAtMeetings`), et « demande bornée
     partout » équivaut à RH (`DemandLevelPremise`, lignes 70 et 75).
  3. **Le « plafond » n'est pas un fait.** La somme des poids lissés est finie (`totalLineWeight`, `indexWeight_summable`),
     mais elle ne plafonne le reste qu'en amplitude relative et seulement pour une famille sans zéro à droite de la ligne
     (`restRelativeAmplitude_le_total` sous l'hypothèse nommée `RestNotRight`). Or le miroir d'un zéro OFF est à droite.
     En canal non lissé, la somme des amplitudes diverge (maître ligne 875).
  4. **La conclusion est circulaire.** Le schéma « OFF diverge, ON plafonné, donc ligne » est exactement le théorème
     compilé `not_low_of_bounded_demand_and_restNotRight`, dont les deux hypothèses réunies équivalent à RH
     (`expectedFrequencyRises_iff_meetings_and_restNeverRight`, puis `riemannHypothesis_of_meetings`). Le corpus ne réfute
     pas l'énoncé conditionnel ; il réfute qu'il soit une preuve.
* Le panneau contredit en outre le maître sur un point déjà consigné : le prix de la paire OFF est payable, mais seulement par
  une infinité de zéros à droite (§19.8 « compensation acquise », lignes 2126 et 2155, TotalityPays), et « ce que paie une
  infinité n'est pas compilé ».

**Panneau 3, « Fenêtre minimale trois écarts, signature hyperbolique ».** Régime ON en montée stricte sur quatre premiers,
régime OFF avec pas horizontal gelé.

* Fidèle pour le gel : `outgoing_frozen`, `single_frozen_step_of_mirror` (montée, gel, montée dans le cas (a)).
* Infidèle par omission pour la « montée stricte » : la cascade stricte d'un pas est équivalente à RH
  (`strict_frequency_cascade_iff_riemannHypothesis`, `consecutive_heights_distinct_iff_riemannHypothesis`) ; elle n'est vraie
  que sur la ligne (`strict_frequency_cascade_onLine`). La dessiner comme « le régime ON » est correct ; la lire comme un
  fait du régime réel est poser la cible.

**Encart, « Principes et conclusions ».** Les points 1 et 2 sont fidèles à P1 et P3. Le point 3 attribue à
`MeetingPoint.lean` une dérive « vers plus l'infini » qui n'y est pas sous cette forme, et un plafond qui n'y est pas. Le
point 4 (« l'égalité exacte interdit formellement une paire OFF », « conséquence formelle : un demi ») n'est établi nulle
part dans le dépôt et contredit le second texte de l'auteur lui-même : « l'absence de défaut global ne suffit pas à exclure
un OFF ». Aucune occurrence de « conséquence formelle » n'existe dans les `.md` du dossier.

**Verdict sur le graphique.** Panneaux 1 et 3 : illustrations fidèles sous réserve des lectures ci-dessus. Panneau 2 et
point 4 de l'encart : à retirer ou à réécrire ; ils affirment comme acquis le contenu exact de la frontière.

## 2. Cohérence entre les deux textes de l'auteur

Le premier texte (contreproposition) et le second (lecture du graphique) ne disent pas la même chose au point décisif. Le
premier : « l'absence de défaut global ne suffit pas à exclure un OFF ; la formule explicite est inconditionnelle » et
« cette implication n'est pas encore démontrée ». Le second : « l'égalité exacte interdit formellement l'existence d'une
paire OFF… conséquence formelle : un demi ». Le dépôt soutient le premier et ne soutient pas le second. L'audit retient le
premier comme doctrine ; le second est traité comme une lecture à rectifier.

## 3. Audit du Lean

### 3.1 Ce que le corpus compile, principe par principe

* **P1 compilé.** `localArithmeticTarget I` est l'incrément du reste lissé des premiers sur l'écart, défini sans zéro ;
  `localSynchronization I` l'égale à la somme sur tous les vrais zéros ; `exactness_is_a_demand` ajoute qu'aucune famille
  finie ne l'accomplit sur un voisinage de la rencontre. Aucune position radiale n'entre
  (`localSynchronization_from_explicit_formula`).
* **P2 compilé.** `localReconstructionResidual s I` est le résidu d'une troncature finie, et `localResidual_eq_tail` le
  déclare égal à la queue des zéros omis ; `remainder_eq_pair_add_rest` écrit « total = couple + reste » comme identité ;
  `eventCompensation_eq_complement` et `break_compensated_by_other_frequencies` sont des égalités exactes avec le
  complément, sans borne.
* **P3 compilé.** `authentic_family_reconstructs_any_radial` : la reconstruction tient pour toute position radiale de la
  famille authentique. Les objets géométriques du projet existent sur tout passage (`towerRaccordOf`,
  `grammaticalRaccordOf`), et `TransportAtSharedPrime` consigne que les premiers fixent la base du transport, jamais
  l'exposant.
* **P4, réciproque, compilée.** `parameter_grid_admissible` : toute position radiale dans l'intervalle ouvert à gauche de
  zéro jusqu'à un demi satisfait les obligations de contact. `InsertionExclusion` dit lui-même qu'il n'exclut pas un membre
  OFF de la famille authentique. Aucun théorème ne traite un résidu non nul comme admissible à une rencontre ; aucun ne
  répare une rencontre avec les autres zéros ; aucun ne conclut la compatibilité d'OFF depuis « cible moins OFF ».
* **P5 non compilé, et nommé.** Tout théorème qui conclut la ligne passe par une hypothèse nommée équivalente à RH :
  `ContinuationForcedOnCarriers` (`continuationForced_iff_riemannHypothesis`), `ExpectedFrequencyRisesAtMeetings`
  (`riemannHypothesis_of_meetings`), `RaccordHierarchy` sur tout passage (`raccordHierarchy_iff_riemannHypothesis`),
  hauteurs consécutives distinctes, loi de constance par membre (`constantNeed_law_iff_riemannHypothesis`). Le théorème
  cité dans la contreproposition sous le nom « contradiction locale » s'appelle `continuation_contradiction`.

### 3.2 La « relation supplémentaire » de P2 est déjà identifiée dans le corpus

Le texte de l'auteur dit que l'égalité de la totalité ne donne pas « chaque zéro fournit une quantité déterminée par
l'écart », et qu'il faut une relation supplémentaire. Dans le Lean, la part d'un membre à la rencontre (`imposedShare`) est
définie par le membre lui-même, sur ses trois paramètres (`imposedShare_at_meeting`), et `imposedShare_eq` l'écrit comme
« cible moins les autres » : c'est l'identité de P2, pas une détermination par l'écart. La relation supplémentaire, sous sa
forme la plus faible connue, est « amplitude relative constante entre rencontres, membre par membre », équivalente à la
ligne pour ce membre (`constantRelativeAmplitude_iff_onLine`), et sa forme universelle équivaut à RH
(`constantNeed_law_iff_riemannHypothesis`). Elle est donc nommée, jamais posée, et c'est la cible P5 elle-même lue en
amplitude.

### 3.3 Infidélités mathématiques dans le Lean : aucune

### 3.4 Défauts de vocabulaire dans le Lean (preuves correctes, lexique à risque P2/P4)

1. `LocalWindowTransmission.lean` (lignes 57-58, 105-110) et `CertifiedRemoval.lean` (21, 75) : « marge admissible »,
   « écart admissible ». Le complément infini y est présenté comme une marge d'erreur autour du signal du groupe. Ce sont
   des majorations vraies de la queue, d'exposant un, non discriminantes.
2. `JointComparison.lean` (13-14, 79-80) : « compensation maximale du complément ». Le complément y apparaît comme une
   réserve bornée ; l'hypothèse n'est pas démontrée.
3. `HeightPacket.lean` (15-16, 143-145) « compensation forcée… ce que tous les autres zéros doivent fournir », et le nom
   `break_compensated_by_other_frequencies` dans `OffCarrier.lean`. Égalités exactes nommées « compensation ».
4. `TotalityPays.lean` (105-107, 118) « annulation fournie par les autres zéros », « ce que la totalité doit payer » ;
   `RemainderRegime.lean` (86) « ce que la ligne entière peut payer ». Les autres zéros y sont des payeurs.
5. `FirstArrivalsAnchor.lean` (213-215) : « une compensation par d'autres modes est une question d'algèbre linéaire finie »,
   docstring sans théorème.

Le mot « plafond » dans `CellRestitution.lean` et `JointComparison.lean` désigne la partie entière supérieure ou une
majoration d'exposant un ; il n'a rien à voir avec le plafond du graphique. Le « ε » de `LowNextZeroSignatures.lean` est
une tolérance de détection sur fenêtre finie, pas une tolérance de rencontre.

## 4. Audit des `.md`

### 4.1 Ce que le maître affirme déjà, fidèle à la doctrine

* Exactitude compilée : lignes 2092 (MeetingPoint), 2118 (MeetingExactness), 2847-2849 (§19.20.1), 2050.
* Identité de décomposition : 388-390, 1905 (« une décomposition dont le résidu est défini par différence n'a aucun
  contenu »), 2532 (§19.12.2 `target_split_of_mirror`).
* Non-exclusion d'OFF par l'exactitude : 2114, 2472-2473 (§19.10.2, lecture littérale FAUSSE), E335 lignes 289-294, E394
  lignes 61-62, e239 (« FIRST_OFF_EXCLUDED : FALSE »).
* Contre « OFF ne peut pas réaliser la cassure » : 2565-2568 (§19.13.2).
* Le plafond n'est qu'en poids lissés, sous hypothèse : 875, 2120, 2122, 2126, 2140, 2155, 2325, 2333.
* Aucune occurrence de « rencontre ratée », « rattraper », « conséquence formelle » ; aucun plafond sur l'amplitude totale.

### 4.2 Infidélités et ambiguïtés dans les `.md`, par gravité

1. **Maître 2868-2869 (§19.20.1 point 4), INFIDÈLE.** « Un signal qui remplit une demande de niveau constant a une
   amplitude relative constante… » lit membre par membre une demande qui porte sur la somme. Contredit 2112, 2114 et E394
   ligne 74 (« que la demande exige cette constance à chaque membre : non établi »).
2. **Maître 2883-2884 (§19.20.2), INFIDÈLE.** « Même cause pour chacun : niveau constant de la demande aux rencontres,
   donc amplitude relative constante, donc ligne. » Une mesure (E394) présentée comme cause, contre P5 et contre e239.
3. **Maître 2911 (§19.20.4), INFIDÈLE par incohérence interne.** « Chaque flèche de la chaîne est compilée, sauf une »,
   alors que le point 3 est « mesuré, non compilé » (2865) et que le point 4 repose sur E394.
4. **Maître 2184, INFIDÈLE, corrigé plus loin sans annotation** (la correction est en 2228).
5. **Maître 2157, 2163, 2167, périmés** (« tout le reste de la chaîne est fermé », « un travail de compilation, pas une
   inconnue »), démentis par §17-18 (obstruction de Landau) et par §19.
6. **Maître 2052**, réfutation attribuée à un théorème non identifié ; 2126 montre que ces théorèmes sont conditionnels.
7. **Maître 2872-2873**, omet l'hypothèse de demande bornée que `shortfall_unbounded_of_bounded_demand` exige.
8. **Lexique « payer le prix »** (2120, 2122, 2140, 2150-2155, 2198, 2255, 2309 ; E396 ligne 71 ; E397 lignes 44, 115) :
   les autres zéros vus comme réserve.
9. **Maître 2390, 2400 (§19.8), 2193 (§16.5)** : « tous les signaux se rencontrent / s'y rencontrent. Théorème. » en
   tension avec 2473. L'énoncé compilé est l'identité de la somme à la fin de l'écart ; « chaque signal se rencontre » est
   la lecture littérale déclarée fausse.
10. **Maître 2194, 2050 (fin), 1370** : la « part imposée » est la cible moins les autres, présentée comme contrainte.
11. **Maître 2859-2861 et E392 ligne 6** : la règle d'arrondi (0,988 compté comme rencontre) sert d'appui causal ; E392 n'a
    pas de pré-enregistrement.
12. **Maître 2878-2880** : « Le premier signal, seul, cesse de rencontrer les fins d'écarts suivantes » est une lecture par
    terme ; « seul régime stable » se lit comme une exclusion (idem 2132, 2146, 2157, 2197).
13. Maître 431-437 et 952 (« dette de compensation » définie contre une paire ON fictive, interdite par §19.17.4) ; 1354 ;
    1941 ; 2190 et 2198 ; 1926 ; 2618 ; 821, 824 ; E386 ligne 35 : ambiguïtés lexicales ou de datation, détaillées dans le
    rapport d'agent, sans effet sur un énoncé compilé.

### 4.3 Verdict `.md`

Aucun passage ne traite un défaut non nul à la rencontre comme admissible. Les seuls résidus admis sont des résidus de
troncature, identifiés à la queue des zéros omis. Les infidélités réelles sont concentrées dans §19.20 (points 1 à 3, 7,
11, 12), écrites la veille, et dans des passages anciens périmés (4, 5, 6). Elles sont rectifiées au §19.21 du maître sans
réécriture du journal.

## 5. Ce que l'audit conclut sur P5

* L'énoncé P5 restreint au porteur canonique est : « pour tout porteur OFF canonique, contradiction ». Il est équivalent à
  RH par `exists_offCarrier_of_not_riemannHypothesis` et par la définition du porteur ; sa forme nommée est
  `ContinuationForcedOnCarriers`, équivalente à RH.
* La reconstruction exacte est déjà incluse dans tout porteur (c'est `localSynchronization` instancié) ; elle n'ajoute rien
  au porteur. Les contacts authentiques et la succession canonique sont satisfaits pour toute position radiale
  (`parameter_grid_admissible`, `grammaticalRaccordOf`). Le premier partagé n'entre dans le transport que multiplié par la
  différence des positions radiales, et le corpus ne contient aucune conservation du transport (§19.19).
* Donc la « contrainte sur la position radiale » demandée par P5 n'est fournie par aucune des quatre prémisses prise
  isolément, ni par leur conjonction telle que compilée. La relation supplémentaire est la constance d'amplitude relative
  par membre, nommée, équivalente à RH. Le plan ci-dessous ne la pose pas ; il la rend visible comme énoncé unique.

## 6. Pièces

* Rapports d'agents (lecture seule) : audit Lean (sections A à E) et audit `.md` (sections 1 à 5), résumés ci-dessus.
* Graphique analysé : `experiments/riemann_graphique.png` ; note d'analyse : `experiments/riemann_graphique_ANALYSE.md`.
* Plan : maître §19.21.
