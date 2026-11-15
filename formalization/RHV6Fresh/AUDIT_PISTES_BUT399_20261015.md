# Audit du projet et du but `:399` : les 136 rigidités relues dans l'ordre du but, inventaire des pistes, trois pistes retenues (2026-10-15)

Base : `main` à `3280137f` (E303). Aucun fichier Lean modifié par cet audit. Sources : `Terminal/DemonstrationChain.lean`
(but `:399`), `RHV6final_STRATEGIE_SEMANTIQUE.md` §12 (136 rigidités), `experiments/E301_AuditContradictoire/`
(classification par dépendances de preuve), `AUDIT_SOLUTION_20261005.md` §1–§81, `AUDIT_RADIAL_TOTAL_20261013.md`,
`CLOSURE_ROUTES_RADIAL_REASSESSMENT.md`, `AUDIT_DIFFERENCES_ON_OFF.md`, `AUDIT_INTERNE_CONCLUSION_20261003.md`, `git log`
(4 681 commits), bases `rhv3_lean` et Mathlib (périmètre d'import de RHV6Fresh).

Les probabilités de ce document sont des estimations argumentées, pas des mesures ; elles sont données pour comparer les
pistes entre elles. Aucune ne vaut comme évaluation de RH.

## 1. Le but `:399` : énoncé, hypothèses, nature logique

**Théorème ouvert** : `radial_conservation_anchored`, `Terminal/DemonstrationChain.lean:395–399`.

| Élément | Contenu |
|---|---|
| Hypothèses | `h₁` : premier membre canonique ON (démontré en amont, `N(15) = 1` certifié dans Lean) ; `p : e → l` passage consécutif ; `hE` hauteur positive ; `hV` la hauteur monte ; `hOn` départ ON ; `hHist` tout membre qui précède l'arrivée est ON. |
| Conclusion | `β_l = β_e`, c'est-à-dire `β_l = 1/2`. |
| Réduction compilée | côté haut `β_l > 1/2` exclu par le miroir (`passage_entry_radial_le_half`) ; reste `⊢ False` sous `hBelow : β_l < 1/2`, affiché comme `⊢ radialFactor l = 1` (`refine absurd ?_ (ne_of_gt hLambda)`). |
| Contexte (≈ 1 600 lignes) | comptage sur la ligne (`δ = 2ΔW ≥ 2` sous la rupture), fibre mixte classée, grammaire mod 6, raccord `M = p_min(e) = Occ(l)`, contacts (`0 < (1/2 − β_l)/(T_l² + 1/4) ≤ log λ_l ≤ (1/2 − β_l)/T_l²`), anneaux ON, champ du premier zéro, reconstruction exacte lissée, interactions complètes, fenêtres 12/24/36, estimations de retrait, comparaison signée (démontrée renversée), dominance du premier zéro, captivités sans supposer ON. |
| Contre-modèle du contexte | `β_l = 1/4` satisfait toutes les hypothèses réunies (`probe_consistency`, `reducedContactSystem_not_identifying`). |

**Nature logique, démontrée dans le build** :

- la loi « conservation du régime au passage authentique avec historique ON », quantifiée sur tous les passages, est
  équivalente à RH sous l'ancre (`riemannHypothesis_of_anchor_and_history_conservation`, `conservation_of_riemannHypothesis`,
  `riemannHypothesis_iff_no_first_regime_break`) ;
- la négation du but est exactement « il existe un premier changement de régime », c'est-à-dire ¬RH
  (`exists_first_regime_break`) ;
- les formes locales du but (fibre ON, `ΔD = 0`, miroir fixé, `λ = 1`, lecture ON des contributions, amplitude stable,
  transport du courant à deux contacts) sont des **caractérisations** deux à deux équivalentes (`regime_probes_equivalent`,
  `localOnScale_iff`, `amplitudeStableSync_iff`, `exact_current_transport_iff_radialFactor`) ; aucune n'est une hypothèse
  plus faible.

Conséquence pour cet audit : **fermer `:399` sans hypothèse ajoutée, c'est démontrer RH**. Les « chances de fermeture »
ci-dessous sont donc les chances qu'une piste apporte l'ingrédient analytique qui manque à une preuve de RH par cette voie,
pas les chances d'un lemme intermédiaire. Toute piste dont l'ingrédient est vrai dans le monde témoin `ζ(s−δ)ζ(s+δ)`
(même support premier, même grammaire, même équation fonctionnelle, poids `Λ(n)(n^δ + n^{−δ})`, tous les zéros hors ligne)
a une chance nulle par construction (`shiftedCompleted_one_sub`, R132–R134).

## 2. État du projet (mesuré)

| Indicateur | Valeur |
|---|---|
| Commits sur `main` | 4 681 (du 2026-09-21 au 2026-10-14) |
| Modules `Terminal/` | 158 ; annexe A des maîtres : 2 101 théorèmes RHV6Fresh (277 fichiers, 18 182 théorèmes avec les bases) |
| Expériences numériques | ≈ 300 (E075 → E303), toutes citées dans `AUDIT_SOLUTION_20261005.md` |
| Buts ouverts | 1 (`:399`) ; `SORRY=0`, `ADMIT=0`, axiomes standard ; signature 643740d74406 depuis E208 (2026-10-13) |
| Contraintes indépendantes de RH (type D) | les trois certificats de comptage `N(15) = 1`, `N(22) = 2`, `N(28) = 3` (`ZetaBox*`), et les 20 théorèmes « sans RH » de E301 (bande, `Re ρ ≤ 1`, symétries, `N = N₀ + 2W`, arrivée `≤ 1/2`, queue d'exposant 1) : **aucune n'exclut `β_l = 1/4`** |
| Caractérisations de `β = 1/2` ou ⟺ RH | 19 + 15 (E301) ; toutes exclues des hypothèses de fermeture |
| Contre-modèles compilés | `regimeWitness`, `engagedBreakWorld`, `shiftedCompleted δ`, `ReducedContactSystem`, `parameter_grid_admissible`, `winding_admissible_current_free`, CM1–CM13 |

Lecture : depuis le 2026-10-13 la signature du but n'a plus bougé malgré neuf campagnes (E208–E303, ≈ 25 modules
fermés). Les modules ajoutés sont des identités, des détecteurs ou des caractérisations ; aucun n'est une contrainte de
type D nouvelle. C'est le signe mesurable que les pistes internes au cadre (Tours, raccords, grammaire, synchronisation)
sont épuisées pour ce but.

## 3. Les 136 rigidités relues dans l'ordre du but

Ordre : du plus proche du but (sa propre réécriture) au plus éloigné (observations, témoins). Classe = classe majoritaire
des théorèmes porteurs lue sur les termes de preuve (E301, `rigidity_classes.csv` : 96 identités universelles, 13
observations sans théorème, 7 identifiabilités, 7 caractérisations de `β = 1/2`, 6 contraintes indépendantes, 2
conditionnels, 2 ⟺ RH, 1 définition, 1 fermeture conditionnelle, 1 contre-modèle). Doublons : R32 ≡ R50, R83 ≡ R93.

Bilan avant la liste : les seules rigidités utilisables comme **hypothèses** d'une fermeture sont celles de T1 (9) ; leur
conjonction, instanciée à l'arrivée, est satisfaite par `β_l = 1/4`. Celles de T0 (15) sont le but ; celles de T2 (7)
le supposent ; T3–T7 (91) sont vraies pour toute position radiale ; T8 (11) n'ont pas de théorème ; T9 (3) servent à
réfuter les lois candidates.

### T0 — forme du but, caractérisations de β = 1/2, équivalences avec RH (ne peuvent pas servir d'hypothèse)

| R | Classe E301 | Énoncé (SEM §12) | Rapport au but `:399` |
|---|---|---|---|
| 15 | caractérisation (⟺ β = 1/2) | Toute Tour est la Tour de ligne translatée ; facteur radial = 1 exactement sur la ligne. | réécriture du but ; exclue des hypothèses |
| 16 | identité universelle | Le résidu de changement tient dans une fenêtre ~ 1/T ; nul exactement sur la ligne. | réécriture du but ; exclue des hypothèses |
| 17 | caractérisation (⟺ β = 1/2) | La partie réelle a deux signatures et deux seulement : translation de grille, puissance d'amplitude. | réécriture du but ; exclue des hypothèses |
| 23 | caractérisation (⟺ β = 1/2) | Énergie propre par unité de largeur égale d'une cellule à la suivante exactement sur la ligne. | réécriture du but ; exclue des hypothèses |
| 25 | caractérisation (⟺ β = 1/2) | L'amplitude ramenée à √x est constante exactement sur la ligne. | réécriture du but ; exclue des hypothèses |
| 43 | identité universelle | Vertical ⟺ pas contracté ; horizontal ⟺ pas conservé ⟺ translation rigide. | réécriture du but ; exclue des hypothèses |
| 44 | conditionnel (hypothèse radiale) | Deux passages verticaux de suite forcent la ligne au membre commun. | réécriture du but ; exclue des hypothèses |
| 45 | identité universelle | Aucun changement de régime sur la ligne. | réécriture du but ; exclue des hypothèses |
| 48 | identité universelle | Un membre en ligne atteint verticalement est quitté verticalement. | réécriture du but ; exclue des hypothèses |
| 49 | identité universelle | À l'arrivée d'un vertical, facteur radial ≥ 1 ; ≤ 1 ⟺ régime gardé. | réécriture du but ; exclue des hypothèses |
| 55 | caractérisation (⟺ β = 1/2) | Miroir annulé exactement sur la ligne ; mouvement radial exactement s'il y a un hors-ligne. | réécriture du but ; exclue des hypothèses |
| 90 | caractérisation (⟺ β = 1/2) | Une dérive radiale porte `θ*` strictement au-dessus de 1/2. | réécriture du but ; exclue des hypothèses |
| 121 | caractérisation (⟺ β = 1/2) | Une Tour est une trajectoire : vitesse angulaire `T`, taux radial `d` ; rayon croît/décroît/constant ⟺ β ≷ 1/2. | réécriture du but ; exclue des hypothèses |
| 135 | caractérisation ⟺ RH | Prémisse unique, conservation + amorce, représentation en ligne, borne √x, exposant 1/2 : chacune ⟺ cible. | réécriture du but ; exclue des hypothèses |
| 136 | caractérisation ⟺ RH | La cible ⟺ absence de toute dette dans l'histoire exacte (`θ* = 1/2`) : caractérisée, non dérivée. | réécriture du but ; exclue des hypothèses |

### T1 — contraintes indépendantes de RH (seules entrées non circulaires)

| R | Classe E301 | Énoncé (SEM §12) | Rapport au but `:399` |
|---|---|---|---|
| 1 | identité universelle | Zéros non triviaux dans la bande ouverte ; existence par la théorie analytique. | en contexte du but ; satisfaite par β_l = 1/4 |
| 2 | contrainte indépendante | Un zéro hors ligne en donne quatre, de même multiplicité. | en contexte du but ; satisfaite par β_l = 1/4 |
| 3 | identité universelle | Le miroir d'un hors-ligne est distinct, même hauteur, partie réelle complémentaire. | en contexte du but ; satisfaite par β_l = 1/4 |
| 4 | contrainte indépendante | La ligne est le lieu fixe de la réflexion ; fonction complétée réelle sur la ligne. | en contexte du but ; satisfaite par β_l = 1/4 |
| 5 | contrainte indépendante | Un changement de signe de la fonction réelle garantit un membre en ligne. | en contexte du but ; satisfaite par β_l = 1/4 |
| 46 | contrainte indépendante | Un hors-ligne exige une entrée en régime horizontal, précédée d'un passage diagonal. | en contexte du but ; satisfaite par β_l = 1/4 |
| 87 | identité universelle | Le reste est borné par `C·x` depuis les premiers seuls ; bande fermée. | en contexte du but ; satisfaite par β_l = 1/4 |
| 88 | contrainte indépendante | L'exposant de croissance est entre 1/2 et 1. | en contexte du but ; satisfaite par β_l = 1/4 |
| 89 | contrainte indépendante | `max(β, 1−β) ≤ θ*`. | en contexte du but ; satisfaite par β_l = 1/4 |

### T2 — fermetures conditionnelles (hypothèse = conclusion du but ou plus forte)

| R | Classe E301 | Énoncé (SEM §12) | Rapport au but `:399` |
|---|---|---|---|
| 74 | fermeture conditionnelle | Le reste = tout en ligne + écart, qu'aucune repondération des membres en ligne n'imite. | ferme sous une hypothèse ⟺ but |
| 86 | conditionnel (hypothèse radiale) | Une croissance bornée du reste interdit tout exposant au-delà (lecture du pôle). | ferme sous une hypothèse ⟺ but |
| 125 | identité universelle | Champ du premier membre en ligne ; tout membre en ligne plus haut y reste ; membre + miroir dans le champ ⟹ en ligne ; « aucun ne dépasse » | ferme sous une hypothèse ⟺ but |
| 126 | identité universelle | Tour prisonnière de la précédente ; rapport = une puissance ; même β ⟹ dans le champ ; β fixé plus grand sort ; témoin ; prisonnière ⟹ haute | ferme sous une hypothèse ⟺ but |
| 127 | identité universelle | L'évasion se paie dans le reste ; mur démontré à l'exposant 1 ; règle `RemainderCaptive` (un côté ⟹ sommet ; deux ⟹ ligne) ⟺ cible ; témoin | ferme sous une hypothèse ⟺ but |
| 128 | identité universelle | Hiérarchie de Tour à Tour au raccord : entre deux ON la plus haute est plus faible, pas plus petit, phase plus rapide ; sur tout passage qui | ferme sous une hypothèse ⟺ but |
| 131 | identité universelle | Captivité locale au raccord exact (budget coût/disponible) ; ⟺ avance de hauteur ; chaîne : produit `≥ 1` ; transition première exacte ; lem | ferme sous une hypothèse ⟺ but |

### T3 — identités du passage, du raccord et du régime (vraies pour toute β)

| R | Classe E301 | Énoncé (SEM §12) | Rapport au but `:399` |
|---|---|---|---|
| 6 | identité universelle | Entre les deux hauteurs d'un passage, la fonction réelle ne s'annule pas et garde son signe. | en contexte ; ne lit pas β_l |
| 7 | identité universelle | Sur tout passage : place + 1, hauteur ne recule pas, occurrence avance strictement. | en contexte ; ne lit pas β_l |
| 8 | identifiabilité | Le membre suivant est unique et, depuis la ligne, fonction de la hauteur de départ seule. | en contexte ; ne lit pas β_l |
| 42 | identité universelle | Deux régimes de passage, vertical et horizontal, exclusifs et exhaustifs. | en contexte ; ne lit pas β_l |
| 47 | identité universelle | Sur la ligne, poussée horizontale nulle ; tout passage entre deux membres en ligne est vertical. | en contexte ; ne lit pas β_l |
| 50 | identité universelle | Le raccord existe et est unique sur tout passage, avec son transport exact. | en contexte ; ne lit pas β_l |
| 51 | identité universelle | Raccord orienté à hauteur croissante ; à même hauteur, transport > 1. | en contexte ; ne lit pas β_l |
| 52 | identité universelle | Charge radiale d'une fibre neutre exactement sur la ligne, signe fixé par deux écarts. | en contexte ; ne lit pas β_l |
| 53 | identité universelle | Registre = raccord + progression ; sommation d'Abel sur une chaîne. | en contexte ; ne lit pas β_l |
| 54 | identité universelle | Excès d'une transition : `= H` en ligne, `< H` diagonale, `> 0` même hauteur ; déficit remboursé. | en contexte ; ne lit pas β_l |
| 56 | identité universelle | Un changement de régime crée un mouvement radial et une jonction hors ligne. | en contexte ; ne lit pas β_l |
| 57 | identité universelle | Cellule VHV : membres centraux miroirs, phase verrouillée, charge jamais neutre. | en contexte ; ne lit pas β_l |
| 58 | identité universelle | Contacts de deux miroirs hors ligne ne coïncident jamais ; translation uniforme. | en contexte ; ne lit pas β_l |
| 59 | identité universelle | La seconde Tour est la première Tour du miroir lue à rebours ; existe aussi sur la ligne. | en contexte ; ne lit pas β_l |
| 60 | identité universelle | Depuis la ligne, la composante radiale de l'arrivée est portée par la seule position d'entrée, la même pour tout nombre. | en contexte ; ne lit pas β_l |
| 105 | identité universelle | Unité minimale : 4 membres, 3 passages, un premier partagé par passage, 3 premiers consécutifs. | en contexte ; ne lit pas β_l |
| 106 | identité universelle | La cellule consomme un rang sans hauteur nouvelle : 4 membres pour 3 hauteurs. | en contexte ; ne lit pas β_l |
| 107 | identité universelle | Membres centraux : même phase, amplitudes `(q/p)^{1/2∓d}` ; sommé sur un mot, extrémités seules. | en contexte ; ne lit pas β_l |
| 108 | identité universelle | Charge de la cellule `d(log(M₂/M₁) − log(M₃/M₂))`, impaire en `d`, bornée. | en contexte ; ne lit pas β_l |
| 130 | identité universelle | Double rigidité : liaison premiers–Tour sur tout passage ; lecture des écarts par la hauteur (différence seulement) ; énoncé de l'auteur « é | en contexte ; ne lit pas β_l |

### T4 — Tour, contacts, grille (vraies pour toute β)

| R | Classe E301 | Énoncé (SEM §12) | Rapport au but `:399` |
|---|---|---|---|
| 9 | identifiabilité | Une Tour par zéro, trace de son terme ; jamais deux zéros. | en contexte ; détecteur ou identité |
| 10 | identité universelle | Un contact à chaque demi-tour, sans fin, côté alterné. | en contexte ; détecteur ou identité |
| 11 | identité universelle | Le rapport de deux contacts consécutifs ne dépend que de la hauteur. | en contexte ; détecteur ou identité |
| 12 | identité universelle | Tout nombre positif a une cellule unique dans la Tour de tout zéro. | en contexte ; détecteur ou identité |
| 13 | identité universelle | L'origine canonique est obtenue sans premier, sans rang, sans comptage. | en contexte ; détecteur ou identité |
| 14 | identité universelle | Dans une même Tour, l'écart de position entre deux nombres ne dépend que de la hauteur. | en contexte ; détecteur ou identité |
| 18 | identifiabilité | Deux contacts consécutifs redonnent le zéro ; deux zéros distincts n'en partagent jamais deux. | en contexte ; détecteur ou identité |
| 19 | identité universelle | À numéro fixé, le contact descend quand la hauteur monte ; anneaux emboîtés. | en contexte ; détecteur ou identité |
| 20 | identité universelle | Un anneau de numéro fixé est vide de tout premier au-delà d'une hauteur finie. | en contexte ; détecteur ou identité |
| 21 | identité universelle | Au contact, la projection réelle du terme a la taille de son rayon. | en contexte ; détecteur ou identité |
| 22 | identité universelle | Une cellule est un demi-tour du terme propre ; incrément ≥ 2 C_k^β/‖ρ‖. | en contexte ; détecteur ou identité |
| 24 | identité universelle | Position et amplitude : deux coordonnées séparées (hauteur seule / partie réelle seule). | en contexte ; détecteur ou identité |

### T5 — formule explicite, unicité spectrale, identifiabilité

| R | Classe E301 | Énoncé (SEM §12) | Rapport au but `:399` |
|---|---|---|---|
| 61 | identité universelle | La Tour est le terme du zéro dans la formule explicite. | identité ou identifiabilité ; ne fixe pas β |
| 62 | identité universelle | La somme explicite ne dépend d'aucun ordre. | identité ou identifiabilité ; ne fixe pas β |
| 63 | identité universelle | L'organisme spectral reconstruit le reste exact et toute l'histoire première. | identité ou identifiabilité ; ne fixe pas β |
| 64 | identité universelle | Le reste arithmétique est défini par les seuls premiers ; poids = poids de l'événement. | identité ou identifiabilité ; ne fixe pas β |
| 65 | identité universelle | Le résidu arithmétique égale le résidu spectral. | identité ou identifiabilité ; ne fixe pas β |
| 66 | identité universelle | Aucun membre n'est retirable : son terme ne s'annule nulle part. | identité ou identifiabilité ; ne fixe pas β |
| 67 | identité universelle | Les profils d'exposants distincts sont indépendants. | identité ou identifiabilité ; ne fixe pas β |
| 68 | identité universelle | La décomposition en profils est unique, somme infinie comprise. | identité ou identifiabilité ; ne fixe pas β |
| 69 | identifiabilité | Toute représentation contient chaque zéro avec sa multiplicité ; aucun intrus n'a de poids. | identité ou identifiabilité ; ne fixe pas β |
| 70 | identifiabilité | `β`, `T`, `m` de chaque membre retrouvés dans toute représentation. | identité ou identifiabilité ; ne fixe pas β |
| 71 | identifiabilité | L'identité d'un hors-ligne n'est effacée par aucune compensation. | identité ou identifiabilité ; ne fixe pas β |
| 72 | identité universelle | Le canal se découpe en paquet de hauteur + complément ; compensation = complément. | identité ou identifiabilité ; ne fixe pas β |
| 73 | identité universelle | Entre deux événements, la différence du reste se lit côté premiers et côté zéros. | identité ou identifiabilité ; ne fixe pas β |

### T6 — grammaire première (aveugle à β)

| R | Classe E301 | Énoncé (SEM §12) | Rapport au but `:399` |
|---|---|---|---|
| 26 | identité universelle | L'occurrence est une étiquette de rang, injective. | aveugle à β ; fixe les sollicitations |
| 27 | identité universelle | Le minimum attendu est le premier qui suit l'occurrence ; deux membres distincts, deux minimums distincts. | aveugle à β ; fixe les sollicitations |
| 28 | observation / externe (aucun théorème) | La cellule de l'état propre est unique et contient le pivot. | aveugle à β ; fixe les sollicitations |
| 29 | identité universelle | L'occurrence du membre suivant est le minimum attendu du précédent. | aveugle à β ; fixe les sollicitations |
| 30 | identité universelle | Le comptage lu à tout contact est la fonction de Tchebychev en ce contact. | aveugle à β ; fixe les sollicitations |
| 31 | identité universelle | La grammaire reconstruite depuis les zéros est la grammaire première. | aveugle à β ; fixe les sollicitations |
| 32 | identité universelle | Le premier partagé d'un passage est unique et déterminé par le rang. | aveugle à β ; fixe les sollicitations |
| 33 | définition | Tout premier > 3 est dans l'un de deux états mod 6. | aveugle à β ; fixe les sollicitations |
| 34 | identité universelle | L'écart entre deux tels premiers n'a que trois classes. | aveugle à β ; fixe les sollicitations |
| 35 | identité universelle | Les changements d'état effectifs alternent : 2, 4, 2, 4. | aveugle à β ; fixe les sollicitations |
| 36 | identité universelle | Deux transitions consécutives avancent d'au moins six. | aveugle à β ; fixe les sollicitations |
| 37 | identité universelle | L'écart s'écrit d'une seule façon `6a + r` (écriture compilée ; vérification à 2·10⁶ numérique). | aveugle à β ; fixe les sollicitations |
| 38 | identité universelle | Magnitude et classe sont des fonctions du rang seul, aveugles à la partie réelle. | aveugle à β ; fixe les sollicitations |
| 39 | identité universelle | L'écart logarithmique entre deux premiers est la différence de leurs poids exacts. | aveugle à β ; fixe les sollicitations |
| 40 | identité universelle | Une Tour lit le même écart trois fois : demi-tours, amplitude, énergie. | aveugle à β ; fixe les sollicitations |
| 41 | identité universelle | Toute lecture cumulée le long d'une chaîne d'écarts se télescope. | aveugle à β ; fixe les sollicitations |
| 95 | identité universelle | Deux changements d'état consécutifs avancent de `6(a + a' + 1)`. | aveugle à β ; fixe les sollicitations |
| 96 | identité universelle | Retour à l'état de départ ⟺ avance ≡ 0 mod 6. | aveugle à β ; fixe les sollicitations |
| 97 | observation / externe (aucun théorème) | `#AB − #BA = 1[fin B] − 1[début B]`, ` | aveugle à β ; fixe les sollicitations |
| 98 | identité universelle | Dette énergétique d'une paire miroir sur un mot : `4d·log(q_m/q_0)`, non nulle exactement hors ligne. | aveugle à β ; fixe les sollicitations |

### T7 — réponse collective, énergie, courbure, captivité (identités ou détecteurs)

| R | Classe E301 | Énoncé (SEM §12) | Rapport au but `:399` |
|---|---|---|---|
| 75 | identité universelle | La demande d'une marche pure = poids du premier atteint − avance du fond. | identité/détecteur ; témoin W_δ la satisfait |
| 76 | identité universelle | L'écart entre dans la demande par magnitude et classe. | identité/détecteur ; témoin W_δ la satisfait |
| 77 | identité universelle | La réponse collective égale la demande sur toute marche. | identité/détecteur ; témoin W_δ la satisfait |
| 78 | identifiabilité | Carré de la réponse = diagonale + croisés. | identité/détecteur ; témoin W_δ la satisfait |
| 79 | identité universelle | Croisés forcés par la demande ; compensation nette ⟺ `D > S²`. | identité/détecteur ; témoin W_δ la satisfait |
| 80 | identité universelle | Des contributions de même signe ne se compensent pas. | identité/détecteur ; témoin W_δ la satisfait |
| 81 | identité universelle | La diagonale ne voit pas les signes. | identité/détecteur ; témoin W_δ la satisfait |
| 82 | identité universelle | Un monde de poids `±Λ` a même diagonale et même borne critique. | identité/détecteur ; témoin W_δ la satisfait |
| 83 | identité universelle | Une paire hors ligne pèse plus que la paire en ligne (forme nue compilée ; numérique sinon). | identité/détecteur ; témoin W_δ la satisfait |
| 92 | identité universelle | `Σ Λ²` a l'exposant critique depuis les premiers seuls. | identité/détecteur ; témoin W_δ la satisfait |
| 93 | identité universelle | Le paquet nu d'un membre et de son miroir ne descend pas sous la loi critique ; égalité sur la ligne. | identité/détecteur ; témoin W_δ la satisfait |
| 94 | identité universelle | Un membre déplacé n'émerge d'un reste critique qu'au-delà d'un horizon croissant avec la hauteur. | identité/détecteur ; témoin W_δ la satisfait |
| 109 | identité universelle | Le côté premier ne lit la profondeur d'une paire qu'à l'ordre 2 (paire en `d`). | identité/détecteur ; témoin W_δ la satisfait |
| 111 | identité universelle | Paire − double `= q^{s₀}κ_q(d)`, `κ ≥ (d log q)²`, croissante en `q`. | identité/détecteur ; témoin W_δ la satisfait |
| 112 | identité universelle | Toute lecture linéaire jusqu'à `X` sépare paire et double au plus de `κ_X(d)·Σ‖a_n‖√n`. | identité/détecteur ; témoin W_δ la satisfait |
| 113 | identité universelle | Paire en ligne serrée : courbure négative ; les deux continuations = signes d'un paramètre, sélectionné par rien. | identité/détecteur ; témoin W_δ la satisfait |
| 115 | identité universelle | Changement d'interaction = courbure × interaction du double ; paire en `d`. | identité/détecteur ; témoin W_δ la satisfait |
| 116 | identité universelle | Avec une Tour de hauteur différente, l'interaction du double change de signe au-delà de tout horizon. | identité/détecteur ; témoin W_δ la satisfait |
| 117 | identité universelle | Seul terme de signe fixe : le terme propre (radiale plus d'énergie, verticale moins). | identité/détecteur ; témoin W_δ la satisfait |
| 118 | identité universelle | Courbure verticale bornée `∈ [−4, 0]`, radiale non bornée ; signe fixé par la présence d'un membre à la hauteur (E160). | identité/détecteur ; témoin W_δ la satisfait |
| 119 | identité universelle | Paire invariante par la réflexion critique : écart recentré de carré réel ; classement d'un déplacement, rien sur la Tour. | identité/détecteur ; témoin W_δ la satisfait |
| 120 | identité universelle | À l'échelle √x, la Tour est invariante par opposition centrale / réflexion arithmétique / réflexion critique chacune ⟺ en ligne ; plan brut | identité/détecteur ; témoin W_δ la satisfait |
| 122 | identité universelle | Boucle miroir : Tour du miroir × étalon `g`, `‖g‖ = 1 ⟺ β = 1/2` ; sur toute famille stable, même famille (E162). | identité/détecteur ; témoin W_δ la satisfait |
| 123 | identité universelle | Paire miroir = deux trajectoires de dérives opposées ; différence nulle exactement en ligne ; le côté arithmétique de ζ ne voit que la somme | identité/détecteur ; témoin W_δ la satisfait |
| 124 | identité universelle | Variation d'énergie d'une fenêtre = excès propre `> 0` + 2⟨atome, complément⟩ ; reste fixé, le croisé devient la lecture du reste à la fréqu | identité/détecteur ; témoin W_δ la satisfait |
| 129 | identité universelle | Ce que les seuls paramètres fixent : comparaison = paramètres ; horizon garanti `(T_w/‖ρ₁‖)²` ; membre bas prisonnier pour toujours ; membre | identité/détecteur ; témoin W_δ la satisfait |

### T8 — observations numériques et résultats externes (aucun théorème)

| R | Classe E301 | Énoncé (SEM §12) | Rapport au but `:399` |
|---|---|---|---|
| 84 | observation / externe (aucun théorème) | Survie réglée par la magnitude (E137bis). | non compilée ; aucun rôle dans le but |
| 85 | observation / externe (aucun théorème) | Signes, phases ou ordre détruits : réponse ≠ demande (E137bis). | non compilée ; aucun rôle dans le but |
| 91 | observation / externe (aucun théorème) | Transport radial borné par `2θ − 1`. | non compilée ; aucun rôle dans le but |
| 99 | observation / externe (aucun théorème) | Maintiens moins fréquents et plus grands que les changements (E157). | non compilée ; aucun rôle dans le but |
| 100 | observation / externe (aucun théorème) | Régularité de ζ revient avec les magnitudes à leur rang (E157). | non compilée ; aucun rôle dans le but |
| 101 | observation / externe (aucun théorème) | Par canal, ζ plus régulière que le hasard ; compensations entre canaux (E157). | non compilée ; aucun rôle dans le but |
| 102 | observation / externe (aucun théorème) | > 2/3 des zéros asymptotiquement simples en ligne ; > 5/6 distincts (zeta23). | non compilée ; aucun rôle dans le but |
| 103 | observation / externe (aucun théorème) | Le côté premier borne ses hors-diagonale par `Σ` des carrés des poids (zeta23). | non compilée ; aucun rôle dans le but |
| 104 | observation / externe (aucun théorème) | Inégalité rang–trace tendue : double en ligne et paire proche coûtent le même prix (zeta23). | non compilée ; aucun rôle dans le but |
| 110 | observation / externe (aucun théorème) | Charge amplifiante ≈ 51,6 % ; défaut `∝ d²` ; horizon ≫ mot (E158). | non compilée ; aucun rôle dans le but |
| 114 | observation / externe (aucun théorème) | Comptage et signes de `Z` identiques pour paire et double ; horizon suit la courbure (E159). | non compilée ; aucun rôle dans le but |

### T9 — mondes témoins (garde-fous)

| R | Classe E301 | Énoncé (SEM §12) | Rapport au but `:399` |
|---|---|---|---|
| 132 | identité universelle | Le monde décalé a même support premier, même grammaire, poids positifs plus grands, tous zéros hors ligne. | réfute toute loi qui ne lit pas Λ(n) |
| 133 | identité universelle | Son poids ≥ 2Λ, carré ≥ 4Λ², égalité ⟺ δ = 0. | réfute toute loi qui ne lit pas Λ(n) |
| 134 | contre-modèle | Le monde de rupture engagée porte un membre en ligne puis deux jumeaux ; la fonction fixe sans premiers change de régime. | réfute toute loi qui ne lit pas Λ(n) |
## 4. Inventaire historique des pistes (toutes familles)

Chaque ligne : famille, ce qui a été compilé, le verdict compilé ou mesuré, et l'obstruction qui a arrêté la piste.
« ⟺ but » signifie que l'énoncé que la piste devrait fournir est une caractérisation du but ; « témoin » signifie que
l'ingrédient est vrai dans un monde témoin.

| # | Famille | Modules / expériences | Compilé | Obstruction |
|---|---|---|---|---|
| G1 | **Géométrique** : enroulement des Tours, contacts emboîtés, grille non translatée | `TowerWinding`, `EngagedNoTranslation`, `TowerTwoSidedRoom`, `SymmetricWinding`, `FirstZeroContactComparison`, E151, E200, E201 | emboîtement à l'infini pour toute `β` ; fenêtre `1 ≤ λ < e^{1/(2T²)}` ; comparaison au premier zéro = identité à trois termes | vrai pour toute `β` (`windingNestedAtInfinity_of_precedes`) ; `λ = 1` ⟺ but ; grille décalée admissible (`parameter_grid_admissible`) |
| G2 | **Géométrique** : symétrie de la Tour, quatre secteurs, anneaux ON, dominance du premier zéro | `EngagedAllConstraints`, `TowerFourSectors`, `OnRadialRing`, `FirstZeroDominance`, E161, E163b | symétrie centrale ⟺ `β = 1/2` ; anneau exact entre membres ON ; étage de dominance ⟺ ON | caractérisations ; l'étage de l'arrivée est le but |
| G3 | **Cinématique** : registre, Abel, excès de transition, écarts lus par la hauteur | `GrammarKinematics`, `DoubleRigidity`, E142 | identités télescopiques vraies pour toute `β` ; `ΔT_min` est une équation | aucune borne inférieure sur l'avancée de hauteur (passage de même hauteur admis) |
| A1 | **Grammaire première** : mod 6, magnitudes, fenêtres 12/24/36, planchers `3m` | `Grammar/*`, `WindowProgression`, `GrammarWordLoad`, `FiniteGrammarLayer`, E157, E183, E187, E190 | classes et planchers compilés ; verrou `|#AB − #BA| ≤ 1` | fonctions du rang seul, aveugles à `β` (`pointed_primes_rank_only`, `gap_signature_constraint_vacuous`) ; les données ne contiennent pas `d` (E232) |
| A2 | **Arithmétique** : lecture du reste sans zéro, exposant `θ*`, poids exacts `Λ(n)` | `ArithmeticReading`, `RemainderExponent`, `RemainderEnergy`, `ExactAxisReading`, `CompensationRigidity`, E150, E153–E155, E137bis | `1/2 ≤ θ* ≤ 1` depuis `Λ ≥ 0` + Chebyshev ; RH ⟺ `θ* = 1/2` ; diagonale critique `ΣΛ² ≤ C x log x` | seule la **taille exacte** des poids sépare du témoin ; il manque la borne quadratique critique à toute résolution (`Tr` borné), de nature von Koch |
| A3 | **Arithmétique locale** : blocs premiers, transitions, cellules `ϑ₃ − M`, voie `ϑ` | `PrimeBlockDecomposition`, `PrimeTransitionDecomposition`, `PrimeCellError`, E193, E194 | blocs à l'exposant `1 + 1` ; `prime_blocks_iff_zero_free` | la borne demandée est une bande sans zéro sur tous les zéros ; rien dans Mathlib/rhv3_lean au-delà de Chebyshev |
| E1 | **Énergétique** : énergie quadratique, cellules de Tour, `Tr × Dw` | `RemainderEnergy`, E154 | `Dw` borné compilé ; `Tr` invariant ζ/`W_δ` | `Tr` borné à toute résolution non dérivé, porte toute la difficulté |
| E2 | **Énergétique** : loi de rappel harmonique, courant, énergie stationnaire | `HarmonicRestoringLaw`, `HarmonicCurrentTransport`, `HarmonicCrossCurrent`, `ExactSignalArchitecture`, E224–E230, E239–E242 | `E' = 2dE` ; mode borné ⟺ `d = 0` ; transport du courant ⟺ `λ = 1` | caractérisations ; contre-modèle `Λ(s−δ)Λ(s+δ)` ; Lagarias `Re ξ'/ξ > 0` ⟺ RH (E227) |
| E3 | **Énergétique** : variation quadratique locale, paire contre double, courbure | `QuadraticVariation`, `PairCurvature`, `PairInteraction`, E159, E160 | excès propre `≥ 0`, nul ⟺ `d = 0` ; terme croisé libre | « déterminer le terme croisé = lecture du pôle, le borner = croissance critique [⟺ RH] » (audit 2026-10-03) |
| S1 | **Spectrale** : unicité, insertion exclue, remplacement | `SpectralUniqueness`, `InsertionExclusion`, `AmplitudeStableSynchronization`, E186, E244 | toute insertion/remplacement casse la reconstruction | aveugle à la position radiale ; n'exclut pas un OFF **authentique** |
| S2 | **Synchronisation** : par écart, locale (C126), collective | `GapSynchronization`, `LocalPrimeGapSynchronization`, `SynchronizationAudit`, E243, E264–E303 | loi par écart démontrée pour toute famille ; rigidité identifie toute `β` | linéarité ; queue générique ; borne d'exposant 1 non discriminante (`tail_bound_admits_offline_point`) |
| C1 | **Comptage** : `N = N₀ + 2W`, pas de comptage, boîtes certifiées 15/22/28 | `CountingDeficit`, `LineCountingDefect`, `BoxCount*`, `ZetaBox*`, E174, E176, E185, E208, E210 | déficit entier, monotone ; `N(T_l) < N(T_e) + 2 ⟹ λ = 1` ; trois premiers zéros ON **dans Lean** | seule famille à contrainte de type D ; locale, non transportée ; le pas de comptage exige la simplicité (plus fort que RH) |
| C2 | **Comptage** : induction du régime ON, invariant indépendant | `OnRegimeInduction`, `RegimeTransportAudit`, E208–E217 | parité des fibres ; `ΔD = 0` quantifié ⟺ RH | aucun invariant indépendant trouvé |
| P1 | **Premier zéro, captivité, gain collectif** | `FirstZeroField`, `FixedExponentField`, `FirstGainPremise`, `CanonicalEnumeration`, `CaptivityWithoutOn`, E164–E184 | `hDom ⟹ RH` ; prémisse réduite au miroir ; captivité des membres bas et ON par théorème | raccord `hGain ⟹ hDom` non dérivé ; captivité universelle ⟺ RH ; E184 : la prémisse ne lit pas une sortie du champ |
| R1 | **Reconstruction par fenêtres** : séparation, estimation de retrait, comparaison signée | `GrammarWindowSeparation`, `GrammarWindowEstimate`, `SignedWindowComparison`, `RemovalExponent`, `CertifiedRemoval`, `WindowComparison`, E195–E199 | identités de fenêtre ; comparaison signée **démontrée renversée** pour toute fenêtre | exposant du retrait ⟺ bande sans zéro au-dessus de `H` ; la grammaire ne borne pas `R` |
| R2 | **Fond `li`, cellules de comptage, registre des écarts** | `BackgroundModulation`, `StageCell`, `CountingFieldContacts`, `PrimeGapLedger`, `ContactSensitivity`, E188, E189, E204–E207 | modulation = dérivée de la contribution brute ; attendu de la fibre = `R − P − Q`, queue à l'exposant 1 | « fibre `≤ C√x` ⟹ fibre ON » = forme exacte du but ; borne de `Q` à coupure fixée d'exposant `< 1` non dérivée |
| X1 | **Formulations analytiques externes** : Lagarias, Weil, Li, Hilbert–Pólya, noyaux positifs, de Bruijn–Newman | E226–E228, `HarmonicRestoringLaw` (contre-modèle) | — | toutes ⟺ RH ; noyaux positifs à zéros non réels existent ; opérateur non défini sans les zéros |
| X2 | **Résultats inconditionnels classiques importables** : région sans zéro, densité locale `O(log T)`, Backlund, Rosser, proportions (Selberg/Levinson/Conrey), zeta23 | `thm_localZeroDensity_le_log` (rhv2, hors périmètre), Kadiri/Backlund (rhv3), zeta23 (externe) | densité locale, majorant crude `N(T) ≤ A T^{3/2}`, Hadamard | aucun ne borne une seule partie réelle sous 1 ; les proportions sont asymptotiques ; zeta23 aveugle à une paire |

Constat transversal : toutes les pistes aboutissent à l'une de trois formes, **toutes démontrées équivalentes à RH** :
(i) borne du reste des premiers d'exposant `< 1` uniforme (von Koch, bande sans zéro) ; (ii) captivité/domination universelle
par le premier zéro ; (iii) lecture de `N₀` égale à `N` à toute hauteur. Les 48 différences ON/OFF connues
(`AUDIT_DIFFERENCES_ON_OFF.md`) se classent de même : lecture, poids, ⟺ RH, conditionnel ; seule la couche du poids exact sépare.

## 5. Tableau comparatif des pistes de fermeture

Chance = probabilité estimée que la piste, poussée à fond, ferme `:399` sans hypothèse ajoutée (donc démontre RH). Rendement
partiel = ce que la piste produit même si elle ne ferme pas. Les pistes sont classées par chance décroissante puis par
rendement partiel.

| Rang | Piste | Ingrédient manquant exact | Chance de fermeture | Avantages | Inconvénients | Rendement partiel | Coût |
|---|---|---|---|---|---|---|---|
| 1 | **C1+ Comptage sur la ligne, lecture de `N₀` indépendante des zéros** (prolonger `δ = 2ΔW = 0` de bande en bande ; forme locale `N(T_l) − N(T_e)` = multiplicité d'un seul point ON) | une minoration **uniforme** de `N₀(T) − N₀(H)` par `N(T) − N(H)` ; en pratique : argument de Turing/Backlund rendu uniforme, ou une lecture du signe de `Z` propre à ζ (pas aux témoins) | **≈ 3 %** | seule famille à contrainte de type D dans le dépôt ; réduction compilée sans perte (`lineDefect_invariant_iff_riemannHypothesis`, `passage_count_step_lt_two_iff`) ; générateur de certificats (`ZetaBox*`) déjà opérationnel ; chaque bande certifiée est un théorème Lean définitif | le pas de comptage `< 2` exige la simplicité (plus fort que RH) ; la version uniforme est RH ; Turing ne donne jamais mieux qu'un certificat fini ; le texte « un OFF ajouterait +2 » est circulaire comme dérivation | **100 %** pour toute hauteur finie : premier zéro OFF repoussé aussi loin que la machine le permet (`T ≤ 10³`–`10⁴` réalistes avec le générateur e192/e196) | moyen (générateur existant ; coût machine croissant en `T log T`) |
| 2 | **A2+ Borne critique du reste depuis les poids exacts `Λ(n)`** (route `Λ → reste lissé → θ* → β` ; cible intermédiaire : `Tr` borné à toute résolution, corrélations des poids signés) | une inégalité **démontrée** sur `Σ_{n ≤ x} Λ(n)·n^{−iT}` ou sur `Σ Λ(n)Λ(n+h)` à l'échelle `π/T`, fausse pour `W_δ`, d'exposant `< 1` | **≈ 2 %** | c'est la **seule couche qui sépare ζ des témoins** (compilé : `shiftedWorld_weight_eq_iff`, `signedWorld_diagonal_linear`) ; objet exact et sans zéro (`riemannHypothesis_iff_remainder_sqrt_growth`) ; toute avancée partielle (`θ < 1`) serait une bande sans zéro inconditionnelle, résultat majeur | aucun résultat inconditionnel connu ne descend sous l'exposant `1 − ε(x)` (région de la Vallée Poussin) ; la diagonale `ΣΛ²` ne contrôle pas le transfert (E155) ; exige une théorie des corrélations de `Λ` hors de portée de Mathlib | faible pour `:399` ; élevé scientifiquement si un exposant `< 1` tombe | élevé (analyse nouvelle, pas de base Lean) |
| 3 | **E2+/X1 Positivité de la formule explicite sur une classe de fonctions test fixée par la structure des Tours** (Weil, ou `Re ξ'/ξ ≥ 0` sur `σ > 1/2`, restreint aux fonctions `e^{(β−1/2)u}cos(Tu − φ)` tronquées aux cellules) | la positivité `Σ_ρ ĥ(ρ) ≥ 0` pour les seules fonctions test que le cadre produit (noyaux de cellule), **démontrée depuis le produit eulérien** et fausse pour `W_δ` | **≈ 2 %** | vocabulaire de l'auteur (énergie, courant, synchronisation) exactement formalisable ; outils déjà compilés (formule explicite lissée, `ExactSignalArchitecture`, `GapSynchronization`) ; E227 a compilé la forme `Re ξ'/ξ = Σ(σ−β)/|s−ρ|²` | toutes les formes connues sont ⟺ RH (Weil, Lagarias, Li) ; les noyaux positifs à zéros non réels existent (E226) ; une restriction de la classe de test qui resterait vraie ne décide pas | moyen : fournit un critère quantitatif par fenêtre déjà numériquement vérifié (E224, E303) | élevé |
| 4 | P1 Dominance du premier zéro / gain collectif (`hGain ⟹ hDom`) | borne uniforme des sommes oscillantes `Σ cos((T_n − T_1) log p − Δφ)` sur fenêtres de battement | ≈ 1 % | fermeture `hDom ⟹ RH` compilée ; prémisse réduite au miroir ; rangs bas captifs par théorème | captivité universelle ⟺ RH ; E184 : la prémisse ne lit pas une sortie du champ, seul le défaut de reconstruction la lit | faible | moyen |
| 5 | X2 Import de résultats inconditionnels (région sans zéro de la Vallée Poussin, densité `O(log T)`, Backlund, proportions) | aucun ne touche `β_l < 1/2` | ≈ 0,5 % pour `:399` | ajoute des contraintes de type D au dépôt ; `thm_localZeroDensity_le_log` déjà prouvé dans rhv2 (hors périmètre) | exclus du périmètre (rhv3 seul) ; les proportions sont asymptotiques et aveugles à une paire | moyen (hygiène du dépôt) | moyen |
| 6 | E3 Courbure, paire contre double, terme croisé | borne du terme croisé | ≈ 0,5 % | mesure de séparation exacte, ordre `d²` | « le borner = croissance critique » (audit 2026-10-03, voie B close) | nul | — |
| 7 | R1/R2 Fenêtres, retrait, fond `li`, cellules | borne de `Q_H` à coupure fixée d'exposant `< 1` | ≈ 0,5 % | identités fines, canal `J` exploré | ⟺ bande sans zéro au-dessus de `H` ; comparaison signée démontrée renversée | nul | — |
| 8 | S1/S2 Unicité spectrale, insertion, synchronisation | — | **0 %** | identités et identifiabilité exactes | aveugles à `β` (compilé : `rigidity_identifies_any_radial`, `tail_bound_any_family`) | nul | — |
| 9 | G1/G2/G3 Enroulement, contacts, grille, symétrie, cinématique | — | **0 %** | géométrie entièrement formalisée | vraies pour toute `β` ou ⟺ but ; contre-modèles compilés (`parameter_grid_admissible`, `winding_admissible_current_free`, `reducedContactSystem_not_identifying`) | nul | — |
| 10 | A1 Grammaire mod 6, fenêtres, canaux | — | **0 %** | planchers exacts | fonctions du rang seul ; données sans `d` | nul | — |
| 11 | E1 Énergie quadratique `Tr × Dw` | `Tr` borné à toute résolution | se confond avec le rang 2 | — | — | — | — |
| 12 | X1 Hilbert–Pólya, de Bruijn–Newman, noyaux | un opérateur ou un noyau défini sans les zéros | < 0,5 % | — | circulaire sans objet indépendant (E228) | nul | très élevé |

## 6. Les trois pistes retenues, programme et critère d'arrêt

### Piste 1 — Comptage sur la ligne : lecture de `N₀` et prolongement du déficit nul

- **Objet** : `zeroCountDeficit T = N(T) − N₀(T) = 2W(T)` (`CountingDeficit`, `LineCountingDefect`). Sous `hHist`,
  `W(T) = 0` pour `T < T_l` ; le but équivaut à `W(T_l) = 0`, c'est-à-dire `ΔD(T_e, T_l) = 0` (`regime_probes_equivalent`).
- **Ce qui est acquis** : `N(15) = 1`, `N(22) = 2`, `N(28) = 3` dans Lean ; pas de comptage `lowCount_eq_zero_of_count_step` ;
  rectangles de droite `σ' → 1/2⁺` d'enroulement nul ⟹ `δ = 0` (`LineCountingDefect`) ; Turing local suffisant.
- **Programme** : (1) remplacer le pas de comptage `N(T_l) < N(T_e) + 2` (exige la simplicité) par la forme exacte
  `fibre(T_l) = m_ζ(1/2 + iT_l)` (« premier raccord analytique ouvert », §64) ; (2) chercher une **minoration de `N₀`**
  propre à ζ : changements de signe de `Z` lus par la formule de Riemann–Siegel tronquée avec reste explicite (Gabcke) ;
  (3) à défaut, industrialiser le générateur de boîtes (`e192`, `e196`) pour certifier `W(T) = 0` jusqu'à `T ≈ 10³`,
  puis `10⁴`, chaque bande étant un théorème Lean définitif.
- **Critère d'arrêt** : si la minoration de (2) n'est pas démontrable sans supposer l'absence de paire (ce que l'audit
  §64 et E210 indiquent déjà : « saut `+2` de `S(T)` exclu par aucune borne »), la piste se réduit à (3), qui ne ferme
  jamais `:399`.
- **Ce qu'il ne faut pas refaire** : réintroduire le pas de comptage comme dernier sous-but (retiré §63) ; confondre
  `N₀` et les changements de signe de `Z` ; présenter « un OFF ajouterait +2 » comme dérivation.

### Piste 2 — Borne critique du reste depuis les poids exacts `Λ(n)`

- **Objet** : `smoothedRemainder` (premiers seuls) ; RH ⟺ `∃ C, ‖R(x)‖ ≤ C√x` (`riemannHypothesis_iff_remainder_sqrt_growth`) ;
  forme intermédiaire ouverte : `∃ θ < 1, ∃ C, ‖R(x)‖ ≤ C x^θ` (bande sans zéro inconditionnelle, `prime_blocks_iff_zero_free`).
- **Ce qui est acquis** : exposant 1 (`smoothedRemainder_linear_growth`) ; diagonale critique `ΣΛ² ≤ C x log x` ;
  `Dw` borné ; témoins : `w_δ ≥ 2Λ`, égalité ⟺ `δ = 0` ; mondes à signes cohérents (E155) : exposant 1,58.
- **Programme** : (1) formaliser la décomposition `Tr × Dw` à résolution `π/T` et isoler l'énoncé exact « `Tr` borné » ;
  (2) viser un exposant `θ < 1` quelconque par une méthode de la Vallée Poussin **lue sur les poids** (produit eulérien,
  `3 + 4cos + cos 2θ`) : cela donne classiquement `θ = 1 − c/log x`, pas un exposant fixe ; vérifier si le cadre des
  cellules (`π/T`) permet une inégalité de grande valeur à résolution fixée ; (3) à chaque étape, tester contre `W_δ`.
- **Critère d'arrêt** : toute borne obtenue qui reste vraie pour `W_δ` est à jeter ; toute borne qui n'atteint pas un
  exposant fixe `< 1` ne réduit pas `:399`.
- **Ce qu'il ne faut pas refaire** : positivité/Landau comme source de l'exposant (E153) ; `Li` comme contenu de cellule
  (E155) ; « le carré élimine les compensations » (E154).

### Piste 3 — Positivité de la formule explicite sur les noyaux du cadre

- **Objet** : pour un noyau réel `h` de transformée `ĥ`, `Σ_ρ ĥ(ρ) = ĥ(0) + ĥ(1) − Σ_n Λ(n) n^{−1/2}(h(log n) + h(−log n)) + …`
  (formule de Weil ; dans le dépôt : `smoothedRemainder_eq_tsum_residueTerm`, `prime_gap_synchronization`). RH ⟺ positivité
  pour tous les `h = g * g̃`.
- **Ce qui est acquis** : contributions par écart et par cellule exactes pour toute `β` (`GapSynchronization`,
  `LocalPrimeGapSynchronization`) ; énergie des modes `E' = 2dE` ; `Re ξ'/ξ = Σ(σ−β)/|s−ρ|²` (E227) ; noyau de Riemann vérifié,
  noyaux positifs à zéros non réels (E226).
- **Programme** : (1) écrire la forme de Weil dans Lean depuis la formule explicite lissée (le canal lissé est le seul
  démontré) ; (2) restreindre la classe de test aux noyaux produits par les cellules de Tour (`e^{(β−1/2)u}cos(Tu − φ)` fenêtré)
  et calculer le côté premier **exactement** ; (3) chercher pour quels noyaux la positivité découle du produit eulérien
  seul (termes `Λ(n)` de signe fixe), et vérifier qu'elle est fausse pour `W_δ`.
- **Critère d'arrêt** : si la positivité démontrable depuis le produit eulérien reste vraie pour `W_δ` (ce qui est le cas
  de toute positivité à poids `Λ ≥ 0`, E153), la piste ne décide pas et doit être close.
- **Ce qu'il ne faut pas refaire** : présenter la stationnarité de l'énergie ou la bornitude du mode comme une loi
  (caractérisations du but, E224–E230) ; invoquer le théorème spectral sans opérateur défini sans les zéros.

## 7. Verdict

| Ligne | Valeur |
|---|---|
| NATURE_DU_BUT_399 | ⟺ RH sous ses hypothèses (compilé : `riemannHypothesis_iff_no_first_regime_break`) |
| RIGIDITÉS_UTILISABLES_EN_HYPOTHÈSE | 9 (T1) ; conjonction satisfaite par `β_l = 1/4` |
| RIGIDITÉS_QUI_RÉÉCRIVENT_LE_BUT | 15 (T0) ; 7 ferment sous une hypothèse ⟺ but (T2) |
| PISTES_À_CHANCE_NULLE_COMPILÉE | géométrie (G1–G3), grammaire (A1), spectrale et synchronisation (S1–S2) |
| PISTES_RETENUES | 1. comptage sur la ligne (≈ 3 %, rendement partiel 100 % à hauteur finie) ; 2. borne critique du reste depuis `Λ(n)` (≈ 2 %) ; 3. positivité de la formule explicite sur les noyaux du cadre (≈ 2 %) |
| CONDITION_COMMUNE | un ingrédient analytique **faux dans `ζ(s−δ)ζ(s+δ)`**, donc lisant la taille exacte des poids `Λ(n)` ; aucune piste interne au cadre (Tours, raccords, grammaire, synchronisation) ne le fournit |
| RH_FOUND | FALSE ; `lake build RHV6Fresh` : une erreur, `:399`, signature 643740d74406 |
