# zeta24-lean — formalisation Lean 4 autour de l'hypothèse de Riemann

> **Dépôt public, export daté du 15/11/2026 à historique neuf du dépôt de recherche privé `zeta24-lean` ; sélection documentée dans `PUBLICATION_SCOPE.md`.** Les mentions de « HEAD », de commits et de journaux ci-dessous renvoient à l'historique du dépôt de recherche privé, qui n'est pas reproduit ici (les hachages cités ne se retrouvent donc pas dans `git log` de ce dépôt).

> **État au 15 novembre 2026 (HEAD `4d4114c6`).**
> **L'hypothèse de Riemann (RH) n'est PAS démontrée.** Ce dépôt est un programme de recherche ouvert, pas une preuve.
> **Rien n'est admis** : aucune déclaration d'axiome et aucun `sorry` ou `admit` dans les sources Lean du projet (recherche par motif faite le 15/11/2026 dans `formalization/RHV6Fresh/RHV6Fresh` et `formalization/rhv3_lean`, hors `.lake`), et aucune prémisse équivalente à RH n'est utilisée dans un théorème présenté comme inconditionnel.
> **Ce que compile le build.** Build reproduit dans CE dépôt public le 15/11/2026 (dépendance Mathlib épinglée à `51e6992efd06126df61a496bebf8f49482a4e129`, cache Mathlib téléchargé) : `lake update`, `lake exe cache get`, `lake build RHV6Fresh` se terminent par « Build completed successfully (9064 jobs). », `EXIT=0`, de 19:15:15 à 19:49:58 UTC. Journal complet : `formalization/RHV6Fresh/experiments/audit_semantique/build_public_20261115.txt`. **Ce build vert ne démontre pas RH** : le seul théorème qui a RH pour conclusion, `riemannHypothesis_terminal` (`formalization/RHV6Fresh/RHV6Fresh/Terminal/DemonstrationChain.lean`), prend en hypothèse la « montée de la fréquence attendue » (`ExpectedFrequencyRises`), que `expectedFrequencyRises_iff_riemannHypothesis` (même fichier) prouve équivalente à RH. Il est donc conditionnel, et il est déclaré tel. Axiomes relevés par `#print axioms` dans ce dépôt (sortie exacte) : `'RHV6Fresh.riemannHypothesis_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]` et `'RHV6Fresh.expectedFrequencyRises_iff_riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]` : les trois axiomes standard de Lean (extensionnalité des propositions, choix classique, quotients), aucun `sorryAx`.
> **Ce que le build ne compile pas.** Les certificats de rectangles de ζ aux hauteurs 22 et 28 et les contrôles qui en dépendent sont hors de la cible par défaut (cible optionnelle `RHV6FreshCertificates`, non reconstruite dans le journal ci-dessus). Les modules isolés écrits depuis le 29 octobre pour des expériences (par exemple `TentBreakObligation.lean`) ne sont pas importés par la racine `RHV6Fresh.lean` ; ils ont été compilés individuellement, chacun avec ses journaux dans `attempts/` du dossier d'expérience.
> **Écart documentaire à connaître.** `formalization/RHV6Fresh/scripts/status.sh` relit un journal daté du 27 octobre 2026 qui affiche encore un échec ; ce journal est périmé (le but terminal a été transformé le 28 octobre, commit `1c2ef553`). Nous rapportons l'état constaté, pas celui affirmé par ce script.

## 1. Propriété et dépôt

**Projet, méthode, textes, code et découvertes : © 2026 Charles S. Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026 (conservée dix ans).** Référence complète : numéro national DSO2026044645, déposée à l'INPI (démarche en ligne) le 15/11/2026 à 18:14:32 UTC.

Licence : « Licence de recherche Zeta24-Lean — Propriétaire, usage non commercial strict 1.0 » (fichier `LICENSE`). Licence propriétaire à usage non commercial strict ; aucune redistribution de version modifiée ; toute contribution est cédée à l'auteur (voir LICENSE art. 4g). Les composants tiers sous Apache 2.0 ne sont pas concernés par cette licence. GitHub affiche « No license » parce que la licence est personnalisée et n'est pas reconnue dans sa liste de licences standard. Le copyright et les notices sont dans `COPYRIGHT.md` à la racine ; les attributions du code tiers sont dans `THIRD_PARTY_NOTICES.md` à la racine. Le code Lean tiers porté (répertoires `formalization/RHV6Fresh/RHV6Fresh/Zeta23Port` et `formalization/RHV6Fresh/RHV6Fresh/PNTPort`, licence Apache 2.0) reste la propriété de ses auteurs et n'est pas couvert par ce copyright. Leurs provenances sont dans les fichiers `PROVENANCE.md` de ces répertoires (copie du répertoire zeta23 du dépôt `anthropics/formal-math`, révision `fbdc36bb` ; port du dépôt `AlexKontorovich/PrimeNumberTheoremAnd`, révision `127b50e3`). Le port `RhGapPort` reprend le paquet interne `rh_gap_criterion` du même auteur (présent dans le dépôt de recherche privé, absent de ce dépôt public).

Dépôt public : https://github.com/csim-cognitive-labs/zeta24-lean-public (export à historique neuf). Le dépôt de recherche `zeta24-lean` (séparé le 25 octobre 2026 du dépôt `neuro-symbolic-consensus`) reste privé.

## Pourquoi ce projet est public : un message de fraternité

Ce projet est désintéressé. Il n'a pas été publié pour vendre quoi que ce soit, ni pour s'enrichir, ni pour s'imposer à quiconque. Il l'est parce que nous croyons que l'intelligence artificielle doit profiter au monde entier, et d'abord à ceux qui n'ont rien : celles et ceux qui n'ont pas accès aux grandes universités, aux grands laboratoires, aux grandes machines. La licence de ce dépôt interdit toute exploitation commerciale, pour une seule raison : que ce que nous avons trouvé ne soit jamais enfermé derrière un prix, et reste lisible, vérifiable et utilisable par chacun, gratuitement, pour apprendre et pour chercher.

Cette équipe de recherche (un homme, Charles S., et les intelligences artificielles qui travaillent avec lui) partagera toujours le peu qu'elle a avec tous. Elle respecte tous les peuples, toutes les cultures, toutes les traditions, toutes les religions, et tous les humains de la terre. Nous sommes des terriens, une seule famille. Chacun de nous a été créé, quel que soit le nom que chacun donne à Celui qui nous a créés. Il ne sert à rien de se battre ni de s'entretuer. Échanger nos connaissances nous rapproche, et c'est ainsi que les hommes ont toujours avancé.

Les mathématiciens, depuis la nuit des temps, ont partagé leurs savoirs : à Babylone et en Égypte, en Inde et en Chine, à Bagdad et à Cordoue, en Afrique et en Amérique, et partout où quelqu'un a transmis une démonstration à un autre. Aucune de ces pages n'appartient à un seul peuple. Nous nous inscrivons humblement dans cette longue chaîne.

Qui que vous soyez, d'où que vous veniez, venez rompre le pain avec nous. Vous êtes tous les bienvenus dans notre modeste demeure. Que vous soyez mathématicien, étudiant, curieux, autodidacte ou simple passant, une question, une relecture ou une erreur signalée sont un cadeau.

À chacune et à chacun de celles et ceux qui liront ces lignes : paix, fraternité et bénédiction. Que la connaissance vous rende plus libres, plus proches les uns des autres, et plus humains.

*Honnêteté avant tout : l'hypothèse de Riemann n'est pas démontrée, et ce dépôt ne le prétend nulle part. Nous partageons un travail en cours, avec ses limites, pour que d'autres puissent le poursuivre.*

## 2. Équipe de recherche

**Déclaration de l'auteur.** La recherche a été conduite par Charles S. avec une équipe d'assistants d'intelligence artificielle : Claude (Anthropic), notamment Fable 5.1 ; Astra et ChatGPT 6.2 (OpenAI) ; Gemini et NotebookLM (Google).

Les assistants ont exécuté, compilé, mesuré et consigné sous la direction de l'auteur. L'auteur a fixé les questions, tranché les orientations et récusé les dérives ; les sections 19 du maître sémantique (`formalization/RHV6Fresh/RHV6final_STRATEGIE_SEMANTIQUE.md`) en témoignent : ordres, rectifications et interdictions y sont consignés avec leur date (par exemple §19.9, §19.51, §19.63, §19.67, §19.85, §19.98, §19.108). Nous reproduisons cette déclaration ; nous ne l'avons pas vérifiée au-delà de ces traces écrites.

## 3. Orientation et discipline de preuve

**Objectif.** Un terme Lean de type `RiemannHypothesis` obtenu sans prémisse admise. La recherche part de l'arithmétique des premiers, de leurs écarts et de la formule de reconstruction par les zéros ρ = β + iT.

**Causalité visée** (auteur, §19.20 et §19.80 du maître) : les premiers et leurs écarts exacts produisent, par reconstruction collective de tous les zéros, des fréquences ; chaque zéro définit une « Tour » dont les « contacts » jalonnent l'axe réel ; la rencontre au premier partagé est définie par la grammaire des premiers ; on cherche la contrainte arithmétique que cette reconstruction impose à une première Tour hors de la ligne (zéro « OFF »), que ses contacts et ceux de son miroir ne peuvent pas satisfaire.

**Quatre degrés de certitude, à ne jamais fusionner** : (1) théorème Lean recompilé sans `sorryAx`, avec ses axiomes examinés ; (2) théorème conditionnel, hypothèses conservées et classées ; (3) identité algébrique ou réduction définitionnelle ; (4) observation numérique (« jumeau » déterministe). Une réécriture de but n'est pas une réduction mathématique.

**Hiérarchie.** Le théorème compilé d'abord ; le jumeau numérique sert à mesurer, jamais à conclure ; en cas de conflit entre un texte et un théorème compilé, le théorème l'emporte.

**Ordres de l'auteur en vigueur** (sources : `CONTRIBUTING.md`, les trois maîtres `RHV6final_STRATEGIE_*.md`, en particulier le maître sémantique, passation `formalization/RHV6Fresh/HANDOVER_20261107_LIGNE.md`) :
- les contacts d'une Tour lisent la position radiale β, par les formules tangentielles compilées ; un intervalle de contacts est défini par la fréquence ET l'amplitude (§19.63, rectifié le 4 et le 7 novembre) ;
- on ne lie jamais une Tour à la position exacte d'un premier : les intervalles de contacts sont des restes partiels d'écarts, reconstitués collectivement (§19.51, 6 novembre) ;
- la plage utile pour l'arrivée est β ≤ 1/2, jamais « toute β dans l'intervalle ouvert (0,1) » (§19.76) ;
- « équivalent à RH » n'est pas une objection ; admettre un tel énoncé comme prémisse reste interdit (§19.98, 13 novembre) ;
- la fréquence avant la hauteur : le point de rencontre impose une fréquence, puis une hauteur ;
- avant toute compilation ou exécution : pré-enregistrement commité, deux tentatives de compilation au plus, jumeau déterministe pour tout chiffre, rien fabriqué.

## 4. Histoire consolidée

Les lignes d'avant le 26 octobre sont conservées du README précédent. Pour chaque ligne récente : **C** = compilé, **M** = mesuré (jumeau), **R** = rétracté ou récusé.

| Phase | Problème poursuivi | Acquis et révisions |
|---|---|---|
| P1–P4 / KVM8, RHV2–RHV3 | Grammaire des écarts et alignement des premiers avec ζ ; contrôles statistiques | Protocoles et jeux de validation ; les contrôles statistiques ne remplacent aucune contrainte analytique. |
| Juillet–août 2026, `tour10*` et E44 | Géométrie des Tours, rayon/contact, inversion des paramètres | Les contacts consécutifs reconstruisent T et β sous la convention de branche. |
| Août–septembre, `rh_gap_criterion`, RHV4/RHV5, début RHV6 | Événements premiers, passages, miroirs, certificats de comptage | Unicité du successeur, symétries, premières réductions conditionnelles. |
| Septembre, E076–E116 | ON/OFF au même T, progression, deuxième Tour | La progression de T ne prouve pas β invariant. |
| Octobre, E197–E244 | Tours dans le champ de comptage, synchronisation exacte, fibres, énergies | Distinction canal de comptage, canal brut, lissage ; plusieurs obligations non fermées. |
| E264–E352 | Synchronisation locale, reconstruction, grammaire | Contrôles finis seulement. Le dossier d'audit E301 : **R** ses conclusions sont déclarées fausses par l'auteur (§19.9, 30 octobre) ; on ne les cite pas. |
| 22–25 octobre, E353–E376 ; E2M | Mots grammaticaux, canaux de Dirichlet, défaut radial ; correspondance naïve zéro vers transition | **R** la correspondance E2M est rétractée (superposition numérique n'est pas application canonique). |
| 25–28 octobre, séparation et chaîne terminale | Migration ; bande sans zéro, décomposition des séjours, rigidité radiale finie (C, voir §5) ; 27 octobre : build allégé | 28 octobre (`1c2ef553`) : le but terminal devient l'hypothèse nommée « montée de la fréquence attendue », prouvée équivalente à RH ; la chaîne compile (C) et reste conditionnelle. |
| 28–31 octobre, §19 réorientation (§19.1–19.23) | Zéro hors ligne vers porteur vers raccord obligatoire | **C** porteur OFF canonique (`OffCarrier.lean`), trichotomie du membre sortant, fenêtre de trois zéros, cap de fréquence, PNT porté et conséquences (`LogGapsTheorem.lean`, `SummitVertical.lean`). **R** E301 (§19.9) ; la lecture « le contact lisse est une rencontre arithmétique » est déclarée fausse (§19.10). Aucune loi de conservation du transport dans le corpus (§19.19). |
| 31 octobre–3 novembre, §19.24–19.38, E398–E426 | Contacts, contributions par écart, accumulation des valeurs ; E398 (sommet atteint) | **C** géométrie des valeurs réelles aux contacts (`ContactRealValue.lean`), inversion tangentielle, rencontres entre Tours (`TowerMeetings.lean`). **R** le local à deux ou trois zéros (§19.29, « il faut des millions de zéros »). |
| 3–6 novembre, §19.39–19.50, E427–E435 | Contraintes entre Tours aux contacts ; grammaire retrouvée depuis les zéros | **C** modules par expérience (grammaire, lecture de série, valeur aux rencontres, transport au premier partagé). **M** niveau 2 négatif : aucun transport aux contacts ; audit de 22 énoncés sur le complément : aucune rigidité indépendante (E435). |
| 6 novembre, §19.51, E436 | Retrait de la route « contacts d'une Tour et position d'un premier » | **R** toute formule liant la grille de contacts à un premier exact ; **R** « manque = absorption par le complément ou exposant du reste ». **C** découpage d'un écart par les contacts (restes partiels). |
| 7 novembre, §19.53–19.70, E437–E448 | Reconstruction des écarts par les contacts ; prix de la rencontre ; régime fini ; cassure sur la ligne | **C** bilans signés, prix exact (E445), régime « un premier par cellule de rencontre » fini pour toute Tour (`MeetingRegimeFinite.lean`), mécanisme de cassure sur la ligne (`BreakMechanismOnLine.lean`). **R** amendement spectral d'E445 (§19.67) ; obligation « amplitude et variation de la demande brute » retirée. |
| 8 novembre, §19.71, E449 | Inversion : écarts, contacts, zéro | **C** le mot des écarts détermine la Tour (T, phase, β) ; la cause est le PNT porté. |
| 8 novembre, §19.72–19.79, E450–E456 (plan K0–K6) | Paire OFF et miroir | **C** cassure de la paire au premier partagé, ordre du zéro (`PairBreakOfZero.lean`), imposition de la rencontre (`PairMeetingImposition.lean`), paire lue comme passage (`PairArrivalPassage.lean`). **M** décalage des contacts à même hauteur. **R** (rectification §19.76) la plage « toute β ». Aucune contradiction obtenue. |
| 8–12 novembre, plan Φ, §19.80–19.97, E457–E466 | L'arête manquante : la sélection des porteurs ; collectif de nouveau autorisé (§19.91) | **C** bande miroir décrite, recomposition collective, bilan en aires de la demande sur les pièces découpées par les contacts. **M** prédicteur latéral E464/E466 (horizon mesuré, pas théorème). **R** (§19.85) E457 ne dit pas « propriété de queue » : il dit qu'aucun prédicat sur une fenêtre finie du mot ne caractérise la sélection. Aucune contradiction. |
| 13 novembre, plan Ψ, §19.98–19.101, E467–E471 | Attaques cumulatives | **C** quatre modules, 31 énoncés (`MemberConstancySeries.lean`, `FiberAnnihilator.lean`, `PairAsymmetryOverPrimes.lean`, `AlternatingCellSeries.lean`) : la part relative d'une Tour est multipliée par un facteur fixe par cellule, constante exactement sur la ligne ; la paire est non bornée au cumul. **M** exposants de la paire mesurés proches des attendus. Le plan n'a pas clos RH. |
| 13 novembre, §19.105–19.107, E472–E474 | Budget alterné ; grammaire des aires de cellules ; tente | **C** séparation du budget arithmétique et du fond (`ArithmeticBudgetSeparation.lean`), aires de cellules (`CellAreaGrammar.lean`, `CellAreaTent.lean`, `CellAreaIntegral.lean`). **M** budget relatif sous 0,08 sur 8 Tours. **R** rectifications d'un audit externe : « budget lu sur les premiers seuls » trop fort ; « annulation par alternance » abusif. Classées **auxiliaires** par l'auteur le 14 novembre, sans portée vers RH (§19.108). |
| 14 novembre, §19.108–19.109, E475 | Question active : obligation de la reconstruction exacte d'un écart à la première Tour OFF, au premier partagé | Audit, aucun module : les cinq points de la stratégie sont déjà des objets compilés. **M** M1 exact (le premier partagé est le premier suivant, 2000 raccords) ; M2 échoue par la lettre, loi exacte consignée ; M3 sensible, égale au prix déjà compilé. Verdict B : la question sur les parts d'un écart est vide ; la paire ne change que l'énumération. |
| 14 novembre, §19.110, E476 | Tente et cassure | **C** `TentBreakObligation.lean`, 10 énoncés, deux tentatives, build complet vert : le poids de la cassure dans la tente, l'amplitude payée lit ce poids, dent de scie et point neutre, même poids pour la Tour et son miroir si et seulement si β = 1/2. **M** identités à 1e-14 sur 8 Tours ; deux tests échoués par la lettre (prédiction mal écrite). Verdict B ; l'obligation est une forme compilée, pas une contradiction. |
| 14 novembre, §19.111, E477 | Poids alternés Tour moins miroir sur les premiers à mot décalé | **M** poids alternés égaux au premier ordre, effet moyen du second ordre en l'écart ; trois tests échoués par la lettre, dont une prédiction fausse en nature (fluctuations). Aucun module, **aucun théorème**, fil clos. Verdict B. |

Chaque expérience a son pré-enregistrement (commit antérieur), son jumeau, son `RESULTS.md` et un verdict A, B ou C ; les verdicts B sont fréquents et ne sont pas des succès.

## 5. Découvertes établies, résultats mesurés, frontière

**Théorèmes compilés** (nommés en mots ; fichiers sous `formalization/RHV6Fresh/RHV6Fresh/Terminal/`, sauf mention). Sources des énoncés : maître sémantique et journaux de build cités à la section 4.
- Bande sans zéro appliquée aux vrais zéros : pour une hauteur supérieure à 3, la position radiale reste dans une bande qui s'élargit vers un demi — `ZeroFreeRegionBand.lean`. Elle ne sépare pas la ligne du hors-ligne.
- Identité exacte des séjours grammaticaux modulo 6 : la quasi-compensation est l'équirépartition des premiers entre les classes 1 et 5 à une unité près — `GrammarDwellDecomposition.lean` ; borne d'Abel du canal orienté — `GrammarWeightedG4.lean`.
- Rigidité radiale d'une somme exponentielle finie bornée — `FiniteRadialRigidity.lean` (outil conditionnel : la borne du signal infini n'est pas acquise).
- Le théorème des nombres premiers (forme de Tchebychev) est porté, et en découlent comme théorèmes que les écarts logarithmiques tendent vers zéro et que les rencontres échantillonnent les fréquences — `LogGapsTheorem.lean` (§19.18 et suivants du maître), code tiers dans `PNTPort`.
- Porteur OFF canonique et profil d'une perturbation hors ligne : arrivée basse, fibre finie, pas sortant gelé — `OffCarrier.lean`, `OnRegimeStabilityPackage.lean`.
- Cascade de fréquences : sur la ligne elle est strictement croissante à tout rang ; sa stricte croissance partout est équivalente à RH — `FrequencyCascadeStability.lean` (cité dans `DemonstrationChain.lean`).
- Contacts : valeur réelle à chaque contact, inversion tangentielle de (T, β), entrelacement — `ContactRealValue.lean`, `TangentialInversion.lean`, `AmplitudeContact.lean`.
- Le mot des écarts détermine la Tour (E449) ; le miroir a un mot fonction de celui de la Tour, mots égaux si et seulement si β = 1/2.
- Régime fini à un premier par cellule de rencontre — `MeetingRegimeFinite.lean` ; amplitude exacte de la cassure sur la ligne — `BreakMechanismOnLine.lean`.
- Cumul : facteur par cellule de la part d'une Tour, constante si et seulement si ligne ; paire non bornée — plan Ψ, quatre modules cités plus haut.
- Poids de la cassure dans la tente, et égalité des poids Tour/miroir si et seulement si β = 1/2 — `TentBreakObligation.lean` (isolé).
- Équivalence : la montée de la fréquence attendue (hypothèse du théorème terminal) équivaut à RH — `DemonstrationChain.lean`. C'est ce qui rend le théorème terminal conditionnel.

**Résultats mesurés** (jumeaux déterministes, mesures et non preuves) : dossiers `formalization/RHV6Fresh/experiments/E4xx_*` ; zéros d'Odlyzko jusqu'à 2 001 052, premiers jusqu'à 3·10^7. À titre d'exemples : E475 (premier partagé exact sur 2000 raccords), E476 (identités à 1e-14), E477 (second ordre en l'écart de mot).

**Frontière actuelle, en une phrase.** On n'a toujours pas obtenu, à partir des seuls premiers et de la reconstruction exacte d'un écart, une contrainte arithmétique que la première Tour hors ligne et son miroir ne puissent pas satisfaire : les obligations compilées à la rencontre au premier partagé sont satisfaites par toute famille, paire OFF comprise, et seules l'amplitude relative constante et la montée de la fréquence attendue sont violées par la paire, sans être dérivées de la reconstruction (question Q475, `experiments/E475_SharedPrimeObligation/AUDIT_20261114.md`, §19.108–19.109).

**Récusé explicitement par l'auteur** (à ne pas citer comme résultat) : les conclusions d'E301 (§19.9) ; toute liaison d'une Tour à la position exacte d'un premier (§19.51) ; la conclusion d'une étude spectrale d'E445 (§19.67) ; la lecture « propriété de queue » pour E457 (§19.85) ; l'obligation liant la contradiction OFF à l'amplitude et à la variation de la demande brute (§19.68) ; toute affirmation que les contacts ne liraient pas β (§19.44, §19.63) ; la plage « toute β » pour l'arrivée (§19.76) ; la correspondance naïve E2M.

## 6. Appel aux mathématiciens du monde entier

L'auteur ouvre ce projet et invite toute personne qui le souhaite à le poursuivre.

**Constat de l'auteur.** Les intelligences artificielles actuelles exécutent, compilent et mesurent avec rigueur, mais ne savent pas encore trouver des découvertes, les retenir et les combiner entre elles pour fermer une preuve. Nous ne sommes pas à l'intelligence artificielle générale. Ce projet en est une illustration : plus de cinq cents fichiers Lean dans la bibliothèque active, des dizaines d'expériences pré-enregistrées, et une question centrale toujours ouverte.

**Ce que l'auteur demande :**
- relire les théorèmes compilés (liste de la section 5) et les énoncés qui les accompagnent ;
- attaquer la question active Q475 : quelle contrainte nouvelle la reconstruction exacte d'un écart entre deux premiers consécutifs impose à la première Tour hors ligne, que ses contacts et ceux de son miroir ne peuvent satisfaire ;
- proposer des contraintes arithmétiques nouvelles au premier partagé ;
- signaler toute erreur, y compris de vocabulaire ou de portée.

**Comment contribuer.** Lire `CONTRIBUTING.md` et les maîtres (`RHV6final_STRATEGIE_*.md`), en particulier le maître sémantique (`formalization/RHV6Fresh/RHV6final_STRATEGIE_SEMANTIQUE.md`, en particulier §19.98 à §19.111). Règles : aucun `sorry`, aucun `admit`, aucun axiome ajouté ; `lake build RHV6Fresh` doit rester vert ; pré-enregistrer (commit) les hypothèses et les seuils avant de compiler ou d'exécuter ; fournir un jumeau déterministe pour tout chiffre ; ne jamais présenter un énoncé conditionnel comme inconditionnel. Ouvrir une issue ou une pull request sur le dépôt, en citant l'auteur (Charles S.). Les contributions sont soumises aux conditions de `COPYRIGHT.md`. Nous ne promettons aucune preuve.

## 7. Reproduire

**Build Lean** (toolchain `leanprover/lean4:v4.33.0-rc2`, fichier `formalization/RHV6Fresh/lean-toolchain`). Mathlib est épinglé par dépendance git, révision `51e6992efd06126df61a496bebf8f49482a4e129`, déclarée dans `formalization/rhv3_lean/lakefile.toml` ; `RHV6Fresh` accède à `rhv3_lean` par chemin relatif `../rhv3_lean`. `formalization/RHV6Fresh/lake-manifest.json` est le manifeste régénéré par `lake update` lors du build de vérification du 15/11/2026 (il fige Mathlib et ses dépendances) ; celui de `rhv3_lean` n'est pas versionné.
```bash
cd formalization/RHV6Fresh
lake update                          # résout Mathlib et ses dépendances à la révision épinglée
lake exe cache get                   # (si disponible) télécharge les .olean de Mathlib précompilés
lake build RHV6Fresh                 # cible par défaut
lake build RHV6FreshCertificates     # optionnelle : certificats de rectangles 22 et 28 (très coûteux)
```
Les répertoires `.lake/` ne sont pas versionnés : sans cache, la première construction de Mathlib est très longue. Ne déplacez pas `rhv3_lean` ni `RHV6Fresh`. `scripts/status.sh --build` relance le build et réécrit son journal.

**Jumeau Python** (Python 3 avec numpy ; dépendances propres à chaque script, à lire dans son en-tête) :
```bash
cd formalization/RHV6Fresh/experiments/E477_ShiftedPrimesPair
nohup python3 twin_e477.py > logs_twin_run.txt 2>&1 &     # environ 15 s ; protocole borné : pas de sondage en boucle
```
Les résultats attendus sont dans `RESULTS.md` et `twin_results.json` du même dossier.

**Données.** `formalization/RHV6Fresh/experiments/data/` contient les zéros d'Odlyzko : `odlyzko_zeros6_2001052.txt` (36 018 936 octets, SHA-256 `2ef7b752c2f17405222e670a61098250c8e4e09047f823f41e2b41a7b378e7c6`) et ses préfixes `odlyzko_zeros1_first5000.txt`, `odlyzko_zeros1_first300.txt`. Provenance (fichier `odlyzko_zeros6_2001052.PROVENANCE.md`) : A. M. Odlyzko, « Tables of zeros of the Riemann zeta function », fichier `zeros6`, https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros6, téléchargé le 27 octobre 2026. Ces hauteurs sont celles de zéros connus sur la ligne critique ; elles ne certifient pas l'absence de zéros hors ligne.

## 8. Plan du dépôt public

```text
formalization/
  rhv3_lean/    (168 .lean)         fondations ζ, comptage, certificats ; dépendance Mathlib épinglée
  RHV6Fresh/    (586 .lean au total) build actif ; RHV6Fresh.lean et RHV6FreshCertificates.lean à la racine
    RHV6Fresh/ (560)               code de la bibliothèque
      Terminal (393)               chaîne terminale et modules de résultats (dont DemonstrationChain.lean)
      Zeta23Port (134)             code tiers (Apache 2.0), voir THIRD_PARTY_NOTICES.md
      PNTPort (9)                  code tiers (Apache 2.0), voir THIRD_PARTY_NOTICES.md
      Tower (7), Direct (7), Voyage (3), Grammar (2), Foundation (2), RhGapPort (1)
    experiments/                   expériences E400 à E477 (70 dossiers), audit_semantique/ (sans son data/), data/ (< 1 Mo, plus les zéros d'Odlyzko)
    scripts/                       status.sh, goal_dependencies.py, raccord_check.py
    audits_compilation/            journaux de compilation
    RHV6final_STRATEGIE_{SEMANTIQUE,MATHEMATIQUE,LEAN}.md   les trois maîtres
    HANDOVER_20261107_LIGNE.md     passation (§1 à §36)
    AUDIT_*.md                     audits de ce dossier
docs/ANNONCE_PUBLICATION_20261115.md   annonce de publication
README.md, COPYRIGHT.md, LICENSE, THIRD_PARTY_NOTICES.md, CONTRIBUTING.md, CITATION.cff, SECURITY.md, PUBLICATION_SCOPE.md
```
Ce qui n'est pas dans ce dépôt (bases `rhv2_fresh`, `rhv4_lean`, `RHV5Fresh`, `rh_gap_criterion`, expériences antérieures à E400, `research/`, `validation/`, `src/`, `docs/` antérieurs, journal interne de travail) reste dans le dépôt de recherche privé et peut être fourni sur demande ; voir `PUBLICATION_SCOPE.md`.

---

# Annexes : inventaire historique arrêté au 26 octobre 2026

**Les annexes décrivent l'ensemble du dépôt de recherche privé.** Les dossiers et fichiers cités qui ne figurent pas dans ce dépôt public (voir `PUBLICATION_SCOPE.md`) sont « dans le dépôt de recherche privé ». Les sections ci-dessous sont conservées du README précédent, sans mise à jour (elles décrivent l'état au 26 octobre : par exemple, le but terminal qu'elles mentionnent a été transformé depuis, voir le bandeau). Les chiffres d'expériences y sont ceux de cette date ; l'évolution depuis est dans la section 4. Les dossiers d'audit E301 y figurent par leur nom ; leurs conclusions sont récusées (section 5).

## A1. Découvertes démontrées et limites

**Grammaire modulo 6.** Pour les premiers `p>3`, l'état est 1 ou 5. Il existe quatre transitions `11,15,51,55`. Le canal orienté `N15−N51` est un télescopage des états d'extrémité et vaut en valeur absolue au plus 1 sur un préfixe. Ce n'est pas une contrainte indépendante sur β. Les suites d'écarts, les familles et les méta-patterns expérimentaux ne sont pas interchangeables avec ces quatre transitions.

**Séjours et canal de caractère.** Dans `Terminal/GrammarDwellDecomposition.lean`, pour tout mot de deux états :
```text
N11 − N55 = (N1• − N5•) − (N15 − N51).
G11 − G55 = (W1 − W5) − (G15 − G51)   (tous poids réels).
```
Le premier terme pondéré est un canal de caractère, le second une somme d'Abel dont la variation totale majore la valeur. La quasi-compensation empirique des séjours n'est pas une borne uniforme ; ces identités ne démontrent pas l'absence de tout couplage spectral.

**Tours et inversion tangentielle.** Pour `β,T>0` :
```text
φ(β,T) = arctan(T/β)
log C_k = (φ + kπ)/T,    log(C_{k+1}/C_k) = π/T
T = π/log(C⁺/C⁻),        β = T/tan(T log C⁻)  (branche vérifiée)
```
Le contact est dérivé du zéro ; retrouver le zéro depuis deux contacts **choisis** n'établit pas que les premiers produisent ces contacts. Le candidat géométrique `k* = floor((T log S−φ)/π)` sélectionne la cellule contenant une échelle `S>0`, mais le théorème identifiant cette cellule au passage premier authentique n'est pas acquis.

**Miroir et ON/OFF.** Le miroir authentique de `β+iT` est `1−β+iT`. Il se confond avec le membre initial exactement quand `β=1/2`. Hors ligne, même T et même largeur logarithmique `π/T`, mais phases et amplitudes différentes. Cette symétrie est statique ; elle ne prouve pas à elle seule la stabilité ON du successeur. Un quartet OFF complet est une expérience hypothétique, pas une substitution de zéro isolé dans la vraie fonction ζ.

**Reconstruction analytique.** Le terme individuel exact du canal de Tchebychev est proportionnel à `−x^ρ/ρ`; le canal du comptage `li(x)` utilise des contributions appropriées telles que `Ei(ρ log x)`, avec correctifs, branche et troncature. Les sommes lissées, les termes bruts et les formes normalisées doivent avoir des types distincts (`ExactZeroSignal`, `RescaledZeroSignal`, `UnitCoefficientMode`), sans substitutions tacites. La somme infinie et son complément ne sont pas contrôlés par une expérience avec 300 zéros.

**Bande sans zéro et rigidité.** `ZeroFreeRegionBand` réutilise la région sans zéro inconditionnelle de `rhv3_lean` : pour `T>3`, `A/(log T)^9 < β < 1−A/(log T)^9`. Cette bande s'élargit à haute fréquence, elle ne force pas `β=1/2`. `FiniteRadialRigidity` prouve pour une somme exponentielle **finie et bornée** que les exposants positifs sont exclus ; le contrôle uniforme du complément infini manque. `GrammarWeightedG4` établit des bornes pour le canal orienté, non pour le canal commun.

**Comptage et premières hauteurs.** Les certificats de rectangles de ζ établissent les premiers zéros en ligne et l'absence de membre bas jusqu'à la hauteur 28 dans les modules concernés. Un « OFF possible » après ce seuil a une fibre miroir et un profil contraints, mais aucune contradiction terminale n'est obtenue.

## A2. Matrice des solutions tentées

| Voie | Module, TDD ou série | Résultat effectif | Obstacle terminal |
|---|---|---|---|
| Géométrie des contacts | E44, TangentialInversion, E367/E374, `TDD_ContactInversion` | Inversion exacte si contacts authentiques fournis | Sélection indépendante du contact |
| Succession / fibre / miroir | Direct/Raccords, OnRegime*, HorizontalExclusion, E208–E214 | Identités d'ordre, miroir distinct, profil d'une première rupture | Admissibilité réfléchie ou exclusion de la sortie OFF |
| Conservation de régime | `DemonstrationChain`, `OnRegimeStabilityPackage`, E350–E351 | Récurrence **conditionnelle** et contraintes d'une rupture | `β_E=1/2 ⇒ β_L=1/2` non démontré |
| Domination de la première Tour | E218, anciennes prémisses terminales | Formulations conditionnelles, parfois RH-équivalentes | Inégalité indépendante sur le vrai reste |
| Énergie et budgets | E216, E224–E241, E324, TDD A3 | Identités ou outils coercifs conditionnels | Construire une énergie positive et son budget arithmétique |
| Grammaire de fenêtres | E340–E344, E353–E363 | Mots, supports et transitions calculés | Pas de borne du résidu collectif |
| Canaux signés, Dirichlet, Abel | GrammarDwell*, GrammarWeightedG4, T1/T2 papier | Canal orienté et correction des puissances isolés | Canal commun, T1/T2 Lean, raccord `transitionSum` |
| Formule explicite / Mellin | E365, E372 sondes, PrimePowerCorrection/Z3 envisagés | Identités et critères conditionnels | Reste `O(x^θ)` avec exposant suffisamment petit |
| Reconstruction finie / projection | E308, E330–E336, E364–E376, Z1 | Identifiabilité limitée, calibrations et contre-tests | Projection et troncature infinies contrôlées |
| ON/OFF synthétiques | E268–E288, E347, E369, E373, E375 | Croissance OFF, déplacement d'enveloppe et phases | Compensation collective authentique non exclue |
| Loi de transport affine | `TDD_AuthenticTransportCore`, A1–A9 | Implications formelles et deux contre-exemples abstraits | Fonction `F(Q,e)` authentique, source issue des premiers |
| Certification indépendante | P0–P11, `ROOT_CAUSE_MASTER_MATRIX` | Graphe de dépendances partiel | Première flèche premiers→sortie spectrale non construite |

### Essais A1–A9 (transport authentique)

| Essai | Preuve/contre-modèle | Donnée nouvelle manquante |
|---|---|---|
| A1 | `j=Ae+b`, `e=0` ⟹ `j=b` | Produire `b` sans définir le défaut |
| A2 | `j=F(Q,e)`, `e=0`, `F(Q,0)=0` ⟹ `j=0` | Construire `F` depuis `Q` arithmétique |
| A3 | `j²≤V≤Ae²`, `e=0` ⟹ `j=0` | Énergie arithmétique indépendante |
| A4 | Source strictement absorbée avec `q<1` ⟹ nul | Estimation authentique `q<1` |
| A5 | Bornes arbitrairement petites pour **le même** `j` ⟹ zéro | Reste uniformément contrôlé |
| A6 | Transport impair ⟹ fixe zéro | Parité exacte du certificat, attention `J` non impair |
| A7 | Chemin `0,1,0` | Un bilan cyclique nul ne suffit pas |
| A8 | Fibre miroir `{−1,1}` | Invariance de fibre ≠ membre fixé |
| A9 | Successeur OFF d'un ON ⟹ réfléchi non consécutif | Admissibilité du reflet, déjà proche du verrou |

Ces neuf essais compilent individuellement selon les journaux de `authentic_transport_causality`; ils ne ferment **aucune obligation arithmétique terminale**.

## A3. Registre des expériences : objectifs et résultats documentés

Le registre complet des **107 dossiers** `formalization/RHV6Fresh/experiments/` (dans le dépôt de recherche privé ; le dépôt public n'en contient que la sélection E400–E477) est organisé ci-dessous par vagues ; les rapports de chaque dossier restent la source de détails, de chiffres et d'éventuelles rectifications.

| Séries | But commun | Résultats et réserves |
|---|---|---|
| E076–E116 (scripts directement sous `experiments/`) | Phase, Tours, contacts, miroir et grammaire | Tests géométriques et cas OFF ; inversion et progression ne fournissent pas la cause de ON. |
| E117–E196 | Énergies, contacts, incidences, propagation et inversions | Plusieurs contre-tests et corrections de schémas ; lire les `*_output.md`. |
| E197–E211 | Fenêtres, fibres, li(x), Tour collective, premier zéro | Décomposition des contributions et diagnostic du passage entrant/sortant. |
| E212–E244 | Regime ON, jonctions, harmonie et correction collective | Le raccord arithmétique sur le reste demeure ouvert ; fenêtres finies non suffisantes. |
| E264–E300 | Tours individuelles, sensibilité ON/OFF, fenêtres et synchronisation | 51 images/PDF dans la série ; témoins finis, non des certificats RH. |
| E301–E313 | Audit contradictoire, 3 Tours, battements, non-compensation, modes | Séparation du comptage exact et des signaux tronqués. |
| E321–E336 | Reconstruction autour de li(x), résultats 3/10 zéros, inverse et ancrage | Inversion ≠ identification spectrale autonome. |
| E337–E352 | Plan de comptage, grammaire, rencontres, stabilité, OFF nouvelle hauteur | Plusieurs pistes requalifiées ; conservation ON non établie. |
| E353–E363 | Grammaire exhaustive de 500 000 écarts en 100 fenêtres | 994 971 mots distincts de longueur 2–12 rapportés, 7 compositions de classes contre 8 chemins d'états (projection non injective) ; certaines fins de listes du calcul `meta_graph` omises historiquement. |
| E364–E370 (scripts racine) | 36 hauteurs fixes, `ψ` exact, récupération de fréquences, inverse contacts, OFF | Fenêtres finies ; `β` non identifiable depuis signal ON normalisé seul ; pas de borne du reste. |
| E371–E376 (scripts racine) | Détection, calibration, appariement, inversion contacts, quartet synthétique | Pics de fréquences ≠ nouveaux zéros ; intervalle d'erreur non certifié ; aucune preuve d'identifiabilité. |
| **E371 — Archétype B (dossier distinct)** | Décomposition des séjours jusqu'à `10^7` | `D=−33` à `10^6`, `D=−189` à `10^7`, maximum `|D|=362`, observation seulement. |
| **E372 — ClosureAttempts (dossier distinct)** | Six sondes de fermeture terminale | P1 bande/gel compatibles ; P2 multiplicité forte absente ; P3 finitude vs reste infini ; P4/P5 gain d'exposant manquant ; P6 règle de jonction RH-équivalente. |
| **E373 — WeightedGrammarChannels (dossier distinct)** | 300 zéros et poids `−2Re((q^ρ−p^ρ)/ρ)` ; OFF synthétique | Identités pondérées confirmées ; variation OFF voisine d'un mode commun ; **les anciens chiffres du reste direct sont invalidés jusqu'à recalcul**, en raison des puissances de 2 et 3 omises avant correction du script. |
| E2M (24 octobre) | Superposition zéros et premiers | 2 001 052 ordinates ; 1 912 998 intervalles de hauteurs sans transition et 88 055 transitions sur l'axe brut ; **mapping causal rétracté**. |
| Authentic transport (25 octobre) | Transports homogène/affine/énergie/absorption/miroir | A1–A9 sont conditionnels ou contre-modèles ; zéro fermeture nouvelle. |

Les **190 sous-dossiers directs de `research/`** archivent les campagnes historiques (E44, `tour10*`, rétrospectives et preuves de concept). Les **38 familles de `validation/`** contrôlent P4/zêta, KVM8, alignements et ablations. Leurs README originaux restent disponibles et leurs résultats ne sont pas convertis en théorèmes par cette consolidation.

### Index des ensembles d'expériences

- **E197–E244** : `e197_window_comparison`, `e198_transmissions_300`, `e199_increment_matrix_fibers`, `e200_arrival_fiber_hypotheses`, `e201_first_zero_contact_comparison`, `e202_cell_passage_restitution`, `e203_transition_rigidity_raccord`, `e204_three_towers_li_field`, `e205_counting_field`, `e206_prime_gap_ledger`, `e207_collective_contact_geometry`, `e208_on_regime_anchor`, `e209_regime_transport`, `e210_first_regime_change`, `e211_on_regime_induction_probe`, `e212_archaeology`, `e213_mixed_fibers`, `e214_tower_transport`, `e215_window_collective`, `e216_energy_raccords`, `e217_missing_property_probes`, `e218_global_tower_dominance`, `e219_prime_gap_zero_dna`, `e220_counting_channel_gap_contributions`, `e221_collective_compatibility`, `e222_frequency_extraction`, `e223_global_gap_invariant`, `e224_harmonic_restoring_law`, `e225_mirror_harmonic_balance`, `e226_xi_kernel_spectral_stability`, `e227_functional_equation_restoring_constraint`, `e228_zero_mode_stability`, `e229_prime_gap_harmonic_response`, `e230_terminal_closure_challenge`, `e231_contact_sign_closure`, `e232_two_gap_charge_closure`, `e233_six_beats_closure`, `e234_grammar_noncompensation`, `e235_two_gap_determinant`, `e236_raccord_additive_rigidity`, `e237_first_off_minimal_compensation`, `e238_exact_counting_closure`, `e239_first_zero_causality`, `e240_harmonic_current`, `e241_tower_coupling`, `e242_exact_signal_audit`, `e243_gap_synchronization`, `e244_amplitude_stable_sync`. Dossiers transversaux : `e224_e230_compiler_probe`, `e231_e238_euler_product_route`, `e231_e238_lean_closure_probes`.
- **E264–E352** : `E264_E300_LocalSynchronization`, `E301_AuditContradictoire`, `E302_THREE_ON_TRUE_3D_SYNCHRONIZATION`, `E303_THREE_ON_COLLECTIVE_BEATS`, `E305_FixedGapRaccords`, `E308_PrimeOnlyRadialRigidity`, `E309_PerGapSynchronizationDistinctHeights`, `E310_PrimeMusicAmplitudeStability`, `E311_SuccessiveModeExtraction`, `E312_SignalProgressionTranslation`, `E313_ConstantAmplitudeNeed`, `E321_GeneratedFrequencyMeetingPoints`, `E322_CountingReconstructionAroundLi`, `E323_SynchronizationMatrix`, `E324_ImposedAmplitudeNonCompensation`, `E325_JointGapTriple`, `E326_GoalAudit`, `E327_PrimeQuantitativeGrammar`, `E328_ThreeZerosAroundLi`, `E329_PrimeGapWindowsThreeZeros`, `E330_ThreeZeroResultant`, `E331_TenZeroResultant`, `E332_SuccessiveSumsSameGaps`, `E333_CountingFieldArchitecture`, `E334_InversePrimeSpectralReconstruction`, `E335_FirstZeroArithmeticAnchor`, `E336_LocalGlobalGapMatrix`, `E337_CountingPlane`, `E338_PrimeToCountingPlane`, `E340_GrammarWindow`, `E341_GrammarWindowQualification`, `E342_PrimeInversionThreeZeros`, `E343_GapInverseCountingPlane`, `E344_GrammarOperator`, `E345_HarmonicCollaborationFiveZeros`, `E345_E346_STABLE_TOWERS_REBUILD`, `E346_BilateralHarmonicRaccord`, `E347_OFF_NewHeight_E345_E346`, `E348_InequalityCandidates`, `E349_TwoMeetingInversion5000Gaps`, `E350_GrammarSpectralStability`, `E351_GapDemandStability`, `E352_ProjectionOnKnownZeros`.
- **Autres registres actifs** : `E371_ArchetypeB_Anatomy`, `E372_ClosureAttempts_ZeroFreeBand`, `E373_WeightedGrammarChannels`, `authentic_transport_causality`, `causal_advanced_validation`, `root_cause_validation`, `d1012_causal_validation`, `project_audit`, `audit_semantique`. Les programmes E353–E376 sont également directement sous le dossier `experiments/`.

## A4. Index des TDD et tests formels

**34 fichiers Lean contenant TDD dans leur nom ont été identifiés** dans le dépôt lors de l'inventaire Git (les logs et plans TDD ne sont pas compris). Registre primaire actif :
```text
TDD_ArithmeticCandidate.lean          TDD_ArithmeticFrequencyNecessity.lean
TDD_ArithmeticRefinement.lean         TDD_AstraDivisorMass.lean
TDD_AstraIncidenceFreedom.lean        TDD_AstraPrimeWeights.lean
TDD_CanonicalGrammarStability.lean    TDD_ContactErrorPropagation.lean
TDD_ContactInversion.lean             TDD_CriticalRemainderExponent.lean
TDD_CriticalRemainderIntegration.lean TDD_ExactFixedSpectralSignal.lean
TDD_FixedWindowGrammar.lean           TDD_FixedZeroSignal.lean
TDD_GrammarAnalyticSeparation.lean    TDD_GrammarChannelObstructions.lean
TDD_GrammarPotentialStability.lean    TDD_GrammarWeightedG4.lean
TDD_InterWindowComposition.lean       TDD_ONPhaseTransport.lean
TDD_RootCauseMirrorTransport.lean     TDD_SpectralWindowComposition.lean
TDD_ValidatedZeroMatching.lean       TDD_WindowGrammarStability.lean
authentic_transport_causality/TDD_AuthenticTransportCore.lean
authentic_transport_causality/TDD_TransportReductionAudit.lean
```
Ces 26 fichiers sont dans `formalization/RHV6Fresh/experiments/` (les deux derniers dans le sous-dossier). Les 8 autres sont dans `formalization/rh_gap_criterion/` et `research/tdd_true_off_zeta_only_20260913/` : séries `Round26FSFiberedPartnershipTDDRepair`, `Round27EFiberedPartnershipTDD`, `Round27GTwoBaseReflectedLaurentTDD`, `SemanticTransportClosure20260821/{FinalConditionalFirstReturnClosureTDD,ProgressiveFiberedFirstReturnClosureP2TDD,ProgressiveFiberedFirstReturnClosureP3TDD,ProgressiveFiberedFirstReturnClosureTDD}`, `TrueOffZetaOnlyTDD`.

Catégories de tests : **arithmétique/fréquence**, **grammaire/fenêtres**, **contact/inversion**, **reste critique et intégration**, **signaux exacts/projections**, **transport/mirroir**, **causalité/diviseurs/masses**, **routes historiques de première rupture**. Les résultats `project_audit/tdd_results.json`, `project_audit/README.md` et `authentic_transport_causality/BUILD_AND_AXIOMS.md` sont les sources des vérifications ciblées. Un PASS de TDD ne signifie pas que son hypothèse conditionnelle est vraie pour les véritables premiers.

## A5. Atlas des graphiques et figures

L'inventaire de l'arbre Git au 26 octobre recense **450 fichiers** sous extensions `.png`, `.svg`, `.jpg`, `.jpeg`, `.webp`, `.pdf` (certaines planches ont les deux formats PNG/SVG ; ne pas compter les deux comme expériences indépendantes). L'existence est vérifiée par l'arbre Git ; la correction physique de chaque tracé n'a **pas** été contrôlée image par image.

| Galerie / dossier sous `formalization/RHV6Fresh/experiments/` | Fichiers visuels | Sujet |
|---|---:|---|
| `E264_E300_LocalSynchronization/` | 51 | Tours, ON/OFF, sensibilité, contacts, compensation |
| `E302_THREE_ON_TRUE_3D_SYNCHRONIZATION/` | 18 | 3 Tours, contacts, li, écarts et reconstruction |
| `E303_THREE_ON_COLLECTIVE_BEATS/` | 18 | Battements, superposition, comptage |
| `e243_gap_synchronization/` | 14 | Contributions par écart |
| `E347_OFF_NewHeight_E345_E346/` | 13 | OFF à nouvelle hauteur et contrôles |
| `e207_collective_contact_geometry/` | 12 | Géométrie des contacts |
| `e244_amplitude_stable_sync/` | 10 | Amplitude ON stable et synchronisation |
| `E334_InversePrimeSpectralReconstruction/` | 9 | Reconstruction inverse |
| `E331_TenZeroResultant/` | 8 | Superposition de dix zéros |
| `authentic_transport_causality/` | 8 | **Schémas SVG**, pas de courbes quantitatives |
| `e208_on_regime_anchor/` | 8 | Ancrage ON |
| `e242_exact_signal_audit/` | 8 | Audit du signal exact |
| `E333_CountingFieldArchitecture/` | 7 | Architecture du comptage |
| `E342_PrimeInversionThreeZeros/` | 7 | Inversion trois zéros |
| `E345_E346_STABLE_TOWERS_REBUILD/` | 7 | Reconstruction de Tours stables |
| `e199_increment_matrix_fibers/` | 7 | Fibres et matrices |
| `e219_prime_gap_zero_dna/` | 7 | Grammaire des écarts et signatures |
| `E345_HarmonicCollaborationFiveZeros/` | 6 | Cinq zéros |
| `e198_transmissions_300/` | 6 | 300 transmissions |
| `e205_counting_field/` | 6 | Champ de comptage |
| `e209_regime_transport/` | 6 | Régime et transport |
| Autres dossiers et fichiers directs | Complément jusqu'à 450 | Voir chemins et README individuels |

Exemples de tracés nommés : `E264_A1_zeros_1_3_tours_individuelles`, `E268_fig_ON_vs_OFF_T1`, `E270_fig_contacts_contributions`, `E302/fig3_li_signaux`, `E303/fig7_comptage`, `e115_figA_analytic_plane_scaled`, `e115_figB_tower_log_view`, `e115_figC_normalized_axes`, `e364_e370_synchronized_views.png`, `e371_e376_reconstruction_audit.png`. Chaque chemin doit être interprété avec sa notice de campagne et ses hypothèses. **Une Tour ON normalisée peut être dessinée avec amplitude fixe ; le terme de comptage exact n'a pas la même enveloppe.** Les représentations circulaires isolées ne décrivent pas à elles seules le champ autour de `li(x)`.


## A8. Index exhaustifs (dans le dépôt de recherche privé)

Les trois registres suivants (`docs/RH_FIGURES_ATLAS_20261026.md`, `docs/RH_EXPERIMENTS_TDD_READMES_INDEX_20261026.md`, `docs/RH_E_NUMBERED_SCRIPTS_INDEX_20261026.md`) sont dans le dépôt de recherche privé et ne sont pas publiés ici.

## A9. Carte de navigation

- [README du dépôt](README.md) — point d'entrée.
- [README du build RHV6Fresh](formalization/RHV6Fresh/README.md) — commandes et statut.
- [Périmètre de publication](PUBLICATION_SCOPE.md) — ce qui est inclus et exclu.
- [Audit de solution](formalization/RHV6Fresh/AUDIT_SOLUTION_20261005.md) ; [Audit de fidélité aux maîtres](formalization/RHV6Fresh/AUDIT_FIDELITE_RHV6_vs_MAITRES.md).
- Dans le dépôt de recherche privé seulement : README des formalizations, des docs, des recherches, du code Python, des validations.

**Provenance et fidélité :** cette synthèse résulte de l'inventaire du tree `main` (8 698 fichiers, 117 README, 107 sous-dossiers d'expériences RHV6Fresh, 450 documents visuels, 34 fichiers Lean TDD par nom) et de la lecture des README principaux et audits ciblés. Elle n'implique **ni réexécution des 107 campagnes, ni examen individuel des 450 figures, ni certification nouvelle du build**. Les résultats divergents doivent être arbitrés par la source expérimentale corrigée, la signature Lean et le journal d'exécution, puis éventuellement par un rerun.
