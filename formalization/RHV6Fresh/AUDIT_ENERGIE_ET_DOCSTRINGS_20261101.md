# Audit préparatoire (lecture seule) — énergie exacte et docstrings « rencontre » (2026-11-01)

Reconnaissance menée par deux agents Sonnet sous pilotage Fable, puis vérifiée par sondage (définitions citées relues dans
les fichiers ; table de remplacements validée ligne à ligne : 211 lignes, 0 décalage). Aucun fichier Lean modifié, aucun
build lancé par les agents. Ce document prépare le plan §19.26 du maître ; il ne conclut rien sur β.

## 1. Audit énergétique des sept modules cités par l'auteur

Grandeurs de référence (auteur, 2026-11-01) : (1) énergie brute x^{2β}/|ρ|² ; (2) énergie normalisée x^{2β−1}/|ρ|² ;
(3) énergie géométrique = K_ρ² × énergie analytique ; (4) énergie collective = somme des énergies individuelles + termes croisés.

| Module | Définitions à caractère énergétique | Grandeur | Passage individuel → collectif | Hypothèses nommées | Dans la clôture de `DemonstrationChain` |
|---|---|---|---|---|---|
| EnergyIdentity | `verticalEnergy` (:25, log du rapport des modules de deux zéros), `horizontalEnergy` (:29, (β_l−β_e)·log q) | aucune : logarithmes d'amplitudes, pas de carré | aucun (deux zéros e, l seulement) | `hβ`, seuil `hthr` (:84–85) ; `PVerticalDominatesAtRaccord`, `PVerticalEnergyPush` cités en commentaire, non compilés ici | oui |
| GeometricEnergyRaccord | aucune définition ; théorèmes d'encadrement de ‖zeroTerm z x‖ entre contacts | racine de (1), même zéro, points différents ; aucun K_ρ | aucun | positivité, même hauteur (:133, :161) | oui |
| RayEnergy | aucune définition ; `ray_energy` (:97 : partie réelle au contact = (−1)^k C_k^β/‖ρ‖), `ray_energy_growth` (:138) | racine de (1) sur les rayons ; signe alterné | aucun (mono-zéro ; `passage_double_constraint` = deux zéros, pas de somme de carrés) | aucune | oui |
| RemainderEnergy | `ownCellIncrement` (:109), `ownCellEnergyDensity` (:151 : incrément² / largeur de cellule), `vonMangoldt_sq_sum_*` (:45–73) | (incrément)²/largeur, exposant 2β−1 d'une cellule à la suivante (:154) — PAS x^{2β−1}/|ρ|² ; sommes de Λ(n)² = diagonale arithmétique, sans zéro | une seule somme de carrés, côté premiers, terme à terme ; en-tête :26–28 : « le transfert énergie du reste ≤ C·diagonale n'est pas dérivé » | aucune | oui |
| QuadraticVariation | `windowEnergy` (:40 : Σ μ(q)·normSq f(q)), `windowCross` (:44 : Σ μ(q)·Re(f·conj g)), `pairTerm`, `doubleTerm` (:81–85, sans 1/ρ) | (4) exactement, à poids μ | `windowEnergy_add` (:47–53) : identité EXACTE avec termes croisés (via `Complex.normSq_add`) ; `cross_term_unconstrained` (:186) : aucune identité ne fixe le terme croisé | aucune | NON (importé par Audit, OnLineBetaEqPrevious) |
| GrammarWordLoad | `stateIndicator`, `abMinusBa` ; `mirror_word_energy_debt` (:84 : 4d·log(q_m/q_0)) | aucune : dette linéaire télescopique | aucun | aucune | oui |
| GapDemandStability | `gapBudget` (:60), `windowDrift` (:79 : Σ log du rapport d'amplitudes normalisées = (β−1/2)·budget), `gapDemand := localArithmeticTarget` (:145) | `windowDrift` = log d'une racine de (2), sans carré | `gapDemand_eq_sum` (:148) : somme COMPLEXE de `smoothedLocalContribution` sur tous les zéros (`localSynchronization`), aucune énergie formée | `hAnchor` (β du premier zéro = 1/2, :171/179/190) ; `WindowStable`, `DemandTransported`, `ImposedScaleStable` (⟺ RH par `*_iff_riemannHypothesis`) | NON (importé par la racine seule) |

Aucun `sorry`, `admit` ni `axiom` en code dans les sept modules (le mot « sorry » n'apparaît qu'en commentaire d'en-tête).

**Constat.** Aucun des sept modules ne définit (1), (2) ni (3) ; aucun K_ρ n'existe dans le corpus (la constante d'homothétie
n'apparaît que dans `SameGapsAudit.geometricTower_similar_zeroTerm`, compilée le 2026-11-01 : K = ‖ρ‖²·exp(−2βφ/T)). Une seule
définition réalise (4), `windowEnergy`, et son unique passage à une somme (`windowEnergy_add`) conserve les termes croisés. Il
n'existe donc, dans ces sept modules, AUCUN passage d'une énergie individuelle à une obligation collective qui omette les termes
croisés, et AUCUNE comparaison énergie géométrique / énergie analytique (donc aucune sans K_ρ). Ce que les anciens théorèmes
« énergétiques » manipulent, ce sont des amplitudes ‖zeroTerm‖, leurs logarithmes, ou un incrément au carré par cellule : jamais
le carré de la contribution lissée d'un écart |Δ_{ρ,n}|², ni la somme de ces carrés à une rencontre. La question de l'auteur
(« les anciennes contraintes portent-elles sur les mêmes grandeurs que les contributions aux rencontres ? ») reçoit donc, par
lecture, la réponse : NON, elles ne portent pas sur ces grandeurs ; elles n'en sont ni une version fautive ni une version
correcte, elles sont à côté. Cette lecture doit être compilée (plan §19.26, étape I) avant d'être tenue pour acquise.

Limites déclarées par l'agent : dépendances (`PairInteraction`, `ExplicitFormulaLink`, `FixedGapRaccords`, `GapSynchronization`)
non relues au-delà des définitions citées ; clôture d'imports calculée par script sur les lignes `import`, pas par `lake`.
Les définitions `windowEnergy`, `windowCross`, `windowEnergy_add`, `cross_term_unconstrained`, `ownCellEnergyDensity` et
l'en-tête de RemainderEnergy ont été relus par Fable dans les fichiers : conformes au rapport.

## 2. Recensement « rencontre » dans les six fichiers de la chaîne

| Fichier | Occurrences | (R) = p_{n+1}, à conserver | (C) = contact de Tour, à remplacer | (?) ambigu |
|---|---|---|---|---|
| GeneratedFrequency.lean | 118 | 0 | 109 | 9 (« rencontre collective », :397–448 : `CollectiveMeeting x` = annulation du reste lissé en x quelconque) |
| DemonstrationChain.lean | 35 | 0 | 32 | 3 (:648, :651, :697 : rencontre collective du signal avec son fond) |
| OccupiedFrequency.lean | 13 | 0 | 13 | 0 (dont :7–8 citation verbatim de l'auteur, non remplacée) |
| ConstantAmplitudeNeed.lean | 14 | 0 | 5 | 9 (`ConstantNeed` quantifie sur toutes les abscisses x ≥ 1 ; :30 « points de rencontre de la courbe des premiers ») |
| CoupleLock.lean | 30 | 0 | 30 | 0 |
| GrammarTransportLaw.lean | 26 | 0 | 26 | 0 |
| **Total** | **236** | **0** | **215** | **21** |

Aucun identifiant Lean ne contient « rencontre » (tous anglais). Les quatre objets de `GeneratedFrequency` sont des contacts de
Tour : `meetingOf p` = C_0 de x^p (:127, confirmé par `contactMinusAt_eq_meetingOf` :303) ; `MeetingOnLine T` = égalité de deux
contacts (:165) ; `ArithmeticMeeting T c` = un C_0 par composante du reste (:150 ; « arithmétique » qualifie l'origine des
composantes, pas p_{n+1} — docstring proposée : « contact de Tour arithmétique », à valider par l'auteur) ; `smoothedMeeting p k`
= contacts lissés (:1261). Aucun des six fichiers n'appelle `meetingPoint` ni `localArithmeticTarget` : le mot « rencontre » au
sens réservé (p_{n+1}) n'y apparaît jamais.

Table de remplacement prête (docstrings et commentaires seuls, identifiants inchangés, accords corrigés, verbe « rencontre
l'axe » → « fait contact avec l'axe ») : `audits_compilation/DOCSTRINGS_RENCONTRE_CONTACT_PROPOSES_20261101.tsv`, 211 lignes
(GeneratedFrequency 108, DemonstrationChain 31, CoupleLock 30, GrammarTransportLaw 26, OccupiedFrequency 11,
ConstantAmplitudeNeed 5), chaque ancien texte vérifié présent à la ligne indiquée. Non couverts, en attente de l'auteur : les
21 lignes ambiguës et les 5 citations verbatim (OccupiedFrequency :7–8, DemonstrationChain :77, GeneratedFrequency :17–18, :1067).

## 3. Clash racine `windowProjection` (reproduit le 2026-11-01)

```
error: RHV6Fresh.lean:1:0: import RHV6Fresh.Terminal.SpectralWindowProjection failed,
environment already contains 'RHV6Fresh.windowProjection' from RHV6Fresh.Terminal.GapTranslationInvariance
```

`GapTranslationInvariance.windowProjection f a L T` (:41) et `SpectralWindowProjection.windowProjection f T U L` (:37) portent le
même nom dans le même espace `RHV6Fresh` (`windowProjection_finset_sum` est également doublé). Chaque module compile seul
(`lake build RHV6Fresh.Terminal.GapDemandStability` : succès, 3993 jobs). Le clash n'apparaît qu'à la racine. Importateurs de
`SpectralWindowProjection` : `GapDemandStability` et la racine seulement ; aucun des deux n'est dans la clôture de
`DemonstrationChain`. Correction la moins invasive : espace de noms `RHV6Fresh.Spectral` autour de `SpectralWindowProjection`
et qualification des usages dans `GapDemandStability` ; la chaîne n'est pas touchée.

## 4. Étape K′ exécutée (2026-11-01, feu vert « continues avec la tentative envisagée »)

`Terminal/AuthenticRaccordLock.lean` (isolé, 12 théorèmes, axiomes standard, 2 tentatives ; journal
`audits_compilation/authenticraccordlock/`). Identités I7 (relation d'amplitudes au premier partagé = champ `transport`,
déjà compilée) et I8 (énergie exacte de la contribution avec cosinus de phase, `contribution_energy_on_occurrenceGap`)
compilées ; le premier partagé est la rencontre de l'écart d'occurrence (`sharedPrime_eq_meeting`). Résultat de la
composition : l'orientation du raccord sortant d'un zéro authentique est un théorème (`authentic_departure_hierarchy`) et une
lecture de fréquence seule (`lock_relation_reads_frequency_only`) ; une arrivée OFF ne casse que le raccord suivant
(`off_arrival_keeps_hierarchy_breaks_next`) ; premier but non résolu = `RadialConservationAtAuthenticDeparture`
(`arrival_onLine_iff_next_hierarchy`), jamais prouvé. I1–I6, I9, J, B′, H′ : non lancés. Voir maître §19.27.
