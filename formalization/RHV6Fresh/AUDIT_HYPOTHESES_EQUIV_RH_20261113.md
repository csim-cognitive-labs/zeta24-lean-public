# Audit des hypothèses écartées au motif « équivalent à RH » (ordre de l'auteur, 2026-11-13, règle R-RH)

Objet : relever chaque hypothèse ou cible que l'exécutant a écartée, suspendue ou déclarée « frontière » au motif qu'elle équivaut à
l'hypothèse de Riemann ; dire pour chacune qui l'a écartée, si elle a été attaquée comme cible, ce que le compilateur en a fait, et si,
sous la règle R-RH, elle aurait dû être considérée. Sources : maître sémantique §19 (lignes citées), `CLAUDE.md`, modules compilés.

Grille de jugement. Trois cas seulement : **(T) refusée comme cible** (jamais attaquée, ou abandonnée, au seul motif « ⟺ RH ») —
rejet À TORT sous R-RH ; **(R) attaquée puis rapportée comme « frontière »** — travail fait, faute de compte rendu (le mot « frontière »
était un frein) ; **(P) refus de l'admettre en prémisse, ou ordre de l'auteur** — légitime, inchangé.

| n° | Hypothèse (en mots) | Où | Écartée par / motif | Attaquée comme cible ? | Compilé | Jugement | Action |
|---|---|---|---|---|---|---|---|
| H1 | Continuation forcée : le pas sortant de la première cassure du porteur monte | §19.8–19.11 | exécutant : « frontière ⟺ RH » | oui : sonde directe §19.9.4 (3 sondes, négatives), §19.10–19.11 | `ContinuationForced ⟺ RH` | R | reste la cible mère ; la réattaquer avec les outils collectifs (E462–E465) |
| H2 | Un écart ne peut être reconstitué sans fréquence nouvelle entre deux écarts qui en apportent une | §19.11.3–19.12 | exécutant : « HYPOTHÈSE, ne jamais la démontrer directement » | non | — | **T** | rouvrir comme cible |
| H3 | Constance par membre : la part de chaque membre garde une amplitude relative constante entre rencontres (doctrine P2 de l'auteur) | §19.21 B4 | exécutant : « relation supplémentaire ⟺ RH, jamais une flèche du graphe » | non (seulement classée) | `constantRelativeAmplitude_law_iff_riemannHypothesis` ; échoue exactement au zéro OFF et à son miroir | **T** | **cible prioritaire** : c'est la « stabilité de la grammaire » décrite par l'auteur ; la dériver des premiers sur les cellules (E463/E465) |
| H4 | Tout porteur OFF est contradictoire (P5) | §19.21 B3 | exécutant : « nommée, fermée comme cible » | oui, indirectement (K0–K6, Φ) | `no_carrier_iff_riemannHypothesis` | **T** (formulation) | c'est le but lui-même ; ne plus jamais l'écrire « fermée » |
| H5 | Demande bornée aux rencontres ET reste jamais à droite (panneau 2 du graphique de l'auteur) | §19.21 B5 | exécutant : « circulaire » | non ; compilé seulement comme théorème conditionnel | `carrier_contradiction_under_panel_two` | **T** | rouvrir : démontrer les deux hypothèses depuis les premiers |
| H6 | Cascade stricte : montée stricte du régime en ligne, écart d'un pas strict | §19.16 | exécutant : « cible ⟺ RH, pas un fait » | partiellement (ThreeZeroWindow encadre, n'oriente pas) | encadrement compilé | **T** | rouvrir comme cible |
| H7 | Occurrences distinctes ⟹ hauteurs distinctes ; hauteurs n et n+1 distinctes sur le porteur | §19.17, §19.28 | exécutant : « cible fermée », « pas un lemme intermédiaire » | non | `common_height_excluded_iff_riemannHypothesis` | **T** | cible candidate (même famille que `NoMixedHeight`, E457 R2) |
| H8 | Conservation du transport au premier partagé | §19.19 | exécutant : « l'inventer serait poser RH ; recherche SUSPENDUE » | audit du corpus seulement | défaut du détour compilé, non nul | **T** | rouvrir : la conservation comme cible à démontrer, pas à inventer |
| H9 | Rigidité radiale de la foule d'un écart | §19.30 | exécutant : « blocage mathématique » | oui : sonde ⊢ False avec tout le contexte, négative | `crowdRadialRigidity_iff_riemannHypothesis` | R | cible légitime ; « blocage » à ne plus écrire |
| H10 | Toute amplitude de contact est celle de la ligne | §19.32 | exécutant : « c'est RH » | non | — | **T** | rouvrir ; lié à E444 (β lu par l'amplitude) et E463 |
| H11 | Croissance du reste lissé d'exposant un demi | §19.34, §15 | exécutant : « ⟺ RH » + verdict §15 (défaut dyadique) | oui, tentatives §15 négatives | `riemannHypothesis_iff_remainderExponent_eq_half` | R (motif ⟺ RH tombe ; le constat §15 reste un essai négatif, pas une interdiction) | cible légitime |
| H12 | Absorption par les Tours de tête (piste B d'E404) | §19.35 | exécutant : « morte, contrainte seulement par H3 ⟺ RH » | non (tuée par l'argument) | — | **T** | rouvrir SOUS RÉSERVE : l'auteur a ordonné de ne pas citer E404/E408 (décision auteur) |
| H13 | Borne d'accumulation des contacts | §19.37 | exécutant : « prémisse ⟺ RH, jamais posée » | non | `riemannHypothesis_of_contact_accumulation_bound` (implication) | **T** | rouvrir : démontrer la borne depuis les premiers |
| H14 | « Stabilité posée », « prémisse ⟺ RH » dans la liste d'interdictions de §19.41.1 | §19.41 | **auteur** : interdiction de POSER | — | — | P | rien ; conforme à R-RH (ne pas admettre) |
| H15 | La constellation ne peut pas payer le prix de la rencontre sur la série (budget d'E445) | §19.66 | exécutant : « énoncé manquant unique ⟺ RH, non posé » | oui : 3 tentatives T1–T3, journalisées, négatives | prix exact/non borné compilé | R | réattaquer avec les aires d'E465 ; **tension** avec R-E446 (auteur : ne pas lier à « amplitude ↔ variation de la demande ») à trancher par l'auteur |
| H16 | La fréquence attendue monte aux rencontres (prémisse unique) | §19.20, §19.77 L6 | exécutant : « prémisse ⟺ RH » ; point 3 mesuré non compilé | mesurée, non attaquée en Lean | `ExpectedFrequencyRisesAtMeetings` ⟺ RH | **T** | rouvrir comme cible |
| H17 | R1 porteur = miroir ; R2 hauteur injective sur les porteurs ; R3 prix égal à la ligne en tout premier ; R3' même module des termes du zéro et du miroir en deux premiers | E457, §19.81 | exécutant : « chacune ⟺ RH, aucune posée » | non | quatre équivalences compilées | **T** | **cible candidate** : R3' (deux premiers distincts suffisent) est la forme la plus arithmétique |
| H18 | Poids de fibre sous deux pour toute hauteur porteuse | §19.85 Q2 | exécutant : « RH et simplicité, plus fort que RH » | non | — | P (plus fort que RH : l'attaquer est plus dur que RH ; remarque, pas interdiction) | basse priorité |
| H19 | H-b : même lecture de la cellule de rencontre à partir d'un rang | E459, §19.88 | exécutant : « reformulation jamais posée » | non | H-b ⟺ RH compilé | **T** | cible candidate |
| H20 | Relation exacte aux premiers lue dans le collectif | §19.89 | **auteur** : canal interdit (levé le 2026-11-09) | depuis : E461–E465 | oui | P (levé) | fait |
| H21 | Toute Tour réalisée est sur la ligne | E462 R8, §19.92 | exécutant : « c'est RH elle-même, frontière » | non directement | R8 compilé comme équivalence | R/**T** | c'est la cible du fil Φ ; Φ9 l'attaque |
| H22 | Annulateur de fibre (Φ9) | §19.96 | exécutant : « à classer contre RH avant de poser » ; lancement sur ordre de l'auteur | — | — | P (décision auteur) | prêt |
| H23 | Capture persistante (inégalité de type RH sur tous les passages) | `CLAUDE.md` l. 667, revue du 2026-10-04 | « à ne PAS chercher à démontrer » — attribué à la revue de l'auteur | non | `PersistentCapture` ⟺ RH | P ? (si l'ordre est de l'auteur, il tient ; le motif ⟺ RH est caduc) | **à trancher par l'auteur** |
| H24 | Hypothèses locales d'E459 classées en trois rubriques | §19.80, §19.88 | exécutant : classement puis « réciproque ouverte » | non | H-a ⟸ RH compilé | **T** (le classement a servi de tri, non de point de départ) | reprendre H-b (= H19) |

**Bilan.** 24 énoncés. Quatorze (H2–H8, H10, H12, H13, H16, H17, H19, H21, H24) ont été refusés ou abandonnés COMME CIBLES au seul
motif de leur équivalence à RH : rejets à tort sous R-RH. Cinq (H1, H9, H11, H15, H21) ont été réellement attaqués puis rapportés
comme « frontière » ou « blocage » : le travail existe, le compte rendu freinait. Cinq (H14, H18, H20, H22, H23) relèvent d'ordres de
l'auteur ou d'un refus de prémisse, légitimes et inchangés ; H23 demande une décision de l'auteur.

**Autres interdictions en vigueur, par origine** (hors motif ⟺ RH). D'ORIGINE AUTEUR, inchangées tant que l'auteur ne les lève pas :
ne jamais citer E301 ; ne jamais « la Tour touche un premier » (§19.51) ; R-E446 (ne pas lier la contradiction OFF à « amplitude ↔
variation de la demande par cellule ») ; §19.40 (pas de test direct des premiers ou du OFF sur la route de preuve) ; ne pas citer
E404/E408 ; jamais « aveugle à β » (§19.63) ; plage utile β ≤ 1/2 (§19.76) ; comptage = constat d'aval (§19.20). D'ORIGINE EXÉCUTANT,
LEVÉES par cet audit : toute formule « frontière inchangée (… ⟺ RH) », « fermée comme cible », « ne jamais démontrer directement »,
« recherche suspendue car l'inventer serait poser RH », « blocage mathématique » appliquée aux énoncés H2–H13, H16–H17, H19, H21, H24.

**Recommandation (une seule cible à la fois).** H3, la constance par membre : c'est l'énoncé exact de la « grammaire stable qui se
répète » invoquée par l'auteur ; il est compilé qu'elle échoue exactement au zéro hors ligne et à son miroir ; l'outil pour la lire
sur les premiers est la part d'une Tour sur ses cellules (E463) face à l'aire de demande (E465), c'est-à-dire Φ9. Seconde cible : H17
R3' (même module des termes du zéro et du miroir en deux premiers distincts).
