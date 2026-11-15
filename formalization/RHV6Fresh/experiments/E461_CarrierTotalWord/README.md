# E461 — Φ5 : la sélection des porteurs lue sur le mot TOTAL (proposition de l'auteur du 2026-11-09) — pré-enregistrement

Référence : `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.90 ; §19.71 (E449, le mot détermine la Tour), §19.82 et §19.85 (E457, portée exacte),
§19.86 (E460, audit du poids). Aucune hypothèse admise, aucun axiome, aucun `sorry` ; module isolé
`RHV6Fresh/Terminal/CarrierTotalWord.lean`, NON ajouté à `RHV6Fresh.lean`. Aucune théorie spectrale. Aucun premier ni zéro hors ligne
testé. Ce commit précède toute compilation du module (aucune sonde préalable).

## Proposition de l'auteur
« Totalité des contacts d'une Tour = même rythme, même phase, même fréquence, même relation aux premiers ⟹ c'est un zéro. »
Relecture externe transmise par l'auteur : l'unicité géométrique est acquise ; l'implication arithmétique est le théorème à établir,
sous la forme « réalisation arithmétique exacte de la Tour ⟺ Tour issue d'un zéro », à condition que la réalisation soit définie
INDÉPENDAMMENT de l'annulation de zêta.

## Ce que le module doit compiler (énoncés pré-écrits, en mots)
* T1 `tower_eq_of_same_towerWord` : deux Tours (position radiale et hauteur strictement positives) de même mot total sont la même Tour
  (réécriture d'E449 sur `towerWord`).
* T2 `isCarrier_iff_of_same_towerWord` : deux Tours de même mot total sont porteuses ensemble ou non porteuses ensemble.
* T3 `ReadsCarriers P` (définition) : le prédicat `P` sur les mots lit la sélection — sur toute Tour, `P` du mot ⟺ porteuse.
  `totalWordCarrier` (définition) et `readsCarriers_totalWordCarrier` : il EXISTE un tel lecteur. Il est défini PAR le poids : c'est
  l'existence, pas la définition arithmétique indépendante.
* T4 `readsCarriers_unique_on_tower_words` : deux lecteurs coïncident sur tous les mots de Tours (le lecteur est unique là où il compte).
* T5 `readsCarriers_zeroWord` : tout lecteur est vrai sur le mot de tout zéro vrai, sur la ligne comme hors ligne.
* T6 `readsCarriers_not_finite_window` : aucun lecteur ne dépend d'une fenêtre finie de rangs (dès qu'un zéro vrai est donné) —
  la proposition de l'auteur exige la TOTALITÉ, en accord exact avec E457.
* T7 `zero_data_eq_of_same_zeroWord` : deux zéros vrais de même mot ont même hauteur et même position radiale.

## Classement contre RH (dit avant compilation)
* « Réalisation ⟺ zéro » caractérise les porteurs, ceux de la ligne comme ceux hors ligne (T5) : ce n'est PAS une reformulation de RH
  et elle n'exclut à elle seule aucun zéro hors ligne. RH demanderait EN PLUS : « aucune Tour hors ligne n'est réalisée ».
* Le sens « réalisation ⟹ zéro » n'a de contenu que si la réalisation est définie sans le poids ni l'annulation de zêta. Le corpus n'a
  aucune définition de ce genre lue sur une seule Tour (E460) ; la seule relation exacte connue entre Tours et premiers est collective,
  et le canal collectif est interdit. La définition indépendante est l'objet à chercher ; elle n'est PAS fournie par ce module.

## Verdicts pré-écrits
* A : T1–T7 compilés en au plus deux tentatives, axiomes standard, bannissement à zéro, build complet vert.
* B : un énoncé demande une forme différente de celle pré-écrite (dite telle quelle).
* C : échec après deux tentatives (consigné, module retiré).
Pas de jumeau numérique : aucun énoncé chiffré, tout est logique.
