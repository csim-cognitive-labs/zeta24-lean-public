> Version française conservée à titre de référence. Main language: English, see README.md.

# E459 — Φ3 : hypothèses locales H-a et H-b, classement en trois rubriques puis exigences (pré-enregistrement, 2026-11-09)

Référence : `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.80 (Φ3), §19.83 point 3 (règle des trois rubriques), §19.86 (prévision issue de
l'audit E460), §19.88. Aucune hypothèse admise, aucun axiome, aucun `sorry` ; module isolé
`RHV6Fresh/Terminal/CarrierLocalReading.lean`, NON ajouté à `RHV6Fresh.lean`. Aucune théorie spectrale. Aucun zéro hors ligne n'est
supposé ni testé : le classement se fait au niveau des Tours (couples position radiale, hauteur), et les énoncés sur les zéros vrais
sont des équivalences ou des implications depuis RH.

Ordre suivi, dit tel quel : une sonde non versionnée (`attempts/probe1.txt`, sans erreur) a précédé ce pré-enregistrement pour établir
le classement, comme l'ordre de l'auteur le demande (classer AVANT de pré-enregistrer) ; le module définitif est compilé après ce commit.

## Formes précises des hypothèses
* **Forme paramétrique** `SameReadingAt β T n` : le rang `n` n'est pas dans la bande de la Tour `(β, T)` (le mot du miroir et le mot de
  la Tour coïncident au premier de rang `n`).
* **H-a (au rang `n`)**, sur les zéros vrais : `SameReadingAtRankOnCarriers n` — pour tout zéro vrai, même lecture au rang `n`. Le plan
  disait « au premier de la première cassure » ; E450 traite un premier partagé quelconque : H-a est donc posée à rang fixé quelconque
  (et, par extension, sur tout ensemble FINI de rangs).
* **H-b**, sur les zéros vrais : `SameMeetingCellsOnCarriers` — même cellule de rencontre pour la Tour et son miroir à TOUTE rencontre ;
  variante `SameReadingBeyondOnCarriers N` (toutes les rencontres à partir du rang `N`). La cellule de rencontre de l'écart de rang `n`
  est le mot au rang `n + 1` (identité de définition, à compiler).

## Classement en trois rubriques (établi par la sonde, à compiler dans le module)
| Hypothèse | (i) implication compilée | (ii) contre-modèle compilé au niveau des Tours | (iii) réciproque |
|---|---|---|---|
| H-a au rang `n` (ou sur un ensemble fini de rangs) | RH ⟹ H-a | OUI, hors cas dégénéré : si aucun premier de l'ensemble n'est exactement sur un contact de la ligne à la hauteur `T`, il existe une fenêtre ouverte autour de la ligne où toute Tour a la même lecture ; en particulier une Tour du côté bas, hors ligne, la satisfait. Cas dégénéré (premier exactement sur un contact de la ligne) : la même lecture à ce rang FORCE la ligne à cette hauteur. Classement exact : « H-a au rang `n` force la ligne à la hauteur `T` » ⟺ « le premier de rang `n` est exactement sur un contact de la ligne de hauteur `T` ». | H-a ⟹ RH : OUVERTE, dite comme telle ; au niveau des Tours elle ne force pas la ligne (rubrique ii) : « strictement plus faible, sur les Tours ». |
| H-b sur toutes les rencontres (ou à partir d'un rang quelconque) | RH ⟺ H-b (les deux sens) | aucun : sur les Tours, même lecture à partir d'un rang ⟺ ligne | sans objet : ÉQUIVALENTE, donc REFORMULATION, jamais posée |
| H-b restreinte à une sous-suite infinie stricte de rencontres | RH ⟹ | non établi | OUVERTE ; la trancher demanderait de savoir si la bande rencontre la sous-suite, question de répartition INTERDITE (aucune densité affirmée) ; non poursuivie |
| H-c (poids et bande) | — | — | équivalente : close comme reformulation en E458 (B6) |

Remarque de portée (§19.85) : « même lecture à partir d'un rang ⟺ ligne » est un énoncé de queue pour la question du MIROIR (compilé
ici) ; il ne dit rien de la sélection des porteurs.

## Énoncés à compiler
1. `sameReadingAt_iff`, `meetingCell_eq_towerWord`, `same_meetingCell_iff` (dictionnaire).
2. `floor_stable_of_continuous_not_int`, `towerWord_stable_near` : hors contact exact, le mot est localement constant en la position
   radiale (des deux côtés).
3. `sameReading_window` : fenêtre de même lecture autour de la ligne sur tout ensemble fini de rangs sans contact exact ;
   `exists_offLine_sameReading_on_finset` : contre-modèle du côté bas (rubrique ii).
4. `mem_mirrorStrip_of_prime_on_line_contact` : cas dégénéré ; `sameReadingAt_forces_line_iff` : classement exact de H-a.
5. `sameReading_beyond_iff` : sur les Tours, même lecture à partir d'un rang ⟺ ligne.
6. `sameReadingAtRank_of_riemannHypothesis` (RH ⟹ H-a) ; `sameReadingBeyond_iff_riemannHypothesis`,
   `sameMeetingCells_iff_riemannHypothesis` (H-b ⟺ RH).
Limite dite d'avance : la non-vacuité de la branche « sans contact exact » n'est pas compilée (elle est mesurée par le jumeau) ; le
classement exact (énoncé 4) couvre les deux branches sans en avoir besoin. Le cas dégénéré est une branche logique : il n'est JAMAIS
affirmé qu'un premier est sur un contact (§19.51).

## Prévisions écrites avant exécution
* Tout compile (la sonde est passée).
* Critère d'arrêt du plan (hypothèse plus faible que RH, vraie sur les contrôles, dont l'exigence compilée fait intervenir le poids) :
  NON atteint — H-a est plus faible sur les Tours mais son exigence ne fait pas intervenir le poids (fenêtre autour de la ligne,
  fixée par la fraction de cellule) ; H-b est une reformulation.

## Volet déterministe — `e459_local_reading.py`
200 premières hauteurs d'Odlyzko, premiers ≤ 10⁶, contrôles `β ∈ {0,3 ; 0,4 ; 0,45}` (Tours non porteuses). Mesures : (a) fraction de
cellule de la ligne aux dix premiers rangs, pour les 200 hauteurs : plus petite distance à un contact (attendu : strictement positive
partout, branche non dégénérée) ; (b) demi-largeur EXACTE de la fenêtre de même lecture au rang 0 et sur les dix premiers rangs
(formule tangentielle), recoupée par test direct de part et d'autre du bord ; (c) part des contrôles qui satisfont H-a au rang 0 et
sur les dix premiers rangs (attendu : majoritaire au rang 0 pour chaque contrôle, le décalage de phase étant petit devant la
cellule ; aucun seuil chiffré n'est fixé) ; (d) premier rang de bande (rang où H-b casse) pour chaque contrôle : attendu fini pour
toutes les Tours de contrôle (déjà observé en E458 : aucune bande vide). Mesure, aucune loi, aucune densité.

## Protocole
Deux tentatives au plus ; `attempts/` ; `#print axioms` ; grep du ban à zéro ; `lake build RHV6Fresh` complet vert ; script une fois
sous `nohup`, sortie dans `logs/`.
