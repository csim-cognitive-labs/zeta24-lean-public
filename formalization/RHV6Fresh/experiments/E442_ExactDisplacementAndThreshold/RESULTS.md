# E442 — Résultats (exécutée 2026-11-07, après le pré-enregistrement 3d5492d6)

Pièces : `logs/probe_attempt{1,2,3,4}.txt` (sonde non versionnée : (1) olean manquant puis trois défauts — ordre
`unfold towerPhase`, positivité de `q` entier, `push_neg` déprécié — (2–3) ordre des réécritures `log_exp`/`unfold`,
(4) EXIT=0), `logs/lean_attempt1.txt` (module définitif, EXIT=0, **une seule tentative**, 13 `#print axioms`
standards), `logs/lake_build_full_trimmed.txt` (« Build completed successfully (9064 jobs) »). Aucune expérience
chiffrée nouvelle : les règles compilées ici ont été mesurées à 0 violation en E441.

## Module `Terminal/ExactDisplacementAndThreshold.lean` (isolé, 13 énoncés)
| bloc | énoncés | règle d'E441 |
|---|---|---|
| D1–D2 | `floor_add_sub_floor`, `displacement_rule`, `meetingCell_displacement_rule` | R1 : déplacement exact = partie entière de `T log(p'/p)/π` + un si la fraction de cellule à `p` ajoutée à la partie fractionnaire atteint un |
| D3–D4 | `stagePosition_contact`, `lastContactBefore_contact`, `stagePosition_mono`, `stagePosition_strictMono`, `lastContactBefore_of_mem_cell` | la position d'étage d'un contact est son indice ; un entier d'une cellule (hors contact) a cette cellule pour dernier contact |
| D5 | `signedPrimeSum_eq_primes_in_block` | cas général : poids premier signé d'un bloc = Σ `(−1)^{cellule(q) − a}·log q` sur les premiers du bloc, sans hypothèse de contact par écart (hypothèse ponctuelle : aucun contact n'est un entier) |
| D6 | `cellLength_meeting_le`, `meeting_rises_of_weight_dominates`, `meeting_falls_of_length_dominates` | R4 : sûre-zone basse (`p(r−1) ≤ log p` ⇒ la cellule de rencontre monte) et haute (`log p` + poids non premiers `< p(1 − 1/r)` ⇒ elle descend) |
| D7 | `weight_dominates_below_threshold` | R4 : sous un point `x` où `x(r−1) ≤ log x` (au-dessus de `1/(r−1)`), `p(r−1) ≤ log p` : le seuil `x*` sépare bien |

## Lecture (contacts, intervalles, signes)
Le signe de la cellule de rencontre se transmet d'une rencontre à la suivante par un déplacement que la fréquence
lit à une unité près et que la fraction de cellule à la rencontre précédente rend exact ; R2 d'E441 (la fréquence
seule ne prédit le signe qu'à 75 %) est ainsi expliquée par un énoncé compilé. Dans un bloc quelconque de cellules,
y compris quand plusieurs rencontres partagent une cellule, le poids premier signé est la somme des rencontres avec
le signe de leur cellule. Les cellules de rencontre montent tant que la rencontre est sous le seuil `x*` où
`x*/log x*` vaut `T/π` ; au-delà de `x*·r`, elles descendent.

## Verdict
**B** : tout compile en une tentative, build complet vert. Rien n'est déclaré manquant. R2, R3, R5 restent des
mesures rattachées aux énoncés compilés (R3 l'est déjà par la forme close d'E441).
