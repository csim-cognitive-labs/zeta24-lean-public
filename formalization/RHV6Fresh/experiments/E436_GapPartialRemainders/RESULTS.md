# E436 — résultats (exécutée le 2026-11-06 ; `logs/probe_attempt{1,2}.txt`, `logs/lean_attempt1.txt`, `logs/lake_build_full_trimmed.txt`)

Pré-enregistrement : `README.md` (commit 6bd6913d, addendum ba1a6947 avant toute compilation). Aucun critère modifié
après exécution. Module isolé `Terminal/GapPartialRemainders.lean` : **une seule tentative** (`lean_attempt1.txt`,
EXIT=0), 26 déclarations, aucun `sorry`, aucun `admit`, 8 affichages d'axiomes tous standards ; `lake build RHV6Fresh`
vert. Aucune mesure numérique. Aucun retour à l'analyse spectrale : `all_signals_meet` n'est ni importé comme appui ni
cité ; aucune somme infinie n'apparaît dans le module.

## 1. Sondes (`probe_attempt1.txt`, `probe_attempt2.txt`)
| sonde | résultat | tentative |
|---|---|---|
| S1 découpage de la contribution de cellule brute par les contacts | compilé | 1 (seule erreur : `fnPrimeAtRank` sans `open RHV3Lean`, corrigée à la 2) |
| S1 restes de bord = fractions de cellule ; écart sans contact ⊂ une cellule | compilé | 1 |
| S2 fréquence partagée : nombres de contacts différant d'au plus un | compilé | 1 |
| S3 restes de part et d'autre d'un point de rencontre = une cellule ; série | compilé | 1 (après correction d'espace de noms) |
| S4a bilan avec reste nul + paire + valeurs du miroir bornées ⟹ `False` | **but laissé** | 2 |
| S4b porteur + bilan avec reste explicite ⟹ `False` | **but laissé** | 2 |

## 2. Compilé (noms exacts)
`rawCellContribution`, `firstContactAfterLower`, `wholeCellCount`, `initialEdgeRemainder`, `finalEdgeRemainder`,
`wholeCellSum`, `GapHasContact`, `firstContact_add_count`, `gap_variation_eq_remainders`,
`rawCellContribution_eq_remainders`, `firstContact_gt_lower`, `lastContact_le_upper`, `finalRemainder_span`,
`finalRemainder_span_lt`, `initialRemainder_span`, `gap_span_lt_cell_of_no_contact`, `stageOffset`,
`stagePosition_same_height`, `lastContact_same_height_bounds`, `same_height_contact_count_diff`,
`mirror_contact_count_diff`, `mirror_contact_ratio_gt`, `consecutive_lower_eq_upper`, `edge_remainders_complete_cell`,
`rawCellContribution_series`, `rawCellContribution_series_eq_accumulation`.

Lecture en mots. (S1) La contribution de cellule brute d'une Tour à un écart — l'intégrale exacte de sa densité entre
les deux premiers — se découpe sur les propres contacts de la Tour en un reste partiel initial, des cellules entières et
un reste partiel final, dès que l'écart contient un contact ; les deux restes de bord couvrent des fractions de cellule
lues aux deux bornes ; si l'écart ne contient aucun contact, il tient dans une seule cellule. Aucun contact ne pointe
vers un premier : les bornes de l'écart sont les premiers, les contacts découpent la part de la Tour. (S2) Deux Tours de
même fréquence ont leurs positions d'étage décalées d'une constante purement radiale ; dans tout écart leurs nombres de
contacts diffèrent d'au plus un ; pour un zéro sous la ligne, les valeurs aux contacts du miroir croissent strictement
plus vite, d'un contact au suivant, que celles du zéro (sur-amplitude du miroir, compilée). (S3) Au point de rencontre,
le reste final de l'écart précédent et le reste initial de l'écart suivant recomposent exactement une cellule de la
Tour ; sur une série d'écarts, la somme des contributions télescope et ne lit, pour chaque Tour, que des cellules
entières et deux restes de bord.

## 3. Buts Lean terminaux restants (reproduits intégralement, `probe_attempt2.txt`)
```
error: unsolved goals
s : Finset (ℝ × ℝ)
β T target x : ℝ
hβ : 0 < β
hβ1 : β < 1
hT : 0 < T
h₁ : (β, T) ∈ s
h₂ : (1 - β, T) ∈ s
hne : (β, T) ≠ (1 - β, T)
hbal : breakResidual s target x = 0
hpair : breakResidual ((s.erase (β, T)).erase (1 - β, T)) target x = 0 + (towerRe β T x + towerRe (1 - β) T x)
K : ℝ
hK : ∀ (k : ℤ), |contactRealValue (1 - β) T k| ≤ K
hv : |contactRealValue (1 - β) T 0| = contactAt (1 - β) T 0 ^ (1 - β) / ‖{ re := 1 - β, im := T }‖
⊢ False
```
Note sur S4a : l'hypothèse `hK` (valeurs aux contacts du miroir bornées) est fausse pour toute Tour, en ligne ou non
(`abs_contactRealValue_ratio` : rapport `exp(βπ/T) > 1`) ; elle ne peut donc pas servir de levier, et le but laissé
n'est pas une information sur la structure.
```
error: unsolved goals
C : OffCarrier
h :
  ∀ (I : PrimeGapInterval) (s : Finset (ℝ × ℝ)),
    breakResidual s (log I.upper) I.upper = log I.upper - ∑ ρ ∈ s, towerRe ρ.1 ρ.2 I.upper
hmirror : rZeroRadialPosition ↑(mirrorMember C.zero) = 1 / 2 + C.radialShift
hzero : rZeroRadialPosition ↑C.zero = 1 / 2 - C.radialShift
⊢ False
```
Note sur S4b : l'hypothèse `h` est la définition du reste (`breakResidual`), vraie par `rfl` ; le bilan avec reste
explicite est une identité pour toute famille finie.

## 4. Non-circularité
Aucune hypothèse posée dans le module ; aucune somme infinie ; aucune prémisse sur la position radiale ; les sondes S4
déclarent leurs hypothèses et n'alimentent aucun théorème.

## 5. Verdict : B
Réduction compilée : la part d'une Tour sur un écart et sur une série d'écarts est lue entièrement en restes partiels de
cellule aux contacts, en canal brut, sans somme infinie ; la sur-amplitude du miroir aux contacts est compilée. Aucune
contradiction ; aucune propriété n'est déclarée manquante. Ce que les sondes montrent : le bilan au point de rencontre
avec reste explicite est, pour une famille finie, une définition ; la propriété d'énergie du reste énoncée par l'auteur
(le reste ne peut pas fournir une compensation divergente) n'a pas encore de forme compilée dans ce module — elle est
l'énoncé suivant à écrire en Lean, dans les objets de ce module (restes partiels, valeurs aux contacts, bilan avec reste),
et le compilateur décidera.
