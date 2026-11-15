# E437 — Résultats : recomposition collective d'un écart par les restes partiels, canal brut (2026-11-07)

Pré-enregistrement : commit 2f22152d. Module isolé `Terminal/CollectiveGapRecomposition.lean` (non ajouté à
`RHV6Fresh.lean`). **Une seule tentative de compilation** (`logs/lean_attempt1.txt`, EXIT=0) ; sonde de noms préalable
`logs/probe_attempt1.txt` (deux corrections : `continuousAt_finset_sum` inexistant → `tendsto_finsetSum` ;
`positivity` ne déduit pas `0 ≤ x` de `N ≤ x` → transitivité explicite). Huit `#print axioms` : `propext`,
`Classical.choice`, `Quot.sound` seulement. Aucune hypothèse, aucun `sorry`, aucune position radiale, aucune somme infinie.
Scratch supprimé après capture. Build complet : `logs/lake_build_full_trimmed.txt`.

## 1. Énoncés visés et verdict du compilateur

| Énoncé | Nom Lean | Verdict |
|---|---|---|
| R4 descente entre rencontres | `rawDemand_on_cell` | compilé |
| R4 saut au passage d'un entier | `rawDemand_jump` | compilé |
| R1 recomposition collective par les restes partiels | `familyGapShare_eq_remainders` | compilé |
| R2 bilan d'un écart avec reste explicite | `gap_balance` | compilé (identité) |
| R3 passage à l'écart suivant (série) | `rawResidual_series`, `rawGapDemand_series`, `series_balance` | compilés |
| R5 continuité de toute famille finie | `towerRe_continuousAt`, `familyRe_continuousAt` | compilés |
| R6 le reste porte tout le saut | `rawResidual_jump_tendsto`, `meeting_jump_carried_by_residual` | compilés |
| R7 aucune famille finie ne recompose la rencontre | `no_finite_family_recomposes_meeting`, `meeting_not_recomposed_by_finite_family` | compilés |

Aucun but laissé.

## 2. Ce que cela dit, en mots (canal brut, axe réel, aucune position radiale)

1. La demande brute d'un écart est la variation de « masse des entiers moins l'entier » entre deux premiers consécutifs.
   Entre deux entiers elle descend d'une unité par unité de longueur ; au passage d'un entier elle saute de son poids,
   nul sauf aux puissances de premiers, égal au logarithme du premier à un premier.
2. Pour une famille finie de Tours dont chaque membre a au moins un contact dans l'écart, la part de la famille sur
   l'écart est exactement la somme, membre par membre, du reste partiel initial, des cellules entières et du reste
   partiel final de ce membre (découpage d'E436, chacun sur ses propres contacts). C'est la recomposition collective.
3. Bilan d'un écart : demande = part de la famille + variation du reste explicite. Sur une série d'écarts, les parts
   s'additionnent écart par écart et le reste télescope : le passage à l'écart suivant est exact, sans perte, pour
   toute famille finie.
4. Toute famille finie de Tours est continue. La demande saute à la rencontre. Donc la variation du reste explicite
   au passage de la rencontre tend vers le saut entier, le logarithme du premier, pour TOUTE famille finie. Les
   contacts et cellules d'une famille finie recomposent la partie continue de l'écart ; le saut à la rencontre est
   porté par le reste, jamais par les contacts.
5. Conséquence compilée : aucune famille finie ne recompose la rencontre seule (le reste ne peut pas être constant à
   gauche d'un premier).

## 3. Réponse au point de l'auteur sur la somme infinie (constat compilé, pas opinion)

- Canal brut : aucune somme infinie de Tours n'est compilée dans le corpus pour `ψ(x) − x` ; la seule représentation
  compilée aux entiers est `psiRemainder_eq_spectral_add_correction` (canal de cellule + correction bornée), qui n'est
  pas une somme de Tours convergeant point par point. L'énoncé de l'auteur « la somme infinie ne comble aucun écart »
  est cohérent avec le corpus : rien de compilé ne comble le saut d'une rencontre par une somme de Tours.
- Canal lissé : `smoothed_gap_synchronization` reste un théorème (somme absolument convergente). Il reconstitue un
  incrément CONTINU, sans saut : il ne comble aucun écart au sens de la rencontre brute. Consigné comme fait, non comme
  appui (§19.51).
- Ce que les contacts font, compilé ici : ils recomposent la partie continue de chaque écart (R1–R3) et passent à
  l'écart suivant exactement ; le saut de la rencontre est dans le reste de toute famille finie (R6–R7).

## 4. Non-circularité
Aucun énoncé ne mentionne `rZeroRadialPosition`, aucun zéro OFF, aucune équivalence à RH, aucune limite sur les
hauteurs. Les seules hypothèses sont « chaque membre a un contact dans l'écart » (R1) et « le poids de l'entier est
non nul » (R7, satisfait à tout premier).

## 5. Verdict : B
Réduction inconditionnelle nouvelle : recomposition collective d'un écart par les restes partiels, bilan avec reste
explicite, passage exact à l'écart suivant, et le reste porte tout le saut de la rencontre pour toute famille finie.
