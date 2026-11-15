> Version française conservée à titre de référence. Main language: English, see README.md.

# E438 — La pente de l'écart reconstituée par les contacts, les intervalles et leurs signes

Pré-enregistrement (2026-11-07), avant toute compilation. Ordre de l'auteur : interdiction de toute théorie spectrale
(CLAUDE.md « INTERDICTION SPECTRALE », maître §19.55). Fil : la pente de l'écart et la reconstitution des écarts par les
contacts.

## Vérification des neuf erreurs
1. Aucune hypothèse nouvelle. 2. Le compilateur décide. 3. Noms vérifiés par grep (`rawDemand`, `initialEdgeRemainder`,
`wholeCellSum`, `finalEdgeRemainder`, `GapHasContact`, `contactRealValue`, `wholeCellCount`, `lastContactBefore`,
`cellFraction`, `thm_noPrimeStrictlyBetweenSuccessivePrimes` réutilisés ; aucun nom dupliqué). 4. `lake build RHV6Fresh`
après tout changement. 5. Aucun premier ni OFF testé directement. 6. Aucune position radiale. 7. Aucune somme de Tours,
aucune famille, aucun canal de zéros : UNE Tour, SES contacts, les pièces qu'ils découpent, leurs signes. 8. Module isolé,
non ajouté à `RHV6Fresh.lean`. 9. Les intervalles de contacts sont des restes partiels d'écart, jamais liés à la position
d'un premier.

## Question
Entre deux rencontres la demande brute `ψ(x) − x` descend d'une unité par unité de longueur ; à la rencontre elle saute
du poids `log p`. Les contacts d'une Tour découpent l'écart en reste initial, cellules entières, reste final, chaque
pièce bordée par des contacts de signes alternés. Comment la pente se répartit-elle sur ces pièces, et que disent les
signes ?

## Objets (tous existants)
`rawDemand` (E437, canal brut : `ψ(x) − x`), `PrimeGapInterval`, `contactAt`, `contactRealValue` (signe `(−1)^k`),
`lastContactBefore`, `firstContactAfterLower`, `wholeCellCount`, `initialEdgeRemainder`, `wholeCellSum`,
`finalEdgeRemainder`, `GapHasContact`, `gap_variation_eq_remainders`, `thm_noPrimeStrictlyBetweenSuccessivePrimes`.
Mathlib : `Chebyshev.psi_eq_psi_coe_floor`, `Finset.sum_Ioc_consecutive`, `Nat.floor_eq_iff`.

## Énoncés visés (module isolé `Terminal/GapSlopeByContacts.lean`)
- R1 `rawDemand_variation` : pour `0 ≤ a ≤ b`, variation de la demande = somme des poids des entiers franchis − (b − a).
- R2 `rawDemand_pure_descent` : si aucun entier franchi n'a de poids, variation = −(b − a).
- R3 `gap_length_eq_pieces` / `gap_demand_eq_pieces` : longueur et demande de l'écart découpées par les mêmes contacts.
- R4 `no_prime_crossed_inside_gap` : aucune pièce intérieure à l'écart ne franchit un premier ;
  `finalRemainder_carries_meeting` : le poids de la rencontre est dans le reste final (quand le dernier contact est
  strictement avant la rencontre).
- R5 `contactRealValue_add_nat`, `gap_edge_contacts_sign` : signe du dernier contact = (−1)^(cellules entières) × signe du
  premier contact.
- R6 `cell_linear_length`, `finalRemainder_shorter_than_cell` : longueur linéaire d'une cellule, reste final < cellule.
- R7 `wholeCellCount_bounds` : encadrement du nombre de cellules entières par `T·log(p_{n+1}/p_n)/π`.
- R8 `alternating_sum_le_last` (tentative) : somme signée d'une suite croissante positive bornée par le dernier terme.

## Protocole
Sonde `*_SCRATCH.lean` (non versionnée, supprimée après capture), deux tentatives de compilation au plus, journaux dans
`logs/`, `#print axioms` sur chaque énoncé, puis `lake build RHV6Fresh` complet.

## Critères
A : un énoncé contredit un fait compilé. B : tout compile, faits consignés, rien déclaré manquant. C : un énoncé ne
compile pas en deux tentatives (consigné avec les erreurs exactes). Attendu : B (R8 possiblement C).
