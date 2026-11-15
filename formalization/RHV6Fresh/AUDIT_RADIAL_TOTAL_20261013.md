# Audit radial total de RHV6Fresh (2026-10-13)

Question : l'usage de représentations harmoniques normalisées (modes unitaires, différences de phases, courants réduits,
observables collectives) a-t-il masqué une information sur `β` qui fournirait une contrainte de fermeture ?

Réponse : non. Le signal exact est restauré dans Lean (`Terminal/ExactSignalArchitecture.lean`, 41 théorèmes, 18 objets) et
toutes les comparaisons concernées ont été recalculées (E242, 16 PASS). Le coefficient `1/ρ` est constant en `t` : il ne
change aucune caractérisation, il corrige deux interprétations (E240, E241) et il n'apporte aucune contrainte de type D.

Documents liés : `RADIAL_SIGNAL_CONVERSIONS.md` (formules), `EXPERIMENTS_RADIAL_CORRECTION_INDEX.md` (172 scripts),
`CLOSURE_ROUTES_RADIAL_REASSESSMENT.md` (pistes), `experiments/e242_exact_signal_audit/` (données, figures, sonde).

## 1. Inventaire statique des représentations (Lean)

`e242_lean_inventory.csv` : 614 occurrences de onze identifiants, avec fichier, ligne, nature, signal, `β` dans l'amplitude,
`β` dans la phase, coefficient `1/ρ` et conséquence.

| Identifiant | Signal | `β` amplitude | `β` phase | `1/ρ` | Correction |
|---|---|---|---|---|---|
| `zeroTerm` (67 fichiers à signal exact) | exact `x^ρ/ρ` | oui | oui (`θ`) | conservé | aucune |
| `energyRatio`, `successive_tower_ratio` | exact, normes | oui | sans objet | `‖ρ‖` conservé | aucune |
| `towerPosition` | exact, phase `(T log q − θ)/π` | non | oui | `arg ρ` conservé | aucune |
| `complexMode` (`HarmonicRestoringLaw`) | unitaire | oui (`e^{dt}`) | non | supprimé | conversion `unitMode_eval_eq_complexMode`, `exact_eq_unit` |
| `harmonicMode`, `harmonicEnergy` | unitaire réel | oui | `φ` paramètre libre | supprimé | aucune caractérisation affectée (constante) |
| `harmonicCurrent`, `reducedCurrent`, `currentRatio` | unitaire | oui | sans objet | supprimé (constante) | `exactCurrent_eq_scaled_reduced`, `exactCurrentRatio_eq` : multiple réel positif, tests inchangés |
| `crossCurrent`, `collectiveCurrent` | unitaire | oui | non (`θ₁ − θ₂` perdu) | supprimé | `exactCross_eq`, `exactCross_eq_rotated_unit` (rotation complexe) |

Trois fichiers seulement utilisent le mode unitaire : `HarmonicRestoringLaw`, `HarmonicCurrentTransport` et
`HarmonicCrossCurrent`. `ExactSignalArchitecture` cite le mode unitaire pour le convertir. Aucun de ces modules n'est importé
par `DemonstrationChain.lean`.

## 2. Classement des contrats

Les types sont ceux de la mission :
- A : identité universelle ;
- B : détecteur radial ;
- C : caractérisation équivalente à la fermeture ;
- D : contrainte indépendante ;
- E : proposition fausse ou trop forte.

| Module | Énoncé | Type | Raison |
|---|---|---|---|
| `TowerRaccord` | champs `M = p_min(e) = Occ(l)`, cellules, encadrements, `transport` | A | chaque champ est rempli par un théorème vrai pour toute `β` (`towerRaccordOf`) |
| `TowerRaccord` | `towerRaccord_eq` | A | unicité d'une structure pour deux Tours DÉJÀ fixées ; ce n'est pas une rigidité radiale |
| `TowerRaccord` | `transport : ‖Z_l(M)‖/‖Z_e(M)‖ = M^{β_l−β_e}‖ρ_e‖/‖ρ_l‖` | A | rapport calculé ; ce n'est pas une « conservation » |
| `TowerRaccord` | `towerRaccord_oriented_of_vertical` | A | vrai dès que la hauteur avance, pour toute `β` |
| `LocalReading` | `localReading_modeA` | A | théorème sous `Δβ = 0` (hypothèse) |
| `LocalReading` | prémisse locale (lecture au raccord) | C / E | ⟺ RH à une condition près ; FAUSSE au passage de même hauteur dès `T ≥ 2` (`localReading_fails_modeC`) |
| `RegimeTransportAudit` | `arrival_fiber_interval_equivalent` | C | arrivée ON ⟺ fibre ON ⟺ `ΔD = 0` |
| `RegimeTransportAudit` | `inside_large_iff`, `inside_small_iff`, `inside_primes_iff_at_two` | B | inclusion : `x ≥ 1` ⟺ `β ≤ 1/2` ∧ support ; `0 < x ≤ 1` ⟺ `β ≥ 1/2` ∧ support ; premiers ⟺ `x = 2` |
| `RegimeTransportAudit` | `transport_ratio_eq_at_two_points_iff` | C | égalité des rapports en deux points ⟺ même `β` |
| `RegimeTransportAudit` | `raccord_norm_equalities_false_of_vertical` | E | égalités de normes aux deux raccords FAUSSES sur tout passage qui monte, ON compris : rejetées comme fermeture |
| `VerticalForce` | F1a `mirror_net_horizontal_force_zero` | A | vraie pour tout zéro |
| `VerticalForce` | F1b, F1c, F2b, F2c | B | détecteurs (`= 0 ⟺ β = 1/2`, entrelacement, `p_min` distinct) |
| `VerticalForce` | poussée verticale au miroir (F4) | E | échoue à tout premier sur le passage miroir |
| `HorizontalExclusion` | `contactMinus_eq_iff_radial_eq` | B | contacts égaux à même hauteur ⟺ même `β` |
| `HorizontalExclusion` | `mirror_amplitude_ratio` | A | identité |
| `HorizontalExclusion` | exclusion de `HorizontalMirrorRealization` | C | ⟺ RH |
| `HorizontalExclusion` | `energy_balance_two_primes_false` | E | égalité de normes à deux premiers fausse |
| `EnergyIdentity` | `log_amplitude_ratio_eq` (`log(A_l/A_e) = H − V`) | A | identité |
| `EnergyIdentity` | `PVerticalDominatesAtRaccord` | C | non compilée, impliquée par une prémisse retirée |
| `HarmonicCurrentTransport` | `harmonicCurrent_eq`, `currentRatio_eq` | A | mode unitaire ; versions exactes `exactCurrent_eq`, `exactCurrentRatio_eq` |
| `HarmonicCurrentTransport` | tests B, C, D | C | ⟺ même `d`, inchangés au signal exact (`exactCurrentRatio_two_points_iff`) |
| `HarmonicCurrentTransport` | `winding_admissible_current_free` | A | contre-modèle : grille admissible pour toute `β < 1/2` |
| `HarmonicCurrentTransport` | `contact_current_transport_iff` | C | ⟺ but ; version exacte `exact_current_transport_iff_radialFactor`, même nature |
| `HarmonicCrossCurrent` | `crossCurrent_eq`, `collectiveCurrent_eq_sum` | A | mode unitaire ; versions exactes `exactCross_eq`, `exactCollectiveCurrent_eq_sum` |
| `HarmonicCrossCurrent` | `mirror_cross_current_blind` | A (unitaire) | vrai pour les modes unitaires ; l'interprétation « la partie croisée ne lit pas `d` » est FAUSSE pour le signal exact (`exact_mirror_cross_lt_double`, détecteur B d'ordre `d²`) ; portée ajoutée au docstring |
| `HarmonicCrossCurrent` | `currentRatio_eq_tower_ratio_sq` | A | le rapport unitaire réécrit les normes exactes |
| `ExactSignalArchitecture` | conversions, forme polaire, courants, interférence | A | identités vraies pour tout `(β, T)` |
| `ExactSignalArchitecture` | `exact_contacts_determine_parameters`, `exact_mirror_cross_lt_double` | B | détecteurs |
| `ExactSignalArchitecture` | `exact_current_transport_iff_radialFactor`, `exactCurrentRatio_two_points_iff` | C | caractérisations |
| `DemonstrationChain` (contexte de `:399`) | comptage, grammaire, raccord, contacts, fibres, captivité, fenêtres | A / B / C | aucune hypothèse du contexte ne contredit `hBelow` ; contre-modèle `reducedContactSystem_not_identifying` |
| comptage certifié 15 / 22 / 28 (`ZetaBox*`, `BoxCountHeight`) | `N(15) = 1`, `N(22) = 2`, `N(28) = 3` | D, locale | seules contraintes indépendantes du dépôt ; elles imposent ON aux trois premiers zéros et ne se transportent à aucune hauteur au-delà |

Résultat : en dehors des certificats finis de comptage, aucune contrainte de type D n'existe. Restaurer `1/ρ` n'en crée pas.

## 3. Contrôles spéciaux

- **Raccord.** `TowerRaccord` ne contient aucune contrainte indépendante : tous ses champs sont construits depuis les
  définitions. `towerRaccord_eq` est l'unicité d'une structure pour deux Tours fixées.
- **Inclusion (E212–E217).** Les trois domaines sont séparés dans Lean :
  - `x ≥ 1` : `inside_large_iff` ;
  - `0 < x ≤ 1` : `inside_small_iff` ;
  - premiers : `inside_primes_iff_at_two`, réduit à `x = 2`.
  
  Une inclusion sur les premiers ne se prolonge pas à `x > 0` (`passage_inclusion_split`).
- **Égalités de normes.** Elles sont fausses sur deux zéros ON de hauteurs différentes (`raccord_norm_equalities_false_of_vertical`,
  E216) : rejetées immédiatement comme fermeture.

## 4. Les quatre scénarios (E242 D, 12 cas)

Hauteurs testées : `T_e`, `T_l` aux rangs 1, 10 et 100. L'arrivée est le membre de partie réelle minimale de sa fibre
(`arrival_radial_le_fiber`).

| Scénario | Arrivée | Fenêtre des contacts | Identité du raccord | Courant exact égal à deux contacts |
|---|---|---|---|---|
| ON → ON | `β = 1/2` | tenue | tenue | oui |
| ON → OFF bas | `β = 0,3` | tenue | tenue | non (détecteur) |
| ON → OFF haut, miroir bas | le miroir bas (`0,3`), le haut n'est pas l'arrivée | tenue | tenue | non |
| fibre mixte (ON + paire) | le bas (`0,3`) | tenue | tenue | non |

ON reste admissible. Aucun scénario OFF ne viole une contrainte acquise. Seul le test à deux abscisses le sépare, et ce test
⟺ le but.

## 5. Combinaison 4.4

Combinaison testée : contacts absolus, premier partagé `M`, coefficients `1/ρ` et deux écarts successifs. Le balayage porte sur
1 075 cas (43 passages, `β_l ∈ [0,02 ; 0,5]`) : 0 relation violée. Chaque quantité est une fonction de `(β_l, T_l)` qui existe
pour toute `β_l` : fenêtre `1 ≤ λ < e^{1/(2T²)}`, identité du raccord, inversion finie, écarts et `q² ≠ pr`.

**INDEPENDENT_CLOSURE_CONSTRAINT = NOT_PROVED.** Aucune contrainte indépendante n'est obtenue.
