# Audit — différences entre le régime ON et le régime OFF (2026-10-01)

Récapitulatif de toutes les différences connues entre un membre en ligne (ON, `β = 1/2`) et un membre hors
ligne (OFF, `β ≠ 1/2`), compilées ou non. Pour chaque différence : la couche, ce que voit ON, ce que voit OFF,
le statut, et la portée, c'est-à-dire si la différence peut porter une contradiction.

Statut :
- **C** : compilé dans `RHV6Fresh`, avec le nom du théorème ;
- **N** : numérique, cité sans être rejoué ;
- **M** : mathématique classique, non compilé ;
- **A** : analyse interne, non compilée.

Portée :
- **LECTURE** : la différence classe un membre donné. C'est un certificat ; elle est vraie aussi dans les mondes
  témoins et n'interdit rien.
- **POIDS** : la différence lit le poids exact `Λ(n)`. Elle est fausse dans au moins un monde témoin, donc c'est
  un candidat séparateur.
- **⟺ RH** : la différence, posée comme loi, est équivalente à RH.
- **COND** : il y a une contradiction, mais sous une prémisse non déchargée.

---

## 1. Le membre lui-même

| # | Différence | ON | OFF | Statut | Portée |
|---|---|---|---|---|---|
| 1.1 | Orbite de la réflexion et de la conjugaison | 2 zéros : `ρ`, `ρ̄`, et `1 − ρ̄ = ρ` | 4 zéros : `ρ`, `ρ̄`, `1 − ρ̄`, `1 − ρ` (zeta23) | C | LECTURE |
| 1.2 | Fibre de hauteur | un seul membre | deux membres jumeaux à la même hauteur (`fibre_multiple_iff_off`) | C | LECTURE (« toute fibre réduite à un membre » ⟺ RH) |
| 1.3 | Fonction réelle sur la ligne | zéro = une seule équation réelle en `T`, détecté par un changement de signe (`completedZeta_real_onLine`, `onLine_zero_iff_lineValue`) | zéro = deux équations réelles ; aucun changement de signe de `lineValue` à sa hauteur | C / A | LECTURE |
| 1.4 | Comptage contre changements de signe | chaque zéro compte 1 et produit 1 changement de signe | une paire compte 2 et ne produit aucun changement de signe : déficit 2 | M (argument), N (E142 : `D̂ = 0` sur 300/300, déclenché sur `regimeWitness`) | LECTURE (le comptage `N(T)` contre les changements de signe n'est pas compilé) |
| 1.5 | Côté dans la caractérisation | aucun côté | un membre de chaque côté ; « aucun zéro `β < 1/2` » ⟺ RH (`riemannHypothesis_iff_noLowerSide`) | C | ⟺ RH |
| 1.6 | Facteur radial des contacts | `r = 1` | `r > 1` sous la ligne, `r < 1` au-dessus (`contact_eq_line_mul_radial`, `radialFactor_gt_one_iff`) | C | LECTURE |
| 1.7 | Résidu de changement | `D = 0` | `D = −T log r ≠ 0`, fenêtre `−1/(2T) < D < 1/T` (`changeResidue_eq_radial`, `changeResidueAt_window`, `change_detector`) | C | LECTURE |
| 1.8 | Poussée horizontale | nulle (`onLine_horizontal_push_zero`) | non nulle | C | LECTURE |
| 1.9 | Réponse radiale au premier ordre (déformation réelle) | nulle pour un membre simple (`reflection_direction_response`) | sans objet : le membre est déjà hors ligne | C | LECTURE (vraie aussi pour `regimeWitness`) |
| 1.10 | Sortie de la ligne dans une déformation qui conserve l'équation fonctionnelle et la réalité | un membre simple ne peut pas quitter la ligne ; il faut d'abord une collision de deux membres en ligne (zéro double) | un OFF n'apparaît que par paire, après une collision | M (principe classique, non compilé) | A : localise le seul point de rupture possible (membre multiple), mais zêta n'a pas de paramètre de déformation (`zeta_generated_by_primes`) |

## 2. La Tour et ses contacts

| # | Différence | ON | OFF | Statut | Portée |
|---|---|---|---|---|---|
| 2.1 | Amplitude du terme `q^ρ/ρ` | `q^{1/2}/‖ρ‖` | `q^β/‖ρ‖` ; dans le quadruplet, le membre `β > 1/2` domine en `x^β` | C (`ExplicitFormulaLink`) | POIDS (seulement collectivement, voir 6.1) |
| 2.2 | Contacts du miroir | confondus avec ceux du membre | intercalés strictement avec ceux du membre (`mirror_contacts_interlace`) | C | LECTURE, sous même hauteur |
| 2.3 | Grille à même hauteur | une seule grille | translation rigide d'un facteur `0 < c < 1` (`sameHeight_grid_rigid_translation`) | C | LECTURE |
| 2.4 | Position d'une occurrence dans sa Tour | position de ligne | position de ligne `+ D/π` (`towerPosition_eq_line_add_residue`) | C | LECTURE (porteur unique de la composante radiale dans la flèche) |
| 2.5 | Rayons du terme | le terme est réel aux rayons de ligne | il l'est aux rayons déplacés (`zeroTerm_real_iff_ray`) | C | LECTURE (lit `Π(l)`, sans le déterminer) |

## 3. Le passage et le raccord

| # | Différence | ON | OFF | Statut | Portée |
|---|---|---|---|---|---|
| 3.1 | Régime du passage | ON → ON : vertical pur (`onLine_passage_vertical_signature`, `vertical_pure_iff_onLine`) | diagonal (`diagonal_iff_off`) puis horizontal ; une entrée horizontale est précédée d'une diagonale (`regime_entry_diagonal`) | C | LECTURE (« aucun passage diagonal » ⟺ RH) |
| 3.2 | Jonctions | VV ⟹ `β = 1/2` ; aucun changement de régime sur la ligne (`onLine_keeps_regime`) | VH ⟹ `β < 1/2`, HV ⟹ `β > 1/2` (`regimeChange_offLine`) ; un OFF force l'entrée en régime horizontal (`off_forces_regime_entry`) | C | LECTURE (« aucune entrée horizontale » ⟺ RH ; `PNoRegimeChange` ⟺ RH) |
| 3.3 | Pas de grille | contracté (`vertical_iff_pitch_contracts`) | conservé avec translation rigide (`horizontal_iff_tower_translation`) | C | LECTURE |
| 3.4 | Orientation du raccord | orienté, transport `≤ 1` (`towerRaccord_oriented_of_vertical`) | renversé, transport `> 1` à même hauteur (`towerRaccord_reverses_of_sameHeight`, `off_towerRaccord_reverses`) | C | LECTURE (orienté ⟺ la hauteur avance) |
| 3.5 | Amplitude aux raccords | décroît avec la hauteur (`amplitude_lt_of_height_lt`) | s'inverse à même hauteur (`sameHeight_amplitude_inverts_at_raccords`) | C | LECTURE |
| 3.6 | Égalités d'énergie aux raccords | — | deux égalités avec `β_e < β_l` donnent `False` (`energy_balance_two_primes_false`) | C | COND : la prémisse `PEnergyBalanceAtRaccords` ⟺ RH (V160), retirée |
| 3.7 | Pas d'un membre | `(Occ/p_min)^{β−1/2} = 1` (`memberStep_eq_one_iff`) | `≠ 1` | C | LECTURE |
| 3.8 | Charge d'une fibre / cellule V → H → V | neutre | `(M₂²/(M₁M₃))^d ≠ 1`, lue sur la translation (`fibre_charge_eq_one_iff`, `charge_reads_translation`), verrou de phase (`horizontal_term_phase_lock`) | C | LECTURE (l'existence d'une cellule depuis un OFF n'est pas compilée) |
| 3.9 | Séparation par une fenêtre de hauteur | toujours séparé | non séparé à même hauteur (`passage_separated_by_window_iff`) | C | LECTURE |
| 3.10 | Arrivée depuis la ligne | `r' = 1` | `r' > 1` ; seul `r' ≥ 1` est dérivé (`arrival_radial_ge_one`, `engaged_progression` : `β' ≤ 1/2`) | C | Sens manquant : `r' ≤ 1` |

## 4. Grammaire première et registre

| # | Différence | ON | OFF | Statut | Portée |
|---|---|---|---|---|---|
| 4.1 | Pas grammatical | identique | identique (`grammar_step_regime_blind`, `grammar_event_reads_no_radial`) | C | AUCUNE DIFFÉRENCE |
| 4.2 | Événement premier, certificat grammatical | complet | complet et renversé (`off_grammaticalRaccord_complete_and_reversed`) | C | AUCUNE DIFFÉRENCE de contenu |
| 4.3 | Registre d'une paire | écart à la grammaire `= H` (`onLine_pair_ledger`) | à même hauteur `H = 0`, mais `Π` avance strictement plus que la grammaire (`horizontal_ledger_exceeds_grammar`, `off_pair_vs_onLine_pair`) | C | LECTURE (l'excès de phase n'est confronté à rien de fixé) |
| 4.4 | Excès de transition | `= H` | diagonale `< H`, même hauteur `> 0` ; déficit remboursé exactement (`transition_kinematics_by_configuration`, `first_off_configuration_two_transitions`, `first_off_configuration_alternation_floor`) | C | LECTURE |
| 4.5 | Contenu radial d'une chaîne | nul | `−T_m log r_m`, quelle que soit la longueur (`chain_from_line_radial_content`) | C | LECTURE |
| 4.6 | Identité du registre | vraie | vraie pour toute position radiale (`required_eq_realised`) | C | AUCUNE DIFFÉRENCE |
| 4.7 | Comptage de Tchebychev du premier partagé | `⌊C⁺⌋` | `⌊r·C⁺_ligne⌋`, avec `\|log r\| < 1/T²` (`countedPrime_eq_vonMangoldt`) | C / A | LECTURE aveugle hors d'une fenêtre relative `1/T²` |

## 5. Le spectre comme organisme

| # | Différence | ON | OFF | Statut | Portée |
|---|---|---|---|---|---|
| 5.1 | Identité spectrale | chaque membre est retrouvé | chaque membre est retrouvé, y compris le OFF (`off_identity_not_erased`, `recovers_member`) | C | LECTURE (l'unicité ne lit pas `Re ρ`) |
| 5.2 | Représentation en ligne du canal | existe | n'existe pas (`riemannHypothesis_iff_onLine_representation`) | C | ⟺ RH |
| 5.3 | Écart au tout en ligne | nul | non nul et non absorbable (`off_member_deviates`, `lineDeviation_not_absorbed`) | C | LECTURE (« écart nul » ⟺ RH) |
| 5.4 | Compensation par le complément | exacte | exacte (`off_forced_compensation`) | C | AUCUNE DIFFÉRENCE (même identité lue après soustraction) |
| 5.5 | Système rigide global | quinze couches remplies | les quinze couches tiennent, et reste, grammaire et géométrie sont conservés (`off_inside_globalRigidSystem`, `off_conserves_three_equalities`) | C | AUCUNE DIFFÉRENCE structurelle |

## 6. Le reste arithmétique et le poids exact : seule zone séparatrice

| # | Différence | ON | OFF | Statut | Portée |
|---|---|---|---|---|---|
| 6.1 | Croissance du reste `ψ(x) − x` | `O(√x log²x)` | `Ω±(x^{β−ε})` : oscillation au moins de l'ordre `x^β` (Landau, Ingham) | C pour un sens (`radial_le_of_remainder_growth`), M pour l'oscillation | ⟺ RH (`riemannHypothesis_iff_remainder_sqrt_growth`) |
| 6.2 | Poids d'une paire dans l'incrément du reste | deux membres pèsent `2x^{−1/2}` | une paire pèse strictement plus (`off_pair_density_exceeds_line`) | C | POIDS, mais l'incrément exigé ne fixe que la somme sur tous les zéros |
| 6.3 | Loi de Landau `moyenne cos(T_n log x) = −c Λ(x)/√x` | vérifiée | un OFF ajoute un terme en `x^{β−1/2}` | N (E142, corrélation 0,998), M | POIDS, collectif |
| 6.4 | Module des poids premiers dans une famille | conservé ⟺ réponse radiale nulle (`weightFamily_radial_zero_iff_weight_modulus`) | `Λ(n)·n^c` déplace le membre de `Re c` | C | POIDS (contrôle, pas un mécanisme pour zêta) |
| 6.5 | Mondes témoins | — | `ζ(s−δ)ζ(s+δ)` : mêmes premiers, poids `Λ(n)(n^δ+n^{−δ})`, tous les zéros OFF ; `regimeWitness` : ON puis jumeaux, sans premiers ; `engagedBreakWorld` : poids `Λ(n)n^c`, ON à `T` puis jumeaux à `T+τ` ; Davenport–Heilbronn : équation fonctionnelle sans produit d'Euler, zéros OFF | C (trois), M (Davenport–Heilbronn) | Fixe la règle : seule une différence qui lit `Λ(n)` exact **et** le produit d'Euler peut séparer |

## 7. Critères classiques non compilés (tous équivalents à RH)

| # | Critère | ON (sous RH) | OFF | Statut |
|---|---|---|---|---|
| 7.1 | Speiser | `ζ'` sans zéro dans `0 < Re s < 1/2` | un OFF force un zéro de `ζ'` à gauche | M, ⟺ RH |
| 7.2 | Li | `λ_n ≥ 0` pour tout `n` | `λ_n < 0` pour `n` grand, avec une croissance exponentielle en `n·log\|ρ/(ρ−1)\|` | M, ⟺ RH |
| 7.3 | Positivité de Weil | forme positive | une fonction test rend la forme négative | M, ⟺ RH |
| 7.4 | de Bruijn–Newman | `Λ_dBN = 0` | `Λ_dBN > 0` : sous le flot de la chaleur, une paire OFF se rapproche, entre en collision sur la ligne et s'y sépare en deux membres ON ; `Λ_dBN ≥ 0` est prouvé (Rodgers–Tao) | M, ⟺ RH |
| 7.5 | Nyman–Beurling, Robin, Lagarias | approximation ou inégalité vérifiée | violée | M, ⟺ RH |
| 7.6 | Densité de zéros | — | `N(σ,T) = o(N(T))` pour `σ > 1/2` (Bohr–Landau) : presque tous les zéros sont près de la ligne ; plus de 40 % sont sur la ligne (Selberg, Levinson, Conrey) | M : borne la proportion de OFF, n'exclut aucun OFF isolé |

---

## Synthèse

1. **Les couches 1 à 5 sont des lectures.** Elles sont toutes compilées : membre, Tour, passage, raccord,
   grammaire, registre, organisme spectral. Chacune distingue ON de OFF sur un membre donné, mais aucune n'est
   un déclencheur. Elles tiennent mot pour mot dans un monde qui contient un OFF (5.5, 4.2, 4.6), donc aucune
   contradiction ne se dérive d'elles seules. Lignes sans aucune différence : 4.1, 4.2, 4.6, 5.4, 5.5.
2. **Une contradiction conditionnelle existe** (3.6). Sa prémisse est équivalente à RH.
3. **La seule zone séparatrice est la couche 6**, celle qui lit le poids exact `Λ(n)`. La différence y est
   quantitative et collective (6.1 à 6.3) : l'excès d'une paire OFF n'est confronté qu'à la somme sur tous les
   zéros. Le transformer en contradiction revient à la borne en `√x` du reste, équivalente à RH.
4. **Les critères classiques (7.1 à 7.5) sont des reformulations.** Ils ne fournissent pas de différence
   exploitable sans RH.
5. **Pour la flèche ON ⇒ ON (`CanonicalTransition`)** :
   - le porteur unique de la composante radiale est la position d'entrée du premier partagé (2.4) ;
   - aucune différence des couches 1 à 5 ne la fixe ;
   - la différence 1.10 est le seul énoncé local de structure qui contraint un changement de régime : une
     sortie de la ligne exige un membre multiple. Ce principe n'est pas compilé, et zêta n'a pas de paramètre
     de déformation.
6. **Ce qui manque** : une lecture du poids exact propre à un passage, qui ne passe pas par la somme sur tous
   les zéros. Aucune des 48 différences recensées n'en est une.
