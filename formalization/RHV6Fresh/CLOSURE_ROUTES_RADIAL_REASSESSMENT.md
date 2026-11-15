# Pistes de fermeture : réévaluation au signal exact (audit radial total, 2026-10-13)

But conservé, non modifié : `radial_conservation_anchored` (`Terminal/DemonstrationChain.lean:399`). Ses hypothèses sont :
- premier zéro ON ;
- passage vertical ;
- départ ON ;
- historique ON.

Il reste ouvert sous la forme `⊢ radialFactor ⟨p.zLaterMember, hL⟩ = 1`. Aucune hypothèse n'est ajoutée, aucune équivalence à
RH n'est posée.

Sonde hors build `experiments/e242_exact_signal_audit/ProbeE242_ExactCurrent.lean` : une erreur, le but réécrit exactement en
`exactCurrentRatio(E_e, E_l)(log C_0) = exactCurrentRatio(E_e, E_l)(log C_1)`
(`exact_current_transport_iff_radialFactor`). Les éléments suivants sont en contexte, et aucun ne ferme le but :
- forme polaire ;
- courant croisé exact ;
- interférence exacte ;
- contacts absolus ;
- correction miroir.

## Tableau de synthèse

Colonnes `β amplitude` / `β phase` : `β` est-il présent dans l'amplitude, dans la phase du signal utilisé ?
Les colonnes « ON valide » et « OFF exclu » portent sur la configuration testée.

| Piste | β amplitude | β phase | Signal exact | Contrainte indépendante | ON valide | OFF exclu | Lean | Conclusion |
|---|---|---|---|---|---|---|---|---|
| enroulement, contacts absolus | non (contacts) | oui (`θ`) | oui | non | oui | non | `windingNestedAtInfinity_of_precedes`, `exact_contacts_determine_parameters` | A + B : enroulement vrai pour toute `β`, contacts = détecteur |
| conservation radiale supposée | — | — | — | non (c'est le but) | oui | — | `riemannHypothesis_iff_conservation_and_base` | C, circulaire |
| poussée verticale | oui | non | oui | non | oui | non | `offMirror_all_elements_hold_and_vertical_force_fails` | E au passage miroir |
| écarts premiers, positivité | non | phase seule | oui | non | oui | non | `gap_signature_constraint_vacuous` | A (télescope) |
| deux écarts successifs | `d` à l'ordre 1 dans la charge | oui | oui | non | oui | non | `windowCharge_log_eq_zero_iff` | B ; les données de la grammaire ne contiennent pas `d` (E232) |
| raréfaction des premiers | non | phase | oui | non | oui | non | `prime_free_run`, `window_abel_all_sameHeight` | A |
| charge orientée des patterns | oui | non | oui | non | oui | non | `fibre_charge_eq_one_iff` | B |
| paires miroirs | oui (paire en `d`) | oui | oui | non | oui | non | `mirror_pair_no_internal_compensation`, `exact_mirror_cross_lt_double` | B (détecteur d'ordre `d²`) |
| énergie sur les rayons | oui | non | oui | non | oui | non | `energyRatio_flat_iff` | C |
| balance aux raccords | oui | non | oui | non | NON (fausse ON) | — | `raccord_norm_equalities_false_of_vertical` | E, rejetée |
| amplitudes exactes | oui | — | oui | non | oui | non | `exactSignal_norm`, `successive_tower_ratio` | A |
| phases et déphasages exacts | — | oui | oui | non | oui | non | `exactSignal_polar`, `conj_mul_exactSignal` | A |
| transmission du courant | oui | — | oui (E242) | non | oui | non | `exact_current_transport_iff_radialFactor` | C (⟺ but) |
| courants croisés et collectifs | oui | oui (`θ₁ − θ₂`) | oui (E242) | non | oui | non | `exactCross_eq`, `exactCollectiveCurrent_eq_sum` | A + B |
| battements harmoniques | oui | oui | oui | non | oui | non | `mirror_beat_modulus`, `exact_interference_normSq` | A |
| domination du premier zéro | oui | — | oui | non | oui (ON) | non | `firstZero_dominates`, `individual_domination_iff_riemannHypothesis` | C sur tous les rangs |
| comptage certifié | — | — | — | OUI, locale (`T ≤ 28`) | oui | oui sous 28 | `ZetaBox*`, `first_three_canonical_onLine` | D locale, non transportée |
| formule explicite de von Mangoldt | oui (somme) | oui | oui | non | oui | non | `smoothedRemainder_eq_tsum_residueTerm`, `psiRecoveredFromZeros_eq_psi` | A |
| reconstruction de `ψ`, `J`, `π`, `li` | oui | oui | oui | non | oui | non | `remainder_eq_preceding_add_following` ; E204, E242 fig. 2 | A ; la borne `√x` du reste ⟺ RH |
| contraintes spectrales et de stabilité | oui | — | — | non | oui | non | `shiftedCompleted_one_sub`, `harmonicEnergy_flat_iff_radialFactor` | C ; contre-modèle `Λ(s−δ)Λ(s+δ)` |
| contre-modèles CM1–CM13 | — | — | — | — | — | — | `winding_admissible_current_free`, `parameter_grid_admissible` | conservés, toujours valides au signal exact |
| combinaison 4.4 (contacts absolus + `M` + `1/ρ` + deux écarts) | oui | oui | oui (E242) | non | oui | non | sonde E242 | 0 violation sur 1 075 cas : fonctions de `(β_l, T_l)` existant pour toute `β_l` |

## Obligation restante

Une borne démontrée, indépendante de la position des zéros, du complément collectif d'exposant `< 1/2 + d`. Cela revient à
une bande sans zéro. Toutes ses formes connues sont ⟺ RH une fois quantifiées sur tous les passages.

Le signal exact ne la remplace pas. Le coefficient `1/ρ` est une constante en `t`, fonction de `(β, T)`. Il déplace des
contacts, des annulations et des minima d'interférence d'une quantité qui dépend de `β` : ce sont des détecteurs. Il ne relie
pas `β_l` à une donnée du départ.

## Verdict

| Ligne | Valeur |
|---|---|
| EXACT_SIGNAL_ARCHITECTURE | PASS (`Terminal/ExactSignalArchitecture.lean`, 41 théorèmes, 18 objets) |
| RADIAL_INFORMATION_PRESERVED | PASS (`1/ρ` restauré ; conversions et pertes démontrées et mesurées) |
| CONTRACT_AUDIT | PASS (`AUDIT_RADIAL_TOTAL_20261013.md` ; type D : certificats finis seuls) |
| EXPERIMENTS_REBUILT | PASS (172 scripts classés ; E240, E241 CORRECTED ; E44, E96–E100, sondes E116 NOT_REPRODUCIBLE) |
| GRAPHICS_CORRECTED | PASS (E242, quatre figures) |
| ON_REGRESSION | PASS (ON admissible dans tous les scénarios ; inversion exacte des trois premiers zéros à 1e−9) |
| OFF_COUNTERMODELS | PASS (CM1–CM13 valides au signal exact ; 1 075 configurations OFF hypothétiques sans violation) |
| INDEPENDENT_CLOSURE_CONSTRAINT | NOT_PROVED |
| RADIAL_CONSERVATION_PROVED | NOT_PROVED |
| RH_FOUND | NOT_PROVED |
