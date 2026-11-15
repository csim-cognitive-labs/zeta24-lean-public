# Index de correction radiale des expériences (audit radial total, 2026-10-13)

Méthode. Chaque script de `experiments/` (172 scripts) a été classé automatiquement par marqueurs
(`experiments/e242_exact_signal_audit/e242_exact_signal_audit.py`, partie B ; sortie `e242_script_inventory.csv`).
- EXACT : `x^ρ/ρ`, `/rho`, `arctan(T/β)` ou `zeroTerm`.
- UNIT : `exp((d + 1j T)t)`, `complexMode` ou mode harmonique.
- ZERO_SANS_TERME : les zéros sont lus par hauteur, comptage, contacts de ligne ou grammaire, sans terme individuel.
- SANS_ZERO : premiers ou grammaire seuls.

Les scripts marqués UNIT ont été revus à la main, puis recalculés au signal exact lorsqu'il s'agissait d'une contribution
analytique (E242, parties C et D). Les résultats historiques ne sont pas effacés ; les corrections sont ajoutées dans les
README et les rapports concernés.

Statuts possibles : `UNCHANGED`, `CORRECTED`, `CONCLUSION_WEAKENED`, `INVALIDATED`, `CIRCULAR`, `REQUIRES_NEW_PROOF`,
`NOT_REPRODUCIBLE`.

Bilan : 170 UNCHANGED, 2 CORRECTED (E240, E241), 0 INVALIDATED. Les numéros prioritaires sans script dans l'arbre ni dans
l'historique git sont NOT_REPRODUCIBLE (§1).

## 1. Expériences prioritaires de la mission

| Exp. | Script / données | Normalisation | Recalcul exact | Statut | Note |
|---|---|---|---|---|---|
| E44 | aucun script dans l'arbre ni l'historique de `formalization/` | — | impossible | NOT_REPRODUCIBLE | inversions initiales ; l'inversion exacte est démontrée (`inversion_from_consecutive_contacts`, `exact_contacts_determine_parameters`) |
| E88, E88c, E88d | `e088*.py` | `x^ρ/ρ` exact, cercles ramenés à `√q` | non requis | UNCHANGED | cercles = terme complexe isolé dans son plan, jamais le champ (E163b, E204) |
| E93 | `e093_*.py` | exact | non requis | UNCHANGED | — |
| E96–E100 | plan `PLAN_E096_E100_verrou_hauteur_20260927.md` seul | — | impossible | NOT_REPRODUCIBLE | aucun script versionné |
| E101 | `e101_*.py` | exact (contacts `arctan(T/β)`) | non requis | UNCHANGED | déplacement de β à hauteur fixée lu par amplitude et phase exactes |
| E111, E112, E114 | `e11{1,2,4}_*.py` | hauteurs et phases de ligne | non requis | UNCHANGED | aucun mode unitaire |
| E115 | `e115_*.py` | exact | non requis | UNCHANGED | couplage inter-Tours lu sur `x^ρ/ρ` |
| E116 | sondes retirées en `1a61a410` | `‖zeroTerm‖` exact | — | NOT_REPRODUCIBLE (sondes) ; résultat compilé | égalités de normes aux deux raccords FAUSSES sur tout passage qui monte, ON compris (`raccord_norm_equalities_false_of_vertical`, `energy_balance_two_primes_false`) : TYPE E |
| E150 | `e150_*.py` | `Σ 2Re x^ρ/ρ` exact | non requis | UNCHANGED | pente radiale lue sur le canal exact |
| E151, E157 | scripts | contacts de ligne ; modèle de poids | non requis | UNCHANGED | — |
| E158 | `e158_*.py` | exact | non requis | UNCHANGED | charge `(M₂²/(M₁M₃))^d` : identité |
| E200–E217 | répertoires `e2xx_*` | exact ou comptage | non requis | UNCHANGED | E213 sans zéro (modèle fini) ; E216 `‖Z‖` exact |
| E218–E223 | répertoires | `(b^s − a^s)/s` exact | non requis | UNCHANGED | — |
| E224 | `e224_harmonic_restoring_law.py` | UNIT | E242 C4 | UNCHANGED | stationnarité de l'énergie ⟺ `d = 0` inchangée par la constante `1/‖ρ‖²` ; caractérisation du but (CIRCULAR comme fermeture, déjà classé) |
| E225 | `e225_*.py` | EXACT + UNIT | — | UNCHANGED | dénominateurs exacts déjà utilisés |
| E226–E228 | Ξ, ξ'/ξ, opérateurs | sans terme individuel | — | UNCHANGED | — |
| E229 | `e229_*.py` | `∫t^{ρ−1}` exact | — | UNCHANGED | — |
| E230–E238 | sondes, fenêtres | exact | — | UNCHANGED | — |
| E239 | `e239_*.py` | Ξ, comptage, canal J | — | UNCHANGED | part du premier zéro dépendante de la fenêtre |
| E240 | `e240_harmonic_current.py` | UNIT | E242 C4′ | CORRECTED | rapport exact `= (T_l‖ρ_e‖²)/(T_e‖ρ_l‖²)·Q` (constante ∈ [0,673 ; 0,995]) ; variation entre contacts identique ; tests B–E inchangés ; E reste CIRCULAR |
| E241 | `e241_tower_coupling.py` | UNIT | E242 C5, C6 | CORRECTED | « partie croisée miroir `2T` pour toute `d` » propre au mode unitaire ; exact : `< ` double ON dès `d ≠ 0` (ordre `d²`) ; annulations du croisé décalées de `arctan(β₁/T₁)/ΔT` ; AUTHENTIC_TOWER_COUPLING : toujours aucun |

Aucune conclusion invalidée n'était utilisée dans la chaîne terminale : `DemonstrationChain.lean` n'importe aucun des
trois modules à mode unitaire.

## 2. Inventaire complet (172 scripts)

| Exp. | Script | Classe | Statut | Note |
|---|---|---|---|---|
| — | `audit_semantique/diffnames.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| — | `audit_semantique/grepcounts.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| — | `audit_semantique/impact_tour_grille/calc.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| — | `audit_semantique/impact_tour_grille/calc2.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| — | `audit_semantique/impact_tour_grille/classify_thms.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| — | `audit_semantique/impact_tour_grille/select_thms.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| — | `audit_semantique/miss.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| — | `audit_semantique/modules.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| — | `audit_semantique/run_extract.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| — | `audit_semantique/summarize.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| — | `block_ranks_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| — | `c_lecture_rank_audit_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E076 | `e076_explicit_formula_identification_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E076 | `e076_geometric_trajectories_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E077 | `e077_spiral_axis_crossing_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E078 | `e078_axis_from_zero_set_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E079 | `e079_tower_starting_points_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E080 | `e080_canonical_origin_stop_event_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E081 | `e081_next_expected_pivot_stop_factor_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E082 | `e082_two_data_min_vs_target_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E083 | `e083_predecessor_pointed_prime_chain_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E084 | `e084_reversed_second_tower_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E084B | `e084b_reversed_tower_jumps_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E085 | `e085_same_height_two_towers_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E086 | `e086_four_zeros_all_situations_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E087 | `e087_pair_height_gap_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E088 | `e088_tower_geometry_complex_plane_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E088C | `e088c_two_consecutive_on_towers.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E088D | `e088d_two_consecutive_on_towers_axes.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E093 | `e093_multi_tower_progression_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E094 | `e094_off_zero_insertion_prime_shift_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E095 | `e095_forced_mirror_pair_insertion_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E101 | `e101_fixed_height_beta_displacement_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E102 | `e102_mod6_grammar_rigidity_at_scale_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E103 | `e103_prime_gap_magnitude_decomposition_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E104 | `e104_zero_sequence_magnitude_invariance_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E105 | `e105_gap_family_prediction_and_saturation_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E106 | `e106_tower_boundary_intrinsic_vs_injected_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E109 | `e109_grid_alignment_shift_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E111 | `e111_translation_vs_progression_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E112 | `e112_phase_quantum_per_event_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E113 | `e113_translation_vs_next_progression_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E114 | `e114_inter_tower_repulsion_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E115 | `e115_inter_tower_coupling_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E117 | `e117_intrinsic_stop_trace_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E117 | `e117_two_towers_energy_conflict_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E118 | `e118_full_stage_energy_series_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E118 | `e118_phase_uniqueness_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E119 | `e119_family_pushforward_height_vs_radial_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E119 | `e119_on_line_vs_two_off_same_height_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E120 | `e120_energetic_insertion_two_boundaries_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E120 | `e120_stop_reverse_engineering_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E121 | `e121_tower_data_collection_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E121 | `e121_vertical_energy_transmission_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E122 | `e122_amplitude_inequality_on_e121_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E123 | `e123_vertical_force_hypotheses_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E124 | `e124_ray_capture_depth_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E127 | `e127_radial_budget_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E128 | `e128_phase_position_at_raccord_published.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| E129 | `e129_spectral_stability_on_off_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E130 | `e130_quartet_holonomy_published.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| E131 | `e131_conjugation_metapattern_audit.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E135 | `e135_all_off_world_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E136 | `e136_primal_event_history_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E137 | `e137_residual_increment_off_test_published.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E137B | `e137bis_diagonal_cross_split_by_exact_gap.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E142 | `e142_reverse_engineering_300_zeros_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E146 | `e146_entry_position_arrow_hypotheses.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E147 | `e147_pointed_primes_on300_vs_off150.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E148 | `e148_tower_grid_all_primes.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E149 | `e149_grid_translation_imprint.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E150 | `e150_li_remainder_height_radial_slope.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E151 | `e151_fixed_k_vs_rank_k_cells.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E153 | `e153_landau_audit_real_channel_li.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E154 | `e154_quadratic_energy_tower_cells.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E155 | `e155_diagonal_refutation_exact_axis.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E156 | `e156_oriented_flux_check.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E157 | `e157_grammar_words_load_and_depth.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E158 | `e158_regime_window_packet.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E159 | `e159_pair_vs_double_curvature_horizon.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E160 | `e160_continuations_interaction_engaged_towers.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E161 | `e161_tower_symmetry_table.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E162 | `e162_mirror_loop_gauge.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E163 | `e163_mirror_antisymmetric_channel.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E163 | `e163_on_off_tower_geometry.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E163B | `e163b_three_zeros_on_off_towers.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E164 | `e164_remainder_captive_constant.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E165 | `e165_tower_to_tower_hierarchy.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E166 | `e166_first_tower_parameter_horizon.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E168 | `e168_following_sum_all_zeros.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E169 | `e169_marginal_refinement_per_zero.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E170 | `e170_first_tower_encapsulation.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E171 | `e171_li_refinement_and_witness_worlds.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E172 | `e172_second_off_zero_window.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E173 | `e173_off_surplus_audit.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E174 | `e174_certified_count_and_detection.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E174B | `e174b_certified_tail_and_detection.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E175 | `e175_windows_12_24_36.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E176 | `e176_tangential_inversion_2_3.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E177 | `e177_interval_decay_and_off_window.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E178 | `e178_gain_decomposition_prime_support.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E179 | `e179_grammar_windows_12_24_36.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E180 | `e180_zero_contributions_plate.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E181 | `e181_complete_interaction_nested_supports.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E182 | `e182_coupling_pitch_frequency_amplitude.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E183 | `e183_tower_chains_joint_constraints.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E184 | `e184_first_removal_collective_mechanics.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E185 | `e185_anchor_certification.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E186 | `e186_insertion_defect_vs_pair_deformation.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E187 | `e187_chains_windows_beats_joint.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E188 | `e188_background_cells_modulation.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E189 | `e189_stage_cells_expected_next.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E190 | `e190_finite_grammar_layer.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E191 | `e191_em10_certificate_generator.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| E192 | `e192_zeta_box_certificate_generator.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| E193 | `e193_window_floor_signed_mass_check.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| E194 | `e194_cell_error_exact_definitions.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| E195 | `e195_first_window_margin.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E196 | `e196_zeta_box_height_generator.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E197 | `e197_independent_check.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E197 | `e197_window_comparison.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E198 | `e198_transmissions_300.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E199 | `e199_increment_matrix_fibers.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E200 | `e200_arrival_fiber_hypotheses.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E201 | `e201_first_zero_contact_comparison.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E202 | `e202_cell_passage_restitution.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E203 | `e203_transition_rigidity_raccord.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E204 | `e204_three_towers_li_field.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E205 | `e205_counting_field.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E206 | `e206_prime_gap_ledger.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E207 | `e207_collective_contact_geometry.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E208 | `e208_on_regime_anchor.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E209 | `e209_regime_transport.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E210 | `e210_first_regime_change.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E213 | `e213_mixed_fibers.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| E214 | `e214_tower_transport.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E215 | `e215_window_collective.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E216 | `e216_energy_raccords.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E218 | `e218_global_tower_dominance.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E219 | `e219_prime_gap_zero_dna.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E220 | `e220_counting_channel_gap_contributions.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E221 | `e221_collective_compatibility.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E222 | `e222_frequency_extraction.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E224 | `e224_harmonic_restoring_law.py` | UNIT | UNCHANGED | mode unitaire ; stationnarité de l'énergie réduite inchangée par la constante 1/‖ρ‖² ; caractérisation (⟺ but) maintenue |
| E225 | `e225_mirror_harmonic_balance.py` | EXACT+UNIT | UNCHANGED | dénominateurs exacts déjà utilisés (terme croisé 2Re(1/(ρ₊ρ̄₋)) > 0) |
| E226 | `e226_xi_kernel_spectral_stability.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E227 | `e227_functional_equation_restoring_constraint.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E228 | `e228_zero_mode_stability.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E229 | `e229_prime_gap_harmonic_response.py` | UNIT | UNCHANGED | réponse par écart ∫t^{ρ−1} exacte ; marqueur « harmonic » seulement |
| E231 | `e231_contact_sign_closure.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E231 | `e231_e238_common.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E231 | `e231_e238_euler_product_route.py` | SANS_ZERO | UNCHANGED | aucune contribution analytique de zéro (premiers, grammaire) |
| E232 | `e232_two_gap_charge_closure.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E233 | `e233_six_beats_closure.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E234 | `e234_grammar_noncompensation.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E235 | `e235_two_gap_determinant.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E236 | `e236_raccord_additive_rigidity.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E237 | `e237_first_off_minimal_compensation.py` | EXACT | UNCHANGED | contribution x^ρ/ρ (ou phase arctan(T/β)) conservée |
| E238 | `e238_exact_counting_closure.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E239 | `e239_first_zero_causality/e239_first_zero_causality.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| E240 | `e240_harmonic_current/e240_harmonic_current.py` | EXACT+UNIT | CORRECTED | rapport des courants recalculé au signal exact (E242 C4′) : seule une constante (T_l‖ρ_e‖²)/(T_e‖ρ_l‖²) apparaît ; tests B–E inchangés, E reste CIRCULAR |
| E241 | `e241_tower_coupling/e241_tower_coupling.py` | UNIT | CORRECTED | « partie croisée miroir 2T pour toute d » propre au mode unitaire ; signal exact : < double ON dès d ≠ 0 (exact_mirror_cross_lt_double), détecteur d²; couplage : toujours aucun |
| — | `full_cell_reading_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| — | `gap_comparison_theorem_vs_pivot_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| — | `global_zero_sum_correspondence_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| — | `inverted_second_tower_reach_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| — | `k_reading_characterization_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| — | `own_cell_contact_check.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| — | `own_cell_contact_check_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| — | `proper_state_fidelity_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| — | `reached_audit_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
| — | `vonmangoldt_chebyshev_rank_identity_published.py` | ZERO_SANS_TERME | UNCHANGED | zéros lus par hauteur, comptage, contacts de ligne ou grammaire ; aucun mode unitaire |
