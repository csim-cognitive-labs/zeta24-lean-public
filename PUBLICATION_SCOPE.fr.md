> Version française conservée à titre de référence. Main language: English, see PUBLICATION_SCOPE.md.

# Périmètre de publication

Export public daté du 15/11/2026, à historique neuf, du dépôt de recherche privé `zeta24-lean`. Ce document décrit la **sélection** : c'est un périmètre de publication, pas une dissimulation. Les expériences E400 à E477, nécessaires à l'évaluation des affirmations du `README.md` et des maîtres, sont incluses. Les anciennes campagnes RHV2 à RHV5 et les expériences antérieures à E400 restent dans le dépôt de recherche privé et peuvent être fournies sur demande à l'auteur.

Seuls des fichiers suivis par git dans le dépôt privé ont été copiés (`git ls-files`), sans lien, en préservant les fichiers. Aucun historique n'est repris.

## Inclus

- `formalization/RHV6Fresh/` : bibliothèque `RHV6Fresh/` (dont `Zeta23Port` et `PNTPort` avec leurs `LICENSE`, `NOTICE`, `PROVENANCE.md` intacts), `RHV6Fresh.lean`, `RHV6FreshCertificates.lean`, `lakefile.toml`, `lean-toolchain`, `scripts/`, `audits_compilation/`, les trois maîtres `RHV6final_STRATEGIE_*.md` (et les anciens `RHV6_STRATEGIE_*.md`), `HANDOVER_20261107_LIGNE.md`, les `AUDIT_*.md` et autres documents de ce dossier, `README.md`.
- `formalization/RHV6Fresh/experiments/` : les 70 sous-dossiers `E4NN_*` (E400 à E477) ; `audit_semantique/` sauf son sous-dossier `data/` ; `data/odlyzko_zeros6_2001052.txt` (36 018 936 octets, nécessaire aux jumeaux) et les fichiers de `data/` de moins de 1 Mo.
- `formalization/rhv3_lean/` : tout (sauf `.lake/`).
- Racine : `README.md` (adapté), `COPYRIGHT.md`, `LICENSE`, `THIRD_PARTY_NOTICES.md`, `CONTRIBUTING.md`, `CITATION.cff`, `SECURITY.md`, `PUBLICATION_SCOPE.md`, `PUBLICATION_EXCLUSIONS.tsv`, `.gitignore`, `docs/ANNONCE_PUBLICATION_20261115.md`.

## Modifications faites à l'export

- `formalization/rhv3_lean/lakefile.toml` : la dépendance Mathlib par chemin (`../rhv2_fresh/.lake/packages/mathlib`, non reproductible hors du dépôt privé) est remplacée par une dépendance git épinglée, révision `51e6992efd06126df61a496bebf8f49482a4e129` (celle du manifeste de `rhv2_fresh`).
- `lake-manifest.json` de `rhv3_lean` et de `RHV6Fresh` : non repris, régénérés par `lake update`.
- Racine : `README.md` adapté (bandeau, références à `CLAUDE.md` remplacées par `CONTRIBUTING.md` et les maîtres, plan du dépôt, reproduction), `CONTRIBUTING.md`, `COPYRIGHT.md` et `docs/ANNONCE_PUBLICATION_20261115.md` (URL du dépôt public).
- Aucun fichier d'expérience, de maître ou d'audit n'a été réécrit. Les chemins absolus du dépôt privé (`/opt/zeta24-lean/...`) subsistent dans quelques documents d'archive, listés ci-dessous.

## Exclu

Exclusions de dossiers : `CLAUDE.md` (journal interne de travail), `research/`, `archive/`, `validation/`, `src/`, `scripts/` racine, `tests/`, `.github/` (aucun workflow dans le public), `docs/` sauf l'annonce, `formalization/rhv2_fresh`, `rhv4_lean`, `RHV5Fresh`, `rh_gap_criterion`, `rhv5_lean`, fichiers racine Python et protocoles hors Lean, tout fichier `.log`, tout `.lake/`, tout `venv/`.

Exclusions dans `formalization/RHV6Fresh/` et `formalization/rhv3_lean/` (fichiers suivis non copiés) : 2262 fichiers, 452 Mo au total. Détail fichier par fichier (chemin, taille, motif) : `PUBLICATION_EXCLUSIONS.tsv`. Agrégat par dossier :

| Dossier | Fichiers | Taille (Mo) | Motif |
|---|---:|---:|---|
| `experiments/E264_E300_LocalSynchronization` | 118 | 98.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e358_results.json` | 1 | 46.7 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/project_audit` | 31 | 22.7 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E2M_reproduction_20261027` | 3 | 18.5 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e219_prime_gap_zero_dna` | 15 | 17.8 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E303_THREE_ON_COLLECTIVE_BEATS` | 46 | 17.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E302_THREE_ON_TRUE_3D_SYNCHRONIZATION` | 53 | 16.7 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/data` | 5 | 14.7 | data/ >= 1 Mo |
| `experiments/audit_semantique` | 38 | 14.5 | audit_semantique/data/ exclu (extractions RHV2-RHV5) |
| `experiments/e207_collective_contact_geometry` | 19 | 12.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E308_PrimeOnlyRadialRigidity` | 19 | 9.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/constraint_correlation_20261026` | 41 | 9.5 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e220_counting_channel_gap_contributions` | 9 | 9.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e358_positions.dat` | 1 | 8.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E377_TimesFM_CertificateCampaign` | 14 | 6.9 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/INVENTAIRE_REVISION_20261028` | 43 | 5.8 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E345_E346_STABLE_TOWERS_REBUILD` | 40 | 4.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e360_results.json` | 1 | 3.5 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E331_TenZeroResultant` | 21 | 3.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e197_window_comparison` | 11 | 2.9 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e243_gap_synchronization` | 27 | 2.9 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E342_PrimeInversionThreeZeros` | 77 | 2.9 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e202_cell_passage_restitution` | 18 | 2.9 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E334_InversePrimeSpectralReconstruction` | 38 | 2.8 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E345_HarmonicCollaborationFiveZeros` | 18 | 2.8 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/authentic_transport_causality` | 20 | 2.7 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e355_results.json` | 1 | 2.7 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E336_LocalGlobalGapMatrix` | 46 | 2.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/grammar_channel_global_build.log` | 1 | 2.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e198_transmissions_300` | 13 | 2.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e199_increment_matrix_fibers` | 16 | 2.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e208_on_regime_anchor` | 13 | 2.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E347_OFF_NewHeight_E345_E346` | 19 | 2.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E341_GrammarWindowQualification` | 45 | 2.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e180_zero_contributions_plate_full.png` | 1 | 2.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e242_exact_signal_audit` | 22 | 2.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E328_ThreeZerosAroundLi` | 9 | 1.9 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e180_zero_contributions_plate_zoom15.png` | 1 | 1.8 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E301_AuditContradictoire` | 22 | 1.7 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E346_BilateralHarmonicRaccord` | 18 | 1.7 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e163b_three_zeros_on_off_towers_corrige.png` | 1 | 1.5 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e163b_three_zeros_on_off_towers.png` | 1 | 1.5 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e201_first_zero_contact_comparison` | 7 | 1.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E330_ThreeZeroResultant` | 10 | 1.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E335_FirstZeroArithmeticAnchor` | 42 | 1.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e209_regime_transport` | 10 | 1.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E333_CountingFieldArchitecture` | 20 | 1.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E332_SuccessiveSumsSameGaps` | 8 | 1.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E378_TimesFM_LargeBases` | 12 | 1.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e244_amplitude_stable_sync` | 16 | 1.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e206_prime_gap_ledger` | 8 | 1.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e218_global_tower_dominance` | 10 | 1.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e203_transition_rigidity_raccord` | 11 | 1.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E350_GrammarSpectralStability` | 26 | 1.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E327_PrimeQuantitativeGrammar` | 9 | 1.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E379_TimesFM_Cascade` | 33 | 1.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E310_PrimeMusicAmplitudeStability` | 8 | 0.9 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e205_counting_field` | 10 | 0.9 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E329_PrimeGapWindowsThreeZeros` | 12 | 0.9 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e204_three_towers_li_field` | 5 | 0.9 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e215_window_collective` | 6 | 0.8 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E349_TwoMeetingInversion5000Gaps` | 16 | 0.8 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E343_GapInverseCountingPlane` | 21 | 0.8 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E322_CountingReconstructionAroundLi` | 8 | 0.8 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E420_ContactRealValues` | 4 | 0.7 | fichier .log |
| `experiments/e233_six_beats_closure` | 7 | 0.7 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e163_on_off_tower_geometry.png` | 1 | 0.7 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e190_fig1_geometrie_bande.png` | 1 | 0.7 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e222_frequency_extraction` | 7 | 0.7 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e088d_two_consecutive_on_towers_axes.png` | 1 | 0.7 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e101_fig1_overlay_same_T_three_beta.png` | 1 | 0.7 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e232_two_gap_charge_closure` | 6 | 0.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e214_tower_transport` | 8 | 0.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e094_off_zero_insertion_prime_shift.png` | 1 | 0.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e088c_two_consecutive_on_towers.png` | 1 | 0.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e095_forced_mirror_pair_insertion.png` | 1 | 0.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E-XXX-TimeFMPatternMatching` | 8 | 0.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e093_multi_tower_progression.png` | 1 | 0.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e210_first_regime_change` | 9 | 0.6 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e238_exact_counting_closure` | 7 | 0.5 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E321_GeneratedFrequencyMeetingPoints` | 10 | 0.5 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E352_ProjectionOnKnownZeros` | 10 | 0.5 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e241_tower_coupling` | 11 | 0.5 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E323_SynchronizationMatrix` | 8 | 0.5 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e221_collective_compatibility` | 9 | 0.5 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e184_first_removal_collective_mechanics.png` | 1 | 0.5 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e361_results.json` | 1 | 0.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e229_prime_gap_harmonic_response` | 5 | 0.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e213_mixed_fibers` | 8 | 0.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E311_SuccessiveModeExtraction` | 12 | 0.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e216_energy_raccords` | 6 | 0.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e239_first_zero_causality` | 9 | 0.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e364_e370_synchronized_views.png` | 1 | 0.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e359_results.json` | 1 | 0.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E309_PerGapSynchronizationDistinctHeights` | 7 | 0.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/riemann_graphique.png` | 1 | 0.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e231_contact_sign_closure` | 6 | 0.4 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e088_schema3_collage_control.png` | 1 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/root_cause_validation` | 11 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e106_fig1_no_shared_trajectory_stop.png` | 1 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E325_JointGapTriple` | 11 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e115_figB_tower_log_view.png` | 1 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E313_ConstantAmplitudeNeed` | 5 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e224_harmonic_restoring_law` | 5 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e227_functional_equation_restoring_constraint` | 5 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E324_ImposedAmplitudeNonCompensation` | 7 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e237_first_off_minimal_compensation` | 6 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e088_schema2_off_line_two_towers.png` | 1 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e200_arrival_fiber_hypotheses` | 10 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e235_two_gap_determinant` | 6 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e228_zero_mode_stability` | 5 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e356_results.json` | 1 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e183_tower_chains_joint_constraints.png` | 1 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e121_vertical_energy_transmission.png` | 1 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e117_fig1_two_towers_same_height.png` | 1 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e240_harmonic_current` | 9 | 0.3 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e181_complete_interaction_nested_supports.png` | 1 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e106_fig2_same_T_pair_lex_order.png` | 1 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e364_results.json` | 1 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e225_mirror_harmonic_balance` | 5 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e119_off_beta0.4_towers.csv` | 1 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e119_off_beta0.2_towers.csv` | 1 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e226_xi_kernel_spectral_stability` | 5 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e104_fig1_a_n_prefix_invariance_K0_vs_K10.png` | 1 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e355_window_frequencies.png` | 1 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e236_raccord_additive_rigidity` | 6 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e121_tower_data_300.csv` | 1 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e234_grammar_noncompensation` | 6 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e231_e238_euler_product_route` | 5 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `archives/ARCHIVES_MAITRES_RHV4_RHV5_20260921.md` | 1 | 0.2 | archives (ancien dossier d'archives des maîtres RHV4/RHV5, hors périmètre) |
| `experiments/E373_WeightedGrammarChannels` | 8 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e120_energetic_insertion_two_boundaries.png` | 1 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e102_fig3_nonzero_transition_alternation.png` | 1 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e118_fig1_full_stage_series_corrige.png` | 1 | 0.2 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e088_schema1_on_line_tower.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e117_fig2_amplitude_gap.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e101_fig2_RT_vs_Wn_amplitude_separation.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e118_fig1_full_stage_series.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e184_first_removal_zoom.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e119_pushforward_height_vs_radial.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e357_results.json` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/gemini_cells_luna_20261026` | 5 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E397_RencontresEtPolynomeDeFrequences` | 5 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/causal_advanced_validation` | 7 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E393_PartArriveeBasseAuxRencontres` | 4 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e117_fig3_sin_phase.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e105_fig1_family_frequency_vs_scale.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e151_fixed_k_vs_rank_k_cells.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/d1012_causal_validation` | 7 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e358_family_frequencies.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e115_figA_analytic_plane_scaled.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E396_PrixPayeParLHistorique` | 5 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e118_fig2_series_vs_q_corrige.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e118_fig2_series_vs_q.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e115_figC_normalized_axes.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e371_e376_reconstruction_audit.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e355_window_similarity.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/LUNA_GLOBAL_GRAMMAR_COMPENSATION_PLAN_20261023.md` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e101_fig3_relative_phase_contact_shift.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e356_cumulative_frequencies.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E344_GrammarOperator` | 6 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E372_ClosureAttempts_ZeroFreeBand` | 15 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e190_fig4_admissible_lectures.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e105_fig2_predictor_accuracy_small_vs_huge.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e172_second_off_zero_window.txt` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e119_on_towers.csv` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e105_fig3_huge_prime_window_strip_and_prediction.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e190_fig3_ecart_rupture.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e190_fig2_rho_canaux.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E371_ArchetypeB_Anatomy` | 7 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e102_fig1_mod6_state_strip.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e105_fig4_a_n_growth_to_huge_scale.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e360_pattern_similarity.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e102_fig2_gapclass_histogram_by_K.png` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e184_first_removal_collective_mechanics.py` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `audits_compilation/transportatsharedprime` | 4 | 0.1 | fichier .log |
| `experiments/PLAN_FABLE_THEOREME_TERMINAL_UNIQUE_20261027.md` | 1 | 0.1 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E394_DemandeDesPremiersAuxRencontres` | 4 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e136_environnement_123_verites.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e183_tower_chains_joint_constraints.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e180_zero_contributions_plate.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e103_fig1_magnitude_over_mod6_strip.png` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e103_fig2_magnitude_histogram_log.png` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e212_archaeology` | 2 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e231_e238_lean_closure_probes` | 19 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e362_results.json` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e103_fig3_mean_magnitude_by_transition.png` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e189_stage_cells_expected_next.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e368_results.json` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e202_cell_passage_restitution.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e365_results.json` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e190_finite_grammar_layer.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e177_interval_decay_and_off_window.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e207_collective_contact_geometry.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e103_fig4_running_max_magnitude_growth.png` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e184_first_removal_collective_mechanics_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/PLAN_FABLE_CLOTURE_TERMINALE_20261027.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E395_DemandeInterieureEtExactitude` | 4 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E424_E425_SuccessiveContacts` | 10 | 0.0 | fichier .log |
| `experiments/e192_zeta_box_certificate_generator.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e199_increment_matrix_fibers.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e183_tower_chains_joint_constraints_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e186_insertion_defect_vs_pair_deformation.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/PROJECT_CLOSURE_AUDIT_20261022.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e105_gap_family_prediction_and_saturation_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E398_SommetAtteint` | 4 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e176_tangential_inversion_2_3.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e178_gain_decomposition_prime_support_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e198_transmissions_300.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e173_off_surplus_audit.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e172_second_off_zero_window.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e076_explicit_formula_identification_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e181_complete_interaction_nested_supports.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E312_SignalProgressionTranslation` | 3 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/PROMPT_MAITRE_FABLE_20261027_SOURCE.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E305_FixedGapRaccords` | 6 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e188_background_cells_modulation.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E348_InequalityCandidates` | 4 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E351_GapDemandStability` | 4 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e200_arrival_fiber_hypotheses.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e171_li_refinement_and_witness_worlds.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e076_geometric_trajectories_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e186_insertion_defect_vs_pair_deformation_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/ASTRA_AUTHENTIC_TRANSPORT_CAUSAL_PLAN_20261025.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e189_stage_cells_expected_next_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E387_TroisParametresAttendus` | 3 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/PLAN_FABLE_TIMESFM_CASCADE_20261027.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/PLAN_E096_E100_verrou_hauteur_20260927.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e171_li_refinement_and_witness_worlds_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e177_interval_decay_and_off_window_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e358_scale_controls.json` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e115_inter_tower_coupling_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e372_results.json` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e204_three_towers_li_field.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e078_axis_from_zero_set_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e175_windows_12_24_36.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/ASTRA_GLOBAL_STABILITY_WORKPACKETS_20261024.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E389_RencontresObligees` | 5 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e211_on_regime_induction_probe` | 3 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e076_geometric_trajectories_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E386_ServiceEcartVoieT_VoieBeta` | 3 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e176_tangential_inversion_2_3_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e174_certified_count_and_detection.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e187_chains_windows_beats_joint.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e173_off_surplus_audit_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e103_prime_gap_magnitude_decomposition_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e191_em10_static_lemmas.lean.in` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e163b_three_zeros_on_off_towers.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e135_all_off_world_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/HISTORICAL_AUDIT_ON_REGIME_E212_20261013.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e230_terminal_closure_challenge` | 7 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e169_marginal_refinement_per_zero_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e206_prime_gap_ledger.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/PLAN_COMPILER_RESIDUAL_HORIZONTAL_EXCLUSION_20260928.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e154_quadratic_energy_tower_cells.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e203_transition_rigidity_raccord.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e174b_certified_tail_and_detection.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e170_first_tower_encapsulation.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e101_fixed_height_beta_displacement_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e077_spiral_axis_crossing_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e136_primal_event_history_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e120_energetic_insertion_two_boundaries_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e201_first_zero_contact_comparison.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e197_window_comparison.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e106_tower_boundary_intrinsic_vs_injected_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e175_windows_12_24_36_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e117_two_towers_energy_conflict_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/FOUR_TRANSITION_GLOBAL_STABILITY_PRIORITY_20261024.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/PLAN_VERTICAL_ENERGY_CLOSURE_20260928.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e137_residual_increment_off_test_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e088d_two_consecutive_on_towers_axes.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e187_chains_windows_beats_joint_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e080_canonical_origin_stop_event_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e163_on_off_tower_geometry.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/PLAN_LUNA_CELLULES_GEMINI_20261026.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e224_e230_rapport_mathematique.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e208_on_regime_anchor.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e190_finite_grammar_layer_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e137bis_diagonal_cross_split_by_exact_gap.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/ROOT_CAUSE_MASTER_MATRIX.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e102_mod6_grammar_rigidity_at_scale_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `audits_compilation/occurrenceheightcomposition` | 2 | 0.0 | fichier .log |
| `experiments/e155_diagonal_refutation_exact_axis.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e181_complete_interaction_nested_supports_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e088_tower_geometry_complex_plane_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e150_li_remainder_height_radial_slope.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e085_same_height_two_towers_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/COLLECTIVE_STABILITY_PHYSICAL_DIRECTION_AUDIT_20261023.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e121_vertical_energy_transmission_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/INVENTAIRE_REVISION_20261028.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/GRAMMAR_CHANNEL_CLOSURE_REFINEMENT_20261023.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/CONTACT_ACCUMULATION_MASTER_REPORT.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e157_grammar_words_load_and_depth.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e174_certified_count_and_detection_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e191_em10_certificate_generator.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/ASTRA_LUNA_CAUSAL_WORKPACKETS_20261023.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e182_coupling_pitch_frequency_amplitude.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E390_DefinitionRencontre` | 4 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e142_reverse_engineering_300_zeros_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e094_off_zero_insertion_prime_shift_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e179_grammar_windows_12_24_36_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e085_same_height_two_towers_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e077_spiral_axis_crossing_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e210_first_regime_change.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e219_prime_gap_zero_dna.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e169_marginal_refinement_per_zero.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e137_residual_increment_off_test_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e082_two_data_min_vs_target_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/PLAN_TDD_DEUX_HORLOGES_20260928.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e170_first_tower_encapsulation_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e076_explicit_formula_identification_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e180_zero_contributions_plate_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e147_pointed_primes_on300_vs_off150.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e205_counting_field.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e095_forced_mirror_pair_insertion_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e208_e211_rapport_mathematique.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e084_reversed_second_tower_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/ASTRA_LUNA_CAUSAL_EXECUTION_RESULTS.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e367_results.json` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e209_regime_transport.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e081_next_expected_pivot_stop_factor_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e118_full_stage_energy_series_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/PLAN_TDD_PROGRESSION_CONTINUE_20260928.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e153_landau_audit_real_channel_li.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e220_counting_channel_gap_contributions.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e078_axis_from_zero_set_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e224_e230_compiler_diagnostic.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/k_reading_characterization_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e086_four_zeros_all_situations_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e080_canonical_origin_stop_event_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e123_vertical_force_hypotheses_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/FABLE_CAUSAL_PHASE_AUDIT_AND_SONNET_PLAN_20261024.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e135_all_off_world_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e088c_two_consecutive_on_towers.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/LUNA_CAUSAL_DISCOVERY_PROTOCOL_20261023.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e127_radial_budget_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/PLAN_TDD_TRANSLATION_PROGRESSION_20260928.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E391_SommeExacteAuxRencontres` | 4 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/GRAMMAR_CONTACT_STABILITY_REPORT.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e218_e223_rapport_mathematique.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e218_global_tower_dominance.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e231_e238_rapport_mathematique.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e374_results.json` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e127_radial_budget_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/FABLE_REPRISE_INTEGRALE_DIRECTIVE_20261027.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e114_inter_tower_repulsion_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e119_family_pushforward_height_vs_radial_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/c_lecture_rank_audit_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e086_four_zeros_all_situations_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e158_regime_window_packet.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/CONSECUTIVITY_WEIGHT_VARIATION_REFINEMENT_20261024.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e151_fixed_k_vs_rank_k_cells.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e239_e241_rapport_mathematique.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e223_global_gap_invariant` | 3 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e188_background_cells_modulation_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/ASTRA_D1012_BUILD_CAUSAL_CHALLENGE_20261025.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e146_entry_position_arrow_hypotheses.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e221_collective_compatibility.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e356_cumulative_grammar.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/c_lecture_rank_audit_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/vonmangoldt_chebyshev_rank_identity_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e163_mirror_antisymmetric_channel.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e217_missing_property_probes` | 3 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e178_gain_decomposition_prime_support.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e151_fixed_k_vs_rank_k_cells_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `audits_compilation/frequencycap` | 2 | 0.0 | fichier .log |
| `experiments/e083_predecessor_pointed_prime_chain_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e355_fixed_5000_windows.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e104_zero_sequence_magnitude_invariance_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e105_gap_family_prediction_and_saturation_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e154_quadratic_energy_tower_cells_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e233_six_beats_closure.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e147_pointed_primes_on300_vs_off150_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/PLAN_TDD_INTER_TOWER_EXCESS_20260928.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e112_phase_quantum_per_event_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e155_diagonal_refutation_exact_axis_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e157_grammar_words_load_and_depth_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e081_next_expected_pivot_stop_factor_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/PROMPT_LUNA_CLOTURE_CONJOINTE_20261026.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E422_CollectiveRealValueAtContacts` | 2 | 0.0 | fichier .log |
| `experiments/e214_tower_transport.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e182_coupling_pitch_frequency_amplitude_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/inverted_second_tower_reach_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E399_DetourPrimeContent` | 5 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e136_primal_event_history_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e215_window_collective.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e213_mixed_fibers.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/FABLE_DIRECTION_ON_STABILITY_PLAN_SONNET_20261025.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e123_vertical_force_hypotheses_published_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/PLAN_TDD_MIROIR_FREQUENCE_20260928.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/LUNA_ON_RIGIDITY_AUDIT_20261023.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/GRAMMAR_STABILITY_ADVANCED_CAUSAL_AUDIT_20261024.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `audits_compilation/threezerowindow` | 2 | 0.0 | fichier .log |
| `experiments/e137bis_diagonal_cross_split_by_exact_gap_output.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e093_multi_tower_progression_published.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/LUNA_FOUR_TRANSITION_GLOBAL_STABILITY_EXECUTION_20261024.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e226_xi_kernel_spectral_stability.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/LUNA_ADVANCED_CAUSAL_EXECUTION_20261024.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/e231_contact_sign_closure.py` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `experiments/E371_E376_ZERO_MATCHING_TABLE.md` | 1 | 0.0 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |

## Exclusions par taille

Tout fichier de plus de 5 Mo est exclu (sauf le fichier d'Odlyzko). Les fichiers de 1 Mo et plus exclus, un par un :

| Chemin | Octets | Motif |
|---|---:|---|
| `formalization/RHV6Fresh/experiments/e358_results.json` | 46716971 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/E264_E300_LocalSynchronization/E267_conjoint/e267bis_partial_contributions.csv.gz` | 26868485 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/E264_E300_LocalSynchronization/data/e264_matrix.npz` | 23733960 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/E264_E300_LocalSynchronization/E264_matrice/e264_cells.csv.gz` | 16387676 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/E2M_reproduction_20261027/all_zero_pair_paths.npz` | 12416755 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/E308_PrimeOnlyRadialRigidity/e308_prime_events.csv` | 8974828 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/data/e190_channels.csv` | 8426818 | data/ >= 1 Mo |
| `formalization/RHV6Fresh/experiments/e358_positions.dat` | 8196683 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/audit_semantique/data/rh_gap_criterion.jsonl` | 7437937 | audit_semantique/data/ exclu (extractions RHV2-RHV5) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/e207_collective_contact_geometry/e207_figF_identifiabilite.svg` | 6740458 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/project_audit/kernel_axioms_0.log` | 6491012 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/e219_prime_gap_zero_dna/e219_fig_ecarts_zero1.svg` | 6329109 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/project_audit/theorem_axioms.tsv` | 6192204 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/E2M_reproduction_20261027/nonempty_paths.csv` | 6080245 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/e220_counting_channel_gap_contributions/e220_fig_attribution.svg` | 5644286 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/e219_prime_gap_zero_dna/e219_valeurs_signees_zeros_1_3.csv` | 5248906 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/e219_prime_gap_zero_dna/e219_matrice_on_300x_ecarts_2e4.npz` | 5066426 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) ; > 5 Mo |
| `formalization/RHV6Fresh/experiments/E302_THREE_ON_TRUE_3D_SYNCHRONIZATION/figures/plotly.min.js` | 4815814 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E303_THREE_ON_COLLECTIVE_BEATS/figures/plotly.min.js` | 4815814 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E377_TimesFM_CertificateCampaign/series/u_series.npz` | 4607572 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E264_E300_LocalSynchronization/E267_conjoint/e267bis_density_sign_changes.csv.gz` | 4233799 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/project_audit/source_inventory.json` | 3537430 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/e360_results.json` | 3527040 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E264_E300_LocalSynchronization/figures/E264_C_cartes_thermiques.svg` | 3468898 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/project_audit/all_modules_build.log` | 3330504 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E264_E300_LocalSynchronization/figures/E264_C_cartes_thermiques.png` | 2714601 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/e355_results.json` | 2698942 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/authentic_transport_causality/logs/reduction_audit_build.log` | 2648739 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/grammar_channel_global_build.log` | 2625563 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/project_audit/global_build.log` | 2625563 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E264_E300_LocalSynchronization/E265_reconstruction/e265_errors_per_gap.csv` | 2490929 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/e220_counting_channel_gap_contributions/e220_contributions_par_ecart.csv` | 2454375 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/data/e177_windows.csv` | 2370593 | data/ >= 1 Mo |
| `formalization/RHV6Fresh/experiments/E303_THREE_ON_COLLECTIVE_BEATS/prime_gaps_vs_events.csv` | 2361862 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E303_THREE_ON_COLLECTIVE_BEATS/figures/fig1_paires_conjuguees_et_superposition.html` | 2299271 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E303_THREE_ON_COLLECTIVE_BEATS/figures/fig2_interferences_deux_echelles.html` | 2297440 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/constraint_correlation_20261026/kernel_edges_1.jsonl.gz` | 2187382 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/e180_zero_contributions_plate_full.png` | 2133871 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/constraint_correlation_20261026/theorems.jsonl.gz` | 2046864 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/audit_semantique/data/rhv3_lean.jsonl` | 1924556 | audit_semantique/data/ exclu (extractions RHV2-RHV5) |
| `formalization/RHV6Fresh/experiments/constraint_correlation_20261026/round_1.jsonl.gz` | 1857666 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/e197_window_comparison/e197_points_36.csv` | 1792428 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/e180_zero_contributions_plate_zoom15.png` | 1781949 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/constraint_correlation_20261026/edges.tsv.gz` | 1769835 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E302_THREE_ON_TRUE_3D_SYNCHRONIZATION/figures/fig6_reconstruction.html` | 1755237 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/audit_semantique/data/rhv2_fresh.jsonl` | 1523392 | audit_semantique/data/ exclu (extractions RHV2-RHV5) |
| `formalization/RHV6Fresh/experiments/e207_collective_contact_geometry/e207_figB_contacts_individuels.svg` | 1521445 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/e199_increment_matrix_fibers/e199_matrice_increments.csv` | 1507745 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/data/e177_off_window_configurations.csv` | 1475444 | data/ >= 1 Mo |
| `formalization/RHV6Fresh/experiments/e163b_three_zeros_on_off_towers_corrige.png` | 1468812 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/e163b_three_zeros_on_off_towers.png` | 1456001 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E264_E300_LocalSynchronization/E271_E288_campagne/e274bis_dC_dbeta_300x1000.csv.gz` | 1454161 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E264_E300_LocalSynchronization/figures_E268_E288/E268_fig_croissance.svg` | 1421197 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E377_TimesFM_CertificateCampaign/e377_timesfm_results.json` | 1416948 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/data/e177_cells_5000.csv` | 1386606 | data/ >= 1 Mo |
| `formalization/RHV6Fresh/experiments/E302_THREE_ON_TRUE_3D_SYNCHRONIZATION/figures/fig1_trois_tours.html` | 1380005 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E302_THREE_ON_TRUE_3D_SYNCHRONIZATION/figures/fig5_synchro_collective.html` | 1375089 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/e208_on_regime_anchor/e208_zgrid.npz` | 1302372 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E345_HarmonicCollaborationFiveZeros/cumulative_curves.csv` | 1274722 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/constraint_correlation_20261026/catalogue.tsv.gz` | 1103795 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/E331_TenZeroResultant/E331_six_vues.png` | 1090520 | expérience antérieure à E400 / hors sélection (reste dans le dépôt privé) |
| `formalization/RHV6Fresh/experiments/data/e177_predictor.csv` | 1030152 | data/ >= 1 Mo |
