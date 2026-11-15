# Fragment C4b — audit sémantique cumulé, projet `rh_gap_criterion`, second tiers (modules Round26B4GrammarVoiceRow … Round27EFiberedPartnershipTDD)

Base hors de la hiérarchie d'autorité RHV6 (CLAUDE.md §2), auditée selon la même méthode. Sources : `formalization/rh_gap_criterion/`. Données : `data/rh_gap_criterion.jsonl`. Lot : `lots/C4b.txt` (140 modules, 2446 théorèmes). Le préfixe `RhGap.` est omis dans les noms ; les noms sans préfixe sont ceux du champ `name` (racine de l'espace de noms). Le nombre « entraîne » est le nombre de théorèmes de TOUT `rh_gap_criterion.jsonl` dont la preuve utilise le théorème (`deps_project`), lui-même exclu.

Statuts : mécaniquement, aucun `sorryAx` et aucun axiome non standard dans ce lot (0 ligne du TSV des axiomes non standard n'est dans C4b). Le correctif de contrôle n°1 (CONSIGNES_REDACTION.md) a été appliqué après coup par script (`CONFIRMÉE SOUS CONDITION` conservée seulement pour hors ligne, re≠1/2, côté haut/bas, prémisse nommée ; les conditions numériques ou de domaine sont ramenées à `CONFIRMÉE (domaine: …)`). Comptes avant/après correctif : OK 1494→2005, COND 859→348, EQRH 37→37, IMPRH 53→53, TERME 0→0, REF 3→3.

Deux limites de méthode déclarées : (i) les énoncés ont été rédigés par 11 relecteurs en parallèle (un par bloc de modules) à partir du TYPE ; les familles de projections de structure (`GrammarTowerZeroFidelityObject.*`, `FiberedPartnershipTDD*.*`) partagent des énoncés ; (ii) le rattachement `Vi` est prudent : `AJOUT` quand aucune vérité du maître ne correspond au sens exact.


### `Round26B4GrammarVoiceRow`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `grammarWeight_eq_family_signed` (l.52) | Dès que 2 ≤ n+k, le poids grammatical vaut l'indicatrice « gnat(n+k) ≡ 4 mod 6 » moins l'indicatrice « ≡ 2 mod 6 ». [terme hors maître] | CONFIRMÉE (domaine: 2 ≤ n+k) | AJOUT | 8 |
| `grammarWeight_mem_neg_one_zero_one` (l.61) | Le poids grammatical vaut toujours −1, 0 ou 1. | CONFIRMÉE | AJOUT | 5 |
| `grammarVoiceRow_zero` (l.82) | La ligne de voix grammaticale d'un zéro non trivial est nulle à longueur 0. [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `grammarVoiceRow_succ` (l.88) | La ligne à longueur K+1 est la ligne à K plus un pas de colonne. | CONFIRMÉE | AJOUT | 1 |
| `zeroPrimeStepContribution_conjugateMate` (l.102) | La contribution zéro-premier par colonne du conjugué est le conjugué complexe de celle du zéro. | CONFIRMÉE | V63 | 1 |
| `grammarVoiceStep_conjugateMate` (l.116) | Le pas de voix grammaticale du conjugué est le conjugué complexe du pas du zéro. | CONFIRMÉE | V63 | 1 |
| `grammarVoiceRow_conjugateMate` (l.125) | La ligne complète de voix du conjugué est le conjugué complexe de celle du zéro (équivariance, pas réalité). | CONFIRMÉE | V63 | 0 |
| `grammarVoiceRowFin_eq_grammarVoiceRow` (l.149) | La présentation indexée par Fin K coïncide avec la ligne sur range K. | CONFIRMÉE | AJOUT | 1 |
| `grammarVoiceRowPerm_id` (l.157) | La permutation identité restitue la ligne non permutée. | CONFIRMÉE | AJOUT | 1 |
| `perm_preserves_increment_multiset_sum` (l.164) | La somme des incréments par colonne est invariante par toute permutation des colonnes. | CONFIRMÉE | AJOUT | 0 |
| `perm_preserves_weight_multiset_sum` (l.172) | La somme des poids grammaticaux est invariante par toute permutation des colonnes. | CONFIRMÉE | AJOUT | 0 |
| `grammarVoiceRow_swap_diff` (l.183) | Pour i≠j, la différence ligne / ligne transposée vaut (écart des poids)×(écart des incréments). | CONFIRMÉE (domaine: i ≠ j) | AJOUT | 2 |
| `grammarVoiceRow_swap_ne_of_weights_and_increments_ne` (l.212) | Si poids et incréments diffèrent en i et j, la ligne n'est pas invariante par la transposition. | CONFIRMÉE (domaine: i≠j, poids distincts et incréments distincts ) | AJOUT | 0 |
| `grammarVoiceRow_swap_eq_of_weights_eq_or_increments_eq` (l.229) | Si les poids ou les incréments coïncident en i et j, la ligne est invariante par la transposition. | CONFIRMÉE (domaine: poids égaux ou incréments égaux ) | AJOUT | 0 |
| `grammarWeight_two_zero` (l.249) | Le poids grammatical en (2,0) vaut −1. | CONFIRMÉE | AJOUT | 1 |
| `grammarWeight_two_one` (l.255) | Le poids grammatical en (2,1) vaut 1. | CONFIRMÉE | AJOUT | 1 |
| `grammarWeight_not_constant` (l.261) | Le poids grammatical n'est pas constant : il existe n,i,j avec poids distincts. | CONFIRMÉE | AJOUT | 0 |
| `grammarVoiceRow_summation_by_parts` (l.270) | La ligne de voix s'écrit par sommation par parties : poids terminal × contribution de bloc moins somme des sauts de poids × contributions de bloc. | CONFIRMÉE | AJOUT | 1 |
| `grammarVoiceRow_boundary_only_of_constant_weight` (l.289) | Si le poids est constant c sur les colonnes k<K, la ligne vaut c × contribution de bloc (pure différence de bord). | CONFIRMÉE (domaine: poids constant sur les colonnes ) | AJOUT | 0 |

### `Round26B4GrammaticalInsensitivityClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `zero_reconstructed_grammatical_property_iff` (l.54) | Pour tout constructeur déterministe F et toute propriété P, P vaut de l'objet bâti sur les suites reconstruites depuis les zéros ssi elle vaut de l'objet bâti sur les premiers canoniques. [terme hors maître] | CONFIRMÉE | V48,V159,V174 | 2 |
| `zero_reconstructed_count_grammatical_property_iff` (l.65) | Idem avec le comptage reconstruit en plus (constructeur à trois suites). | CONFIRMÉE | V48,V159 | 0 |
| `grammatical_defect_route_equivalent_to_absence` (l.85) | Si la loi première interdit le défaut D, « tout membre Off entraîne D sur l'objet reconstruit » équivaut à « aucun membre Off ». | CONFIRMÉE (domaine: la loi première exclut D (¬D(F p gnat)) ) | AJOUT | 0 |
| `offline_grammatical_defect_is_exactly_rh` (l.105) | Si la loi première interdit D, « tout zéro de re≠1/2 donne D sur l'objet reconstruit » équivaut à « tout zéro non trivial a re=1/2 ». | ÉQUIVALENTE À RH | V126,O10 | 2 |
| `derived_object_invariant_under_any_zero_hypothesis` (l.132) | Sous toute hypothèse H sur un zéro, l'objet dérivé reconstruit égale l'objet dérivé premier. | CONFIRMÉE | V159,V174 | 0 |
| `zeroReconstructed_blockEntryState_eq` (l.161) | L'état d'entrée de bloc reconstruit depuis les zéros égale l'état d'entrée de bloc premier. | CONFIRMÉE | V48,V174 | 1 |
| `zeroReconstructed_blockExitState_eq` (l.166) | L'état de sortie de bloc reconstruit égale l'état de sortie premier. | CONFIRMÉE | V48,V174 | 1 |
| `zeroReconstructed_changeCount_eq` (l.171) | Le nombre de changements d'état reconstruit égale celui du côté premier. | CONFIRMÉE | V48,V174 | 1 |
| `zeroReconstructed_block_change_imbalance_boundary` (l.182) | Côté reconstruit, (changements de classe 4) − (changements de classe 2) = poids d'état de sortie − poids d'état d'entrée. | CONFIRMÉE (domaine: 2 ≤ n) | V48,V174 | 0 |
| `zeroReconstructed_change_skeleton_alternates` (l.194) | Côté reconstruit, deux écarts non nuls mod 6 consécutifs sont l'un 2 l'autre 4 (alternance du squelette). | CONFIRMÉE | V174,V177 | 0 |
| `zeroReconstructed_blocks_join_eq` (l.206) | Le bloc reconstruit de longueur k1+k2 se restreint à ses deux moitiés (positions, écarts, relations). | CONFIRMÉE | V48 | 0 |
| `zeroReconstructed_order_strict_and_prime` (l.228) | Les blocs reconstruits ont positions premières, strictement croissantes, et zerosPrimePosition est strictement monotone. | CONFIRMÉE | V48,V49 | 0 |
| `zeroReconstructed_family_succession_eq` (l.243) | Classificateurs de familles et ordres construits sur l'histoire reconstruite égalent ceux du côté premier ; chaque écart n≥1 a une unique classe dans {0,2,4}. | CONFIRMÉE (domaine: 1 ≤ n) | V48,V174 | 0 |
| `no_grammatical_property_separates_reflected_pair` (l.266) | Pour re≠1/2, aucune propriété d'un objet dérivé reconstruit ne sépare les deux membres de la paire réfléchie. | CONFIRMÉE SOUS CONDITION (zéro hors ligne (re≠1/2)) | V159,V162 | 0 |
| `offline_difference_stays_outside_the_grammar` (l.285) | Pour un zéro hors ligne (0<re<1, re≠1/2) : le réfléchi-conjugué est distinct, une entrée de constellation diffère, mais l'objet reconstruit égale l'objet premier. | CONFIRMÉE SOUS CONDITION (0<re<1 et re≠1/2) | V159,V162,V163 | 0 |
| `lock_two_grammatical_route_closed_negatively` (l.329) | Si la loi première interdit D, l'objet reconstruit égale l'objet premier ET « tout Off donne D » équivaut à « tout zéro a re=1/2 ». | ÉQUIVALENTE À RH | V126,V159 | 0 |

### `Round26B4HeightDeterminedPlacementConstraint`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `reflectConjZero_heightDetermined_eq` (l.70) | Une application déterminée par la hauteur est invariante par la réflexion-conjugaison. [terme hors maître] | CONFIRMÉE | V162 | 1 |
| `not_injOn_of_heightDetermined_of_off_critical_line` (l.78) | Une application déterminée par la hauteur n'est pas injective sur les représentants positifs de hauteur T s'il y en a un hors ligne. | CONFIRMÉE SOUS CONDITION (un représentant de hauteur T hors ligne) | V162 | 0 |
| `not_injOn_heightConstellation_of_heightDetermined_of_off_critical_line` (l.94) | Idem sur la constellation de hauteur T. | CONFIRMÉE SOUS CONDITION (un membre hors ligne dans la constellation) | V162 | 2 |
| `injOn_placement_separates_reflected_pair` (l.109) | Un placement injectif sur la constellation de hauteur T sépare tout membre hors ligne de son réfléchi-conjugué. | CONFIRMÉE SOUS CONDITION (injectif sur la constellation, membre hors ligne) | V162 | 0 |
| `not_heightDetermined_of_injOn_of_off_critical_line` (l.124) | Un placement injectif sur une constellation à membre hors ligne n'est pas déterminé par la hauteur seule. | CONFIRMÉE SOUS CONDITION (injectivité et membre hors ligne) | V162 | 1 |

### `Round26B4InnovationEnergy`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `phiOf_mem_zero_one` (l.80) | phiOf n est dans [0,1]. [terme hors maître] | CONFIRMÉE | AJOUT | 4 |
| `aT_eq_innovationJ_add_coboundary` (l.90) | aT n = innovationJ n + (phiOf(n+1) − phiOf n). [terme hors maître] | CONFIRMÉE | AJOUT | 7 |
| `innovationJ_eq_explicit_form` (l.94) | Pour n≥2, innovationJ n = 6k + 3·terme croisé − log p_n pour une transformation τ réalisée. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 1 |
| `normalizedInnovationWindowEnergy_nonneg` (l.120) | L'énergie normalisée d'innovation sur fenêtre est positive ou nulle. | CONFIRMÉE (domaine: 1 ≤ r) | AJOUT | 0 |
| `normalizedCoboundaryWindowEnergy_nonneg` (l.128) | L'énergie normalisée de cobord sur fenêtre est positive ou nulle. | CONFIRMÉE (domaine: 1 ≤ r) | AJOUT | 0 |
| `normalizedCoboundaryWindowEnergy_subexponential` (l.136) | L'énergie de cobord sur fenêtre est sous-exponentielle sans condition. [terme hors maître] | CONFIRMÉE (domaine: 1 ≤ r) | AJOUT | 1 |
| `normalizedATWindowEnergy_le_innovation_energy` (l.181) | L'énergie aT est majorée par 2×innovation + 2×cobord. | CONFIRMÉE (domaine: 1 ≤ r) | AJOUT | 1 |
| `normalizedInnovationWindowEnergy_le_AT` (l.227) | L'énergie d'innovation est majorée par 2×aT + 2×cobord. | CONFIRMÉE (domaine: 1 ≤ r) | AJOUT | 1 |

### `Round26B4InnovationTerminalPremise`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `normalizedCoboundaryWindowEnergy_subexponential_shift` (l.60) | Le cobord reste sous-exponentiel après translation de fenêtre par s≥0. | CONFIRMÉE (domaine: 1≤r, 0≤s) | AJOUT | 2 |
| `normalizedATWindowEnergy_subexponential_of_innovation` (l.79) | Si l'énergie d'innovation est sous-exponentielle (translatée), celle de aT l'est aussi. | CONFIRMÉE SOUS CONDITION (innovation sous-exponentielle) | AJOUT | 1 |
| `normalizedInnovationWindowEnergy_subexponential_of_AT` (l.107) | Réciproque : aT sous-exponentielle entraîne innovation sous-exponentielle. | CONFIRMÉE (domaine: aT sous-exponentielle ) | AJOUT | 0 |
| `riemann_hypothesis_from_R_and_innovation_window_subexponential` (l.130) | Si les énergies R et d'innovation (fenêtre translatée log 2) sont sous-exponentielles, alors RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | AJOUT | 1 |
| `riemann_hypothesis_from_R_and_zero_reconstructed_innovation_window_subexponential` (l.148) | Même conclusion avec l'innovation construite depuis les suites reconstruites des zéros. | IMPLIQUE RH SOUS PRÉMISSE | AJOUT | 0 |

### `Round26B4LosslessRigiditySpine`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `offline_reflected_pair_scale_characters_differ` (l.64) | Pour re≠1/2, les deux membres de la paire réfléchie ont des caractères d'échelle distincts. [terme hors maître] | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V162,V167 | 1 |
| `offline_reflected_pair_orderKeys_differ` (l.77) | Pour re≠1/2, la clé d'ordre (Im,Re) sépare les deux membres de la paire. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V62,V65,V74 | 1 |
| `lossless_offline_rigidity_spine` (l.83) | Pour re≠1/2, un paquet de rigidités tient simultanément : réfléchi distinct, même hauteur et multiplicité, même constellation, clés d'ordre et caractères d'échelle distincts, défaut de ligne, entrées de constellation distinctes. [type tronqué] | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V62,V65,V162,V163 | 1 |
| `naive_label_premise_is_free_in_a_column` (l.157) | Deux cases d'une même colonne du croisement constellation/premiers partagent écart, transition, bloc de motif et poids grammatical. [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `primeSideLabelledEntryUniqueness_is_row_blindness` (l.170) | La prémisse d'unicité naïve côté premier force deux zéros d'une même colonne à porter la même contribution individuelle. | CONFIRMÉE SOUS CONDITION (PrimeSideLabelledEntryUniqueness) | AJOUT | 1 |
| `primeSideLabelledEntryUniqueness_refutes_row_rigidity` (l.185) | L'unicité naïve côté premier est incompatible avec un défaut de contribution de ligne dans une colonne commune. | CONFIRMÉE SOUS CONDITION (PrimeSideLabelledEntryUniqueness) | AJOUT | 1 |
| `reflectedPairRatio_ne_zero` (l.212) | Le rapport de la paire réfléchie ne s'annule jamais en x>0. | CONFIRMÉE (domaine: 0<x) | AJOUT | 2 |
| `reflectedPairRatio_scale` (l.219) | Sous changement d'échelle lam, le rapport de la paire réfléchie se transporte avec l'exposant complet (1−conj ρ)−ρ. | CONFIRMÉE (domaine: 0<lam, 0<x) | AJOUT | 2 |
| `reflectedPairRatioScaleInvariant_forces_reflect_fixed` (l.255) | L'invariance d'échelle du rapport de la paire réfléchie force le réfléchi-conjugué à égaler ρ. | CONFIRMÉE SOUS CONDITION (ReflectedPairRatioScaleInvariant ρ (pour ce zéro)) | V161 | 1 |
| `critical_line_gives_reflectedPairRatioScaleInvariant` (l.288) | Pour re ρ = 1/2, le rapport de la paire réfléchie est invariant d'échelle. | CONFIRMÉE (domaine: zéro sur la ligne critique ) | V161,V77 | 1 |
| `reflectedPairRatioScaleInvariant_iff_critical_line` (l.300) | Pour tout zéro non trivial, l'invariance d'échelle du rapport ⟺ re ρ = 1/2. | CONFIRMÉE | V161,V162 | 1 |
| `all_reflectedPairRatioScaleInvariant_gives_critical_line` (l.317) | Si tout zéro non trivial a un rapport invariant d'échelle, tout zéro non trivial a re=1/2. | IMPLIQUE RH SOUS PRÉMISSE | V126,O5 | 0 |

### `Round26B4OfflineOrbitMechanismAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `offline_above_scale_factor_gt_one` (l.41) | Si β>1/2 alors 4^(β−1/2) > 1. | CONFIRMÉE SOUS CONDITION (β>1/2) | AJOUT | 0 |
| `offline_below_scale_factor_lt_one` (l.49) | Si β<1/2 alors 4^(β−1/2) < 1. | CONFIRMÉE SOUS CONDITION (β<1/2) | AJOUT | 0 |
| `on_line_scale_factor_eq_one` (l.57) | Si β=1/2 alors 4^(β−1/2) = 1. | CONFIRMÉE (domaine: β=1/2 ) | AJOUT | 0 |
| `reflect_conj_im_eq` (l.64) | La réflexion z ↦ 1−conj z préserve la partie imaginaire. | CONFIRMÉE | V65,V35 | 2 |
| `reflect_conj_re_eq` (l.69) | La réflexion z ↦ 1−conj z envoie la partie réelle sur 1−re. | CONFIRMÉE | V65,V35 | 3 |
| `reflect_conj_ne_self_of_re_ne_half` (l.73) | Si re z ≠ 1/2, le point réfléchi 1−conj z est distinct de z (même hauteur). | CONFIRMÉE (domaine: re z ≠ 1/2 ) | V62,V65,V74 | 1 |
| `reflect_conj_eq_self_of_re_eq_half` (l.86) | Si re z = 1/2, la réflexion fixe z. | CONFIRMÉE (domaine: re z = 1/2 ) | V77,V161 | 1 |
| `reflect_conj_eq_self_iff` (l.94) | La réflexion 1−conj z fixe z ssi re z = 1/2. | CONFIRMÉE | V161,V77 | 2 |

### `Round26B4OfflineRemainderAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `offlineZeroChannelTail.congr_simp` (l.None) | Lemme de congruence auto-généré : offlineZeroChannelTail est compatible avec l'égalité de ρ et de U. [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `offlineZeroAmplitude_conj_ne_zero` (l.71) | Pour un zéro non trivial de re>1/2, l'amplitude hors ligne du conjugué est non nulle. | CONFIRMÉE (domaine: 1/2 < re ρ ) | V102 | 1 |
| `zeroChannelRemainder_eq_conjMode_add_tail` (l.99) | Le reste du canal du zéro ρ égale le mode du conjugué (avec amplitude hors ligne) plus la queue hors ligne. | CONFIRMÉE (domaine: Im ρ ≠ 0, U>0) | AJOUT | 1 |
| `tail_norm_lower_bound_of_windowRemainderNonCancellation` (l.112) | Sous non-annulation de fenêtre du reste de ρ (re>1/2), la norme de la queue est minorée par amplitude·e^{(re−1/2)U} moins un terme de taux plus faible. | CONFIRMÉE SOUS CONDITION (re>1/2 et WindowRemainderNonCancellation (prémisse dite RH-forte dans la docstring)) | V102 | 1 |
| `_private.RhGapCriterion.Round26B4OfflineRemainderAudit.0.RhGap.exp_neg_le_half_of_ge_inv` (l.154) | Pour ε>0 et U ≥ 1/ε, exp(−εU) ≤ 1/2. | CONFIRMÉE (domaine: 0<ε, 1/ε ≤ U) | AJOUT | 1 |
| `tail_not_windowRemainderNonCancellation_of_windowRemainderNonCancellation` (l.170) | Sous non-annulation de fenêtre du reste de ρ (re>1/2), la queue plus profonde ne vérifie pas la non-annulation au même taux. | CONFIRMÉE SOUS CONDITION (re>1/2 et WindowRemainderNonCancellation du reste) | AJOUT | 0 |

### `Round26B4OrbitInternalDefect`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `offline_orbit_internal_defect` (l.64) | Pour re≠1/2, il existe une transition première j où la contribution zéro-premier de ρ diffère de celle de son réfléchi-conjugué. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V162,V167 | 3 |
| `criticalLine_orbit_no_internal_defect` (l.81) | Pour re=1/2, les contributions de ρ et de son réfléchi-conjugué coïncident à toute transition première. | CONFIRMÉE (domaine: zéro sur la ligne ) | V161,V77 | 1 |
| `orbit_internal_defect_iff_off_critical_line` (l.89) | Il existe un défaut interne d'orbite ssi re ρ ≠ 1/2. | CONFIRMÉE | V161,V162 | 0 |
| `two_member_orbit_has_internal_defect` (l.106) | Si l'orbite de réflexion de ρ a deux membres, deux membres de l'orbite ont des contributions distinctes à une transition première. | CONFIRMÉE SOUS CONDITION (orbite de cardinal 2) | V162 | 0 |
| `offline_orbit_internal_defect_symm` (l.118) | Pour re≠1/2, le défaut apparaît aussi en partant du réfléchi-conjugué (ordre inverse). | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V162 | 0 |

### `Round26B4OrderedConstellationView`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `zeroOrderKey_injective` (l.39) | La clé d'ordre (Im,Re) des zéros non triviaux est injective. | CONFIRMÉE | V8 | 3 |
| `instIsTransSubtypeComplexIsNontrivialZetaZeroZeroLe` (l.57) | L'ordre dérivé ZeroLe sur les zéros non triviaux est transitif (instance). | CONFIRMÉE | V8 | 10 |
| `instAntisymmSubtypeComplexIsNontrivialZetaZeroZeroLe` (l.60) | L'ordre ZeroLe est antisymétrique (instance). | CONFIRMÉE | V8 | 10 |
| `instTotalSubtypeComplexIsNontrivialZetaZeroZeroLe` (l.66) | L'ordre ZeroLe est total (instance). | CONFIRMÉE | V8 | 10 |
| `mem_orderedPositiveRepresentatives` (l.83) | Appartenir à la vue ordonnée de hauteur T ⟺ 0<Im ρ et \|Im ρ\|<T. | CONFIRMÉE | V7,V8 | 5 |
| `mem_orderedPositiveRepresentatives_iff_lt` (l.92) | Idem sans valeur absolue : 0<Im ρ<T. | CONFIRMÉE | V7,V8 | 0 |
| `orderedPositiveRepresentatives_pairwise_lt` (l.108) | La vue ordonnée est strictement triée par la clé d'ordre. | CONFIRMÉE | V8 | 1 |
| `orderedPositiveRepresentatives_pairwise_lt_human` (l.122) | Deux entrées voisines diffèrent : hauteur strictement plus grande, ou même hauteur et re strictement plus grande. | CONFIRMÉE | V8,V68 | 5 |
| `orderedPositiveRepresentatives_nodup` (l.137) | La vue ordonnée n'a pas de doublon. | CONFIRMÉE | V8 | 1 |
| `orderedPositiveRepresentatives_toFinset` (l.144) | La vue ordonnée contient exactement les représentants positifs. | CONFIRMÉE | V8 | 4 |
| `orderedPositiveRepresentatives_conjugate_distinct` (l.152) | Pour ρ dans la vue ordonnée, son conjugué est un membre distinct de la constellation de hauteur T. | CONFIRMÉE | V63,V64 | 0 |
| `heightConstellation_mem_ordered_or_conjugate` (l.165) | Tout zéro de la constellation est dans la vue ordonnée, ou son conjugué l'est. | CONFIRMÉE | V64 | 0 |
| `orderedPositiveRepresentatives_sum_eq` (l.192) | Sommer sur la liste ordonnée = sommer sur les représentants positifs. | CONFIRMÉE | AJOUT | 0 |
| `positiveRepresentatives_subset_heightConstellation` (l.202) | Les représentants positifs sont inclus dans la constellation de hauteur T. | CONFIRMÉE | AJOUT | 0 |
| `conjugateMate_coe` (l.218) | La valeur complexe de conjugateMate ρ est conj ρ. | CONFIRMÉE | V63 | 3 |
| `conjugateMate_involutive` (l.222) | conjugateMate est une involution. | CONFIRMÉE | V63 | 2 |
| `conjugateMate_injective` (l.230) | conjugateMate est injective. | CONFIRMÉE | V63 | 1 |
| `conjugateMate_ne_self` (l.234) | conjugateMate ρ est toujours distinct de ρ. | CONFIRMÉE | V63,V64 | 0 |
| `conjugateMate_im` (l.245) | conjugateMate renverse le signe de la hauteur. | CONFIRMÉE | V63 | 2 |
| `conjugateMate_mem_heightConstellation` (l.250) | conjugateMate préserve l'appartenance à la constellation de hauteur T. | CONFIRMÉE (domaine: appartenance à heightConstellation T) | V63,V64 | 1 |
| `heightConstellation_disjoint_pos_neg` (l.265) | Représentants positifs et négatifs de hauteur T sont disjoints. | CONFIRMÉE | AJOUT | 1 |
| `heightConstellation_eq_pos_union_neg` (l.276) | La constellation de hauteur T est la réunion des représentants positifs et négatifs. | CONFIRMÉE | V64 | 1 |
| `negativeRepresentatives_eq_image` (l.295) | Les représentants négatifs sont l'image des positifs par conjugateMate. | CONFIRMÉE | V63,V64 | 1 |
| `heightConstellation_sum_eq_pair_sum` (l.316) | Sommer f sur la constellation = sommer sur les positifs f(ρ)+f(conjugateMate ρ). | CONFIRMÉE | V64 | 1 |
| `nontrivialZeroResidueTerm_conjugateMate` (l.333) | Le terme résiduel du conjugué est le conjugué complexe du terme résiduel de ρ (x>0). | CONFIRMÉE (domaine: 0<x) | V101 | 2 |
| `collective_projection_eq_two_re_over_positive` (l.342) | Sur la constellation, la somme des termes résiduels vaut la somme sur les positifs de 2·Re du terme. | CONFIRMÉE (domaine: 0<x) | V101 | 0 |

### `Round26B4OrderedGapPositionInterface`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `one_le_gnat` (l.68) | L'écart canonique gnat n entre premiers consécutifs est ≥ 1. | CONFIRMÉE | V13 | 1 |
| `gnat_ne_zero` (l.76) | L'écart canonique gnat n n'est jamais nul. | CONFIRMÉE | V13 | 2 |
| `gnat_pos` (l.81) | L'écart canonique gnat n est strictement positif. | CONFIRMÉE | V13 | 18 |
| `constellationGaps_length_eq` (l.87) | La liste des écarts de constellation a pour longueur celle de la vue ordonnée moins 1. | CONFIRMÉE | AJOUT | 4 |
| `constellationGaps_getElem_eq_orderedInternalGapWithNext` (l.95) | L'écart interne à la position i de la vue ordonnée est l'entrée i des écarts de constellation. | CONFIRMÉE (domaine: i < longueur) | AJOUT | 9 |
| `exists_zero_gap_of_off_critical_line` (l.148) | Un membre hors ligne parmi les représentants positifs de hauteur T force un écart nul dans les écarts de constellation. | CONFIRMÉE SOUS CONDITION (un représentant positif hors ligne) | V162,V165 | 3 |
| `exists_position_with_zero_internal_gap_of_off_critical_line` (l.169) | Même condition : il existe une position dont l'écart interne avec le suivant est 0. | CONFIRMÉE SOUS CONDITION (un représentant positif hors ligne) | V162,V165 | 4 |

### `Round26B4PrimeGapExactMellinCancellation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `thetaErrorReal_eq_sub_chebyshev_on_gap` (l.67) | Entre deux premiers consécutifs, l'erreur θ vaut t − θ(p m). [terme hors maître] | CONFIRMÉE (domaine: p m ≤ t < p(m+1)) | V13,V48 | 2 |
| `p_pos_real` (l.89) | Le m-ième premier réel est strictement positif. | CONFIRMÉE | V13 | 80 |
| `p_lt_p_succ_real` (l.93) | p m < p(m+1) dans ℝ. | CONFIRMÉE | V13 | 9 |
| `exact_gap_integrand_intervalIntegrable` (l.96) | (t−c)²/t² est intégrable sur l'écart [p m, p(m+1)]. | CONFIRMÉE | AJOUT | 4 |
| `thetaLocalEnergy_prime_gap_integrand_eq` (l.113) | Sur un écart, l'intégrale de θerr²/t² égale l'intégrale de (t−θ(p m))²/t². | CONFIRMÉE | AJOUT | 4 |
| `thetaLocalEnergy_prime_gap_exact` (l.124) | L'énergie locale θ sur un écart premier égale le terme exact primeGapExactMellinTerm m. | CONFIRMÉE | AJOUT | 5 |
| `primeGapExactMellinTerm_nonneg` (l.193) | Chaque terme exact d'écart premier est ≥ 0. | CONFIRMÉE | AJOUT | 1 |
| `cube_difference_midpoint_identity` (l.209) | ((b−c)³−(a−c)³)/3 = (b−a)((a+b)/2−c)² + (b−a)³/12. | CONFIRMÉE | AJOUT | 3 |
| `primeGapExactMellinTerm_lower_bound` (l.216) | Le terme d'écart premier est minoré par g·(erreur au milieu)²/p(m+1)². | CONFIRMÉE | AJOUT | 1 |
| `primeGapExactMellinTerm_upper_bound` (l.265) | Le terme d'écart premier est majoré par (g·err² + g³/12)/p(m)². | CONFIRMÉE | AJOUT | 3 |
| `primeGapExactMellinTerm_sandwich` (l.314) | Encadrement du terme d'écart premier par les bornes inférieure et supérieure. | CONFIRMÉE | AJOUT | 0 |
| `primeGapExactMellinEnergy_nonneg` (l.332) | L'énergie exacte de Mellin sur [m0,m1] est ≥ 0. | CONFIRMÉE | AJOUT | 0 |
| `theta_mellin_prime_bracket_exact` (l.336) | Pour m0 ≤ m1, l'énergie continue θerr²/t² sur [p m0, p m1] égale la somme des termes d'écart premier. | CONFIRMÉE (domaine: m0 ≤ m1) | AJOUT | 1 |
| `thetaMellinLocalEnergy_le_primeGapExactMellinEnergy` (l.360) | Pour U ≥ log 3, l'énergie locale dyadique est dominée par l'énergie exacte sur [p 1, p ⌈2e^U⌉]. | CONFIRMÉE (domaine: log 3 ≤ U) | AJOUT | 1 |
| `primeGapExactMellinEnergy_le_midpoint_majorant` (l.406) | L'énergie exacte est majorée par la somme finie des majorants d'écart. | CONFIRMÉE | AJOUT | 2 |
| `primeGapExactMellinSubexponential_of_midpoint_majorant` (l.416) | Si le majorant élémentaire est sous-exponentiel, PrimeGapExactMellinSubexponential vaut. | CONFIRMÉE (domaine: sous-exponentialité du majorant du point milieu ) | AJOUT | 1 |
| `subexponential_thetaMellin_of_primeGapExact` (l.436) | PrimeGapExactMellinSubexponential entraîne la sous-exponentialité de thetaMellinLocalEnergy. | CONFIRMÉE SOUS CONDITION (PrimeGapExactMellinSubexponential) | AJOUT | 1 |
| `riemann_hypothesis_from_prime_gap_exact_mellin_subexponential` (l.460) | PrimeGapExactMellinSubexponential entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | AJOUT | 1 |

### `Round26B4PrimeGapExactMellinFullSandwich`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `primeGapExactMellinTerm_full_lower_bound` (l.66) | Le terme d'écart premier est minoré par (g·err²+g³/12)/p(m+1)². | CONFIRMÉE | AJOUT | 2 |
| `primeGapExactMellinTerm_full_sandwich` (l.114) | Le terme d'écart est encadré par la même quantité (g·err²+g³/12) divisée par p(m+1)² et p(m)². | CONFIRMÉE | AJOUT | 0 |
| `p_succ_le_two_mul_real` (l.127) | Postulat de Bertrand réel : p(m+1) ≤ 2·p m. | CONFIRMÉE | AJOUT | 1 |
| `midpoint_majorant_term_le_four_mul_primeGapExactMellinTerm` (l.131) | Le majorant du point milieu d'un écart est ≤ 4 × le terme exact de Mellin. | CONFIRMÉE | AJOUT | 1 |
| `midpoint_majorant_le_four_mul_primeGapExactMellinEnergy` (l.165) | La somme des majorants sur [m0,m1) est ≤ 4 × l'énergie exacte de Mellin. | CONFIRMÉE | AJOUT | 2 |
| `primeGapExactMellinEnergy_midpoint_majorant_two_sided` (l.186) | L'énergie exacte est encadrée par la somme des majorants et 4× l'énergie (deux sens). | CONFIRMÉE | AJOUT | 0 |
| `primeGapExactMellinSubexponential_iff_midpoint_majorant` (l.201) | PrimeGapExactMellinSubexponential ⟺ la somme finie arithmétique des majorants est sous-exponentielle. | CONFIRMÉE | AJOUT | 1 |
| `riemann_hypothesis_from_midpoint_majorant_subexponential` (l.230) | Si la somme arithmétique des majorants d'écart est sous-exponentielle (∀ε ∃C ...), alors RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | AJOUT | 0 |
| `primeGapMidpointError_eq_residual` (l.256) | L'erreur au point milieu d'un écart vaut R m + p0 − log(p m) + (écart)/2. | CONFIRMÉE | AJOUT | 2 |
| `primeGapMidpointError_eq_gap_family_sum` (l.272) | L'erreur au point milieu s'écrit par somme sur les familles d'écarts des résidus g n − log p n plus termes de bord. | CONFIRMÉE | AJOUT | 0 |
| `R_eq_Tmode_add_aT_zero` (l.306) | Pour m≥1, le résidu cumulatif R m égale Tmode m + aT 0. | CONFIRMÉE (domaine: 1 ≤ m) | AJOUT | 1 |
| `primeGapMidpointError_eq_Tmode_affine` (l.313) | Pour m≥1, l'erreur au milieu s'écrit en Tmode plus trois termes de bord. | CONFIRMÉE (domaine: 1 ≤ m) | AJOUT | 0 |

### `Round26B4ProjectedAnnularAccumulation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `thetaScaleFourCellConstant_eq_neg_chebyshev_block` (l.38) | La constante de cellule d'échelle quatre vaut moins le bloc θ de Tchebychev entre p j et p m. [terme hors maître] | CONFIRMÉE (domaine: 1 ≤ j ≤ m) | V48 | 2 |
| `thetaScaleFourCellConstant_eq_neg_theta_block` (l.51) | Même constante = −(θm(m+1) − θm(j+1)) (forme à indice premier). | CONFIRMÉE (domaine: 1 ≤ j ≤ m) | V48 | 1 |
| `thetaScaleFourCellConstant_eq_neg_sum_log_primes` (l.60) | Même constante = −Σ_{n=j+1}^{m} log p_n. | CONFIRMÉE (domaine: 1 ≤ j ≤ m) | V48 | 4 |
| `scaleCellQuadraticForm_degenerate` (l.77) | Une sous-cellule dégénérée (a,a) ne porte aucune énergie quelle que soit la constante. | CONFIRMÉE | AJOUT | 3 |
| `thetaScaleFourMellinEnergy_eq_cell_recomposed_annular_sum` (l.83) | Pour U ≥ log 12, l'énergie de Mellin d'échelle quatre est la double somme de formes quadratiques de sous-cellules à constante = bloc annulaire θ. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 0 |
| `thetaScaleFourMellinEnergy_eq_cell_recomposed_log_mass_sum` (l.106) | Même recomposition avec la constante écrite comme −Σ log p_n. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 0 |
| `phiOf_eq_walsh` (l.131) | phiOf n = (1 − σ_n)/2 avec σ le caractère χ3 de l'état premier. [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `phiOf_coboundary_eq_walsh` (l.137) | phiOf(n+1) − phiOf n = (σ_n − σ_{n+1})/2. | CONFIRMÉE | AJOUT | 2 |
| `grammarCross_eq_walsh` (l.144) | Pour n≥2, le terme croisé de grammaire vaut (1 − σ_n σ_{n+1})/2. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 2 |
| `grammarCross_eq_coboundary_sq` (l.151) | Pour n≥2, le terme croisé est le carré du cobord (phiOf(n+1) − phiOf n)². | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 1 |
| `transform6_indicator_walsh_11` (l.165) | Pour n≥2, l'indicatrice de la transformation τ11 vaut (1+σ_n)(1+σ_{n+1})/4. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 0 |
| `transform6_indicator_walsh_15` (l.174) | Pour n≥2, l'indicatrice de τ15 vaut (1+σ_n)(1−σ_{n+1})/4. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 0 |
| `transform6_indicator_walsh_51` (l.183) | Pour n≥2, l'indicatrice de τ51 vaut (1−σ_n)(1+σ_{n+1})/4. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 0 |
| `transform6_indicator_walsh_55` (l.192) | Pour n≥2, l'indicatrice de τ55 vaut (1−σ_n)(1−σ_{n+1})/4. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 0 |
| `transform6_sum_expand` (l.218) | Une somme sur Transform6 se développe en quatre termes τ11, τ15, τ51, τ55. | CONFIRMÉE | AJOUT | 5 |
| `_private.RhGapCriterion.Round26B4ProjectedAnnularAccumulation.0.RhGap.norm_sq_re_add_im` (l.227) | ‖z‖² = (re z)² + (im z)². | CONFIRMÉE | AJOUT | 1 |
| `sector_state_walsh_reconstruction_of_coboundary_zero` (l.234) | Si la coordonnée de cobord est nulle, l'état de secteur se reconstruit par (G+2H+Y, G−Y, G−Y, G−2H+Y)/4. | CONFIRMÉE SOUS CONDITION (coordonnée de cobord du secteur nulle) | AJOUT | 0 |
| `grammarResidueEnergy_walsh_formula_of_coboundary_zero` (l.252) | Si le cobord de secteur est nul, l'énergie résiduelle vaut \|G\|²/4+\|H\|²/2+\|Y\|²/4. | CONFIRMÉE SOUS CONDITION (coordonnée de cobord nulle) | AJOUT | 1 |
| `canonicalScaleFourThetaZeroAmplitude_eq_neg_explicit_div` (l.280) | L'amplitude θ d'échelle quatre d'un zéro vaut − résidu explicite / ρ. [terme hors maître] | CONFIRMÉE | V100,V102 | 1 |
| `grammar_sector_residue_four_term_sum` (l.294) | La somme des quatre résidus de secteur égale le résidu explicite d'échelle quatre en ρ. | CONFIRMÉE | AJOUT | 1 |
| `projectedGrammarResidueState_global` (l.303) | La coordonnée globale de l'état projeté égale le mode θ canonique du zéro. | CONFIRMÉE | AJOUT | 4 |
| `canonicalThetaZeroMode_ne_zero` (l.316) | Le mode θ canonique ne s'annule jamais en un zéro non trivial. | CONFIRMÉE (domaine: ρ zéro non trivial ) | V102 | 2 |
| `projectedGrammarResidueState_ne_zero` (l.324) | L'état projeté d'un zéro non trivial est non nul. | CONFIRMÉE (domaine: ρ zéro non trivial ) | AJOUT | 1 |
| `projectedGrammarResidueState_energy_pos` (l.335) | L'énergie de l'état projeté d'un zéro non trivial est strictement positive. | CONFIRMÉE (domaine: ρ zéro non trivial ) | AJOUT | 1 |
| `projectedGrammarResidueState_coboundary_zero` (l.344) | Si le cobord du résidu spectral est nul, celui de l'état projeté l'est à tout U. | CONFIRMÉE SOUS CONDITION (cobord du résidu spectral nul) | AJOUT | 2 |
| `projectedGrammarResidueState_walsh_energy` (l.356) | Si le cobord résiduel est nul, l'énergie de l'état projeté vaut ‖mode‖²/4+‖H‖²/2+‖Y‖²/4. | CONFIRMÉE SOUS CONDITION (cobord du résidu spectral nul) | AJOUT | 0 |
| `projectedGrammarResidueState_global_shift` (l.379) | La coordonnée globale du décalage d'échelle quatre vaut 4^(ρ−1/2) × la coordonnée globale de l'état projeté. | CONFIRMÉE | V102 | 0 |
| `projectedScaleFourShift_eq_smul` (l.389) | Le décalage d'échelle quatre de l'état projeté est composante par composante 4^(ρ−1/2) × l'état. | CONFIRMÉE | V102 | 0 |
| `canonicalThetaZeroMode_scale_four_iterate` (l.403) | Le mode θ canonique vérifie mode(U+n log 4) = (4^(ρ−1/2))^n × mode(U). | CONFIRMÉE | V102 | 0 |
| `norm_canonicalThetaZeroMode_orbit` (l.429) | La norme du mode θ sur l'orbite U+n log 4 vaut amplitude × e^{(re−1/2)U} × (e^{(re−1/2)log 4})^n. | CONFIRMÉE | V102 | 2 |
| `not_geometric_le_polynomial` (l.442) | Une suite géométrique de raison q>1 ne peut être majorée par un polynôme en n. | CONFIRMÉE (domaine: K>0, q>1 et hypothèse de majoration ∀n ) | AJOUT | 1 |
| `round26_grammar_spectral_scale_rigidity_of_annular_accumulation` (l.471) | Pour un zéro non trivial dont l'accumulation annulaire d'échelle quatre est bornée, re ρ ≤ 1/2. | CONFIRMÉE SOUS CONDITION (ProjectedAnnularScaleFourAccumulation ρ U) | V102 | 3 |
| `projected_annular_accumulation_of_re_le_half` (l.498) | Si re ρ ≤ 1/2, l'accumulation annulaire d'échelle quatre est bornée à tout U. | CONFIRMÉE SOUS CONDITION (re ρ ≤ 1/2) | V102 | 2 |
| `projected_annular_accumulation_iff_re_le_half` (l.525) | Pour tout zéro non trivial et tout U, accumulation annulaire ⟺ re ρ ≤ 1/2. | CONFIRMÉE | V102 | 1 |
| `all_nontrivial_zeros_re_le_half_of_annular_accumulation` (l.541) | Si tout zéro non trivial vérifie l'accumulation annulaire en U=0, tout zéro non trivial a re ≤ 1/2. | IMPLIQUE RH SOUS PRÉMISSE | V126,O5 | 2 |
| `round27_all_zeros_on_critical_line_of_annular_accumulation` (l.547) | Si tout zéro non trivial vérifie l'accumulation annulaire en U=0, tout zéro non trivial a re=1/2. | IMPLIQUE RH SOUS PRÉMISSE | V126,O5 | 0 |
| `riemann_hypothesis_of_annular_accumulation` (l.554) | Si tout zéro non trivial vérifie ProjectedAnnularScaleFourAccumulation en U=0, alors RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | AJOUT | 0 |

### `Round26B4PromotedPrototypeLemmas`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `canonicalTHorizon_monotone` (l.63) | L'horizon canonique ⌈exp ·⌉ est monotone. | CONFIRMÉE | AJOUT | 2 |
| `rawRWindowEnergy_scale_chasles` (l.71) | Pour r≥1, l'énergie brute R en fenêtres r se recolle : E_r(U+log r)+E_r(U) = E_{r²}(U+log r). | CONFIRMÉE (domaine: 1 ≤ r) | AJOUT | 0 |
| `Rseq_sub_eq_sum_dR` (l.120) | Pour m≤k, Rseq k − Rseq m est la somme des incréments. | CONFIRMÉE (domaine: m ≤ k) | AJOUT | 1 |
| `centered_R_sq_le_card_mul_sum_dR_sq` (l.127) | Pour m≤k, (Rseq k − Rseq m)² ≤ (k−m) × somme des carrés des incréments. | CONFIRMÉE (domaine: m ≤ k) | AJOUT | 1 |
| `R_succ_sub_R_eq_aT` (l.142) | R(n+1) − R n = aT n. | CONFIRMÉE | AJOUT | 3 |
| `centered_R_sq_le_card_mul_sum_aT_sq` (l.149) | Pour m≤k, (R k − R m)² ≤ (k−m) × Σ aT². | CONFIRMÉE (domaine: m ≤ k) | AJOUT | 2 |
| `R_sq_le_card_mul_sum_aT_sq` (l.156) | R k² ≤ k × Σ_{j<k} aT j². | CONFIRMÉE | AJOUT | 0 |
| `R_eq_centered_add_boundary` (l.167) | R k = (R k − R m) + R m. | CONFIRMÉE | AJOUT | 0 |
| `young_param_upper` (l.170) | Pour η>0, (a+b)² ≤ (1+η)a² + (1+1/η)b². | CONFIRMÉE (domaine: 0<η) | AJOUT | 2 |
| `young_param_reverse` (l.180) | Pour η>0, (1−η)c² − (1/η−1)a² ≤ (a+c)². | CONFIRMÉE (domaine: 0<η) | AJOUT | 1 |

### `Round26B4RealBlockVoiceExhibition`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `nontrivialZeroResidueTerm_scale` (l.51) | Le terme individuel d'un zéro transporte sous l'échelle lam≥0 avec le facteur lam^ρ. | CONFIRMÉE (domaine: 0≤lam, 0≤x) | V100,V102 | 1 |
| `scale_factor_eq_voiceScaleCharacter` (l.67) | Le facteur d'échelle lam^(ρ−1/2) est le caractère de voix évalué en log lam. | CONFIRMÉE (domaine: 0<lam) | AJOUT | 1 |
| `blockZeroContribution_join` (l.79) | La contribution d'un zéro sur un bloc réel se compose par jointure de blocs adjacents (télescopage). | CONFIRMÉE | AJOUT | 0 |
| `nontrivialZeroResidueTerm_ne_zero` (l.92) | Le terme individuel d'un zéro ne s'annule jamais en x>0. | CONFIRMÉE (domaine: 0<x) | V100 | 5 |
| `scale_transport_separates_zeros` (l.123) | Si lam^(ρ1−1/2)=lam^(ρ2−1/2) pour toute échelle lam>0, alors ρ1=ρ2. | CONFIRMÉE SOUS CONDITION (égalité des facteurs de transport à toute échelle) | V46 | 2 |
| `scale_transport_separates_conjugate_zeros` (l.138) | Un zéro non trivial se sépare de son conjugué : une échelle lam où les facteurs diffèrent existe. | CONFIRMÉE (domaine: ρ zéro non trivial ) | V63 | 0 |
| `blockZeroContribution_boundary_only` (l.153) | La contribution d'un zéro sur un bloc ne dépend que des deux premiers de bord. | CONFIRMÉE (domaine: mêmes premiers de bord (p n1 = p n2, p(n1+k1) = p(n2+k2)) ) | AJOUT | 1 |
| `blockZeroContribution_step` (l.178) | L'incrément de la contribution de bloc est la contribution entre deux premiers consécutifs. | CONFIRMÉE | AJOUT | 2 |

### `Round26B4RealOrderedBlockCarrier`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `realOrderedBlock_occurrences_prime` (l.43) | Chaque position du bloc réel est un premier. | CONFIRMÉE | V13 | 1 |
| `realOrderedBlock_order_strictMono` (l.49) | L'ordre interne du bloc réel est strictement croissant. | CONFIRMÉE (domaine: i<j ) | V13 | 1 |
| `real_blocks_adjacent_boundary` (l.55) | L'état de sortie d'un bloc égale l'état d'entrée du bloc suivant. | CONFIRMÉE | AJOUT | 0 |
| `signed_change_eq` (l.62) | Pour m≥2, le pas de poids d'état = [écart ≡4 mod 6] − [écart ≡2 mod 6]. | CONFIRMÉE (domaine: 2 ≤ m) | V174 | 2 |
| `changeCount_succ` (l.90) | Récurrence : changeCount c n (k+1) = changeCount c n k + [gnat(n+k) ≡ c mod 6]. | CONFIRMÉE | AJOUT | 2 |
| `real_block_change_imbalance_boundary` (l.102) | Pour n≥2, (#changements 4) − (#changements 2) dans un bloc = poids de sortie − poids d'entrée. | CONFIRMÉE (domaine: 2 ≤ n) | V174 | 4 |
| `real_block_change_imbalance_le_one` (l.129) | Pour n≥2, l'imbalance de familles d'un bloc réel est bornée par 1 en valeur absolue. | CONFIRMÉE (domaine: 2 ≤ n) | V174 | 0 |
| `state_preserved_of_maintenance_run` (l.139) | Un run d'écarts ≡0 mod 6 préserve l'état p mod 6. | CONFIRMÉE (domaine: 2≤n, a≤b et écarts ≡0 mod 6 sur [a,b) ) | V174 | 1 |
| `real_block_change_skeleton_alternates` (l.158) | Deux écarts non nuls mod 6, séparés seulement par des écarts ≡0, sont l'un de classe 2, l'autre de classe 4. | CONFIRMÉE SOUS CONDITION (2≤n, i<j, écarts non nuls, écarts intermédiaires ≡0) | V174 | 2 |
| `changeCount_join` (l.206) | Les comptages de changements s'additionnent sur la jonction de deux blocs. | CONFIRMÉE | AJOUT | 1 |
| `real_blocks_join_eq` (l.218) | Le bloc réel joint se restreint champ par champ à ses deux moitiés. [type tronqué] | CONFIRMÉE | AJOUT | 1 |
| `real_blocks_join_preserves_change_order` (l.245) | L'alternance 2/4 ne dépend pas de la frontière entre deux blocs joints. | CONFIRMÉE (domaine: 2≤n, i<k1≤j, écarts non nuls séparés par des écarts ≡0 ) | V174 | 0 |
| `real_block_imbalance_join` (l.263) | L'imbalance d'un bloc joint est la somme des imbalances de ses deux moitiés. | CONFIRMÉE | AJOUT | 0 |
| `imbalance_cannot_separate_block_interiors` (l.276) | Deux blocs réels de mêmes états de bord ont la même imbalance, quels que soient leurs intérieurs. | CONFIRMÉE (domaine: 2≤n1,n2 et mêmes états d'entrée et de sortie ) | AJOUT | 0 |

### `Round26B4ReflectedPairLabelledTransport`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `reflectConjZero_eq_anonymous` (l.71) | Pour 0<re<1, reflectConjZero ρ est le sous-type ⟨1−conj ρ, _⟩ (coïncidence de définition). | CONFIRMÉE (domaine: 0<re ρ<1) | V65 | 2 |
| `offline_member_gives_labelled_table_entry_defect` (l.81) | Pour un zéro hors ligne (0<re<1, re≠1/2), le réfléchi-conjugué est distinct et il existe une colonne n où défaut de contribution et entrées de table diffèrent. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V162,V167 | 2 |
| `reflected_pair_cells_same_labels_different_entries` (l.101) | Deux cases du crosswalk de même colonne, portant ρ et son réfléchi, sont distinctes, partagent écart, transition, bloc, poids, classe mod 6, mais diffèrent en entrée (type tronqué à la fin). [terme hors maître] | CONFIRMÉE SOUS CONDITION (lignes distinctes, même colonne, membres ρ et reflectConjZero ρ, défaut de contribution) | V159,V162 | 2 |
| `reflectedPairMember_zero` (l.153) | Le membre d'indice 0 de la paire réfléchie est reflectedPairLeft ρ. [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `reflectedPairMember_one` (l.156) | Le membre d'indice 1 de la paire réfléchie est reflectedPairRight ρ. | CONFIRMÉE | AJOUT | 0 |
| `reflectedPair_left_ne_right_iff` (l.165) | Les deux membres de la paire (gauche, droite) sont distincts ssi re ρ ≠ 1/2. | CONFIRMÉE | V62,V161 | 1 |
| `reflectedPair_left_ne_right` (l.177) | Si re ρ ≠ 1/2, gauche ≠ droite. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V62 | 2 |
| `reflectedPair_card_eq_two` (l.183) | Si re ρ ≠ 1/2, le support de la paire a exactement deux éléments. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V63,V64 | 0 |
| `reflectedPair_members_are_nontrivial_zeros` (l.190) | Les deux membres de la paire sont des zéros non triviaux. | CONFIRMÉE | V62,V74 | 0 |
| `reflectedPair_members_have_same_height` (l.197) | Les deux membres ont la même hauteur que ρ. | CONFIRMÉE | V65 | 0 |
| `reflectedPair_right_height_eq_left` (l.206) | Droite et gauche ont même hauteur. | CONFIRMÉE | V65 | 0 |
| `reflectedPair_members_have_same_multiplicity` (l.212) | Les deux membres ont même multiplicité. | CONFIRMÉE | V63,V65 | 0 |
| `reflectedPairFinset_subset_heightConstellation` (l.219) | La paire d'un membre de la constellation de hauteur T reste dans cette constellation. | CONFIRMÉE (domaine: ρ dans la constellation) | V64 | 0 |
| `reflectedPairFinset_sum` (l.230) | Hors ligne, une somme sur le support de la paire est f(gauche)+f(droite). | CONFIRMÉE SOUS CONDITION (re ρ ≠ 1/2) | AJOUT | 1 |
| `tsum_eq_reflectedPairFinset_add_rest` (l.251) | Pour x>1, la somme totale des termes résiduels sur tous les zéros = somme sur le support de la paire + reste. | CONFIRMÉE (domaine: 1<x) | V124,V121 | 1 |
| `tsum_eq_reflectedPair_left_add_right_add_rest` (l.261) | Pour x>1 et re≠1/2, somme totale = terme(gauche)+terme(droite)+reste. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V124,V121 | 2 |
| `primitivePsiPart_smoothedZeroPrimitive` (l.319) | La couche psi générique appliquée à la primitive lissée canonique est psiRecoveredFromZeros. [terme hors maître] | CONFIRMÉE | V48,V121 | 1 |
| `primitiveWeightedPart_smoothedZeroPrimitive` (l.323) | La couche pondérée appliquée à la primitive canonique est zerosWeightedCount. | CONFIRMÉE | V48 | 1 |
| `primitivePrimeCountPart_smoothedZeroPrimitive` (l.327) | La couche comptage premier appliquée à la primitive canonique est zerosPrimeCountReal. | CONFIRMÉE | V48 | 1 |
| `primitiveThetaPart_smoothedZeroPrimitive` (l.331) | Pour x≥2, la couche theta appliquée à la primitive canonique est chebyshevθ ⌊x⌋. | CONFIRMÉE (domaine: 2 ≤ x) | V48,V121 | 1 |
| `weightedKernel_continuousOn` (l.339) | Le noyau d'Abel −t⁻¹/log(t)² est continu sur [2,x]. | CONFIRMÉE (domaine: 2 ≤ x) | AJOUT | 1 |
| `intervalIntegrable_kernel_mul_primitivePsiPart` (l.344) | Pour toute primitive P et noyau continu K, K·Re(primitivePsiPart P) est intégrable sur [a,b]. | CONFIRMÉE (domaine: a ≤ b, K continu) | AJOUT | 1 |
| `intervalIntegrable_weightedKernel_primitivePsiPart` (l.355) | Cas du noyau d'Abel : intégrable sur [2,x]. | CONFIRMÉE (domaine: 2 ≤ x) | AJOUT | 2 |
| `continuousOn_primitiveWeightedPrimitive` (l.363) | La primitive d'Abel de primitivePsiPart P est continue sur [2,x]. | CONFIRMÉE (domaine: 2 ≤ x) | AJOUT | 1 |
| `intervalIntegrable_inv_mul_primitiveWeightedPart_rpow` (l.378) | Intégrabilité de t⁻¹·primitiveWeightedPart P (t^{1/m}) sur [2^m,x]. | CONFIRMÉE (domaine: 2 ≤ x, m dans le cutoff) | AJOUT | 1 |
| `intervalIntegrable_inv_mul_activePrimitiveMobiusTerm` (l.460) | Intégrabilité de t⁻¹·terme de Möbius actif sur [2,x]. | CONFIRMÉE (domaine: 2 ≤ x, m dans le cutoff) | AJOUT | 1 |
| `primitivePrimeCountPart_eq_fixed_cutoff` (l.515) | Réécriture du comptage premier générique à support fixe (somme de Möbius/m avec indicatrice). | CONFIRMÉE (domaine: 2 ≤ x, t dans [2,x]) | V48 | 1 |
| `intervalIntegrable_inv_mul_primitivePrimeCountPart` (l.536) | Intégrabilité de t⁻¹·comptage premier générique sur [2,x]. | CONFIRMÉE (domaine: 2 ≤ x) | AJOUT | 1 |
| `primitivePsiPart_add` (l.571) | primitivePsiPart est additif en la primitive. | CONFIRMÉE | AJOUT | 2 |
| `primitiveWeightedPart_add` (l.577) | primitiveWeightedPart est additif. | CONFIRMÉE (domaine: 2 ≤ x) | AJOUT | 2 |
| `primitivePrimeCountPart_add` (l.598) | primitivePrimeCountPart est additif. | CONFIRMÉE (domaine: 2 ≤ x) | AJOUT | 2 |
| `primitiveThetaPart_add` (l.607) | primitiveThetaPart est additif. | CONFIRMÉE (domaine: 2 ≤ x) | AJOUT | 1 |
| `primitivePsiPart_congr` (l.627) | primitivePsiPart ne dépend de P que via ses valeurs sur y>1. | CONFIRMÉE (domaine: P=Q sur y>1 ) | AJOUT | 2 |
| `primitiveWeightedPart_congr` (l.638) | Idem pour primitiveWeightedPart. | CONFIRMÉE (domaine: P=Q sur y>1 ) | AJOUT | 2 |
| `primitivePrimeCountPart_congr` (l.652) | Idem pour primitivePrimeCountPart. | CONFIRMÉE (domaine: P=Q sur y>1 ) | AJOUT | 2 |
| `primitiveThetaPart_congr` (l.659) | Idem pour primitiveThetaPart. | CONFIRMÉE (domaine: P=Q sur y>1 ) | AJOUT | 1 |
| `smoothedZeroPrimitive_eq_left_add_right_add_rest` (l.695) | Pour x>1 et re≠1/2, la primitive canonique = primitive(gauche)+primitive(droite)+primitive(reste). | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V124,O6 | 2 |
| `smoothedZeroPrimitive_eq_sum_of_gt_one` (l.710) | Pour re≠1/2, forme fonctionnelle de la même décomposition sur y>1. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | O6 | 4 |
| `psiRecoveredFromZeros_eq_left_add_right_add_rest` (l.725) | Pour t≥2 et re≠1/2, psiRecoveredFromZeros = somme des psi-parts des trois composantes. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V121,O6 | 2 |
| `zerosWeightedCount_eq_left_add_right_add_rest` (l.737) | Décomposition analogue de zerosWeightedCount. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | O6 | 0 |
| `zerosPrimeCountReal_eq_left_add_right_add_rest` (l.749) | Décomposition analogue de zerosPrimeCountReal. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | O6 | 0 |
| `chebyshev_theta_eq_left_add_right_add_rest` (l.761) | theta de Tchebychev = somme des theta-parts des trois composantes de la paire. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V121,O6 | 2 |
| `chebyshev_theta_at_prime_eq_left_add_right_add_rest` (l.775) | Même décomposition évaluée en un premier p_j. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V121,O6 | 2 |
| `reflectedPair_primitive_difference_unbounded` (l.796) | Hors ligne, la différence des primitives gauche/droite aux premiers p_j est non bornée. | CONFIRMÉE SOUS CONDITION (0<re<1, re≠1/2) | V102,V167 | 1 |
| `reflectedPair_psi_separated` (l.829) | Hors ligne, il existe n≥2 où psi-parts gauche et droite diffèrent. | CONFIRMÉE SOUS CONDITION (0<re<1, re≠1/2) | V162,V167 | 2 |
| `complex_re_not_injective` (l.883) | Complex.re n'est pas injective. | CONFIRMÉE | AJOUT | 2 |
| `complex_separation_does_not_give_real_separation` (l.904) | Il existe z≠w avec même partie réelle. | CONFIRMÉE | AJOUT | 0 |
| `offline_member_contradicts_prime_side_uniqueness` (l.942) | Sous PrimeSideLabelledEntryUniqueness, deux cases de même colonne portant ρ et son réfléchi avec défaut de contribution donnent False. | CONFIRMÉE SOUS CONDITION (PrimeSideLabelledEntryUniqueness (prémisse)) | V126 | 0 |
| `not_reflectedPairRestNonRestoration` (l.975) | Pour re≠1/2, ReflectedPairRestNonRestoration ρ est fausse (le reste restaure la sortie totale). | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 0 |
| `reflectConjZero_swaps_reflectedPair` (l.997) | L'involution échange gauche et droite de la paire. | CONFIRMÉE | V63 | 0 |
| `reflectedPairFinset_stable_under_reflectConjZero` (l.1004) | Le support de la paire est stable par l'involution. | CONFIRMÉE (domaine: τ dans le support) | V63 | 1 |
| `reflectedPairRest_domain_stable_under_reflectConjZero` (l.1018) | Le complément du support est stable par l'involution. | CONFIRMÉE (domaine: τ hors du support) | V63 | 0 |

### `Round26B4ReflectionOrbit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `mem_reflectionOrbit_self` (l.62) | ρ appartient à sa propre orbite de réflexion. [terme hors maître] | CONFIRMÉE | V63 | 2 |
| `reflectConjZero_mem_reflectionOrbit` (l.69) | Le réfléchi-conjugué de ρ appartient à l'orbite de ρ. | CONFIRMÉE | V63 | 1 |
| `mem_reflectionOrbit_iff` (l.76) | σ est dans l'orbite de ρ ssi σ=ρ ou σ=reflectConjZero ρ. | CONFIRMÉE | V63 | 5 |
| `reflectionOrbit_reflectConjZero` (l.84) | L'orbite du réfléchi-conjugué de ρ est l'orbite de ρ. | CONFIRMÉE | V63 | 2 |
| `reflectionOrbit_eq_of_mem` (l.94) | Si σ est dans l'orbite de ρ, les deux orbites coïncident. | CONFIRMÉE (domaine: σ dans l'orbite) | V63 | 1 |
| `reflectionOrbit_card_eq_one_iff` (l.102) | L'orbite de ρ a un élément ssi re ρ = 1/2. | CONFIRMÉE | V161,V77 | 0 |
| `reflectionOrbit_card_eq_two_iff` (l.119) | L'orbite de ρ a deux éléments ssi re ρ ≠ 1/2. | CONFIRMÉE | V63,V62 | 1 |
| `reflectionOrbit_card_eq_one_or_two` (l.127) | Le cardinal de l'orbite vaut 1 ou 2. | CONFIRMÉE | V63,V161 | 0 |
| `zeroHeight_constant_on_reflectionOrbit` (l.134) | La hauteur est constante sur une orbite. | CONFIRMÉE (domaine: σ dans l'orbite) | V65 | 0 |
| `multiplicity_constant_on_reflectionOrbit` (l.141) | La multiplicité est constante sur une orbite. | CONFIRMÉE (domaine: σ dans l'orbite) | V65 | 0 |
| `reflectionOrbit_subset_heightConstellation` (l.149) | L'orbite d'un membre de la constellation de hauteur T y reste. | CONFIRMÉE (domaine: ρ dans la constellation) | V64 | 0 |
| `orbitStepContribution_reflectConjZero` (l.167) | La contribution d'orbite ne dépend que de l'orbite (invariante par ρ ↦ réfléchi). | CONFIRMÉE | AJOUT | 1 |
| `orbitStepContribution_of_critical_line` (l.175) | Pour re=1/2, la contribution d'orbite égale la contribution individuelle. | CONFIRMÉE (domaine: zéro sur la ligne ) | V161 | 0 |
| `orbitStepContribution_of_off_critical_line` (l.184) | Pour re≠1/2, la contribution d'orbite est la somme des contributions de ρ et de son réfléchi. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V63,V167 | 1 |
| `orbitsOf_biUnion_eq` (l.202) | Pour S stable par l'involution, la réunion des orbites rencontrées est S. | CONFIRMÉE SOUS CONDITION (S stable par reflectConjZero) | AJOUT | 1 |
| `orbitsOf_pairwiseDisjoint` (l.223) | Les orbites rencontrées par S sont deux à deux disjointes. | CONFIRMÉE | AJOUT | 1 |
| `sum_eq_sum_over_orbits` (l.239) | Pour S stable, une somme sur S est la somme sur les orbites des sommes par orbite. | CONFIRMÉE (domaine: S stable par l'involution ) | AJOUT | 1 |
| `heightConstellation_sum_eq_sum_over_orbits` (l.254) | Une somme sur la constellation de hauteur T est la somme sur ses orbites. | CONFIRMÉE | V64 | 0 |

### `Round26B4TerminalArithmeticClosurePrototype`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `bounded_measurable_div_intervalIntegrable` (l.60) | f mesurable bornée sur [a,b] : f(t)/t est intégrable sur [a,b]. [terme hors maître] | CONFIRMÉE (domaine: 0<a≤b, f mesurable et \|f\|≤M) | AJOUT | 1 |
| `thetaScaleFourDefectReal_div_intervalIntegrable` (l.85) | Pour U ≥ log 4, defect_scale4(t)/t est intégrable sur [e^U, 2e^U]. | CONFIRMÉE (domaine: log 4 ≤ U) | AJOUT | 2 |
| `affine_mellin_cell_linear_integral_exact` (l.98) | ∫_a^b (αt+C)/t dt = α(b−a)+C(log b−log a). | CONFIRMÉE (domaine: 0<a, 0<b) | AJOUT | 1 |
| `scaleCellLinearMoment_same` (l.135) | Le moment linéaire de cellule sur [a,a] est nul. | CONFIRMÉE | AJOUT | 2 |
| `scale_subcell_linear_signal_exact` (l.138) | Sur une sous-cellule premier/échelle-quatre, ∫ defect/t = moment linéaire de cellule avec la constante de cellule. | CONFIRMÉE (domaine: bornes de cellule (a≤b, 0<a, p_m≤a, b≤p_{m+1}, p_j≤a/4, b/4≤p_{j+1}, m,j≥1)) | AJOUT | 1 |
| `scale_subcell_linear_signal_exact_indexed` (l.166) | Même identité sur la sous-cellule indexée scaleSubBreak. | CONFIRMÉE (domaine: log 12 ≤ U, cellule non dégénérée) | AJOUT | 1 |
| `scale_subcell_linear_signal_exact_indexed_or_degenerate` (l.199) | Même identité, cellule dégénérée incluse. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 1 |
| `scaleSubBreak_div_intervalIntegrable` (l.218) | defect/t est intégrable sur chaque sous-cellule scaleSubBreak. | CONFIRMÉE (domaine: log 4 ≤ U) | AJOUT | 1 |
| `thetaScaleFourMellinLinearSignal_eq_double_partition_sum` (l.228) | Le signal linéaire de Mellin échelle quatre est une double somme d'intégrales sur les sous-cellules. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 1 |
| `thetaScaleFourMellinLinearSignal_eq_indexed_linear_sum` (l.273) | Le signal est la double somme des moments linéaires de cellule. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 2 |
| `thetaScaleFourMellinLinearSignal_eq_indexed_log_mass_sum` (l.289) | Idem avec la constante de cellule écrite −Σ log p_n (masse logarithmique centrée). | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 0 |
| `inner_log_mass_sum_abel_by_parts` (l.315) | Somme interne masse-log par sommation d'Abel (par parties). | CONFIRMÉE (domaine: M ≤ i+1) | AJOUT | 2 |
| `log_scaleSubBreak_diff_bound` (l.364) | \|log SSB(i,j) − log SSB(i,k)\| ≤ log 2. | CONFIRMÉE | AJOUT | 2 |
| `inner_log_mass_sum_abs_le` (l.395) | Valeur absolue de la somme interne majorée par log 2·(\|constante\|+Σ log p). | CONFIRMÉE (domaine: M ≤ i+1) | AJOUT | 0 |
| `inner_log_mass_sum_eq_effective_cutoff` (l.453) | La somme interne sur range M égale la somme tronquée à min M (i+1). | CONFIRMÉE | AJOUT | 1 |
| `inner_log_mass_sum_abel_by_parts_effective` (l.490) | Sommation d'Abel de la somme interne avec troncature effective min M (i+1). | CONFIRMÉE | AJOUT | 1 |
| `triangularLogKernelRect_eq_triangularLogKernel` (l.530) | Les deux formes (rectangulaire, Ico) du noyau logarithmique triangulaire coïncident. | CONFIRMÉE | AJOUT | 1 |
| `mem_range_min_succ_sub_one_iff` (l.541) | j ∈ range(min M (i+1) − 1) ⟺ j ∈ range(M−1) et j<i. | CONFIRMÉE | AJOUT | 0 |
| `sum_range_ite_lt_eq_sum_Ico` (l.548) | Somme sur range N avec indicatrice j<i égale la somme sur Ico (j+1) N. | CONFIRMÉE | AJOUT | 3 |
| `sum_range_sum_range_min_pred_eq` (l.560) | Identité de Fubini triangulaire finie (transposition du domaine). | CONFIRMÉE | AJOUT | 1 |
| `inner_double_sum_eq_triangular_kernelRect` (l.580) | La double somme signée se factorise par le noyau triangulaire rectangulaire. | CONFIRMÉE | AJOUT | 1 |
| `inner_double_sum_eq_triangular_kernel` (l.600) | Même identité avec le noyau Ico simplifié. | CONFIRMÉE | AJOUT | 1 |
| `scaleCellLinearMoment_sum_eq_endpoint_add_log_mass` (l.621) | Somme des moments = 3/4 (différence de bornes) + somme constante×différence de logs. | CONFIRMÉE | AJOUT | 1 |
| `thetaScaleFourMellinLinearSignal_eq_global_signed_kernel_identity` (l.642) | Le signal linéaire complet = terme affine de bord + terme de bord d'Abel externe − noyau triangulaire apparié aux log-premiers. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 1 |
| `triangularLogKernel_succ_sub` (l.692) | Différence première du noyau triangulaire : terme d'entrée plus somme de différences de poids. | CONFIRMÉE (domaine: j+2 ≤ N) | AJOUT | 2 |
| `triangularLogWeight_succ_sub` (l.705) | La différence de poids triangulaires est un incrément log de fenêtre adjacent. | CONFIRMÉE | AJOUT | 1 |
| `triangularLogKernel_succ_sub_simplified` (l.713) | Différence première simplifiée : terme d'entrée + somme d'incréments log de fenêtre. | CONFIRMÉE (domaine: j+2 ≤ N) | AJOUT | 1 |
| `triangularLogKernel_second_diff` (l.733) | Différence seconde exacte du noyau triangulaire. | CONFIRMÉE (domaine: j+3 ≤ N) | AJOUT | 0 |
| `logPrimePrefix_succ_sub` (l.787) | logPrimePrefix(J+1) − logPrimePrefix J = log p(J+2). | CONFIRMÉE | AJOUT | 2 |
| `triangularLogKernel_second_abel` (l.793) | Deuxième sommation d'Abel de la somme pondérée par log p et le noyau. | CONFIRMÉE | AJOUT | 1 |
| `thetaScaleFourMellinLinearSignal_eq_double_abel_identity` (l.822) | Signal linéaire complet avec le terme noyau-log-premier remplacé par sa forme doublement Abel (type tronqué). | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 1 |
| `M1_triangularLogKernel_telescopes` (l.854) | Le noyau triangulaire télescope en j (différences finies). | CONFIRMÉE | AJOUT | 0 |
| `triangularLogWeight_abs_le` (l.862) | \|poids triangulaire\| ≤ log 2. | CONFIRMÉE | AJOUT | 2 |
| `M2_triangularLogKernel_abs_le` (l.870) | \|noyau\| ≤ (N−(j+1))·log 2 ; la docstring dit « tested and FAILED » pour l'uniformité en N (borne croissante). | CONFIRMÉE | AJOUT | 1 |
| `M3_triangularLogKernel_linear_in_N` (l.885) | \|noyau\| ≤ N·log 2 (variation linéaire en N). | CONFIRMÉE | AJOUT | 0 |
| `M4_triangularLogKernel_chasles` (l.897) | Le noyau à l'horizon N = noyau à N' + somme des poids sur Ico N' N. | CONFIRMÉE (domaine: j+1 ≤ N' ≤ N) | AJOUT | 0 |
| `M5_triangularLogKernel_eq_zero_of_ge` (l.907) | Si N ≤ j+1, le noyau est nul. | CONFIRMÉE (domaine: N ≤ j+1) | AJOUT | 0 |
| `S1_second_diff_sign_undetermined_statement` (l.915) | La différence seconde du poids triangulaire égale log SSB(j+3)−2log SSB(j+2)+log SSB(j+1) (le signe reste ouvert selon la docstring). | CONFIRMÉE | AJOUT | 0 |
| `S2_triangularLogKernel_support` (l.926) | Le noyau = somme des poids sur Ico (j+1) N. | CONFIRMÉE | AJOUT | 0 |
| `S3_triangularLogWeight_constant_uniform` (l.933) | \|poids triangulaire\| ≤ log 2 (constante indépendante de U,i,j). | CONFIRMÉE | AJOUT | 0 |
| `second_abel_remainder_diagonal_bulk_split` (l.949) | Le reste du second Abel se scinde en terme diagonal et terme bulk. | CONFIRMÉE (domaine: n+1 ≤ N) | AJOUT | 1 |
| `sum_range_sum_Ico_add_two_eq` (l.979) | Fubini fini pour une double somme Ico décalée. | CONFIRMÉE | AJOUT | 1 |
| `bulk_term_eq_column_sum` (l.998) | Le terme bulk réindexé par colonne k (troncature min n (k−1)). | CONFIRMÉE | AJOUT | 1 |
| `column_inner_sum_third_abel` (l.1022) | Troisième identité d'Abel par colonne. | CONFIRMÉE | AJOUT | 2 |
| `bulk_term_eq_third_abel_column_sum` (l.1067) | Le terme bulk avec chaque somme interne transformée par un troisième Abel. | CONFIRMÉE | AJOUT | 1 |
| `thetaScaleFourMellinLinearSignal_eq_completeGlobalSignedObject` (l.1086) | Recomposition signée globale complète après troisième Abel (type tronqué). | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 0 |
| `logPrimePrefix_ge_linear` (l.1147) | logPrimePrefix J ≥ J·log 2. | CONFIRMÉE | AJOUT | 0 |
| `column_inner_sum_third_abel_succ_sub` (l.1160) | Différence avant en m de la somme Abel par colonne = un seul terme de bord. | CONFIRMÉE (domaine: 1 ≤ m) | AJOUT | 0 |
| `scaleCellQuadraticForm_le_of_abs_le` (l.1244) | La forme quadratique de cellule est monotone en \|C\|. | CONFIRMÉE (domaine: 0<a≤b, \|C\|≤B) | AJOUT | 2 |
| `thetaScaleFourMellinEnergy_le_of_cellConstant_bound` (l.1261) | Si \|constantes de cellule\| ≤ B i j, l'énergie de Mellin échelle quatre est majorée par la somme des formes quadratiques de cellule en B. | CONFIRMÉE (domaine: majoration ponctuelle des constantes de cellule ) | AJOUT | 0 |
| `thetaScaleFourMellinEnergy_le_of_primeLogBlockSum_bound` (l.1287) | Si \|Σ log p_n sur le bloc\| ≤ B i j, l'énergie de Mellin échelle quatre est majorée par la somme des formes quadratiques de cellule en B. | CONFIRMÉE (domaine: majoration ponctuelle des sommes de log-premiers ) | AJOUT | 0 |
| `canonicalTHorizon_nat_mul_upper` (l.1330) | canonicalTHorizon(U+log k) ≤ k·canonicalTHorizon U. | CONFIRMÉE (domaine: 1 ≤ k) | AJOUT | 2 |
| `canonicalTHorizon_nat_mul_lower` (l.1341) | k·canonicalTHorizon U − (k−1) ≤ canonicalTHorizon(U+log k). | CONFIRMÉE (domaine: 1 ≤ k) | AJOUT | 2 |
| `canonicalTHorizon_double_bounds` (l.1365) | Encadrement de canonicalTHorizon(U+log 2) par 2·H(U)−1 et 2·H(U). | CONFIRMÉE | AJOUT | 0 |
| `canonicalTHorizon_quadruple_bounds` (l.1374) | Encadrement de canonicalTHorizon(U+log 4) par 4·H(U)−3 et 4·H(U). | CONFIRMÉE | AJOUT | 0 |
| `dynamicPairKernelClosedForm_le_inv_windowBreak` (l.1391) | Le noyau de paire dynamique est ≤ 1/windowBreak(max m n). | CONFIRMÉE | AJOUT | 1 |
| `dynamicPairKernelClosedForm_le_exp_neg` (l.1406) | Le noyau de paire dynamique est ≤ e^{−U}. | CONFIRMÉE | AJOUT | 0 |
| `dynamicPairKernelClosedForm_eq_zero_of_clamp_le` (l.1420) | Le noyau est nul quand la borne (clamp) domine la fenêtre externe. | CONFIRMÉE (domaine: min(4p_{r+1},2e^U) ≤ windowBreak ) | AJOUT | 4 |
| `dynamicPairKernelClosedForm_eq_prime_endpoint` (l.1432) | Région B : le noyau = 1/windowBreak − 1/(4 p_{r+1}). | CONFIRMÉE (domaine: windowBreak < 4p_{r+1} ≤ 2e^U ) | AJOUT | 1 |
| `dynamicPairKernelClosedForm_eq_window_endpoint` (l.1446) | Région C : le noyau = 1/windowBreak − 1/(2e^U). | CONFIRMÉE (domaine: windowBreak < 2e^U < 4p_{r+1} ) | AJOUT | 1 |
| `dynamicPairKernelClosedForm_trichotomy` (l.1458) | Tout couple (m,n) tombe dans l'une des trois régions (nul, borne premier, borne fenêtre). | CONFIRMÉE | AJOUT | 1 |
| `dynamicPairKernelClosedForm_pos_iff_lt_clamp` (l.1490) | Le noyau est >0 ssi windowBreak < min(4p_{r+1},2e^U). | CONFIRMÉE | AJOUT | 0 |
| `dynamicPairKernelClosedForm_eq_zero_of_windowBreak_eq_two_exp` (l.1509) | Si windowBreak(max m n) = 2e^U, le noyau est nul. | CONFIRMÉE (domaine: windowBreak = 2e^U ) | AJOUT | 0 |
| `dynamicPairKernelClosedForm_eq_zero_of_r_zero` (l.1518) | Si min(H(U),min m n)=0, le noyau est nul. | CONFIRMÉE (domaine: indice r=0 ) | AJOUT | 0 |
| `lt_min_of_prime_region` (l.1535) | a<b≤c entraîne a<min b c. | CONFIRMÉE | AJOUT | 1 |
| `lt_min_of_rightcap_region` (l.1539) | a<c<b entraîne a<min b c. | CONFIRMÉE | AJOUT | 1 |
| `dynamicPairwiseInnovationClosedForm_eq_two_branch` (l.1563) | La forme close de l'innovation par paires = branche premier + branche bord droit. | CONFIRMÉE | AJOUT | 1 |
| `canonicalTHorizon_le_shift` (l.1606) | canonicalTHorizon U ≤ canonicalTHorizon(U+log k). | CONFIRMÉE (domaine: 1 ≤ k) | AJOUT | 2 |
| `canonicalTHorizon_persistent_subset` (l.1612) | range(H U) ⊆ range(H(U+log k)). | CONFIRMÉE (domaine: 1 ≤ k) | AJOUT | 1 |
| `canonicalTHorizon_range_eq_persistent_union_entering` (l.1616) | range(H(U+log k)) = range(H U) ∪ Ico(H U, H(U+log k)). | CONFIRMÉE (domaine: 1 ≤ k) | AJOUT | 1 |
| `canonicalTHorizon_persistent_entering_disjoint` (l.1624) | Indices persistants et entrants sont disjoints. | CONFIRMÉE | AJOUT | 1 |
| `canonicalTHorizon_no_exiting_indices` (l.1633) | Aucun indice ne sort de l'horizon sous le décalage log k. | CONFIRMÉE (domaine: 1 ≤ k) | AJOUT | 0 |
| `p_succ_lt_two_exp_of_surviving` (l.1648) | Sur une paire survivante (windowBreak<2e^U), p(m+1) et p(n+1) sont < 2e^U. | CONFIRMÉE (domaine: windowBreak(max m n) < 2e^U ) | AJOUT | 1 |
| `card_range_prime_succ_lt_le` (l.1664) | Le nombre de n<M avec p(n+1)<B est ≤ ⌈B⌉. | CONFIRMÉE | AJOUT | 1 |
| `H2_trivial_rate_no_gain` (l.1684) | Le nombre de colonnes à support échelle quatre sur la branche premier est ≤ ⌈8e^U⌉ (taux trivial). | CONFIRMÉE | AJOUT | 0 |
| `windowBreak_strictly_below_windowBreak_quadruple_shift` (l.1728) | windowBreak U i < windowBreak (U+log 4) i. | CONFIRMÉE | AJOUT | 0 |
| `zero_reconstructed_Rgap_eq_Rgap` (l.1756) | Le résidu cumulatif d'écarts reconstruit depuis les zéros égale R, terme à terme. | CONFIRMÉE | V48,V174 | 0 |
| `innovationJ_eq_Rgap_sub_coboundary` (l.1775) | innovationJ n = R(n+1) − R n − (phiOf(n+1)−phiOf n). | CONFIRMÉE | AJOUT | 1 |
| `sum_union_sum_union_eq_four_blocks` (l.1798) | Double somme sur A∪B (disjoints) = quatre blocs A×A, A×B, B×A, B×B. | CONFIRMÉE (domaine: A et B disjoints ) | AJOUT | 2 |
| `scaleFourPersistentEnteringIndexSet_disjoint` (l.1822) | Les ensembles d'indices persistants et entrants (échelle quatre) sont disjoints. | CONFIRMÉE | AJOUT | 2 |
| `scaleFourPersistentUnionEnteringIndexSet_eq` (l.1826) | Persistants ∪ entrants = range(H(U+log 2+log 4)). | CONFIRMÉE | AJOUT | 2 |
| `dynamicPairwiseInnovationPrimeBranch_eq_sum_integrand` (l.1840) | La branche premier est la double somme des intégrandes. | CONFIRMÉE | AJOUT | 1 |
| `dynamicPairwiseInnovationPrimeBranch_shift_eq_four_blocks` (l.1869) | Branche premier au décalage log 4 = cœur persistant + deux blocs mixtes + bloc entrant-entrant. | CONFIRMÉE | AJOUT | 1 |
| `sum_diag_add_sum_offdiag` (l.1898) | Double somme carrée = diagonale + hors-diagonale. | CONFIRMÉE | AJOUT | 1 |
| `scaleFourTransportedPersistentCore_diag_offdiag_split` (l.1910) | Cœur persistant = somme diagonale + somme hors-diagonale. | CONFIRMÉE | AJOUT | 0 |
| `dynamicPairwiseInnovationRightCapBranch_eq_sum_integrand` (l.1944) | La branche bord droit est la double somme des intégrandes. | CONFIRMÉE | AJOUT | 1 |
| `dynamicPairwiseInnovationRightCapBranch_shift_eq_four_blocks` (l.1968) | Branche bord droit au décalage log 4 = quatre blocs (miroir de la branche premier). | CONFIRMÉE | AJOUT | 1 |
| `dynamicPairwiseInnovationClosedForm_shift_eq_eight_blocks` (l.1984) | Forme close complète au décalage log 4 = huit blocs. | CONFIRMÉE | AJOUT | 0 |
| `sum_innovationJ_Ico_eq_Rgap_block_sub_coboundary` (l.2009) | Σ_{n∈Ico a b} innovationJ n = R b − R a − (phiOf b − phiOf a). | CONFIRMÉE (domaine: a ≤ b ) | AJOUT | 2 |
| `weighted_rank_one_pair_sum_eq_square` (l.2026) | Somme par paires à poids de rang un = w·(Σ χ x)². | CONFIRMÉE | AJOUT | 0 |
| `windowBreak_monotone` (l.2094) | windowBreak U est monotone. | CONFIRMÉE | AJOUT | 2 |
| `windowBreak_max_eq` (l.2097) | windowBreak U (max m n) = max des deux windowBreak. | CONFIRMÉE | AJOUT | 1 |
| `primeClampEndpoint_min_eq` (l.2102) | primeClampEndpoint U (min m n) = min des deux extrémités. | CONFIRMÉE | AJOUT | 1 |
| `min_min_min_eq_real` (l.2126) | min a (min b c) = min (min a b) (min a c). | CONFIRMÉE | AJOUT | 1 |
| `dynamicRightEndpoint_pair_eq` (l.2132) | L'extrémité droite de la paire est le min des deux extrémités individuelles. | CONFIRMÉE | AJOUT | 1 |
| `pair_active_iff_both_fibres_active` (l.2149) | La fenêtre active de la paire est l'intersection des deux fibres individuelles. | CONFIRMÉE | AJOUT | 1 |
| `pairActiveIndicator_eq_mul_fibreIndicators` (l.2170) | L'indicatrice de paire active est le produit des indicatrices de fibres. | CONFIRMÉE | AJOUT | 2 |
| `intervalIntegrable_inv_sq` (l.2194) | 1/t² est intégrable sur [a,b] avec 0<a≤b. | CONFIRMÉE (domaine: 0<a≤b) | AJOUT | 2 |
| `dynamicPairKernelClosedForm_eq_integral` (l.2200) | Le noyau de paire dynamique est l'intégrale sur [e^U,2e^U] du produit des indicatrices de fibres contre le poids 1/t². | CONFIRMÉE | AJOUT | 1 |
| `primeClampEndpoint_monotone` (l.2296) | primeClampEndpoint U est monotone. | CONFIRMÉE | AJOUT | 1 |
| `dynamicFibreLeft_monotone` (l.2307) | dynamicFibreLeft U est monotone. | CONFIRMÉE | AJOUT | 2 |
| `dynamicFibreRight_monotone` (l.2311) | dynamicFibreRight U est monotone. | CONFIRMÉE | AJOUT | 2 |
| `activeIndexSets_nonempty` (l.2325) | Pour t<2e^U, les deux ensembles d'indices actifs sont non vides. | CONFIRMÉE (domaine: t<2e^U ) | AJOUT | 5 |
| `dynamicFibreActive_iff_mem_Ico` (l.2348) | Pour t<2e^U, la fibre active est exactement un intervalle contigu Ico. | CONFIRMÉE (domaine: t<2e^U ) | AJOUT | 1 |
| `activeUpperIndex_le_horizon` (l.2374) | L'indice actif supérieur ne dépasse pas H(U+log 2). | CONFIRMÉE (domaine: t<2e^U ) | AJOUT | 2 |
| `activeLowerIndex_le_horizon` (l.2385) | L'indice actif inférieur ne dépasse pas H(U). | CONFIRMÉE (domaine: t<2e^U ) | AJOUT | 1 |
| `activeUpperIndex_monotoneOn` (l.2412) | activeUpperIndex U est monotone en t sur t<2e^U. | CONFIRMÉE (domaine: t1≤t2<2e^U ) | AJOUT | 1 |
| `activeLowerIndex_monotoneOn` (l.2424) | activeLowerIndex U est monotone en t sur t<2e^U. | CONFIRMÉE (domaine: t1≤t2<2e^U ) | AJOUT | 1 |
| `activeUpperIndex_eq_succ_iff` (l.2434) | activeUpperIndex U t = i+1 ⟺ dynamicFibreLeft i < t ≤ dynamicFibreLeft (i+1). | CONFIRMÉE (domaine: t<2e^U) | AJOUT | 3 |
| `activeLowerIndex_eq_succ_iff` (l.2465) | activeLowerIndex U t = i+1 ⟺ dynamicFibreRight i ≤ t < dynamicFibreRight (i+1). | CONFIRMÉE (domaine: t<2e^U) | AJOUT | 3 |
| `dynamicPairKernelIntegrand_intervalIntegrable` (l.2502) | L'intégrande du noyau de paire dynamique est intégrable sur [e^U,2e^U]. | CONFIRMÉE | AJOUT | 1 |
| `dynamicPairwiseInnovationClosedForm_eq_integral_fibre_sum_sq` (l.2564) | La forme close d'innovation par paires est l'intégrale sur [e^U,2e^U] du carré de la somme innovationJ·indicatrice de fibre, contre 1/t². | CONFIRMÉE | AJOUT | 1 |
| `active_fibre_innovation_sum_eq_sum_Ico` (l.2656) | La somme d'innovation sur la fibre active égale la somme d'innovationJ sur Ico(activeLower, activeUpper). | CONFIRMÉE (domaine: t<2e^U) | AJOUT | 1 |
| `active_fibre_innovation_sum_eq_ite_Rgap_sub_phi_boundary` (l.2693) | La somme d'innovation sur la fibre active = (R(upper)−R(lower)−(phi(upper)−phi(lower))) si lower≤upper, sinon 0. | CONFIRMÉE (domaine: t<2e^U) | AJOUT | 2 |
| `active_fibre_innovation_sum_eq_Rgap_sub_phi_boundary` (l.2716) | Forme conditionnelle de G6 : si lower≤upper, la somme = R(upper)−R(lower)−(phi(upper)−phi(lower)). | CONFIRMÉE (domaine: activeLower ≤ activeUpper ) | AJOUT | 0 |
| `sum_Ico_log_p_succ_sub_eq_log_p_sub` (l.2736) | Somme télescopique de log p sur Ico j m = log p_m − log p_j. | CONFIRMÉE (domaine: j ≤ m ) | AJOUT | 1 |
| `grammar_coboundary_cancels_exactly_in_scaleCellCenteredConstant` (l.2747) | Pour j≤m, la constante de cellule centrée = R m − R j − (log p_m − log p_j) − (p_m − p_j) (phiOf éliminé). | CONFIRMÉE (domaine: j ≤ m) | AJOUT | 0 |
| `active_fibre_innovation_sum_eq_Rgap_fibre_block_sub_boundary` (l.2783) | La somme d'innovation sur la fibre active = RGAP_FIBRE_BLOCK − GRAMMAR_FIBRE_BOUNDARY. | CONFIRMÉE (domaine: t<2e^U) | AJOUT | 1 |
| `abs_GRAMMAR_FIBRE_BOUNDARY_le_one` (l.2797) | \|GRAMMAR_FIBRE_BOUNDARY\| ≤ 1. | CONFIRMÉE | AJOUT | 0 |
| `dynamicPairwiseInnovationClosedForm_eq_integral_Rgap_fibre_block_sq` (l.2813) | La forme close d'innovation = intégrale du carré de (RGAP_FIBRE_BLOCK − GRAMMAR_FIBRE_BOUNDARY) contre 1/t². | CONFIRMÉE | AJOUT | 0 |
| `total_mass_inv_sq_window` (l.2831) | ∫_{e^U}^{2e^U} dt/t² = (1/2)e^{−U}. | CONFIRMÉE | AJOUT | 0 |
| `primeCounting'_p` (l.2857) | primeCounting'(p n) = n. | CONFIRMÉE | V13 | 0 |
| `activeUpperIndex_eq_succ_iff_primeCounting_of_unclamped` (l.2863) | Sans borne active, activeUpperIndex U t = i+1 ⟺ primeCounting'(⌈t⌉) = i+2. | CONFIRMÉE (domaine: p(i+1), p(i+2) dans [e^U,2e^U] ) | AJOUT | 0 |
| `activeLowerIndex_eq_succ_iff_primeCounting_of_unclamped` (l.2897) | Sans borne active, activeLowerIndex U t = j+1 ⟺ primeCounting(⌊t/4⌋) = j+2. | CONFIRMÉE (domaine: 4p(j+1), 4p(j+2) ≤ 2e^U, e^U≤t<2e^U, indices ≤ horizon ) | AJOUT | 0 |
| `endpoint_pair_iff_cell` (l.2948) | Le couple d'indices (i+1,j+1) est caractérisé par les quatre inégalités de rupture. | CONFIRMÉE (domaine: t<2e^U) | AJOUT | 1 |
| `blockCellLeft_le_blockCellRight_of_endpoint_pair` (l.2957) | Si le couple est atteint en un t<2e^U, la cellule est non vide au sens faible. | CONFIRMÉE (domaine: couple d'indices atteint ) | AJOUT | 0 |
| `endpoint_pair_sum_strictMono_of_ne` (l.2983) | La somme lower+upper croît strictement quand le couple change. | CONFIRMÉE (domaine: t1≤t2<2e^U et couple différent ) | AJOUT | 2 |
| `endpoint_pair_sum_le_horizon_sum` (l.3001) | lower+upper ≤ H(U)+H(U+log 2). | CONFIRMÉE (domaine: t<2e^U) | AJOUT | 2 |
| `endpoint_pair_distinct_count_le` (l.3010) | Le support en escalier est additif (somme des horizons), non le quadrillage N². | CONFIRMÉE (domaine: couples différents en t1,t2<2e^U ) | AJOUT | 0 |
| `blockCellLeft_pos` (l.3036) | blockCellLeft U i j > 0. | CONFIRMÉE | AJOUT | 2 |
| `blockWeight_nonneg` (l.3041) | blockWeight U i j ≥ 0. | CONFIRMÉE | AJOUT | 1 |
| `blockWeight_pos_iff_overlap` (l.3060) | blockWeight>0 ⟺ blockCellLeft<blockCellRight. | CONFIRMÉE | AJOUT | 1 |
| `blockWeight_pos_implies_endpoint_pair_realized` (l.3078) | blockWeight>0 entraîne qu'un t<2e^U réalise le couple (i+1,j+1). | CONFIRMÉE SOUS CONDITION (blockWeight U i j > 0) | AJOUT | 1 |
| `blockWeightSupport_card_le_horizon_sum` (l.3107) | Le cardinal du support de blockWeight ≤ H(U)+H(U+log 2)+1. | CONFIRMÉE | AJOUT | 0 |
| `telescope_range_rev` (l.3161) | Σ_{j<N}(f j − f(j+1)) = f 0 − f N. | CONFIRMÉE | AJOUT | 2 |
| `scaleSubBreak_log_mass_row_telescopes` (l.3169) | Somme en ligne de la log-masse de cellule = log windowBreak(i+1) − log windowBreak i. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 1 |
| `scaleSubBreak_inverse_mass_row_telescopes` (l.3178) | Somme en ligne de la masse inverse = 1/windowBreak i − 1/windowBreak(i+1). | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 1 |
| `scaleSubBreak_log_mass_total_telescopes` (l.3189) | La log-masse totale de cellule vaut log 2. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 0 |
| `scaleSubBreak_inverse_mass_total_telescopes` (l.3209) | La masse inverse totale de cellule vaut (1/2)e^{−U}. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 0 |
| `staircaseCellDiscrepancy_eq_integral` (l.3232) | L'écart de cellule en escalier est l'intégrale de ((3/4)t+C)/t² sur la cellule. | CONFIRMÉE (domaine: 0<a≤b) | AJOUT | 0 |

### `Round26B4TotalVariationForce`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `norm_nontrivialZeroResidueTerm_eq` (l.58) | Pour x>0, ‖terme résiduel de ρ en x‖ = multiplicité·x^{Re ρ}/(‖ρ‖·‖ρ+1‖). | CONFIRMÉE (domaine: 0<x) | V102,V100 | 3 |
| `_private.RhGapCriterion.Round26B4TotalVariationForce.0.RhGap.prime_cast_pos` (l.72) | Le k-ième premier, vu dans ℝ, est strictement positif. | CONFIRMÉE | V13 | 2 |
| `zeroPrimeStepContribution_telescope` (l.78) | Les incréments zeroPrimeStepContribution ρ n (i+1), i<J, télescopent en terme(p_{n+J+1}) − terme(p_{n+1}). | CONFIRMÉE | AJOUT | 1 |
| `totalVariation_ge_boundary` (l.106) | La variation totale de la voix est ≥ l'écart des normes aux deux bords du segment. [terme hors maître] | CONFIRMÉE | AJOUT | 2 |
| `totalVariation_ge_scale_gap` (l.123) | La variation totale est ≥ (mult/(‖ρ‖‖ρ+1‖))·(p_{n+J+1}^{Re ρ} − p_{n+1}^{Re ρ}). | CONFIRMÉE | V102 | 0 |
| `grammarVoiceRow_true_abel_majorant_lower_bound` (l.146) | Le majorant d'Abel de la ligne de voix est minoré par 4‖T(q_r)‖ − 2‖T(q_0)‖ (négatif de portée exacte). | CONFIRMÉE | AJOUT | 1 |
| `grammarVoiceRow_true_abel_majorant_scale_lower_bound` (l.172) | Même minoration écrite à l'échelle avec l'exposant Re ρ. | CONFIRMÉE | V102 | 0 |

### `Round26B4TrueAbelVariation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `grammarVoiceRow_inner_sum_by_parts` (l.52) | Somme intérieure de la ligne de voix par sommation par parties exacte. | CONFIRMÉE | AJOUT | 3 |
| `grammarVoiceRow_inner_sum_by_parts_zero` (l.80) | Cas N=0 de la sommation par parties (identité). | CONFIRMÉE | AJOUT | 0 |
| `grammarVoiceRow_inner_sum_by_parts_one` (l.93) | Cas N=1 de la sommation par parties (identité). | CONFIRMÉE | AJOUT | 0 |
| `abel_difference_eq_zeroPrimeStepContribution` (l.108) | Chaque différence d'Abel des termes résiduels est zeroPrimeStepContribution ρ n (i+1). | CONFIRMÉE | AJOUT | 1 |
| `grammarVoiceRow_inner_sum_by_parts_step` (l.118) | La somme intérieure par parties, différences réécrites par zeroPrimeStepContribution. | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.Round26B4TrueAbelVariation.0.RhGap.grammarVariation_partial_sum_norm_le` (l.134) | Les sommes partielles de grammarVariation (dans ℂ) ont norme ≤ 2. | CONFIRMÉE | AJOUT | 1 |
| `grammarVoiceRow_inner_sum_norm_le` (l.143) | La norme de la somme intérieure est ≤ 2‖terme au bord‖ + 2·(variation totale des pas). | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.Round26B4TrueAbelVariation.0.RhGap.weight_term_norm_le` (l.183) | ‖grammarWeight n k · z‖ ≤ ‖z‖. | CONFIRMÉE | AJOUT | 1 |
| `grammarVoiceRow_norm_le_true_abel` (l.196) | ‖ligne de voix‖ est majorée par le majorant d'Abel (bords + 2·variation totale). | CONFIRMÉE | AJOUT | 0 |

### `Round26B4VoiceIdentityAnchor`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `zeroMode_scale_eigen` (l.67) | zeroMode ρ A (U+a) = voiceScaleCharacter ρ a · zeroMode ρ A U. [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `voiceScaleCharacter_add` (l.76) | voiceScaleCharacter est multiplicatif en le paramètre d'échelle. | CONFIRMÉE | AJOUT | 0 |
| `voiceScaleCharacter_injective` (l.86) | Deux nombres complexes ayant le même caractère d'échelle à toute échelle réelle sont égaux. | CONFIRMÉE (domaine: égalité des caractères à tout a ) | V46 | 3 |
| `zeroMode_norm_blind_to_height` (l.154) | La norme d'un mode de zéro ne dépend de ρ que par Re ρ. | CONFIRMÉE (domaine: Re ρ1 = Re ρ2 (amplitude aveugle à la hauteur) ) | V102,V158 | 0 |
| `grammarZeroModeEnergy_blind_to_height` (l.160) | L'énergie de secteur grammatical est identique pour deux ρ de même partie réelle. | CONFIRMÉE (domaine: Re ρ1 = Re ρ2 ) | V158,V159 | 1 |
| `grammarZeroModeEnergy_cannot_separate_conjugate_zeros` (l.167) | Pour tout zéro non trivial ρ, son conjugué est un autre zéro non trivial, distinct, avec la même énergie de secteur. | CONFIRMÉE | V63,V159 | 2 |
| `voiceScaleCharacter_separates_conjugate_zeros` (l.189) | Pour un zéro non trivial, le caractère d'échelle sépare ρ de son conjugué (∃ a). | CONFIRMÉE | V63,V158 | 0 |

### `Round26BASemanticGlobalClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `independent_passage_law_scheme_forces_bounded_critical_line` (l.7) | Si une loi de rigidité de passage indépendante est fournie pour toute fenêtre locale K=1 de hauteur T, tout représentant positif de hauteur T a re=1/2. | CONFIRMÉE SOUS CONDITION (loi de rigidité de passage indépendante fournie (fonction `law`)) | O5,O19 | 1 |
| `independent_passage_law_scheme_gives_global_critical_line` (l.19) | Si la loi est fournie pour toute hauteur T et fenêtre, tout zéro non trivial a re=1/2. | IMPLIQUE RH SOUS PRÉMISSE | O5,O19 | 0 |

### `Round26BASemanticIntruderChain`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `offline_produces_indexed_zero_gap` (l.38) | Si un représentant positif de hauteur T est hors ligne, une entrée indexée de constellationGaps T vaut exactement 0. | CONFIRMÉE SOUS CONDITION (un représentant positif hors ligne) | V66,V162,V165 | 4 |
| `offline_produces_degenerate_successive_passage` (l.49) | Même condition : il existe z tel que l'écart interne à la position z avec le suivant vaut 0. | CONFIRMÉE SOUS CONDITION (un représentant positif hors ligne) | V66,V162,V165 | 0 |
| `zero_gap_index_has_two_member_window` (l.55) | Un indice réel d'écart possède les deux membres de la fenêtre locale K=1. | CONFIRMÉE (domaine: z < longueur des écarts) | AJOUT | 5 |
| `passageProgressionTransfer_iff_critical_line` (l.63) | PassageProgressionTransfer T ⟺ tous les représentants positifs de hauteur T ont re=1/2. [terme hors maître] | CONFIRMÉE | V58,O10 | 2 |
| `offline_refutes_passageProgressionTransfer` (l.71) | Un représentant positif hors ligne réfute PassageProgressionTransfer T. | CONFIRMÉE SOUS CONDITION (un représentant positif hors ligne) | V58 | 1 |
| `offline_R1_R10_local_snapshot` (l.80) | Sous hors-ligne, une fenêtre locale contient un raccord structurel R1–R10 constructible ET un passage nul : les dix rigidités ne ferment pas seules la contradiction. | CONFIRMÉE SOUS CONDITION (un représentant hors ligne, 2≤n) | V83,O17 | 0 |
| `semantic_chain_A_B_D_without_C` (l.94) | Sous hors-ligne, une fenêtre K=1 a un passage zéro nul et une place première attribuée strictement progressive. | CONFIRMÉE SOUS CONDITION (un représentant hors ligne, 2≤n) | V66,V83 | 0 |
| `SemanticTerminalRaccord.r11_progression_transfer` (l.116) | Un raccord terminal sémantique fournit PassageProgressionTransfer T (champ de structure). | CONFIRMÉE | AJOUT | 1 |
| `SemanticTerminalRaccord.excludes_offline` (l.118) | Avec un raccord terminal sémantique (A+B+C+D), aucun représentant positif hors ligne n'existe. | CONFIRMÉE | AJOUT | 0 |
| `r11_is_exactly_local_critical_line` (l.125) | PassageProgressionTransfer T ⟺ ligne critique locale sur les représentants positifs (audit anti-circularité). | CONFIRMÉE | V58,O10 | 0 |
| `IndependentPassageRigidity.prime_forces` (l.140) | Une rigidité de passage indépendante fournit sa propriété à chaque i (projection). | CONFIRMÉE | AJOUT | 1 |
| `IndependentPassageRigidity.zero_gap_forbids` (l.141) | Une rigidité indépendante interdit sa propriété si l'écart interne à z+i vaut 0. | CONFIRMÉE (domaine: écart interne nul en z+i ) | AJOUT | 1 |
| `IndependentPassageRigidity.contradicts_zero_gap` (l.144) | Une rigidité indépendante et un écart interne nul à z+i donnent False. | CONFIRMÉE SOUS CONDITION (écart interne nul) | AJOUT | 1 |
| `independent_passage_law_scheme_excludes_offline` (l.151) | Si une loi indépendante existe pour toute fenêtre K=1, aucun représentant positif hors ligne n'existe à hauteur T. | CONFIRMÉE (domaine: `law` fournie pour toute fenêtre K=1 à hauteur T ) | O5,O19 | 1 |

### `Round26BASemanticPassageRaccord`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `zeroPassageWindow_length` (l.43) | Une fenêtre pleine de passages contient exactement K+1 membres. [terme hors maître] | CONFIRMÉE SOUS CONDITION (condition de domaine: z+(K+1) ≤ nombre de représentants positifs) | V50,V56 | 1 |
| `zeroPassageGaps_length` (l.50) | Une fenêtre pleine de K+1 membres porte exactement K écarts de passage. | CONFIRMÉE (domaine: fenêtre pleine ) | V56 | 1 |
| `zeroPassageWindow_nodup` (l.58) | La fenêtre de passage n'a aucun membre en double. | CONFIRMÉE | V8 | 0 |
| `zeroPassageWindow_ordered` (l.64) | Dans toute fenêtre, l'ordre est hauteur croissante puis partie réelle croissante. | CONFIRMÉE | V8,V68 | 0 |
| `zeroPassageGaps_are_successive` (l.72) | Les écarts de passage sont les différences successives des hauteurs de la même fenêtre. | CONFIRMÉE | V56 | 0 |
| `rankedPrimePlace_injective` (l.83) | Ajouter un rang de départ n'identifie aucune place première. | CONFIRMÉE | V49 | 0 |
| `SemanticStructuralRaccord.zero_window_full` (l.101) | Un raccord structurel sémantique garantit que la fenêtre de zéros est pleine (K+1 membres disponibles). [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `SemanticStructuralRaccord.r1_members_preserved` (l.109) | La fenêtre du raccord est exactement la fenêtre de passage des K+1 membres successifs. | CONFIRMÉE | V50 | 1 |
| `SemanticStructuralRaccord.r1_member_count` (l.110) | La fenêtre du raccord a K+1 membres. | CONFIRMÉE | V50 | 1 |
| `SemanticStructuralRaccord.r2_member_uniqueness` (l.113) | La fenêtre du raccord n'a pas de doublon. | CONFIRMÉE | V8 | 0 |
| `SemanticStructuralRaccord.r3_member_order` (l.116) | L'ordre hauteur puis partie réelle est conservé dans la fenêtre du raccord. | CONFIRMÉE | V8 | 0 |
| `SemanticStructuralRaccord.r4_successive_passages_exact` (l.122) | Les passages du raccord sont exactement les écarts successifs de la fenêtre. | CONFIRMÉE | V56 | 2 |
| `SemanticStructuralRaccord.r4_passage_count` (l.123) | Le raccord porte K passages. | CONFIRMÉE | V56 | 1 |
| `SemanticStructuralRaccord.r5_passage_place_bijective` (l.129) | L'application passage vers place est bijective. | CONFIRMÉE | V49,V56 | 0 |
| `SemanticStructuralRaccord.r5_passage_place_order` (l.132) | L'ordre des passages devient l'ordre des places. | CONFIRMÉE (domaine: i<j ) | V56 | 2 |
| `SemanticStructuralRaccord.r6_transition_exact` (l.136) | Toute place ciblée porte la transition exacte du bloc premier. | CONFIRMÉE | V48,V174 | 0 |
| `SemanticStructuralRaccord.r7_pattern_and_family_exact` (l.141) | Pattern et famille des places sont ceux du bloc canonique premier. | CONFIRMÉE | V48,V174 | 0 |
| `SemanticStructuralRaccord.r8_boundary_exact` (l.146) | L'état de sortie de ce bloc égale l'état d'entrée du bloc suivant. | CONFIRMÉE | V174 | 0 |
| `SemanticStructuralRaccord.r9_occurrences_exact` (l.149) | Les ensembles d'occurrences de patterns, familles et transitions reconstruits égalent ceux du côté premier. | CONFIRMÉE | V48,V174 | 0 |
| `SemanticStructuralRaccord.r10_global_transport` (l.159) | Position, écart, comptage, pi, theta, psi reconstruits égalent les objets premiers, et toute construction count/position/gap est transportée. | CONFIRMÉE | V48,V121,V174 | 0 |
| `SemanticStructuralRaccord.prime_place_progresses` (l.217) | Toute place première attribuée à un passage porte un écart strictement positif. | CONFIRMÉE | V61,V149 | 3 |
| `SemanticStructuralRaccord.family_zero_still_progresses` (l.223) | Même une place de famille 0 porte un écart strictement positif. | CONFIRMÉE (domaine: famille de la place = 0 ) | V61 | 0 |
| `SemanticStructuralRaccord.only_four_transitions` (l.230) | Toute place attribuée porte l'une des quatre transitions tau11, tau15, tau51, tau55. | CONFIRMÉE | V174 | 0 |
| `SemanticStructuralRaccord.class_projection` (l.239) | Classe d'écart mod 6 (0/2/4) et états de la transition (A/B) se déterminent mutuellement à la place. | CONFIRMÉE | V174 | 0 |

### `Round26BBLocalPassageRigidityAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `any_column_label_predicate_is_row_blind` (l.38) | Toute propriété construite avec les seuls quatre labels canoniques d'une colonne a même valeur de vérité sur deux lignes d'une même colonne. | CONFIRMÉE (domaine: même colonne ) | V159 | 0 |
| `offline_same_column_labels_do_not_determine_entry` (l.55) | Sous un raccord hors ligne aligné, les labels premiers des deux cases sont égaux mais leurs entrées de table diffèrent. | CONFIRMÉE (domaine: jonction hors ligne alignée donnée par l'objet) | V159,V162 | 0 |
| `grammarWeight_zero_of_family_zero` (l.74) | Pour n≥2 et gnat n ≡ 0 mod 6, le poids grammatical en (n,0) vaut 0. | CONFIRMÉE (domaine: 2≤n, famille 0) | AJOUT | 1 |
| `family_zero_grammarVoiceStep_is_row_blind` (l.85) | En famille 0 (n≥2), le pas de voix grammaticale est le même pour deux zéros quelconques. | CONFIRMÉE (domaine: 2≤n, gnat n ≡ 0 mod 6) | V159 | 0 |
| `offline_defect_survives_on_genuine_change_family` (l.94) | Pour re≠1/2, il existe n≥2 avec poids non nul et pas de voix distinct entre ρ et son réfléchi-conjugué. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V162 | 0 |
| `reflected_change_family_compatibility_is_target_strength` (l.102) | ReflectedChangeFamilyCompatibility ⟺ RhGap.RH. | ÉQUIVALENTE À RH | V126,O10 | 0 |
| `local_label_rigidity_and_offline_value_defect_coexist` (l.109) | Sur une jonction hors ligne alignée, la grammaire active est rigide ET les entrées de table de ρ et de son réfléchi diffèrent. | CONFIRMÉE (domaine: jonction fournie par l'objet) | V159,V162 | 0 |

### `Round26BFRealProgressionScientificAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `bf_prime_determined_real_zero_gaps_exact` (l.37) | Pour une continuation zêta déterminée par les premiers, les écarts de hauteur réels de la constellation égalent ceux de la source canonique. | CONFIRMÉE (domaine: IsPrimeDeterminedZetaContinuation F ) | V48 | 0 |
| `bf_prime_determined_intrinsic_property_iff` (l.47) | Pour une continuation déterminée par les premiers, toute propriété de la grammaire intrinsèque des zéros est transportée à l'identique. | CONFIRMÉE (domaine: IsPrimeDeterminedZetaContinuation F ) | V48 | 0 |
| `bf_direct_gap_defect_capture_is_target_strength` (l.59) | Sur une constellation bornée dont tous les zéros sont dans la bande, CapturePreservesIntruderDefect ⟺ tous les représentants positifs ont re=1/2. | CONFIRMÉE SOUS CONDITION (longueur ≤ k et bande 0<re<1) | V126 | 0 |
| `bf_reconstructed_grammar_defect_is_target_strength` (l.71) | Si la loi première interdit D, « tout Off donne D sur la grammaire reconstruite » ⟺ « tout zéro a re=1/2 ». | ÉQUIVALENTE À RH | V126,V159 | 0 |
| `bf_reflectedGrammarCovariation_eq_row_difference` (l.97) | La covariation grammaticale réfléchie égale la différence des lignes de voix de ρ et de son réfléchi-conjugué. [terme hors maître] | CONFIRMÉE | AJOUT | 2 |
| `bf_offline_gives_nonzero_one_step_covariation` (l.110) | Pour re≠1/2, il existe n≥2 où la covariation à un pas est non nulle. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V162 | 1 |
| `bf_oneStepReflectedGrammarCompatibility_iff_global_critical_line` (l.135) | OneStepReflectedGrammarCompatibility ⟺ tout zéro non trivial a re=1/2. | ÉQUIVALENTE À RH | V126,O10 | 0 |

### `Round26BGCorrectivePhaseCandidate`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `norm_mul_sub_re_pos_of_cross_im_ne_zero` (l.58) | Un complexe de partie imaginaire non nulle a re z < ‖z‖. | CONFIRMÉE (domaine: Im z ≠ 0 ) | AJOUT | 1 |
| `reflectedFloor_eq_norm_sub_re` (l.73) | Le plancher réfléchi vaut 2(‖z‖−Re z) pour z le produit de phase. [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `reflectedFloor_pos_of_phase_product_im_ne_zero` (l.87) | Si le produit de phase n'est pas réel, le plancher réfléchi est >0. | CONFIRMÉE (domaine: Im(produit de phase) ≠ 0 ) | AJOUT | 1 |
| `im_reflectedPoleProduct` (l.106) | Im du produit de pôles réfléchi = 2γ(2β−1)(β²−β−γ²−1). | CONFIRMÉE | V16 | 1 |
| `reflectedPoleProduct_last_factor_neg` (l.117) | Dans la bande, β²−β−γ²−1 < 0. | CONFIRMÉE | V7 | 1 |
| `im_reflectedPoleProduct_ne_zero` (l.124) | Hors ligne, Im du produit de pôles est non nul. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V162 | 1 |
| `reflectedPhaseProduct_eq_div` (l.139) | Le produit de phase est le quotient du produit des multiplicités par le produit de pôles. | CONFIRMÉE | AJOUT | 1 |
| `im_reflectedPhaseProduct_ne_zero` (l.156) | Hors ligne, le produit de phase n'est pas réel. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V162 | 1 |
| `reflectedFloor_pos_of_offline` (l.179) | Hors ligne, le plancher réfléchi est strictement positif. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V162,V167 | 2 |
| `reflectedDefect_pos_at_every_prime_column` (l.187) | Hors ligne, à toute colonne première p n, le carré du défaut réfléchi est minoré par plancher×p n >0. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V167 | 1 |

### `Round26BGRealProgressionFloorAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `two_sqrt_mul_le_add_div` (l.95) | AM-GM : 2√(AB) ≤ A t + B/t. | CONFIRMÉE (domaine: A,B,t>0) | AJOUT | 2 |
| `add_div_eq_two_sqrt_mul` (l.108) | Le minimum AM-GM est atteint en t=√(B/A). | CONFIRMÉE (domaine: A,B>0) | AJOUT | 1 |
| `closedForm_nonneg_is_exponent_blind` (l.133) | Si 2√(AB)+2C ≥ 0, la forme A x^(1+e)+B x^(1−e)+2Cx est ≥0 pour tout exposant e. | CONFIRMÉE (domaine: A,B>0, x>0) | AJOUT | 0 |
| `reflectedNormSqProfile_factor` (l.161) | Le profil de norme² réfléchi se factorise en x·(A x^(2re−1)+B/x^(2re−1)+2C). | CONFIRMÉE (domaine: x>0) | AJOUT | 3 |
| `reflectedNormSqProfile_ge_floor` (l.182) | Le profil de norme² réfléchi est minoré par plancher×x à toute échelle x>0. | CONFIRMÉE (domaine: x>0) | AJOUT | 2 |
| `reflectedFloor_nonneg` (l.192) | Le plancher réfléchi est ≥ 0. | CONFIRMÉE | AJOUT | 0 |
| `reflectedNormSqProfile_floor_attained` (l.217) | Hors ligne, il existe une échelle x>0 où le profil vaut exactement plancher×x. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 1 |
| `normalizedReflectedDefect_isLeast` (l.238) | Hors ligne, le défaut réfléchi normalisé (norme²/x) admet le plancher réfléchi comme plus petit élément (minoration atteinte). | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 1 |
| `normalizedReflectedDefect_unbounded` (l.254) | Hors ligne, le défaut réfléchi normalisé norme²/x n'est pas majoré. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 1 |
| `norm_rowEntry_eq_coeff_rpow` (l.293) | La norme du terme résiduel de ρ en x>0 vaut ‖coefficient de ligne‖·x^{re ρ}. | CONFIRMÉE (domaine: x>0) | V102 | 1 |
| `trueAbel_majorant_ge_row_size` (l.300) | Le majorant d'Abel de la ligne de voix est au moins ‖coeff‖·p(n+K)^{re ρ}. | CONFIRMÉE | AJOUT | 0 |
| `rpow_gt_half_beats_critical_order` (l.320) | Pour b>1/2 et c>0, x^b finit par dépasser toute borne C·x^{1/2}. | CONFIRMÉE (domaine: b>1/2, c>0 ) | AJOUT | 0 |
| `transport_adds_no_exclusion` (l.352) | Le transport d'une propriété le long d'une égalité S=T est une équivalence P S ↔ P T. | CONFIRMÉE (domaine: S=T ) | AJOUT | 1 |
| `primeDetermined_transport_adds_no_exclusion` (l.357) | Pour une continuation déterminée par les premiers, toute propriété de la source déterminée est une propriété de la source canonique. | CONFIRMÉE (domaine: IsPrimeDeterminedZetaContinuation F ) | V48 | 0 |
| `sound_complete_member_detector_iff_critical_line` (l.371) | Si P est vraie sur la ligne et fausse hors ligne, « P pour tout membre » ⟺ tout zéro non trivial a re=1/2. | ÉQUIVALENTE À RH | V126,O10 | 1 |
| `global_critical_line_of_sound_complete_detector` (l.392) | Si P est correcte, détectrice et vraie pour tout zéro, alors tout zéro non trivial a re=1/2. | IMPLIQUE RH SOUS PRÉMISSE | V126,O10 | 0 |
| `offline_normalized_defect_least_and_unbounded` (l.409) | Hors ligne, le défaut normalisé a un plus petit élément (plancher) atteint et n'est pas majoré. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 0 |

### `Round26CHTwoLockAlgebra`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `grammarWeightReal_eq_intCast` (l.49) | Le poids grammatical réel est le cast du poids entier. [terme hors maître] | CONFIRMÉE | AJOUT | 3 |
| `grammarSignReal_sq` (l.55) | Pour n≥2, le signe grammatical réel est de carré 1. | CONFIRMÉE (domaine: 2≤n) | AJOUT | 1 |
| `grammarSignReal_step_diff` (l.64) | La différence de signes consécutifs vaut −2 fois le poids grammatical. | CONFIRMÉE | AJOUT | 1 |
| `grammarSign_product_eq_one_sub_two_weight_sq` (l.71) | Pour n+k≥2, le produit de signes adjacents vaut 1−2·poids². | CONFIRMÉE (domaine: 2≤n+k) | AJOUT | 2 |
| `grammarWeightReal_sq_eq_zero_or_one` (l.85) | Le poids réel au carré vaut 0 ou 1. | CONFIRMÉE | AJOUT | 0 |
| `common_sub_orderQ_eq_two_changeSquare` (l.113) | Identité finie C−Q = 2V (sommes pondérées commune, ordre-Q, variation quadratique). | CONFIRMÉE (domaine: 2≤n) | AJOUT | 2 |
| `totalOccupancy_mod_two` (l.133) | Une paire réfléchie préserve exactement la parité de l'occupation totale. | CONFIRMÉE | AJOUT | 1 |
| `totalOccupancy_sub_line` (l.139) | L'occupation totale excède l'occupation de ligne de 2×(nombre de paires hors ligne). | CONFIRMÉE | V63 | 0 |
| `one_reflected_pair_adds_two` (l.146) | Une paire réfléchie ajoute 2 à l'occupation totale. | CONFIRMÉE | V63 | 0 |
| `one_reflected_pair_parity_invisible` (l.151) | Une injection d'une paire est invisible à la parité. | CONFIRMÉE | AJOUT | 0 |
| `binary_transition_product_eq_one_sub_two_sq` (l.158) | Version entière abstraite : a²=1, b²=1, b−a=2w ⟹ ab = 1−2w². | CONFIRMÉE (domaine: a²=1, b²=1, b−a=2w ) | AJOUT | 0 |
| `finite_common_sub_adjacent_eq_two_variation` (l.167) | Forme finie générique : somme des poids − somme q·poids = 2·somme w²·poids si q=1−2w². | CONFIRMÉE (domaine: q i = 1−2 w i² sur s ) | AJOUT | 0 |
| `total_line_lift_step_gap` (l.186) | Forme entière : cTotal = cLine+2·paires ⟹ écart de pas 2·paires. | CONFIRMÉE (domaine: cTotal=cLine+2·offlinePairs ) | AJOUT | 0 |
| `total_line_same_parity` (l.193) | cTotal = cLine+2·paires ⟹ mêmes parités. | CONFIRMÉE (domaine: cTotal=cLine+2·offlinePairs ) | AJOUT | 0 |
| `finite_total_line_lift_gap` (l.200) | Identité finie cumulée de l'écart de relèvement total/ligne. | CONFIRMÉE (domaine: cTotal i = cLine i + 2·offlinePairs i sur s ) | AJOUT | 0 |
| `discreteArgumentLift_step` (l.224) | Si le compteur gagne c et l'indice de cellule de phase gagne 1, le relèvement gagne c−1. | CONFIRMÉE (domaine: Nnext=N+c ) | AJOUT | 1 |
| `discreteArgumentLift_total_sub_line` (l.233) | À même indice de phase, différence de relèvements = différence de comptages. | CONFIRMÉE | AJOUT | 1 |
| `discreteArgumentLift_gap_eq_two_w` (l.240) | Si N−N0=2W, alors la différence de relèvements vaut 2W. | CONFIRMÉE (domaine: N−N0=2W ) | AJOUT | 1 |
| `two_w_ge_two_of_one_le` (l.247) | W≥1 entraîne 2W≥2. | CONFIRMÉE (domaine: W≥1 ) | AJOUT | 1 |

### `Round26CIGrammarQAdapter`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `grammarWeight_sq_eq_changeIndicator` (l.23) | Le carré du poids grammatical est l'indicateur de changement. | CONFIRMÉE (domaine: 2≤n+k) | AJOUT | 2 |
| `grammarAdjacentSign_eq_one_sub_two_weight_sq` (l.41) | Le signe adjacent vaut 1−2·poids². | CONFIRMÉE (domaine: 2≤n+k) | AJOUT | 1 |
| `grammarAdjacentSign_eq_one_of_family_zero` (l.48) | Une colonne de famille 0 donne le signe +1. | CONFIRMÉE (domaine: gnat(n+k) ≡ 0 mod 6 ) | AJOUT | 0 |
| `grammarAdjacentSign_eq_neg_one_of_family_two` (l.54) | Une colonne de famille 2 donne le signe −1. | CONFIRMÉE (domaine: gnat(n+k) ≡ 2 mod 6 ) | AJOUT | 0 |
| `grammarAdjacentSign_eq_neg_one_of_family_four` (l.61) | Une colonne de famille 4 donne le signe −1. | CONFIRMÉE (domaine: gnat(n+k) ≡ 4 mod 6 ) | AJOUT | 0 |

### `Round26CJTwoLockConcreteCertification`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `certification_prime_block_values` (l.26) | Les premiers p2..p9 valent [5,7,11,13,17,19,23,29]. | CONFIRMÉE | V13 | 0 |
| `certification_prime_block_gaps` (l.31) | Les écarts gnat 2..8 valent [2,4,2,4,2,4,6]. | CONFIRMÉE | V174 | 0 |
| `certification_prime_block_families` (l.37) | Les familles gnat 2..8 mod 6 valent [2,4,2,4,2,4,0]. | CONFIRMÉE | V174 | 0 |
| `certification_change_indicator_block` (l.44) | Les indicateurs de changement (2,0..6) valent [1,1,1,1,1,1,0]. | CONFIRMÉE | AJOUT | 0 |
| `certification_adjacent_sign_block` (l.53) | Les signes adjacents (2,0..6) valent [−1,−1,−1,−1,−1,−1,1]. | CONFIRMÉE | AJOUT | 0 |
| `certification_adjacentSign_cast_eq_sign_product` (l.64) | Le signe adjacent (casté) égale le produit des signes grammaticaux consécutifs. | CONFIRMÉE (domaine: 2≤n+k) | AJOUT | 1 |
| `certification_numeric_real_prime_block_C` (l.78) | Somme commune du bloc de certification (7 colonnes) = 28. | CONFIRMÉE | AJOUT | 1 |
| `certification_numeric_real_prime_block_V` (l.83) | Somme de variation quadratique du bloc = 21. | CONFIRMÉE | AJOUT | 1 |
| `certification_numeric_real_prime_block_Q` (l.90) | Somme ordre-Q du bloc = −14. | CONFIRMÉE | AJOUT | 1 |
| `certification_numeric_real_prime_block_C_sub_Q` (l.97) | C−Q = 42 sur le bloc. | CONFIRMÉE | AJOUT | 0 |
| `certification_numeric_real_prime_block_twoV` (l.103) | 2V = 42 sur le bloc. | CONFIRMÉE | AJOUT | 0 |
| `certification_numeric_real_prime_block_C_sub_Q_eq_twoV` (l.108) | C−Q = 2V sur le bloc de certification. | CONFIRMÉE | AJOUT | 0 |
| `certification_totalOccupancy_three_two` (l.116) | totalOccupancy 3 2 = 7. | CONFIRMÉE | AJOUT | 0 |
| `certification_lift_total_521_500` (l.120) | discreteArgumentLift 521 500 = 20. | CONFIRMÉE | AJOUT | 0 |
| `certification_lift_line_519_500` (l.124) | discreteArgumentLift 519 500 = 18. | CONFIRMÉE | AJOUT | 0 |
| `certification_lift_gap` (l.128) | Écart de relèvement 521/519 à l'indice 500 = 2. | CONFIRMÉE | AJOUT | 0 |
| `certification_two_member_cell_step_lift` (l.132) | Relèvement de pas (521,501) moins (519,500) = 1. | CONFIRMÉE | AJOUT | 0 |
| `certification_finite_three_cell_total_line_defect` (l.153) | Défaut total moins ligne sur trois cellules certifiées = 2. | CONFIRMÉE | AJOUT | 0 |
| `certification_finite_three_cell_total_line_defect_eq_two_offline` (l.157) | Ce défaut vaut 2×(somme des paires hors ligne certifiées). | CONFIRMÉE | AJOUT | 0 |

### `Round26CKGapResidueQClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `gapResidue_polynomial_eq_eight_changeIndicator` (l.25) | Pour n+k≥2, r(6−r) = 8·indicateur de changement, r le résidu d'écart mod 6. | CONFIRMÉE (domaine: 2≤n+k) | V174 | 0 |
| `grammarAdjacentSign_eq_gapResidueCode` (l.50) | Le signe adjacent vaut +1 si gnat(n+k) ≡ 0 mod 6, sinon −1. | CONFIRMÉE | V174 | 1 |
| `orderQWeightedSum_eq_gapDerived` (l.64) | Le canal ordre-Q égale la fonctionnelle dérivée directe des résidus d'écarts ordonnés. | CONFIRMÉE (domaine: 2≤n) | AJOUT | 0 |
| `changeSquareWeightedSum_eq_indicatorWeightedSum` (l.81) | Le canal de variation quadratique égale la somme pondérée des indicateurs de changement. | CONFIRMÉE (domaine: 2≤n) | AJOUT | 1 |
| `common_sub_orderQ_eq_two_changeIndicatorWeightedSum` (l.95) | C−Q = 2 fois la somme pondérée des indicateurs de changement. | CONFIRMÉE (domaine: 2≤n) | AJOUT | 0 |

### `Round26CLMonotoneDefectGate`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `monotone_positive_defect_forces_linear_cumulative_lower_bound` (l.32) | Pour un défaut entier monotone positif en n0, la somme cumulée 2W sur L cellules est ≥ 2L. | CONFIRMÉE (domaine: W monotone et W n0 ≥ 1 ) | AJOUT | 2 |
| `strict_cumulative_upper_forces_zero_at_start` (l.48) | Une borne cumulée stricte < 2L force W n0 = 0. | CONFIRMÉE (domaine: W monotone et somme cumulée < 2L ) | AJOUT | 1 |
| `strict_cumulative_certificate_iff_zero_defect` (l.62) | Pour W monotone, défaut nul partout ⟺ tout départ a une fenêtre à somme cumulée < 2L. | CONFIRMÉE (domaine: W monotone ) | AJOUT | 0 |

### `Round26CMRightHalfDefectBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `rightHalfPositiveZeros_finite` (l.38) | Le rectangle de demi-plan droit strict de hauteur positive est fini. | CONFIRMÉE | V6 | 19 |
| `rightHalfPositiveZero_order_pos` (l.51) | Tout membre de ce rectangle a un ordre analytique strictement positif. | CONFIRMÉE | V12 | 9 |
| `nprime_half_eq_finite_order_sum` (l.59) | N'(1/2,T) est la somme finie des ordres des zéros du rectangle droit. | CONFIRMÉE | AJOUT | 5 |
| `nprime_half_nonneg` (l.76) | Le compteur N'(1/2,T) est ≥ 0. | CONFIRMÉE | AJOUT | 1 |
| `nprime_half_eq_zero_iff_isEmpty` (l.88) | N'(1/2,T)=0 ⟺ le rectangle droit est vide. | CONFIRMÉE | AJOUT | 3 |
| `offline_positive_zero_yields_rightHalf` (l.128) | Tout zéro non trivial hors ligne de hauteur 0<Im<T a un représentant dans le rectangle de demi-plan droit strict (lui-même ou son réfléchi-conjugué). | CONFIRMÉE SOUS CONDITION (zéro non trivial hors ligne, 0<Im ρ<T) | V62,V65 | 3 |
| `rightHalf_isEmpty_iff_bounded_critical_line` (l.153) | Le rectangle droit est vide ⟺ tout zéro non trivial de 0<Im<T a re=1/2. | CONFIRMÉE | V126 | 2 |
| `nprime_half_eq_zero_iff_bounded_critical_line` (l.175) | N'(1/2,T)=0 ⟺ tout zéro non trivial de 0<Im<T a re=1/2. | CONFIRMÉE | V126 | 1 |
| `rightHalfMultiplicityNat_cast_eq_nprime_half` (l.191) | L'enveloppe naturelle rightHalfMultiplicityNat T est le compteur N'(1/2,T). | CONFIRMÉE | AJOUT | 2 |
| `rightHalfPositiveZerosFinset_mono` (l.206) | Le support de hauteur stricte du demi-plan droit est monotone en T. | CONFIRMÉE (domaine: T ≤ U ) | AJOUT | 1 |
| `rightHalfMultiplicityNat_mono` (l.219) | La multiplicité naturelle du demi-plan droit est monotone en la coupure. | CONFIRMÉE (domaine: T ≤ U ) | AJOUT | 2 |
| `rightHalfMultiplicityNat_natHeight_monotone` (l.228) | La suite n ↦ rightHalfMultiplicityNat n est monotone. | CONFIRMÉE | AJOUT | 1 |
| `nprime_natHeight_positive_forces_linear_cumulative_lower_bound` (l.234) | Si le défaut du demi-plan droit est ≥1 à n0, la somme cumulée 2·défaut sur L hauteurs entières est ≥ 2L. | CONFIRMÉE (domaine: rightHalfMultiplicityNat n0 ≥ 1 ) | AJOUT | 0 |

### `Round26CNRightHalfRectangleIdentity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `_private.RhGapCriterion.Round26CNRightHalfRectangleIdentity.0.RhGap.finite_real_finset_enclosed_in_Ioo` (l.35) | Un ensemble fini de réels dans ]a,b[ est inclus dans un ]l,r[ strictement intérieur. [terme hors maître] | CONFIRMÉE (domaine: a<b et tous les éléments dans ]a,b[ ) | AJOUT | 1 |
| `RightHalfPaddedRectangle.sigmaL_gt_half` (l.69) | Le rectangle rembourré a sigmaL > 1/2. | CONFIRMÉE | AJOUT | 2 |
| `RightHalfPaddedRectangle.sigmaL_lt_sigmaR` (l.70) | Le rectangle rembourré a sigmaL < sigmaR. | CONFIRMÉE | AJOUT | 1 |
| `RightHalfPaddedRectangle.sigmaR_lt_one` (l.71) | Le rectangle rembourré a sigmaR < 1. | CONFIRMÉE | AJOUT | 0 |
| `RightHalfPaddedRectangle.t0_pos` (l.72) | Le rectangle rembourré a t0 > 0. | CONFIRMÉE | AJOUT | 1 |
| `RightHalfPaddedRectangle.t0_lt_t1` (l.73) | Le rectangle rembourré a t0 < t1. | CONFIRMÉE | AJOUT | 1 |
| `RightHalfPaddedRectangle.t1_lt_T` (l.74) | Le rectangle rembourré a t1 < T. | CONFIRMÉE | AJOUT | 0 |
| `RightHalfPaddedRectangle.support_strict` (l.75) | Tout zéro du support droit est strictement à l'intérieur du rectangle rembourré. | CONFIRMÉE | AJOUT | 3 |
| `RightHalfPaddedRectangle.rect_zero_mem_support` (l.78) | Tout zéro de zêta dans le rectangle fermé rembourré appartient au support droit. | CONFIRMÉE SOUS CONDITION (ρ dans le rectangle fermé et zêta ρ=0) | AJOUT | 1 |
| `RightHalfPaddedRectangle.lowerLeft_re` (l.90) | La partie réelle du coin bas-gauche vaut sigmaL. | CONFIRMÉE | AJOUT | 4 |
| `RightHalfPaddedRectangle.lowerLeft_im` (l.94) | La partie imaginaire du coin bas-gauche vaut t0. | CONFIRMÉE | AJOUT | 3 |
| `RightHalfPaddedRectangle.upperRight_re` (l.98) | La partie réelle du coin haut-droit vaut sigmaR. | CONFIRMÉE | AJOUT | 3 |
| `RightHalfPaddedRectangle.upperRight_im` (l.102) | La partie imaginaire du coin haut-droit vaut t1. | CONFIRMÉE | AJOUT | 3 |
| `RightHalfPaddedRectangle.re_le` (l.106) | re du coin bas-gauche ≤ re du coin haut-droit. | CONFIRMÉE | AJOUT | 5 |
| `RightHalfPaddedRectangle.im_le` (l.110) | im du coin bas-gauche ≤ im du coin haut-droit. | CONFIRMÉE | AJOUT | 5 |
| `exists_rightHalfPaddedRectangle` (l.116) | Pour T>0 il existe un rectangle rembourré strictement intérieur au support droit. | CONFIRMÉE (domaine: 0<T) | AJOUT | 2 |
| `_private.RhGapCriterion.Round26CNRightHalfRectangleIdentity.0.RhGap.rightHalf_zero_nontrivial` (l.158) | Tout zéro du support droit est un zéro non trivial. | CONFIRMÉE | V6,V7 | 2 |
| `rightHalfPaddedRectangle_support_not_boundary` (l.166) | Aucun zéro du support droit n'est sur le bord du rectangle. | CONFIRMÉE | AJOUT | 2 |
| `rightHalfPaddedRectangle_negLogDeriv_poleSet_eq` (l.187) | L'ensemble des pôles de −ζ'/ζ dans le rectangle est le support droit. | CONFIRMÉE | AJOUT | 3 |
| `rightHalfPaddedRectangle_no_negLogDeriv_poles_on_boundary` (l.216) | Le bord du rectangle ne rencontre aucun pôle de −ζ'/ζ. | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.Round26CNRightHalfRectangleIdentity.0.RhGap.sumResiduesIn_negLogDeriv_rightHalf_eq_neg_nprime` (l.229) | La somme des résidus de −ζ'/ζ sur le support droit vaut −N'(1/2,T). | CONFIRMÉE | AJOUT | 1 |
| `rightHalf_rectangle_argument_principle_identity` (l.269) | L'intégrale de −ζ'/ζ sur le rectangle rembourré vaut −N'(1/2,T) (principe de l'argument). | CONFIRMÉE | AJOUT | 4 |
| `_private.RhGapCriterion.Round26CNRightHalfRectangleIdentity.0.RhGap.weighted_order_eq_negLogDeriv_order_of_half_lt_re` (l.292) | Pour re s>1/2, l'ordre méromorphe de la version pondérée égale celui de −ζ'/ζ. | CONFIRMÉE (domaine: re s > 1/2 ) | AJOUT | 2 |
| `rightHalfPaddedRectangle_weighted_poleSet_eq` (l.317) | L'ensemble des pôles de la version pondérée est le support droit. | CONFIRMÉE | AJOUT | 2 |
| `rightHalfPaddedRectangle_no_weighted_poles_on_boundary` (l.347) | Le bord du rectangle ne rencontre aucun pôle pondéré. | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.Round26CNRightHalfRectangleIdentity.0.RhGap.weighted_hasSimplePolesOn_rectangle` (l.360) | La fonction pondérée a des pôles simples sur le rectangle. | CONFIRMÉE | AJOUT | 1 |
| `residue_weightedRightHalfNegLogDeriv_zero` (l.370) | En un zéro ρ de zêta, le résidu pondéré vaut −(multiplicité)·(ρ−1/2). | CONFIRMÉE (domaine: zêta ρ=0 ) | AJOUT | 1 |
| `_private.RhGapCriterion.Round26CNRightHalfRectangleIdentity.0.RhGap.sumResiduesIn_weighted_rightHalf_eq` (l.390) | La somme des résidus pondérés sur le support droit vaut −Σ ordre·(ρ−1/2). | CONFIRMÉE | AJOUT | 1 |
| `rightHalf_weighted_rectangle_complex_identity` (l.436) | L'intégrale pondérée sur le rectangle vaut −Σ ordre·(ρ−1/2). | CONFIRMÉE | AJOUT | 1 |
| `rightHalf_weighted_zeroes_sum_eq_finite_sum` (l.462) | La somme des (re ρ−1/2) sur les zéros de ]1/2,1[×]0,T[ égale la somme finie sur le support droit. | CONFIRMÉE | AJOUT | 6 |
| `rightHalf_weighted_rectangle_real_identity` (l.480) | −Re(intégrale pondérée) = Σ (re ρ−1/2) sur les zéros du rectangle droit. | CONFIRMÉE | AJOUT | 3 |
| `rightHalf_weighted_defect_nonneg` (l.492) | La somme pondérée Σ(re ρ−1/2) sur le rectangle droit est ≥ 0. | CONFIRMÉE | AJOUT | 2 |
| `rightHalf_weighted_defect_eq_zero_iff_isEmpty` (l.507) | La somme pondérée droite est nulle ⟺ le support droit est vide. | CONFIRMÉE | V126 | 3 |

### `Round26COPrimeHarmonicBoundaryReduction`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `rightHalf_weighted_rectangle_vanishing_iff_bounded_critical_line` (l.30) | Annulation du bord pondéré droit ⟺ tout zéro non trivial de 0<Im<T a re=1/2. | CONFIRMÉE | V126 | 0 |
| `primePowerCorrectionMellin_eq_integral` (l.57) | La transformée de Mellin de la correction psi−theta est l'intégrale sur ]1,∞[ de (psi−theta)(x)·x^(−s−1). [terme hors maître] | CONFIRMÉE | V121 | 0 |
| `primePowerCorrectionMellinIntegrand_aestronglyMeasurable_restrict_Ioi_one` (l.65) | L'intégrande de Mellin de la correction est mesurable p.p. sur ]1,∞[. | CONFIRMÉE | AJOUT | 2 |
| `abs_thetaPsiPrimePowerCorrection_le` (l.86) | Pour x>1, la valeur absolue de la correction est ≤ 2√x·log x. | CONFIRMÉE (domaine: x>1 ) | AJOUT | 2 |
| `primePowerCorrectionMellin_integrableOn_re_gt_half` (l.96) | Pour re s>1/2, l'intégrande de Mellin de la correction est intégrable sur ]1,∞[. | CONFIRMÉE (domaine: re s > 1/2 ) | AJOUT | 2 |
| `primePowerCorrectionMellinDeriv_aestronglyMeasurable_restrict_Ioi_one` (l.167) | L'intégrande dérivé est mesurable p.p. sur ]1,∞[. | CONFIRMÉE | AJOUT | 1 |
| `hasDerivAt_primePowerCorrectionMellin_integrand` (l.197) | Pour x>0, la dérivée en s de correction·x^(−s−1) est correction·x^(−s−1)·log x·(−1). | CONFIRMÉE (domaine: 0<x) | AJOUT | 1 |
| `_private.RhGapCriterion.Round26COPrimeHarmonicBoundaryReduction.0.RhGap.co_ae_on_Ioi_one_of_all` (l.206) | Une propriété vraie partout sur ]1,∞[ l'est p.p. | CONFIRMÉE (domaine: ∀x∈]1,∞[, p x ) | AJOUT | 1 |
| `_private.RhGapCriterion.Round26COPrimeHarmonicBoundaryReduction.0.RhGap.co_dist_lt_of_mem_ball_half` (l.212) | Si z est dans la boule de rayon δ/2 autour de s (δ>0), dist z s < δ. | CONFIRMÉE (domaine: δ>0 ) | AJOUT | 1 |
| `analyticAt_primePowerCorrectionMellin` (l.217) | Pour re s>1/2, la Mellin de la correction est analytique en s. | CONFIRMÉE (domaine: re s > 1/2 ) | AJOUT | 2 |
| `primePowerCorrectionMellin_analyticOn_right_half_plane` (l.404) | La Mellin de la correction est analytique sur re s>1/2. | CONFIRMÉE | AJOUT | 0 |
| `four_grammar_sector_prime_dirichlet_recomposition_re_gt_one` (l.411) | Pour re s>1, la somme des quatre secteurs de Dirichlet premier-grammaire égale la série de Dirichlet première. | CONFIRMÉE (domaine: re s > 1 ) | AJOUT | 2 |

### `Round26CPPrimeChannelPoleIsolation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `primeGrammarChannelContinuation_eq` (l.34) | La continuation du canal premier vaut −ζ'/ζ(s) − s·Mellin de la correction (définitionnel). | CONFIRMÉE | AJOUT | 3 |
| `analyticAt_primePowerCorrectionTerm` (l.40) | Pour re s>1/2, z·Mellin(z) est analytique en s. | CONFIRMÉE (domaine: re s > 1/2 ) | AJOUT | 7 |
| `meromorphicAt_primeGrammarChannelContinuation` (l.46) | Pour re s>1/2, la continuation du canal est méromorphe en s. | CONFIRMÉE (domaine: re s > 1/2 ) | AJOUT | 1 |
| `meromorphicOrderAt_primeGrammarChannelContinuation_zero` (l.60) | En tout zéro de zêta avec re ρ>1/2, la continuation du canal a ordre méromorphe −1 (pôle simple non annulé). | CONFIRMÉE SOUS CONDITION (zêta ρ=0 et re ρ>1/2) | V126 | 6 |

### `Round26CQThetaPrimeDirichletBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `hasSum_primeThetaMellinValueTerm` (l.34) | Pour x≥0, la somme sur q des termes de Mellin indexés par valeur vaut θ(x)·x^(−s−1). | CONFIRMÉE (domaine: 0≤x ) | V121 | 1 |
| `prime_indicator_dirichlet_term_at_p` (l.84) | Le terme de Dirichlet indexé par valeur en p n égale le poids de Dirichlet premier canonique n. | CONFIRMÉE | AJOUT | 0 |
| `prime_indicator_dirichlet_term_of_not_prime` (l.95) | Un entier non premier contribue 0 au canal de Dirichlet premier indexé par valeur. | CONFIRMÉE (domaine: q non premier ) | AJOUT | 0 |
| `prime_enumeration_dirichlet_reindexing` (l.105) | Pour re s>1, la série de Dirichlet premier indexée par valeur égale la série sur la suite canonique des premiers. | CONFIRMÉE (domaine: re s > 1 ) | V13,V48 | 1 |

### `Round26CRThetaL1Completion`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `primeThetaMellinValueTerm_integrableOn` (l.22) | Pour re s>1, chaque terme de Mellin indexé par valeur est intégrable sur ]1,∞[. | CONFIRMÉE (domaine: re s > 1 ) | AJOUT | 1 |
| `integral_primeThetaMellinValueTerm` (l.47) | Pour re s>1, l'intégrale du terme q vaut log q·primeIndicator q·q^(−s)/s. | CONFIRMÉE (domaine: re s > 1 ) | AJOUT | 1 |
| `norm_log_mul_primeIndicator_le_vonMangoldt` (l.83) | La norme de log q·primeIndicator q est ≤ Λ(q) (Von Mangoldt). | CONFIRMÉE | V48 | 1 |
| `norm_primeThetaMellinValueTerm` (l.95) | Pour x>0, la norme du terme vaut (log q·primeIndicator q)·x^(−re s−1) si q≤x, sinon 0. | CONFIRMÉE (domaine: 0<x ) | AJOUT | 1 |
| `integral_norm_primeThetaMellinValueTerm` (l.108) | Pour re s>1, l'intégrale de la norme du terme vaut norm(log q·primeIndicator q)·max(q,1)^(−re s)/re s. | CONFIRMÉE (domaine: re s > 1 ) | AJOUT | 1 |
| `primeTheta_integral_norm_bound_by_vonMangoldt_LSeries_norm` (l.150) | Pour re s>1, l'intégrale de la norme du terme q est majorée par la norme du terme q de la L-série de Von Mangoldt sur re s, divisée par re s. | CONFIRMÉE (domaine: re s > 1 ) | V48 | 1 |
| `summable_integral_norm_primeThetaMellinValueTerm` (l.190) | Pour re s>1, la suite q ↦ intégrale de la norme du terme de Mellin est sommable. | CONFIRMÉE (domaine: re s > 1 ) | AJOUT | 1 |

### `Round26CSThetaMellinBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `thetaMellin_eq_primeDirichlet` (l.25) | Pour re s>1, la Mellin de theta vaut la série de Dirichlet première divisée par s. [terme hors maître] | CONFIRMÉE (domaine: re s > 1 ) | V121,V48 | 1 |

### `Round26CTPrimeChannelCore`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `thetaMellinIntegrand_aestronglyMeasurable_restrict_Ioi_one` (l.22) | L'intégrande theta(x)·x^(−s−1) est mesurable p.p. sur ]1,∞[. | CONFIRMÉE | AJOUT | 1 |
| `thetaMellin_integrableOn_re_gt_one` (l.43) | Pour re s>1, theta(x)·x^(−s−1) est intégrable sur ]1,∞[. | CONFIRMÉE (domaine: re s > 1 ) | AJOUT | 1 |
| `psiMellin_eq_thetaMellin_add_primePowerCorrection` (l.91) | Pour re s>1, l'intégrale de psi(x)·x^(−s−1) vaut Mellin de theta plus Mellin de la correction de puissances premières. | CONFIRMÉE (domaine: re s > 1 ) | V121 | 1 |

### `Round26CUPrimeChannelCompletion`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `negLogDerivRiemannZeta_eq_primeDirichlet_add_correction` (l.21) | Pour re s>1, −ζ'/ζ(s) = série de Dirichlet première + s·Mellin de la correction. | CONFIRMÉE (domaine: re s > 1 ) | V121,V48 | 1 |
| `primeGrammarChannelContinuation_eq_fourGrammarSectors` (l.43) | Pour re s>1, la continuation du canal premier égale la somme des quatre secteurs de Dirichlet premier-grammaire. | CONFIRMÉE (domaine: re s > 1 ) | V174 | 2 |
| `analytic_primeGrammarChannel_impossible_at_right_zero` (l.53) | Si ζ(ρ)=0 avec re ρ>1/2, la continuation du canal premier ne peut pas être analytique en ρ. | CONFIRMÉE SOUS CONDITION (ζ(ρ)=0, re ρ>1/2 et analytique en ρ) | V126 | 1 |

### `Round26CVMoebiusTowerNoGo`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `analyticAt_negLogDerivRiemannZeta_scaled` (l.40) | Pour m≥2 et re s>1/2, z ↦ −ζ'/ζ(m·z) est analytique en s. [terme hors maître] | CONFIRMÉE (domaine: m≥2, re s>1/2 ) | AJOUT | 1 |
| `analyticAt_moebiusTowerFiniteTail` (l.76) | Toute somme finie pondérée de planchers m≥2 est analytique en tout s de re>1/2. | CONFIRMÉE (domaine: tous les m de F ≥ 2, re s > 1/2 ) | AJOUT | 2 |
| `meromorphicOrderAt_moebiusTower_zero` (l.102) | Au zéro hypothétique ρ (re>1/2), aucune combinaison finie de planchers m≥2 ne retire le pôle simple : ordre méromorphe −1. | CONFIRMÉE SOUS CONDITION (ζ(ρ)=0, re ρ>1/2, indices de F ≥ 2 (no-go)) | V126 | 0 |
| `meromorphicOrderAt_moebiusTower_sub_primePowerCorrection_zero` (l.142) | Même no-go avec le plancher m=1 remplacé par la continuation du canal premier : ordre −1 en ρ. | CONFIRMÉE SOUS CONDITION (ζ(ρ)=0, re ρ>1/2, indices de F ≥ 2) | V126 | 0 |

### `Round26CWTowerContactRigidity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `hasDerivAt_towerMode` (l.94) | Dérivée en u du mode de Tour d'étage m : formule explicite en A, β, γ, φ. [terme hors maître] | CONFIRMÉE SOUS CONDITION (domaine: m>0) | V16 | 1 |
| `abs_deriv_towerMode_at_contact` (l.117) | Aux contacts (cos=0), la valeur absolue de la dérivée du mode vaut  A ·( γ /m)·exp((β−1/2)u/m). | CONFIRMÉE (domaine: m>0 et cos(γu/m+φ)=0 (contact) ) | V20,V45 | 1 |
| `contact_succ` (l.144) | Si u est un contact, u+π·m/γ en est un aussi (contact suivant). | CONFIRMÉE (domaine: m>0, γ≠0, u contact ) | V23 | 1 |
| `contact_slope_ratio_eq_contactRatio` (l.154) | Le rapport des exponentielles aux deux contacts consécutifs égale contactRatio β γ. | CONFIRMÉE (domaine: m>0, γ≠0 ) | V45 | 1 |
| `contactRatio_eq_one_iff` (l.166) | Pour γ≠0, contactRatio β γ = 1 ⟺ β = 1/2. | CONFIRMÉE (domaine: γ≠0 ) | V45,V161 | 6 |
| `contactRatio_reflect_mul` (l.187) | contactRatio β γ · contactRatio (1−β) γ = 1. | CONFIRMÉE | V35,V65 | 2 |
| `contactRatio_pos` (l.195) | contactRatio β γ > 0. | CONFIRMÉE | AJOUT | 1 |
| `contactRatio_symmetric_defect_pos` (l.198) | Pour γ≠0 et β≠1/2, contactRatio β γ + contactRatio (1−β) γ > 2. | CONFIRMÉE SOUS CONDITION (γ≠0, β≠1/2 (hors ligne)) | V162,V167 | 0 |
| `contactRatio_eq_one_iff_cayley_unit` (l.222) | Pour γ≠0, contactRatio β γ = 1 ⟺ β²+γ² = (β−1)²+γ². [terme hors maître] | CONFIRMÉE (domaine: γ≠0 ) | AJOUT | 0 |
| `cayley_multiplier_tower_invariant` (l.226) | Le multiplicateur de Cayley −(mρ/m)/((mρ/m)−1) est indépendant de l'étage m. | CONFIRMÉE (domaine: m>0 ) | AJOUT | 0 |
| `cross_cycle_sum_eq_two` (l.234) | grammarCrossV2(1,5)+grammarCrossV2(5,1)=2. | CONFIRMÉE | AJOUT | 1 |
| `coboundary_cycle_sum_eq_zero` (l.238) | Pour tout potentiel psi, psi5−psi1+(psi1−psi5)=0. | CONFIRMÉE | AJOUT | 1 |
| `cross_not_coboundary` (l.242) | Aucun potentiel psi ne représente le canal croisé comme cobord (obstruction de cocycle). | RÉFUTATION COMPILÉE | AJOUT | 4 |
| `contact_slope_ratio_towerMode` (l.255) | Le rapport des  dérivées  du mode aux deux contacts consécutifs vaut contactRatio, indépendant de m. | CONFIRMÉE (domaine: m>0, γ≠0, A≠0, u contact ) | V45 | 2 |
| `contact_slope_ratio_floor_independent` (l.274) | Le rapport de pentes aux deux contacts est identique pour tous les étages. | CONFIRMÉE (domaine: m,m'>0, γ≠0, A≠0, contacts aux deux étages ) | V45 | 0 |
| `contact_slope_ratio_eq_one_iff_critical_line` (l.289) | Le rapport de pentes aux deux contacts vaut 1 ⟺ β=1/2. | CONFIRMÉE (domaine: m>0, γ≠0, A≠0, u contact ) | V45,V161 | 0 |

### `Round26CXTowerCarrierBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `towerMode_floor_eq_base_dilation` (l.62) | Le mode d'étage m est le mode de base (m=1) évalué à u/m. | CONFIRMÉE (domaine: m>0 ) | AJOUT | 2 |
| `towerMode_eq_normalized_zeroRow` (l.77) | Le mode de base à amplitude ‖C‖, plancher re ρ, hauteur Im ρ, phase arg C est la partie réelle du terme de Perron du zéro divisée par exp(u/2). | CONFIRMÉE | V100,V16 | 1 |
| `zeroRow_contactRatio_eq_one_iff_critical_line` (l.128) | Pour tout zéro non trivial, contactRatio(re,im)=1 ⟺ re=1/2. | CONFIRMÉE | V45,V161 | 0 |
| `zeroRow_contactRatio_reflect_mul` (l.137) | Pour tout zéro non trivial, contactRatio(re,im)·contactRatio(1−re,im)=1. | CONFIRMÉE | V35,V65 | 0 |

### `Round26CYCoboundaryLogBound`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `grammarPotentialV2_prime_eq_zero_or_one` (l.55) | Le potentiel grammatical en p n mod 6 vaut 0 ou 1. | CONFIRMÉE | V174 | 3 |
| `log_p_monotone` (l.67) | log p n est monotone. | CONFIRMÉE (domaine: m ≤ n ) | AJOUT | 3 |
| `log_p_nonneg` (l.77) | log p n ≥ 0. | CONFIRMÉE | AJOUT | 10 |
| `_private.RhGapCriterion.Round26CYCoboundaryLogBound.0.RhGap.telescope_log_p` (l.85) | Pour N≥3, somme télescopique des log p k − log p(k−1) sur [3,N) = log p(N−1) − log p 2. | CONFIRMÉE (domaine: 3≤N ) | AJOUT | 1 |
| `weighted_grammar_coboundary_sum_by_parts` (l.103) | Sommation par parties de la somme pondérée du cobord grammatical par log p n. | CONFIRMÉE (domaine: 3≤N ) | AJOUT | 3 |
| `abs_weighted_grammar_coboundary_le_two_log_p` (l.126) | Pour N≥3, la valeur absolue de la somme pondérée du cobord est ≤ 2 log p N. | CONFIRMÉE (domaine: 3≤N ) | AJOUT | 1 |
| `abs_tau15_sub_tau51_weighted_le_two_log_p` (l.199) | Pour N≥3, la valeur absolue de Σ(tau15−tau51)·log p n est ≤ 2 log p N. | CONFIRMÉE (domaine: 3≤N ) | AJOUT | 0 |

### `Round26CZTowerGeometry`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `towerPoint_im` (l.89) | Im(ρ/m) = Im ρ / m. | CONFIRMÉE (domaine: m>0 ) | AJOUT | 0 |
| `towerPoint_re` (l.93) | Re(ρ/m) = Re ρ / m. | CONFIRMÉE (domaine: m>0 ) | AJOUT | 2 |
| `towerPoint_defect_eq_scaled` (l.97) | Le défaut hors ligne à l'étage m, mesuré à la droite 1/(2m), vaut (re ρ − 1/2)/m. | CONFIRMÉE (domaine: m>0 ) | AJOUT | 1 |
| `towerPoint_on_floor_line_iff` (l.105) | ρ/m est sur la droite de son étage ⟺ re ρ = 1/2. | CONFIRMÉE (domaine: m>0 ) | V161 | 0 |
| `towerPoint_re_lt_half_of_two_le` (l.121) | Pour un zéro non trivial et m≥2, Re(ρ/m) < 1/2 strictement (la tour n'offre aucun second contact avec Re=1/2). | CONFIRMÉE (domaine: m≥2 ) | AJOUT | 0 |
| `primeCarrier_dilationCovariant` (l.150) | Le porteur premier est covariant par dilatation. | CONFIRMÉE | AJOUT | 1 |
| `towerMode_dilationCovariant` (l.157) | La famille towerMode est covariante par dilatation. | CONFIRMÉE | AJOUT | 1 |
| `psi_eq_sum_theta_dilations` (l.168) | Pour x≥1, psi(x) = Σ_{n=1}^{⌊log x/log 2⌋} theta(x^(1/n)). | CONFIRMÉE (domaine: x≥1 ) | V121 | 0 |

### `Round26DAContactDefectWelding`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `_private.RhGapCriterion.Round26DAContactDefectWelding.0.RhGap.telescope_log_p_da` (l.73) | Pour N≥3, somme télescopique des log p k − log p(k−1) = log p(N−1) − log p 2. | CONFIRMÉE (domaine: 3≤N ) | AJOUT | 1 |
| `_private.RhGapCriterion.Round26DAContactDefectWelding.0.RhGap.telescope_log_p_da_neg` (l.89) | Pour N≥3, somme des log p(k−1) − log p k = log p 2 − log p(N−1). | CONFIRMÉE (domaine: 3≤N ) | AJOUT | 1 |
| `weighted_grammar_coboundary_le_log_p` (l.102) | Pour N≥3, la somme pondérée du cobord est ≤ log p(N−1). | CONFIRMÉE (domaine: 3≤N ) | AJOUT | 1 |
| `neg_log_p_le_weighted_grammar_coboundary` (l.138) | Pour N≥3, −log p(N−1) ≤ somme pondérée du cobord. | CONFIRMÉE (domaine: 3≤N ) | AJOUT | 1 |
| `abs_weighted_grammar_coboundary_le_log_p` (l.181) | Pour N≥3, valeur absolue de la somme pondérée du cobord ≤ log p(N−1) (constante 1 optimale). | CONFIRMÉE (domaine: 3≤N ) | AJOUT | 1 |
| `abs_tau15_sub_tau51_weighted_le_log_p` (l.192) | Même borne optimale sur les indicateurs de secteurs tau15−tau51. | CONFIRMÉE (domaine: 3≤N ) | AJOUT | 1 |
| `re_sub_half_eq_im_div_pi_mul_log_contactRatio` (l.215) | Pour γ≠0, β−1/2 = (γ/π)·log(contactRatio β γ). | CONFIRMÉE (domaine: γ≠0 ) | V45 | 2 |
| `rightHalf_weighted_defect_eq_contactRatio_sum` (l.225) | Le défaut pondéré droit Σ(re ρ−1/2)·ordre égale Σ (im/π)·log(contactRatio)·ordre. | CONFIRMÉE | V45,V102 | 0 |
| `rightHalf_weighted_defect_eq_zero_iff_all_contactRatio_one` (l.243) | Le défaut pondéré droit est nul ⟺ tout zéro du support droit a contactRatio=1. | CONFIRMÉE | V45,V126 | 0 |

### `Round26DBCoboundaryDirichletAnalytic`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `grammarCoboundaryDirichlet_summable_re_gt_one` (l.90) | Pour re s>1, la série de Dirichlet du cobord (tau15−tau51 pondéré) est sommable. | CONFIRMÉE (domaine: re s > 1 ) | AJOUT | 1 |
| `grammarCoboundaryDirichlet_eq_sector_difference` (l.108) | Pour re s>1, la Dirichlet du cobord = secteur tau15 − secteur tau51. | CONFIRMÉE (domaine: re s > 1 ) | AJOUT | 1 |

### `Round26DCCoboundaryContinuation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `norm_cpow_neg_sub_le` (l.91) | Pour 0<x≤y et re s>0, la norme de x^(−s) − y^(−s) est ≤ ‖s‖·x^(−re s −1)·(y−x). | CONFIRMÉE (domaine: 0<x≤y, re s>0 ) | AJOUT | 4 |
| `coboundaryChannel_sum_by_parts` (l.134) | Sommation d'Abel du canal cobord en blocs [M,N). | CONFIRMÉE (domaine: M<N ) | AJOUT | 2 |

### `Round26DDCoboundaryConvergence`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `majorant_term_le_integral` (l.83) | Chaque terme majorant p^(−σ−1)·(p(n+1)−p n)·log p est dominé par 2^(σ+1) fois l'intégrale de t^(−σ−1)·log t sur l'écart premier (via Bertrand). [terme hors maître] | CONFIRMÉE SOUS CONDITION (σ>0, n≥1 (domaine)) | AJOUT | 1 |
| `integrableOn_log_mul_rpow` (l.165) | t^(−σ−1)·log t est intégrable sur ]1,∞[ pour tout σ>0. | CONFIRMÉE (domaine: σ>0 ) | AJOUT | 1 |
| `summable_coboundary_majorant` (l.219) | La série majorante p_n^(−σ−1)·(p_{n+1}−p_n)·log p_n est sommable pour tout σ>0. | CONFIRMÉE (domaine: σ>0 ) | AJOUT | 1 |

### `Round26DECoboundaryCauchy`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `daCumulativeC_eq_initial_add_Ico` (l.106) | Pour m≥2, daCumulativeC m = daCumulativeC 2 + somme sur Ico 2 m des (indicateur τ15 − τ51)·log p_n. | CONFIRMÉE (domaine: 2≤m) | AJOUT | 1 |
| `daCumulativeC_two_eq` (l.119) | daCumulativeC 2 est la somme des termes n=0 et n=1 (différence d'indicateurs × log p). | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.Round26DECoboundaryCauchy.0.RhGap.tau15_sub_tau51_abs_le_one` (l.133) | La différence des indicateurs τ15 et τ51 est bornée par 1 en valeur absolue. | CONFIRMÉE | AJOUT | 1 |
| `norm_daCumulativeC_two_le` (l.146) | ‖daCumulativeC 2‖ ≤ log 2 + log 3. | CONFIRMÉE | AJOUT | 1 |
| `norm_daCumulativeC_le` (l.187) | Pour m≥3, ‖daCumulativeC m‖ ≤ log p_{m−1} + (log 2 + log 3). | CONFIRMÉE (domaine: 3≤m) | AJOUT | 2 |
| `companion_term_le_integral` (l.219) | Terme compagnon p^(−σ−1)(p(n+1)−p n) dominé par 2^(σ+1) fois l'intégrale de t^(−σ−1) sur l'écart. | CONFIRMÉE (domaine: σ>0, n≥1) | AJOUT | 1 |
| `summable_coboundary_companion_majorant` (l.273) | La série compagnon p^(−σ−1)(p(n+1)−p n) est sommable pour σ>0. | CONFIRMÉE (domaine: σ>0) | AJOUT | 1 |
| `summable_coboundary_combined_majorant` (l.363) | La série p^(−σ−1)(p(n+1)−p n)(log p + K) est sommable pour tout σ>0 et tout K réel. | CONFIRMÉE (domaine: σ>0) | AJOUT | 4 |
| `tendsto_coboundaryBoundaryMajorant_zero` (l.381) | t^(−σ)(log t + K) tend vers 0 en +∞ pour σ>0. | CONFIRMÉE (domaine: σ>0) | AJOUT | 4 |
| `coboundaryChannel_cauchySeq` (l.417) | Pour 0<Re s, les sommes partielles de Dirichlet du canal de cobord forment une suite de Cauchy. | CONFIRMÉE (domaine: 0<Re s) | AJOUT | 1 |
| `exists_coboundaryChannel_limit` (l.607) | Pour 0<Re s, ces sommes partielles convergent vers une limite L (convergence ponctuelle). | CONFIRMÉE (domaine: 0<Re s) | AJOUT | 1 |

### `Round26DFChebyshevGrammarWelding`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `primeGapMidpointError_succ_sub` (l.86) | L'incrément de l'erreur au point milieu vaut (g_n+g_{n+1})/2 − log p_{n+1}. | CONFIRMÉE | V48 | 1 |
| `gap_eq_six_mul_add_cross_add_coboundary` (l.105) | Pour n≥2, g_n = 6k + 3·cross n + (phi(n+1) − phi n) pour un entier k. | CONFIRMÉE (domaine: 2≤n) | V174 | 3 |
| `primeGapMidpointError_succ_sub_grammar` (l.129) | Pour n≥2, l'incrément de l'erreur au milieu s'écrit en coordonnées de grammaire mod 6 (k,k', cross, phi) moins log p_{n+1}. | CONFIRMÉE (domaine: 2≤n) | V48,V174 | 1 |
| `sigma_mul_self` (l.146) | sigma n · sigma n = 1. | CONFIRMÉE | AJOUT | 9 |
| `one_sub_two_cross_eq_sigma_mul` (l.151) | Pour n≥2, 1−2·cross n = sigma n · sigma(n+1). | CONFIRMÉE (domaine: 2≤n) | AJOUT | 4 |
| `prod_one_sub_two_cross` (l.161) | Sur [M,N) avec 2≤M≤N, le produit des (1−2·cross n) vaut sigma M · sigma N. | CONFIRMÉE (domaine: 2≤M≤N) | AJOUT | 13 |
| `abs_prod_one_sub_two_cross` (l.178) | Ce produit télescopé est de module exactement 1. | CONFIRMÉE (domaine: 2≤M≤N) | AJOUT | 1 |
| `primeGapMidpointError_eq_left_right_rest` (l.189) | Pour re ρ≠1/2, l'erreur au milieu s'écrit (p_j+p_{j+1})/2 moins la somme des parties θ primitives gauche, droite et reste de la paire réfléchie. | CONFIRMÉE SOUS CONDITION (zéro hors ligne (re≠1/2)) | V48,V63 | 2 |

### `Round26DGTowerPairingInvariance`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `towerPairing_invariant` (l.77) | Pour m>0, (ρ/m)·(m·lp) = ρ·lp. [terme hors maître] | CONFIRMÉE (domaine: 0<m) | AJOUT | 1 |
| `DilationCovariant.at_scaled_argument` (l.87) | Une famille DilationCovariant évaluée à l'étage m au point m·u égale la famille de base en u. | CONFIRMÉE (domaine: 0<m) | AJOUT | 2 |
| `towerMode_at_scaled_argument` (l.98) | Le mode de tour d'étage m en m·lp égale le mode de base en lp. | CONFIRMÉE (domaine: 0<m) | AJOUT | 0 |
| `primeCarrier_at_scaled_argument` (l.105) | Le porteur premier d'étage m en m·u égale le porteur de base en u. | CONFIRMÉE (domaine: 0<m) | AJOUT | 0 |
| `towerPoint_pairing_invariant` (l.113) | towerPairing_invariant spécialisé à un vrai zéro non trivial. | CONFIRMÉE (domaine: 0<m) | AJOUT | 0 |

### `Round26DHTowerSpectralCharacter`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `cpow_ofReal_pos_eq_exp` (l.61) | Pour P>0, P^z = exp(log P · z) dans ℂ. | CONFIRMÉE (domaine: 0<P) | AJOUT | 15 |
| `towerCharacter_pow` (l.69) | exp(−(ρ−1/2)(m log P)) = (towerCharacter P ρ)^m. [terme hors maître] | CONFIRMÉE (domaine: 0<P) | V16 | 2 |
| `norm_towerCharacter` (l.81) | ‖towerCharacter P ρ‖ = P^(−(re ρ − 1/2)) : le module ne voit que le défaut horizontal. | CONFIRMÉE (domaine: 0<P) | V102,V158 | 15 |
| `towerCharacter_eq_modulus_mul_phase` (l.88) | Le caractère de tour = (module portant re ρ − 1/2) × (phase portant Im ρ · log P). | CONFIRMÉE (domaine: 0<P) | V16,V158 | 9 |
| `norm_towerCharacter_eq_one_iff` (l.101) | Pour P>1, ‖towerCharacter P ρ‖=1 ⟺ re ρ = 1/2. | CONFIRMÉE (domaine: 1<P) | V161,V102 | 7 |
| `towerCharacter_reflect` (l.119) | Le caractère du partenaire 1−conj ρ est l'inverse du conjugué du caractère de ρ. | CONFIRMÉE (domaine: 0<P) | V63,V101 | 4 |
| `norm_towerCharacter_pow_eq_one_of_critical` (l.138) | Sur la ligne critique, chaque étage m de la tour est de module 1. | CONFIRMÉE (domaine: re ρ = 1/2 ) | V161 | 1 |
| `norm_towerCharacter_pow` (l.146) | Le module de l'étage m vaut P^(−m(re ρ −1/2)). | CONFIRMÉE (domaine: 0<P) | V102 | 7 |
| `tendsto_norm_towerCharacter_pow_nhds_zero` (l.155) | Pour re ρ>1/2 et P>1, le module de l'étage m tend vers 0. | CONFIRMÉE SOUS CONDITION (re ρ>1/2) | V102 | 0 |
| `tendsto_norm_towerCharacter_pow_atTop` (l.168) | Pour re ρ<1/2 et P>1, le module de l'étage m diverge vers +∞. | CONFIRMÉE SOUS CONDITION (re ρ<1/2) | V102 | 0 |
| `norm_towerCharacter_pow_mul_reflect` (l.179) | Le produit des modules d'étage m de ρ et de son partenaire 1−conj ρ vaut 1. | CONFIRMÉE (domaine: 0<P) | V102,V167 | 0 |
| `primeDirichletWeight_eq_vonMangoldt_mul_towerCharacter` (l.193) | Le poids de Dirichlet premier = (log p · p^(−1/2)) × caractère de tour de p. | CONFIRMÉE | V48,V100 | 2 |
| `grammarSectorPrimeDirichlet_eq_tsum_towerCharacter` (l.220) | Chaque secteur grammatical (Re s>1) est une somme pondérée von Mangoldt des caractères de tour de ses premiers. | CONFIRMÉE | V48,V100 | 1 |

### `Round26DIChi3SpectralSeparation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `sectorChi3Coord_eq_global_sub_two_state` (l.62) | sectorChi3Coord v = sectorGlobalCoord v − 2·sectorStateCoord v. [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `sectorChi3Coord_eq_weighted_sum` (l.68) | sectorChi3Coord v = somme sur τ des poids chi3 × v τ. | CONFIRMÉE | AJOUT | 0 |
| `sector_tau11_from_spectral_basis` (l.78) | v(τ11) = (global − cross + chi3 − cobord)/2. | CONFIRMÉE | AJOUT | 1 |
| `sector_tau55_from_spectral_basis` (l.85) | v(τ55) = (global − cross − chi3 + cobord)/2. | CONFIRMÉE | AJOUT | 1 |
| `sector_eq_of_spectral_basis_coords_eq` (l.92) | Deux familles v,w de secteurs dont les quatre coordonnées spectrales coïncident sont égales. | CONFIRMÉE SOUS CONDITION (égalité des coordonnées globale, cross, cobord, chi3) | AJOUT | 0 |
| `sum_chi3Weight_grammarTransformIndicator_eq_sigma` (l.112) | Pour n≥2, la somme des poids chi3 × indicateurs de transition vaut sigma n. | CONFIRMÉE (domaine: 2≤n) | AJOUT | 1 |
| `grammarChi3Coeff_eq_sigma` (l.134) | Pour n≥2, grammarChi3Coeff n = sigma n. | CONFIRMÉE (domaine: 2≤n) | AJOUT | 0 |
| `sectorChi3Coord_grammarSectorPrimeDirichlet` (l.138) | Pour Re s>1, la coordonnée chi3 des quatre séries sectorielles est la série de Dirichlet première tordue par le caractère. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 1 |
| `sectorChi3Coord_eq_tsum_towerCharacter` (l.178) | Pour Re s>1, cette coordonnée est une somme pondérée chi3 des poids von Mangoldt × caractère de tour. | CONFIRMÉE (domaine: 1<Re s) | V100 | 0 |
| `sector_residue_pinned` (l.201) | Si cobord=0, chi3=0 et global=−1, alors τ51=τ15, τ55=τ11, τ11+τ15=−1/2 et la coordonnée d'état vaut −1/2. | CONFIRMÉE SOUS CONDITION (coordonnées cobord et chi3 nulles et coordonnée globale −1) | AJOUT | 2 |
| `sector_residue_one_parameter` (l.225) | Sous les mêmes trois hypothèses, le vecteur sectoriel est déterminé par sa seule composante τ15. | CONFIRMÉE SOUS CONDITION (cobord=0, chi3=0, global=−1) | AJOUT | 0 |
| `sector_residue_cross_eq_two_mul_free` (l.250) | Sous les mêmes hypothèses, la coordonnée cross vaut 2·τ15. | CONFIRMÉE SOUS CONDITION (cobord=0, chi3=0, global=−1) | AJOUT | 0 |

### `Round26DJChi3WalshCompression`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `phi_eq_half_one_sub_sigma` (l.57) | phi n = (1 − sigma n)/2. | CONFIRMÉE | AJOUT | 2 |
| `coboundary_eq_half_sigma_sub` (l.62) | phi(n+1) − phi n = (sigma n − sigma(n+1))/2. | CONFIRMÉE | AJOUT | 0 |
| `cross_eq_half_one_sub_sigma_mul` (l.69) | Pour n≥2, cross n = (1 − sigma n · sigma(n+1))/2. | CONFIRMÉE (domaine: 2≤n) | AJOUT | 0 |
| `sum_coboundary_telescope` (l.79) | Pour M≤N, la somme des cobords sur [M,N) vaut (sigma M − sigma N)/2. | CONFIRMÉE (domaine: M≤N) | AJOUT | 1 |
| `sigma_eq_one_or_neg_one` (l.87) | sigma n vaut 1 ou −1. | CONFIRMÉE | AJOUT | 10 |
| `abs_sigma` (l.94) | \|sigma n\| = 1. | CONFIRMÉE | AJOUT | 6 |
| `abs_sum_coboundary_le_one` (l.97) | Pour M≤N, la somme des cobords sur [M,N) est bornée par 1 en valeur absolue. | CONFIRMÉE (domaine: M≤N) | AJOUT | 0 |
| `grammarTransformIndicator_tau11_walsh` (l.109) | Pour n≥2, l'indicateur de τ11 vaut (1+sigma n)(1+sigma(n+1))/4. | CONFIRMÉE (domaine: 2≤n) | V174 | 3 |
| `grammarTransformIndicator_tau15_walsh` (l.117) | Pour n≥2, l'indicateur de τ15 vaut (1+sigma n)(1−sigma(n+1))/4. | CONFIRMÉE (domaine: 2≤n) | V174 | 3 |
| `grammarTransformIndicator_tau51_walsh` (l.125) | Pour n≥2, l'indicateur de τ51 vaut (1−sigma n)(1+sigma(n+1))/4. | CONFIRMÉE (domaine: 2≤n) | V174 | 3 |
| `grammarTransformIndicator_tau55_walsh` (l.133) | Pour n≥2, l'indicateur de τ55 vaut (1−sigma n)(1−sigma(n+1))/4. | CONFIRMÉE (domaine: 2≤n) | V174 | 1 |
| `grammarSectorIndicator_spectral_coords` (l.143) | Pour n≥2, les quatre coordonnées spectrales du vecteur indicateur valent 1, sigma n, (sigma n − sigma(n+1))/2 et (1−sigma n·sigma(n+1))/2. | CONFIRMÉE (domaine: 2≤n) | V174 | 0 |

### `Round26DKCombinedChannelNoCancellation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `analyticOrderNatAt_ne_zero_of_eq_zero` (l.46) | Si f analytique en x, non identiquement nulle, s'annule en x, son ordre naturel d'annulation est non nul. | CONFIRMÉE (domaine: f analytique en x, ordre non infini, f x = 0 ) | AJOUT | 2 |
| `meromorphicOrderAt_neg_logDeriv_zeta_mul_eq_neg_one` (l.59) | En un zéro ρ de ζ, −logDeriv(ζ·F) a un pôle simple pour tout facteur F analytique en ρ et non identiquement nul. [terme hors maître] | CONFIRMÉE (domaine: ζ(ρ)=0, F analytique en ρ d'ordre fini ) | AJOUT | 1 |
| `analyticOrderAt_LFunction_ne_top` (l.89) | La L-fonction d'un caractère de Dirichlet non trivial n'est identiquement nulle en aucun point. | CONFIRMÉE (domaine: χ≠1 ) | AJOUT | 1 |
| `meromorphicOrderAt_combinedChannel_eq_neg_one` (l.105) | Pour χ non trivial, −logDeriv(ζ·L(·,χ)) a un pôle simple en tout zéro de ζ. | CONFIRMÉE (domaine: χ≠1 et ζ(ρ)=0 ) | AJOUT | 1 |

### `Round26DLChi3CharacterBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `chi3_apply_zero` (l.50) | chi3 0 = 0. [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `chi3_apply_one` (l.53) | chi3 1 = 1. | CONFIRMÉE | AJOUT | 1 |
| `chi3_apply_two` (l.56) | chi3 2 = −1. | CONFIRMÉE | AJOUT | 2 |
| `chi3_ne_one` (l.60) | chi3 n'est pas le caractère trivial. | CONFIRMÉE | AJOUT | 4 |
| `p_natCast_zmod_three` (l.71) | Pour n≥2, p n est congru à 1 ou 2 modulo 3. | CONFIRMÉE (domaine: 2≤n) | V174 | 1 |
| `chi3_natCast_p_eq_sigma` (l.87) | Pour n≥2, chi3(p n) = sigma n. | CONFIRMÉE (domaine: 2≤n) | V174 | 7 |
| `combined_weight_of_chi_one` (l.122) | (1+1^m)/2 = 1. | CONFIRMÉE | AJOUT | 0 |
| `combined_weight_of_chi_neg_one` (l.127) | (1+(−1)^m)/2 vaut 1 si m pair, 0 sinon. | CONFIRMÉE | AJOUT | 0 |
| `combined_weight_m_one_of_chi_neg_one` (l.136) | (1+(−1)^1)/2 = 0. | CONFIRMÉE | AJOUT | 0 |
| `sourceOneSectors_eq_half_global_add_chi3` (l.141) | v τ11 + v τ15 = (global + chi3)/2. | CONFIRMÉE | AJOUT | 0 |
| `combinedChannel_m_one_weight_eq_source_one_sectors` (l.149) | Pour n≥2, (1+sigma n)/2 = indicateur τ11 + indicateur τ15. | CONFIRMÉE (domaine: 2≤n) | AJOUT | 2 |
| `meromorphicOrderAt_grammarCombinedChannel_zero` (l.168) | En tout zéro ρ de ζ, le canal combiné concret grammarCombinedChannel a un pôle simple. | CONFIRMÉE (domaine: ζ(ρ)=0 ) | AJOUT | 1 |

### `Round26DMCombinedChannelDirichlet`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `grammarCombinedChannel_eq_sum_logDeriv` (l.46) | Pour Re s>1, grammarCombinedChannel s = −logDeriv ζ s − logDeriv L(·,chi3) s. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 0 |
| `one_add_chi3_pow_of_one` (l.67) | Si chi3 a = 1, alors 1+chi3(a^m) = 2 pour tout m. | CONFIRMÉE (domaine: chi3 a = 1 ) | AJOUT | 1 |
| `one_add_chi3_pow_eq_zero_of_neg_one` (l.73) | Si chi3 a = −1 et m impair, 1+chi3(a^m) = 0. | CONFIRMÉE (domaine: chi3 a = −1, m impair ) | AJOUT | 1 |
| `one_add_chi3_pow_of_neg_one_even` (l.81) | Si chi3 a = −1 et m pair, 1+chi3(a^m) = 2. | CONFIRMÉE (domaine: chi3 a = −1, m pair ) | AJOUT | 0 |
| `one_add_chi3_p_pow_eq_zero_of_state_five` (l.90) | Pour p n ≡ 5 mod 6 et m impair, 1+chi3((p n)^m) = 0. | CONFIRMÉE (domaine: état 5 mod 6, m impair ) | V174 | 0 |
| `one_add_chi3_p_pow_of_state_one` (l.104) | Pour p n ≡ 1 mod 6, 1+chi3((p n)^m) = 2 pour tout m. | CONFIRMÉE (domaine: état 1 mod 6 ) | V174 | 0 |
| `one_add_chi3_p_eq_two_mul_source_one_weight` (l.117) | Pour n≥2, 1+chi3(p n) = 2·(indicateur τ11 + indicateur τ15). | CONFIRMÉE (domaine: 2≤n) | AJOUT | 0 |
| `meromorphicOrderAt_combined_m_one_level_eq_neg_one` (l.142) | Si le canal combiné = étage m=1 + queue analytique en ρ, l'étage m=1 a un pôle simple en tout zéro ρ de ζ. | CONFIRMÉE (domaine: ζ(ρ)=0, décomposition level+tail avec tail analytique en ρ ) | AJOUT | 0 |

### `Round26DNTwistedTowerCocycle`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `towerCharacter_ne_zero` (l.75) | Le caractère de tour est non nul pour P>0. [terme hors maître] | CONFIRMÉE (domaine: 0<P) | AJOUT | 19 |
| `towerCharacter_div` (l.80) | Le caractère de tour est multiplicatif en la base : car(A/B)=car(A)/car(B). | CONFIRMÉE (domaine: 0<A, 0<B) | AJOUT | 11 |
| `towerCharacter_div_mul_cancel` (l.91) | car(A/B)·car(B) = car(A). | CONFIRMÉE (domaine: 0<A, 0<B) | AJOUT | 2 |
| `sigma_ne_zero` (l.101) | sigma n ≠ 0 dans ℂ. | CONFIRMÉE | AJOUT | 1 |
| `twistedTowerCharacter_ne_zero` (l.104) | Le caractère de tour tordu est non nul. | CONFIRMÉE | AJOUT | 10 |
| `twistedTowerCharacter_eq_chi3_mul` (l.107) | Pour n≥2, le caractère tordu = chi3(p n) × caractère de tour de p n. | CONFIRMÉE (domaine: 2≤n) | AJOUT | 2 |
| `norm_twistedTowerCharacter` (l.114) | ‖caractère tordu n ρ‖ = (p n)^(−(re ρ − 1/2)). | CONFIRMÉE | V102,V158 | 8 |
| `norm_twistedTowerCharacter_eq_one_iff` (l.121) | Pour p n>1, le module du caractère tordu vaut 1 ⟺ re ρ = 1/2. | CONFIRMÉE (domaine: 1<p n) | V161,V102 | 8 |
| `twistedTowerCharacter_succ` (l.129) | Pour n≥2, car_tordu(n+1) = (1−2cross n)·car(p(n+1)/p n)·car_tordu(n). | CONFIRMÉE (domaine: 2≤n) | AJOUT | 1 |
| `twistedTowerCharacter_block` (l.152) | car_tordu N = (sigma M·sigma N)·car(p N/p M)·car_tordu M. | CONFIRMÉE | AJOUT | 2 |
| `twistedTowerCharacter_block_prod` (l.174) | Idem avec le facteur grammatical écrit comme produit des (1−2cross n) sur [M,N). | CONFIRMÉE (domaine: 2≤M≤N) | AJOUT | 0 |
| `twistedTower_ratio` (l.183) | Le rapport car_tordu N / car_tordu M = (sigma M·sigma N)·car(p N/p M). | CONFIRMÉE | AJOUT | 7 |
| `norm_twistedTower_ratio` (l.191) | Le module de ce rapport vaut (p N/p M)^(−(re ρ −1/2)) : seul le défaut horizontal compte. | CONFIRMÉE | V102,V158 | 7 |
| `one_lt_p_div_p` (l.200) | Pour M<N, p N / p M > 1. | CONFIRMÉE (domaine: M<N) | AJOUT | 12 |
| `norm_twistedTower_ratio_eq_one_iff` (l.204) | Pour M<N, le module du rapport de bloc vaut 1 ⟺ re ρ = 1/2. | CONFIRMÉE (domaine: M<N) | V161,V102 | 11 |
| `twistedTowerCharacter_reflect` (l.214) | Le caractère tordu en 1−conj ρ est l'inverse du conjugué du caractère tordu en ρ. | CONFIRMÉE | V63,V159 | 2 |
| `norm_twistedTowerCharacter_mul_reflect` (l.226) | Le produit des modules en ρ et 1−conj ρ vaut 1. | CONFIRMÉE | V102,V167 | 1 |
| `towerCharacter_pow_add_twisted_pow` (l.238) | car^m + car_tordu^m = (1+sigma^m)·car^m. | CONFIRMÉE | AJOUT | 2 |
| `towerCharacter_pow_add_twisted_pow_eq_zero` (l.247) | Si sigma n = −1 et m impair, car^m + car_tordu^m = 0. | CONFIRMÉE (domaine: sigma n = −1 (état 5 mod 6), m impair ) | V174 | 0 |
| `towerCharacter_pow_add_twisted_pow_eq_two_mul` (l.256) | Si sigma n = 1, car^m + car_tordu^m = 2·car^m pour tout m et ρ. | CONFIRMÉE (domaine: sigma n = 1 (état 1 mod 6) ) | V174 | 0 |
| `radialDeform_im` (l.272) | La déformation radiale d conserve la partie imaginaire. [terme hors maître] | CONFIRMÉE | V158 | 1 |
| `radialDeform_re` (l.275) | La déformation radiale d ajoute d à la partie réelle. | CONFIRMÉE | V158 | 0 |
| `towerCharacter_radialDeform` (l.278) | La déformation radiale multiplie le caractère de tour par le scalaire réel P^(−d). | CONFIRMÉE (domaine: 0<P) | V102,V158 | 3 |
| `twistedTowerCharacter_radialDeform` (l.289) | La déformation radiale multiplie le cocycle tordu entier par le scalaire réel positif (p n)^(−d). | CONFIRMÉE | V102,V158,V159 | 1 |
| `twistedTower_ratio_radialDeform` (l.300) | Sur un bloc, la déformation radiale agit par le seul scalaire (p N/p M)^(−d). | CONFIRMÉE | V102,V158 | 1 |
| `twistedTower_ratio_radialDeform_grammar` (l.309) | Le rapport de bloc au point déformé porte le même facteur grammatical sigma M·sigma N, seul le transport spectral change. | CONFIRMÉE | V159 | 0 |
| `twistedTowerCharacter_modulus_phase` (l.318) | Le cocycle tordu = (sigma n × (p n)^(−(re ρ −1/2))) × exp(−i·Im ρ·log p n) : phase = hauteur. | CONFIRMÉE | V16,V158 | 0 |
| `twistedTower_phase_radialDeform_invariant` (l.329) | Le facteur de phase est invariant sous déformation radiale. | CONFIRMÉE | V158 | 0 |
| `radial_scalar_eq_one_iff` (l.336) | Pour M<N, (p N/p M)^(−d) = 1 ⟺ d = 0. | CONFIRMÉE (domaine: M<N) | V102 | 0 |
| `radiallyBlindObservable_cannot_separate_radial` (l.362) | Aucune observable radialement aveugle du cocycle tordu ne sépare la déformation d de la déformation nulle. | CONFIRMÉE SOUS CONDITION (F radialement aveugle (RadiallyBlindObservable)) | V159,V158 | 0 |
| `arg_twistedTower_ratio_radialDeform_invariant` (l.377) | L'argument du rapport de bloc est invariant par déformation radiale. | CONFIRMÉE | V158,V159 | 0 |
| `grammarSpectralTransportCompatibility_re` (l.399) | Si la compatibilité grammaire/spectre vaut sur un bloc, alors re ρ = 1/2. | CONFIRMÉE SOUS CONDITION (GrammarSpectralTransportCompatibility ρ (détecteur équivalent à la conclusion, docstring)) | V161 | 0 |
| `grammarSpectralTransportCompatibility_of_re` (l.407) | Si re ρ = 1/2, la compatibilité grammaire/spectre vaut. | CONFIRMÉE (domaine: re ρ = 1/2 ) | V161 | 0 |

### `Round26DOSplitInertTowerStep`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `chi3_isPrimitive` (l.68) | chi3 est primitif. | CONFIRMÉE | AJOUT | 1 |
| `chi3_completedLFunction_one_sub` (l.81) | Équation fonctionnelle de la L-fonction complétée de chi3 sous s ↦ 1−s. | CONFIRMÉE | AJOUT | 0 |
| `chi3_differentiable_LFunction` (l.90) | La L-fonction de chi3 est entière (différentiable sur ℂ). | CONFIRMÉE | AJOUT | 0 |
| `towerCharacter_mul_base` (l.98) | car(A·B) = car(A)·car(B). | CONFIRMÉE (domaine: 0<A, 0<B) | AJOUT | 4 |
| `towerCharacter_sq_base` (l.108) | car(A²) = car(A)². | CONFIRMÉE (domaine: 0<A) | AJOUT | 3 |
| `combined_floor_weight_ne_zero_iff` (l.113) | Le poids 1+sigma^m est non nul ⟺ sigma n = 1 ou m pair. | CONFIRMÉE | V174 | 2 |
| `inert_surviving_floor_eq_tower_over_p_sq` (l.138) | car(p n)^(2k) = car((p n)²)^k. | CONFIRMÉE | AJOUT | 2 |
| `norm_inert_surviving_floor` (l.146) | ‖car((p n)²)^k‖ = (p n)^(−2k(re ρ −1/2)). | CONFIRMÉE | V102 | 1 |
| `inert_radial_grid_ne_split_radial_grid` (l.155) | Pour re ρ≠1/2 et p n>1, le rayon de l'étage 1 sur base p diffère du rayon de l'étage 1 sur base p². | CONFIRMÉE SOUS CONDITION (re ρ ≠ 1/2, 1<p n) | V102 | 0 |
| `grammar_selects_tower_support` (l.176) | La grammaire sélectionne le support des étages (1+sigma^m≠0 ⟺ sigma=1 ou m pair) et car(p)^(2k) = car(p²)^k. | CONFIRMÉE | V174 | 4 |

### `Round26DPPoleLocalizationControl`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `meromorphicOrderAt_neg_logDeriv_eq_neg_one_of_zero` (l.73) | Pour G analytique en ρ, d'ordre fini, s'annulant en ρ, −logDeriv G a un pôle simple en ρ. | CONFIRMÉE (domaine: G analytique en ρ, ordre fini, G ρ = 0 ) | AJOUT | 2 |
| `offLineWitness_analyticAt` (l.91) | Le témoin offLineWitness ρ0 est analytique en tout point. [terme hors maître] | CONFIRMÉE | AJOUT | 3 |
| `offLineWitness_apply_self` (l.94) | offLineWitness ρ0 s'annule en ρ0. | CONFIRMÉE | AJOUT | 2 |
| `offLineWitness_analyticOrderAt_ne_top` (l.97) | L'ordre d'annulation du témoin en ρ0 est fini. | CONFIRMÉE | AJOUT | 1 |
| `offLineWitness_pole_localization` (l.109) | Le témoin a un pôle simple de −logDeriv en ρ0. | CONFIRMÉE | AJOUT | 1 |
| `exists_offLine_pole_localization` (l.117) | Il existe une fonction analytique G et un point ρ0 avec re≠1/2, G ρ0 = 0 et pôle simple de −logDeriv G en ρ0. | CONFIRMÉE | AJOUT | 0 |
| `residueDegree_pos` (l.136) | Le degré résiduel de n est strictement positif. | CONFIRMÉE | AJOUT | 0 |
| `idealNorm_pos` (l.143) | La norme idéale de n est strictement positive. | CONFIRMÉE | AJOUT | 2 |
| `towerCharacter_pow_base` (l.146) | car(A^f) = car(A)^f. | CONFIRMÉE (domaine: 0<A) | AJOUT | 1 |
| `surviving_floor_eq_tower_over_idealNorm` (l.155) | car(p n)^(f·k) = car(idealNorm n)^k où f est le degré résiduel. | CONFIRMÉE | AJOUT | 0 |
| `norm_towerCharacter_idealNorm_pow` (l.163) | ‖car(idealNorm n)^k‖ = idealNorm^(−k(re ρ −1/2)). | CONFIRMÉE | V102 | 0 |
| `towerCharacter_idealNorm_radialDeform` (l.170) | Dans la coordonnée de norme idéale, la déformation radiale agit par le scalaire réel idealNorm^(−d). | CONFIRMÉE | V102,V158 | 0 |
| `residueDegree_determined_by_grammar` (l.179) | sigma n = 1 ⟹ degré résiduel 1 ; sigma n = −1 ⟹ degré résiduel 2. | CONFIRMÉE | V174 | 0 |

### `Round26DQSymmetricRadialWitness`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `symmetricRadialWitness_differentiable` (l.60) | Le témoin symétrique radial est entier. [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `symmetricRadialWitness_functional_equation` (l.65) | F(1−s) = F(s) pour le témoin. | CONFIRMÉE | AJOUT | 1 |
| `symmetricRadialWitness_conj` (l.72) | F(conj s) = conj(F(s)) pour le témoin. | CONFIRMÉE | AJOUT | 1 |
| `radialZero_re` (l.80) | La partie réelle de radialZero γ d est 1/2 + d. | CONFIRMÉE | AJOUT | 2 |
| `radialZero_im` (l.83) | La partie imaginaire de radialZero γ d est γ. | CONFIRMÉE | AJOUT | 1 |
| `symmetricRadialWitness_apply_radialZero` (l.86) | Le témoin s'annule en radialZero γ d. | CONFIRMÉE | AJOUT | 2 |
| `symmetricRadialWitness_analyticAt` (l.94) | Le témoin est analytique en tout point. | CONFIRMÉE | AJOUT | 2 |
| `symmetricRadialWitness_apply_half` (l.99) | Le témoin en 1/2 vaut (d²+γ²)² (réel). | CONFIRMÉE | AJOUT | 1 |
| `symmetricRadialWitness_analyticOrderAt_ne_top` (l.108) | Pour γ≠0, l'ordre d'annulation du témoin est fini en tout point. | CONFIRMÉE (domaine: γ≠0 ) | AJOUT | 1 |
| `symmetricRadialWitness_pole_localization` (l.126) | Pour γ≠0, −logDeriv du témoin a un pôle simple en radialZero γ d. | CONFIRMÉE (domaine: γ≠0 ) | AJOUT | 1 |
| `norm_towerCharacter_radialZero` (l.136) | ‖car P (radialZero γ d)‖ = P^(−d). | CONFIRMÉE (domaine: 0<P) | V102 | 0 |
| `exists_symmetric_witness_at_every_radius` (l.143) | Pour γ≠0 et tout d, il existe une fonction entière F symétrique (F(1−s)=F(s), F(conj s)=conj F(s)) avec un zéro simple-pôle en re=1/2+d, Im=γ. | CONFIRMÉE (domaine: γ≠0 ) | V125,V126 | 1 |
| `no_symmetry_package_law_forces_critical_line` (l.163) | Aucune loi ne consommant que (entière + équation fonctionnelle + réflexion conjuguée + annulation en ρ) ne force re ρ = 1/2. | RÉFUTATION COMPILÉE | V125,V126,I12 | 0 |

### `Round26DRReflectedPairEnergy`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `norm_twistedTowerCharacter_pos` (l.77) | Le module du cocycle tordu est strictement positif. | CONFIRMÉE | AJOUT | 5 |
| `norm_twistedTowerCharacter_reflect_eq_inv` (l.82) | Le module au point réfléchi est l'inverse du module. | CONFIRMÉE | V102,V167 | 3 |
| `reflectedPairEnergy_eq_sq_div` (l.90) | reflectedPairEnergy n ρ = (‖car_tordu‖ − 1)²/‖car_tordu‖. [terme hors maître] | CONFIRMÉE | V167 | 3 |
| `reflectedPairEnergy_nonneg` (l.102) | L'énergie de paire réfléchie est ≥ 0. | CONFIRMÉE | V167 | 5 |
| `one_lt_p_nat` (l.107) | p n > 1. | CONFIRMÉE | V13 | 10 |
| `reflectedPairEnergy_eq_zero_iff` (l.109) | L'énergie de paire réfléchie est nulle ⟺ re ρ = 1/2. | CONFIRMÉE | V161,V180 | 4 |
| `reflectedPairEnergy_pos_of_off_line` (l.129) | Si re ρ ≠ 1/2, l'énergie est strictement positive à chaque n. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V167,V180 | 2 |
| `totalReflectedPairEnergy_nonneg` (l.141) | L'énergie totale sur S est ≥ 0. | CONFIRMÉE | AJOUT | 0 |
| `reflectedPairEnergy_le_totalReflectedPairEnergy` (l.146) | Pour m∈S, l'énergie en m est majorée par l'énergie totale (aucune compensation). | CONFIRMÉE (domaine: m ∈ S) | AJOUT | 1 |
| `totalReflectedPairEnergy_pos_of_off_line` (l.158) | Hors ligne, l'énergie totale sur S non vide est strictement positive. | CONFIRMÉE SOUS CONDITION (re ρ ≠ 1/2, S non vide) | V167 | 0 |
| `energy_antitone_of_le_one` (l.168) | Si 0<x≤y≤1, (y−1)²/y ≤ (x−1)²/x. | CONFIRMÉE (domaine: 0<x≤y≤1) | AJOUT | 1 |
| `energy_monotone_of_one_le` (l.176) | Si 1≤y≤x, (y−1)²/y ≤ (x−1)²/x. | CONFIRMÉE (domaine: 1≤y≤x) | AJOUT | 1 |
| `two_rpow_pos` (l.189) | 2^(−(re ρ − 1/2)) > 0. | CONFIRMÉE | AJOUT | 2 |
| `two_rpow_ne_one_of_off_line` (l.192) | Si re ρ ≠ 1/2, 2^(−(re ρ −1/2)) ≠ 1. | CONFIRMÉE SOUS CONDITION (re ρ ≠ 1/2) | AJOUT | 1 |
| `energyBaseTwo_pos_of_off_line` (l.200) | Si re ρ ≠ 1/2, l'énergie en base 2 est strictement positive. | CONFIRMÉE SOUS CONDITION (re ρ ≠ 1/2) | AJOUT | 1 |
| `energyBaseTwo_le` (l.206) | L'énergie en base 2 minore l'énergie à p n, pour tout n. | CONFIRMÉE | AJOUT | 1 |
| `totalReflectedPairEnergy_ge_card_nsmul` (l.241) | L'énergie totale sur S est ≥ card S × énergie en base 2 (divergence linéaire hors ligne). | CONFIRMÉE | V167 | 1 |
| `primeChannelEnergyBounded_imp_critical` (l.263) | Si le canal premier borne uniformément l'énergie de paire réfléchie, alors re ρ = 1/2. | CONFIRMÉE SOUS CONDITION (PrimeChannelEnergyBounded ρ (pour ce zéro)) | AJOUT | 1 |
| `not_radiallyBlindObservable_unitRadius` (l.291) | L'observable de rayon unité n'est pas radialement aveugle. | CONFIRMÉE | V159 | 0 |
| `unitRadiusObservable_twistedTower_iff` (l.302) | L'observable de rayon unité sur le cocycle tordu vaut ⟺ re ρ = 1/2. | CONFIRMÉE | V161 | 0 |

### `Round26DSIntrinsicTransportHolonomy`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `boundedTransport_forces_critical_line` (l.77) | Si le transport de tour est borné (deux côtés) sur le cocycle tordu de ρ, alors re ρ = 1/2. | CONFIRMÉE SOUS CONDITION (TowerTransportBounded pour ce zéro) | AJOUT | 6 |
| `IntrinsicZeroTransport.ne_zero` (l.117) | Le transport zéro intrinsèque T n ne s'annule jamais (champ de structure). [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `IntrinsicZeroTransport.bounded` (l.119) | Le transport zéro intrinsèque reste dans une couronne fixe (TowerTransportBounded). | CONFIRMÉE | AJOUT | 1 |
| `intrinsic_transport_weld_forces_critical_line` (l.128) | Si un transport zéro intrinsèque réalise le transport de tour de ρ, alors re ρ = 1/2. | CONFIRMÉE SOUS CONDITION (RealizesTowerTransport ρ Tr.T (existence d'un transport intrinsèque réalisant la tour)) | AJOUT | 0 |
| `intrinsicZeroTransport_exists_of_critical` (l.144) | Si re ρ = 1/2, il existe un transport zéro intrinsèque réalisant le transport de tour de ρ. | CONFIRMÉE (domaine: re ρ = 1/2 ) | V161 | 0 |
| `boundedTransport_not_unit_modulus` (l.159) | Il existe un transport borné dont le module n'est pas identiquement 1. | CONFIRMÉE | AJOUT | 0 |

### `Round26DTRankOneScalarCollapse`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `smul_mul_conjTranspose_mul` (l.102) | Pour z scalaire et τ matrice, (zτ)(zτ)*(zτ) = (z·conj z·z)·(τ τ* τ). [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `scalar_partialIsometry_iff` (l.114) | Si τ≠0 est isométrie partielle, zτ l'est ⟺ ‖z‖=1 ou z=0. | CONFIRMÉE (domaine: τ≠0 et τ τ* τ = τ ) | AJOUT | 1 |
| `scalarBlock_partialIsometry_iff_critical` (l.162) | Le bloc de tour réalisé scalairement sur une isométrie partielle τ≠0 est isométrie partielle ⟺ re ρ = 1/2. | CONFIRMÉE (domaine: τ≠0 isométrie partielle, M<N ) | V161 | 3 |
| `stateCoboundary_loop_forces_unit` (l.195) | Sur une boucle de cobord d'état avec poids h s>0, ‖z‖ = 1. | CONFIRMÉE SOUS CONDITION (h s>0, IsStateCoboundary h z s s) | AJOUT | 1 |
| `stateCoboundary_loop_forces_critical` (l.210) | Un bloc-boucle de la tour à forme positive préservée impose re ρ = 1/2. | CONFIRMÉE SOUS CONDITION (h s>0, M<N, IsStateCoboundary sur le bloc) | AJOUT | 0 |
| `nilpotent_offDiagonal_transition` (l.220) | La transition hors-diagonale z·[[0,1],[0,0]] est nilpotente d'ordre 2. | CONFIRMÉE | AJOUT | 0 |
| `singleBlock_bound_is_vacuous` (l.235) | Sur un bloc isolé, une borne ‖T‖≤C avec C libre est toujours satisfaite (vide). | CONFIRMÉE | AJOUT | 0 |
| `twistedTower_radii_eq_of_re` (l.255) | Les rayons du cocycle tordu ne dépendent que de re ρ. | CONFIRMÉE (domaine: re ρ = re σ ) | V102,V158 | 2 |
| `towerRadialObservable_blind_to_height` (l.261) | Une observable radiale de tour a même valeur en ρ et en ρ+it. | CONFIRMÉE (domaine: F observable radiale de tour ) | V158 | 0 |
| `towerRadialObservable_eq_at_re` (l.272) | Une observable radiale de tour en ρ égale sa valeur au point réel re ρ. | CONFIRMÉE (domaine: F observable radiale de tour ) | V158 | 0 |
| `primeChannelEnergyBounded_is_towerRadial` (l.287) | PrimeChannelEnergyBounded est une observable radiale de tour. | CONFIRMÉE | V158 | 0 |
| `towerTransportBounded_is_towerRadial` (l.295) | La bornitude du transport du cocycle tordu est une observable radiale de tour. | CONFIRMÉE | V158 | 0 |

### `Round26DUConditionalClosureArchitecture`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `radialObservable_re_lt_one` (l.103) | « re ρ < 1 » est une observable radiale de tour. | CONFIRMÉE | AJOUT | 1 |
| `zetaZero_re_lt_one` (l.119) | Tout ρ avec ζ(ρ)=0 vérifie re ρ < 1. | CONFIRMÉE (domaine: ζ(ρ)=0 (donnée de l'objet)) | V7 | 1 |
| `towerRadial_does_not_block_zeta_provenance` (l.127) | Il existe une observable radiale de tour vraie de tout zéro de ζ. | CONFIRMÉE | AJOUT | 0 |
| `loopProjector_idem` (l.144) | loopProjector est idempotent. | CONFIRMÉE | AJOUT | 1 |
| `loop_iterate_smul` (l.148) | (z·loopProjector)^n = z^n·loopProjector pour n>0. | CONFIRMÉE (domaine: 0<n) | AJOUT | 0 |
| `loopHolonomy_bounded_norm_le_one` (l.162) | Si x≥0 et x^n ≤ C pour tout n, alors x ≤ 1. | CONFIRMÉE (domaine: puissances de x bornées ) | AJOUT | 1 |
| `loopHolonomy_bounded_forces_critical` (l.176) | Sur un bloc M<N, si les puissances du rapport de bloc et de son inverse sont bornées, alors re ρ = 1/2. | CONFIRMÉE (domaine: bornes uniformes des puissances du rapport de bloc et de son inverse ) | AJOUT | 0 |
| `reflection_oneSided_forces_critical` (l.196) | Si Z est stable par ρ↦1−ρ et tous ses membres vérifient re≤1/2, alors tout membre a re=1/2. | CONFIRMÉE (domaine: Z stable par réflexion et borne re ≤ 1/2 pour tous les membres ) | V63 | 1 |
| `reflection_oneSided_norm_forces_critical` (l.209) | Si le rapport de bloc en ρ et en 1−conj ρ est de module ≤1, alors re ρ = 1/2. | CONFIRMÉE SOUS CONDITION (M<N et contractivité du rapport de bloc en ρ et son réfléchi) | AJOUT | 1 |
| `OffLineCounter.mono` (l.237) | Le compteur hors ligne W est monotone en la hauteur. [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `offLineCount_lt_one_eq_zero` (l.239) | Si W(T) ≤ f<1 alors W(T)=0. | CONFIRMÉE (domaine: majoration réelle f<1 ) | AJOUT | 0 |
| `offLineCount_cofinal_lt_one_vanishes` (l.248) | Si W prend des valeurs <1 à des hauteurs cofinales, alors W ≡ 0. | CONFIRMÉE (domaine: valeurs <1 à des hauteurs arbitrairement grandes ) | AJOUT | 0 |
| `defect_le_all_pos_eq_zero` (l.262) | Si \|d\| ≤ ε pour tout ε>0 alors d=0. | CONFIRMÉE (domaine: \|d\| ≤ ε pour tout ε>0 ) | AJOUT | 2 |
| `tower_annulus_shrinking_forces_critical` (l.271) | Si \|re ρ − 1/2\| ≤ ε pour tout ε>0 alors re ρ = 1/2. | CONFIRMÉE (domaine: \|re ρ −1/2\| ≤ ε pour tout ε>0 ) | AJOUT | 0 |
| `chebyshevExponent_half_forces_critical` (l.287) | Si Z est stable par réflexion et satisfait une borne d'exposant de Chebyshev 1/2, tout membre a re=1/2. | CONFIRMÉE SOUS CONDITION (Z stable par réflexion et ChebyshevExponentBound Z (1/2)) | AJOUT | 0 |
| `chebyshevExponent_bounds_defect` (l.292) | Sous stabilité par réflexion et borne d'exposant θ, \|re ρ −1/2\| ≤ θ−1/2 pour tout membre. | CONFIRMÉE SOUS CONDITION (Z stable par réflexion et ChebyshevExponentBound Z θ) | AJOUT | 0 |

### `Round26DVChebyshevPoleObstruction`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `tendsto_mul_of_boundedNear` (l.96) | Si −ζ'/ζ est bornée près de ρ, alors (w−ρ)·(−ζ'/ζ)(w) → 0. | CONFIRMÉE SOUS CONDITION (LogDerivBoundedNear ρ) | AJOUT | 2 |
| `logDerivBoundedNear_forces_ne_zero` (l.118) | Si −ζ'/ζ est bornée sur un voisinage épointé de ρ, alors ζ(ρ)≠0. | CONFIRMÉE SOUS CONDITION (LogDerivBoundedNear ρ) | AJOUT | 1 |
| `logDerivBoundedRightOf_forces_re_le` (l.151) | Si −ζ'/ζ est bornée à droite de θ, tout zéro ρ≠1 de ζ a re ρ ≤ θ. | CONFIRMÉE SOUS CONDITION (LogDerivBoundedRightOf θ, ρ≠1) | AJOUT | 2 |
| `chebyshevError_mellin_majorant` (l.170) | Si \|erreur de Chebyshev(x)\| ≤ C x^θ (x≥1), l'intégrande de Mellin est majorée par C x^(θ−re s −1). | CONFIRMÉE SOUS CONDITION (borne d'exposant θ sur l'erreur de Chebyshev) | V48 | 1 |
| `chebyshev_bounds_defect` (l.216) | Sous un pont exposant-Chebyshev→borne de logDeriv et une erreur en x^θ, tout zéro de ζ (0<re, ρ≠1, 1−ρ≠1) vérifie \|re ρ −1/2\| ≤ θ−1/2. | CONFIRMÉE SOUS CONDITION (ChebyshevExponentGivesLogDerivBound θ et ChebyshevErrorExponent θ) | V48,V126 | 1 |
| `chebyshevHalf_forces_critical_line` (l.231) | Avec θ=1/2 (pont + erreur de Chebyshev en x^(1/2)), tout zéro de ζ (0<re, ρ≠1, 1−ρ≠1) a re=1/2. | IMPLIQUE RH SOUS PRÉMISSE | V126,O5 | 2 |

### `Round26DWResidueThresholdBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `residueBelowOne_forces_ne_zero` (l.83) | Si le résidu échelonné de −ζ'/ζ passe sous 1 près de ρ, alors ζ(ρ)≠0. [terme hors maître] | CONFIRMÉE (domaine: LogDerivResidueBelowOne ρ ) | AJOUT | 4 |
| `boundedNear_imp_residueBelowOne` (l.103) | Une borne locale de −ζ'/ζ près de ρ entraîne le seuil de résidu sous 1. | CONFIRMÉE SOUS CONDITION (LogDerivBoundedNear ρ) | AJOUT | 3 |
| `residueThreshold_strictly_weaker` (l.116) | Il existe g avec ‖(w−0)g(w)‖=1/2 partout mais g non bornée sur tout voisinage épointé de 0. | CONFIRMÉE | AJOUT | 0 |
| `residueBelowOne_forces_re_le` (l.168) | Si le résidu échelonné est sous 1 à droite de θ, tout zéro ρ≠1 de ζ a re ρ ≤ θ. | CONFIRMÉE (domaine: LogDerivResidueBelowOneRightOf θ, ρ≠1 ) | AJOUT | 2 |
| `boundedRightOf_imp_residueBelowOneRightOf` (l.174) | La borne locale à droite de θ entraîne le seuil de résidu à droite de θ. | CONFIRMÉE SOUS CONDITION (LogDerivBoundedRightOf θ) | AJOUT | 0 |

### `Round26DXSingleLockThreeFormulations`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `primeChannelEnergyBounded_iff_critical` (l.74) | Pour tout ρ, PrimeChannelEnergyBounded ρ ⟺ re ρ = 1/2. | CONFIRMÉE | V161,V180 | 4 |
| `towerTransportBounded_iff_critical` (l.84) | Pour tout ρ, le transport de tour tordu de ρ est borné ⟺ re ρ = 1/2. | CONFIRMÉE | V161 | 5 |
| `single_lock_three_formulations` (l.94) | Pour τ≠0 isométrie partielle et M<N, l'isométrie partielle du bloc réalisé ⟺ (énergie première bornée ∧ transport de tour borné). | CONFIRMÉE (domaine: τ≠0 isométrie partielle, M<N ) | V161 | 0 |
| `chebyshev_delivers_the_single_lock` (l.122) | Sous le pont et l'erreur de Chebyshev en θ=1/2, tout zéro ρ de ζ (0<re, ρ≠1, 1−ρ≠1) a énergie première et transport de tour bornés. | CONFIRMÉE SOUS CONDITION (ChebyshevExponentGivesLogDerivBound(1/2) et ChebyshevErrorExponent(1/2)) | V126 | 0 |
| `chebyshev_delivers_partial_isometry` (l.140) | Sous les mêmes deux prémisses, le bloc réalisé scalairement est une isométrie partielle pour tout zéro. | CONFIRMÉE SOUS CONDITION (mêmes deux prémisses Chebyshev 1/2, τ≠0 isométrie partielle, M<N) | V126 | 0 |

### `Round26DYRegularityBudgetSkeleton`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `PrimeChannelRegularityBudget.budget` (l.90) | Le budget de régularité du canal premier donne, pour tout ρ à droite de la ligne (ρ≠1), un résidu échelonné sous 1. [terme hors maître] | CONFIRMÉE SOUS CONDITION (PrimeChannelRegularityBudget (objet supposé)) | AJOUT | 2 |
| `SymmetricPrimeChannelRegularityBudget.budget` (l.96) | La version symétrique donne ce résidu sous 1 en tout point ρ≠1 hors de la ligne critique. | CONFIRMÉE SOUS CONDITION (SymmetricPrimeChannelRegularityBudget) | AJOUT | 1 |
| `riemannHypothesis_of_symmetric_budget` (l.100) | SymmetricPrimeChannelRegularityBudget entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V116,O5 | 1 |
| `riemannHypothesis_of_budget` (l.122) | PrimeChannelRegularityBudget (unilatéral) et NontrivialZeroInStrip entraînent RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V116,O5 | 4 |
| `budget_delivers_the_single_lock` (l.152) | Sous le budget et le fait de bande, tout zéro non trivial ρ≠1 de ζ a énergie première et transport de tour bornés. | CONFIRMÉE SOUS CONDITION (PrimeChannelRegularityBudget et NontrivialZeroInStrip) | AJOUT | 0 |
| `budget_delivers_partial_isometry` (l.166) | Sous le budget et le fait de bande, le bloc réalisé est isométrie partielle pour tout zéro non trivial. | CONFIRMÉE SOUS CONDITION (budget, bande, τ≠0 isométrie partielle, M<N) | AJOUT | 0 |
| `budget_of_chebyshev` (l.185) | Les deux prémisses Chebyshev θ=1/2 (pont, erreur) fournissent PrimeChannelRegularityBudget. | CONFIRMÉE SOUS CONDITION (ChebyshevExponentGivesLogDerivBound(1/2) et ChebyshevErrorExponent(1/2)) | AJOUT | 0 |

### `Round26DZChebyshevFamilyClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `chebyshevExponentFamily_of_half` (l.82) | L'erreur de Chebyshev en x^(1/2) entraîne la famille d'exposants (θ>1/2). | CONFIRMÉE SOUS CONDITION (ChebyshevErrorExponent(1/2)) | AJOUT | 0 |
| `riemannHypothesis_of_budgetFamily` (l.106) | PrimeChannelRegularityBudgetFamily et NontrivialZeroInStrip entraînent RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V116,O5 | 1 |
| `budgetFamily_of_chebyshevFamily` (l.140) | Le pont pour tout θ>1/2 et la famille d'exposants de Chebyshev fournissent la famille de budgets. | CONFIRMÉE SOUS CONDITION (pont ∀θ>1/2 et ChebyshevExponentFamily) | AJOUT | 2 |
| `riemannHypothesis_of_chebyshevFamily` (l.146) | Le pont pour tout θ>1/2, la famille d'exposants de Chebyshev et le fait de bande entraînent RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V116,V48,O5 | 3 |

### `Round26EATrueZeroGrammarHolonomyTarget`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `IntrinsicZeroTransportCore.ne_zero` (l.34) | Le transport du noyau intrinsèque T n ne s'annule jamais (champ). [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `PrimeGrammarHolonomyAsset.unit_norm_from_finite_holonomy` (l.43) | L'actif d'holonomie de grammaire première a module 1 à tout n (champ). | CONFIRMÉE | AJOUT | 2 |
| `primeGrammarHolonomyAsset_bounded` (l.45) | Un actif d'holonomie première (module 1) est borné à deux côtés (couronne). | CONFIRMÉE | AJOUT | 1 |
| `bounded_of_primeHolonomyRealization` (l.65) | Si H est borné et Tr réalise H à phase unitaire près, Tr.T est borné. | CONFIRMÉE SOUS CONDITION (H borné et RealizesPrimeHolonomyUpToUnitPhase) | AJOUT | 1 |
| `trueZeroPrimePowerIntervalRealization_forces_rh` (l.96) | Si la cible TrueZeroPrimePowerIntervalRealization vaut pour un actif A, RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126,O5 | 2 |
| `primeGrammarSigmaAsset_H` (l.152) | L'actif sigma a pour holonomie sigma n. | CONFIRMÉE | AJOUT | 1 |
| `twistedTowerCharacter_eq_asset_mul` (l.155) | Le cocycle tordu = holonomie de l'actif sigma × caractère de tour de p n. | CONFIRMÉE | AJOUT | 0 |
| `exists_realization_iff_unit_tower` (l.171) | À ρ fixé, un porteur zéro réalisant holonomie première et module de tour existe ⟺ le cocycle tordu est de module 1 à tout n. | CONFIRMÉE | V161 | 2 |
| `trueZeroPrimePowerIntervalRealization_asset_independent` (l.201) | TrueZeroPrimePowerIntervalRealization A ⟺ TrueZeroPrimePowerIntervalRealization B pour deux actifs quelconques. | ÉQUIVALENTE À RH | AJOUT | 0 |
| `trueZeroPrimePowerIntervalRealization_iff_rh` (l.215) | TrueZeroPrimePowerIntervalRealization A ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V126,O10 | 0 |

### `Round26EBTrueZeroLoopPowerBounded`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `loopBlockM_le` (l.78) | Le bord inférieur loopBlockM du bloc de boucle canonique vérifie 2 ≤ loopBlockM. [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `loopBlock_lt` (l.80) | loopBlockM < loopBlockN. | CONFIRMÉE | AJOUT | 4 |
| `loopBlock_same_state` (l.82) | Les deux bords du bloc portent le même état mod 6 (p M ≡ p N). | CONFIRMÉE | V174 | 0 |
| `sigma_loopBlockM` (l.87) | sigma en loopBlockM vaut −1. | CONFIRMÉE | AJOUT | 1 |
| `sigma_loopBlockN` (l.92) | sigma en loopBlockN vaut −1. | CONFIRMÉE | AJOUT | 1 |
| `loopBlock_interval_holonomy` (l.97) | Le produit des (1−2·cross n) sur [loopBlockM, loopBlockN) vaut 1. | CONFIRMÉE | AJOUT | 0 |
| `loopBlock_spectral_nontrivial` (l.109) | Le rapport p(loopBlockN)/p(loopBlockM) est > 1. | CONFIRMÉE | AJOUT | 0 |
| `loopPowerBoundedCofinalAt_of_loopPowerBoundedAt` (l.142) | La bornitude des puissances de boucle en ρ entraîne sa version cofinale. | CONFIRMÉE SOUS CONDITION (LoopPowerBoundedAt M N ρ) | AJOUT | 1 |
| `trueZeroLoopPowerBoundedCofinal_of_trueZeroLoopPowerBounded` (l.147) | TrueZeroLoopPowerBounded entraîne sa version cofinale. | CONFIRMÉE SOUS CONDITION (TrueZeroLoopPowerBounded M N) | AJOUT | 1 |
| `cofinal_pow_bounded_norm_le_one` (l.156) | Si x^k ≤ C à des exposants cofinaux, alors x ≤ 1. | CONFIRMÉE SOUS CONDITION (puissances majorées à exposants cofinaux) | AJOUT | 2 |
| `trueZeroLoopPowerBoundedCofinal_forces_rh` (l.175) | Pour M<N, la bornitude cofinale des puissances de boucle de tout vrai zéro entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126 | 1 |
| `trueZeroLoopPowerBounded_forces_rh` (l.188) | Pour M<N, TrueZeroLoopPowerBounded M N entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126 | 2 |
| `trueZeroLoopPowerBounded_canonicalBlock_forces_rh` (l.194) | TrueZeroLoopPowerBounded sur le bloc canonique entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126 | 0 |
| `loopPowerBoundedAt_of_critical` (l.201) | Pour re ρ = 1/2, la bornitude des puissances de boucle vaut. | CONFIRMÉE (domaine: zéro sur la ligne ) | AJOUT | 3 |
| `trueZeroLoopPowerBounded_of_rh` (l.212) | RiemannHypothesis entraîne TrueZeroLoopPowerBounded sur tout bloc. | CONFIRMÉE SOUS CONDITION (RH: hypothèse RiemannHypothesis (sens RH → objet)) | AJOUT | 4 |
| `trueZeroLoopPowerBounded_iff_rh` (l.218) | Pour M<N, TrueZeroLoopPowerBounded M N ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V126,V117 | 1 |
| `trueZeroLoopPowerBounded_of_towerTransportBounded` (l.224) | Si tout vrai zéro a une tour bornée en transport, alors TrueZeroLoopPowerBounded. | CONFIRMÉE (domaine: tour bornée pour tout zéro non trivial ) | AJOUT | 0 |
| `trueZeroLoopPowerBounded_of_trueZeroPrimePowerIntervalRealization` (l.233) | La réalisation d'intervalle de puissance première entraîne TrueZeroLoopPowerBounded. | CONFIRMÉE (domaine: TrueZeroPrimePowerIntervalRealization A (prémisse ⟺ RH par trueZeroPrimePowerIntervalRealization_iff_rh) ) | AJOUT | 0 |
| `trueZeroLoopPowerBounded_of_symmetric_budget` (l.239) | Le budget de régularité symétrique du canal premier entraîne TrueZeroLoopPowerBounded. | CONFIRMÉE SOUS CONDITION (SymmetricPrimeChannelRegularityBudget) | AJOUT | 0 |
| `trueZeroLoopPowerBounded_of_budget` (l.244) | Budget de régularité et fait de bande entraînent TrueZeroLoopPowerBounded. | CONFIRMÉE SOUS CONDITION (PrimeChannelRegularityBudget et NontrivialZeroInStrip) | AJOUT | 0 |
| `loopPowerBoundedAt_of_towerTransportBounded` (l.257) | Bornitude de tour en ρ entraîne bornitude de boucle en ρ. | CONFIRMÉE SOUS CONDITION (TowerTransportBounded en ρ) | AJOUT | 0 |
| `loopPowerBoundedAt_not_towerTransportBounded` (l.263) | Pour M<N, il existe ρ à boucle bornée mais tour non bornée (la réciproque est fausse). | CONFIRMÉE (domaine: M<N ) | AJOUT | 0 |
| `loopPowerBoundedAt_iff_norm_le_one` (l.286) | La bornitude des puissances de boucle ⟺ ‖ratio de tour N/M‖ ≤ 1. | CONFIRMÉE | AJOUT | 2 |
| `loopPowerBoundedAt_iff_half_le_re` (l.299) | Pour M<N, bornitude des puissances de boucle en ρ ⟺ 1/2 ≤ re ρ. | CONFIRMÉE (domaine: M<N) | AJOUT | 4 |
| `trueZeroLoopPowerBounded_iff_rightHalfPlane` (l.322) | Pour M<N, TrueZeroLoopPowerBounded ⟺ TrueZeroRightHalfPlane. | CONFIRMÉE (domaine: M<N) | AJOUT | 0 |
| `trueZeroRightHalfPlane_forces_rh` (l.331) | TrueZeroRightHalfPlane entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126 | 2 |
| `loopPowerBounded_is_exactly_half_of_towerBound` (l.360) | Pour M<N et tout ρ : boucle bornée ⟺ 1/2 ≤ re ρ, et tour bornée ⟺ re ρ = 1/2. | CONFIRMÉE (domaine: M<N) | AJOUT | 0 |

### `Round26ECTerminalSocketClassification`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `logDerivResidueBelowOne_of_ne_zero` (l.68) | Pour ρ≠1 et ζ(ρ)≠0, le résidu logarithmique de ζ est sous le seuil. | CONFIRMÉE (domaine: ρ≠1, ζ(ρ)≠0 ) | AJOUT | 2 |
| `logDerivResidueBelowOne_iff_zeta_ne_zero` (l.90) | Pour ρ≠1, LogDerivResidueBelowOne ρ ⟺ ζ(ρ)≠0. | CONFIRMÉE (domaine: ρ≠1 ) | AJOUT | 0 |
| `re_le_neg_two_of_isTrivialZetaZero` (l.107) | Un zéro trivial a une partie réelle ≤ −2. | CONFIRMÉE (domaine: zéro trivial ) | V6 | 4 |
| `re_pos_of_nontrivial_zeta_zero` (l.116) | Un zéro de ζ non trivial a une partie réelle > 0. | CONFIRMÉE (domaine: ζ(ρ)=0 et non trivial ) | V7 | 8 |
| `nontrivialZeroInStrip_holds` (l.195) | Le prédicat NontrivialZeroInStrip (fait de bande) est établi sans condition. | CONFIRMÉE | V7 | 4 |
| `primeChannelRegularityBudget_iff_noRightZetaZero` (l.207) | PrimeChannelRegularityBudget ⟺ NoRightZetaZero. | CONFIRMÉE | AJOUT | 1 |
| `riemannHypothesis_of_noRightZetaZero` (l.221) | NoRightZetaZero entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126 | 1 |
| `noRightZetaZero_of_riemannHypothesis` (l.243) | RiemannHypothesis entraîne NoRightZetaZero. | CONFIRMÉE SOUS CONDITION (RH: hypothèse RiemannHypothesis (RH → NoRightZetaZero)) | AJOUT | 1 |
| `noRightZetaZero_iff_riemannHypothesis` (l.254) | NoRightZetaZero ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 3 |
| `primeChannelRegularityBudget_iff_riemannHypothesis` (l.259) | PrimeChannelRegularityBudget ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 0 |
| `trueZeroRightHalfPlane_iff_noRightZetaZero` (l.271) | TrueZeroRightHalfPlane ⟺ NoRightZetaZero. | CONFIRMÉE | AJOUT | 1 |
| `trueZeroRightHalfPlane_iff_riemannHypothesis` (l.300) | TrueZeroRightHalfPlane ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 0 |
| `trueZeroPrimeChannelEnergyBounded_iff_riemannHypothesis` (l.320) | TrueZeroPrimeChannelEnergyBounded ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 0 |
| `trueZeroTowerTransportBounded_iff_riemannHypothesis` (l.330) | TrueZeroTowerTransportBounded ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 0 |
| `trueZeroLoopPowerBounded_canonicalBlock_iff_riemannHypothesis` (l.340) | TrueZeroLoopPowerBounded sur le bloc canonique ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 0 |
| `analyticAt_primeGrammarChannelContinuation_of_ne_zero` (l.354) | Pour re ρ>1/2, ρ≠1, ζ(ρ)≠0, le canal grammatical premier continué est analytique en ρ. | CONFIRMÉE SOUS CONDITION (re ρ>1/2, ρ≠1, ζ(ρ)≠0) | AJOUT | 1 |
| `primeGrammarChannelAnalyticRightOfHalf_iff_riemannHypothesis` (l.369) | L'analyticité du canal grammatical à droite de la ligne ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 0 |
| `riemannHypothesis_of_chebyshevFamily_unconditionalStrip` (l.394) | Si tout θ>1/2 donne la borne log-dérivée de Chebyshev et si la famille d'exposants Chebyshev existe, alors RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126 | 0 |
| `riemannHypothesis_of_budget_unconditionalStrip` (l.399) | PrimeChannelRegularityBudget entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126 | 0 |

### `Round26EDTrueZeroFullRigidityIntegration`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `centeredTrueZeroRow_eq` (l.66) | Pour x>0, la ligne centrée du vrai zéro vaut reflectedRowCoeff ρ · x^(ρ−1/2). [terme hors maître] | CONFIRMÉE (domaine: 0<x) | V100 | 4 |
| `centeredTrueZeroRow_one` (l.76) | En x=1, la ligne centrée vaut le coefficient canonique reflectedRowCoeff ρ. | CONFIRMÉE | AJOUT | 1 |
| `centeredTrueZeroRow_ne_zero` (l.83) | Pour x>0, la ligne centrée du vrai zéro est non nulle. | CONFIRMÉE (domaine: 0<x) | AJOUT | 0 |
| `trueZeroReturnTransport_eq` (l.97) | Le transport de retour M→N du vrai zéro égale le caractère de tour en p N/p M. | CONFIRMÉE | V45,V100 | 7 |
| `trueZeroReturnTransport_factors_through_value` (l.127) | Le transport de retour ne dépend que de la valeur complexe de ρ. | CONFIRMÉE (domaine: ↑ρ = ↑ρ' ) | AJOUT | 0 |
| `trueZeroQReturn_eq` (l.139) | Pour 2≤M≤N, le retour Q du vrai zéro égale le quotient des caractères de tour tordus N/M. | CONFIRMÉE (domaine: 2≤M≤N) | AJOUT | 6 |
| `trueZeroQReturn_ne_zero` (l.153) | Pour 2≤M≤N, le retour Q est non nul. | CONFIRMÉE (domaine: 2≤M≤N) | AJOUT | 3 |
| `norm_trueZeroQReturn` (l.163) | Pour 2≤M≤N, ‖QReturn‖ = (p N/p M)^(−(re ρ −1/2)) : seul le défaut horizontal est lu. | CONFIRMÉE (domaine: 2≤M≤N) | V102,V158 | 2 |
| `trueZeroQReturn_grammar_factor` (l.172) | Pour 2≤M≤N, le produit grammatical vaut σM·σN et de valeur absolue 1. | CONFIRMÉE (domaine: 2≤M≤N) | AJOUT | 0 |
| `trueZeroReturnTransport_modulus_phase` (l.179) | Le transport de retour s'écrit module (p N/p M)^(−(re ρ−1/2)) fois phase exp(−i·Im ρ·log(p N/p M)). | CONFIRMÉE | V100,V158 | 0 |
| `trueZeroQReturn_adjacent_step` (l.190) | Pour n≥2, le pas n→n+1 de la tour tordue = (1−2·cross n) × retour adjacent × tour tordue en n. | CONFIRMÉE (domaine: 2≤n) | AJOUT | 0 |
| `centeredTrueZeroRow_primePow` (l.203) | À l'étage x=p^m, la ligne centrée vaut reflectedRowCoeff ρ × (caractère de tour^m)⁻¹. | CONFIRMÉE | V100 | 1 |
| `trueZeroLevelReturn` (l.221) | Le quotient ligne centrée(1)/ligne centrée(p^m) vaut le caractère de tour à la puissance m. | CONFIRMÉE | V100 | 3 |
| `norm_trueZeroLevelReturn` (l.235) | Le module de ce quotient est p^(−m·(re ρ−1/2)). | CONFIRMÉE | V102 | 0 |
| `vonMangoldt_p_pow` (l.242) | Pour m≠0, Λ(p^m) = log p. | CONFIRMÉE (domaine: m≠0 ) | V48 | 2 |
| `primePowerWeight_p_pow` (l.249) | Pour m≠0, le poids atomique de p^m vaut 1/m. | CONFIRMÉE (domaine: m≠0 ) | AJOUT | 1 |
| `trueZeroPrimePowerIntervalWeld` (l.265) | Pour m≠0 : retour de niveau = caractère^m, Λ(p^m)=log p, poids 1/m, et log(p^m)·poids = Λ(p^m). | CONFIRMÉE (domaine: m≠0) | V48,V145 | 0 |
| `explicitFormulaBridge_at_p` (l.289) | ψ(p n) = log p·PiMangoldt − ∫ PiMangoldt/t, et PiMangoldt(p n) = PiWeighted(...) : pont d'Abel en la position p n. | CONFIRMÉE | V48,V121 | 0 |
| `trueZeroQReturn_reflect` (l.303) | Pour 2≤M≤N, le retour Q du réfléchi-conjugué est l'inverse du conjugué du retour Q de ρ. | CONFIRMÉE (domaine: 2≤M≤N) | V80,V101 | 2 |
| `norm_trueZeroQReturn_mul_reflect` (l.314) | Les modules des retours Q de ρ et de son réfléchi-conjugué ont pour produit 1. | CONFIRMÉE (domaine: 2≤M≤N) | V102 | 0 |
| `trueZeroBlockEnergy_eq_sq_div` (l.331) | L'énergie de bloc vaut (‖Q‖−1)²/‖Q‖. | CONFIRMÉE (domaine: 2≤M≤N) | AJOUT | 3 |
| `trueZeroBlockEnergy_nonneg` (l.345) | L'énergie de bloc est ≥ 0. | CONFIRMÉE (domaine: 2≤M≤N) | AJOUT | 1 |
| `trueZeroBlockEnergy_eq_zero_iff` (l.350) | Pour 2≤M<N, l'énergie de bloc est nulle ssi re ρ = 1/2. | CONFIRMÉE (domaine: 2≤M<N) | V161,V167 | 1 |
| `trueZeroBlockEnergy_pos_of_off_line` (l.371) | Pour re ρ ≠ 1/2, l'énergie de bloc est > 0. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V167 | 1 |
| `trueZeroCarrier_eq` (l.392) | Le carrier du vrai zéro égale la tour tordue. [terme hors maître] | CONFIRMÉE | V100 | 9 |
| `trueZeroCarrier_ne_zero` (l.402) | Le carrier du vrai zéro est non nul. | CONFIRMÉE | AJOUT | 0 |
| `trueZeroCarrier_realizes_harmonic_tower_modulus` (l.414) | Pour tout vrai zéro, le carrier réalise le module de la tour harmonique. | CONFIRMÉE | V100 | 4 |
| `trueZeroCarrier_realizesPrimeHolonomy_iff` (l.424) | Le carrier réalise l'holonomie première à phase unitaire près ⟺ re ρ = 1/2. | CONFIRMÉE | V161 | 1 |
| `trueZeroTarget_content` (l.453) | Réalisation de l'holonomie à phase unitaire près et du module harmonique ⟺ re ρ = 1/2. | CONFIRMÉE | V161 | 0 |
| `case_critical` (l.475) | Pour re ρ = 1/2 (2≤M≤N), toutes les observables valent leur valeur de bord : normes 1, énergie 0, tour bornée. | CONFIRMÉE (domaine: zéro sur la ligne ) | V161,V181 | 0 |
| `case_off_line` (l.502) | Pour re ρ ≠ 1/2 (2≤M<N), rayon ≠1, énergies strictement positives, module p^(−m(re−1/2)), erreur du point milieu explicitée. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V162,V167 | 0 |
| `integrated_system_is_zerohood_free` (l.537) | Pour tout z complexe et 2≤M≤N, le système intégré est une identité algébrique (bloc, rayon, réciprocité sous réflexion, puissance m, énergie ≥0). | CONFIRMÉE | AJOUT | 0 |
| `off_line_countermodel` (l.561) | Pour M<N, δ≠0 et toute hauteur γ, le rapport de tours en 1/2+δ+iγ a un module ≠ 1. | CONFIRMÉE (domaine: δ≠0 ) | AJOUT | 0 |
| `critical_countermodel` (l.575) | Pour M<N et tout γ, le rapport de tours en 1/2+iγ a un module 1. | CONFIRMÉE | AJOUT | 0 |
| `only_zerohood_input` (l.584) | Pour tout vrai zéro, reflectedRowCoeff ρ ≠ 0 et le transport de retour égale le caractère de tour en p N/p M. | CONFIRMÉE | V100 | 0 |

### `Round26EEGrammarFinitenessSubstitution`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `completeGrammarBlock_state_finite` (l.64) | Pour n≥2, chaque état du bloc grammatical complet vaut 1 ou 5 (mod 6). | CONFIRMÉE (domaine: 2≤n, i<k) | V174 | 0 |
| `exists_grammatical_return` (l.75) | Pour M≥2, il existe A<B, A≥2, avec sigma A = sigma B. | CONFIRMÉE (domaine: 2≤M) | AJOUT | 0 |
| `prod_one_sub_two_cross_of_return` (l.96) | Si sigma A = sigma B (2≤A≤B), le produit des (1−2·cross n) sur [A,B) vaut 1. | CONFIRMÉE (domaine: 2≤A≤B) | AJOUT | 6 |
| `trueZeroCarrier_return_eq_towerCharacter` (l.106) | Sur un bloc de retour grammatical (sigma A = sigma B), le retour du carrier égale le caractère de tour en p B/p A. | CONFIRMÉE (domaine: sigma A = sigma B ) | AJOUT | 1 |
| `norm_trueZeroCarrier_return` (l.119) | Sur un bloc de retour, le module du transport est (p B/p A)^(−(re ρ−1/2)). | CONFIRMÉE (domaine: sigma A = sigma B ) | V102 | 2 |
| `grammatical_return_does_not_decide_loop` (l.130) | Sur un bloc A<B, il existe z avec boucle bornée et z sans boucle bornée. | CONFIRMÉE (domaine: A<B ) | AJOUT | 0 |
| `return_holonomy_is_radially_invisible` (l.150) | Sur un bloc de retour, holonomie = 1 et module du transport = (p B/p A)^(−(re−1/2)). | CONFIRMÉE (domaine: sigma A = sigma B, 2≤A≤B ) | V158,V159 | 0 |
| `grammatical_return_is_not_transport_return` (l.160) | Pour re ρ ≠ 1/2 et sigma A = sigma B, les modules du carrier en A et B diffèrent. | CONFIRMÉE SOUS CONDITION (retour grammatical et zéro hors ligne) | V158,V159 | 2 |

### `Round26EFIdealTerminalObject`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `idealTerminalObject_imp_chebyshevExponentFamily` (l.86) | L'objet terminal idéal entraîne ChebyshevExponentFamily. | CONFIRMÉE SOUS CONDITION (IdealTerminalObject) | AJOUT | 0 |
| `idealTerminalObject_imp_bridge` (l.91) | L'objet terminal idéal entraîne, pour tout θ>1/2, le pont exposant de Chebyshev → borne log-dérivée. | CONFIRMÉE SOUS CONDITION (IdealTerminalObject) | AJOUT | 0 |
| `idealTerminalObject_of_family_and_bridge` (l.95) | Famille d'exposants de Chebyshev et pont donnent l'objet terminal idéal. | CONFIRMÉE (domaine: famille et pont ) | AJOUT | 0 |
| `idealTerminalObject_iff` (l.105) | IdealTerminalObject ⟺ (ChebyshevExponentFamily et pont pour tout θ>1/2). | CONFIRMÉE | AJOUT | 0 |
| `riemannHypothesis_of_idealTerminalObject` (l.113) | IdealTerminalObject entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126,O5 | 1 |
| `idealTerminalObject_forces_rh` (l.124) | IdealTerminalObject entraîne RiemannHypothesis (forme pont explicite). | IMPLIQUE RH SOUS PRÉMISSE | V126 | 1 |
| `rh_is_only_conditional_here` (l.166) | IdealTerminalObject entraîne RiemannHypothesis (certificat de non-habitation). | IMPLIQUE RH SOUS PRÉMISSE | V119,V141 | 0 |

### `Round26EGChebyshevMellinBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `mellinErrorIntegrand_aestronglyMeasurable` (l.30) | L'intégrande de Mellin de l'erreur de Chebyshev est mesurable sur (1,∞). [terme hors maître] | CONFIRMÉE | V121 | 1 |
| `integrableOn_mellinErrorIntegrand` (l.43) | Sous un exposant de Chebyshev θ et θ<Re s, l'intégrande de Mellin est intégrable sur (1,∞). | CONFIRMÉE SOUS CONDITION (ChebyshevErrorExponent θ et θ<Re s) | V121 | 1 |
| `sum_Icc_one_vonMangoldt_eq_psi` (l.62) | La somme des Λ(k), k=1..⌊t⌋, égale ψ(t). | CONFIRMÉE | V48,V121 | 2 |
| `isBigO_sum_Icc_vonMangoldt` (l.74) | Les sommes partielles de Λ sont O(n). | CONFIRMÉE | V121 | 1 |
| `LSeries_vonMangoldt_eq_mul_integral` (l.90) | Pour Re s>1, la série L de Λ égale s·∫₁^∞ ψ(t)t^(−s−1)dt. | CONFIRMÉE (domaine: 1<Re s) | V121 | 1 |
| `integral_psi_split` (l.102) | Sous exposant θ et 1<Re s, θ<Re s, ∫ψ t^(−s−1) = 1/(s−1) + transformée de Mellin de l'erreur. | CONFIRMÉE SOUS CONDITION (ChebyshevErrorExponent θ, θ<Re s) | V121 | 1 |
| `measurable_chebyshevErrorTail` (l.140) | La queue d'erreur de Chebyshev est mesurable. | CONFIRMÉE | AJOUT | 0 |
| `mellinChebyshevError_eq_mellin` (l.145) | mellinChebyshevError s est la transformée de Mellin de la queue en −s. | CONFIRMÉE | AJOUT | 1 |
| `locallyIntegrableOn_chebyshevErrorTail` (l.170) | La queue d'erreur est localement intégrable sur (0,∞). | CONFIRMÉE | AJOUT | 1 |
| `differentiableAt_mellinChebyshevError` (l.189) | Sous exposant θ, la transformée de Mellin de l'erreur est différentiable en tout s avec θ<Re s. | CONFIRMÉE SOUS CONDITION (ChebyshevErrorExponent θ, θ<Re s) | V121 | 3 |
| `negLogDeriv_eq_pole_add_mellinError` (l.216) | Sous exposant θ et Re s>1, θ<Re s : −ζ'/ζ(s) = s/(s−1) + s·M_E(s). | CONFIRMÉE SOUS CONDITION (ChebyshevErrorExponent θ) | V121 | 2 |
| `p1_mellinIdentity_of_chebyshevExponent` (l.233) | Sous un exposant de Chebyshev θ<1, P1_MellinIdentity vaut. | CONFIRMÉE SOUS CONDITION (θ<1 et ChebyshevErrorExponent θ) | AJOUT | 0 |
| `re_pos_of_one_lt_re` (l.244) | Si Re s>1 alors s≠0. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 2 |
| `ne_one_of_one_lt_re` (l.247) | Si Re s>1 alors s≠1. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 3 |
| `zetaPoleFactor_eq_mul` (l.250) | Pour w≠0,1, zetaPoleFactor w = (w−1)ζ(w). | CONFIRMÉE (domaine: w≠0, w≠1) | AJOUT | 3 |
| `analyticAt_zetaPoleFactor` (l.257) | zetaPoleFactor est analytique en tout s≠0. | CONFIRMÉE (domaine: s≠0) | AJOUT | 2 |
| `zetaPoleFactor_ne_zero_of_one_lt_re` (l.268) | zetaPoleFactor ne s'annule pas pour Re s>1. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 2 |
| `logDeriv_zetaPoleFactor_eq` (l.273) | Sous exposant θ, Re s>1, θ<Re s : logDeriv G = −(1 + s·M_E(s)). | CONFIRMÉE SOUS CONDITION (ChebyshevErrorExponent θ) | AJOUT | 1 |
| `deriv_zetaPoleFactor_eq_of_mellin` (l.298) | Sous exposant θ, Re s>1 : G' = −(1+s·M_E)·G (EDO régularisée). | CONFIRMÉE SOUS CONDITION (ChebyshevErrorExponent θ) | AJOUT | 1 |
| `isOpen_rightHalfPlane` (l.309) | Le demi-plan {Re s>θ} est ouvert. | CONFIRMÉE | AJOUT | 3 |
| `isPreconnected_rightHalfPlane` (l.313) | Le demi-plan {Re s>θ} est préconnexe. | CONFIRMÉE | AJOUT | 2 |
| `deriv_zetaPoleFactor_eq_continued` (l.317) | Pour 1/2<θ<1 avec exposant θ, l'EDO G' = −(1+s·M_E)G vaut sur tout {Re s>θ}. | CONFIRMÉE SOUS CONDITION (1/2<θ<1 et ChebyshevErrorExponent θ) | AJOUT | 2 |
| `zetaPoleFactor_ne_zero_of_lt_re` (l.354) | Pour 1/2<θ<1 avec exposant θ, zetaPoleFactor ne s'annule pas sur {Re>θ}. | CONFIRMÉE SOUS CONDITION (1/2<θ<1 et ChebyshevErrorExponent θ) | AJOUT | 1 |
| `exists_bound_of_continuousAt` (l.420) | Une fonction continue en ρ est localement bornée près de ρ. | CONFIRMÉE (domaine: continuité en ρ ) | AJOUT | 2 |
| `analyticAt_riemannZeta_of_ne_one` (l.432) | ζ est analytique en tout s≠1. | CONFIRMÉE (domaine: s≠1) | AJOUT | 1 |
| `logDerivBoundedNear_of_one_lt_re` (l.437) | Pour Re ρ>1, −ζ'/ζ est localement bornée près de ρ. | CONFIRMÉE (domaine: 1<Re ρ) | AJOUT | 1 |
| `chebyshevExponentGivesLogDerivBound_of_lt_one` (l.449) | Pour 1/2<θ<1, un exposant de Chebyshev θ donne la borne locale de log-dérivée. | CONFIRMÉE (domaine: 1/2<θ<1) | AJOUT | 1 |
| `chebyshevExponentGivesLogDerivBound_of_half_lt` (l.524) | Pour tout θ>1/2, ChebyshevExponentGivesLogDerivBound θ vaut. | CONFIRMÉE (domaine: 1/2<θ) | AJOUT | 1 |
| `hbridge_proved` (l.538) | Le pont hbridge (θ>1/2 ⟹ borne log-dérivée) est prouvé sans condition. | CONFIRMÉE (domaine: 1/2<θ) | AJOUT | 3 |
| `budgetFamily_of_chebyshevFamily_unconditional` (l.542) | ChebyshevExponentFamily entraîne PrimeChannelRegularityBudgetFamily. | CONFIRMÉE SOUS CONDITION (ChebyshevExponentFamily) | AJOUT | 0 |
| `riemannHypothesis_of_chebyshevFamily_only` (l.547) | ChebyshevExponentFamily seule entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126,O5 | 0 |

### `Round26EHUniformCarrierBoundTest`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `norm_trueZeroCarrier` (l.42) | Le module du carrier du vrai zéro est p(n)^(−(re ρ−1/2)). | CONFIRMÉE | V102 | 1 |
| `uniformCarrierBoundAt_iff_half_le_re` (l.47) | Pour un vrai zéro, la borne uniforme du carrier ⟺ 1/2 ≤ re ρ. | CONFIRMÉE | AJOUT | 3 |
| `uniformCarrierBound_iff_trueZeroRightHalfPlane` (l.75) | La borne uniforme du carrier sur tous les vrais zéros ⟺ TrueZeroRightHalfPlane. | CONFIRMÉE | AJOUT | 1 |
| `uniformCarrierBound_iff_rh` (l.87) | UniformCarrierBound ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 0 |
| `uniformCarrierBound_forces_rh` (l.97) | UniformCarrierBound entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126 | 0 |
| `uniformTowerBoundAt_iff_half_le_re` (l.118) | Pour tout z complexe, la borne uniforme de tour ⟺ 1/2 ≤ re z. | CONFIRMÉE | V10,V156 | 2 |
| `carrierBound_eq_towerBound` (l.145) | La borne du carrier d'un vrai zéro ⟺ la borne de tour du point ↑ρ. | CONFIRMÉE | AJOUT | 0 |
| `exists_unbounded_tower` (l.151) | Il existe z sans borne uniforme de tour. | CONFIRMÉE | AJOUT | 0 |
| `rest_decomposition_permits_two_radii` (l.166) | Pour re ρ ≠ 1/2, x>1 : la primitive lissée se décompose en gauche+droite+reste pour ρ et pour son réfléchi, avec des parties réelles différentes. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V162 | 0 |

### `Round26EIProvenanceInterfaceAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `interfaceRatio_eq` (l.78) | interfaceRatio M N ρ = (p N/p M)^(1/2−re ρ). [terme hors maître] | CONFIRMÉE | V102 | 7 |
| `interfaceRatio_canonicalBlock` (l.85) | Sur le bloc [2,4), interfaceRatio = (11/5)^(1/2−re ρ). | CONFIRMÉE | AJOUT | 2 |
| `interfaceRatio_pos` (l.91) | interfaceRatio M N ρ > 0. | CONFIRMÉE | AJOUT | 0 |
| `interfaceBoundAt_iff_half_le_re` (l.98) | Pour M<N, InterfaceBoundAt M N ρ ⟺ 1/2 ≤ re ρ. | CONFIRMÉE (domaine: M<N) | AJOUT | 3 |
| `interfaceRatio_le_of_le_re` (l.111) | Si a ≤ re ρ, interfaceRatio ≤ (p N/p M)^(1/2−a). | CONFIRMÉE (domaine: a ≤ re ρ, M<N ) | AJOUT | 1 |
| `lt_interfaceRatio_of_re_lt` (l.117) | Si re ρ < b, (p N/p M)^(1/2−b) < interfaceRatio. | CONFIRMÉE (domaine: re ρ < b, M<N ) | AJOUT | 0 |
| `interfaceRatio_lt_of_lt_re` (l.123) | Si a < re ρ, interfaceRatio < (p N/p M)^(1/2−a). | CONFIRMÉE (domaine: a < re ρ, M<N ) | AJOUT | 0 |
| `interfaceBand_iff` (l.141) | Pour M<N, InterfaceBand M N z ⟺ 0<re z<1. | CONFIRMÉE (domaine: M<N) | V7 | 6 |
| `interfaceBand_of_trueZero` (l.152) | Tout zéro non trivial vérifie InterfaceBand M N. | CONFIRMÉE (domaine: M<N) | V7 | 0 |
| `interfaceBand_canonicalBlock_of_trueZero` (l.160) | Pour tout zéro non trivial, (11/5)^(−1/2) < interfaceRatio < (11/5)^(1/2) sur le bloc [2,4). | CONFIRMÉE | V7 | 0 |
| `exists_not_interfaceBand` (l.177) | Pour M<N, il existe un point du plan violant la bande. | CONFIRMÉE (domaine: M<N) | AJOUT | 0 |
| `not_interfaceBand_one` (l.185) | Pour M<N, z=1 viole la bande. | CONFIRMÉE (domaine: M<N) | AJOUT | 1 |
| `interfaceBand_not_interfaceBoundAt` (l.196) | Pour M<N, il existe z dans la bande sans borne d'interface. | CONFIRMÉE (domaine: M<N) | AJOUT | 0 |
| `interfaceBoundAt_not_interfaceBand` (l.206) | Pour M<N, il existe z avec borne d'interface hors de la bande. | CONFIRMÉE (domaine: M<N) | AJOUT | 0 |
| `interfaceRatio_reflect` (l.218) | interfaceRatio en 1−conj ρ est l'inverse de interfaceRatio en ρ. | CONFIRMÉE | V80,V102 | 0 |
| `interfaceBand_reflect_iff` (l.227) | Pour M<N, la bande d'interface vaut en z ssi elle vaut en son réfléchi. | CONFIRMÉE (domaine: M<N) | V161,V65 | 0 |
| `interfaceBand_iff_abs_defect_lt` (l.243) | Pour M<N, InterfaceBand ⟺ \|re z − 1/2\| < 1/2. | CONFIRMÉE (domaine: M<N) | V7 | 0 |
| `re_ge_of_chebyshevExponent` (l.261) | Un exposant de Chebyshev θ>1/2 donne 1−θ ≤ re ρ pour tout zéro non trivial. | CONFIRMÉE SOUS CONDITION (θ>1/2 et ChebyshevErrorExponent θ) | V126 | 3 |
| `interfaceRatio_le_of_chebyshevExponent` (l.273) | Sous un exposant θ>1/2, interfaceRatio ≤ (p N/p M)^(θ−1/2) pour tout zéro non trivial. | CONFIRMÉE SOUS CONDITION (θ>1/2, exposant θ, M<N) | AJOUT | 0 |
| `interfaceRatio_canonicalBlock_le_of_chebyshevExponent` (l.285) | Sur le bloc [2,4) : interfaceRatio ≤ (11/5)^(θ−1/2) sous exposant θ>1/2. | CONFIRMÉE SOUS CONDITION (θ>1/2, exposant θ) | AJOUT | 0 |
| `chebyshevErrorExponent_of_family` (l.293) | Pour θ>1/2, la famille d'exposants de Chebyshev fournit un exposant θ. | CONFIRMÉE SOUS CONDITION (θ>1/2 et ChebyshevExponentFamily) | AJOUT | 0 |
| `one_lt_chebyshevInterfaceBound` (l.302) | Pour θ>1/2 et M<N, (p N/p M)^(θ−1/2) > 1. | CONFIRMÉE (domaine: θ>1/2, M<N) | AJOUT | 0 |
| `chebyshevInterfaceBound_eq_one_iff` (l.311) | Pour M<N, (p N/p M)^(θ−1/2)=1 ssi θ=1/2. | CONFIRMÉE (domaine: M<N) | AJOUT | 0 |
| `interfaceBoundAt_of_chebyshevFamily` (l.330) | La famille complète d'exposants de Chebyshev donne InterfaceBoundAt pour tout zéro non trivial. | CONFIRMÉE SOUS CONDITION (ChebyshevExponentFamily) | AJOUT | 0 |

### `Round26EJPrimeHeightSquareBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `one_lt_bridgeRatio` (l.65) | bridgeRatio > 1. [terme hors maître] | CONFIRMÉE | AJOUT | 2 |
| `bridgeRatio_pos` (l.68) | bridgeRatio > 0. | CONFIRMÉE | AJOUT | 0 |
| `primeHeightSquareBridge_def` (l.82) | PrimeHeightSquareBridge W ⟺ pour tout zéro non trivial, ‖W(Im ρ)‖² = (11/5)^(re ρ−1/2) − 1. | CONFIRMÉE | AJOUT | 0 |
| `primeHeightSquareBridge_heightOnly` (l.90) | Sous PrimeHeightSquareBridge W, deux zéros de même hauteur ont le même bridgeRatio^(re−1/2). | CONFIRMÉE (domaine: PrimeHeightSquareBridge W ) | V62,V158 | 1 |
| `bridgeRatio_rpow_le_rpow_iff` (l.108) | bridgeRatio^x ≤ bridgeRatio^y ⟺ x ≤ y. | CONFIRMÉE | AJOUT | 2 |
| `primeHeightSquareBridge_half_le_re` (l.113) | Sous PrimeHeightSquareBridge W, tout zéro non trivial a 1/2 ≤ re ρ. | CONFIRMÉE (domaine: PrimeHeightSquareBridge W ) | AJOUT | 1 |
| `primeHeightSquareBridge_trueZeroRightHalfPlane` (l.128) | PrimeHeightSquareBridge W entraîne TrueZeroRightHalfPlane. | CONFIRMÉE (domaine: PrimeHeightSquareBridge W ) | AJOUT | 1 |
| `riemannHypothesis_of_primeHeightSquareBridge` (l.134) | Toute réalisation W de PrimeHeightSquareBridge entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126 | 1 |
| `reflectConjZero_im_of_bridge` (l.145) | Le zéro réfléchi-conjugué a la même partie imaginaire. | CONFIRMÉE | V65 | 0 |
| `sub_conj_im` (l.152) | (1−conj ρ).im = ρ.im. | CONFIRMÉE | V65 | 1 |
| `sub_conj_re` (l.155) | (1−conj ρ).re = 1−ρ.re. | CONFIRMÉE | V65 | 1 |
| `primeHeightSquareBridge_re_eq_half_via_reflection` (l.157) | Sous PrimeHeightSquareBridge W, tout zéro non trivial a re ρ = 1/2. | CONFIRMÉE SOUS CONDITION (PrimeHeightSquareBridge W) | V126 | 2 |
| `riemannHypothesis_of_primeHeightSquareBridge_reflection` (l.171) | PrimeHeightSquareBridge W entraîne RiemannHypothesis (route par réflexion). | IMPLIQUE RH SOUS PRÉMISSE | V126 | 0 |
| `bridge_identity_not_tautological` (l.182) | Il existe W et z violant l'identité du pont (l'identité est falsifiable). | CONFIRMÉE | AJOUT | 0 |
| `primeHeightSquareBridge_norm_eq_zero` (l.197) | Sous PrimeHeightSquareBridge W, ‖W(Im ρ)‖ = 0 à chaque hauteur de zéro non trivial. | CONFIRMÉE (domaine: PrimeHeightSquareBridge W ) | AJOUT | 0 |
| `primeHeightSquareBridge_zero_of_rh` (l.214) | RiemannHypothesis entraîne PrimeHeightSquareBridge (W ≡ 0). | CONFIRMÉE SOUS CONDITION (RH: hypothèse RiemannHypothesis (RH → objet habité par 0)) | AJOUT | 1 |
| `primeHeightSquareBridge_zero_iff_rh` (l.221) | PrimeHeightSquareBridge (fun _ => 0) ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 0 |

### `Round26EKPrimeHeightCrossFiber`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `primeHeightFiberPoint_re` (l.71) | La partie réelle du point de fibre (γ,σ) est σ. [terme hors maître] | CONFIRMÉE | AJOUT | 5 |
| `primeHeightFiberPoint_im` (l.75) | La partie imaginaire du point de fibre (γ,σ) est γ. | CONFIRMÉE | AJOUT | 3 |
| `primeGrammarSectorVector_apply` (l.84) | Le vecteur de secteurs grammaticaux en s, secteur τ, égale grammarSectorPrimeDirichlet τ s. | CONFIRMÉE | AJOUT | 0 |
| `primeHeightCrossFiber_eq_crossComponent` (l.95) | La fibre croisée en (γ,σ) est la coordonnée cross du vecteur de secteurs en σ+iγ. | CONFIRMÉE | AJOUT | 0 |
| `primeHeightCrossFiber_eq_sector_sum` (l.100) | La fibre croisée est la somme des secteurs τ15 et τ51 au point de fibre. | CONFIRMÉE | AJOUT | 1 |
| `primeHeightCrossFiber_add_coboundaryCoord` (l.106) | Fibre croisée + coordonnée de cobord = 2×secteur τ15. | CONFIRMÉE | AJOUT | 0 |
| `sum_transform6` (l.118) | La somme sur Transform6 est la somme des quatre transformations τ11, τ15, τ51, τ55. | CONFIRMÉE | AJOUT | 1 |
| `sectorGlobalCoord_primeGrammarSectorVector` (l.128) | Pour Re s>1, la coordonnée globale du vecteur de secteurs est le canal grammatical premier continué. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 1 |
| `primeGrammarChannelContinuation_eq_diagonal_add_crossFiber` (l.137) | Pour σ>1, le canal continué = secteurs diagonaux τ11+τ55 + fibre croisée. | CONFIRMÉE (domaine: 1<σ) | AJOUT | 3 |
| `crossFiber_coefficient_eq_grammarCrossV2` (l.152) | Pour n≥2, le coefficient τ15+τ51 est grammarCrossV2(p n mod 6, p(n+1) mod 6). | CONFIRMÉE (domaine: 2≤n) | V174 | 0 |
| `primeHeightCrossFiber_eq_tsum` (l.165) | Pour σ>1, la fibre croisée est la série de Dirichlet du coefficient cross contre le poids premier. | CONFIRMÉE (domaine: 1<σ) | AJOUT | 0 |
| `crossFiber_signature_not_coboundary` (l.194) | Aucune fonction psi ne réalise les indicateurs de croisement (1→5, 5→1) comme cobord. | CONFIRMÉE | AJOUT | 0 |
| `primeHeightFiberPoint_self` (l.205) | Le point de fibre (Im ρ, Re ρ) est ρ. | CONFIRMÉE | AJOUT | 6 |
| `primeHeightFiberPoint_reflected` (l.210) | Le point de fibre (Im ρ, 1−Re ρ) est le réfléchi 1−conj ρ. | CONFIRMÉE | V63,V65 | 2 |
| `reflected_same_height` (l.216) | Le réfléchi a la même hauteur. | CONFIRMÉE | V65 | 0 |
| `reflected_radial_position` (l.221) | Le réfléchi a la position radiale 1−re ρ. | CONFIRMÉE | V65 | 0 |
| `primeHeightCrossFiber_at_trueZero` (l.226) | Un vrai zéro ρ est le point de base de la fibre de sa hauteur en position Re ρ. | CONFIRMÉE (domaine: ρ zéro non trivial ) | AJOUT | 1 |
| `primeHeightCrossFiber_reflected_same_height` (l.235) | Le point (Im ρ, 1−Re ρ) de la même fibre est un zéro non trivial. | CONFIRMÉE (domaine: ρ zéro non trivial ) | V62,V65 | 2 |
| `trueZero_gives_reflected_pair_in_same_primeHeightCrossFiber` (l.243) | Tout zéro non trivial donne dans une même fibre de hauteur deux zéros aux positions β et 1−β. | CONFIRMÉE (domaine: ρ zéro non trivial ) | V62,V65,V162 | 3 |
| `primeHeightCrossFiber_reflected_pair_same_function` (l.257) | Les valeurs de fibre en β et 1−β sont deux évaluations de la même fonction de σ. | CONFIRMÉE | AJOUT | 0 |
| `meromorphicOrderAt_primeGrammarChannel_at_fiberPoint` (l.269) | Pour un zéro non trivial avec re>1/2, le canal continué a un ordre méromorphe −1 au point de base. | CONFIRMÉE SOUS CONDITION (zéro non trivial, re ρ>1/2) | AJOUT | 2 |
| `meromorphicOrderAt_primeGrammarChannel_at_reflected_fiberPoint` (l.280) | Même énoncé à la position 1−β lorsque 1/2<1−re ρ. | CONFIRMÉE (domaine: zéro non trivial, 1/2<1−re ρ ) | AJOUT | 1 |
| `primeHeightCrossFiber_reflected_pair_pole_alternative` (l.293) | Pour tout zéro non trivial : re=1/2, ou pôle simple à l'une des deux positions de la fibre. | CONFIRMÉE | V162 | 3 |
| `primeHeightFiberPoint_tower_floor_eq_base_dilation` (l.314) | Sur le point de fibre, l'étage m de towerMode égale l'étage 1 dilaté (u/m). | CONFIRMÉE (domaine: 0<m ) | AJOUT | 0 |
| `primeHeightCrossFiber_exists_unconditionally` (l.333) | Pour tout (γ,σ), la fibre croisée existe (∃ z, fibre = z). | CONFIRMÉE | AJOUT | 0 |

### `Round26ELPrimeHeightCrossOperatorFiber`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `primeHeightCrossPairFiber_fst` (l.100) | La première composante de la fibre paire (γ,σ) est la Dirichlet de secteur premier τ15 au point de fibre. [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `primeHeightCrossPairFiber_snd` (l.104) | La seconde composante est la Dirichlet de secteur premier τ51 au point de fibre. | CONFIRMÉE | AJOUT | 0 |
| `primeHeightCrossPairFiber_sum_eq_crossFiber` (l.108) | La somme des deux composantes de la fibre paire redonne la fibre cross. | CONFIRMÉE | AJOUT | 0 |
| `primeCrossSwapOperator_eq` (l.125) | L'opérateur swap premier est la matrice [[0,1],[1,0]]. [terme hors maître] | CONFIRMÉE | AJOUT | 3 |
| `primeCrossSwapOperator_sq` (l.130) | Le carré du swap premier est l'identité. | CONFIRMÉE | AJOUT | 2 |
| `primeCrossSwapOperator_conjTranspose` (l.135) | Le swap premier est égal à son adjoint. | CONFIRMÉE | AJOUT | 3 |
| `primeCrossSwapOperator_isSelfAdjoint` (l.141) | Le swap premier est auto-adjoint. | CONFIRMÉE | AJOUT | 4 |
| `primeCrossSwapOperator_mul_conjTranspose` (l.144) | Swap · swap† = 1. | CONFIRMÉE | AJOUT | 2 |
| `primeCrossSwapOperator_conjTranspose_mul` (l.149) | Swap† · swap = 1. | CONFIRMÉE | AJOUT | 2 |
| `primeCrossSwapOperator_mem_unitary` (l.154) | Le swap premier est unitaire. | CONFIRMÉE | AJOUT | 4 |
| `primeCrossSwapOperator_isStarNormal` (l.158) | Le swap premier est *-normal. | CONFIRMÉE | AJOUT | 3 |
| `crossBlockRatio_eq` (l.170) | Le rapport de bloc croisé vaut 11/5. | CONFIRMÉE | AJOUT | 2 |
| `one_lt_crossBlockRatio` (l.174) | Le rapport de bloc croisé est > 1. | CONFIRMÉE | AJOUT | 2 |
| `crossBlockRatio_pos` (l.177) | Le rapport de bloc croisé est > 0. | CONFIRMÉE | AJOUT | 6 |
| `crossBlockRatio_rpow_le_rpow_iff` (l.180) | P^x ≤ P^y ⟺ x ≤ y pour P le rapport de bloc croisé. | CONFIRMÉE | AJOUT | 1 |
| `crossBlockRatio_rpow_inj` (l.184) | P^x = P^y entraîne x = y. | CONFIRMÉE (domaine: hypothèse d'égalité des puissances) | AJOUT | 4 |
| `crossBlockRatio_rpow_pos` (l.189) | P^x > 0 pour tout x réel. | CONFIRMÉE | AJOUT | 0 |
| `crossBlockRatio_rpow_neg_mul_self` (l.192) | P^(−d)·P^d = 1. | CONFIRMÉE | AJOUT | 2 |
| `radialCrossOperator_zero` (l.204) | À défaut nul (d=0), l'opérateur radial est le swap premier. [terme hors maître] | CONFIRMÉE | AJOUT | 5 |
| `radialCrossOperator_apply_zero_one` (l.209) | L'entrée (0,1) de l'opérateur radial d vaut P^(−d). | CONFIRMÉE | AJOUT | 3 |
| `radialCrossOperator_apply_one_zero` (l.213) | L'entrée (1,0) de l'opérateur radial d vaut P^d. | CONFIRMÉE | AJOUT | 3 |
| `radialCrossOperator_sq_eq_one` (l.217) | L'opérateur radial d est une involution pour tout d. | CONFIRMÉE | AJOUT | 2 |
| `radialCrossOperator_conjTranspose` (l.231) | L'adjoint de l'opérateur radial d est [[0,P^d],[P^(−d),0]]. | CONFIRMÉE | AJOUT | 4 |
| `radialCrossOperator_mul_conjTranspose` (l.240) | T_d T_d† = diag(P^(−2d), P^(2d)). | CONFIRMÉE | AJOUT | 2 |
| `radialCrossOperator_conjTranspose_mul` (l.256) | T_d† T_d = diag(P^(2d), P^(−2d)). | CONFIRMÉE | AJOUT | 2 |
| `radialCrossOperator_normal_iff_zero_defect` (l.274) | L'opérateur radial d est *-normal ssi d = 0 (sans zéro, sans RH). | CONFIRMÉE | AJOUT | 3 |
| `radialCrossOperator_selfAdjoint_iff_zero_defect` (l.295) | L'opérateur radial d est auto-adjoint ssi d = 0. | CONFIRMÉE | AJOUT | 0 |
| `radialCrossOperator_unitary_iff_zero_defect` (l.313) | L'opérateur radial d est unitaire ssi d = 0. | CONFIRMÉE | AJOUT | 0 |
| `radialCrossOperator_injective` (l.329) | d ↦ T_d est injective. | CONFIRMÉE | AJOUT | 2 |
| `radialCrossOperator_one_sq_eq_one` (l.342) | T_1 est une involution. | CONFIRMÉE | AJOUT | 1 |
| `radialCrossOperator_one_not_normal` (l.345) | T_1 n'est pas *-normal. | CONFIRMÉE | AJOUT | 1 |
| `involution_alone_does_not_force_zero_defect` (l.350) | Il existe d≠0 dont T_d est involutif, non normal et distinct du swap : l'involution seule ne force pas défaut nul. | RÉFUTATION COMPILÉE | AJOUT | 0 |
| `crossHeightPhase_ne_zero` (l.371) | La phase de hauteur croisée est non nulle pour tout γ. | CONFIRMÉE | AJOUT | 7 |
| `trueZeroReflectedCrossTransport_entries_eq_returnTransport` (l.385) | Les entrées (0,1) et (1,0) du transport croisé sont les quotients de retour du zéro et de son réfléchi sur le bloc [2,4). | CONFIRMÉE | V162 | 2 |
| `towerCharacter_reflected_eq` (l.400) | Le caractère de tour au zéro réfléchi vaut P^(re−1/2)·phase de hauteur. [terme hors maître] | CONFIRMÉE | V35,V158 | 1 |
| `towerCharacter_self_eq` (l.412) | Le caractère de tour en ρ vaut P^(−(re−1/2))·phase de hauteur. | CONFIRMÉE | V158 | 1 |
| `trueZeroReflectedCrossOperator_eq_radial_matrix` (l.417) | L'opérateur croisé du zéro réfléchi est l'opérateur radial de défaut re−1/2. | CONFIRMÉE | V158,V167 | 12 |
| `trueZeroReflectedCrossOperator_eq_radial_matrix_concrete` (l.436) | Forme concrète avec P=11/5 : [[0,(11/5)^(−d)],[(11/5)^d,0]]. | CONFIRMÉE | V158,V167 | 4 |
| `trueZeroReflectedCrossOperator_sq_eq_one` (l.445) | Le carré de l'opérateur croisé du zéro réfléchi est 1 pour tout ρ. | CONFIRMÉE | AJOUT | 2 |
| `trueZeroReflectedCrossOperator_conjTranspose` (l.452) | Adjoint exact de l'opérateur croisé du zéro réfléchi. | CONFIRMÉE | AJOUT | 3 |
| `trueZeroReflectedCrossOperator_mul_conjTranspose` (l.459) | T T† = diag(P^(−2d), P^(2d)) avec d = re−1/2. | CONFIRMÉE | AJOUT | 3 |
| `trueZeroReflectedCrossOperator_conjTranspose_mul` (l.466) | T† T = diag(P^(2d), P^(−2d)). | CONFIRMÉE | AJOUT | 3 |
| `trueZeroReflectedCrossOperator_normal_iff_critical` (l.473) | L'opérateur croisé est *-normal ssi re ρ = 1/2 (par zéro, sans hypothèse). | CONFIRMÉE | V161 | 7 |
| `trueZeroReflectedCrossOperator_normal_forces_critical` (l.481) | La *-normalité de l'opérateur croisé de ρ force re ρ = 1/2. | CONFIRMÉE SOUS CONDITION (opérateur de ρ *-normal) | V161 | 4 |
| `trueZeroReflectedCrossOperator_eq_swap_iff_critical` (l.485) | L'opérateur croisé égale le swap premier ssi re ρ = 1/2. | CONFIRMÉE | V161 | 5 |
| `trueZeroReflectedCrossOperator_offdiag_product_eq_one` (l.503) | Le produit des deux entrées hors diagonale vaut 1 inconditionnellement. | CONFIRMÉE | V158 | 7 |
| `trueZeroReflectedCrossOperator_normal_iff_offdiag_eq` (l.514) | *-normalité ⟺ égalité des entrées (0,1) et (1,0). | CONFIRMÉE | V161 | 7 |
| `reflection_gives_product_star_needs_ratio` (l.534) | Le produit des entrées vaut 1 inconditionnellement ; l'égalité des entrées ⟺ re ρ = 1/2. | CONFIRMÉE | V161 | 1 |
| `all_trueZero_cross_operators_normal_iff_rh` (l.545) | Tout opérateur croisé de zéro non trivial est *-normal ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V126,O10 | 0 |
| `all_trueZero_cross_operators_eq_swap_iff_rh` (l.559) | Tout opérateur croisé de zéro non trivial égale le swap premier ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V126,O10 | 0 |
| `trueZeroReflectedCrossTransport_entries_from_fiber_positions` (l.576) | Les entrées (0,1),(1,0) du transport se lisent dans la même fibre de hauteur Im ρ, aux positions β et 1−β. | CONFIRMÉE | V158,V162 | 3 |
| `primeHeightCrossPairFiber_common_tower_multiplier` (l.597) | Les deux composantes de la fibre paire portent le même multiplicateur towerCharacter(p n), avec des indicateurs de support τ15/τ51. | CONFIRMÉE | AJOUT | 3 |
| `grammarTransformIndicator_tau15_mul_tau51` (l.612) | Les supports de τ15 et τ51 sont disjoints : produit des indicateurs nul. | CONFIRMÉE | AJOUT | 0 |
| `primeCrossSwapOperator_offdiag_symmetric` (l.624) | grammarCrossV2 1 5 = grammarCrossV2 5 1 (symétrie première, libre de ρ). | CONFIRMÉE | AJOUT | 1 |
| `star_compatibility_exact_gap` (l.629) | Symétrie première libre de ρ, produit des entrées = 1, et égalité des entrées ⟺ re ρ = 1/2. | CONFIRMÉE | V161 | 0 |

### `Round26EMPrimeHeightCrossClosureObject`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `PrimeHeightCrossZeroCertificate.zeroCarrierSurface` (l.79) | Sous un certificat, le carrier de vrai zéro égale la tour tordue à tout n. [terme hors maître] | CONFIRMÉE (domaine: PrimeHeightCrossZeroCertificate ρ hρ ) | AJOUT | 0 |
| `PrimeHeightCrossZeroCertificate.reflectedZeroSurface` (l.82) | Sous un certificat, le réfléchi-conjugué est un zéro non trivial. | CONFIRMÉE (domaine: certificat ) | V62,V63 | 0 |
| `PrimeHeightCrossZeroCertificate.sameHeightSurface` (l.85) | Sous un certificat, le réfléchi-conjugué a la même partie imaginaire. | CONFIRMÉE (domaine: certificat ) | V65 | 0 |
| `PrimeHeightCrossZeroCertificate.reflectedRadialSurface` (l.88) | Sous un certificat, la partie réelle du réfléchi vaut 1−re ρ. | CONFIRMÉE (domaine: certificat ) | V65 | 0 |
| `PrimeHeightCrossZeroCertificate.fiberPairSurface` (l.93) | Sous un certificat, les points de fibre en β et 1−β sont des zéros non triviaux de même hauteur. | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `PrimeHeightCrossZeroCertificate.tau15Surface` (l.100) | Sous un certificat, la composante τ15 se lit à la position β. | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `PrimeHeightCrossZeroCertificate.tau51Surface` (l.105) | Sous un certificat, la composante τ51 se lit à la position 1−β. | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `PrimeHeightCrossZeroCertificate.orientedFiberSurface` (l.110) | Sous un certificat, les entrées du transport sont les quotients de tourCharacter aux positions β et 1−β. | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `PrimeHeightCrossZeroCertificate.towerSurface` (l.119) | Sous un certificat, le carrier réalise le module de la tour harmonique tordue. | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `PrimeHeightCrossZeroCertificate.towerMultiplierSurface` (l.123) | Sous un certificat, les deux composantes ont le multiplicateur commun towerCharacter(p n). | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `PrimeHeightCrossZeroCertificate.meromorphicSurface` (l.135) | Sous un certificat, re=1/2 ou le canal premier continué a un pôle simple en l'une des deux positions de fibre. | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `PrimeHeightCrossZeroCertificate.phaseSurface` (l.144) | Sous un certificat, ρ et son réfléchi ont la même phase de hauteur non nulle et l'opérateur = phase⁻¹ · transport. | CONFIRMÉE (domaine: certificat ) | V158 | 0 |
| `PrimeHeightCrossZeroCertificate.trueZeroTransportSurface` (l.153) | Sous un certificat, les entrées du transport sont les quotients de retour au zéro et à son réfléchi. | CONFIRMÉE (domaine: certificat ) | V162 | 0 |
| `PrimeHeightCrossZeroCertificate.radialDefectSurface` (l.160) | Sous un certificat, l'opérateur croisé vaut [[0,(11/5)^(−d)],[(11/5)^d,0]], d=re−1/2 signé. | CONFIRMÉE (domaine: certificat ) | V158,V167 | 0 |
| `PrimeHeightCrossZeroCertificate.radialOperatorSurface` (l.165) | Sous un certificat, l'opérateur croisé est l'opérateur radial de défaut re−1/2. | CONFIRMÉE (domaine: certificat ) | V158 | 0 |
| `PrimeHeightCrossZeroCertificate.involutionSurface` (l.169) | Sous un certificat, T_ρ² = 1. | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `PrimeHeightCrossZeroCertificate.offdiagProductSurface` (l.173) | Sous un certificat, le produit des entrées hors diagonale vaut 1. | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `PrimeHeightCrossZeroCertificate.adjointSurface` (l.176) | Sous un certificat, adjoint exact de l'opérateur croisé. | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `PrimeHeightCrossZeroCertificate.ttStarSurface` (l.181) | Sous un certificat, T T† = diag(P^(−2d), P^(2d)). | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `PrimeHeightCrossZeroCertificate.tStarTSurface` (l.186) | Sous un certificat, T† T = diag(P^(2d), P^(−2d)). | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `PrimeHeightCrossZeroCertificate.orientedBalance` (l.195) | Sous un certificat, les entrées (0,1) et (1,0) de l'opérateur croisé sont égales (champ terminal). | CONFIRMÉE (domaine: certificat (champ non constructible ) | V161 | 1 |
| `PrimeHeightCrossClosureObject.primeCrossSelfAdjoint` (l.249) | Sous un objet de clôture, le swap premier est auto-adjoint. | CONFIRMÉE SOUS CONDITION (PrimeHeightCrossClosureObject) | AJOUT | 0 |
| `PrimeHeightCrossClosureObject.primeCrossUnitary` (l.251) | Sous un objet de clôture, le swap premier est unitaire. | CONFIRMÉE SOUS CONDITION (PrimeHeightCrossClosureObject) | AJOUT | 0 |
| `PrimeHeightCrossClosureObject.primeCrossNormal` (l.253) | Sous un objet de clôture, le swap premier est normal. | CONFIRMÉE SOUS CONDITION (PrimeHeightCrossClosureObject) | AJOUT | 0 |
| `PrimeHeightCrossClosureObject.primeCrossSwapSurface` (l.255) | Sous un objet de clôture, swap = [[0,cross 1 5],[cross 5 1,0]]. | CONFIRMÉE SOUS CONDITION (PrimeHeightCrossClosureObject) | AJOUT | 0 |
| `PrimeHeightCrossClosureObject.zeroCertificate` (l.259) | Sous un objet de clôture, chaque zéro non trivial porte un certificat complet. | CONFIRMÉE SOUS CONDITION (PrimeHeightCrossClosureObject) | AJOUT | 2 |
| `PrimeHeightCrossZeroCertificate.operator_normal` (l.264) | Sous un certificat, l'opérateur croisé de ρ est *-normal (dérivé de orientedBalance). | CONFIRMÉE (domaine: certificat ) | V161 | 1 |
| `PrimeHeightCrossZeroCertificate.re_eq_half` (l.272) | Sous un certificat, re ρ = 1/2. | CONFIRMÉE (domaine: certificat (dont l'égalité orientée orientedBalance) ) | V161 | 2 |
| `PrimeHeightCrossZeroCertificate.operator_eq_primeSwap` (l.279) | Sous un certificat, l'opérateur croisé de ρ égale le swap premier. | CONFIRMÉE (domaine: certificat ) | V161 | 1 |
| `riemannHypothesis_of_primeHeightCrossClosureObject` (l.286) | Un PrimeHeightCrossClosureObject entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | O10 | 2 |
| `riemannHypothesis_of_primeHeightCrossClosureObject_via_swap` (l.292) | Même conclusion, par l'égalité opératorielle T_ρ = swap. | IMPLIQUE RH SOUS PRÉMISSE | O10 | 0 |
| `primeHeightCrossClosureObject_iff_rh` (l.305) | PrimeHeightCrossClosureObject ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V126,O10 | 0 |
| `offdiagProductSurface_holds_for_every_rho` (l.368) | Le produit des entrées hors diagonale vaut 1 pour tout ρ complexe. | CONFIRMÉE | AJOUT | 0 |
| `involutionSurface_holds_for_every_rho` (l.375) | T_ρ² = 1 pour tout ρ complexe. | CONFIRMÉE | AJOUT | 0 |
| `orientedBalance_is_the_discriminating_field` (l.381) | L'égalité des entrées (0,1) et (1,0) de l'opérateur croisé ⟺ re ρ = 1/2. | CONFIRMÉE | V161 | 0 |
| `riemannHypothesis_of_orientedBalance` (l.395) | Si tout zéro non trivial a ses deux entrées croisées égales, alors RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | O10 | 0 |

### `Round26ENGrammarTowerZeroFidelityObject`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `grammarTransformIndicator_tau15_eq_one_iff` (l.61) | Pour n≥2, l'indicateur τ15 vaut 1 ssi p_n ≡ 1 et p_{n+1} ≡ 5 mod 6. | CONFIRMÉE (domaine: 2 ≤ n) | V174 | 3 |
| `grammarTransformIndicator_tau51_eq_one_iff` (l.70) | Pour n≥2, l'indicateur τ51 vaut 1 ssi p_n ≡ 5 et p_{n+1} ≡ 1 mod 6. | CONFIRMÉE (domaine: 2 ≤ n) | V174 | 3 |
| `GrammarTowerZeroFidelityObject.zeroCarrierSurface` (l.97) | Sous l'objet de fidélité, le carrier de vrai zéro égale la tour tordue à tout n. | CONFIRMÉE (domaine: GrammarTowerZeroFidelityObject (prémisse ⟺ RH par fidelity_is_strictly_necessary) ) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.individualMemberSurface` (l.102) | Sous l'objet de fidélité, chaque zéro est le point de base de sa propre fibre à sa propre position. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.reflectedZeroSurface` (l.106) | Sous l'objet de fidélité, le réfléchi est un zéro non trivial. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | V62 | 1 |
| `GrammarTowerZeroFidelityObject.sameHeightSurface` (l.111) | Sous l'objet de fidélité, la réflexion préserve la hauteur. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | V65 | 1 |
| `GrammarTowerZeroFidelityObject.reflectedRadialSurface` (l.115) | Sous l'objet de fidélité, la réflexion complémente la position radiale. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | V65 | 1 |
| `GrammarTowerZeroFidelityObject.grammarRigidSurface` (l.121) | Sous l'objet de fidélité, le bloc de grammaire complet premier canonique est GrammarRigid. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | V174 | 1 |
| `GrammarTowerZeroFidelityObject.grammarProjectionSurface` (l.125) | Sous l'objet de fidélité, écart mod 6 ∈ {0,2,4} ⟺ transition d'états correspondante. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | V174 | 1 |
| `GrammarTowerZeroFidelityObject.grammarCompositionSurface` (l.132) | Sous l'objet de fidélité, le produit des (1−2·cross n) sur [M,N) télescope en σ_M σ_N. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.grammarReturnSurface` (l.137) | Sous l'objet de fidélité, sur un bloc de retour σ_A=σ_B, l'holonomie vaut 1. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject et σ_A=σ_B) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.chi3GrammarSurface` (l.142) | Sous l'objet de fidélité, χ3(p_n) = σ_n pour n≥2. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.tau15Surface` (l.146) | Sous l'objet de fidélité, τ15 vaut 1 ssi transition 1→5 mod 6. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | V174 | 1 |
| `GrammarTowerZeroFidelityObject.tau51Surface` (l.151) | Sous l'objet de fidélité, τ51 vaut 1 ssi transition 5→1 mod 6. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | V174 | 1 |
| `GrammarTowerZeroFidelityObject.inverseTransitionSurface` (l.157) | Sous l'objet de fidélité, transformOf s t est τ11/τ15/τ51/τ55 exactement selon (s,t) dans {1,5}². | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject, s,t ∈ {1,5}) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.crossNonCoboundarySurface` (l.165) | Sous l'objet de fidélité, le canal cross n'est le cobord d'aucun potentiel ψ. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.fiberPairSurface` (l.172) | Sous l'objet de fidélité, les positions β et 1−β sont deux points de base d'une même fibre de hauteur, chacun zéro non trivial. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.tau15FiberSurface` (l.179) | Sous l'objet de fidélité, la composante τ15 de la fibre est le vecteur de secteur τ15 non sommé. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.tau51FiberSurface` (l.184) | Sous l'objet de fidélité, la composante τ51 de la fibre est le vecteur de secteur τ51 non sommé. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.harmonicTowerSurface` (l.191) | Sous l'objet de fidélité, le carrier de vrai zéro réalise le module de la tour harmonique tordue. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.towerMultiplierSurface` (l.196) | Sous l'objet de fidélité, les deux composantes de fibre portent le même multiplicateur towerCharacter(p n). | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.grammarTowerSupportSurface` (l.208) | Sous l'objet de fidélité, la grammaire sélectionne le support des étages de tour (1+σ^m≠0 ⟺ σ=1 ou m pair) et towerCharacter(p)^(2k)=towerCharacter(p²)^k. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.trueZeroTransportSurface` (l.216) | Sous l'objet de fidélité, les entrées du transport sont les quotients de retour du zéro et de son réfléchi sur [2,4). | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | V162 | 1 |
| `GrammarTowerZeroFidelityObject.commonTransportSurface` (l.223) | Sous l'objet de fidélité, les entrées du transport sont le même quotient de tour aux positions β et 1−β. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | V162 | 1 |
| `GrammarTowerZeroFidelityObject.commonHeightPhaseSurface` (l.233) | Sous l'objet de fidélité, ρ et son réfléchi ont la même phase de hauteur inversible et l'opérateur = phase⁻¹·transport. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | V158 | 1 |
| `GrammarTowerZeroFidelityObject.primeChannelSurface` (l.246) | Sous l'objet de fidélité, le canal premier continué = diagonale τ11+τ55 + fibre cross (σ>1), et la provenance fibrée canonique tient. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 2 |
| `GrammarTowerZeroFidelityObject.meromorphicSurface` (l.255) | Sous l'objet de fidélité, re=1/2 ou pôle simple du canal premier continué en l'une des deux positions. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.radialDefectSurface` (l.265) | Sous l'objet de fidélité, l'opérateur croisé vaut [[0,(11/5)^(−d)],[(11/5)^d,0]], d=re−1/2. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | V158,V167 | 1 |
| `GrammarTowerZeroFidelityObject.radialOperatorSurface` (l.271) | Sous l'objet de fidélité, l'opérateur croisé est l'opérateur radial de défaut re−1/2. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | V158 | 1 |
| `GrammarTowerZeroFidelityObject.reflectionReciprocitySurface` (l.275) | Sous l'objet de fidélité, le produit des entrées croisées vaut 1. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.involutionSurface` (l.278) | Sous l'objet de fidélité, T_ρ²=1. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.adjointSurface` (l.282) | Sous l'objet de fidélité, adjoint exact de l'opérateur croisé. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.ttStarSurface` (l.287) | Sous l'objet de fidélité, T T† = diag(P^(−2d), P^(2d)). | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.tStarTSurface` (l.292) | Sous l'objet de fidélité, T† T = diag(P^(2d), P^(−2d)). | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObject.orientedFidelitySurface` (l.300) | Sous l'objet de fidélité, pour tout zéro non trivial les entrées (0,1) et (1,0) de l'opérateur croisé sont égales (donnée terminale). | CONFIRMÉE (domaine: GrammarTowerZeroFidelityObject ) | V161,O10 | 1 |
| `GrammarTowerZeroFidelityObject.trueZero_operator_normal` (l.309) | Sous l'objet de fidélité, l'opérateur croisé de tout zéro non trivial est *-normal. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | V161 | 1 |
| `GrammarTowerZeroFidelityObject.trueZero_re_eq_half` (l.316) | Sous l'objet de fidélité, tout zéro non trivial a re = 1/2. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | O10 | 2 |
| `GrammarTowerZeroFidelityObject.trueZero_eq_primeSwap` (l.322) | Sous l'objet de fidélité, l'opérateur croisé de tout zéro non trivial égale le swap premier. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | O10 | 3 |
| `GrammarTowerZeroFidelityObject.trueZero_isSelfAdjoint` (l.328) | Sous l'objet de fidélité, l'opérateur croisé de tout zéro non trivial est auto-adjoint. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 0 |
| `GrammarTowerZeroFidelityObject.trueZero_mem_unitary` (l.335) | Sous l'objet de fidélité, l'opérateur croisé de tout zéro non trivial est unitaire. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 0 |
| `riemannHypothesis_of_grammarTowerZeroFidelityObject` (l.346) | GrammarTowerZeroFidelityObject entraîne RiemannHypothesis. [docstring ≠ type] | IMPLIQUE RH SOUS PRÉMISSE | O10 | 1 |
| `riemannHypothesis_of_grammarTowerZeroFidelityObject_via_swap` (l.352) | Même conclusion, par l'égalité au swap premier. | IMPLIQUE RH SOUS PRÉMISSE | O10 | 0 |
| `riemannHypothesis_of_orientedFidelity_alone` (l.365) | Si tout zéro non trivial a ses entrées croisées égales, alors RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | O10 | 0 |
| `orientedFidelity_at_rho_iff_critical` (l.377) | Pour ρ, égalité des entrées (0,1),(1,0) ⟺ re ρ = 1/2. | CONFIRMÉE | V161 | 9 |
| `reciprocity_and_involution_hold_for_every_rho` (l.385) | Produit des entrées = 1 et T_ρ² = 1 pour tout ρ. | CONFIRMÉE | AJOUT | 3 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.zeroCarrierSurface` (l.408) | Sous l'objet de fidélité amputé du champ terminal, le carrier de vrai zéro égale la tour tordue à tout n. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.individualMemberSurface` (l.411) | Sous l'objet de fidélité amputé du champ terminal, chaque zéro est le point de base de sa propre fibre à sa propre position. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.reflectedZeroSurface` (l.413) | Sous l'objet de fidélité amputé du champ terminal, le réfléchi est un zéro non trivial. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | V62 | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.sameHeightSurface` (l.417) | Sous l'objet de fidélité amputé du champ terminal, la réflexion préserve la hauteur. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | V65 | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.reflectedRadialSurface` (l.420) | Sous l'objet de fidélité amputé du champ terminal, la réflexion complémente la position radiale. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | V65 | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.grammarRigidSurface` (l.423) | Sous l'objet de fidélité amputé du champ terminal, le bloc de grammaire complet premier canonique est GrammarRigid. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | V174 | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.grammarProjectionSurface` (l.425) | Sous l'objet de fidélité amputé du champ terminal, écart mod 6 ∈ {0,2,4} ⟺ transition d'états correspondante. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | V174 | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.grammarCompositionSurface` (l.430) | Sous l'objet de fidélité amputé du champ terminal, le produit des (1−2·cross n) sur [M,N) télescope en σ_M σ_N. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.grammarReturnSurface` (l.433) | Sous l'objet de fidélité amputé du champ terminal, sur un bloc de retour σ_A=σ_B, l'holonomie vaut 1. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.chi3GrammarSurface` (l.436) | Sous l'objet de fidélité amputé du champ terminal, χ3(p_n) = σ_n pour n≥2. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.tau15Surface` (l.438) | Sous l'objet de fidélité amputé du champ terminal, τ15 vaut 1 ssi transition 1→5 mod 6. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | V174 | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.tau51Surface` (l.442) | Sous l'objet de fidélité amputé du champ terminal, τ51 vaut 1 ssi transition 5→1 mod 6. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | V174 | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.inverseTransitionSurface` (l.446) | Sous l'objet de fidélité amputé du champ terminal, transformOf s t est τ11/τ15/τ51/τ55 exactement selon (s,t) dans {1,5}². | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.crossNonCoboundarySurface` (l.452) | Sous l'objet de fidélité amputé du champ terminal, le canal cross n'est le cobord d'aucun potentiel ψ. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.fiberPairSurface` (l.456) | Sous l'objet de fidélité amputé du champ terminal, les positions β et 1−β sont deux points de base d'une même fibre de hauteur, chacun zéro non trivial. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.tau15FiberSurface` (l.462) | Sous l'objet de fidélité amputé du champ terminal, la composante τ15 de la fibre est le vecteur de secteur τ15 non sommé. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.tau51FiberSurface` (l.466) | Sous l'objet de fidélité amputé du champ terminal, la composante τ51 de la fibre est le vecteur de secteur τ51 non sommé. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.harmonicTowerSurface` (l.470) | Sous l'objet de fidélité amputé du champ terminal, le carrier de vrai zéro réalise le module de la tour harmonique tordue. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.towerMultiplierSurface` (l.473) | Sous l'objet de fidélité amputé du champ terminal, les deux composantes de fibre portent le même multiplicateur towerCharacter(p n). | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.grammarTowerSupportSurface` (l.483) | Sous l'objet de fidélité amputé du champ terminal, la grammaire sélectionne le support des étages de tour (1+σ^m≠0 ⟺ σ=1 ou m pair) et towerCharacter(p)^(2k)=towerCharacter(p²)^k. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.trueZeroTransportSurface` (l.488) | Sous l'objet de fidélité amputé du champ terminal, les entrées du transport sont les quotients de retour du zéro et de son réfléchi sur [2,4). | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | V162 | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.commonTransportSurface` (l.493) | Sous l'objet de fidélité amputé du champ terminal, les entrées du transport sont le même quotient de tour aux positions β et 1−β. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | V162 | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.commonHeightPhaseSurface` (l.501) | Sous l'objet de fidélité amputé du champ terminal, ρ et son réfléchi ont la même phase de hauteur inversible et l'opérateur = phase⁻¹·transport. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | V158 | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.primeChannelSurface` (l.509) | Sous l'objet de fidélité amputé du champ terminal, le canal premier continué = diagonale τ11+τ55 + fibre cross (σ>1), et la provenance fibrée canonique tient. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 2 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.meromorphicSurface` (l.516) | Sous l'objet de fidélité amputé du champ terminal, re=1/2 ou pôle simple du canal premier continué en l'une des deux positions. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.radialDefectSurface` (l.523) | Sous l'objet de fidélité amputé du champ terminal, l'opérateur croisé vaut [[0,(11/5)^(−d)],[(11/5)^d,0]], d=re−1/2. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | V158,V167 | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.radialOperatorSurface` (l.528) | Sous l'objet de fidélité amputé du champ terminal, l'opérateur croisé est l'opérateur radial de défaut re−1/2. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | V158 | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.reflectionReciprocitySurface` (l.530) | Sous l'objet de fidélité amputé du champ terminal, le produit des entrées croisées vaut 1. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.involutionSurface` (l.532) | Sous l'objet de fidélité amputé du champ terminal, T_ρ²=1. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.adjointSurface` (l.534) | Sous l'objet de fidélité amputé du champ terminal, adjoint exact de l'opérateur croisé. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.ttStarSurface` (l.538) | Sous l'objet de fidélité amputé du champ terminal, T T† = diag(P^(−2d), P^(2d)). | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `GrammarTowerZeroFidelityObjectMinusFidelity.tStarTSurface` (l.542) | Sous l'objet de fidélité amputé du champ terminal, T† T = diag(P^(2d), P^(−2d)). | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObjectMinusFidelity (objet amputé, habité sans condition par grammarTowerZeroFidelityObjectMinusFidelity_holds)) | AJOUT | 1 |
| `grammarTowerZeroFidelityObjectMinusFidelity_holds` (l.547) | L'objet de fidélité amputé de son champ terminal (32 surfaces) est habité sans condition. [terme hors maître] | CONFIRMÉE | AJOUT | 3 |
| `fidelity_is_strictly_necessary` (l.591) | Depuis l'objet amputé, (RiemannHypothesis ↔ RiemannHypothesis) : l'objet amputé étant habité, fermer RH depuis lui revient à prouver RH sans hypothèse. | CONFIRMÉE | O10,O21 | 0 |
| `GrammarTowerZeroFidelityObject.toMinusFidelity` (l.604) | L'objet de fidélité complet fournit l'objet amputé. | CONFIRMÉE SOUS CONDITION (GrammarTowerZeroFidelityObject) | AJOUT | 0 |

### `Round26EOComplexZeroTowerReconstruction`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `cpow_realExp_eq_exp` (l.63) | Pour u réel et z complexe, (exp u)^z = exp(u·z) dans ℂ. [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `floorTowerPrimitive_eq_inv_voiceScaleCharacter` (l.78) | La primitive d'étage vaut l'inverse du caractère d'échelle à la coordonnée u/m. | CONFIRMÉE | AJOUT | 1 |
| `floorTowerPrimitive_ne_zero` (l.87) | La primitive d'étage est toujours non nulle. | CONFIRMÉE | AJOUT | 2 |
| `floorTowerPrimitive_at_primePower` (l.90) | Au point u=m·log P, la primitive d'étage égale le caractère de tour towerCharacter P z (m disparaît), pour tout z. | CONFIRMÉE (domaine: 0<P, 0<m) | V158 | 6 |
| `floorTowerPrimitive_floor_independent_at_primePower` (l.99) | Deux étages m,k lus à leur coordonnée premier-puissance donnent la même valeur. | CONFIRMÉE (domaine: 0<P, 0<m, 0<k) | AJOUT | 0 |
| `norm_floorTowerPrimitive` (l.109) | La norme de la primitive d'étage vaut exp((u/m)·−(re z −1/2)). | CONFIRMÉE | V16,V158 | 1 |
| `floorTowerPrimitive_eq_modulus_mul_phase` (l.116) | La primitive d'étage = module exp((u/m)(−(re−1/2))) × phase exp(−i(u/m)·Im z). | CONFIRMÉE | V16,V158 | 0 |
| `floorNormalizedZeroRow_eq` (l.135) | La ligne normalisée par étage = amplitude propre du membre × inverse de la primitive d'étage. | CONFIRMÉE | V102,V158 | 2 |
| `floorNormalizedZeroRow_at_primePower` (l.147) | Au point m·log P, la ligne normalisée vaut amplitude propre × (towerCharacter P ρ)⁻¹, indépendamment de m. | CONFIRMÉE (domaine: 0<P, 0<m) | V158,V172 | 3 |
| `floorNormalizedZeroRow_floor_independent_at_primePower` (l.163) | Tous les étages d'un même premier lisent la même signature complexe du zéro. | CONFIRMÉE (domaine: 0<P, 0<m, 0<k) | V172 | 1 |
| `floorOne_walk_is_power_of_floorM_step` (l.173) | À l'étage 1 la marche jusqu'à m·log P est la puissance m-ième du pas de l'étage m. | CONFIRMÉE (domaine: 0<P, 0<m) | AJOUT | 0 |
| `re_floorNormalizedZeroRow_one_eq_towerMode` (l.187) | La partie réelle de la ligne normalisée à l'étage 1 est le towerMode de module ‖coeff‖, phase arg(coeff). | CONFIRMÉE | V100 | 0 |
| `floorTowerPrimitive_reflect_ratio` (l.201) | Le rapport primitive(z)/primitive(1−conj z) est le réel exp((u/m)(−2(re z−1/2))), sans phase. | CONFIRMÉE | V35,V158 | 1 |
| `floorTowerPrimitive_reflect_ratio_at_primePower` (l.212) | Au point premier-puissance, ce rapport vaut P^(−2(re z −1/2)). | CONFIRMÉE (domaine: 0<P, 0<m) | V102,V158 | 4 |
| `floorTowerPrimitive_reflect_ratio_gamma_and_floor_free` (l.222) | Deux points de même re, hauteurs et étages quelconques, ont le même rapport de réflexion. | CONFIRMÉE (domaine: z.re = w.re ) | V158 | 0 |
| `floorTowerPrimitive_reflect_ratio_eq_one_iff` (l.234) | Ce rapport vaut 1 ssi re z = 1/2. | CONFIRMÉE (domaine: 1<P, 0<m) | V161 | 1 |
| `floorTowerPrimitive_reflect` (l.259) | La primitive au réfléchi vaut l'inverse du conjugué de la primitive. | CONFIRMÉE | V35,V101 | 1 |
| `floorTowerPrimitive_reflect_product` (l.268) | primitive(z)·conj(primitive(1−conj z)) = 1. | CONFIRMÉE | V158 | 2 |
| `two_prime_scale_agreement_reflect_forces_critical` (l.278) | Si un point et son réfléchi ont même primitive à deux échelles premières distinctes (étage 1), alors re z = 1/2. | CONFIRMÉE (domaine: accord aux échelles log a et log b, a≠b premiers ) | V161 | 0 |
| `two_dependent_scales_not_faithful` (l.309) | Pour u>0, deux points distincts ont même primitive à u et 2u. | CONFIRMÉE (domaine: 0<u) | AJOUT | 0 |
| `floorNormalizedZeroRow_return_quotient` (l.339) | Le quotient de la ligne normalisée en deux échelles est le quotient inverse de primitives (l'amplitude s'annule). | CONFIRMÉE | V172 | 1 |
| `all_floor_tower_relations_hold_for_arbitrary_point` (l.355) | Pour tout z complexe : disparition de l'étage, produit réfléchi = 1, additivité des primitives. | CONFIRMÉE | V158 | 1 |
| `offline_deformation_survives_all_floor_relations` (l.374) | Pour tout d≠0 et γ, un point re≠1/2 de hauteur γ vérifie toutes les relations d'étage. | CONFIRMÉE SOUS CONDITION (d≠0) | AJOUT | 0 |
| `multiple_prime_cycles_are_simultaneously_consistent` (l.393) | Pour tout z, m>0 et P>0, le rapport de réflexion en m·log P vaut P^(−2(re z−1/2)). | CONFIRMÉE (domaine: 0<m, 0<P) | V158 | 0 |
| `two_block_defects_carry_the_same_information` (l.404) | P^(−2(re z −1/2)) = 1 ⟺ re z = 1/2 ou P = 1. | CONFIRMÉE (domaine: 0<P) | V161 | 0 |
| `trueZeroReflectedCrossTransport_from_floorNormalizedZeroRow` (l.424) | L'entrée (0,1) du transport croisé est le quotient de la ligne normalisée aux échelles log p2 et log p4 (étage 1). | CONFIRMÉE | V162 | 0 |
| `master_identity_couples_all_floors_and_primes` (l.442) | Identité maîtresse : ligne normalisée en m·log P = amplitude propre × (towerCharacter P ρ)⁻¹ pour tout étage m et premier P. | CONFIRMÉE (domaine: 0<P, 0<m) | V158,V172 | 0 |
| `tour10DV_exact_diagnosis` (l.455) | Diagnostic : à m·log P, primitive = caractère de tour, norme exp(−log P·(re−1/2)), rapport de réflexion P^(−2d), = 1 ssi re=1/2, produit réfléchi = 1. | CONFIRMÉE (domaine: 1<P, 0<m) | V158,V161 | 0 |

### `Round26EPTerminalFidelityComposition`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `rawZeroPrimeSignature_eq_floorNormalizedZeroRow` (l.44) | La signature brute zéro-premier égale la ligne normalisée par étage en m·log P, pour tout étage m>0. [terme hors maître] | CONFIRMÉE (domaine: 0<P, 0<m) | V172 | 1 |
| `rawZeroPrimeSignature_floor_independent` (l.50) | La signature brute ne dépend d'aucun étage. | CONFIRMÉE (domaine: 0<P, 0<m, 0<k) | V172 | 0 |
| `rawZeroPrimeSignature_eq_coeff_mul_character` (l.60) | La signature brute vaut coefficient propre du membre × caractère d'échelle au log P. | CONFIRMÉE (domaine: 0<P) | V172 | 5 |
| `rawZeroPrimeSignature_ne_zero` (l.71) | La signature brute est non nulle. | CONFIRMÉE (domaine: 0<P) | V172 | 2 |
| `norm_rawZeroPrimeSignature` (l.77) | La norme de la signature brute vaut ‖coeff‖·exp((re−1/2)·log P). | CONFIRMÉE (domaine: 0<P) | V102,V172 | 0 |
| `rawZeroPrimeCharacter_eq` (l.100) | Le caractère premier brut égale le caractère d'échelle en log P. | CONFIRMÉE (domaine: 0<P) | AJOUT | 1 |
| `character_agreement_at_one_prime_reflect_forces_critical` (l.106) | Si les caractères bruts de ρ et de son réfléchi coïncident à un premier p_n, alors re ρ = 1/2. | CONFIRMÉE (domaine: accord des caractères à un seul premier ) | V161 | 0 |
| `generic_single_scale_character_eq_forces_critical` (l.124) | Pour tout z complexe, x>0, x≠1 : accord du caractère d'échelle de z et de son réfléchi en log x force re z = 1/2. | CONFIRMÉE (domaine: accord à une échelle ) | V161 | 1 |
| `crossScaleSignature_eq` (l.154) | La signature inter-échelles vaut le caractère d'échelle en log(P/Q) (l'amplitude s'annule). | CONFIRMÉE (domaine: 0<P, 0<Q) | V172 | 4 |
| `crossScaleSignature_eq_cpow` (l.169) | La signature inter-échelles vaut (P/Q)^(ρ−1/2). | CONFIRMÉE (domaine: 0<P, 0<Q) | AJOUT | 1 |
| `crossScaleSignature_reflect_eq_iff_critical` (l.179) | Pour P≠Q, accord des signatures inter-échelles de ρ et son réfléchi ⟺ re ρ = 1/2. | CONFIRMÉE (domaine: 0<P, 0<Q, P≠Q) | V161 | 1 |
| `crossScaleSignature_is_generic_z_valid` (l.202) | Pour z arbitraire, P≠Q : accord de caractère de z et 1−conj z en log(P/Q) force re z = 1/2. | CONFIRMÉE (domaine: accord ) | V161 | 0 |
| `crossScaleSignature_forgets_true_zero_amplitude` (l.219) | La signature inter-échelles ne dépend pas de l'amplitude propre : deux zéros de même valeur complexe ont la même signature. | CONFIRMÉE (domaine: ↑ρ = ↑σ ) | V172 | 1 |
| `tau15_add_tau51_eq_cross` (l.235) | Pour n≥2, τ15 + τ51 = cross de la transition. | CONFIRMÉE (domaine: 2 ≤ n) | V174 | 3 |
| `tau15_sub_tau51_eq_signedCoboundary` (l.242) | Pour n≥2, τ15 − τ51 = cobord signé. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 3 |
| `tau15_eq_half_cross_add_signed` (l.250) | Pour n≥2, τ15 = (cross + cobord signé)/2. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 0 |
| `tau51_eq_half_cross_sub_signed` (l.258) | Pour n≥2, τ51 = (cross − cobord signé)/2. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 0 |
| `cross_eq_signedCoboundary_sq` (l.266) | Pour n≥2, cross = (cobord signé)² : le carré efface l'orientation. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 0 |
| `orientation_witness_same_cross_opposite_orientation` (l.274) | Aux transitions (7,11) et (5,7), même cross, cobords ±1, indicateurs τ15/τ51 opposés. | CONFIRMÉE | AJOUT | 1 |
| `orientedPrimeComplex_add` (l.304) | Pour n≥2, lift15 + lift51 = cross × signature brute. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 1 |
| `orientedPrimeComplex_sub` (l.312) | Pour n≥2, lift15 − lift51 = cobord signé × signature brute. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 1 |
| `oriented_lift_inversion_acts_on_grammar_only` (l.320) | Aux positions n=3 et n=2, les lifts orientés s'échangent à ρ et P inchangés. | CONFIRMÉE | V34 | 0 |
| `oriented_lift_walsh_expansion` (l.337) | Pour n≥2, somme et différence des lifts s'expriment dans la base de Walsh χ3. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 0 |
| `hermitianGram_re_polarization` (l.361) | Re H(v,w) = (‖v+w‖²−‖v−w‖²)/4. [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `hermitianGram_im_polarization` (l.369) | Im H(v,w) = (‖v+iw‖²−‖v−iw‖²)/4. | CONFIRMÉE | AJOUT | 0 |
| `old_scalar_energy_does_not_determine_hermitian_gram` (l.380) | Les paires (1,1) et (1,−1) ont même énergie scalaire mais des Gram hermitiens distincts. | CONFIRMÉE | AJOUT | 0 |
| `rawHermitian_eq` (l.401) | Le Gram hermitien inter-échelles brut vaut ‖C(ρ)‖²·e^{(re−1/2)(log P+log Q)}·e^{iγ(log P−log Q)}. | CONFIRMÉE (domaine: 0<P, 0<Q) | V102,V172 | 2 |
| `norm_rawHermitian` (l.435) | Sa norme vaut normSq(coeff)·exp((re−1/2)(log P+log Q)). | CONFIRMÉE (domaine: 0<P, 0<Q) | V102 | 4 |
| `rawHermitian_phase_carries_gamma` (l.446) | Sa phase lit la hauteur γ à travers log(P/Q). | CONFIRMÉE (domaine: 0<P, 0<Q) | V158 | 0 |
| `rawHermitian_retains_true_zero_provenance` (l.457) | La norme du Gram divisée par l'exponentielle vaut normSq(coeff) > 0 : la provenance zéro ne s'annule pas. | CONFIRMÉE (domaine: 0<P, 0<Q) | V172 | 0 |
| `rawHermitian_reflect_eq_two_products_forces_critical` (l.469) | Si les normes des Gram de ρ et du réfléchi coïncident en deux produits d'échelles distincts, alors re ρ = 1/2. | CONFIRMÉE SOUS CONDITION (deux égalités de normes à log P+log Q ≠ log P'+log Q') | V161,V170 | 0 |
| `spreadWitness_L0_global_residue_free` (l.533) | La somme des quatre composantes du témoin sectoriel vaut c pour tout t. | CONFIRMÉE | AJOUT | 0 |
| `spreadWitness_L1_scalar_energy_free` (l.539) | Les paramètres t et −c−t donnent la même énergie scalaire (τ11,τ15). | CONFIRMÉE | AJOUT | 0 |
| `spreadWitness_L1_two_distinct_parameters` (l.548) | Si c+2t≠0 alors t ≠ −c−t. | CONFIRMÉE (domaine: c+2t ≠ 0) | AJOUT | 0 |
| `spreadWitness_L2_signed_orientation_pins_t` (l.553) | L'égalité des coordonnées orientées v15−v51 pour t et t' force t=t'. | CONFIRMÉE (domaine: égalité des orientations signées ) | AJOUT | 0 |
| `killing_spread_witness_does_not_constrain_the_zero_side` (l.565) | Pour d≠0, il existe z de re=1/2+d vérifiant la disparition de l'étage : la couche L2 ne contraint pas le côté zéro. | CONFIRMÉE (domaine: d≠0 ) | AJOUT | 0 |
| `tour10DW_exact_diagnosis` (l.586) | Bilan : signature brute non nulle, signature inter-échelles = caractère en log(P/Q), normSq>0, norme du Gram, accord inter-échelles ⟺ re=1/2. | CONFIRMÉE (domaine: 0<P, 0<Q, P≠Q) | V161,V172 | 0 |

### `Round26EPTransformedZeroGrammar`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `transformedZeroGrammarVertex_state` (l.48) | L'état du sommet de grammaire transformée est grammarPrimeStateChi3 n. [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `transformedZeroGrammarVertex_character` (l.51) | Le caractère du sommet est towerCharacter(p n) en ρ. | CONFIRMÉE | AJOUT | 0 |
| `transformedZeroScaleCocycle_eq_towerCharacter_ratio` (l.63) | Le cocycle d'échelle est le rapport towerCharacter Q ρ / towerCharacter P ρ. | CONFIRMÉE (domaine: 0<P, 0<Q) | AJOUT | 4 |
| `transformedZeroScaleCocycle_comp` (l.74) | Le cocycle d'échelle est multiplicatif par composition de chemins. | CONFIRMÉE | AJOUT | 1 |
| `transformedZeroScaleCocycle_self` (l.85) | Le cocycle d'échelle de P à P vaut 1. | CONFIRMÉE | AJOUT | 1 |
| `transformedZero_tau15_sub_tau51` (l.94) | Pour n≥2, la différence des arêtes orientées = cobord signé × cocycle complexe. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 1 |
| `transformedZero_tau15_add_tau51` (l.123) | Pour n≥2, la somme des arêtes orientées = cross × cocycle complexe. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 1 |
| `transformedZero_oriented_sector_eq_of_coboundary_zero` (l.150) | Si la coordonnée de cobord du vecteur de résidus de secteur est nulle, les résidus τ15 et τ51 sont égaux. | CONFIRMÉE SOUS CONDITION (sectorCoboundaryCoord r = 0) | AJOUT | 0 |

### `Round26EQCoboundaryLocalUniform`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `isOpen_coboundaryDomain` (l.98) | Le domaine du canal de cobord est ouvert. [terme hors maître] | CONFIRMÉE | AJOUT | 5 |
| `coboundary_block_bound_on_box` (l.104) | Sur une boîte coboundaryBox, l'écart de deux sommes partielles du canal de cobord est majoré par deux majorants de bord plus M fois une somme de majorants intérieurs. | CONFIRMÉE (domaine: 0<sigma0, 3≤N<n) | AJOUT | 1 |
| `coboundaryPartial_dist_anchor_lt` (l.280) | Pour tout ε>0 il existe une ancre N telle que toute somme partielle k≥N reste à distance <ε de celle de N, uniformément sur la boîte. | CONFIRMÉE (domaine: 0<sigma0, 0<ε) | AJOUT | 1 |
| `coboundaryPartial_uniformCauchySeqOn_box` (l.353) | Les sommes partielles de Dirichlet du canal de cobord sont uniformément de Cauchy sur toute boîte. [terme hors maître] | CONFIRMÉE (domaine: 0<sigma0) | AJOUT | 1 |
| `coboundaryChannelLimit_tendsto` (l.381) | Pour Re s>0, les sommes partielles du cobord convergent vers coboundaryChannelLimit s. | CONFIRMÉE (domaine: 0<Re s) | AJOUT | 3 |
| `coboundaryPartial_tendstoLocallyUniformlyOn` (l.390) | Les sommes partielles du cobord convergent localement uniformément vers la limite sur {Re s>0}. | CONFIRMÉE | AJOUT | 1 |
| `coboundaryPartial_differentiableOn` (l.435) | Chaque somme partielle du canal de cobord est holomorphe sur le domaine Re s>0. | CONFIRMÉE | AJOUT | 1 |
| `coboundaryChannelLimit_differentiableOn` (l.459) | La limite du canal de cobord est holomorphe sur Re s>0. | CONFIRMÉE | AJOUT | 2 |
| `coboundaryChannelLimit_eq_sector_difference` (l.471) | Pour Re s>1, la limite du cobord égale la différence des séries de Dirichlet des secteurs τ15 et τ51. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 4 |
| `coboundaryChannelLimit_differentiableAt_generic` (l.507) | La limite du cobord est dérivable en tout point de Re z>0 (sans rien sur les zéros). | CONFIRMÉE (domaine: 0<Re z) | AJOUT | 1 |
| `coboundaryChannelLimit_differentiableAt_zeta_zero` (l.516) | La limite du cobord est dérivable en tout zéro non trivial de zêta. | CONFIRMÉE | AJOUT | 0 |
| `crossScaleSignature_eq_transformedZeroScaleCocycle` (l.537) | La signature inter-échelles d'un zéro égale le cocycle d'échelle de la grammaire transformée. [terme hors maître] | CONFIRMÉE (domaine: 0<P, 0<Q) | AJOUT | 2 |
| `transformedZeroScaleCocycle_forgets_true_zero_amplitude` (l.547) | Deux zéros de même valeur complexe ont le même cocycle : le cocycle oublie l'amplitude du vrai zéro. | CONFIRMÉE (domaine: 0<P,0<Q) | V158,V159 | 0 |

### `Round26ERCrossChannelReduction`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `crossCoeff_zero` (l.32) | Le coefficient croisé de grammaire aux premiers p0,p1 (mod 6) vaut 1. | CONFIRMÉE | AJOUT | 1 |
| `crossCoeff_one` (l.35) | Le coefficient croisé aux premiers p1,p2 (mod 6) vaut 1. | CONFIRMÉE | AJOUT | 1 |
| `crossInitialCorrection_eq_explicit` (l.38) | La correction initiale croisée vaut log 2·2^{−s} + log 3·3^{−s}. | CONFIRMÉE | AJOUT | 1 |
| `crossInitialCorrection_differentiable` (l.45) | La correction initiale croisée est entière. | CONFIRMÉE | AJOUT | 4 |
| `grammarCrossPrimeDirichlet_summable_re_gt_one` (l.61) | Pour Re s>1, la série de Dirichlet croisée (coefficient croisé × poids premier) est sommable. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 1 |
| `grammarCrossPrimeDirichlet_eq_initial_add_tail` (l.73) | Pour Re s>1, la série croisée = correction initiale + queue. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 1 |
| `grammarCrossPrimeDirichlet_eq_initial_add_half_global_sub_half_correlation` (l.91) | Pour Re s>1, la série croisée = correction initiale + ½ queue globale − ½ corrélation de caractères consécutifs. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 0 |
| `adjacentChi3CoeffSum_eq_sub_two_mul_crossCoeffSum` (l.111) | La somme d'autocorrélation adjacente χ3 vaut N − 2×(somme des coefficients croisés) : elle compte les changements d'état. [terme hors maître] | CONFIRMÉE | V174 | 1 |
| `crossCoeffSum_nonneg` (l.126) | La somme des coefficients croisés est ≥ 0. | CONFIRMÉE | AJOUT | 1 |
| `crossCoeffSum_le` (l.133) | La somme des coefficients croisés est ≤ N. | CONFIRMÉE | AJOUT | 1 |
| `abs_adjacentChi3CoeffSum_le` (l.143) | \|somme d'autocorrélation adjacente\| ≤ N. | CONFIRMÉE | AJOUT | 1 |
| `grammarPrimeStateChi3_succ_eq_sub_two_mul_coboundary` (l.152) | σ_{n+1} = σ_n − 2×(potentiel(p_{n+1}) − potentiel(p_n)) sans hypothèse sur n. | CONFIRMÉE | AJOUT | 1 |
| `alignedChi3PrimeDirichletTail_summable_re_gt_one` (l.169) | Pour Re s>1, la queue de Dirichlet alignée σ_{n+2}·poids est sommable. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 1 |
| `shiftedChi3PrimeDirichletTail_summable_re_gt_one` (l.182) | Pour Re s>1, la queue décalée σ_{n+3}·poids_{n+2} est sommable. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 0 |
| `shiftedChi3PrimeDirichletTail_eq_aligned_sub_two_mul_coboundary` (l.195) | Pour Re s>1, queue décalée = queue alignée − 2×queue de cobord. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 0 |
| `potentialCoboundaryCoeffSum_telescopes` (l.248) | Les sommes partielles des coefficients de cobord télescopent : potentiel(p_{N+2}) − potentiel(p_2). | CONFIRMÉE | AJOUT | 1 |
| `abs_potentialCoboundaryCoeffSum_le_one` (l.258) | Ces sommes partielles sont bornées par 1 en valeur absolue, uniformément en N. | CONFIRMÉE | AJOUT | 0 |

### `Round26ESOrientedPrincipalPartGeneric`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `coboundaryChannelLimit_analyticAt` (l.49) | Le canal de cobord est analytique en tout point de Re z>0. | CONFIRMÉE (domaine: 0<Re z) | AJOUT | 7 |
| `coboundaryChannelLimit_meromorphicOrderAt_nonneg` (l.55) | Le canal de cobord a un ordre méromorphe ≥ 0 en tout point de Re z>0. [terme hors maître] | CONFIRMÉE (domaine: 0<Re z) | AJOUT | 0 |
| `orientedPair_meromorphicOrderAt_eq` (l.71) | Si (F15,F51) forment une paire orientée et F51 a un pôle en z (Re z>0), F15 a le même ordre méromorphe en z. | CONFIRMÉE (domaine: IsOrientedContinuationPair, F51 méromorphe avec pôle en z ) | AJOUT | 1 |
| `orientedPair_meromorphicTrailingCoeffAt_eq` (l.98) | Mêmes hypothèses : F15 et F51 ont le même coefficient dominant en z. | CONFIRMÉE (domaine: paire orientée, F51 avec pôle en z ) | AJOUT | 3 |
| `orientedPair_trailingCoeff_eq_at_zeta_zero` (l.128) | En un zéro non trivial de zêta où F51 a un pôle, F15 et F51 ont même coefficient dominant. | CONFIRMÉE (domaine: paire orientée, F51 avec pôle au zéro ) | AJOUT | 0 |
| `orientedContinuation_isPair` (l.152) | Pour tout Ccross, les continuations orientées τ15 et τ51 forment une paire orientée (fait algébrique). | CONFIRMÉE | AJOUT | 0 |
| `orientedContinuation_add` (l.162) | Les continuations orientées τ15 et τ51 somment à Ccross. | CONFIRMÉE | AJOUT | 0 |
| `orientedContinuation_sub` (l.167) | Leur différence égale la limite du canal de cobord. | CONFIRMÉE | AJOUT | 0 |
| `orientedTau15Continuation_eq_raw_re_gt_one` (l.176) | Si Ccross égale la somme des séries de secteur pour Re s>1, la continuation τ15 égale la série brute τ15 pour Re s>1. | CONFIRMÉE (domaine: Ccross = somme des deux séries de secteur sur Re s>1 (paramètre, pas d'existence affirmée) ) | AJOUT | 0 |
| `orientedTau51Continuation_eq_raw_re_gt_one` (l.191) | Même énoncé pour τ51. | CONFIRMÉE (domaine: idem ) | AJOUT | 0 |

### `Round26ETCrossTrueZeroPole`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `grammarTransformIndicator_tau15_eq_zero_of_lt_two` (l.42) | L'indicatrice de transformation τ15 est nulle pour n<2. | CONFIRMÉE (domaine: n<2) | AJOUT | 1 |
| `grammarTransformIndicator_tau51_eq_zero_of_lt_two` (l.52) | L'indicatrice de τ51 est nulle pour n<2. | CONFIRMÉE (domaine: n<2) | AJOUT | 1 |
| `sector_tau15_add_tau51_eq_crossTail_re_gt_one` (l.62) | Pour Re s>1, les séries de secteur τ15 et τ51 somment exactement à la queue de la série croisée. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 2 |
| `globalTailContinuation_eq_raw_re_gt_one` (l.96) | Pour Re s>1, la continuation de la queue globale égale la queue de Dirichlet globale brute. | CONFIRMÉE (domaine: 1<Re s) | AJOUT | 1 |
| `globalTailContinuation_meromorphicAt` (l.106) | La continuation de la queue globale est méromorphe en tout s de Re s>1/2. | CONFIRMÉE (domaine: 1/2<Re s) | AJOUT | 2 |
| `globalTailContinuation_eq_add_neg` (l.113) | La continuation de la queue globale = continuation du canal premier + (−correction initiale entière). | CONFIRMÉE | AJOUT | 2 |
| `globalTailContinuation_order_at_true_zero` (l.123) | En un zéro de zêta de Re>1/2, la continuation de la queue globale a un ordre méromorphe −1. | CONFIRMÉE SOUS CONDITION (zêta(ρ)=0 et Re ρ>1/2) | V100 | 2 |
| `globalTailContinuation_trailingCoeff_at_true_zero` (l.140) | En un zéro de zêta de Re>1/2, la queue globale a même coefficient dominant que la continuation du canal premier. | CONFIRMÉE SOUS CONDITION (zêta(ρ)=0, Re ρ>1/2) | AJOUT | 1 |
| `crossChannelContinuation_eq_raw_re_gt_one` (l.169) | Si Corr égale la corrélation de caractères consécutifs sur Re s>1, la continuation du canal croisé égale la queue croisée brute sur Re s>1. | CONFIRMÉE (domaine: Corr = corrélation sur Re s>1 ) | AJOUT | 2 |
| `crossChannelContinuation_meromorphicAt` (l.178) | Si Corr est analytique en s et Re s>1/2, la continuation croisée est méromorphe en s. | CONFIRMÉE SOUS CONDITION (Corr analytique en s) | AJOUT | 2 |
| `crossChannelContinuation_order_at_true_zero` (l.195) | Si Corr est analytique en ρ, zêta(ρ)=0 et Re ρ>1/2, la continuation croisée a ordre −1 en ρ. | CONFIRMÉE SOUS CONDITION (Corr analytique en ρ, zêta(ρ)=0, Re ρ>1/2) | AJOUT | 2 |
| `crossChannelContinuation_trailingCoeff_at_true_zero` (l.226) | Même condition : le coefficient dominant croisé vaut ½ × celui du canal premier. | CONFIRMÉE (domaine: idem ) | AJOUT | 1 |
| `orientedTau15Cont_eq_raw_re_gt_one` (l.273) | Si Corr égale la corrélation sur Re s>1, la continuation orientée τ15 égale la série de secteur τ15 brute sur Re s>1. | CONFIRMÉE (domaine: Corr = corrélation sur Re s>1 ) | AJOUT | 0 |
| `orientedTau51Cont_eq_raw_re_gt_one` (l.284) | Même énoncé pour τ51. | CONFIRMÉE (domaine: idem ) | AJOUT | 0 |
| `orientedTau51Cont_meromorphicAt` (l.295) | Si Corr analytique en s et Re s>1/2, la continuation orientée τ51 est méromorphe en s. | CONFIRMÉE SOUS CONDITION (Corr analytique) | AJOUT | 2 |
| `orientedTau51Cont_order_at_true_zero` (l.312) | Si Corr analytique en ρ, zêta(ρ)=0, Re ρ>1/2, la continuation τ51 a ordre −1. | CONFIRMÉE SOUS CONDITION (Corr analytique en ρ, zêta(ρ)=0, Re ρ>1/2) | AJOUT | 2 |
| `orientedTau51Cont_trailingCoeff_at_true_zero` (l.346) | Si Corr analytique en ρ, zêta(ρ)=0, Re ρ>1/2, le coefficient dominant de la continuation τ51 vaut ¼ × celui du canal premier. | CONFIRMÉE SOUS CONDITION (Corr analytique en ρ, zêta(ρ)=0, Re ρ>1/2) | AJOUT | 1 |
| `orientedTauCont_isPair` (l.389) | Pour tout Corr, les continuations orientées τ15 et τ51 forment une paire orientée. | CONFIRMÉE | AJOUT | 2 |
| `orientedTau15Cont_order_at_true_zero` (l.395) | Si Corr analytique en ρ, zêta(ρ)=0, Re ρ>1/2, la continuation τ15 a ordre méromorphe −1 en ρ. | CONFIRMÉE SOUS CONDITION (Corr analytique en ρ, zêta(ρ)=0, Re ρ>1/2) | AJOUT | 0 |
| `orientedTau_trailingCoeff_eq` (l.408) | Sous les mêmes conditions, les deux orientations τ15 et τ51 ont le même coefficient dominant au vrai zéro. | CONFIRMÉE SOUS CONDITION (Corr analytique en ρ, zêta(ρ)=0, Re ρ>1/2) | V35,V81 | 1 |
| `orientedTau_trailingCoeff_value` (l.422) | Sous les mêmes conditions, ce coefficient commun vaut ¼ × celui du canal premier global (aucune donnée grammaticale, d'échelle ou d'orientation). | CONFIRMÉE SOUS CONDITION (Corr analytique en ρ, zêta(ρ)=0, Re ρ>1/2) | AJOUT | 0 |

### `Round26EUOperatorWeldDichotomy`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `commonFactorWeld_forces_critical` (l.58) | Pour une paire orientée, un pôle de F51 en z (Re z>0) et une soudure à facteur commun en z, on a Re z = 1/2. [terme hors maître] | CONFIRMÉE SOUS CONDITION (paire orientée, F51 méromorphe à pôle en z, CommonFactorWeldAt F15 F51 z) | V126,O5 | 2 |
| `not_commonFactorWeld_of_re_gt_half` (l.76) | Pour Re z>1/2 avec pôle de F51 en z et paire orientée, la soudure à facteur commun n'existe pas en z. | CONFIRMÉE (domaine: paire orientée, F51 méromorphe à pôle en z ) | V126 | 0 |
| `rh_of_commonFactorWeld_everywhere` (l.90) | Si une paire orientée (F15,F51) est méromorphe avec pôle de F51 en chaque zéro non trivial et une soudure à facteur commun en chaque zéro non trivial, alors RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126,O5 | 1 |
| `trueZeroReflectedCrossOperator_offdiag_ne_zero` (l.105) | Les deux entrées hors-diagonale de l'opérateur croisé réfléchi du vrai zéro z sont non nulles. [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `twoFactorWeld_always_satisfiable` (l.123) | Avec deux facteurs indépendants, la soudure des coefficients dominants avec les entrées hors-diagonale est toujours satisfaisable. | CONFIRMÉE SOUS CONDITION (entrées (0,1) et (1,0) de l'opérateur non nulles) | AJOUT | 0 |

### `Round26EVPartialSumHolomorphyCriterion`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `weightedCumulative_eq_ofReal` (l.107) | Le cumulatif pondéré complexe est le cast du cumulatif pondéré réel. [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `weightedCumulativeReal_eq_by_parts` (l.115) | Le cumulatif pondéré réel s'écrit par sommation d'Abel : log p_{m−1}·Σa − Σ(log p_{i+1} − log p_i)·Σ_{n≤i}a. | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.Round26EVPartialSumHolomorphyCriterion.0.RhGap.abs_sub_le_abs_add_abs` (l.133) | \|x−y\| ≤ \|x\|+\|y\|. | CONFIRMÉE | AJOUT | 1 |
| `norm_weightedCumulative_le` (l.138) | Sous coeffPartialSumBound, ‖cumulatif pondéré‖ ≤ C(2^θ+1)·(p_{m−1})^θ·log p_{m−1}. | CONFIRMÉE SOUS CONDITION (coeffPartialSumBound a C θ) | AJOUT | 2 |
| `weightedChannel_sum_by_parts` (l.233) | Identité d'Abel pour les sommes par blocs du canal pondéré, générique en a. | CONFIRMÉE (domaine: M<N) | AJOUT | 2 |
| `weightedPartial_eq_sum_Ico` (l.251) | La somme partielle pondérée est Σ_{n<N} a_n log p_n p_n^{−s}. | CONFIRMÉE | AJOUT | 2 |
| `weightedPartial_cauchySeq` (l.261) | Sous coeffPartialSumBound, les sommes partielles de Dirichlet pondérées forment une suite de Cauchy pour θ<Re s. | CONFIRMÉE SOUS CONDITION (coeffPartialSumBound) | AJOUT | 1 |
| `exists_weightedLimit` (l.466) | Sous coeffPartialSumBound, les sommes partielles pondérées convergent pour θ<Re s. | CONFIRMÉE SOUS CONDITION (coeffPartialSumBound) | AJOUT | 1 |
| `isOpen_weightedDomain` (l.481) | Le demi-plan {θ<Re s} est ouvert. | CONFIRMÉE | AJOUT | 1 |
| `weighted_block_bound_on_box` (l.494) | Sous coeffPartialSumBound, l'écart de deux sommes partielles pondérées est majoré uniformément sur la boîte weightedBox. | CONFIRMÉE SOUS CONDITION (coeffPartialSumBound) | AJOUT | 1 |
| `weightedPartial_dist_anchor_lt` (l.684) | Sous coeffPartialSumBound, ∀ε>0 il existe une ancre N telle que toute somme partielle k≥N reste à <ε de celle de N, uniformément sur la boîte. | CONFIRMÉE SOUS CONDITION (coeffPartialSumBound) | AJOUT | 1 |
| `weightedPartial_uniformCauchySeqOn_box` (l.771) | Sous coeffPartialSumBound, weightedPartial est uniformément de Cauchy sur toute boîte. | CONFIRMÉE SOUS CONDITION (coeffPartialSumBound) | AJOUT | 1 |
| `weightedLimit_tendsto` (l.799) | Sous coeffPartialSumBound, les sommes partielles convergent vers weightedLimit pour θ<Re s. | CONFIRMÉE SOUS CONDITION (coeffPartialSumBound) | AJOUT | 1 |
| `weightedPartial_tendstoLocallyUniformlyOn` (l.810) | Sous coeffPartialSumBound, weightedPartial converge localement uniformément vers weightedLimit sur {θ<Re s}. | CONFIRMÉE SOUS CONDITION (coeffPartialSumBound) | AJOUT | 3 |
| `weightedPartial_differentiableOn` (l.856) | Chaque somme partielle pondérée est holomorphe sur {θ<Re s}. | CONFIRMÉE | AJOUT | 1 |
| `weightedLimit_differentiableOn` (l.874) | Sous coeffPartialSumBound, weightedLimit est holomorphe sur {θ<Re s}. | CONFIRMÉE SOUS CONDITION (coeffPartialSumBound) | AJOUT | 1 |
| `weightedPartial_tendstoLocallyUniformlyOn_of_coeffBound` (l.887) | Une borne coeffPartialSumBound entraîne l'existence d'une limite localement uniforme sur θ<Re s. | CONFIRMÉE SOUS CONDITION (coeffPartialSumBound) | AJOUT | 0 |
| `weightedLimit_differentiableOn_of_coeffBound` (l.897) | Une borne coeffPartialSumBound entraîne une limite locally uniforme holomorphe sur θ<Re s. | CONFIRMÉE SOUS CONDITION (coeffPartialSumBound) | AJOUT | 0 |

### `Round26EWCrossOutsideContinuedSpan`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `sectorCrossCoord_not_in_span_global_chi3_coboundary` (l.40) | La coordonnée croisée de secteur n'est combinaison linéaire complexe d'aucune des coordonnées globale, χ3 et cobord. [terme hors maître] | CONFIRMÉE | AJOUT | 0 |

### `Round26EXCanonicalTrueZeroCarrier`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `canonicalCarrier_basePoint` (l.99) | Le point de base du carrier canonique de ρ est ρ. [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `canonicalCarrier_reflectedPoint` (l.102) | Le point réfléchi du carrier canonique de ρ est reflectConjZero ρ. | CONFIRMÉE | V63,V80 | 0 |
| `canonicalCarrier_source` (l.105) | La source du carrier canonique de ρ est reflectedRowCoeff ρ. | CONFIRMÉE | AJOUT | 2 |
| `canonicalCarrier_reflectedSource` (l.108) | La source réfléchie du carrier est reflectedRowCoeff(reflectConjZero ρ). | CONFIRMÉE | AJOUT | 0 |
| `canonicalCarrier_state` (l.111) | L'état du carrier au rang n est σ_n (caractère χ3 de l'état premier). | CONFIRMÉE | AJOUT | 0 |
| `canonicalCarrier_signedTransition` (l.114) | La transition signée du carrier vaut indicatrice τ15 − indicatrice τ51. | CONFIRMÉE | AJOUT | 2 |
| `canonicalCarrier_character` (l.120) | Le caractère du carrier au rang n est towerCharacter (p n) ρ. | CONFIRMÉE | V100 | 1 |
| `canonicalCarrier_edgeCocycle` (l.123) | Le cocycle d'arête du carrier est transformedZeroEdgeCocycle ρ n. | CONFIRMÉE | AJOUT | 0 |
| `canonicalCarrier_source_ne_zero` (l.127) | La source du carrier canonique n'est jamais nulle. | CONFIRMÉE | V156 | 5 |
| `canonicalCarrier_toGrammarState` (l.184) | toGrammarState du carrier = σ_n. | CONFIRMÉE | AJOUT | 0 |
| `canonicalCarrier_toTransformedVertex` (l.187) | toTransformedVertex du carrier = transformedZeroGrammarVertex ρ n. | CONFIRMÉE | AJOUT | 0 |
| `canonicalCarrier_toRawSignature` (l.191) | toRawSignature du carrier = reflectedRowCoeff ρ. | CONFIRMÉE | AJOUT | 0 |
| `canonicalCarrier_toTwistedTower` (l.194) | toTwistedTower du carrier au rang n = twistedTowerCharacter n ρ. | CONFIRMÉE | AJOUT | 1 |
| `canonicalCarrier_toOrientedEdge` (l.198) | toOrientedEdge du carrier = transformedZeroOrientedEdge ρ τ n. | CONFIRMÉE | AJOUT | 0 |
| `canonicalCarrier_toCrossOperator` (l.202) | toCrossOperator du carrier = opérateur croisé réfléchi du vrai zéro ρ. | CONFIRMÉE | AJOUT | 0 |
| `canonicalCarrier_toTwistedTower_eq_trueZeroCarrier` (l.205) | La projection tour tordue du carrier canonique est le carrier de vrai zéro trueZeroCarrier. | CONFIRMÉE | AJOUT | 2 |
| `prod_transformedZeroEdgeCocycle_Ico` (l.214) | Le produit des cocycles d'arête sur [M,N) télescope en le cocycle d'échelle entre p_M et p_N. | CONFIRMÉE (domaine: M≤N) | AJOUT | 1 |
| `canonicalCarrier_toBlockHolonomy_eq_towerCharacter_ratio` (l.226) | L'holonomie du carrier sur un bloc [M,N) est le rapport des caractères de Tour en p_N et p_M. | CONFIRMÉE (domaine: M≤N) | V100 | 12 |
| `canonicalCarrier_toBlockHolonomy_eq_crossTransport_zero_one` (l.242) | L'holonomie du carrier sur [2,4) est l'entrée (0,1) du transport croisé réfléchi. | CONFIRMÉE | AJOUT | 7 |
| `canonicalCarrier_reflected_toBlockHolonomy_eq_crossTransport_one_zero` (l.251) | L'holonomie du carrier réfléchi sur [2,4) est l'entrée (1,0) du transport croisé réfléchi. | CONFIRMÉE | V80 | 6 |
| `crossTransport_eq_carrier_holonomies` (l.262) | Le transport croisé réfléchi est la matrice antidiagonale des holonomies du carrier et de son réfléchi sur [2,4). | CONFIRMÉE | AJOUT | 0 |
| `canonicalCarrier_toSectorPartial_sub` (l.281) | La différence des sommes partielles de secteur τ15−τ51 du carrier égale la somme du cobord signé × source × cocycle × poids premier. | CONFIRMÉE | AJOUT | 0 |
| `canonicalCarrier_toSectorPartial_add` (l.302) | La somme des deux sommes partielles de secteur du carrier égale la somme du coefficient croisé × source × cocycle × poids premier. | CONFIRMÉE | AJOUT | 0 |
| `towerCharacter_mul_primeDirichletWeight` (l.331) | Le caractère de Tour absorbe le poids de Dirichlet premier : il translate l'argument de ρ−1/2. | CONFIRMÉE | V100,V102 | 7 |
| `canonicalCarrier_toAccumulatedSectorPartial_eq_shifted` (l.356) | Le canal transformé accumulé du carrier est source/caractère(p2) × la somme non transformée évaluée en s+(ρ−1/2). | CONFIRMÉE | V102 | 0 |
| `canonicalCarrier_accumulated_constant_ne_zero` (l.386) | La constante multiplicative source/caractère(p2) du canal accumulé est non nulle. | CONFIRMÉE | AJOUT | 0 |
| `canonicalCarrier_toAccumulatedSectorPartialFrom_eq_shifted` (l.414) | Pour toute base M, le canal accumulé est la constante d'accumulation × la somme non transformée translatée de ρ−1/2. | CONFIRMÉE | AJOUT | 1 |
| `canonicalCarrier_toBlockHolonomy_eq_accumulationConstant_ratio` (l.436) | L'holonomie du bloc [M,N) est le rapport des constantes d'accumulation en M et N. | CONFIRMÉE (domaine: M≤N) | AJOUT | 5 |
| `canonicalCarrier_accumulationConstant_orientation_blind` (l.456) | Les orientations τ15 et τ51 du même point de base reçoivent la même constante d'accumulation. | CONFIRMÉE | AJOUT | 0 |

### `Round26EYCarrierFidelityRegistry`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `carrier_zeroCarrierSurface` (l.41) | Le carrier de vrai zéro est la projection tour tordue du carrier canonique. [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `carrier_individualMemberSurface` (l.47) | Le point de base du carrier est le point de base de sa propre fibre de hauteur. | CONFIRMÉE | AJOUT | 1 |
| `carrier_reflectedZeroSurface` (l.60) | Le point réfléchi du carrier est un zéro non trivial. | CONFIRMÉE | V63,V74 | 1 |
| `carrier_sameHeightSurface` (l.66) | Les deux points de base du carrier ont la même partie imaginaire. | CONFIRMÉE | V65 | 1 |
| `carrier_reflectedRadialSurface` (l.73) | La partie réelle du point réfléchi vaut 1 moins celle du point de base. | CONFIRMÉE | V65 | 1 |
| `carrier_chi3GrammarSurface` (l.88) | Pour n≥2, la projection tour tordue = χ3(p_n) × caractère du carrier. | CONFIRMÉE (domaine: 2≤n) | AJOUT | 0 |
| `carrier_tau15Surface` (l.103) | Pour n≥2, la transition signée du carrier vaut +1 exactement sur l'arête 1→5 (p_n≡1, p_{n+1}≡5 mod 6). | CONFIRMÉE (domaine: 2≤n) | V174 | 0 |
| `carrier_tau51Surface` (l.113) | Pour n≥2, la transition signée vaut −1 exactement sur l'arête 5→1. | CONFIRMÉE (domaine: 2≤n) | V174 | 0 |
| `carrier_harmonicTowerSurface` (l.135) | Le noyau de transport bâti sur le carrier réalise le module de la tour harmonique. | CONFIRMÉE | AJOUT | 0 |
| `carrier_trueZeroTransportSurface` (l.149) | Les deux entrées du transport croisé sont les holonomies du carrier et de son réfléchi sur [2,4). | CONFIRMÉE | AJOUT | 1 |
| `carrier_radialDefectSurface` (l.165) | L'opérateur croisé du carrier est la matrice antidiagonale (11/5)^{−(re−1/2)}, (11/5)^{re−1/2}. | CONFIRMÉE | V102 | 0 |
| `carrier_radialOperatorSurface` (l.172) | L'opérateur croisé du carrier est radialCrossOperator(re ρ − 1/2). | CONFIRMÉE | V102 | 0 |
| `carrier_reflectionReciprocitySurface` (l.177) | Le produit des deux entrées hors-diagonale de l'opérateur croisé vaut 1. | CONFIRMÉE | AJOUT | 0 |
| `carrier_involutionSurface` (l.183) | L'opérateur croisé au carré vaut l'identité. | CONFIRMÉE | AJOUT | 0 |
| `carrier_adjointSurface` (l.188) | Le conjugué transposé de l'opérateur croisé est l'antidiagonale (r^{re−1/2}, r^{−(re−1/2)}), r=crossBlockRatio. | CONFIRMÉE | AJOUT | 0 |
| `carrier_ttStarSurface` (l.195) | T·T* = diag(r^{−2(re−1/2)}, r^{2(re−1/2)}). | CONFIRMÉE | AJOUT | 0 |
| `carrier_tStarTSurface` (l.202) | T*·T = diag(r^{2(re−1/2)}, r^{−2(re−1/2)}). | CONFIRMÉE | AJOUT | 0 |
| `carrier_orientedFidelity_iff_holonomy_eq` (l.220) | Les deux orientations de l'opérateur croisé sont égales ssi l'holonomie du carrier égale celle du réfléchi sur [2,4). | CONFIRMÉE | V140 | 1 |
| `carrier_holonomy_eq_iff_critical` (l.242) | L'égalité des holonomies du carrier et de son réfléchi sur [2,4) ⟺ re ρ = 1/2. | CONFIRMÉE | V140,V161 | 1 |
| `carrier_critical_iff_accumulationConstant_ratio_eq` (l.259) | re ρ = 1/2 ⟺ le rapport des constantes d'accumulation en 2 et 4 est égal pour le carrier et son réfléchi. | CONFIRMÉE | V140,V161 | 0 |

### `Round26EZCanonicalCarrierCore`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `core_toSnapshot_eq` (l.122) | Le snapshot du core d'un vrai zéro est le carrier canonique. [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `canonicalCore_zero` (l.132) | Le zéro du core canonique de ρ est ρ. | CONFIRMÉE | AJOUT | 0 |
| `canonicalCore_toSnapshot` (l.135) | Le snapshot du core canonique de ρ est canonicalCarrier ρ. | CONFIRMÉE | AJOUT | 0 |
| `canonicalCore_source_ne_zero` (l.138) | La source de tout core canonique est non nulle. | CONFIRMÉE | V156 | 0 |
| `core_state_eq_sigma` (l.151) | Le champ state du core est le signe grammatical sigma. | CONFIRMÉE | AJOUT | 0 |
| `core_one_sub_two_cross_eq_state_mul` (l.155) | Pour n≥2, 1−2·cross n = state n · state(n+1). | CONFIRMÉE (domaine: 2≤n) | V174 | 0 |
| `core_grammarRigidSurface` (l.179) | Le bloc grammatical projeté du core est rigide. | CONFIRMÉE (domaine: 2≤n) | V174 | 1 |
| `core_grammarProjectionSurface` (l.193) | Pour n≥2, classes d'écart 0/2/4 ⟺ transitions d'état (égal, 5→1, 1→5). | CONFIRMÉE (domaine: 2≤n) | V174 | 1 |
| `core_grammarCompositionSurface` (l.202) | Le produit sur [M,N) de (1−2 cross n) vaut state M × state N. | CONFIRMÉE (domaine: 2≤M≤N) | V174 | 1 |
| `core_grammarReturnSurface` (l.210) | Si state A = state B, le produit sur [A,B) de (1−2 cross) vaut 1. | CONFIRMÉE (domaine: state A = state B ) | V174 | 1 |
| `core_inverseTransitionSurface` (l.225) | Pour états s,t dans {1,5}, la transformation vaut τ11/τ15/τ51/τ55 exactement pour (1,1)/(1,5)/(5,1)/(5,5). | CONFIRMÉE (domaine: s,t ∈ {1,5} ) | V174 | 1 |
| `core_crossNonCoboundarySurface` (l.239) | La projection croisée du core n'est le cobord d'aucun potentiel ψ. | CONFIRMÉE | AJOUT | 1 |
| `core_fiberPairSurface` (l.264) | Les deux points de fibre du core sont deux zéros non triviaux de même hauteur. | CONFIRMÉE | V63,V65 | 1 |
| `core_tau15FiberSurface` (l.279) | La première composante de la fibre orientée est le vecteur de secteur τ15 au point de fibre (γ,σ). | CONFIRMÉE | AJOUT | 1 |
| `core_tau51FiberSurface` (l.285) | La seconde composante est le vecteur de secteur τ51. | CONFIRMÉE | AJOUT | 1 |
| `core_tauFiberSurface_at_core` (l.290) | Au point de fibre du core, les composantes orientées sont les deux secteurs du canal premier lus au vrai zéro. | CONFIRMÉE | AJOUT | 0 |
| `core_towerMultiplierSurface` (l.301) | Les deux composantes de la fibre orientée sont des séries sur p_n avec un multiplicateur de Tour commun. | CONFIRMÉE | V100 | 1 |
| `core_grammarTowerSupportSurface` (l.315) | La grammaire sélectionne le support des étages (1+σ^m≠0 ⟺ σ=1 ou m pair) et les puissances paires se replient sur le caractère au carré. | CONFIRMÉE | AJOUT | 0 |
| `core_commonTransportSurface` (l.327) | Les deux entrées du transport croisé sont les rapports de caractères de Tour en p4 et p2 aux deux points de fibre. | CONFIRMÉE | V100 | 0 |
| `core_commonHeightPhaseSurface` (l.339) | La phase de hauteur est la même aux deux points de base du core, non nulle, et relie l'opérateur croisé au transport (opérateur = phase⁻¹ · transport). | CONFIRMÉE | V65 | 1 |
| `core_primeChannelSurface` (l.359) | Pour Re s>1, le canal premier du core = secteurs diagonaux τ11+τ55 + fibre croisée. | CONFIRMÉE (domaine: 1<σ (région sans vrai zéro) ) | AJOUT | 1 |
| `core_meromorphicSurface` (l.371) | Ou bien le zéro du core est critique, ou bien le canal premier a un pôle simple en l'un des deux points de fibre du core. | CONFIRMÉE | V126 | 1 |
| `core_toMinusFidelity` (l.393) | Un objet GrammarTowerZeroFidelityObjectMinusFidelity (32 champs sur 33) se construit depuis tout core canonique. | CONFIRMÉE | V140 | 0 |
| `core_alone_cannot_close` (l.437) | (Pour tout core canonique, RiemannHypothesis) ⟺ RiemannHypothesis. | ÉQUIVALENTE À RH | V140,I4 | 0 |

### `Round26FALocalEdgeChannel`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `transformedZeroEdgeCocycle_eq_towerCharacter_ratio` (l.64) | Le cocycle d'arête sur l'arête n est le rapport des caractères de Tour en p_{n+1} et p_n. | CONFIRMÉE | V100 | 8 |
| `localEdgeDefect_pos_arg` (l.78) | p_{n+1}/p_n² > 0. [terme hors maître] | CONFIRMÉE | AJOUT | 3 |
| `localEdgeDefect_ne_zero` (l.81) | Le défaut local d'arête est toujours non nul. | CONFIRMÉE | AJOUT | 1 |
| `localEdgeDefect_eq_ratio` (l.84) | Défaut local = caractère(p_{n+1}) / caractère(p_n)². | CONFIRMÉE | AJOUT | 2 |
| `localEdgeTerm_eq_defect_mul_shifted` (l.95) | Cocycle d'arête × poids premier(s) = défaut local × poids premier(s+ρ−1/2). | CONFIRMÉE | V102 | 3 |
| `canonicalCarrier_toSectorPartial_term_exact` (l.108) | Chaque terme du canal sectoriel local du carrier = source × indicatrice × défaut local × poids translaté. | CONFIRMÉE | AJOUT | 1 |
| `canonicalCarrier_toSectorPartial_eq_defect_weighted` (l.128) | Le canal sectoriel local partiel = somme translatée pondérée par le défaut local (le facteur ne sort pas de la somme). | CONFIRMÉE | AJOUT | 0 |
| `localEdgeDefect_two_div_three` (l.151) | Le rapport des défauts locaux aux indices 2 et 3 vaut towerCharacter(343/275) ρ. | CONFIRMÉE | AJOUT | 1 |
| `localEdgeDefect_eq_forces_critical` (l.165) | Si le défaut local prend la même valeur aux indices 2 et 3, alors re ρ = 1/2. | CONFIRMÉE SOUS CONDITION (défaut(2)=défaut(3)) | V102,V161 | 0 |
| `norm_localEdgeDefect_eq_one_of_critical` (l.184) | Pour re ρ = 1/2, le défaut local a module 1 à chaque arête. | CONFIRMÉE (domaine: re ρ=1/2 ) | V102 | 0 |
| `vertexCharacterTerm_eq_shifted` (l.216) | Le terme du canal caractère de sommet est un translaté pur du poids premier en s+(ρ−1/2). | CONFIRMÉE | AJOUT | 1 |
| `rawSignatureTerm_eq_shifted` (l.224) | Le terme de signature brute = source × poids premier en s−(ρ−1/2) (translaté dans l'autre sens). | CONFIRMÉE | AJOUT | 1 |
| `localEdgeChannelTerm_eq_defect_mul_shifted` (l.237) | Le terme du canal d'arête local = source × défaut local × poids translaté. | CONFIRMÉE | AJOUT | 1 |
| `accumulatedChannelTerm_eq_shifted` (l.256) | Le terme du canal accumulé = constante d'accumulation × poids translaté (n ≥ M). | CONFIRMÉE (domaine: M≤n) | AJOUT | 1 |
| `four_channel_comparison` (l.273) | Comparaison des quatre canaux : sommet, signature brute et accumulé sont des translatés à facteur constant ; seul l'arête locale a un facteur variant avec l'arête. | CONFIRMÉE | AJOUT | 0 |
| `abel_summation_finite` (l.307) | Identité d'Abel finie pour suites arbitraires φ, B sur [M,N). | CONFIRMÉE (domaine: M≤N) | AJOUT | 1 |
| `localTwistedCoboundary_abel` (l.320) | Le cobord tordu local du carrier sur [M,N) = terme de bord − somme d'incréments du poids tordu. | CONFIRMÉE (domaine: M≤N) | AJOUT | 0 |
| `twistedEdgeWeight_increment` (l.358) | L'incrément du poids d'arête tordu = défaut(n+1)·poids(n+1) − défaut(n)·poids(n) (poids translatés). | CONFIRMÉE | AJOUT | 1 |
| `twistedEdgeWeight_increment_explicit` (l.372) | Même incrément écrit avec towerCharacter aux arguments p_{n+2}/p_{n+1}² et p_{n+1}/p_n². | CONFIRMÉE | AJOUT | 0 |

### `Round26FBReflectedSourceAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `reflectConjZero_val` (l.67) | Le point réfléchi est 1 − conj ρ. | CONFIRMÉE | V63,V65 | 2 |
| `carrier_reflected_multiplicity` (l.72) | La multiplicité de zêta est conservée par l'involution de réflexion, sans condition. | CONFIRMÉE | V63,V65 | 4 |
| `source_mul_eq_reflectedSource_mul` (l.80) | source × ρ(ρ+1) = source réfléchie × ρ*(ρ*+1) (la multiplicité s'élimine). | CONFIRMÉE | AJOUT | 2 |
| `zero_sub_reflected_eq_two_radial_defect` (l.101) | ρ − ρ* = 2(re ρ − 1/2) (réel). | CONFIRMÉE | V102,V161 | 1 |
| `zero_add_reflected_add_one_ne_zero` (l.110) | ρ + ρ* + 1 ≠ 0 (partie réelle 2). | CONFIRMÉE | AJOUT | 1 |
| `source_eq_reflectedSource_iff_critical` (l.121) | Source = source réfléchie ⟺ re ρ = 1/2. | CONFIRMÉE | V140,V161 | 0 |
| `reflectedSource_norm_relation` (l.165) | ‖source‖·‖ρ(ρ+1)‖ = ‖source réfléchie‖·‖ρ*(ρ*+1)‖. | CONFIRMÉE | V102 | 0 |
| `source_mul_conj_reflectedSource` (l.175) | source × conj(source réfléchie) = source × conj(−m/(ρ*(ρ*+1))). | CONFIRMÉE | AJOUT | 0 |
| `eventually_re_lt_one_of_isNontrivialZetaZero` (l.200) | Tout zéro non trivial a un voisinage dans {Re s<1}. | CONFIRMÉE (domaine: ρ zéro non trivial ) | V7 | 1 |
| `sectorContinuation_pointwise_is_vacuous` (l.209) | Il existe une continuation sectorielle égale à la série pour Re s>1 et méromorphe en chaque vrai zéro (inconditionnel). | CONFIRMÉE | V125,I12 | 1 |
| `sectorContinuation_pointwise_not_a_lock` (l.229) | Sous l'existence d'une telle continuation, RiemannHypothesis ⟺ RiemannHypothesis (tautologie). | ÉQUIVALENTE À RH | V125,I12 | 0 |
| `commonFactorWeld_everywhere_is_rh` (l.250) | Paire orientée, F51 méromorphe à pôle en chaque zéro non trivial, soudure à facteur commun en chaque zéro ⟹ RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126,I4,O5 | 0 |

### `Round26FCGlobalLaurentProvenance`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `tendsto_mul_primeGrammarChannelContinuation_zero` (l.48) | En un zéro de zêta de Re>1/2, (w−ρ)·canal premier continué → −m(ρ). | CONFIRMÉE SOUS CONDITION (zêta(ρ)=0, Re ρ>1/2) | V100 | 2 |
| `residue_primeGrammarChannelContinuation_zero` (l.84) | En un zéro de zêta de Re>1/2, le résidu du canal premier continué vaut −m(ρ). | CONFIRMÉE SOUS CONDITION (zêta(ρ)=0, Re ρ>1/2) | V100 | 2 |
| `residue_negLogDeriv_reflectConj_eq` (l.90) | Le résidu de −ζ'/ζ en ρ* égale celui en ρ (conservation de la multiplicité). | CONFIRMÉE | V63,V65 | 0 |
| `residue_primeGrammarChannelContinuation_eq_reflected_global` (l.104) | Pour Re ρ>1/2, résidu du canal premier en ρ = résidu de −ζ'/ζ au point réfléchi. | CONFIRMÉE (domaine: 1/2<Re ρ ) | V63 | 1 |
| `residue_primeGrammarChannelContinuation_eq_carrier_source_mul` (l.119) | Pour Re ρ>1/2, résidu du canal premier en ρ = source du carrier × ρ(ρ+1). | CONFIRMÉE (domaine: 1/2<Re ρ ) | V100 | 1 |
| `residue_primeGrammarChannelContinuation_ne_zero` (l.134) | Pour Re ρ>1/2, le résidu du canal premier en ρ est non nul. | CONFIRMÉE (domaine: 1/2<Re ρ ) | V156 | 1 |
| `residue_negLogDeriv_reflected_ne_zero` (l.142) | Pour Re ρ>1/2, le résidu de −ζ'/ζ au point réfléchi est non nul. | CONFIRMÉE (domaine: 1/2<Re ρ ) | V63 | 0 |

### `Round26FDOrientedResidueCarrierWeld`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `_private.RhGapCriterion.Round26FDOrientedResidueCarrierWeld.0.RhGap.tendsto_centered_factor_zero` (l.26) | (w−ρ) → 0 quand w → ρ (w≠ρ). | CONFIRMÉE | AJOUT | 3 |
| `tendsto_mul_globalTailContinuation_zero` (l.32) | En un zéro de zêta de Re>1/2, (w−ρ)·queue globale continuée → −m(ρ). | CONFIRMÉE SOUS CONDITION (zêta(ρ)=0, Re ρ>1/2) | V100 | 1 |
| `tendsto_mul_crossChannelContinuation_zero` (l.52) | Si Corr analytique en ρ, zêta(ρ)=0, Re ρ>1/2, (w−ρ)·continuation croisée → ½·(−m(ρ)). | CONFIRMÉE SOUS CONDITION (Corr analytique en ρ, zêta(ρ)=0, Re ρ>1/2) | AJOUT | 2 |
| `tendsto_mul_coboundaryChannelLimit_zero` (l.81) | Pour Re ρ>1/2, (w−ρ)·limite du cobord → 0 : le cobord holomorphe ne contribue pas au résidu au zéro. | CONFIRMÉE (domaine: 1/2<Re ρ ) | AJOUT | 2 |
| `tendsto_mul_orientedTau15Cont_zero` (l.90) | Si Corr analytique en ρ, zêta(ρ)=0, Re ρ>1/2, (w−ρ)·continuation orientée τ15 → ¼·(−m(ρ)). | CONFIRMÉE SOUS CONDITION (Corr analytique en ρ, zêta(ρ)=0, Re ρ>1/2) | AJOUT | 2 |
| `tendsto_mul_orientedTau51Cont_zero` (l.115) | Même limite ¼·(−m(ρ)) pour la continuation orientée τ51. | CONFIRMÉE (domaine: idem ) | AJOUT | 2 |
| `residue_orientedTau15Cont_zero` (l.140) | Sous les mêmes conditions, le résidu de la continuation τ15 en ρ vaut ¼·(−m(ρ)). | CONFIRMÉE SOUS CONDITION (Corr analytique en ρ, zêta(ρ)=0, Re ρ>1/2) | AJOUT | 2 |
| `residue_orientedTau51Cont_zero` (l.149) | Même résidu ¼·(−m(ρ)) pour τ51. | CONFIRMÉE (domaine: idem ) | AJOUT | 1 |
| `residue_orientedTau15_eq_tau51` (l.158) | Sous les mêmes conditions, les résidus des continuations τ15 et τ51 en ρ sont égaux. | CONFIRMÉE (domaine: idem ) | V35 | 0 |
| `residue_orientedTau15Cont_ne_zero` (l.167) | Pour un zéro non trivial ρ avec Corr analytique et Re ρ>1/2, le résidu commun τ15 est non nul. | CONFIRMÉE SOUS CONDITION (Corr analytique en ρ, Re ρ>1/2) | AJOUT | 0 |
| `carrierOrientedResidue_ne_zero` (l.187) | Le résidu orienté du carrier de tout zéro non trivial est non nul. | CONFIRMÉE | AJOUT | 4 |
| `canonicalCarrier_accumulationConstant_ne_zero_at` (l.194) | La constante d'accumulation du carrier à toute base M est non nulle. | CONFIRMÉE | AJOUT | 6 |
| `carrierBaseLaurentDatum_ratio_eq_blockHolonomy` (l.202) | Le rapport des données de Laurent de base en M et N égale l'holonomie de bloc du carrier. | CONFIRMÉE (domaine: M≤N) | AJOUT | 4 |
| `carrierBaseLaurentDatum_ratio_eq_crossTransport_zero_one` (l.215) | Le rapport des données de Laurent en 2 et 4 est l'entrée (0,1) du transport croisé réfléchi. | CONFIRMÉE | AJOUT | 2 |
| `carrierBaseLaurentDatum_reflected_ratio_eq_crossTransport_one_zero` (l.224) | Le rapport des données de Laurent du point réfléchi en 2 et 4 est l'entrée (1,0) du transport. | CONFIRMÉE | AJOUT | 2 |

### `Round26FDPerronCarrierHolonomy`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `residue_perronZetaIntegrand_zero_eq_nontrivialZeroResidueTerm` (l.48) | Le résidu en ρ de −ζ'/ζ·Perron.f P est le terme individuel nontrivialZeroResidueTerm P ρ. | CONFIRMÉE (domaine: 0<P) | V100 | 2 |
| `centeredPerronResidueSignature_eq_rawZeroPrimeSignature` (l.67) | Le résidu de Perron centré est la signature brute du carrier. | CONFIRMÉE (domaine: 0<P) | AJOUT | 3 |
| `centeredPerronResidueSignature_ratio_eq_crossScaleSignature` (l.84) | Le quotient de deux résidus de Perron centrés est la signature inter-échelles. | CONFIRMÉE (domaine: 0<P,0<Q) | AJOUT | 1 |
| `centeredPerronResidueSignature_ratio_eq_transformedZeroScaleCocycle` (l.94) | Le même quotient est le cocycle d'échelle transformé. | CONFIRMÉE (domaine: 0<P,0<Q) | AJOUT | 1 |
| `centeredPerronResidueSignature_ratio_eq_carrier_holonomy` (l.103) | Sur [M,N), l'holonomie du carrier est le quotient des résidus de Perron centrés en p_M et p_N. | CONFIRMÉE (domaine: M≤N) | AJOUT | 7 |
| `centeredPerronResidueSignature_ratio_eq_crossTransport_zero_one` (l.123) | Sur [2,4), le quotient de résidus au point de base est l'entrée (0,1) du transport réfléchi. | CONFIRMÉE | AJOUT | 1 |
| `centeredPerronResidueSignature_reflect_ratio_eq_crossTransport_one_zero` (l.133) | Sur [2,4), le quotient de résidus au point réfléchi est l'entrée (1,0) du transport. | CONFIRMÉE | AJOUT | 1 |
| `trueZeroReflectedCrossOperator_zero_one_eq_perron_ratio` (l.144) | Entrée (0,1) de l'opérateur croisé = phase de hauteur⁻¹ × quotient de résidus de Perron en p2 et p4. | CONFIRMÉE | AJOUT | 1 |
| `trueZeroReflectedCrossOperator_one_zero_eq_reflected_perron_ratio` (l.158) | Entrée (1,0) = phase⁻¹ × quotient de résidus de Perron du point réfléchi en p2 et p4. | CONFIRMÉE | AJOUT | 1 |
| `orientedFidelity_at_rho_iff_centeredPerronResidue_ratio_eq` (l.169) | Égalité des deux entrées de l'opérateur croisé ⟺ égalité des quotients de résidus de Perron du couple réfléchi en p2 et p4. | CONFIRMÉE | V140,V161 | 1 |

### `Round26FEAccumulatedCarrierResidueRealization`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `_private.RhGapCriterion.Round26FEAccumulatedCarrierResidueRealization.0.RhGap.tendsto_carrier_shift_punctured` (l.27) | s ↦ s+(ρ−1/2) envoie un voisinage pointé de 1/2 dans un voisinage pointé de ρ. | CONFIRMÉE | AJOUT | 2 |
| `tendsto_mul_carrierAccumulatedTau15Cont_half` (l.54) | Si Corr analytique en ρ et Re ρ>1/2, (s−1/2)·continuation accumulée τ15 → donnée de Laurent de base du carrier en 1/2. | CONFIRMÉE SOUS CONDITION (Corr analytique en ρ, Re ρ>1/2) | AJOUT | 1 |
| `tendsto_mul_carrierAccumulatedTau51Cont_half` (l.86) | Même limite pour la continuation accumulée τ51. | CONFIRMÉE (domaine: idem ) | AJOUT | 1 |
| `residue_carrierAccumulatedTau15Cont_half` (l.117) | Le résidu en 1/2 de la continuation accumulée τ15 est la donnée de Laurent de base du carrier. | CONFIRMÉE SOUS CONDITION (Corr analytique en ρ, Re ρ>1/2) | AJOUT | 1 |
| `residue_carrierAccumulatedTau51Cont_half` (l.126) | Même énoncé pour τ51. | CONFIRMÉE (domaine: idem ) | AJOUT | 1 |
| `residue_carrierAccumulatedTau15_ratio_eq_blockHolonomy` (l.135) | Le rapport des résidus τ15 accumulés aux bases M et N égale l'holonomie de bloc du carrier. | CONFIRMÉE SOUS CONDITION (Corr analytique en ρ, Re ρ>1/2) | AJOUT | 1 |
| `residue_carrierAccumulatedTau51_ratio_eq_blockHolonomy` (l.148) | Même égalité pour τ51. | CONFIRMÉE (domaine: idem ) | AJOUT | 0 |
| `residue_carrierAccumulatedTau15_ratio_eq_crossTransport_zero_one` (l.160) | Sur [2,4), le rapport des résidus τ15 accumulés est l'entrée (0,1) du transport croisé réfléchi. | CONFIRMÉE SOUS CONDITION (Corr analytique en ρ, Re ρ>1/2) | AJOUT | 0 |

### `Round26FGSixWayTerminalSocketMatrix`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `grammarTowerZeroFidelityObject_of_orientedFidelitySurface` (l.49) | La surface de fidélité orientée (terminale) construit l'objet complet grammaire-Tour-zéro (33/33). [terme hors maître] | CONFIRMÉE (domaine: OrientedFidelitySurface (⟺ RH par orientedFidelitySurface_iff_rh) ) | AJOUT | 2 |
| `rh_of_orientedFidelitySurface` (l.55) | OrientedFidelitySurface entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V140,O5 | 7 |
| `orientedFidelitySurface_of_rh` (l.60) | RiemannHypothesis entraîne la surface de fidélité orientée. | CONFIRMÉE SOUS CONDITION (RH en hypothèse) | V140 | 1 |
| `orientedFidelitySurface_iff_rh` (l.65) | La surface de fidélité orientée équivaut à RiemannHypothesis. | ÉQUIVALENTE À RH | V140,V126 | 1 |
| `re_eq_half_of_rh` (l.69) | Sous RiemannHypothesis, tout zéro non trivial du sous-type a re = 1/2. | CONFIRMÉE SOUS CONDITION (RH: hypothèse RH (prémisse), conclusion re=1/2 par zéro) | AJOUT | 5 |
| `p_two_ne_p_four` (l.73) | Les premiers p 2 et p 4 (bloc certifié [2,4)) sont distincts. | CONFIRMÉE | AJOUT | 0 |
| `centeredPerronResidueSignature_ne_zero` (l.78) | La signature de Perron centrée d'un zéro ne s'annule pas à une échelle P>0. | CONFIRMÉE (domaine: 0<P) | V100 | 3 |
| `h1Determinant_iff_h1Ratio` (l.115) | Les prémisses H1Determinant et H1Ratio sont équivalentes. | ÉQUIVALENTE À RH | AJOUT | 1 |
| `h1Lambda_of_h1Ratio` (l.127) | H1Ratio entraîne H1Lambda. | CONFIRMÉE (domaine: H1Ratio (⟺ RH via h1Determinant_iff_h1Ratio, h1Determinant_iff_rh) ) | AJOUT | 0 |
| `h1Ratio_of_h1Lambda` (l.141) | H1Lambda entraîne H1Ratio. | CONFIRMÉE (domaine: H1Lambda ) | AJOUT | 0 |
| `orientedFidelitySurface_of_h1` (l.148) | H1Determinant entraîne la surface de fidélité orientée. | CONFIRMÉE (domaine: H1Determinant (⟺ RH par h1Determinant_iff_rh) ) | AJOUT | 3 |
| `rh_of_h1` (l.154) | H1Determinant entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | AJOUT | 1 |
| `h1Determinant_iff_rh` (l.158) | H1Determinant équivaut à RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 2 |
| `carrierBaseLaurentDatum_ne_zero` (l.172) | La donnée de Laurent de base du porteur canonique d'un zéro n'est jamais nulle. [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `crossTransport_offdiag_eq_of_h2` (l.183) | Sous H2, les deux transports croisés réfléchis (0,1) et (1,0) sont égaux pour tout zéro. | CONFIRMÉE (domaine: H2BaseIndependentReflectionFactor (⟺ RH par h2_iff_rh) ) | AJOUT | 1 |
| `orientedFidelitySurface_of_h2` (l.193) | H2BaseIndependentReflectionFactor entraîne la surface de fidélité orientée. | CONFIRMÉE (domaine: H2 (⟺ RH) ) | AJOUT | 2 |
| `rh_of_h2` (l.200) | H2BaseIndependentReflectionFactor entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | AJOUT | 1 |
| `h2_iff_rh` (l.203) | H2BaseIndependentReflectionFactor équivaut à RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 1 |
| `h5_iff_h1` (l.224) | H5RankOne équivaut à H1Determinant. | ÉQUIVALENTE À RH | AJOUT | 2 |
| `orientedFidelitySurface_of_h5` (l.229) | H5RankOne entraîne la surface de fidélité orientée. | CONFIRMÉE (domaine: H5RankOne (⟺ RH) ) | AJOUT | 2 |
| `rh_of_h5` (l.233) | H5RankOne entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | AJOUT | 0 |
| `h5_iff_rh` (l.236) | H5RankOne équivaut à RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 1 |
| `tableEntry_carries_member_amplitude_and_two_scales` (l.247) | L'entrée individuelle de la table vaut C(ρ)·(p_{n+k+1}^ρ − p_{n+k}^ρ) : amplitude du zéro et deux échelles premières. | CONFIRMÉE | V100,V172 | 0 |
| `totalColumnBridge_value_is_member_free` (l.258) | La somme sur tous les zéros des contributions de colonne égale une quantité purement première (Von Mangoldt lissé moins fond lissé, différence entre deux premiers). | CONFIRMÉE | V121,V124 | 0 |
| `orientedFidelitySurface_of_h3` (l.275) | H3GrammarChangeCompatibility entraîne la surface de fidélité orientée. | CONFIRMÉE (domaine: H3 (⟺ RH par h3_iff_rh) ) | AJOUT | 2 |
| `rh_of_h3` (l.285) | H3GrammarChangeCompatibility entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | AJOUT | 1 |
| `h3_iff_rh` (l.288) | H3GrammarChangeCompatibility équivaut à RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 1 |
| `norm_grammarHeightQ` (l.299) | Le nombre complexe grammarHeightQ n ρ est de norme 1. | CONFIRMÉE | AJOUT | 1 |
| `orientedFidelitySurface_of_h4` (l.311) | H4PhaseRealization entraîne la surface de fidélité orientée. | CONFIRMÉE (domaine: H4 (⟺ RH par h4_iff_rh) ) | AJOUT | 2 |
| `rh_of_h4` (l.320) | H4PhaseRealization entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | AJOUT | 1 |
| `h4_iff_rh` (l.323) | H4PhaseRealization équivaut à RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 1 |
| `reflectedFiberSecondMoment_eq_square` (l.353) | Le second moment de fibre réfléchie vaut mult² · (e^{(β−1/2)a} − e^{(1/2−β)a})² : un carré parfait. | CONFIRMÉE | V102 | 2 |
| `reflectedFiberSecondMoment_nonneg` (l.368) | Le second moment de fibre réfléchie est ≥ 0. | CONFIRMÉE | AJOUT | 0 |
| `reflectedFiberSecondMoment_eq_zero_iff_critical` (l.374) | À une échelle a≠0, le second moment est nul ssi re ρ = 1/2. | CONFIRMÉE (domaine: a ≠ 0) | V161,V162 | 2 |
| `orientedFidelitySurface_of_h6` (l.399) | H6FiberSecondMomentVanishes entraîne la surface de fidélité orientée. | CONFIRMÉE (domaine: H6 (⟺ RH par h6_iff_rh) ) | AJOUT | 2 |
| `rh_of_h6` (l.407) | H6FiberSecondMomentVanishes entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | AJOUT | 1 |
| `h6_iff_rh` (l.410) | H6FiberSecondMomentVanishes équivaut à RiemannHypothesis. | ÉQUIVALENTE À RH | V126 | 1 |
| `height_only_is_blind_to_reflection` (l.422) | Toute fonction de la seule hauteur d'un zéro est invariante par réflexion-conjugaison. | CONFIRMÉE | V159,V162 | 0 |
| `height_list_is_blind_to_memberwise_reflection` (l.430) | Toute fonction de la liste des hauteurs est invariante quand chaque membre est remplacé par son réfléchi. | CONFIRMÉE | V159 | 0 |
| `coupledGrammar_carries_heights_and_prime_block` (l.442) | La grammaire couplée zéros-premiers porte hauteurs et écarts de hauteur, et ses écarts premiers sont non nuls. [terme hors maître] | CONFIRMÉE (domaine: 2 ≤ n ) | V60 | 0 |
| `coupledGrammar_zeroGap_and_primeColumn_same_bundle` (l.453) | Dans la grammaire couplée, l'écart de hauteur en r et la colonne première c sont lus dans le même objet (case pondérée). | CONFIRMÉE (domaine: 2 ≤ n ) | V60 | 0 |
| `twistedCocycle_carries_grammar_height_and_radius` (l.465) | Le caractère de tour tordu vaut χ3(p_n)·caractère de tour et sa norme est p_n^{−(re ρ −1/2)}. | CONFIRMÉE (domaine: 2 ≤ n ) | V102,V158 | 0 |
| `eventualStrict_is_already_unconditional` (l.478) | ReflectedDifferenceEventuallyStrictOnPrimes est vrai (acquis). | CONFIRMÉE | AJOUT | 0 |
| `changeFamilyCompatibility_is_target_strength` (l.483) | ReflectedChangeFamilyCompatibility équivaut à RhGap.RH. | ÉQUIVALENTE À RH | V126 | 0 |
| `sixWay_matrix_is_one_reformulation` (l.494) | Les sept prémisses H1, H2, H3, H4, H5, H6 et la surface de fidélité orientée sont chacune équivalentes à RiemannHypothesis. | ÉQUIVALENTE À RH | V126,O10,I4 | 0 |
| `sixWay_all_build_the_full_tdd_object` (l.508) | Si l'une des six prémisses H1..H6 vaut, l'objet TDD complet est construit. | CONFIRMÉE (domaine: disjonction H1 ∨ … ∨ H6 (chacune ⟺ RH) ) | AJOUT | 0 |

### `Round26FHCentralPrimePivotCarrier`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `central_prime_unique` (l.62) | Tout premier q strictement entre p n et p(n+2) est p(n+1). | CONFIRMÉE (domaine: q premier, p n<q<p(n+2) ) | V61 | 3 |
| `canonical_pivot_prime` (l.78) | p 3 (=7) est premier. | CONFIRMÉE | AJOUT | 1 |
| `canonical_pivot_between` (l.81) | p 2 < p 3 < p 4. | CONFIRMÉE | AJOUT | 1 |
| `canonical_center_unique` (l.85) | Tout premier q avec 5<q<11 vaut 7. | CONFIRMÉE (domaine: q premier, 5<q<11 ) | V61 | 0 |
| `canonical_center_not_arithmetic` (l.92) | Le pivot p 3 n'est pas le milieu arithmétique de p 2 et p 4. | CONFIRMÉE | AJOUT | 0 |
| `canonical_center_not_logarithmic` (l.96) | Le pivot p 3 n'est pas le milieu logarithmique de p 2 et p 4. | CONFIRMÉE | AJOUT | 0 |
| `sigma_two` (l.102) | sigma 2 = −1. | CONFIRMÉE | AJOUT | 5 |
| `sigma_three` (l.106) | sigma 3 = 1. | CONFIRMÉE | AJOUT | 5 |
| `sigma_four` (l.110) | sigma 4 = −1. | CONFIRMÉE | AJOUT | 5 |
| `sourceOneProjector_eq_sectors` (l.122) | Pour n≥2, le projecteur source vaut la somme des indicatrices τ11 et τ15. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 0 |
| `targetOneProjector_eq_sectors` (l.129) | Pour n≥2, le projecteur cible vaut la somme des indicatrices τ11 et τ51. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 0 |
| `targetOneProjector_eq_sourceOneProjector_succ` (l.138) | Le projecteur cible en n égale le projecteur source en n+1. | CONFIRMÉE | AJOUT | 0 |
| `canonical_pivot_projectors` (l.144) | Le sommet canonique 7 est d'état 1 comme cible en 2 et comme source en 3. | CONFIRMÉE | AJOUT | 0 |
| `canonical_pivot_edges` (l.151) | Les arêtes autour du pivot canonique sont τ51 (entrante) et τ15 (sortante). | CONFIRMÉE | AJOUT | 2 |
| `odd_floor_support_iff` (l.161) | Pour m impair, 1+σ_n^m ≠ 0 ssi σ_n = 1. | CONFIRMÉE (domaine: m impair) | AJOUT | 2 |
| `canonical_odd_floor_support_word` (l.171) | Pour m impair, le mot de support du bloc [5,7,11] est [0,1,0]. | CONFIRMÉE (domaine: m impair) | AJOUT | 0 |
| `oddFloorPivot_iff_sigmaPattern` (l.184) | Pour m impair, le mot de support [0,1,0] équivaut au motif de signes [−1,+1,−1]. | CONFIRMÉE (domaine: m impair) | AJOUT | 1 |
| `sigmaPattern_iff_transitionPair` (l.202) | Pour n≥2, le motif [−1,+1,−1] équivaut à la paire de transitions [τ51,τ15]. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 5 |
| `transformedZeroEdgeCocycle_ne_zero` (l.235) | Le cocycle d'arête du zéro transformé n'est jamais nul. | CONFIRMÉE | AJOUT | 2 |
| `towerCharacter_mul_edgeCocycle` (l.242) | Caractère du bord gauche × cocycle entrant = caractère du pivot (q_n κ_n = q_{n+1}). | CONFIRMÉE | V101 | 3 |
| `towerCharacter_div_edgeCocycle` (l.251) | Caractère du bord droit / cocycle sortant = caractère du pivot. | CONFIRMÉE | V101 | 3 |
| `centralPivotIncidenceFactorization` (l.266) | Les deux incidences du pivot p_{n+1} produisent la même quantité spectrale. | CONFIRMÉE | AJOUT | 0 |
| `canonicalCentralPivotIncidence` (l.274) | Sur [5,7,11] : caractère(5)·cocycle(2) = caractère(7) et caractère(11)/cocycle(3) = caractère(7). | CONFIRMÉE | AJOUT | 0 |
| `centralPivotMemberSensitiveFactorization` (l.288) | Pour tout zéro, la factorisation centrale des deux incidences se tient avec la source vrai-zéro du porteur canonique. | CONFIRMÉE | V100,V172 | 0 |
| `edgeProduct_eq_boundary_transport` (l.315) | Le produit des deux arêtes est le caractère de tour du rapport p(n+2)/p n : le pivot disparaît. | CONFIRMÉE | AJOUT | 0 |
| `edgeCurvature_eq_central_log_curvature` (l.329) | Le rapport des deux arêtes est le caractère de tour de p(n+1)²/(p n·p(n+2)). | CONFIRMÉE | AJOUT | 1 |
| `canonical_center_curvature_base` (l.349) | La base de courbure centrale du bloc canonique vaut 49/55 (≠1). | CONFIRMÉE | AJOUT | 1 |
| `edgeCurvature_eq_one_forces_critical` (l.354) | Si la courbure d'arête du bloc canonique (n=2) vaut 1, alors re ρ = 1/2. | CONFIRMÉE SOUS CONDITION (edgeCurvature ρ 2 = 1 (docstring : de force RH, jamais intermédiaire)) | V161,I13 | 1 |
| `gapSym_reversal` (l.379) | La partie paire gapSym est invariante par renversement (b,a). | CONFIRMÉE | AJOUT | 0 |
| `gapSkew_reversal` (l.382) | La partie impaire gapSkew change de signe par renversement. | CONFIRMÉE | AJOUT | 0 |
| `phi_eq_of_sigma` (l.391) | phi n = (1 − sigma n)/2. | CONFIRMÉE | AJOUT | 3 |
| `cross_eq_of_sigma` (l.394) | Pour n≥2, cross n = (1 − σ_n σ_{n+1})/2. | CONFIRMÉE (domaine: 2 ≤ n) | AJOUT | 3 |
| `gapSkew_grammar_residue_alternating` (l.400) | Sur un retour alternant (σ_{n+1}=−σ_n, σ_{n+2}=σ_n), la partie impaire des deux écarts est ≡ −σ_n mod 3. | CONFIRMÉE (domaine: 2≤n et retour alternant ) | V174 | 1 |
| `gapSkew_grammar_residue_constant` (l.420) | Sur un retour constant, la partie impaire des deux écarts est ≡ 0 mod 3. | CONFIRMÉE (domaine: 2≤n et retour constant ) | V174 | 0 |
| `alternating_return_gaps_ne` (l.439) | Un retour alternant n'a jamais deux écarts égaux (g n ≠ g(n+1)). | CONFIRMÉE (domaine: 2≤n et retour alternant ) | V174 | 0 |
| `canonical_block_gaps` (l.459) | g 2 = 2 et g 3 = 4. | CONFIRMÉE | AJOUT | 0 |
| `centeredChebyshevGrammarMark_eq_core` (l.478) | Pour n≥2, il existe des relevés kL,kR où la marque de Tchebychev centrée égale son cœur grammatical. | CONFIRMÉE (domaine: 2 ≤ n) | V48 | 1 |
| `centeredChebyshevMarkCore_on_return` (l.487) | Sur un retour (σ_{n+2}=σ_n), le cœur de marque vaut 3(1−σ_nσ_{n+1})/2. | CONFIRMÉE (domaine: 2≤n et retour ) | AJOUT | 3 |
| `centeredChebyshevMarkCore_constant_return` (l.498) | Sur un retour constant, le cœur de marque vaut 0. | CONFIRMÉE (domaine: 2≤n et retour constant ) | AJOUT | 1 |
| `centeredChebyshevMarkCore_alternating_return` (l.506) | Sur un retour alternant, le cœur de marque vaut 3. | CONFIRMÉE (domaine: 2≤n et retour alternant ) | AJOUT | 1 |
| `four_return_motifs` (l.514) | Sur un retour, soit (σ_{n+1}=σ_n, marque 0), soit (σ_{n+1}=−σ_n, marque 3). | CONFIRMÉE (domaine: 2≤n et retour ) | AJOUT | 0 |
| `centeredMark_and_pivot_separate_return_motifs` (l.530) | Deux retours de même marque centrée et même état de pivot ont les mêmes trois signes. | CONFIRMÉE (domaine: 2≤n,n' ) | V174 | 0 |
| `centralPivotCarrierFactor_ne_zero` (l.559) | Le facteur central du porteur canonique n'est jamais nul. | CONFIRMÉE | AJOUT | 1 |
| `edgeCocycle_weight_eq_rightChar_mul_translate` (l.565) | Poids de Dirichlet tordu par le cocycle d'arête = caractère du bord droit × poids translaté. | CONFIRMÉE | AJOUT | 1 |
| `incomingIncidence_eq_central_mul_translate` (l.578) | Le terme du canal d'arête n vaut facteur central × poids de Dirichlet translaté d'indice n (incidence entrante τ51). | CONFIRMÉE | AJOUT | 2 |
| `pivotChar_mul_localEdgeDefect` (l.589) | Le caractère du pivot absorbe le défaut local de l'arête sortante. | CONFIRMÉE | AJOUT | 1 |
| `outgoingIncidence_eq_central_mul_defect` (l.604) | Le terme du canal d'arête n+1 vaut facteur central × défaut local × poids de Dirichlet d'indice n+1 (incidence sortante τ15). | CONFIRMÉE | AJOUT | 3 |
| `twoIncidences_share_central_member_sensitive_factor` (l.616) | Les incidences τ51 (arête n) et τ15 (arête n+1) partagent le même facteur central sensible au membre. | CONFIRMÉE | V172 | 2 |
| `incoming_incidence_not_pivot_indexed` (l.640) | L'incidence entrante n'est pas un multiple constant du poids de Dirichlet au pivot (n+1). | CONFIRMÉE | AJOUT | 0 |
| `centralPivotWeightTransport_forces_edgeCurvature_one` (l.695) | Un transport de poids central en n force edgeCurvature = 1 pour tout zéro. | CONFIRMÉE SOUS CONDITION (CentralPivotWeightTransport n) | I13 | 1 |
| `centralPivotWeightTransport_two_is_target_strength` (l.719) | CentralPivotWeightTransport 2 entraîne re ρ = 1/2 pour tout zéro. | IMPLIQUE RH SOUS PRÉMISSE | V126,I13 | 0 |
| `centralPivotResidualZeroBlind_iff_defect_zero_blind` (l.746) | CentralPivotResidualZeroBlind équivaut à : le défaut local × poids de Dirichlet est indépendant du zéro. | ÉQUIVALENTE À RH | AJOUT | 2 |
| `beatPhase_resynchronisation` (l.774) | Translater l'échelle log d'un pas de battement laisse la phase de battement inchangée. | CONFIRMÉE (domaine: γ ≠ γ' ) | AJOUT | 0 |
| `centralPivotCarrierFactor_norm` (l.790) | La norme du facteur central vaut ‖source‖·p(n+1)^{−(re ρ −1/2)}. | CONFIRMÉE | V102 | 0 |
| `dynamic_propagation_does_not_force_zero` (l.797) | Il existe une suite d avec d(j+1)=d j et d 0 ≠ 0 (contre-modèle). | CONFIRMÉE | AJOUT | 0 |

### `Round26FIPivotReflectionCovarianceAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `primeDirichletWeight_zero_two_ne_zero` (l.24) | Le poids de Dirichlet en s=0, n=2 est non nul. | CONFIRMÉE | AJOUT | 2 |
| `localEdgeDefect_two_eq_reflect_forces_critical` (l.30) | Si le défaut local en 2 de ρ égale celui de son réfléchi, alors re ρ = 1/2. | CONFIRMÉE SOUS CONDITION (égalité des défauts locaux ρ / réfléchi en 2) | V161 | 2 |
| `centralPivotResidualZeroBlind_is_target_strength` (l.44) | CentralPivotResidualZeroBlind entraîne re ρ=1/2 pour tout zéro non trivial. | IMPLIQUE RH SOUS PRÉMISSE | V126,I13 | 0 |
| `canonical_tau51_tau15_central_pivot_specialization` (l.65) | Sur [5,7,11], arêtes τ51 (indice 2) et τ15 (indice 3), indicatrices égales à 1 et deux termes de canal partageant le facteur central sur le pivot 7. | CONFIRMÉE | AJOUT | 0 |
| `centeredChebyshevGrammarMark_eq_labelled_zero_interval` (l.107) | Pour n≥2 et re ρ≠1/2, la marque centrée égale −δL−δR−δREST + (p(n+2)−p n)/2 + log p(n+1) − 3(kL+kR). | CONFIRMÉE SOUS CONDITION (2≤n et zéro hors ligne (re≠1/2)) | AJOUT | 0 |

### `Round26FJSingleLockComposition`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `carrierOrientedResidue_reflect` (l.27) | La réflexion préserve la donnée singulière orientée du porteur (même hors ligne). | CONFIRMÉE | V63 | 2 |
| `carrierBaseLaurentDatum_reflect_eq_common_residue` (l.35) | Le datum de Laurent réfléchi = constante d'accumulation réfléchie × résidu orienté commun. | CONFIRMÉE | AJOUT | 1 |
| `carrierBaseLaurentDatum_reflection_ratio_eq_accumulation_ratio` (l.44) | Le rapport des data de Laurent réfléchi/original égale le rapport des constantes d'accumulation. | CONFIRMÉE | AJOUT | 1 |
| `accumulationConstant_reflection_ratio_exact` (l.57) | Le rapport des constantes d'accumulation = (source réfléchie/source) × \|caractère de tour\|². | CONFIRMÉE | V102 | 2 |
| `carrierBaseLaurentDatum_reflection_ratio_exact` (l.79) | Le rapport des data de Laurent réfléchi/original = (source réfléchie/source) × \|caractère de tour\|². | CONFIRMÉE | V102 | 0 |
| `canonicalCarrier_toBlockHolonomy_comp` (l.93) | L'holonomie de bloc du porteur se compose : hol(M,N) = hol(M,K)·hol(K,N). | CONFIRMÉE (domaine: M ≤ K ≤ N ) | AJOUT | 1 |
| `canonicalCarrier_toBlockHolonomy_reflect` (l.107) | La réflexion envoie l'holonomie de bloc sur l'inverse de son conjugué. | CONFIRMÉE (domaine: M ≤ N ) | V63,V80 | 1 |
| `canonical_tau51_tau15_reflected_blockHolonomy_relation` (l.120) | Sur la cellule canonique, l'holonomie réfléchie 2→4 est le produit des inverses conjugués des holonomies 2→3 et 3→4. | CONFIRMÉE | AJOUT | 1 |
| `orientedTau_reflection_orientation_commutator` (l.138) | Pour toute continuation Corr, le commutateur de réflexion τ15/τ51 vaut ½(commutateur croisé + terme de cobord). | CONFIRMÉE | AJOUT | 1 |

### `Round26FKCanonicalCorrelationReflection`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `coboundaryPartial_conj` (l.31) | Toute somme partielle de cobord commute avec la conjugaison complexe. | CONFIRMÉE | V101 | 1 |
| `coboundaryChannelLimit_conj` (l.42) | La limite du canal de cobord commute avec la conjugaison sur Re s>0. | CONFIRMÉE (domaine: 0<re s ) | AJOUT | 1 |
| `coboundaryChannelLimit_reflect_exact` (l.61) | Pour re s<1, la limite en 1−conj s est le conjugué de la limite en 1−s. | CONFIRMÉE (domaine: re s<1 ) | AJOUT | 1 |
| `coboundary_reflection_pair_exact` (l.70) | Sur la bande critique, le terme de cobord du commutateur est le conjugué de la somme en s et 1−s. | CONFIRMÉE (domaine: 0<re s<1 ) | AJOUT | 1 |
| `orientedTau_correlation_reflection_residual` (l.81) | Sur la bande 0<re s<1, après retrait des termes de queue globale et de cobord, le commutateur de réflexion τ15/τ51 vaut −¼(Corr(1−conj s) − conj Corr(s)). | CONFIRMÉE (domaine: 0<re s<1 ) | AJOUT | 1 |
| `orientedTau_trueZero_correlation_reflection_residual` (l.105) | Même identité spécialisée en un zéro non trivial ρ et son réfléchi-conjugué. | CONFIRMÉE | AJOUT | 0 |

### `Round26FLGenericPrimeCell`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `one_lt_primeCellRatio` (l.31) | Le rapport de cellule première primeCellRatio n est > 1. [terme hors maître] | CONFIRMÉE | AJOUT | 2 |
| `primeCellRatio_pos` (l.36) | primeCellRatio n > 0. | CONFIRMÉE | AJOUT | 3 |
| `primeCellRatio_rpow_inj` (l.39) | x ↦ primeCellRatio n ^ x est injective. | CONFIRMÉE (domaine: primeCellRatio n ^ x = primeCellRatio n ^ y ) | AJOUT | 1 |
| `primeCellRatio_rpow_neg_mul_self` (l.45) | primeCellRatio n^(−d) · primeCellRatio n^d = 1. | CONFIRMÉE | AJOUT | 1 |
| `primeCellHeightPhase_ne_zero` (l.53) | La phase de hauteur de la cellule première n'est jamais nulle. | CONFIRMÉE | AJOUT | 1 |
| `primeCell_towerCharacter_self` (l.68) | Le caractère de tour du rapport de cellule vaut module r^{−(re ρ −1/2)} × phase de hauteur. | CONFIRMÉE | V102,V158 | 1 |
| `primeCell_towerCharacter_reflected` (l.74) | Le caractère de tour en 1−conj ρ vaut r^{(re ρ −1/2)} × la même phase de hauteur. | CONFIRMÉE | V102,V35 | 1 |
| `primeCellReflectedCrossOperator_eq_radial_matrix` (l.85) | L'opérateur croisé réfléchi de cellule est la matrice [[0,r^{−(β−1/2)}],[r^{β−1/2},0]]. | CONFIRMÉE | V102 | 2 |
| `primeCellReflectedCrossOperator_apply_zero_one` (l.98) | Entrée (0,1) de l'opérateur croisé = r^{−(re ρ −1/2)}. | CONFIRMÉE | V102 | 2 |
| `primeCellReflectedCrossOperator_apply_one_zero` (l.104) | Entrée (1,0) de l'opérateur croisé = r^{re ρ −1/2}. | CONFIRMÉE | V102 | 2 |
| `primeCellReflectedCrossOperator_offdiag_product_eq_one` (l.110) | Le produit des entrées hors diagonale de l'opérateur croisé vaut 1 pour tout point. | CONFIRMÉE | AJOUT | 0 |
| `primeCellReflectedCrossOperator_offdiag_eq_iff_critical` (l.119) | Les deux entrées hors diagonale sont égales ssi re ρ = 1/2. | CONFIRMÉE | V161,V162 | 1 |
| `alternatingPrimeCell_transitionPair` (l.137) | Si σ_n=−1, σ_{n+1}=1, σ_{n+2}=−1 alors les indicatrices τ51 en n et τ15 en n+1 valent 1. | CONFIRMÉE (domaine: 2≤n et motif de signes [−1,+1,−1] ) | AJOUT | 0 |
| `primeCellRatio_two` (l.144) | primeCellRatio 2 = crossBlockRatio (bloc [5,7,11]). | CONFIRMÉE | AJOUT | 2 |
| `primeCellHeightPhase_two` (l.148) | primeCellHeightPhase 2 γ = crossHeightPhase γ. | CONFIRMÉE | AJOUT | 1 |
| `primeCellReflectedCrossTransport_two` (l.152) | Le transport croisé de cellule en n=2 égale le transport croisé de vrai zéro. | CONFIRMÉE | AJOUT | 1 |
| `primeCellReflectedCrossOperator_two` (l.156) | L'opérateur de cellule en n=2 égale l'opérateur croisé réfléchi de vrai zéro. | CONFIRMÉE | AJOUT | 0 |

### `Round26FMXiLocalReflectionAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `deriv_riemannXi_one_sub` (l.25) | deriv ξ(1−s) = −deriv ξ(s) (équation fonctionnelle dérivée de ξ). | CONFIRMÉE | V35,V62 | 2 |
| `logDeriv_riemannXi_one_sub` (l.38) | logDeriv ξ(1−s) = −logDeriv ξ(s). | CONFIRMÉE | V35,V62 | 1 |
| `riemannXi_trueZero_reflected_pair` (l.46) | Un zéro non trivial et son réfléchi-conjugué annulent tous deux ξ. | CONFIRMÉE | V62,V63 | 1 |
| `riemannXi_trueZero_local_inventory` (l.54) | En un zéro : ξ s'annule en ρ et en son réfléchi, deriv ξ(1−ρ) = −deriv ξ(ρ), logDeriv de même. | CONFIRMÉE | V62,V63 | 0 |

### `Round26FNPrimeChannelRegularPart`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `existsUnique_zetaLogDerivRegularDatum` (l.33) | En un zéro de ζ, retirer la partie principale de −ζ'/ζ laisse une limite unique. | CONFIRMÉE (domaine: ζ(ρ)=0 ) | V172 | 1 |
| `zetaLogDerivRegularDatum_spec` (l.65) | La donnée régulière canonique de −ζ'/ζ en ρ est sa limite caractéristique. | CONFIRMÉE | V172 | 4 |
| `tendsto_primeGrammarChannel_regularized` (l.72) | Pour re ρ>1/2, le canal premier régularisé tend vers datum régulier de ζ − ρ × correction de puissance première. [terme hors maître] | CONFIRMÉE SOUS CONDITION (domaine: 1/2<re ρ ; hors ligne côté haut) | AJOUT | 2 |
| `existsUnique_primeGrammarChannelRegularDatum` (l.103) | Pour re ρ>1/2, la limite régulière du canal premier en ρ est unique. | CONFIRMÉE (domaine: 1/2<re ρ ) | AJOUT | 0 |

### `Round26FORegularPartReflection`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `conjugateTrueZero_coe` (l.31) | La valeur complexe de conjugateTrueZero ρ est conj ρ. | CONFIRMÉE | V63 | 0 |
| `logDeriv_riemannZeta_conj` (l.35) | Réflexion de Schwarz de logDeriv ζ hors du pôle. | CONFIRMÉE (domaine: s ≠ 1 ) | AJOUT | 1 |
| `tendsto_conj_punctured` (l.49) | La conjugaison envoie le voisinage pointé de conj ρ sur celui de ρ. | CONFIRMÉE | AJOUT | 1 |
| `zetaLogDerivRegularDatum_conj` (l.63) | La donnée régulière du conjugué est le conjugué de la donnée régulière. | CONFIRMÉE | V63 | 1 |
| `logDeriv_completedRiemannZeta_one_sub` (l.108) | logDeriv ζ complétée (1−s) = −logDeriv ζ complétée (s). | CONFIRMÉE (domaine: s≠0, s≠1 ) | V35 | 1 |
| `logDeriv_riemannZeta_eq_completed_add_archimedean` (l.131) | Pour re s>0, s≠1, ζ(s)≠0 : logDeriv ζ = logDeriv ζ complétée + correction archimédienne. | CONFIRMÉE (domaine: 0<re s, s≠1, ζ(s)≠0 ) | AJOUT | 1 |
| `negLogDeriv_riemannZeta_one_sub` (l.161) | Réflexion fonctionnelle ponctuelle de −ζ'/ζ hors des zéros appariés. | CONFIRMÉE (domaine: 0<re s<1, ζ(s)≠0, ζ(1−s)≠0 ) | V35 | 2 |
| `functionalReflectTrueZero_coe` (l.197) | La valeur de functionalReflectTrueZero ρ est 1−ρ. | CONFIRMÉE | V63 | 0 |
| `tendsto_one_sub_punctured` (l.202) | 1−s envoie le voisinage pointé de 1−ρ sur celui de ρ. | CONFIRMÉE | AJOUT | 2 |
| `eventually_riemannZeta_ne_zero_punctured` (l.220) | ζ ne s'annule pas sur un petit voisinage pointé d'un de ses zéros. | CONFIRMÉE (domaine: ζ(ρ)=0 ) | AJOUT | 2 |
| `analyticAt_zetaArchimedeanLogDeriv` (l.232) | La correction archimédienne logarithmique est analytique sur re s>0. | CONFIRMÉE (domaine: 0<re s ) | AJOUT | 2 |
| `zetaLogDerivRegularDatum_one_sub` (l.241) | La donnée régulière en 1−ρ = −(donnée en ρ) − corrections archimédiennes en ρ et 1−ρ. | CONFIRMÉE | V35,V63 | 2 |
| `zetaLogDerivRegularDatum_reflectConj` (l.339) | La donnée régulière en 1−conj ρ s'exprime explicitement par −conj(donnée) − corrections archimédiennes. | CONFIRMÉE | V63,V80 | 1 |

### `Round26FPRegularPartFirstJet`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `zetaLogDerivRegularized_apply_zero` (l.32) | Le prolongement régularisé prend la valeur de la donnée régulière en ρ. | CONFIRMÉE | AJOUT | 3 |
| `analyticAt_zetaLogDerivRegularized` (l.37) | Le prolongement régularisé est analytique en ρ. | CONFIRMÉE | AJOUT | 2 |
| `hasDerivAt_zetaLogDerivRegularized` (l.78) | Le prolongement régularisé a pour dérivée le premier jet régulier en ρ. | CONFIRMÉE | AJOUT | 2 |
| `zetaLogDerivRegularized_one_sub_eventuallyEq` (l.89) | La réflexion fonctionnelle vaut comme égalité de germes analytiques remplis. | CONFIRMÉE | V35 | 1 |
| `zetaLogDerivFirstRegularJet_one_sub` (l.168) | Le premier jet régulier vérifie l'équation fonctionnelle dérivée. | CONFIRMÉE | V35 | 0 |

### `Round26FQSingleLockProducerAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `primeGrammarChannelRegularized_apply_zero` (l.49) | Le canal premier régularisé en ρ vaut sa donnée régulière. | CONFIRMÉE | AJOUT | 0 |
| `analyticAt_primeGrammarChannelRegularized` (l.54) | Pour re ρ>1/2, le canal premier régularisé est analytique en ρ. | CONFIRMÉE (domaine: 1/2<re ρ ) | AJOUT | 1 |
| `_private.RhGapCriterion.Round26FQSingleLockProducerAudit.0.RhGap.tendsto_carrier_regular_shift_punctured` (l.72) | s ↦ s+(ρ−1/2) envoie le voisinage pointé de 1/2 sur celui de ρ. | CONFIRMÉE | AJOUT | 1 |
| `tendsto_carrierAccumulatedPrimeContinuation_regularized_half` (l.87) | Pour re ρ>1/2, le canal accumulé, après retrait de la partie principale décalée, a une limite finie canonique en 1/2. | CONFIRMÉE (domaine: 1/2<re ρ ) | AJOUT | 1 |
| `existsUnique_carrierPrimeRegularDatum` (l.110) | Pour re ρ>1/2, cette limite en 1/2 est unique. | CONFIRMÉE (domaine: 1/2<re ρ ) | AJOUT | 0 |
| `carrierPrimeRegularDatum_base_change` (l.126) | Le datum régulier est simplement remis à l'échelle à chaque base. | CONFIRMÉE | AJOUT | 0 |
| `carrierPrimeRegularDatum_ratio_eq_blockHolonomy` (l.136) | Si le datum commun est non nul, le rapport des data aux bases M,N égale l'holonomie de bloc. | CONFIRMÉE (domaine: M≤N et datum régulier non nul (non connu d'après la docstring) ) | AJOUT | 0 |
| `primeGrammarChannelRegularDatum_reflect_exact` (l.149) | La valeur régulière réfléchie est une correction affine explicite de −conj(datum ζ). | CONFIRMÉE | V63 | 0 |
| `hasDerivAt_primeGrammarChannelRegularized` (l.173) | Pour re ρ>1/2, le canal premier régularisé a pour dérivée le premier jet régulier. | CONFIRMÉE (domaine: 1/2<re ρ ) | AJOUT | 2 |
| `primeGrammarChannelFirstRegularJet_eq` (l.180) | Pour re ρ>1/2, le jet du canal premier = jet ζ − jet de correction de puissance première. | CONFIRMÉE (domaine: 1/2<re ρ ) | AJOUT | 0 |
| `hasDerivAt_carrierAccumulatedPrimeRegularized_half` (l.205) | Pour re ρ>1/2, la dérivée en 1/2 du canal accumulé régularisé est le datum de jet de base. | CONFIRMÉE (domaine: 1/2<re ρ ) | AJOUT | 1 |
| `deriv_carrierAccumulatedPrimeRegularized_half` (l.228) | Pour re ρ>1/2, deriv du canal accumulé régularisé en 1/2 = carrierPrimeFirstJetDatum. | CONFIRMÉE (domaine: 1/2<re ρ ) | AJOUT | 0 |
| `carrierPrimeFirstJetDatum_base_change` (l.235) | Le datum de jet a la même dépendance de base aveugle à l'orientation que le datum régulier. | CONFIRMÉE | AJOUT | 0 |
| `carrierPrimeFirstJetDatum_ratio_eq_blockHolonomy` (l.245) | Si le jet est non nul, le rapport des data de jet aux bases M,N égale l'holonomie de bloc. | CONFIRMÉE (domaine: M≤N et jet non nul ) | AJOUT | 0 |
| `orientedTau15Cont_sub_tau51Cont` (l.259) | La différence des continuations orientées τ15−τ51 est la limite du canal de cobord, indépendante de Corr. | CONFIRMÉE | AJOUT | 0 |
| `orientedTau15Cont_add_tau51Cont` (l.267) | La somme des continuations orientées τ15+τ51 est la continuation du canal croisé (garde Corr libre). | CONFIRMÉE | AJOUT | 0 |
| `genericPrimeCell_oriented_equality_iff_critical` (l.282) | Sur toute cellule première n, l'égalité des deux orientations de l'opérateur croisé ⟺ re ρ = 1/2. | CONFIRMÉE | V161,V162 | 0 |
| `adjacentChi3Coefficient_sum_eq` (l.295) | La somme des coefficients χ3 adjacents sur range N égale adjacentChi3CoeffSum N. | CONFIRMÉE | AJOUT | 1 |
| `adjacentChi3Coefficient_coeffPartialSumBound_one` (l.298) | L'estimation triviale instancie le critère générique seulement à l'exposant 1. | CONFIRMÉE | AJOUT | 0 |

### `Round26FRFiberedCanonicalPartnership`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `FiberedCanonicalZeroPrimePartnership.zero_height_lt` (l.53) | Le membre d'un partenariat fibré a hauteur \|Im\| < T. | CONFIRMÉE | V158 | 2 |
| `FiberedCanonicalZeroPrimePartnership.capture_eq_canonical` (l.65) | La capture du partenariat est la capture canonique à la même hauteur. [terme hors maître] | CONFIRMÉE | V48 | 9 |
| `FiberedCanonicalZeroPrimePartnership.directCarrier_eq_canonical` (l.67) | Le porteur direct est le porteur canonique du membre. | CONFIRMÉE | AJOUT | 5 |
| `FiberedCanonicalZeroPrimePartnership.reflectedCarrier_eq_canonical` (l.69) | Le porteur réfléchi est le porteur canonique du partenaire miroir (reflectConjZero). | CONFIRMÉE | V63,V67 | 4 |
| `FiberedCanonicalZeroPrimePartnership.directFiber_eq_canonical` (l.71) | La fibre directe est la fibre de hauteur du membre à sa position re. | CONFIRMÉE | V50 | 2 |
| `FiberedCanonicalZeroPrimePartnership.reflectedFiber_eq_canonical` (l.74) | La fibre réfléchie est la même fibre de hauteur à la position 1−re. | CONFIRMÉE | V50,V65 | 2 |
| `FiberedCanonicalZeroPrimePartnership.capture_source_eq_canonical` (l.95) | La source de la capture est la source canonique des zéros. | CONFIRMÉE | AJOUT | 3 |
| `FiberedCanonicalZeroPrimePartnership.capture_primeSide_eq_M` (l.102) | Le côté premier de la capture encode exactement la grammaire première M. | CONFIRMÉE | V48,V174 | 1 |
| `FiberedCanonicalZeroPrimePartnership.capture_primeSide_eq_MZ` (l.109) | Le même côté premier est compatible avec la reconstruction M^Z (bloc reconstruit depuis les zéros). | CONFIRMÉE | V48,V174 | 1 |
| `FiberedCanonicalZeroPrimePartnership.capture_zeroSide_eq_canonical` (l.119) | Le côté zéro de la capture est la grammaire de constellation de la source canonique. | CONFIRMÉE | AJOUT | 0 |
| `FiberedCanonicalZeroPrimePartnership.directCarrier_basePoint` (l.126) | Le point de base du porteur direct est le membre du partenariat. | CONFIRMÉE | AJOUT | 3 |
| `FiberedCanonicalZeroPrimePartnership.reflectedCarrier_basePoint` (l.133) | Le point de base du porteur réfléchi est reflectConjZero du membre. | CONFIRMÉE | V63 | 3 |
| `FiberedCanonicalZeroPrimePartnership.same_height` (l.140) | Les points de base des deux porteurs ont la même partie imaginaire. | CONFIRMÉE | V65 | 1 |
| `FiberedCanonicalZeroPrimePartnership.reflected_height_lt` (l.148) | Le partenaire réfléchi a hauteur \|Im\| < T. | CONFIRMÉE | V65 | 1 |
| `FiberedCanonicalZeroPrimePartnership.zero_mem_captured_height_slice` (l.155) | Le membre appartient à la tranche de hauteur de la source capturée. | CONFIRMÉE | AJOUT | 2 |
| `FiberedCanonicalZeroPrimePartnership.reflected_mem_captured_height_slice` (l.162) | Le miroir appartient à la même tranche de la même source. | CONFIRMÉE | V65 | 2 |
| `FiberedCanonicalZeroPrimePartnership.carrier_pair_localizes_captured_true_pair` (l.170) | Les deux porteurs sont les deux localisations du vrai couple contenu dans la même tranche de la même capture. | CONFIRMÉE | V62,V65 | 0 |
| `FiberedCanonicalZeroPrimePartnership.directFiber_eq_carrierFiber` (l.182) | La fibre directe est celle du point de base du porteur direct. | CONFIRMÉE | AJOUT | 0 |
| `FiberedCanonicalZeroPrimePartnership.reflectedFiber_eq_carrierFiber` (l.190) | La fibre réfléchie est celle du point de base du porteur réfléchi, dans la même fibre de hauteur. | CONFIRMÉE | AJOUT | 0 |
| `FiberedCanonicalZeroPrimePartnership.directCarrier_grammarState` (l.200) | L'état de grammaire du porteur direct est l'état canonique grammarPrimeStateChi3. | CONFIRMÉE | AJOUT | 0 |
| `FiberedCanonicalZeroPrimePartnership.reflectedCarrier_grammarState` (l.207) | Le porteur réfléchi utilise la même grammaire première canonique que le direct. | CONFIRMÉE | V60,V174 | 1 |
| `FiberedCanonicalZeroPrimePartnership.capture_transition` (l.216) | Les transitions du côté premier de la capture sont celles du bloc de grammaire premier. | CONFIRMÉE | V174 | 0 |
| `FiberedCanonicalZeroPrimePartnership.capture_pattern` (l.223) | Le motif du côté premier de la capture est celui du bloc premier. | CONFIRMÉE | V174 | 0 |
| `FiberedCanonicalZeroPrimePartnership.capture_family` (l.229) | Les familles du côté premier de la capture sont celles du bloc premier. | CONFIRMÉE | V174 | 0 |
| `FiberedCanonicalZeroPrimePartnership.capture_entry` (l.235) | L'entrée du côté premier de la capture est celle du bloc premier. | CONFIRMÉE | AJOUT | 0 |
| `FiberedCanonicalZeroPrimePartnership.capture_exit` (l.241) | L'état de sortie du côté premier est celui du bloc premier. | CONFIRMÉE | AJOUT | 0 |
| `FiberedCanonicalZeroPrimePartnership.direct_holonomy_eq_crossTransport` (l.247) | L'holonomie du porteur direct 2→4 est l'entrée (0,1) du transport croisé du membre. | CONFIRMÉE | AJOUT | 3 |
| `FiberedCanonicalZeroPrimePartnership.reflected_holonomy_eq_crossTransport` (l.255) | L'holonomie du porteur miroir 2→4 est l'entrée (1,0) du transport croisé. | CONFIRMÉE | AJOUT | 3 |
| `FiberedCanonicalZeroPrimePartnership.crossTransport_eq_carrier_holonomies` (l.263) | Le transport croisé réfléchi est reconstruit depuis les deux porteurs du même partenariat (soudure de provenance). | CONFIRMÉE | AJOUT | 1 |
| `fiberedCanonicalZeroPrimePartnership_exists` (l.274) | Pour tout zéro non trivial de \|Im\|<T, un partenariat fibré canonique de membre ρ existe. | CONFIRMÉE (domaine: \|Im ρ\|<T) | V15 | 0 |
| `zero_height_lt_canonicalFiberedPartnershipCutoff` (l.290) | Tout zéro non trivial a \|Im ρ\| < canonicalFiberedPartnershipCutoff ρ. | CONFIRMÉE | AJOUT | 0 |
| `FiberedCanonicalPartnershipCertificate.truePairInCapturedSlice` (l.307) | Sous certificat, le membre et son miroir sont dans la tranche capturée. | CONFIRMÉE SOUS CONDITION (FiberedCanonicalPartnershipCertificate P (vrai sans condition par ...Partnership.certificate)) | V65 | 0 |
| `FiberedCanonicalPartnershipCertificate.captureSourceCanonical` (l.311) | Sous certificat, la source de la capture est canonique. | CONFIRMÉE (domaine: certificat (inconditionnel via certificate) ) | AJOUT | 0 |
| `FiberedCanonicalPartnershipCertificate.capturePrimeSideEqM` (l.312) | Sous certificat, le côté premier égale le bloc premier M. | CONFIRMÉE (domaine: certificat ) | V174 | 0 |
| `FiberedCanonicalPartnershipCertificate.capturePrimeSideEqMZ` (l.314) | Sous certificat, le côté premier égale le bloc reconstruit M^Z. | CONFIRMÉE (domaine: certificat ) | V174 | 0 |
| `FiberedCanonicalPartnershipCertificate.directCarrierCanonical` (l.317) | Sous certificat, le porteur direct est le porteur canonique du membre. | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `FiberedCanonicalPartnershipCertificate.reflectedCarrierCanonical` (l.318) | Sous certificat, le porteur réfléchi est le porteur canonique du miroir. | CONFIRMÉE (domaine: certificat ) | V63 | 0 |
| `FiberedCanonicalPartnershipCertificate.sameHeight` (l.319) | Sous certificat, les deux points de base ont même hauteur. | CONFIRMÉE (domaine: certificat ) | V65 | 0 |
| `FiberedCanonicalPartnershipCertificate.directFiberCanonical` (l.322) | Sous certificat, la fibre directe est canonique. | CONFIRMÉE (domaine: certificat ) | V50 | 0 |
| `FiberedCanonicalPartnershipCertificate.reflectedFiberCanonical` (l.324) | Sous certificat, la fibre réfléchie est canonique (position 1−re). | CONFIRMÉE (domaine: certificat ) | V50,V65 | 0 |
| `FiberedCanonicalPartnershipCertificate.sameGrammar` (l.326) | Sous certificat, les deux porteurs ont le même état de grammaire. | CONFIRMÉE (domaine: certificat ) | V60 | 0 |
| `FiberedCanonicalPartnershipCertificate.directHolonomy` (l.328) | Sous certificat, l'holonomie directe 2→4 est l'entrée (0,1) du transport croisé. | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `FiberedCanonicalPartnershipCertificate.reflectedHolonomy` (l.330) | Sous certificat, l'holonomie miroir 2→4 est l'entrée (1,0). | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `FiberedCanonicalPartnershipCertificate.crossTransportReconstructed` (l.332) | Sous certificat, le transport croisé est reconstruit depuis les deux holonomies. | CONFIRMÉE (domaine: certificat ) | AJOUT | 0 |
| `FiberedCanonicalZeroPrimePartnership.certificate` (l.337) | Tout partenariat fibré canonique porte un certificat. | CONFIRMÉE | AJOUT | 1 |
| `canonicalFiberedPartnershipProvenance_holds` (l.360) | CanonicalFiberedPartnershipProvenance vaut sans condition. | CONFIRMÉE | AJOUT | 3 |

### `Round26FSFiberedPartnershipTDDRepair`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `GrammarTowerZeroFidelityObjectMinusFidelity.fiberedPartnershipProvenance` (l.27) | L'objet TDD amputé de la fidélité expose la provenance du partenariat fibré. | CONFIRMÉE SOUS CONDITION (objet TDD amputé) | AJOUT | 0 |
| `GrammarTowerZeroFidelityObject.fiberedPartnershipProvenance` (l.34) | L'objet TDD complet expose la même provenance. | CONFIRMÉE SOUS CONDITION (objet TDD complet) | AJOUT | 0 |
| `canonicalFiberedPartnershipProvenance_no_terminal_strength` (l.40) | Sous la provenance fibrée, RiemannHypothesis ↔ RiemannHypothesis (tautologie). | CONFIRMÉE | AJOUT | 0 |
| `crossTransport_offdiag_eq_iff_operator_offdiag_eq` (l.56) | L'égalité des entrées hors diagonale du transport croisé équivaut à celle de l'opérateur (phase commune retirée). | CONFIRMÉE | AJOUT | 1 |
| `fiberedPartnershipOrientedCoherence_iff_orientedFidelity` (l.67) | La cohérence orientée d'un partenariat équivaut à l'égalité des deux entrées hors diagonale de l'opérateur croisé de son zéro. | CONFIRMÉE | V162 | 1 |
| `fiberedPartnershipOrientedCoherence_iff_critical` (l.78) | La cohérence orientée d'un partenariat équivaut à re(zéro) = 1/2. | CONFIRMÉE | V161,V162 | 1 |
| `canonicalFiberedPartnershipOrientedCoherence_iff_rh` (l.90) | CanonicalFiberedPartnershipOrientedCoherence équivaut à RiemannHypothesis. | ÉQUIVALENTE À RH | V126,O10 | 0 |
| `repaired_minusFidelity_is_inhabited` (l.105) | L'objet TDD amputé (32 surfaces) est habité sans condition. | CONFIRMÉE | AJOUT | 0 |

### `Round26M56ZeroMetaPatternScaleRigidity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `phiOfFrom_p_eq` (l.110) | phiOfFrom appliqué à p égale phiOf. | CONFIRMÉE | AJOUT | 1 |
| `innovationJFrom_p_gnat_eq` (l.118) | innovationJFrom au couple canonique (p,gnat) égale innovationJ. | CONFIRMÉE | AJOUT | 3 |
| `zero_reconstructed_innovationJ_eq` (l.125) | L'innovation construite depuis le couple reconstruit des zéros égale innovationJ à tout indice. | CONFIRMÉE | V48,V174 | 2 |
| `zero_reconstructed_normalized_innovation_window_energy_eq` (l.141) | L'énergie de fenêtre d'innovation reconstruite égale l'énergie canonique. | CONFIRMÉE | V48,V174 | 2 |
| `innovation_window_spectral_scale_intertwining` (l.159) | La fenêtre de Gram appliquée à un mode de zéro obéit à l'entrelacement d'échelle e^{(ρ−1/2)a}. | CONFIRMÉE | V102 | 1 |
| `zero_reconstructed_innovation_window_scale_square` (l.179) | Carré commutatif : énergie reconstruite = canonique ET entrelacement d'échelle du mode, simultanément. | CONFIRMÉE | V48,V102 | 0 |
| `innovation_window_rh_from_hypothetical_decomposition` (l.199) | Pour un ensemble Z stable par ρ↦1−ρ, à amplitudes non nulles, avec WT=mode+reste, WT et reste sous-exponentiels sur Z, tout ρ∈Z a re=1/2. | CONFIRMÉE SOUS CONDITION (RH: conclusion re=1/2 sur un ensemble Z arbitraire (RH si Z = zéros non triviaux) ; 6 hypothèses de décomposition et de sous-exponentialité non déchargées) | V126,O5 | 0 |

### `Round26M57GrammarPairMaxWeightCollapse`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `scaleBlockPairEnergy_eq_sum_grammar_pair_classes` (l.80) | L'énergie de paires du bloc d'échelle se partitionne exactement en somme sur les seize classes de paires de transformations. [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `zeroReconstructedScaleBlockPairEnergy_eq_canonical` (l.101) | L'énergie de paires de bloc reconstruite depuis les zéros égale l'énergie canonique. | CONFIRMÉE | V48,V174 | 3 |
| `zero_reconstructed_scale_block_pair_energy_grammar_class_eq` (l.107) | Pour chaque classe de paire k, l'énergie de classe reconstruite depuis les zéros égale l'énergie de classe canonique. | CONFIRMÉE | V48,V174 | 1 |
| `zero_reconstructed_scale_block_pair_energy_grammar_partition_eq` (l.133) | La partition en seize classes de l'énergie reconstruite égale l'énergie reconstruite de bloc. | CONFIRMÉE | V48,V174 | 0 |
| `blockKernelWeight_nonneg` (l.153) | Le poids de noyau de bloc est positif ou nul. | CONFIRMÉE | AJOUT | 3 |
| `blockKernelWeight_antitone` (l.156) | Le poids de noyau de bloc est décroissant en l'indice. | CONFIRMÉE (domaine: i ≤ j ) | AJOUT | 3 |
| `energyTerm_eq_max_index_weight` (l.164) | Le terme d'énergie de paire vaut a_m a_n × poids au max(m,n). | CONFIRMÉE | AJOUT | 2 |
| `blockInnovationPrefix_self` (l.185) | Le préfixe d'innovation de bloc vide (my,my) est nul. | CONFIRMÉE | AJOUT | 5 |
| `blockInnovationPrefix_succ` (l.189) | Le préfixe d'innovation s'étend par innovationJ k. | CONFIRMÉE (domaine: my ≤ k ) | AJOUT | 1 |
| `sum_pair_max_weight_eq_prefix_square_telescope` (l.194) | Pour a, w quelconques, la double somme a_m a_n w(max m n) égale la somme télescopique des carrés de préfixes pondérés. | CONFIRMÉE (domaine: my ≤ mx ) | AJOUT | 1 |
| `scaleBlockPairEnergy_eq_prefix_square_telescope` (l.240) | L'énergie de paires de bloc s'écrit comme somme télescopique de carrés de préfixes d'innovation. | CONFIRMÉE (domaine: my ≤ mx ) | AJOUT | 4 |
| `antitone_weight_telescope_upper` (l.255) | Borne d'Abel supérieure : poids décroissant contre quantité télescopée bornée nulle à gauche donne somme ≤ w(my)·B. | CONFIRMÉE (domaine: poids antitone, Q(my)=0, my≤mx, Q≤B ) | AJOUT | 1 |
| `antitone_weight_telescope_lower` (l.285) | Borne d'Abel inférieure : la somme télescopée est ≥ w(mx)·Q(mx). | CONFIRMÉE (domaine: poids antitone, Q(my)=0, Q≥0, my≤mx ) | AJOUT | 1 |
| `scaleBlockPairEnergy_le_head_weight_mul_prefix_square_bound` (l.303) | Si les carrés de préfixes sont ≤ B, l'énergie de bloc est ≤ poids de tête × B. | CONFIRMÉE (domaine: my≤mx et borne uniforme B ) | AJOUT | 2 |
| `tail_weight_mul_block_square_le_scaleBlockPairEnergy` (l.325) | L'énergie de bloc est ≥ poids de queue × carré de la somme d'innovation totale. | CONFIRMÉE (domaine: my ≤ mx ) | AJOUT | 1 |
| `scaleBlockPairEnergy_nonneg` (l.337) | L'énergie de paires de bloc est ≥ 0. | CONFIRMÉE (domaine: my ≤ mx ) | AJOUT | 1 |
| `blockInnovationPrefix_eq_aT_prefix_sub_coboundary` (l.344) | Le préfixe d'innovation = somme de aT moins cobord phiOf k − phiOf my. | CONFIRMÉE (domaine: my ≤ k ) | AJOUT | 1 |
| `scaleBlockPairEnergy_le_head_weight_mul_aT_prefix_bound` (l.359) | Si les sommes de préfixes de aT sont bornées par D, l'énergie de bloc est ≤ poids de tête × (D+1)². | CONFIRMÉE (domaine: my≤mx, D≥0, borne sur préfixes aT ) | AJOUT | 0 |
| `zero_reconstructed_scale_block_pair_energy_prefix_square_telescope` (l.384) | Le même télescopage vaut pour l'énergie reconstruite depuis les zéros avec l'innovation reconstruite. | CONFIRMÉE (domaine: my ≤ mx ) | V48,V174 | 0 |
| `zeroReconstructedScaleBlockPairEnergy_le_head_weight_mul_prefix_square_bound` (l.402) | Borne supérieure par poids de tête × B pour l'énergie reconstruite. | CONFIRMÉE (domaine: my≤mx et borne B sur carrés de préfixes ) | V48,V174 | 0 |

### `Round26M57PositiveAbelExpansion`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `abelCoefficient_nonneg_of_antitone` (l.68) | Les coefficients d'Abel sont ≥ 0 si le poids est ≥0 et décroissant. | CONFIRMÉE (domaine: w ≥ 0 et antitone ) | AJOUT | 0 |
| `abel_positive_expansion` (l.78) | Expansion d'Abel positive : Σ w_k (Q_{k+1}−Q_k) = w_r Q_{r+1} + Σ (w_k − w_{k+1}) Q_{k+1}. | CONFIRMÉE (domaine: Q(my)=0, my ≤ r ) | AJOUT | 2 |
| `abel_positive_expansion_coefficient_form` (l.97) | Même expansion en somme unique à coefficients d'Abel. | CONFIRMÉE (domaine: Q(my)=0, my ≤ r ) | AJOUT | 0 |
| `scaleBlockPairEnergy_empty` (l.119) | Le bloc vide a une énergie nulle. | CONFIRMÉE (domaine: mx ≤ my ) | AJOUT | 0 |
| `scaleBlockPairEnergy_eq_positive_prefix_square_sum` (l.126) | Expansion positive de l'énergie de bloc : terme terminal + Σ (poids_k − poids_{k+1}) P_{k+1}². | CONFIRMÉE (domaine: my ≤ r ) | AJOUT | 2 |
| `scaleBlockPairEnergy_singleton` (l.140) | Pour un bloc singleton, l'énergie = poids de tête × carré du préfixe. | CONFIRMÉE | AJOUT | 0 |
| `blockKernelWeight_sub_next_eq_zero_of_le` (l.150) | Si X ≤ p(k+1), la différence de poids consécutifs est nulle. | CONFIRMÉE (domaine: X ≤ p(k+1) ) | AJOUT | 0 |
| `blockKernelWeight_sub_next_eq_partial_of_between` (l.159) | Si p(k+1) ≤ X ≤ p(k+2), la différence vaut X − p(k+1). | CONFIRMÉE (domaine: p(k+1) ≤ X ≤ p(k+2) ) | AJOUT | 0 |
| `blockKernelWeight_sub_next_eq_prime_gap_of_active` (l.167) | Si p(k+2) ≤ X, la différence vaut exactement l'écart premier p(k+2) − p(k+1). | CONFIRMÉE (domaine: p(k+2) ≤ X ) | V13 | 1 |
| `prime_gap_coefficient_eq_gnat` (l.177) | p(k+2) − p(k+1) = gnat(k+1). | CONFIRMÉE | V13 | 0 |
| `prime_gap_coefficient_ge_one` (l.185) | L'écart premier p(k+2) − p(k+1) est ≥ 1. | CONFIRMÉE | V13 | 3 |
| `prime_gap_coefficient_pos` (l.192) | L'écart premier p(k+2) − p(k+1) est > 0. | CONFIRMÉE | V13 | 1 |
| `blockKernelWeight_sub_next_nonneg` (l.195) | La différence de poids consécutifs est ≥ 0. | CONFIRMÉE | AJOUT | 0 |
| `canonical_block_weak_tail_weight_eq_zero` (l.204) | Si X < p(mx+1), le poids de queue en mx est nul. | CONFIRMÉE (domaine: X < p(mx+1) ) | AJOUT | 0 |
| `canonical_block_exact_terminal_coefficient` (l.214) | Si p(r+1) ≤ X, le poids terminal vaut X − p(r+1). | CONFIRMÉE (domaine: p(r+1) ≤ X ) | AJOUT | 0 |
| `scaleBlockPairEnergy_ge_interior_prime_gap_sum` (l.226) | Si les indices intérieurs sont actifs, l'énergie est ≥ Σ (écart premier)×P_{k+1}². | CONFIRMÉE (domaine: my≤r et activité p(k+2) ≤ X pour k<r ) | AJOUT | 2 |
| `scaleBlockPairEnergy_ge_interior_prefix_square_sum` (l.248) | Sous activité intérieure, l'énergie est ≥ Σ P_{k+1}² nue. | CONFIRMÉE (domaine: my≤r et activité intérieure ) | AJOUT | 1 |
| `interior_prefix_square_le_scaleBlockPairEnergy` (l.260) | Sous activité intérieure, chaque préfixe intérieur au carré est ≤ énergie. | CONFIRMÉE (domaine: my≤r, activité, j dans [my,r) ) | AJOUT | 1 |
| `canonical_scale_block_endpoints` (l.270) | Pour x≥0, il existe my ≤ mx bornant le bloc canonique avec p(n+1) ≤ x pour n<mx et x < p(mx+1). | CONFIRMÉE (domaine: 0 ≤ x ) | AJOUT | 0 |
| `canonical_block_interior_activity` (l.350) | Sur le bloc canonique, tout k<r vérifie p(k+2) ≤ x. | CONFIRMÉE (domaine: saturation p(n+1) ≤ x pour n<mx, mx=r+1 ) | AJOUT | 0 |
| `one_step_extension_terminal_coercivity` (l.361) | Dans l'énergie prolongée d'un indice, le préfixe terminal a pour coefficient l'écart premier : écart × P² ≤ énergie. | CONFIRMÉE (domaine: my≤r, activité jusqu'à r ) | AJOUT | 1 |
| `one_step_extension_terminal_prefix_square_le` (l.381) | Forme nue : P(r+1)² ≤ énergie prolongée. | CONFIRMÉE (domaine: my≤r, activité jusqu'à r ) | AJOUT | 0 |

### `Round26M57ScaleInjectionEnergy`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `thetaErrorReal_eq_scaleFourDefect_add_previous` (l.139) | θerr(x) = défaut d'échelle quatre(x) + θerr(x/4). | CONFIRMÉE | AJOUT | 2 |
| `thetaScaleFourDefectReal_measurable` (l.151) | Le défaut d'échelle quatre est mesurable. | CONFIRMÉE | AJOUT | 3 |
| `thetaErrorReal_shift_measurable` (l.156) | t ↦ θerr(t/4) est mesurable. | CONFIRMÉE | AJOUT | 1 |
| `shift_mem_window` (l.159) | Si t ∈ [e^U, 2e^U] alors t/4 est dans la fenêtre décalée de log 4. | CONFIRMÉE (domaine: t dans la fenêtre ) | AJOUT | 2 |
| `thetaScaleFourDefectReal_bound_on_window` (l.173) | Sur la fenêtre [e^U,2e^U], \|défaut\| ≤ (5/2) log 4 · e^U. | CONFIRMÉE (domaine: log 4 ≤ U ) | AJOUT | 3 |
| `thetaErrorReal_shift_bound_on_window` (l.190) | Sur la fenêtre, \|θerr(t/4)\| ≤ (log 4 /2) e^U. | CONFIRMÉE (domaine: log 4 ≤ U ) | AJOUT | 1 |
| `thetaScaleFourDefectReal_intervalIntegrable` (l.204) | défaut²/t² est intégrable sur la fenêtre. | CONFIRMÉE (domaine: log 4 ≤ U ) | AJOUT | 9 |
| `thetaErrorReal_shift_intervalIntegrable` (l.211) | θerr(t/4)²/t² est intégrable sur la fenêtre. | CONFIRMÉE (domaine: log 4 ≤ U ) | AJOUT | 5 |
| `thetaScaleFourMellinEnergy_nonneg` (l.222) | L'énergie de Mellin d'échelle quatre est ≥ 0. | CONFIRMÉE (domaine: log 4 ≤ U ) | AJOUT | 0 |
| `thetaErrorReal_shift_integral_eq_quarter_mellin` (l.227) | ∫ θerr(t/4)²/t² sur la fenêtre = (1/4)·énergie locale en U−log 4. | CONFIRMÉE | AJOUT | 4 |
| `thetaMellinLocalEnergy_scale_four_recurrence` (l.251) | E(U) ≤ 2·énergie d'échelle quatre + (1/2)E(U−log 4). | CONFIRMÉE (domaine: log 4 ≤ U ) | AJOUT | 1 |
| `thetaMellinLocalEnergy_le_exp_bound` (l.300) | E(U) ≤ 4 (log 4)² e^U. | CONFIRMÉE (domaine: 0 ≤ U ) | AJOUT | 2 |
| `thetaMellinLocalEnergy_base_bound` (l.328) | Pour 0 ≤ U < log 4, l'énergie locale est ≤ 16 (log 4)². | CONFIRMÉE (domaine: 0 ≤ U < log 4 ) | AJOUT | 1 |
| `theta_scale_four_energy_subexponential_implies_theta_mellin` (l.341) | La sous-exponentialité de l'énergie d'échelle quatre entraîne celle de l'énergie locale θ-Mellin. | CONFIRMÉE (domaine: sous-exponentialité de thetaScaleFourMellinEnergy (obligation B4, docstring) ) | AJOUT | 2 |
| `downClosed_filter_eq_range` (l.416) | Un sous-ensemble de range(N+1) filtré et fermé par le bas est un range. | CONFIRMÉE (domaine: P fermé par le bas ) | AJOUT | 3 |
| `fullATCumulative_sub_eq_sum_annulus` (l.440) | Pour y ≤ x, y ≥ 0, la différence des cumulés aT est la somme de aT sur l'annulus réel (y,x]. | CONFIRMÉE (domaine: y ≤ x, 0 ≤ y ) | AJOUT | 1 |
| `scale_block_aT_eq_innovation_sum_add_boundary` (l.495) | Pour x ≥ 0, la différence d'échelle quatre du cumulé aT = somme d'innovation sur le bloc + bord borné par 1. | CONFIRMÉE (domaine: 0 ≤ x ) | AJOUT | 2 |
| `scale_block_innovation_square_eq_pair_sum` (l.596) | Le carré de la somme d'innovation du bloc égale la double somme complète des produits croisés. | CONFIRMÉE | AJOUT | 1 |
| `VTkernel_eq_scaleBlockPairEnergy_add_rest` (l.618) | Le noyau VT d'innovation = énergie de paires du bloc + somme sur les paires complémentaires. | CONFIRMÉE (domaine: mx ≤ N ) | AJOUT | 1 |
| `scaleBlockPairEnergyFrom_p_gnat_eq` (l.651) | L'énergie de bloc construite depuis (p,gnat) égale l'énergie canonique. | CONFIRMÉE | AJOUT | 1 |
| `zero_reconstructed_scale_block_pair_energy_eq_canonical` (l.656) | L'énergie de bloc construite depuis les positions/écarts reconstruits des zéros égale l'énergie canonique. | CONFIRMÉE | V48,V159,V174 | 2 |

### `Round26M57TwoBlockTerminalCoercivity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `blockInnovationPrefix_base_change` (l.41) | Le préfixe sur [my,k) = préfixe sur [my,my') + préfixe sur [my',k). | CONFIRMÉE (domaine: my ≤ my' ≤ k ) | AJOUT | 2 |
| `blockInnovationPrefix_succ_self` (l.49) | Le préfixe d'un pas unique vaut innovationJ my. | CONFIRMÉE | AJOUT | 0 |
| `blockInnovationPrefix_sub_base` (l.55) | P(my,k) − P(my',k) = P(my,my'). | CONFIRMÉE (domaine: my ≤ my' ≤ k ) | AJOUT | 0 |
| `canonical_extension_left_endpoint_le` (l.62) | Le nouveau bord gauche canonique de l'extension à x'=p(r+2) vérifie my' ≤ r. | CONFIRMÉE (domaine: x' = p(r+2) et caractérisation canonique du bord gauche ) | AJOUT | 1 |
| `terminal_prefix_two_block_coercivity` (l.86) | Le carré du préfixe terminal est ≤ 2×énergie du bloc initial + 2×énergie du bloc étendu. | CONFIRMÉE (domaine: my ≤ my' ≤ r et activité aux paramètres x, x' ) | AJOUT | 1 |
| `canonical_terminal_prefix_two_block_coercivity` (l.126) | Forme canonique de la coercivité à deux blocs, avec my' ≤ r déchargé. | CONFIRMÉE (domaine: my ≤ my', activité, caractérisation du bord gauche ) | AJOUT | 1 |

### `Round26M58DynamicCellTwoBlockBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `dynamicPairCellWeight_nonneg` (l.77) | Le poids de cellule 1/a − 1/b est ≥ 0. | CONFIRMÉE | AJOUT | 2 |
| `dynamicPairCellWeight_eq_zero_of_degenerate` (l.87) | Une cellule dégénérée (a=b) a un poids nul. | CONFIRMÉE (domaine: cellule dégénérée ) | AJOUT | 1 |
| `dynamicPairwiseInnovationForm_nonneg` (l.93) | La forme pairwise dynamique d'innovation est ≥ 0. | CONFIRMÉE | AJOUT | 0 |
| `dynamicInnovationBlock_eq_blockInnovationPrefix` (l.104) | Le bloc d'innovation dynamique (i,j) est le préfixe de bloc (j+1,i+1). | CONFIRMÉE | AJOUT | 1 |
| `dynamic_cell_canonical_endpoints` (l.113) | Pour une cellule non dégénérée, quatre encadrements premiers exacts et j ≤ i. | CONFIRMÉE (domaine: cellule non dégénérée ) | AJOUT | 3 |
| `dynamic_cell_scale_block_eq_Ico` (l.129) | Pour une cellule non dégénérée, le bloc d'échelle canonique est Ico (j+1) (i+1). | CONFIRMÉE (domaine: cellule non dégénérée ) | AJOUT | 0 |
| `exists_canonical_left_endpoint` (l.191) | Pour tout x il existe m avec n<m ⟺ p(n+1) ≤ x/4. | CONFIRMÉE | AJOUT | 1 |
| `exists_canonical_left_endpoint_family` (l.215) | Il existe une famille e des bords gauches canoniques pour les paramètres p(i+2). | CONFIRMÉE | AJOUT | 0 |
| `canonical_left_endpoint_mono` (l.221) | Si x1 ≤ x2, le bord gauche canonique de x1 est ≤ celui de x2. | CONFIRMÉE (domaine: x1≤x2 et caractérisations des bords ) | AJOUT | 0 |
| `dynamic_cell_left_endpoint_le` (l.234) | Sur une cellule non dégénérée, j+1 ≤ bord gauche canonique du paramètre étendu p(i+2). | CONFIRMÉE (domaine: cellule non dégénérée et caractérisation du bord ) | AJOUT | 1 |
| `dynamic_cell_two_block_coercivity` (l.248) | Sur cellule non dégénérée, le carré du bloc d'innovation dynamique ≤ 2×énergie du bloc initial + 2×énergie du bloc étendu. | CONFIRMÉE (domaine: cellule non dégénérée et bord canonique ) | AJOUT | 1 |
| `dynamicPairwiseInnovationForm_le_weighted_two_block_energy` (l.276) | La forme pairwise dynamique est ≤ somme pondérée par les poids cellulaires positifs des coercivités à deux blocs. | CONFIRMÉE (domaine: famille e de bords canoniques ) | AJOUT | 0 |
| `dynamicPairCellWeight_row_sum_eq` (l.307) | La somme des poids cellulaires sur une ligne télescope : 1/a_0 − 1/a_J. | CONFIRMÉE | AJOUT | 2 |
| `dynamicPairCellWeight_row_sum_le` (l.314) | La somme des poids cellulaires d'une ligne est ≤ 1/e^U uniformément. | CONFIRMÉE | AJOUT | 0 |
| `extended_block_term_row_factorisation` (l.333) | Le terme de bloc prolongé se factorise sur chaque ligne : (poids total de ligne) × 2 × E_prolongée. | CONFIRMÉE | AJOUT | 0 |

### `Round26M58GrammarSectorVacuity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `GrammarSectorMeromorphicContinuationAt.mk.congr_simp` (l.None) | Lemme de congruence auto-généré du constructeur de continuation méromorphe de secteur. [terme hors maître] | CONFIRMÉE | AJOUT | 0 |
| `GrammarSectorMeromorphicFamilyAt.mk.congr_simp` (l.None) | Lemme de congruence auto-généré du constructeur de famille de secteurs. | CONFIRMÉE (domaine: égalité des secteurs ) | AJOUT | 0 |
| `sectorSimplePole_meromorphicAt` (l.59) | Le pôle simple de secteur c/(x−ρ) est méromorphe en ρ. | CONFIRMÉE | AJOUT | 0 |
| `residue_sectorSimplePole` (l.65) | Le résidu du pôle simple de secteur en ρ est c. | CONFIRMÉE | AJOUT | 1 |
| `residue_const_zero` (l.75) | Le résidu de la fonction nulle est 0. | CONFIRMÉE | AJOUT | 1 |
| `sum_transform6_expand` (l.80) | Une somme complexe sur Transform6 se développe en quatre termes. | CONFIRMÉE | AJOUT | 0 |
| `grammarSectorFamily_admits_arithmetically_empty_witness` (l.107) | L'interface de famille de secteurs est habitée pour tout ρ (par un témoin à trois secteurs nuls). | CONFIRMÉE | AJOUT | 0 |
| `sum_transform6_expand_real` (l.129) | Une somme réelle sur Transform6 se développe en quatre termes. | CONFIRMÉE | AJOUT | 1 |
| `spreadSectorVector_globalCoord` (l.144) | La coordonnée globale du vecteur de secteurs étalé (c,t) est c. | CONFIRMÉE | AJOUT | 1 |
| `spreadSectorVector_energy_ge` (l.149) | L'énergie du vecteur étalé (c,t) est ≥ t². | CONFIRMÉE | AJOUT | 2 |
| `globalCoord_does_not_bound_sectorEnergy` (l.159) | La coordonnée globale ne borne pas l'énergie de secteur : pour tout c et M, il existe v de coordonnée c et d'énergie ≥ M. | CONFIRMÉE | AJOUT | 0 |
| `spreadSectorFamily_residue` (l.192) | Le résidu spectral de la famille étalée égale le vecteur étalé du résidu explicite d'échelle quatre. | CONFIRMÉE | AJOUT | 1 |
| `grammarSectorFamily_sectorEnergy_unbounded` (l.200) | À résidu global inchangé, l'énergie sectorielle d'une famille peut dépasser toute borne M. | CONFIRMÉE | AJOUT | 0 |

### `Round26M58MarkedStateB4Comparison`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `cellLength_le_four_prime_gap` (l.82) | Chaque longueur de cellule est ≤ 4 × écart premier correspondant. | CONFIRMÉE | AJOUT | 1 |
| `scaleSubBreak_ge_exp` (l.107) | L'extrémité gauche de toute cellule est ≥ e^U. | CONFIRMÉE | AJOUT | 5 |
| `geometricCellVariance_div_le_cubic_uniform` (l.113) | Variance géométrique de cellule / poids ≤ (9/64)(longueur)³/e^{2U}. | CONFIRMÉE | AJOUT | 1 |
| `geometricContribution_sum_le_of_maxCellLength` (l.153) | La contribution géométrique totale est ≤ (9/64) L² e^{−U} si toute cellule a longueur ≤ L. | CONFIRMÉE (domaine: log 12 ≤ U et longueur de cellule ≤ L ) | AJOUT | 2 |
| `geometricContribution_sum_le_of_maxPrimeGap` (l.231) | Même borne avec G majorant 4×écart premier. | CONFIRMÉE (domaine: log 12 ≤ U et 4×écart premier ≤ G ) | AJOUT | 0 |
| `cellStateDrift_sq_div_le_cubic_uniform` (l.257) | Dérive d'état² / poids ≤ (9/64)(longueur)³/e^{2U}. | CONFIRMÉE | AJOUT | 1 |
| `driftContribution_sum_le_of_maxCellLength` (l.283) | La contribution de dérive totale est ≤ (9/64) L² e^{−U} si toute cellule a longueur ≤ L. | CONFIRMÉE (domaine: log 12 ≤ U et longueur ≤ L ) | AJOUT | 2 |
| `centeredCell_le_two_weighted_plus_two_drift` (l.360) | Discrépance centrée²/poids ≤ 2·poids·état² + 2·dérive²/poids, par cellule. | CONFIRMÉE | AJOUT | 1 |
| `centeredContribution_sum_le_two_weighted_plus_drift` (l.397) | La contribution centrée totale est ≤ 2×somme pondérée d'état marqué + terme de dérive (borne en L, type tronqué). [type tronqué] | CONFIRMÉE (domaine: log 12 ≤ U et longueur de cellule ≤ L ) | AJOUT | 1 |
| `thetaScaleFourMellinEnergy_le_two_weighted_plus_remainder` (l.465) | L'énergie θ-Mellin d'échelle quatre est ≤ 2×Σ poids·état² + (27/64) L² e^{−U}. | CONFIRMÉE (domaine: log 12 ≤ U et longueur de cellule ≤ L ) | AJOUT | 0 |
| `weightedMarkedState_cell_le_two_centered_plus_two_drift` (l.521) | Par cellule, poids·état² ≤ 2 discrépance²/poids + 2 dérive²/poids. | CONFIRMÉE | AJOUT | 1 |
| `weightedMarkedStateEnergy_sum_le_two_centered_plus_drift` (l.559) | Somme d'état marqué pondéré ≤ 2×somme centrée + terme de dérive (type tronqué). [type tronqué] | CONFIRMÉE (domaine: log 12 ≤ U et longueur ≤ L ) | AJOUT | 1 |
| `weightedMarkedStateEnergy_le_two_B4_plus_remainder` (l.633) | Σ poids·état² ≤ 2×énergie θ-Mellin d'échelle quatre + (9/32) L² e^{−U}. | CONFIRMÉE (domaine: log 12 ≤ U et longueur ≤ L ) | AJOUT | 0 |

### `Round26M58MarkedStateCumulativeOperator`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `centeredMeanEnergy_eq_global_weighted_state_energy` (l.51) | L'énergie centrée totale égale l'énergie d'état marqué pondéré plus des termes croisés état×dérive (type tronqué). [type tronqué] | CONFIRMÉE (domaine: log 12 ≤ U ) | AJOUT | 0 |
| `sum_weight_mul_partial_sum_eq_tail_bilinear` (l.97) | Identité d'Abel/Fubini : Σ_j w_j Σ_{k<j} inc_k = Σ_k inc_k Σ_{j>k} w_j. | CONFIRMÉE | AJOUT | 1 |
| `row_energy_expansion` (l.126) | Si state_j = s0 + Σ_{k<j} inc_k, l'énergie pondérée se décompose en terme constant + linéaire + quadratique. | CONFIRMÉE (domaine: récurrence de Chasles sur state ) | AJOUT | 1 |
| `cellAffineState_row_energy_eq_cumulative_operator_plus_quadratic_remainder` (l.154) | L'énergie d'état marqué sur une ligne active = constante + opérateur cumulatif sur les incréments + reste quadratique. | CONFIRMÉE (domaine: ligne active (pas strict de scaleSubBreak jusqu'à Nrow) ) | AJOUT | 0 |
| `cellWeight_eq_zero_of_ge` (l.205) | Le poids de cellule est nul au-delà de la diagonale (i+1 ≤ j). | CONFIRMÉE (domaine: i+1 ≤ j ) | AJOUT | 1 |
| `centeredMeanEnergyRow_eq_restricted_to_diagonal` (l.211) | L'énergie de ligne égale sa restriction à j < min(i+1, Horizon). | CONFIRMÉE | AJOUT | 1 |
| `cellAffineState_shifted_chasles` (l.234) | Chasles décalé : état en j = état en q + somme des incréments locaux sur [q,j). | CONFIRMÉE (domaine: q ≤ j et pas stricts entre q et j ) | AJOUT | 1 |
| `globalWeightedStateEnergy_eq_diagonal_restricted` (l.255) | L'énergie globale d'état pondéré égale sa restriction diagonale. | CONFIRMÉE | AJOUT | 0 |
| `scaleSubBreak_weight_pos_iff_step_pos` (l.280) | Poids de cellule > 0 ⟺ pas scaleSubBreak strict. | CONFIRMÉE | AJOUT | 5 |
| `scaleSubBreak_step_pos_iff_maxmin` (l.300) | Pas strict ⟺ max(4p(j+1),W_i) < min(4p(j+2),W_{i+1}). | CONFIRMÉE | AJOUT | 1 |
| `scaleSubBreak_step_pos_iff_four_conditions` (l.341) | Pas strict ⟺ quatre conditions (tautologie, sortie, entrée, fenêtre). | CONFIRMÉE | AJOUT | 2 |
| `scaleSubBreak_weight_pos_iff_four_conditions` (l.363) | Poids > 0 ⟺ les quatre conditions. | CONFIRMÉE | AJOUT | 1 |
| `blockWeight_pos_iff_scaleSubBreak_step_pos` (l.374) | blockWeight > 0 ⟺ pas strict de scaleSubBreak. | CONFIRMÉE (domaine: j < canonicalTHorizon U ) | AJOUT | 1 |
| `blockWeight_pos_iff_strict_row_overlap` (l.382) | blockWeight > 0 ⟺ les quatre conditions de recouvrement de ligne. | CONFIRMÉE (domaine: j < canonicalTHorizon U ) | AJOUT | 0 |

### `Round26M58MarkedStateEnergy`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `_private.RhGapCriterion.Round26M58MarkedStateEnergy.0.RhGap.rowActiveThreshold_witness` (l.74) | e^U ≤ p(canonicalTHorizon U + 2). | CONFIRMÉE | AJOUT | 1 |
| `rowActiveStart_set_nonempty` (l.84) | L'ensemble des j avec W_i < 4p(j+2) est non vide. | CONFIRMÉE | AJOUT | 1 |
| `rowActiveStopRaw_set_nonempty` (l.93) | L'ensemble des j avec ¬(4p(j+1) < W_{i+1}) est non vide. | CONFIRMÉE | AJOUT | 1 |
| `lt_four_p_succ_succ_iff_rowActiveStart_le` (l.102) | W_i < 4p(j+2) ⟺ rowActiveStart ≤ j. | CONFIRMÉE | AJOUT | 1 |
| `four_p_succ_lt_iff_lt_rowActiveStopRaw` (l.117) | 4p(j+1) < W_{i+1} ⟺ j < rowActiveStopRaw. | CONFIRMÉE | AJOUT | 1 |
| `row_positive_support_interval` (l.135) | Poids de cellule > 0 ⟺ j ∈ [rowActiveStart, rowActiveStop). | CONFIRMÉE | AJOUT | 6 |
| `rowActiveStop_le_i_succ_of_nonempty` (l.159) | Si la ligne est non vide, rowActiveStop ≤ i+1. | CONFIRMÉE (domaine: rowActiveStart < rowActiveStop ) | AJOUT | 0 |
| `centeredMeanEnergyRow_eq_rowActiveSupport` (l.193) | L'énergie de ligne égale sa restriction au support actif exact. | CONFIRMÉE (domaine: rowActiveStop ≤ Horizon ) | AJOUT | 2 |
| `globalWeightedStateEnergy_eq_rowActiveSupport` (l.221) | L'énergie globale égale sa restriction au support actif exact de chaque ligne. | CONFIRMÉE (domaine: rowActiveStop ≤ HorizonInner pour toute ligne ) | AJOUT | 1 |
| `cellAffineState_eq_initial_plus_active_increments` (l.238) | Sur le support actif, état en j = état initial + somme des incréments actifs. | CONFIRMÉE (domaine: rowActiveStart ≤ j < rowActiveStop ) | AJOUT | 2 |
| `rowActiveTailWeight_telescopes` (l.259) | Le poids inverse-masse télescope sur Ico q r : 1/a_q − 1/a_r. | CONFIRMÉE (domaine: q ≤ r ) | AJOUT | 2 |
| `rowActiveSupport_totalTailWeight_eq` (l.274) | La masse totale du support actif vaut 1/a(start) − 1/a(stop). | CONFIRMÉE | AJOUT | 1 |
| `log_ratio_second_order_upper` (l.312) | Pour 0<a≤b, log b − log a − 1 + a/b ≤ (b−a)²/(2ab). | CONFIRMÉE (domaine: 0<a, a≤b ) | AJOUT | 1 |
| `cellStateDrift_sq_div_le_cubic` (l.333) | Pour 0<a<b, dérive²/(1/a−1/b) ≤ (9/64)(b−a)³/a². | CONFIRMÉE (domaine: 0<a<b ) | AJOUT | 1 |
| `logLinFracAuxFn_hasDerivAt` (l.389) | logLinFracAuxFn a pour dérivée x⁻¹ − 4(x+1)⁻² en x>0. | CONFIRMÉE (domaine: 0<x ) | AJOUT | 1 |
| `logLinFracAuxFn_deriv_nonneg` (l.408) | Pour x>1, x⁻¹ − 4(x+1)⁻² ≥ 0. | CONFIRMÉE (domaine: 1<x ) | AJOUT | 1 |
| `logLinFracAuxFn_continuousOn` (l.419) | logLinFracAuxFn est continue sur [1,∞). | CONFIRMÉE | AJOUT | 1 |
| `two_mul_ratio_sub_one_div_add_one_le_log` (l.432) | Pour s ≥ 1, 2(s−1)/(s+1) ≤ log s. | CONFIRMÉE (domaine: 1 ≤ s ) | AJOUT | 1 |
| `log_ratio_second_order_lower` (l.460) | Pour 0<a≤b, 2(b−a)/(a+b) ≤ log b − log a. | CONFIRMÉE (domaine: 0<a, a≤b ) | AJOUT | 1 |
| `geometricCellVariance_div_le_cubic` (l.473) | Pour 0<a<b, variance géométrique/(1/a−1/b) ≤ (9/64)(b−a)³/a². | CONFIRMÉE (domaine: 0<a<b ) | AJOUT | 1 |
| `rowActiveStart_le_canonicalTHorizon` (l.537) | rowActiveStart ≤ canonicalTHorizon U. | CONFIRMÉE | AJOUT | 1 |
| `rowActiveStopRaw_le_canonicalTHorizon` (l.553) | rowActiveStopRaw ≤ canonicalTHorizon U. | CONFIRMÉE | AJOUT | 1 |
| `rowActiveStop_le_canonicalTHorizon` (l.564) | rowActiveStop ≤ canonicalTHorizon U. | CONFIRMÉE | AJOUT | 3 |
| `centeredMeanEnergyRow_eq_rowActiveSupport_canonical` (l.574) | À l'horizon canonique, l'énergie de ligne égale sa restriction au support actif exact, sans hypothèse. | CONFIRMÉE | AJOUT | 0 |
| `globalWeightedStateEnergy_eq_rowActiveSupport_canonical` (l.585) | À l'horizon canonique, l'énergie globale pondérée égale sa restriction au support actif exact, pour tout HorizonOuter. | CONFIRMÉE | AJOUT | 2 |

### `Round26M58MarkedStateGeometry`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `thetaScaleFourCellConstant_succ_sub` (l.63) | C_{m,k+1} − C_{m,k} = log p_{k+1}. | CONFIRMÉE (domaine: 1 ≤ k et k+1 ≤ m ) | V48 | 2 |
| `scaleSubBreak_succ_eq_of_ge` (l.77) | Au-delà de la diagonale (i+1 ≤ j), scaleSubBreak est constant en j. | CONFIRMÉE (domaine: i+1 ≤ j ) | AJOUT | 2 |
| `telescope_range` (l.131) | Télescopage réel : Σ_{j<N}(f(j+1)−f(j)) = f N − f 0. | CONFIRMÉE | AJOUT | 5 |
| `scaleSubBreak_length_row_telescopes` (l.138) | La somme des longueurs de cellule d'une ligne vaut windowBreak(i+1) − windowBreak(i). | CONFIRMÉE (domaine: log 12 ≤ U ) | AJOUT | 1 |
| `scaleSubBreak_length_total_telescopes` (l.147) | La somme des longueurs de toutes les cellules vaut e^U. | CONFIRMÉE (domaine: log 12 ≤ U ) | AJOUT | 3 |
| `scaleSubBreak_eq_blockCellLeft_of_overlap` (l.178) | scaleSubBreak U i j = blockCellLeft U i j si le sous-point reste dans la ligne ou la ligne est saturée à 2e^U. | CONFIRMÉE (domaine: j<canonicalTHorizon U et recouvrement gauche ) | AJOUT | 1 |
| `scaleSubBreak_succ_eq_blockCellRight_of_overlap` (l.195) | scaleSubBreak U i (j+1) = blockCellRight U i j sous recouvrement droit. | CONFIRMÉE (domaine: j<canonicalTHorizon U et W_i ≤ 4p(j+2) ) | AJOUT | 1 |
| `scaleSubBreak_cell_degenerate_of_not_right_overlap` (l.218) | Sans recouvrement droit, la cellule se réduit à un point W_i et blockWeight = 0. | CONFIRMÉE (domaine: j<canonicalTHorizon U et 4p(j+2) < W_i ) | AJOUT | 1 |
| `scaleSubBreak_cell_degenerate_of_not_left_overlap` (l.254) | Sans recouvrement gauche, la cellule se réduit à W_{i+1} et blockWeight = 0. | CONFIRMÉE (domaine: j<canonicalTHorizon U, W_{i+1} < 4p(j+1), W_{i+1} < 2e^U ) | AJOUT | 1 |
| `cellInverseMass_eq_blockWeight_of_overlaps` (l.291) | Sous les deux recouvrements, la masse inverse de cellule égale blockWeight. | CONFIRMÉE (domaine: j<canonicalTHorizon U et les deux recouvrements ) | AJOUT | 1 |
| `cellInverseMass_eq_blockWeight` (l.308) | La masse inverse de cellule égale blockWeight pour j<canonicalTHorizon U (cas dégénérés inclus). | CONFIRMÉE (domaine: j < canonicalTHorizon U ) | AJOUT | 1 |
| `scaleCellQuadraticForm_completed_square_homogeneous` (l.347) | (1/a−1/b)·forme quadratique = discrépance² + variance géométrique. | CONFIRMÉE | AJOUT | 1 |
| `cellWeight_pos_of_active` (l.364) | Pour 0<a<b, 1/a − 1/b > 0. | CONFIRMÉE (domaine: 0<a, a<b ) | AJOUT | 6 |
| `scaleCellQuadraticForm_completed_square` (l.371) | Sur cellule active, forme quadratique = d²/w + G/w. | CONFIRMÉE (domaine: 0<a<b ) | AJOUT | 1 |
| `logSqAuxFn_hasDerivAt` (l.395) | logSqAuxFn a pour dérivée 1 + x⁻² − 2x⁻¹ en x≠0. | CONFIRMÉE (domaine: x ≠ 0 ) | AJOUT | 1 |
| `logSqAuxFn_deriv_nonneg` (l.411) | Pour x>1, 1 + x⁻² − 2x⁻¹ ≥ 0. | CONFIRMÉE (domaine: 1<x ) | AJOUT | 1 |
| `logSqAuxFn_continuousOn` (l.415) | logSqAuxFn est continue sur [1,∞). | CONFIRMÉE | AJOUT | 1 |
| `two_mul_log_le_of_ge_one` (l.421) | Pour s ≥ 1, 2 log s ≤ s − 1/s. | CONFIRMÉE (domaine: 1 ≤ s ) | AJOUT | 2 |
| `log_le_sqrt_sub_inv_sqrt` (l.439) | Pour s ≥ 1, log s ≤ √s − 1/√s. | CONFIRMÉE (domaine: 1 ≤ s ) | AJOUT | 1 |
| `log_ratio_sq_le` (l.447) | Pour 0<a≤b, (log b − log a)² ≤ (1/a−1/b)(b−a). | CONFIRMÉE (domaine: 0<a≤b ) | AJOUT | 1 |
| `geometricCellVariance_nonneg` (l.472) | Pour 0<a≤b, la variance géométrique de cellule est ≥ 0. | CONFIRMÉE (domaine: 0<a≤b ) | AJOUT | 1 |
| `scaleCellQuadraticForm_completed_square_le` (l.489) | Carré complété déshomogénéisé, étendu à a ≤ b. | CONFIRMÉE (domaine: 0<a≤b ) | AJOUT | 1 |
| `thetaScaleFourMellinEnergy_eq_global_mean_variance_sum` (l.501) | Pour U ≥ log 12, l'énergie θ-Mellin d'échelle quatre = Σ discrépance²/poids + Σ variance géométrique/poids. | CONFIRMÉE (domaine: log 12 ≤ U ) | AJOUT | 3 |
| `geometricCellVariance_div_le_cellLength` (l.538) | Pour 0<a≤b, variance géométrique/poids ≤ (9/16)(b−a). | CONFIRMÉE (domaine: 0<a≤b ) | AJOUT | 1 |
| `geometricContribution_sum_le_exp` (l.552) | La contribution géométrique totale est ≤ (9/16) e^U. | CONFIRMÉE (domaine: log 12 ≤ U ) | AJOUT | 1 |
| `thetaScaleFourMellinEnergy_normalized_identity` (l.621) | e^{−U}·énergie = énergie centrée normalisée + énergie géométrique normalisée. | CONFIRMÉE (domaine: log 12 ≤ U ) | AJOUT | 0 |
| `normalizedGeometricStaircaseEnergy_le` (l.632) | L'énergie géométrique normalisée est ≤ 9/16. | CONFIRMÉE (domaine: log 12 ≤ U ) | AJOUT | 0 |
| `thetaScaleFourDefectReal_eq_affine_on_cell` (l.661) | Sur une cellule non dégénérée, le défaut d'échelle quatre est affine : (3/4)t + constante de cellule. | CONFIRMÉE (domaine: cellule non dégénérée et t dans la cellule demi-ouverte ) | AJOUT | 2 |
| `cellAffineState_eq_affine` (l.700) | L'état marqué d'une cellule non dégénérée vaut (3/4)a + constante de cellule. | CONFIRMÉE (domaine: cellule non dégénérée ) | AJOUT | 3 |
| `thetaScaleFourDefectReal_eq_cellAffineState_add_drift` (l.709) | Sur la cellule, défaut = état marqué + (3/4)(t−a). | CONFIRMÉE (domaine: cellule non dégénérée et t dans la cellule ) | AJOUT | 0 |
| `cellAffineState_step_eq_chebyshev` (l.721) | L'incrément de l'état marqué entre deux cellules adjacentes s'écrit (3/4)Δlongueur + Δconstante de cellule. | CONFIRMÉE SOUS CONDITION (deux cellules consécutives non dégénérées) | AJOUT | 5 |
| `cellAffineState_step_eq_prime_log` (l.738) | Même incrément réduit à (3/4)Δlongueur + log p(j+2). | CONFIRMÉE (domaine: cellules non dégénérées et j+1 ≤ i ) | AJOUT | 0 |
| `cellAffineState_step_eq_R` (l.753) | Même incrément réécrit en coordonnées R/correction de Tchebychev. | CONFIRMÉE SOUS CONDITION (deux cellules consécutives non dégénérées) | AJOUT | 0 |
| `cellAffineState_row_chasles` (l.782) | Chasles de ligne : état en N − état en 0 = somme des incréments. | CONFIRMÉE (domaine: cellules non dégénérées de 0 à N ) | AJOUT | 1 |
| `thetaScaleFourCellConstant_succ_sub_eq_innovation` (l.801) | Incrément de la constante de cellule en coordonnées d'innovationJ, cobord et log. | CONFIRMÉE (domaine: j+1 ≤ i ) | AJOUT | 1 |
| `cellAffineState_step_eq_innovation` (l.830) | Incrément de l'état marqué en coordonnées innovationJ (forme directe). | CONFIRMÉE (domaine: cellules non dégénérées et j+1 ≤ i ) | AJOUT | 0 |
| `staircaseCellDiscrepancy_eq_weighted_state_add_drift` (l.861) | Discrépance de cellule = poids × état marqué + dérive. | CONFIRMÉE (domaine: cellule non dégénérée ) | AJOUT | 2 |
| `staircaseCellDiscrepancy_sq_div_eq_weighted_state_energy` (l.878) | d²/w = w·état² + 2·état·dérive + dérive²/w par cellule active. | CONFIRMÉE (domaine: cellule non dégénérée ) | AJOUT | 1 |
| `staircaseCellDiscrepancy_sq_div_eq_weighted_state_energy_le` (l.901) | Même identité pour cellule active ou dégénérée (a ≤ b). | CONFIRMÉE (domaine: a ≤ b ) | AJOUT | 3 |

### `Round26M58MarkedStateGram`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `sum_weight_mul_partial_sum_eq_tail_bilinear_Ico` (l.93) | Version Ico de l'identité d'Abel/Fubini. | CONFIRMÉE (domaine: q ≤ r ) | AJOUT | 1 |
| `row_energy_expansion_Ico` (l.120) | Version Ico du développement d'énergie de ligne. | CONFIRMÉE (domaine: q ≤ r et récurrence de Chasles sur [q,r) ) | AJOUT | 1 |
| `quadraticRemainder_eq_gram_Ico` (l.140) | Le reste quadratique de l'énergie de ligne égale la double somme Gram à noyau T(max k l). | CONFIRMÉE | AJOUT | 1 |
| `row_energy_expansion_Ico_gram` (l.197) | Développement de l'énergie de ligne sur Ico q r avec double somme Gram à noyau T(max k l). | CONFIRMÉE (domaine: q ≤ r et récurrence de Chasles sur [q,r) ) | AJOUT | 2 |
| `rowActiveEnergy_augmentedGram_factorization` (l.212) | L'énergie de ligne sur le support actif exact se factorise en terme constant + linéaire + double somme Gram (type tronqué). [type tronqué] | CONFIRMÉE | AJOUT | 1 |
| `globalWeightedStateEnergy_augmentedGram_factorization` (l.248) | Somme sur i de la factorisation Gram de ligne = énergie globale à l'horizon canonique (type tronqué). [type tronqué] | CONFIRMÉE | AJOUT | 0 |
| `tailWeight_eq_zero_of_ge` (l.288) | La masse de queue sur Ico (k+1) r est nulle si r ≤ k+1. | CONFIRMÉE (domaine: r ≤ k+1 ) | AJOUT | 2 |
| `gram_linear_drops_terminal` (l.295) | Le terme linéaire de Gram ignore la coordonnée terminale (k jusqu'à r−1 au lieu de r). | CONFIRMÉE | AJOUT | 1 |
| `gram_quadratic_drops_terminal` (l.317) | Le terme quadratique de Gram ignore la coordonnée terminale dans les deux indices. | CONFIRMÉE | AJOUT | 1 |
| `row_energy_expansion_Ico_gram_reduced` (l.360) | Identité de Gram réduite : sommes sur Ico q (r−1). | CONFIRMÉE (domaine: q ≤ r et récurrence de Chasles ) | AJOUT | 2 |
| `rowActiveEnergy_reducedGram_factorization` (l.377) | Factorisation de Gram réduite de la ligne sur le support actif exact (type tronqué). [type tronqué] | CONFIRMÉE | AJOUT | 2 |
| `globalWeightedStateEnergy_reducedGram_factorization` (l.413) | Somme sur i de la factorisation réduite = énergie globale à l'horizon canonique (type tronqué). [type tronqué] | CONFIRMÉE | AJOUT | 0 |
| `rowActiveEnergy_reducedGram_closedFormKernel` (l.437) | Factorisation réduite avec masses de queue en forme close télescopée K(a,b) (type tronqué). [type tronqué] | CONFIRMÉE | AJOUT | 0 |
| `reducedGram_of_any_state` (l.502) | Gram réduit pour toute fonction d'état f, incréments = différences avant. | CONFIRMÉE (domaine: q ≤ r ) | AJOUT | 1 |
| `centeredCellEnergy_eq_weighted_shiftedState_sq` (l.532) | Sur cellule active, d²/w = poids × (état décalé)². | CONFIRMÉE (domaine: cellule non dégénérée ) | AJOUT | 1 |
| `centeredRowEnergy_eq_rowActiveSupport_canonical` (l.555) | L'énergie centrée de ligne à l'horizon canonique égale sa restriction au support actif exact. | CONFIRMÉE | AJOUT | 1 |
| `centeredRowEnergy_eq_weighted_shiftedState_sq` (l.590) | Sur le support actif, la somme d²/w = somme poids × état décalé². | CONFIRMÉE | AJOUT | 1 |
| `rowActiveEnergy_reducedGram_shiftedState_factorization` (l.608) | Gram réduit de l'énergie centrée sur le support actif en état décalé (type tronqué). [type tronqué] | CONFIRMÉE | AJOUT | 1 |
| `centeredRowEnergy_reducedGram_factorization` (l.644) | Même factorisation sur le domaine canonique non restreint (type tronqué). [type tronqué] | CONFIRMÉE | AJOUT | 1 |
| `globalCenteredEnergy_reducedGram_factorization` (l.672) | Somme sur i de la factorisation centrée réduite (type tronqué). [type tronqué] | CONFIRMÉE | AJOUT | 0 |

### `Round26M58ScaleFourEquivalence`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `thetaScaleFourDefectReal_bound_global` (l.59) | Pour t ≥ 0, \|défaut d'échelle quatre\| ≤ (5/4)(1+log 4) t. | CONFIRMÉE (domaine: 0 ≤ t ) | AJOUT | 3 |
| `thetaScaleFourDefectReal_intervalIntegrable_of_nonneg` (l.73) | défaut²/t² est intégrable sur la fenêtre pour tout U ≥ 0. | CONFIRMÉE (domaine: 0 ≤ U ) | AJOUT | 1 |
| `thetaScaleFourMellinEnergy_le_crude_of_nonneg` (l.91) | Pour U ≥ 0, énergie d'échelle quatre ≤ (25/16)(1+log 4)² e^U (borne de taux 1). | CONFIRMÉE (domaine: 0 ≤ U ) | AJOUT | 1 |
| `thetaScaleFourMellinEnergy_le_two_thetaMellin_plus_half` (l.121) | B4(U) ≤ 2E(U) + (1/2)E(U−log 4). | CONFIRMÉE (domaine: log 4 ≤ U ) | AJOUT | 1 |
| `subexponential_scale_four_of_subexponential_thetaMellin` (l.171) | La sous-exponentialité de l'énergie θ-Mellin entraîne celle de l'énergie d'échelle quatre. | CONFIRMÉE SOUS CONDITION (sous-exponentialité de thetaMellinLocalEnergy (docstring: de force RH)) | AJOUT | 1 |
| `subexponential_scale_four_iff_subexponential_thetaMellin` (l.230) | Sous-exponentialité de l'énergie d'échelle quatre ⟺ sous-exponentialité de l'énergie θ-Mellin. | CONFIRMÉE | AJOUT | 1 |
| `thetaScaleFourMellinEnergy_le_crude` (l.253) | Pour U ≥ log 4, énergie d'échelle quatre ≤ (25/16)(1+log 4)² e^U. | CONFIRMÉE (domaine: log 4 ≤ U ) | AJOUT | 0 |
| `thetaTwoScaleCorrelation_cross_pointwise` (l.292) | Polarisation ponctuelle : θerr(t)θerr(t/4)/t² = (1/2)(θerr(t)²+θerr(t/4)²−défaut²)/t². | CONFIRMÉE | AJOUT | 1 |
| `thetaTwoScaleCorrelation_intervalIntegrable` (l.301) | Le terme croisé θerr(t)θerr(t/4)/t² est intégrable sur la fenêtre. | CONFIRMÉE (domaine: log 4 ≤ U ) | AJOUT | 1 |
| `thetaScaleFourMellinEnergy_eq_bilinear` (l.317) | B4(U) = E(U) + (1/4)E(U−log 4) − 2C(U), C la corrélation à deux échelles. | CONFIRMÉE (domaine: log 4 ≤ U ) | AJOUT | 0 |
| `riemann_hypothesis_from_thetaMellin_subexponential` (l.354) | La sous-exponentialité de l'énergie θ-Mellin dyadique (Tchebychev) entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | AJOUT | 2 |

### `Round26Round27RHClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `thetaScaleFourDefectReal_on_prime_scale_cell` (l.34) | Sur une cellule où t et t/4 tombent entre deux premiers consécutifs, le défaut réel d'échelle quatre vaut 3t/4 + la constante de cellule. [terme hors maître] | CONFIRMÉE (domaine: 1≤m, 1≤j, p m ≤ t < p(m+1), p j ≤ t/4 < p(j+1)) | AJOUT | 5 |
| `affine_mellin_cell_integral_exact` (l.48) | ∫_a^b (αt+C)²/t² dt = α²(b−a) + 2αC(log b − log a) + C²(1/a − 1/b). | CONFIRMÉE (domaine: 0<a, 0<b) | AJOUT | 2 |
| `scaleSubBreak_step_nonneg` (l.103) | Les points de coupure scaleSubBreak sont croissants en j. | CONFIRMÉE | AJOUT | 28 |
| `scaleSubBreak_bounds` (l.112) | scaleSubBreak U i j est encadré par windowBreak U i et windowBreak U (i+1). | CONFIRMÉE | AJOUT | 6 |
| `scaleSubBreak_left_eq` (l.122) | Pour U ≥ log 12, scaleSubBreak U i 0 = windowBreak U i. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 6 |
| `scaleSubBreak_right_eq` (l.136) | scaleSubBreak U i (horizon canonique) = windowBreak U (i+1). | CONFIRMÉE | AJOUT | 5 |
| `scaleSubBreak_nontrivial_bounds` (l.150) | Si la sous-cellule (i,j) est non dégénérée, ses bornes sont dans [windowBreak i, windowBreak (i+1)]. | CONFIRMÉE (domaine: sous-cellule non dégénérée ) | AJOUT | 5 |
| `windowBreak_nontrivial_prime_bounds` (l.156) | Si la fenêtre i est non dégénérée, ses bornes sont entre p(i+1) et p(i+2). | CONFIRMÉE (domaine: fenêtre non dégénérée ) | AJOUT | 5 |
| `scaleSubBreak_nontrivial_prime_bounds` (l.171) | Si la sous-cellule (i,j) est non dégénérée, ses bornes sont entre 4p(j+1) et 4p(j+2). | CONFIRMÉE (domaine: sous-cellule non dégénérée ) | AJOUT | 5 |
| `scaleSubBreak_mem_window` (l.191) | Tout scaleSubBreak est dans [e^U, 2e^U]. | CONFIRMÉE | AJOUT | 12 |
| `scaleSubBreak_intervalIntegrable` (l.197) | Le défaut d'échelle quatre au carré sur t² est intégrable sur chaque sous-cellule. | CONFIRMÉE (domaine: log 4 ≤ U) | AJOUT | 1 |
| `thetaScaleFourMellinEnergy_eq_double_partition_sum` (l.207) | Pour U ≥ log 12, l'énergie de Mellin d'échelle quatre est la double somme des intégrales sur les sous-cellules. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 1 |
| `scale_subcell_energy_exact` (l.252) | Sur une sous-cellule contenue dans une cellule première, l'intégrale du défaut² vaut 9/16(b−a)+3/2·C·(log b−log a)+C²(1/a−1/b). | CONFIRMÉE (domaine: bornes p m ≤ a ≤ b ≤ p(m+1), p j ≤ a/4, b/4 ≤ p(j+1), 0<a, 0<b) | AJOUT | 1 |
| `scaleCellQuadraticForm_innovation_expansion` (l.290) | La forme quadratique de cellule à constante I+E se développe en I², termes croisés et terme en E. | CONFIRMÉE | AJOUT | 1 |
| `scale_subcell_energy_eq_quadratic_form` (l.304) | Sous les mêmes conditions, l'intégrale du défaut² égale scaleCellQuadraticForm a b C(m,j). | CONFIRMÉE (domaine: mêmes conditions de cellule) | AJOUT | 1 |
| `scaleCellQuadraticForm_same` (l.314) | La forme quadratique de cellule dégénérée (a,a) est nulle. | CONFIRMÉE | AJOUT | 3 |
| `scale_subcell_energy_exact_indexed` (l.319) | Pour U ≥ log 12 et sous-cellule non dégénérée, l'intégrale du défaut² égale la forme quadratique de constante C(i+1,j+1). | CONFIRMÉE (domaine: sous-cellule non dégénérée ) | AJOUT | 1 |
| `scale_subcell_energy_exact_indexed_or_degenerate` (l.359) | Même égalité sans condition de non-dégénérescence (cas dégénéré nul). | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 1 |
| `thetaScaleFourMellinEnergy_eq_indexed_quadratic_sum` (l.375) | Pour U ≥ log 12, l'énergie d'échelle quatre est la double somme des formes quadratiques indexées. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 6 |
| `sum_Ico_forward_difference` (l.392) | Σ_{n∈[j,m)} (F(n+1)−F n) = F m − F j. | CONFIRMÉE (domaine: j ≤ m) | AJOUT | 10 |
| `scaleSubBreak_nontrivial_inner_index_le_outer_index` (l.397) | Une sous-cellule non dégénérée a j ≤ i. | CONFIRMÉE (domaine: sous-cellule non dégénérée ) | AJOUT | 8 |
| `R_difference_eq_aT_block` (l.422) | Pour j≤i, R(i+1) − R(j+1) = Σ_{n∈[j+1,i+1)} aT n. | CONFIRMÉE (domaine: j ≤ i) | AJOUT | 0 |
| `aT_block_eq_innovation_block_plus_coboundary` (l.431) | Pour j≤i, le bloc aT = bloc d'innovation + phiOf(i+1) − phiOf(j+1). | CONFIRMÉE (domaine: j ≤ i) | AJOUT | 0 |
| `sum_Ico_eq_sum_range_indicator` (l.448) | Somme sur Ico a b = somme sur range N avec indicatrice, si b ≤ N. | CONFIRMÉE (domaine: b ≤ N) | AJOUT | 2 |
| `weighted_dynamic_innovation_pair_fubini` (l.464) | Échange de sommes (Fubini fini) de la forme paire pondérée des blocs d'innovation. | CONFIRMÉE | AJOUT | 1 |
| `thetaScaleFourCellConstant_eq_innovation_block_plus_explicit` (l.606) | Pour 1≤j≤m, la constante de cellule = bloc d'innovation + cobord − Σ(log p(n+1)−log p n) − (p m − p j). | CONFIRMÉE (domaine: 1≤j≤m) | AJOUT | 3 |
| `thetaScaleFourCellConstant_eq_R_difference` (l.643) | La constante de cellule (i+1,j+1) = ΔR + ΔRChebyshevCorrection − (p(i+1)−p(j+1)). | CONFIRMÉE | AJOUT | 2 |
| `thetaScaleFourDefectReal_eq_R_block_plus_local_correction` (l.658) | Sur une cellule première, le défaut d'échelle quatre = ΔR + correction locale + ΔRChebyshevCorrection. | CONFIRMÉE (domaine: t et t/4 dans leurs cellules premières) | AJOUT | 0 |
| `scale_cell_complete_innovation_cross_coefficient` (l.708) | La forme quadratique à constante (innovation + correction explicite) se décompose en trois termes avec coefficient croisé. | CONFIRMÉE | AJOUT | 1 |
| `weighted_dynamic_innovation_linear_fubini` (l.730) | Fubini fini de la somme linéaire pondérée des blocs d'innovation. | CONFIRMÉE | AJOUT | 1 |
| `weighted_dynamic_complete_innovation_linear_fubini` (l.798) | Fubini fini de la forme linéaire complète d'innovation avec noyau linéaire dynamique. | CONFIRMÉE | AJOUT | 1 |
| `dynamic_pairwise_innovation_form_eq_cell_sum` (l.839) | La forme paire d'innovation dynamique égale la somme sur cellules de bloc²×(1/a−1/b). | CONFIRMÉE | AJOUT | 3 |
| `dynamic_linear_innovation_form_eq_cell_sum` (l.851) | La forme linéaire d'innovation égale la somme cellule par cellule bloc × coefficient croisé. | CONFIRMÉE | AJOUT | 1 |
| `scale_cell_complete_recomposition` (l.862) | La forme quadratique à constante C(i+1,j+1) se recompose en terme d'innovation², croisé et local. | CONFIRMÉE | AJOUT | 1 |
| `thetaScaleFourMellinEnergy_eq_complete_recomposition` (l.904) | Pour U ≥ log 12, l'énergie d'échelle quatre = forme paire + forme linéaire + forme résiduelle locale. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 1 |
| `pair_indicator_rectangle_reduction` (l.921) | Pour j dans l'horizon, (m,n ∈ [j+1,i+1)) ⟺ max m n ≤ i et j < min(horizon, m, n). | CONFIRMÉE (domaine: j < horizon) | AJOUT | 1 |
| `sum_range_indicator_ge_eq_sum_Ico` (l.933) | Σ_{i<N} [q≤i] f i = Σ_{i∈[q,N)} f i. | CONFIRMÉE | AJOUT | 1 |
| `sum_range_indicator_lt_eq_sum_range` (l.946) | Σ_{j<M} [j<r] f j = Σ_{j<r} f j. | CONFIRMÉE (domaine: r ≤ M) | AJOUT | 1 |
| `dynamicPairKernel_eq_rectangular` (l.959) | Le noyau paire dynamique est une somme rectangulaire sur i∈[max m n, horizon) et j<min(...). | CONFIRMÉE | AJOUT | 1 |
| `dynamic_kernel_inner_telescoping` (l.1049) | Σ_{j<r}(1/scaleSubBreak j − 1/scaleSubBreak(j+1)) = 1/scaleSubBreak 0 − 1/scaleSubBreak r. | CONFIRMÉE | AJOUT | 1 |
| `dynamic_kernel_inner_telescoping_left_endpoint` (l.1070) | Même somme = 1/windowBreak i − 1/scaleSubBreak r pour U ≥ log 12. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 1 |
| `clamped_inverse_step_eq_potential_diff` (l.1078) | Pour w monotone, le pas d'inverse serré 1/w i − 1/max(w i, min T (w(i+1))) est une différence de potentiels en N. | CONFIRMÉE (domaine: w monotone, i+1 ≤ N ) | AJOUT | 1 |
| `clamped_inverse_telescoping` (l.1114) | Pour w monotone et q≤N, Σ_{i∈[q,N)} des pas d'inverse serrés = 1/w q − 1/max(w q, min T (w N)). | CONFIRMÉE (domaine: w monotone, q ≤ N ) | AJOUT | 1 |
| `windowBreak_clamped_inverse_telescoping` (l.1153) | Même télescopage pour w = windowBreak U. | CONFIRMÉE (domaine: q ≤ N) | AJOUT | 1 |
| `dynamic_pair_kernel_rectangular_second_telescoping` (l.1164) | Σ_{i∈[q,N)}(1/windowBreak i − 1/scaleSubBreak i r) = 1/windowBreak q − 1/max(windowBreak q, min(4p(r+1), windowBreak N)). | CONFIRMÉE (domaine: q ≤ N) | AJOUT | 1 |
| `dynamic_pair_kernel_rectangular_second_telescoping_horizon` (l.1176) | Même somme jusqu'à l'horizon canonique, avec borne supérieure 2e^U. | CONFIRMÉE (domaine: q ≤ horizon(U+log 2)) | AJOUT | 1 |
| `dynamicPairKernel_eq_closedForm` (l.1209) | Pour U ≥ log 12 et m,n sous l'horizon, le noyau paire dynamique égale sa forme close. | CONFIRMÉE (domaine: log 12 ≤ U, m,n < horizon) | AJOUT | 4 |
| `dynamicPairwiseInnovationForm_eq_closedForm` (l.1239) | Pour U ≥ log 12, la forme paire d'innovation égale sa forme close. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 1 |
| `thetaScaleFourMellinEnergy_eq_complete_closed_recomposition` (l.1249) | Pour U ≥ log 12, énergie d'échelle quatre = forme paire close + forme linéaire + forme résiduelle locale. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 1 |
| `p_succ_max_eq_max` (l.1259) | p(max m n + 1) = max(p(m+1), p(n+1)). | CONFIRMÉE | AJOUT | 1 |
| `p_succ_min_eq_min` (l.1272) | p(min m n + 1) = min(p(m+1), p(n+1)). | CONFIRMÉE | AJOUT | 1 |
| `inverse_clamped_difference_nonneg` (l.1285) | Pour a>0, 1/a − 1/max a c ≥ 0. | CONFIRMÉE (domaine: 0<a) | AJOUT | 1 |
| `inverse_clamped_difference_pos_lt_clamp` (l.1293) | Pour a>0, si 1/a − 1/max a c > 0 alors a < c. | CONFIRMÉE (domaine: différence strictement positive ) | AJOUT | 2 |
| `windowBreak_prime_le_of_lt_two` (l.1309) | Si windowBreak U q < 2e^U alors p(q+1) ≤ windowBreak U q. | CONFIRMÉE (domaine: windowBreak U q < 2e^U ) | AJOUT | 2 |
| `dynamicPairKernel_scale4_support` (l.1324) | Si le noyau paire dynamique est >0, max(p(m+1),p(n+1)) < 4·min(p(m+1),p(n+1)) (support d'échelle quatre). | CONFIRMÉE (domaine: U ≥ log 12, m,n sous l'horizon, noyau >0 ) | AJOUT | 1 |
| `dynamicPairKernelClosedForm_nonneg` (l.1367) | La forme close du noyau paire dynamique est ≥ 0. | CONFIRMÉE | AJOUT | 1 |
| `dynamicPairKernel_nonneg` (l.1374) | Pour U ≥ log 12 et m,n sous l'horizon, le noyau paire dynamique est ≥ 0. | CONFIRMÉE (domaine: log 12 ≤ U, m,n < horizon) | AJOUT | 1 |
| `dynamicPairKernel_eq_zero_of_not_scale4_support` (l.1382) | Hors du support d'échelle quatre, le noyau paire dynamique est nul. | CONFIRMÉE (domaine: U ≥ log 12, m,n sous l'horizon, négation de max<4·min ) | AJOUT | 1 |
| `dynamicPairwiseInnovationClosedForm_eq_scale4_supported` (l.1396) | Pour U ≥ log 12, la forme paire close égale sa forme restreinte au support d'échelle quatre. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 1 |
| `thetaScaleFourMellinEnergy_eq_complete_supported_recomposition` (l.1417) | Pour U ≥ log 12, énergie d'échelle quatre = forme paire supportée + linéaire + résiduelle locale. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 1 |
| `dynamicPairwiseInnovationScale4SupportedForm_eq_sum_grammar_pair_classes` (l.1474) | La forme paire supportée égale la somme sur les quatre classes de paires grammaticales (Transform6) de leurs contributions. | CONFIRMÉE | AJOUT | 1 |
| `dynamicLinearInnovationForm_eq_sum_grammar_pair_classes` (l.1497) | La forme linéaire d'innovation égale la somme sur les classes de paires grammaticales. | CONFIRMÉE | AJOUT | 1 |
| `dynamicLocalResidualForm_eq_sum_grammar_pair_classes` (l.1510) | La forme résiduelle locale égale la somme sur les classes de paires grammaticales. | CONFIRMÉE | AJOUT | 1 |
| `supportedCompleteScale4Form_eq_sum_grammar_pair_classes` (l.1534) | La forme complète supportée d'échelle quatre égale la somme sur les classes grammaticales. | CONFIRMÉE | AJOUT | 1 |
| `thetaScaleFourMellinEnergy_eq_complete_supported_grammar_partition` (l.1546) | Pour U ≥ log 12, l'énergie d'échelle quatre égale la somme sur les classes grammaticales de la contribution complète supportée. | CONFIRMÉE (domaine: log 12 ≤ U) | AJOUT | 0 |
| `scaleCellExplicitCorrection_eq_endpoint_form` (l.1556) | Pour j≤m, la correction explicite = Δphi − Δlog p − Δp. | CONFIRMÉE (domaine: j ≤ m) | AJOUT | 2 |
| `affine_plus_explicitCorrection_eq_local_residual` (l.1566) | Pour j≤m, 3t/4 + correction explicite = résidu local de cellule en t. | CONFIRMÉE (domaine: j ≤ m) | AJOUT | 2 |
| `thetaScaleFourCellConstant_eq_centered_constant` (l.1576) | Pour 1≤j≤m, la constante de cellule égale la constante centrée. | CONFIRMÉE (domaine: 1≤j≤m) | AJOUT | 2 |
| `scaleCellQuadraticForm_eq_centered_constant` (l.1583) | La forme quadratique de cellule prend la même valeur avec la constante de cellule et la constante centrée. | CONFIRMÉE (domaine: 1≤j≤m) | AJOUT | 0 |
| `thetaScaleFourDefectReal_eq_centered_cell_discrepancy` (l.1589) | Sur une cellule première, défaut d'échelle quatre = 3t/4 + constante centrée. | CONFIRMÉE (domaine: 1≤j≤m et t, t/4 dans leurs cellules premières) | AJOUT | 1 |
| `thetaScaleFourDefectReal_eq_innovation_block_plus_local_residual` (l.1598) | Sur une cellule première, défaut = bloc d'innovation + résidu local. | CONFIRMÉE (domaine: j≤i et t, t/4 dans leurs cellules premières) | AJOUT | 1 |
| `scaleCellLocalResidual_eq_affine_plus_explicitCorrection` (l.1639) | Pour j≤m, résidu local de cellule = 3t/4 + correction explicite. | CONFIRMÉE (domaine: j ≤ m) | AJOUT | 1 |
| `thetaScaleFourDefectReal_eq_dynamicInnovationBlock_add_localResidual` (l.1647) | Sur une cellule première, défaut = bloc d'innovation dynamique + résidu local de cellule (j+1,i+1). | CONFIRMÉE (domaine: j≤i et t, t/4 dans leurs cellules premières) | AJOUT | 0 |
| `scaleCellLocalResidual_mellin_energy_exact` (l.1662) | L'énergie de Mellin du résidu local sur [a,b] vaut 9/16(b−a)+3/2·corr·(log b−log a)+corr²(1/a−1/b). | CONFIRMÉE (domaine: j≤m, 0<a, 0<b) | AJOUT | 0 |
| `sum_Ico_aT_eq_prime_gap_sub_log_block` (l.1686) | Pour j≤m, Σ_{n∈[j,m)} aT n = p m − p j − Σ log p n. | CONFIRMÉE (domaine: j ≤ m) | AJOUT | 1 |
| `sum_Ico_log_succ_eq_sub_left_add_endpoint` (l.1706) | Pour j≤m, Σ_{[j+1,m+1)} log p n = Σ_{[j,m)} log p n + log p m − log p j. | CONFIRMÉE (domaine: j ≤ m) | AJOUT | 1 |
| `scaleCellCenteredConstant_eq_neg_prime_log_block` (l.1741) | Pour 1≤j≤m, la constante centrée vaut −Σ_{n∈[j+1,m+1)} log p n. | CONFIRMÉE (domaine: 1≤j≤m) | AJOUT | 0 |
| `scaleBlockPairEnergy_eq_weighted_innovation_pair_sum` (l.1764) | L'énergie de paire de blocs égale la double somme pondérée des produits d'innovations. | CONFIRMÉE | AJOUT | 0 |
| `scale_block_cross_term_eq_pair_sum` (l.1773) | Le produit des sommes d'innovation de bloc en x et y égale la double somme des produits d'innovations. | CONFIRMÉE | AJOUT | 2 |
| `scale_block_cross_term_class_partition` (l.1782) | Cette double somme se partitionne selon toute classification κ à valeurs finies. | CONFIRMÉE | AJOUT | 1 |
| `centered_pairwise_energy_scale_recurrence` (l.1800) | Si q = somme d'innovation de bloc + q_préc/2, alors q² = paire diagonale + q_préc²/4 + somme×q_préc. | CONFIRMÉE (domaine: q = S + q_préc/2 ) | AJOUT | 0 |
| `theta_scale_four_normalized_square_identity_v2` (l.1813) | Pour t≠0, (θerr t/t)² = (défaut/t)² + (2θerr(t/4)/t)²/4 + (défaut/t)(2θerr(t/4)/t). | CONFIRMÉE (domaine: t≠0) | AJOUT | 1 |
| `theta_scale_four_global_signed_cross_identity` (l.1830) | Pour U ≥ log 4, l'intégrale du croisé signé sur [e^U,2e^U] = énergie θ(U) − énergie d'échelle quatre − ¼ énergie θ(U−log 4). | CONFIRMÉE (domaine: log 4 ≤ U) | AJOUT | 0 |
| `scale_block_cross_term_reindexed_pair_sum` (l.1917) | Le produit des sommes d'innovation en x et x/4 est la double somme réindexée. | CONFIRMÉE | AJOUT | 1 |
| `scale_block_cross_term_reindexed_class_partition` (l.1925) | Cette double somme (x, x/4) se partitionne selon toute classification finie κ. | CONFIRMÉE | AJOUT | 1 |
| `innovationJ_pair_explicit_expansion` (l.1939) | Pour m,n≥2, le produit innovationJ m × innovationJ n s'écrit en lifts k et termes croisés de grammaire pour des transformations τ réalisées. [type tronqué] | CONFIRMÉE (domaine: 2≤m, 2≤n) | AJOUT | 1 |
| `scale_block_cross_term_reindexed_pairwise_explicit_exists` (l.1968) | Si tous les indices des deux blocs (x et x/4) sont ≥2, il existe un terme de paire explicite en lifts k et termes croisés de grammaire égal au produit d'innovations pour chaque (m,n). [type tronqué] | CONFIRMÉE (domaine: indices des blocs ≥ 2 ) | AJOUT | 0 |
| `scaleBlockInnovationSum_eq_cumulative_sub_boundary` (l.2010) | Pour x≥0, la somme d'innovation de bloc = fullATCumulative x − fullATCumulative(x/4) − bord, avec \|bord\| ≤ 1. | CONFIRMÉE (domaine: 0 ≤ x) | AJOUT | 1 |
| `scaleBlockInnovationProduct_eq_cumulative_endpoint_product` (l.2022) | Pour x≥0, le produit des sommes d'innovation en x et x/4 = produit des différences cumulatives moins bords, \|bords\| ≤ 1. | CONFIRMÉE (domaine: 0 ≤ x) | AJOUT | 1 |
| `scale_four_endpoint_cross_polarization` (l.2039) | 2(A−B)(B−C) = (A−C)² − (A−B)² − (B−C)². | CONFIRMÉE | AJOUT | 0 |
| `scale_four_endpoint_product_with_boundaries` (l.2045) | (A−B−b)(B−C−b') développé en produit + termes de bord. | CONFIRMÉE | AJOUT | 0 |
| `scale_four_endpoint_boundary_abs_bounds` (l.2055) | Si \|b\|,\|b'\| ≤ 1, \|b'(A−B)\| ≤ \|A−B\|, \|b(B−C)\| ≤ \|B−C\|, \|bb'\| ≤ 1. | CONFIRMÉE (domaine: \|bord\| ≤ 1 et \|bord précédent\| ≤ 1 ) | AJOUT | 0 |
| `boundary_linear_abs_le_quadratic` (l.2079) | Si \|b\| ≤ 1, \|b z\| ≤ (z²+1)/2. | CONFIRMÉE (domaine: \|b\| ≤ 1 ) | AJOUT | 1 |
| `gramWindowWeight_mul_boundary_linear_abs_le_quadratic` (l.2093) | Même borne pondérée par le poids de fenêtre de Gram. | CONFIRMÉE (domaine: \|b\| ≤ 1 ) | AJOUT | 1 |
| `normalized_weighted_boundary_linear_abs_le_half_square_add_half_mass` (l.2101) | Somme pondérée normalisée des \|b_j z_j\| ≤ ½ (somme pondérée des z²) + ½ (masse pondérée). | CONFIRMÉE (domaine: \|b_j\| ≤ 1 pour j<N ) | AJOUT | 2 |
| `boundary_linear_terms_absorbed_scale4` (l.2157) | Les termes de bord linéaires d'échelle quatre (R(j+1)−R(K4 j)) sont absorbés par ½ énergie + ½ masse. | CONFIRMÉE (domaine: \|bords précédents\| ≤ 1 ) | AJOUT | 0 |
| `boundary_linear_terms_absorbed_scale4_previous` (l.2180) | Idem pour les termes R(K4 j) − R(K16 j). | CONFIRMÉE (domaine: \|bords\| ≤ 1 ) | AJOUT | 0 |
| `normalized_weighted_boundary_product_abs_le_mass` (l.2203) | Somme pondérée normalisée des \|b_j b'_j\| ≤ masse pondérée normalisée. | CONFIRMÉE (domaine: \|b_j\| ≤ 1 et \|b'_j\| ≤ 1 ) | AJOUT | 0 |
| `scaleBlockInnovationProduct_eq_polarized_cumulative_with_boundaries` (l.2239) | Pour x≥0, produit d'innovations en x et x/4 = ½[(Δ16)²−(Δ4)²−(Δ4/16)²] − termes de bord. | CONFIRMÉE (domaine: 0 ≤ x) | AJOUT | 1 |
| `weighted_scale_four_endpoint_cross_polarization` (l.2258) | Polarisation pondérée : 2Σ w_j (A−B)(B−C) = Σ w(A−C)² − Σ w(A−B)² − Σ w(B−C)². | CONFIRMÉE | AJOUT | 2 |
| `VTkernel_cross_polarization` (l.2282) | Polarisation du noyau VT : 2Σ poids × produit des cumuls = VT(a−c) − VT(a−b) − VT(b−c). | CONFIRMÉE (domaine: X ≤ p(N+1) ) | AJOUT | 1 |
| `weighted_cross_term_VTkernel_identity` (l.2305) | Le terme croisé pondéré vaut ½[VT(a−c) − VT(a−b) − VT(b−c)]. | CONFIRMÉE (domaine: X ≤ p(N+1) ) | AJOUT | 1 |
| `weighted_cross_term_gramWindow_identity` (l.2323) | Le terme croisé pondéré sur fenêtre de Gram vaut ½ combinaison de noyaux VT à e^{U+log 2} moins à moitié. [type tronqué] | CONFIRMÉE | AJOUT | 1 |
| `m49_exp_neg_two_shift_eq` (l.2382) | exp(−2(U+log 2)) = ¼ exp(−2U). | CONFIRMÉE | AJOUT | 1 |
| `weighted_cross_term_gramWindow_identity_normalized` (l.2392) | Version normalisée de l'identité croisée de fenêtre de Gram (facteur ¼ e^{−2U}). [type tronqué] | CONFIRMÉE | AJOUT | 1 |
| `normalized_gramWindowWeight_sum_shift_le_exp_neg` (l.2420) | La masse normalisée des poids de Gram décalés est ≤ e^{−U}. | CONFIRMÉE | AJOUT | 1 |
| `normalized_gramWindowWeight_sum_shift_subexponential` (l.2444) | La masse normalisée des poids de Gram décalés est sous-exponentielle. | CONFIRMÉE | AJOUT | 0 |
| `scaleBlockPairEnergy_eq_VTkernel_sub_rest` (l.2454) | Pour mx≤N, l'énergie de paire de bloc = VT(innovationJ) − somme des termes d'énergie hors du carré [my,mx)². | CONFIRMÉE (domaine: mx ≤ N ) | AJOUT | 1 |
| `zero_reconstructed_scale_block_pair_energy_eq_VTkernel_sub_rest` (l.2464) | Même identité pour l'énergie de paire construite sur les suites reconstruites des zéros. | CONFIRMÉE (domaine: mx ≤ N ) | V48,V174 | 0 |
| `fullATCumulative_weighted_scale_four_endpoint_cross_polarization` (l.2474) | Polarisation pondérée appliquée à fullATCumulative aux points p(j+1), p(j+1)/4, p(j+1)/16. | CONFIRMÉE | AJOUT | 0 |
| `fullATCumulative_eq_R_zero_of_lt_first_jump` (l.2501) | Pour y < p 1, fullATCumulative y = R 0. | CONFIRMÉE (domaine: y < p 1 ) | AJOUT | 1 |
| `fullATCumulative_eq_R_of_prime_bracket` (l.2520) | Si p(k+1) ≤ y < p(k+2), fullATCumulative y = R(k+1). | CONFIRMÉE (domaine: 0≤y et y dans le crochet premier ) | AJOUT | 3 |
| `fullATCumulative_prime_div_four_eq_R_of_prime_bracket` (l.2556) | Si p(j+1)/4 est dans le crochet [p(k+1),p(k+2)), fullATCumulative(p(j+1)/4) = R(k+1). | CONFIRMÉE (domaine: p(j+1)/4 dans le crochet ) | AJOUT | 0 |
| `fullATCumulative_prime_div_sixteen_eq_R_of_prime_bracket` (l.2565) | Idem pour p(j+1)/16. | CONFIRMÉE (domaine: p(j+1)/16 dans le crochet ) | AJOUT | 0 |
| `fullATCumulative_reindexed_of_lt_prime` (l.2574) | Pour 0≤y<p(j+1), il existe K avec fullATCumulative y = R K et K=0 ou y dans le crochet de K. | CONFIRMÉE (domaine: 0≤y, y<p(j+1) ) | AJOUT | 2 |
| `fullATCumulative_prime_div_four_reindexed_with_bracket` (l.2612) | Il existe K avec fullATCumulative(p(j+1)/4) = R K et K=0 ou crochet premier de K. | CONFIRMÉE | AJOUT | 2 |
| `fullATCumulative_prime_div_sixteen_reindexed_with_bracket` (l.2628) | Même énoncé pour p(j+1)/16. | CONFIRMÉE | AJOUT | 2 |
| `fullATCumulative_prime_div_four_reindexed` (l.2644) | Il existe K avec fullATCumulative(p(j+1)/4) = R K. | CONFIRMÉE | AJOUT | 0 |
| `fullATCumulative_prime_div_sixteen_reindexed` (l.2651) | Il existe K avec fullATCumulative(p(j+1)/16) = R K. | CONFIRMÉE | AJOUT | 0 |
| `fullATCumulative_prime_div_four_reindexed_family` (l.2658) | Pour tout N, une famille K j réindexe simultanément tous les j<N (avec crochet). | CONFIRMÉE | AJOUT | 2 |
| `fullATCumulative_prime_div_sixteen_reindexed_family` (l.2673) | Idem pour p(j+1)/16. | CONFIRMÉE | AJOUT | 2 |
| `fullATCumulative_prime_div_four_weighted_square_sum_reindexed` (l.2688) | Pour tout U, il existe K tel que la somme pondérée des carrés (Δ à /4) égale la somme pondérée des (R(j+1)−R(K j))². | CONFIRMÉE | AJOUT | 0 |
| `fullATCumulative_prime_div_sixteen_weighted_square_sum_reindexed` (l.2708) | Même réindexation pour la somme pondérée des carrés à /16 (type tronqué, lu par analogie avec /4 : à vérifier). | CONFIRMÉE | AJOUT | 0 |
| `fullATCumulative_div_four_div_sixteen_weighted_square_sum_reindexed` (l.2728) | Pour tout U, il existe K4, K16 tels que la somme pondérée des carrés (Δ entre /4 et /16) égale la somme pondérée des (R(K4 j)−R(K16 j))². | CONFIRMÉE | AJOUT | 0 |
| `fullATCumulative_at_prime_eq_corrected_sub_RChebyshevCorrection` (l.2751) | Pour m≥1, fullATCumulative(p m) = correctedTAtPrime m − RChebyshevCorrection m. | CONFIRMÉE (domaine: 1 ≤ m) | AJOUT | 1 |
| `fullATCumulative_at_prime_eq_p_sub_chebyshev_sub_RChebyshevCorrection` (l.2759) | Pour m≥1, fullATCumulative(p m) = p m − θ(p m) − RChebyshevCorrection m. | CONFIRMÉE (domaine: 1 ≤ m) | V48 | 0 |
| `thetaScaleFourMellinEnergy_rate_one_source_bound` (l.2766) | Pour U ≥ log 4, l'énergie d'échelle quatre est ≤ 25/4·(log 4)²·e^U. | CONFIRMÉE (domaine: log 4 ≤ U) | AJOUT | 0 |
| `isNontrivialZetaZero_zetaReflect` (l.2805) | Si ρ est un zéro non trivial, son réfléchi zetaReflect ρ l'est aussi. | CONFIRMÉE SOUS CONDITION (ρ zéro non trivial) | V62,V63 | 1 |
| `round27_right_half_bound_from_left_half_bound` (l.2823) | Si tout zéro non trivial a re ≤ 1/2, alors tout zéro non trivial a re ≥ 1/2. | CONFIRMÉE (domaine: tous les zéros non triviaux ont re ≤ 1/2 (par réflexion) ) | V63,V126 | 1 |
| `round27_from_left_half_bound` (l.2832) | Si tout zéro non trivial a re ≤ 1/2, alors tout zéro non trivial a re = 1/2. | IMPLIQUE RH SOUS PRÉMISSE | V63,V126 | 3 |
| `riemann_hypothesis_from_left_half_bound` (l.2841) | Si tout zéro non trivial a re ≤ 1/2, alors RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V63,V126,O10 | 2 |
| `unconditional_theta_mellin_energy_subexponential_from_scale_four` (l.2850) | La sous-exponentialité de l'énergie d'échelle quatre entraîne celle de l'énergie de Mellin locale de θ. | CONFIRMÉE (domaine: énergie d'échelle quatre sous-exponentielle ) | AJOUT | 1 |
| `all_nontrivial_zeros_re_le_half_from_scale_four` (l.2855) | Si l'énergie d'échelle quatre est sous-exponentielle, tout zéro non trivial a re ≤ 1/2. | CONFIRMÉE (domaine: sous-exponentialité de l'énergie d'échelle quatre ) | V126 | 2 |
| `round27_all_nontrivial_zeros_on_critical_line_from_scale_four` (l.2861) | Si l'énergie d'échelle quatre est sous-exponentielle, tout zéro non trivial a re = 1/2. | IMPLIQUE RH SOUS PRÉMISSE | V126,O5 | 0 |
| `riemann_hypothesis_from_scale_four_subexponential` (l.2867) | Si l'énergie de Mellin d'échelle quatre est sous-exponentielle, alors RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V126 | 3 |

### `Round27ALocalZeroContext`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `mem_constellationHeightFiber` (l.61) | z est dans la fibre de hauteur γ de la source S ssi z est dans la tranche de hauteur T et Im z = γ. [terme hors maître] | CONFIRMÉE | V50 | 2 |
| `mem_constellationHeightFiber_canonical` (l.66) | Pour la source canonique, z est dans la fibre ssi z est un zéro non trivial, \|Im z\|<T, Im z=γ. | CONFIRMÉE | V50,V6,V7 | 4 |
| `constellationHeightFiber_subset` (l.72) | La fibre de hauteur est incluse dans la tranche de hauteur T. | CONFIRMÉE | V50 | 1 |
| `LocalZeroContext.height_lt` (l.90) | Le zéro d'un contexte local vérifie \|Im\|<T (champ de structure). | CONFIRMÉE | V7 | 2 |
| `LocalZeroContext.members_eq` (l.94) | Les membres du contexte local sont exactement la fibre de hauteur du zéro. | CONFIRMÉE | V50 | 6 |
| `LocalZeroContext.zero_mem_members` (l.108) | Le zéro du contexte appartient à ses membres. | CONFIRMÉE | V50 | 4 |
| `LocalZeroContext.mirror_height_lt` (l.114) | Le réfléchi-conjugué du zéro a \|Im\|<T. | CONFIRMÉE | V65 | 1 |
| `LocalZeroContext.mirror_mem_members` (l.119) | Le partenaire miroir appartient aux membres du même contexte local. | CONFIRMÉE | V62,V65,V74 | 4 |
| `LocalZeroContext.mem_members_height` (l.126) | Tout membre du contexte local a la hauteur du zéro. | CONFIRMÉE (domaine: z ∈ members ) | V50 | 0 |
| `LocalZeroContext.mem_members_isZero` (l.132) | Tout membre du contexte local est un zéro non trivial. | CONFIRMÉE (domaine: z ∈ members ) | V6 | 0 |
| `LocalZeroContext.members_subset` (l.137) | Les membres du contexte local sont dans la tranche de hauteur canonique T. | CONFIRMÉE | V50 | 0 |
| `MirrorPairDefect.mirror_eq` (l.164) | Le miroir du couple est le réfléchi-conjugué du zéro. | CONFIRMÉE | V65 | 13 |
| `MirrorPairDefect.radial_eq` (l.166) | Le défaut radial du couple est Re(zéro) − 1/2. | CONFIRMÉE | V158,V102 | 4 |
| `MirrorPairDefect.verticalGap_eq` (l.168) | L'écart vertical du couple est Im(miroir) − Im(zéro). [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `MirrorPairDefect.same_height` (l.185) | Le miroir et le zéro d'un couple ont la même hauteur. | CONFIRMÉE | V65,V162 | 2 |
| `MirrorPairDefect.verticalGap_eq_zero` (l.190) | L'écart vertical d'un couple est nul. | CONFIRMÉE | V66,V83 | 2 |
| `MirrorPairDefect.mirror_radial` (l.194) | Le miroir porte le défaut radial opposé : Re(miroir) − 1/2 = −radial. | CONFIRMÉE | V65,V158 | 1 |
| `MirrorPairDefect.distinct_iff_radial_ne_zero` (l.199) | Le miroir est distinct du zéro ssi le défaut radial est non nul. | CONFIRMÉE | V62,V77,V161 | 1 |
| `MirrorPairDefect.projections_never_identified` (l.213) | Si le défaut radial est non nul, écart vertical nul et défaut radial sont deux valeurs différentes. | CONFIRMÉE (domaine: radial ≠ 0 (couple distinct) ) | AJOUT | 0 |
| `MirrorPairDefect.two_le_localContext_card` (l.222) | Si radial ≠ 0 et le contexte local est celui du zéro du couple, il contient au moins deux membres à la même hauteur. | CONFIRMÉE (domaine: L.zero = D.zero et radial ≠ 0 ) | V162,V50 | 1 |
| `MirrorPairDefect.pair_mem_localContext` (l.242) | Le zéro et le miroir d'un couple appartiennent au contexte local du zéro. | CONFIRMÉE (domaine: L.zero = D.zero ) | V62,V74 | 0 |
| `canonicalMirrorPairDefect_exists` (l.251) | Pour tout zéro non trivial il existe un défaut de paire miroir de radial Re ρ − 1/2. | CONFIRMÉE | V65 | 0 |

### `Round27BSelectedPrimeBlock`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `SelectedPrimeBlock.start_ge_two` (l.55) | Le début d'un bloc premier sélectionné est ≥ 2. [terme hors maître] | CONFIRMÉE | AJOUT | 9 |
| `SelectedPrimeBlock.len_pos` (l.57) | Un bloc premier sélectionné a une longueur >0. | CONFIRMÉE | AJOUT | 1 |
| `SelectedPrimeBlock.start_lt_end` (l.66) | Début < fin pour un bloc sélectionné. | CONFIRMÉE | AJOUT | 14 |
| `SelectedPrimeBlock.end_ge_two` (l.70) | La fin d'un bloc sélectionné est ≥ 2. | CONFIRMÉE | AJOUT | 0 |
| `SelectedPrimeBlock.ratio_pos` (l.76) | Le rapport p(fin)/p(début) d'un bloc est >0. | CONFIRMÉE | AJOUT | 11 |
| `SelectedPrimeBlock.one_lt_ratio` (l.79) | Le rapport d'un bloc sélectionné est >1. | CONFIRMÉE | AJOUT | 6 |
| `SelectedPrimeBlock.log_ratio_pos` (l.87) | Le log du rapport d'un bloc est >0. | CONFIRMÉE | AJOUT | 1 |
| `SelectedPrimeBlock.rpow_pos` (l.89) | ratio^x > 0 pour tout réel x. | CONFIRMÉE | AJOUT | 0 |
| `SelectedPrimeBlock.rpow_injective` (l.91) | d ↦ ratio^d est injective (injectivité radiale du bloc). | CONFIRMÉE | V158 | 4 |
| `terminalPrimeBlock_pEnd` (l.113) | La fin du bloc terminal vaut 4. | CONFIRMÉE | AJOUT | 0 |
| `terminalPrimeBlock_ratio` (l.115) | Le rapport du bloc terminal est crossBlockRatio. | CONFIRMÉE | AJOUT | 0 |
| `blockHeightPhase_ne_zero` (l.124) | La phase de hauteur d'un bloc est non nulle. | CONFIRMÉE | V158 | 3 |
| `blockHeightPhase_terminal` (l.127) | La phase de hauteur du bloc terminal est crossHeightPhase. | CONFIRMÉE | AJOUT | 0 |
| `blockCrossTransport_zero_one` (l.136) | L'entrée (0,1) du transport croisé de bloc est le caractère de tour au rapport du bloc en ρ. [terme hors maître] | CONFIRMÉE | V16,V100 | 1 |
| `blockCrossTransport_one_zero` (l.140) | L'entrée (1,0) du transport est le caractère de tour au rapport en 1−conj ρ. | CONFIRMÉE | V63,V101 | 1 |
| `blockCrossTransport_terminal` (l.144) | Le transport du bloc terminal est TrueZeroReflectedCrossTransport. | CONFIRMÉE | AJOUT | 0 |
| `blockCrossOperator_terminal` (l.151) | L'opérateur croisé du bloc terminal est TrueZeroReflectedCrossOperator. | CONFIRMÉE | AJOUT | 1 |
| `towerCharacter_block_self` (l.160) | Le caractère de tour au rapport du bloc en ρ vaut ratio^(−(re ρ−1/2)) × phase de hauteur. | CONFIRMÉE | V16,V102 | 2 |
| `towerCharacter_block_reflected` (l.165) | Le caractère de tour en 1−conj ρ vaut ratio^(re ρ−1/2) × phase de hauteur. | CONFIRMÉE | V35,V80,V102 | 2 |
| `blockCrossOperator_eq_radial` (l.175) | L'opérateur croisé de bloc en ρ égale l'opérateur radial au défaut d = re ρ − 1/2. | CONFIRMÉE | V158 | 12 |
| `blockCrossOperator_zero_one` (l.189) | L'entrée (0,1) de l'opérateur croisé est ratio^(−(re ρ − 1/2)). | CONFIRMÉE | V102 | 5 |
| `blockCrossOperator_one_zero` (l.193) | L'entrée (1,0) est ratio^(re ρ − 1/2). | CONFIRMÉE | V102 | 3 |
| `blockCrossOperator_orientedFidelity_iff_critical` (l.202) | Les entrées (0,1) et (1,0) de l'opérateur croisé de tout bloc coïncident ssi re ρ = 1/2. | CONFIRMÉE | V140,V161 | 5 |
| `blockFidelity_iff_terminalFidelity` (l.225) | La fidélité orientée sur un bloc quelconque équivaut à celle du bloc terminal. | CONFIRMÉE | V140 | 0 |
| `canonicalCarrier_blockHolonomy_eq_transport_zero_one` (l.239) | L'holonomie du carrier canonique sur les deux ancrages du bloc égale l'entrée (0,1) du transport de bloc. [terme hors maître] | CONFIRMÉE | AJOUT | 2 |
| `canonicalCarrier_reflected_blockHolonomy_eq_transport_one_zero` (l.249) | L'holonomie du carrier du réfléchi-conjugué égale l'entrée (1,0). | CONFIRMÉE | AJOUT | 2 |
| `blockCrossTransport_eq_carrier_holonomies` (l.259) | Le transport de bloc est la matrice d'antidiagonale formée des deux holonomies du couple. | CONFIRMÉE | AJOUT | 0 |
| `SelectedPrimeBlock.rpow_neg_mul_self` (l.275) | ratio^(−d) × ratio^d = 1. | CONFIRMÉE | AJOUT | 2 |
| `blockRadialCrossOperator_apply_zero_one` (l.279) | L'entrée (0,1) de l'opérateur radial vaut ratio^(−d). | CONFIRMÉE | AJOUT | 0 |
| `blockRadialCrossOperator_apply_one_zero` (l.283) | L'entrée (1,0) de l'opérateur radial vaut ratio^d. | CONFIRMÉE | AJOUT | 0 |
| `blockRadialCrossOperator_sq_eq_one` (l.287) | L'opérateur radial de bloc est une involution pour tout d. | CONFIRMÉE | AJOUT | 1 |
| `blockRadialCrossOperator_conjTranspose` (l.300) | L'adjoint de l'opérateur radial est l'antidiagonale (ratio^d, ratio^(−d)). | CONFIRMÉE | AJOUT | 3 |
| `blockRadialCrossOperator_mul_conjTranspose` (l.308) | T T† = diag(ratio^(−2d), ratio^(2d)). | CONFIRMÉE | AJOUT | 1 |
| `blockRadialCrossOperator_conjTranspose_mul` (l.323) | T† T = diag(ratio^(2d), ratio^(−2d)) (ordre inversé). | CONFIRMÉE | AJOUT | 2 |
| `blockCrossOperator_offdiag_product_eq_one` (l.338) | Le produit des entrées (0,1) et (1,0) de l'opérateur croisé vaut 1. | CONFIRMÉE | AJOUT | 3 |
| `blockCrossOperator_sq_eq_one` (l.346) | L'opérateur croisé de bloc est une involution pour tout ρ. | CONFIRMÉE | AJOUT | 3 |
| `blockCrossOperator_conjTranspose` (l.352) | L'adjoint de l'opérateur croisé de bloc est l'antidiagonale (ratio^(re−1/2), ratio^(−(re−1/2))). | CONFIRMÉE | AJOUT | 2 |
| `blockCrossOperator_mul_conjTranspose` (l.359) | T T† = diag(ratio^(−2(re ρ−1/2)), ratio^(2(re ρ−1/2))) pour l'opérateur croisé de bloc. | CONFIRMÉE | AJOUT | 2 |
| `blockCrossOperator_conjTranspose_mul` (l.366) | T† T = diag(ratio^(2(re ρ−1/2)), ratio^(−2(re ρ−1/2))). | CONFIRMÉE | AJOUT | 2 |

### `Round27CDecoupledPartnership`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `GlobalZeroPrimePartnership.source_eq` (l.56) | La source d'un partenariat global zéro-premier est la source canonique des zéros. [terme hors maître] | CONFIRMÉE | V13 | 4 |
| `GlobalZeroPrimePartnership.reconstructs_prime_history` (l.67) | Le bloc de grammaire encodé depuis la source des zéros égale le bloc de grammaire premier canonique, pour toute fenêtre première. | CONFIRMÉE | V48,V49,V174 | 1 |
| `GlobalZeroPrimePartnership.MZ_eq_M` (l.73) | Le bloc encodé depuis la source égale le bloc obtenu par le canal des zéros (M^Z = M). | CONFIRMÉE | V48,V174,V159 | 1 |
| `GlobalZeroPrimePartnership.factors_through_zero_channel` (l.80) | Deux sources aux mêmes canaux de zéros produisent la même grammaire encodée. | CONFIRMÉE (domaine: canaux de zéros égaux ) | V48 | 0 |
| `DecoupledZeroPrimeCapture.zeroSide_eq` (l.115) | Le côté zéros d'une capture découplée est la grammaire de la fenêtre zéro de la source. [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `DecoupledZeroPrimeCapture.primeSide_eq` (l.117) | Le côté premier est l'encodage de la source sur la fenêtre première. | CONFIRMÉE | AJOUT | 2 |
| `decoupled_capture_indices_are_free` (l.134) | Pour tout quadruplet d'indices (zs,zl,ps,pl) il existe une capture canonique à ces indices : aucun théorème ne relie rang zéro et rang premier. | CONFIRMÉE | V60,O16 | 0 |
| `decoupled_primeSide_independent_of_zero_window` (l.144) | Le côté premier de la capture canonique ne dépend pas de la fenêtre zéro. | CONFIRMÉE | AJOUT | 1 |
| `decoupled_zeroSide_independent_of_prime_window` (l.153) | Le côté zéro ne dépend pas de la fenêtre première. | CONFIRMÉE | AJOUT | 0 |
| `DecoupledZeroPrimeCapture.primeSide_eq_M` (l.164) | Pour une capture à source canonique, le côté premier égale la grammaire première canonique sur la fenêtre première. | CONFIRMÉE (domaine: source canonique ) | V48,V174 | 7 |
| `DecoupledZeroPrimeCapture.primeSide_eq_MZ` (l.170) | Pour une capture à source canonique, le côté premier est aussi le bloc reconstruit M^Z. | CONFIRMÉE (domaine: source canonique ) | V48,V174 | 3 |
| `DecoupledZeroPrimeCapture.primeSide_positions` (l.178) | Positions du côté premier = p(primeStart+i). | CONFIRMÉE (domaine: source canonique ) | V13 | 2 |
| `DecoupledZeroPrimeCapture.primeSide_transitions` (l.184) | Transitions du côté premier = transformOf(p mod 6) aux rangs du bloc. | CONFIRMÉE (domaine: source canonique ) | V174 | 2 |
| `DecoupledZeroPrimeCapture.primeSide_entry` (l.191) | L'entrée du côté premier est p(primeStart) mod 6. | CONFIRMÉE (domaine: source canonique ) | V174 | 1 |
| `DecoupledZeroPrimeCapture.primeSide_exit` (l.196) | La sortie du côté premier est p(primeStart+primeLength) mod 6. | CONFIRMÉE (domaine: source canonique ) | V174 | 1 |
| `DecoupledZeroPrimeCapture.zeroSide_members` (l.201) | Les membres du côté zéro sont ceux de la fenêtre zéro. | CONFIRMÉE | AJOUT | 1 |

### `Round27DLocalizedPartnership`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `CanonicalLocalizedZeroPrimePartnership.capture_source` (l.69) | La capture d'un partenariat localisé porte la source du partenariat global. [terme hors maître] | CONFIRMÉE | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.capture_height` (l.71) | La capture porte la borne T du contexte. | CONFIRMÉE | AJOUT | 0 |
| `CanonicalLocalizedZeroPrimePartnership.defect_zero` (l.73) | Le défaut porte le zéro du contexte local. | CONFIRMÉE | AJOUT | 10 |
| `CanonicalLocalizedZeroPrimePartnership.block_start` (l.75) | Le premier ancrage du bloc est le début de la fenêtre première. | CONFIRMÉE | AJOUT | 9 |
| `CanonicalLocalizedZeroPrimePartnership.block_len` (l.77) | La longueur du bloc est celle de la fenêtre première. | CONFIRMÉE | AJOUT | 2 |
| `CanonicalLocalizedZeroPrimePartnership.directCarrier_eq` (l.79) | La branche directe est le carrier du membre. | CONFIRMÉE | AJOUT | 11 |
| `CanonicalLocalizedZeroPrimePartnership.reflectedCarrier_eq` (l.81) | La branche miroir est le carrier du miroir du même défaut. | CONFIRMÉE | V67 | 8 |
| `CanonicalLocalizedZeroPrimePartnership.directFiber_eq` (l.83) | La lecture directe est prise dans la fibre de hauteur du membre à sa position radiale. | CONFIRMÉE | V50 | 6 |
| `CanonicalLocalizedZeroPrimePartnership.reflectedFiber_eq` (l.86) | La lecture miroir est prise dans la même fibre de hauteur à la position réfléchie 1−re. | CONFIRMÉE | V50,V65 | 5 |
| `CanonicalLocalizedZeroPrimePartnership.source_canonical` (l.99) | La source de la capture du partenariat est la source canonique. | CONFIRMÉE | V13 | 16 |
| `CanonicalLocalizedZeroPrimePartnership.block_pEnd` (l.103) | Le second ancrage du bloc = primeStart + primeLength de la capture. | CONFIRMÉE | AJOUT | 3 |
| `CanonicalLocalizedZeroPrimePartnership.block_identity` (l.107) | Les deux ancrages du bloc sont exactement ceux de la fenêtre première de la capture. | CONFIRMÉE | AJOUT | 0 |
| `CanonicalLocalizedZeroPrimePartnership.zero_mem_context` (l.116) | Le zéro du partenariat appartient au contexte local. | CONFIRMÉE | V50 | 1 |
| `CanonicalLocalizedZeroPrimePartnership.mirror_mem_context` (l.119) | Le miroir du partenariat appartient au contexte local. | CONFIRMÉE | V62,V65,V74 | 1 |
| `CanonicalLocalizedZeroPrimePartnership.localizes_true_pair` (l.123) | Les carriers directs et miroir ont pour points de base le zéro et le miroir, tous deux membres du contexte local. | CONFIRMÉE | V62,V65,V74 | 0 |
| `CanonicalLocalizedZeroPrimePartnership.same_height` (l.135) | Le miroir et le zéro du partenariat ont la même hauteur. | CONFIRMÉE | V65 | 3 |
| `CanonicalLocalizedZeroPrimePartnership.opposite_radial` (l.139) | Le miroir porte le défaut radial opposé (re miroir − 1/2 = −radial). | CONFIRMÉE | V65,V158 | 1 |
| `CanonicalLocalizedZeroPrimePartnership.radial_eq` (l.142) | Le défaut radial du partenariat est re(zéro) − 1/2. | CONFIRMÉE | V158 | 15 |
| `CanonicalLocalizedZeroPrimePartnership.directCarrier_state_from_primeSide` (l.151) | L'état du carrier direct au rang i du bloc vaut 1 − 2·potentiel grammatical de la position du côté premier. | CONFIRMÉE | AJOUT | 0 |
| `CanonicalLocalizedZeroPrimePartnership.reflectedCarrier_state_from_primeSide` (l.159) | Le carrier miroir a le même état, projeté du même côté premier. | CONFIRMÉE | AJOUT | 0 |
| `CanonicalLocalizedZeroPrimePartnership.orientedIndicator_from_primeSide` (l.166) | L'indicateur orienté au rang i est décidé par la transition du côté premier. | CONFIRMÉE | AJOUT | 2 |
| `CanonicalLocalizedZeroPrimePartnership.directCarrier_signedTransition_from_primeSide` (l.174) | La transition signée du carrier direct est [τ15]−[τ51] de la transition du côté premier. | CONFIRMÉE | AJOUT | 0 |
| `CanonicalLocalizedZeroPrimePartnership.reflectedCarrier_signedTransition_eq_direct` (l.185) | Le carrier miroir porte la même transition signée que le direct. | CONFIRMÉE | AJOUT | 0 |
| `CanonicalLocalizedZeroPrimePartnership.block_entry_from_primeSide` (l.191) | L'état d'entrée du premier ancrage est l'entrée du côté premier. | CONFIRMÉE | AJOUT | 2 |
| `CanonicalLocalizedZeroPrimePartnership.block_exit_from_primeSide` (l.197) | L'état de sortie du second ancrage est la sortie du côté premier. | CONFIRMÉE | AJOUT | 2 |
| `CanonicalLocalizedZeroPrimePartnership.block_grammatical_return` (l.203) | Si entrée = sortie du côté premier, le produit Π(1−2·cross n) sur le bloc vaut 1. | CONFIRMÉE (domaine: entrée du côté premier = sortie ) | AJOUT | 2 |
| `CanonicalLocalizedZeroPrimePartnership.direct_holonomy` (l.223) | L'holonomie de la branche directe sur les ancrages est l'entrée (0,1) du transport. | CONFIRMÉE | AJOUT | 3 |
| `CanonicalLocalizedZeroPrimePartnership.reflected_holonomy` (l.230) | L'holonomie de la branche miroir sur les mêmes ancrages est l'entrée (1,0) du même transport. | CONFIRMÉE | AJOUT | 3 |
| `CanonicalLocalizedZeroPrimePartnership.transport_eq_branch_holonomies` (l.241) | Le transport est la matrice antidiagonale des deux holonomies. | CONFIRMÉE | AJOUT | 0 |
| `CanonicalLocalizedZeroPrimePartnership.operator_zero_one_eq_defect` (l.259) | L'entrée (0,1) de l'opérateur vaut ratio^(−radial). | CONFIRMÉE | V102,V158 | 2 |
| `CanonicalLocalizedZeroPrimePartnership.operator_one_zero_eq_defect` (l.265) | L'entrée (1,0) de l'opérateur vaut ratio^(radial). | CONFIRMÉE | V102,V158 | 1 |
| `CanonicalLocalizedZeroPrimePartnership.radial_defect_recovered_from_operator` (l.272) | Deux partenariats de même bloc et même entrée (0,1) ont le même défaut radial. | CONFIRMÉE SOUS CONDITION (Q.block = P.block et Q.operator 0 1 = P.operator 0 1) | V45,V46 | 2 |
| `CanonicalLocalizedZeroPrimePartnership.defect_two_manifestations` (l.285) | Si radial ≠ 0 : au moins deux membres dans le contexte, entrées (0,1)≠(1,0) de l'opérateur, écart vertical nul, radial ≠ écart vertical. | CONFIRMÉE SOUS CONDITION (défaut radial non nul (zéro hors ligne)) | V162,V165,V161 | 0 |
| `zero_height_lt_localizedCutoff` (l.317) | La hauteur d'un zéro non trivial est < localizedCutoff ρ. | CONFIRMÉE | V7 | 0 |
| `canonicalLocalizedPartnership_exists` (l.345) | Pour tout zéro non trivial, tout bloc et toute fenêtre zéro, un partenariat localisé existe. | CONFIRMÉE | AJOUT | 0 |

### `Round27EFiberedPartnershipTDD`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne (nb) |
|---|---|---|---|---|
| `CanonicalLocalizedZeroPrimePartnership.tdd_zeroCarrier` (l.54) | La tour tordue de la branche directe de P, à chaque rang n, égale le porteur vrai-zéro du membre de P. [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_individualMember` (l.59) | Le point de base de la fibre de hauteur du membre de P (à sa hauteur et sa partie réelle) est le membre lui-même. [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_reflectedZero` (l.63) | Le miroir de P est un zéro non trivial de zêta. | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | V62 | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_sameHeight` (l.65) | Le miroir et le membre de P ont la même partie imaginaire. | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | V65 | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_reflectedRadial` (l.67) | La partie réelle du miroir de P vaut 1 moins celle du membre. | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | V65 | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_grammarRigid` (l.73) | Le bloc de grammaire complète des premiers du bloc de P (piCount, p, gnat) est rigide (GrammarRigid). [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_grammarProjection` (l.77) | Sur le bloc de P, classe d'écart mod 6 de gnat = 0/2/4 équivaut à la paire de résidus mod 6 des premiers p_i, p_{i+1} (égaux / 5→1 / 1→5). | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | V174 | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_grammarComposition` (l.86) | Le produit sur le bloc de P des (1 − 2·cross n) vaut sigma(pStart)·sigma(pEnd) (télescopage du canal de changement d'état). [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 3 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_chi3` (l.91) | Le caractère chi3 du premier initial du bloc de P vaut le signe grammatical sigma(pStart). [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_inverseTransition` (l.95) | Les transitions du côté premier de P sont transformOf des résidus mod 6 consécutifs, et transformOf s t = tau11/15/51/55 équivaut à (s,t) = (1,1)/(1,5)/(5,1)/(5,5). [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_crossNonCoboundary` (l.106) | Le signal signé de la branche directe de P est l'indicateur tau15 moins tau51, et le canal croisé orienté (1,5),(5,1) n'est le cobord d'aucun potentiel psi. [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_fiberPair` (l.118) | Le membre de P et son symétrique (1 − partie réelle) donnent deux zéros non triviaux de la même fibre de hauteur, de même partie imaginaire. | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | V162 | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_tau15Fiber` (l.125) | Le premier composant de la fibre directe (resp. réfléchie) de P égale le vecteur de secteur tau15 au point de fibre du membre (resp. du symétrique). | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_tau51Fiber` (l.135) | Le second composant de la fibre directe (resp. réfléchie) de P égale le vecteur de secteur tau51 au point de fibre du membre (resp. du symétrique). | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_harmonicTower` (l.145) | Le coeur de transport du membre de P réalise le module de la tour harmonique du membre. [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_towerMultiplier` (l.149) | Les deux composantes de la fibre directe de P sont les sommes tsum des indicateurs tau15 / tau51 fois log p_n·p_n^(−1/2) fois le caractère de tour au point de fibre du membre. [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_grammarTowerSupport` (l.163) | Pour le premier initial du bloc de P, 1 + sigma^m ≠ 0 équivaut à sigma = 1 ou m pair, et le caractère de tour à la puissance 2k égale celui du carré à la puissance k. | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_commonTransport` (l.169) | Le transport de P a pour entrées les quotients du caractère de tour en p_end sur p_start, au membre (0,1) et au miroir (1,0). [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_commonHeightPhase` (l.183) | La phase de hauteur du bloc de P est la même au miroir et au membre, non nulle, et l'opérateur de P égale son inverse fois le transport. [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_primeChannel` (l.189) | Le canal premier se décompose (tau11 + tau55 + fibre croisée pour σ>1) et le côté premier de P est le bloc de M (piCount,p,gnat) et de M^Z (zerosPrime…) sur les ancrages du bloc de P. [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_meromorphic` (l.207) | Soit le membre de P est sur la ligne (re = 1/2), soit la continuation du canal premier a un ordre méromorphe −1 en l'un des deux points de fibre (membre ou symétrique). [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_radialDefect` (l.216) | L'opérateur de P est la matrice antidiagonale (0, ratio^(−défaut radial) ; ratio^(défaut radial), 0). [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_radialOperator` (l.222) | L'opérateur de P égale l'opérateur croisé radial du bloc de P au défaut radial de P. | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_reflectionReciprocity` (l.226) | Le produit des deux entrées croisées de l'opérateur de P vaut 1. | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 2 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_involution` (l.229) | L'opérateur de P au carré vaut l'identité. | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_adjoint` (l.233) | L'adjoint (conjugué transposé) de l'opérateur de P est l'antidiagonale (0, ratio^(défaut) ; ratio^(−défaut), 0). [terme hors maître] | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_ttStar` (l.239) | T·T† de l'opérateur de P vaut diag(ratio^(−2·défaut), ratio^(2·défaut)). | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `CanonicalLocalizedZeroPrimePartnership.tdd_tStarT` (l.247) | T†·T de l'opérateur de P vaut diag(ratio^(2·défaut), ratio^(−2·défaut)). | CONFIRMÉE (domaine: P partenariat localisé canonique en hauteur T) | AJOUT | 1 |
| `FiberedPartnershipTDD.zeroCarrierSurface` (l.269) | La tour tordue de la branche directe de P, à chaque rang n, égale le porteur vrai-zéro du membre de P. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.individualMemberSurface` (l.271) | Le point de base de la fibre de hauteur du membre de P (à sa hauteur et sa partie réelle) est le membre lui-même. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.reflectedZeroSurface` (l.275) | Le miroir de P est un zéro non trivial de zêta. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | V62 | 1 |
| `FiberedPartnershipTDD.sameHeightSurface` (l.277) | Le miroir et le membre de P ont la même partie imaginaire. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | V65 | 1 |
| `FiberedPartnershipTDD.reflectedRadialSurface` (l.279) | La partie réelle du miroir de P vaut 1 moins celle du membre. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | V65 | 1 |
| `FiberedPartnershipTDD.grammarRigidSurface` (l.282) | Le bloc de grammaire complète des premiers du bloc de P (piCount, p, gnat) est rigide (GrammarRigid). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.grammarProjectionSurface` (l.285) | Sur le bloc de P, classe d'écart mod 6 de gnat = 0/2/4 équivaut à la paire de résidus mod 6 des premiers p_i, p_{i+1} (égaux / 5→1 / 1→5). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | V174 | 1 |
| `FiberedPartnershipTDD.grammarCompositionSurface` (l.293) | Le produit sur le bloc de P des (1 − 2·cross n) vaut sigma(pStart)·sigma(pEnd) (télescopage du canal de changement d'état). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.grammarReturnSurface` (l.297) | Si l'entrée et l'état de sortie du côté premier de P coïncident, le produit des (1 − 2·cross n) sur le bloc vaut 1. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.chi3GrammarSurface` (l.301) | Le caractère chi3 du premier initial du bloc de P vaut le signe grammatical sigma(pStart). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.tau15Surface` (l.304) | L'indicateur grammatical tau15 sur le bloc de P vaut 1 exactement quand la transition du côté premier de P est tau15, sinon 0. [terme hors maître] | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.tau51Surface` (l.308) | L'indicateur grammatical tau51 sur le bloc de P vaut 1 exactement quand la transition du côté premier de P est tau51, sinon 0. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.inverseTransitionSurface` (l.313) | Les transitions du côté premier de P sont transformOf des résidus mod 6 consécutifs, et transformOf s t = tau11/15/51/55 équivaut à (s,t) = (1,1)/(1,5)/(5,1)/(5,5). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.crossNonCoboundarySurface` (l.323) | Le signal signé de la branche directe de P est l'indicateur tau15 moins tau51, et le canal croisé orienté (1,5),(5,1) n'est le cobord d'aucun potentiel psi. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.fiberPairSurface` (l.332) | Le membre de P et son symétrique (1 − partie réelle) donnent deux zéros non triviaux de la même fibre de hauteur, de même partie imaginaire. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | V162 | 1 |
| `FiberedPartnershipTDD.tau15FiberSurface` (l.338) | Le premier composant de la fibre directe (resp. réfléchie) de P égale le vecteur de secteur tau15 au point de fibre du membre (resp. du symétrique). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.tau51FiberSurface` (l.346) | Le second composant de la fibre directe (resp. réfléchie) de P égale le vecteur de secteur tau51 au point de fibre du membre (resp. du symétrique). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.harmonicTowerSurface` (l.355) | Le coeur de transport du membre de P réalise le module de la tour harmonique du membre. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.towerMultiplierSurface` (l.358) | Les deux composantes de la fibre directe de P sont les sommes tsum des indicateurs tau15 / tau51 fois log p_n·p_n^(−1/2) fois le caractère de tour au point de fibre du membre. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.grammarTowerSupportSurface` (l.370) | Pour le premier initial du bloc de P, 1 + sigma^m ≠ 0 équivaut à sigma = 1 ou m pair, et le caractère de tour à la puissance 2k égale celui du carré à la puissance k. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.trueZeroTransportSurface` (l.377) | Les deux entrées du transport de P sont les holonomies de bloc des branches directe et réfléchie entre pStart et pEnd. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.commonTransportSurface` (l.381) | Le transport de P a pour entrées les quotients du caractère de tour en p_end sur p_start, au membre (0,1) et au miroir (1,0). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.commonHeightPhaseSurface` (l.389) | La phase de hauteur du bloc de P est la même au miroir et au membre, non nulle, et l'opérateur de P égale son inverse fois le transport. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.primeChannelSurface` (l.396) | Le canal premier se décompose (tau11 + tau55 + fibre croisée pour σ>1) et le côté premier de P est le bloc de M (piCount,p,gnat) et de M^Z (zerosPrime…) sur les ancrages du bloc de P. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.meromorphicSurface` (l.410) | Soit le membre de P est sur la ligne (re = 1/2), soit la continuation du canal premier a un ordre méromorphe −1 en l'un des deux points de fibre (membre ou symétrique). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.radialDefectSurface` (l.419) | L'opérateur de P est la matrice antidiagonale (0, ratio^(−défaut radial) ; ratio^(défaut radial), 0). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.radialOperatorSurface` (l.423) | L'opérateur de P égale l'opérateur croisé radial du bloc de P au défaut radial de P. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.reflectionReciprocitySurface` (l.426) | Le produit des deux entrées croisées de l'opérateur de P vaut 1. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.involutionSurface` (l.428) | L'opérateur de P au carré vaut l'identité. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.adjointSurface` (l.431) | L'adjoint (conjugué transposé) de l'opérateur de P est l'antidiagonale (0, ratio^(défaut) ; ratio^(−défaut), 0). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.ttStarSurface` (l.435) | T·T† de l'opérateur de P vaut diag(ratio^(−2·défaut), ratio^(2·défaut)). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.tStarTSurface` (l.440) | T†·T de l'opérateur de P vaut diag(ratio^(2·défaut), ratio^(−2·défaut)). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | AJOUT | 1 |
| `FiberedPartnershipTDD.orientedFidelitySurface` (l.448) | Les deux entrées croisées de l'opérateur de P sont égales (fidélité orientée, champ 33). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDD (33 champs)) | V140 | 1 |
| `FiberedPartnershipTDDMinusFidelity.zeroCarrierSurface` (l.455) | La tour tordue de la branche directe de P, à chaque rang n, égale le porteur vrai-zéro du membre de P. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.individualMemberSurface` (l.456) | Le point de base de la fibre de hauteur du membre de P (à sa hauteur et sa partie réelle) est le membre lui-même. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.reflectedZeroSurface` (l.458) | Le miroir de P est un zéro non trivial de zêta. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | V62 | 1 |
| `FiberedPartnershipTDDMinusFidelity.sameHeightSurface` (l.459) | Le miroir et le membre de P ont la même partie imaginaire. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | V65 | 1 |
| `FiberedPartnershipTDDMinusFidelity.reflectedRadialSurface` (l.460) | La partie réelle du miroir de P vaut 1 moins celle du membre. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | V65 | 1 |
| `FiberedPartnershipTDDMinusFidelity.grammarRigidSurface` (l.461) | Le bloc de grammaire complète des premiers du bloc de P (piCount, p, gnat) est rigide (GrammarRigid). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.grammarProjectionSurface` (l.463) | Sur le bloc de P, classe d'écart mod 6 de gnat = 0/2/4 équivaut à la paire de résidus mod 6 des premiers p_i, p_{i+1} (égaux / 5→1 / 1→5). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | V174 | 1 |
| `FiberedPartnershipTDDMinusFidelity.grammarCompositionSurface` (l.470) | Le produit sur le bloc de P des (1 − 2·cross n) vaut sigma(pStart)·sigma(pEnd) (télescopage du canal de changement d'état). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.grammarReturnSurface` (l.473) | Si l'entrée et l'état de sortie du côté premier de P coïncident, le produit des (1 − 2·cross n) sur le bloc vaut 1. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.chi3GrammarSurface` (l.476) | Le caractère chi3 du premier initial du bloc de P vaut le signe grammatical sigma(pStart). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.tau15Surface` (l.477) | L'indicateur grammatical tau15 sur le bloc de P vaut 1 exactement quand la transition du côté premier de P est tau15, sinon 0. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.tau51Surface` (l.480) | L'indicateur grammatical tau51 sur le bloc de P vaut 1 exactement quand la transition du côté premier de P est tau51, sinon 0. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.inverseTransitionSurface` (l.483) | Les transitions du côté premier de P sont transformOf des résidus mod 6 consécutifs, et transformOf s t = tau11/15/51/55 équivaut à (s,t) = (1,1)/(1,5)/(5,1)/(5,5). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.crossNonCoboundarySurface` (l.491) | Le signal signé de la branche directe de P est l'indicateur tau15 moins tau51, et le canal croisé orienté (1,5),(5,1) n'est le cobord d'aucun potentiel psi. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.fiberPairSurface` (l.498) | Le membre de P et son symétrique (1 − partie réelle) donnent deux zéros non triviaux de la même fibre de hauteur, de même partie imaginaire. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | V162 | 1 |
| `FiberedPartnershipTDDMinusFidelity.tau15FiberSurface` (l.503) | Le premier composant de la fibre directe (resp. réfléchie) de P égale le vecteur de secteur tau15 au point de fibre du membre (resp. du symétrique). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.tau51FiberSurface` (l.510) | Le second composant de la fibre directe (resp. réfléchie) de P égale le vecteur de secteur tau51 au point de fibre du membre (resp. du symétrique). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.harmonicTowerSurface` (l.517) | Le coeur de transport du membre de P réalise le module de la tour harmonique du membre. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 2 |
| `FiberedPartnershipTDDMinusFidelity.towerMultiplierSurface` (l.519) | Les deux composantes de la fibre directe de P sont les sommes tsum des indicateurs tau15 / tau51 fois log p_n·p_n^(−1/2) fois le caractère de tour au point de fibre du membre. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.grammarTowerSupportSurface` (l.530) | Pour le premier initial du bloc de P, 1 + sigma^m ≠ 0 équivaut à sigma = 1 ou m pair, et le caractère de tour à la puissance 2k égale celui du carré à la puissance k. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.trueZeroTransportSurface` (l.534) | Les deux entrées du transport de P sont les holonomies de bloc des branches directe et réfléchie entre pStart et pEnd. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.commonTransportSurface` (l.537) | Le transport de P a pour entrées les quotients du caractère de tour en p_end sur p_start, au membre (0,1) et au miroir (1,0). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.commonHeightPhaseSurface` (l.544) | La phase de hauteur du bloc de P est la même au miroir et au membre, non nulle, et l'opérateur de P égale son inverse fois le transport. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.primeChannelSurface` (l.548) | Le canal premier se décompose (tau11 + tau55 + fibre croisée pour σ>1) et le côté premier de P est le bloc de M (piCount,p,gnat) et de M^Z (zerosPrime…) sur les ancrages du bloc de P. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.meromorphicSurface` (l.561) | Soit le membre de P est sur la ligne (re = 1/2), soit la continuation du canal premier a un ordre méromorphe −1 en l'un des deux points de fibre (membre ou symétrique). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.radialDefectSurface` (l.568) | L'opérateur de P est la matrice antidiagonale (0, ratio^(−défaut radial) ; ratio^(défaut radial), 0). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.radialOperatorSurface` (l.571) | L'opérateur de P égale l'opérateur croisé radial du bloc de P au défaut radial de P. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 2 |
| `FiberedPartnershipTDDMinusFidelity.reflectionReciprocitySurface` (l.572) | Le produit des deux entrées croisées de l'opérateur de P vaut 1. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.involutionSurface` (l.573) | L'opérateur de P au carré vaut l'identité. | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.adjointSurface` (l.574) | L'adjoint (conjugué transposé) de l'opérateur de P est l'antidiagonale (0, ratio^(défaut) ; ratio^(−défaut), 0). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.ttStarSurface` (l.577) | T·T† de l'opérateur de P vaut diag(ratio^(−2·défaut), ratio^(2·défaut)). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `FiberedPartnershipTDDMinusFidelity.tStarTSurface` (l.581) | T†·T de l'opérateur de P vaut diag(ratio^(2·défaut), ratio^(−2·défaut)). | CONFIRMÉE SOUS CONDITION (P satisfait la structure FiberedPartnershipTDDMinusFidelity (32 champs, sans le champ 33)) | AJOUT | 1 |
| `fiberedPartnershipTDDMinusFidelity_holds` (l.586) | Pour tout partenariat localisé canonique P, la structure FiberedPartnershipTDDMinusFidelity (32 champs non terminaux) est vraie, sans hypothèse. | CONFIRMÉE (domaine: P partenariat localisé canonique) | AJOUT | 6 |
| `FiberedPartnershipTDD.toMinusFidelity` (l.625) | La structure FiberedPartnershipTDD (33 champs) de P entraîne FiberedPartnershipTDDMinusFidelity de P. | CONFIRMÉE SOUS CONDITION (P satisfait FiberedPartnershipTDD) | AJOUT | 0 |
| `FiberedPartnershipTDD.zero_re_eq_half` (l.642) | Si P satisfait FiberedPartnershipTDD, la partie réelle de son membre vaut 1/2. | CONFIRMÉE SOUS CONDITION (P satisfait FiberedPartnershipTDD (dont le champ 33 : égalité des deux entrées croisées ⟺ criticité, field33_iff_critical)) | V140 | 1 |
| `riemannHypothesis_of_fiberedPartnershipTDD` (l.650) | Si, pour tout vrai zéro ρ, tout bloc premier B et tous zs zl, FiberedPartnershipTDD tient pour le partenariat canonique localisé, alors RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE | V140,I4 | 0 |
| `minusFidelity_carries_no_terminal_force` (l.663) | Pour tout vrai zéro ρ, bloc B, zs, zl, le TDD amputé (32 champs) tient pour le partenariat canonique localisé, sans hypothèse. | CONFIRMÉE (domaine: ρ vrai zéro) | AJOUT | 1 |
| `fidelity_is_strictly_necessary_for_partnership` (l.671) | (Le TDD amputé vaut pour tout partenariat canonique localisé → RiemannHypothesis) est équivalent à RiemannHypothesis. | ÉQUIVALENTE À RH | V140,O21 | 0 |
| `field33_iff_critical` (l.683) | Pour tout partenariat localisé canonique P, les deux entrées croisées de l'opérateur sont égales si et seulement si la partie réelle du membre vaut 1/2. | CONFIRMÉE (domaine: P partenariat localisé) | V140 | 5 |

## Correspondance avec RHV6Fresh

Seules les vérités dont le TYPE des deux côtés a été lu figurent ici ; « même vérité » = même contenu mathématique, formulation différente ; « analogue » = même mécanisme, objets différents. Les indices `RHV6=` non vérifiés notés par les relecteurs (« à rapprocher de … ») sont écartés faute de contrôle.

| théorème rh_gap_criterion | théorème RHV6Fresh (data/RHV6Fresh.jsonl) | nature | Vi |
|---|---|---|---|
| `reflect_conj_re_eq` | `RHV6Fresh.zetaReflect_re` | même vérité (partie réelle de la réflexion 1−conj z ; RHV6 : zetaReflect ρ, et `conj_zetaReflect` donne conj(zetaReflect ρ)=1−ρ) | V65,V35 |
| `reflect_conj_im_eq` | `RHV6Fresh.zetaReflect_im` | même vérité (la réflexion préserve la partie imaginaire) | V65 |
| `reflect_conj_eq_self_iff` | `RHV6Fresh.zetaReflect_eq_self_iff` | même vérité (la réflexion fixe ρ ssi re ρ = 1/2) | V161,V77 |
| `carrier_reflected_multiplicity` | `RHV6Fresh.zeta_mult_functionalReflect` | même vérité voisine (multiplicité conservée par la réflexion ; rh_gap : 1−conj ρ, RHV6 : zetaFunctionalReflect) | V63 |
| `nontrivialZeroResidueTerm_conjugateMate` | `RHV6Fresh.conjugate_term_eq_conj` | analogue (terme du conjugué = conjugué du terme ; termes différents : résidu à multiplicité rh_gap, q^ρ/ρ RHV6) | V101 |
| `norm_nontrivialZeroResidueTerm_eq` | `RHV6Fresh.zeroTerm_norm` | analogue (le module du terme d'un zéro porte q^{re ρ} : la position radiale entre dans l'amplitude ; objets différents) | V102 |
| `norm_rawZeroPrimeSignature` | `RHV6Fresh.zeroTerm_norm` | analogue (norme = coefficient × exp((re ρ − 1/2)·log P) ; objets différents) | V102 |
| `rawHermitian_reflect_eq_two_products_forces_critical` | `RHV6Fresh.energy_balance_two_primes_false` | analogue (deux égalités de normes en deux raccords distincts forcent l'égalité des positions radiales / la criticité ; formulations différentes) | V170 |
| `real_block_change_skeleton_alternates` | `RHV6Fresh.primeGapClass6_alternates` | même vérité (alternance 2/4 des écarts non nuls mod 6 ; rh_gap : écarts gnat(n+i), n≥2 ; RHV6 : premiers >3 par gapClass6) | V174 |
| `zeroReconstructed_change_skeleton_alternates` | `RHV6Fresh.primeGapClass6_alternates` | même vérité transportée au côté reconstruit depuis les zéros (par zeros_prime_gaps_eq_prime_gaps) ; RHV6 : expectedMinimumPrime_gapClass6_alternates | V174,V177 |
| `real_blocks_join_preserves_change_order` | `RHV6Fresh.gapClass6_alternates` | instance de la même alternance (frontière de bloc sans effet) | V174 |

Les 11 correspondances ont été contrôlées par script (les deux noms existent dans les jsonl). Non-correspondances notables : l'audit `RHV6Fresh` n'a pas d'homologue direct pour les théorèmes de Mellin/Dirichlet/coboundary/Chebyshev-exposant, de la fidélité orientée (`GrammarTowerZeroFidelityObject`) ni de la rigidité mod 6 par blocs ; `primitivePsiPart_smoothedZeroPrimitive` et `r10_global_transport` (ψ reconstruit) portent la vérité V48/V121 que RHV6 attribue à la base rhv3 (`psiRecoveredFromZeros_eq_psi`, absent de RHV6Fresh.jsonl).

## Théorèmes mentionnant `RiemannHypothesis` (76, champ `mentions_RH`)

Aucun n'est de type exactement `RiemannHypothesis` : pas de TERME RH FERMÉ dans le lot. `IMPLIQUE RH SOUS PRÉMISSE` = conclusion `RiemannHypothesis`, prémisse non déchargée (nommée en mots) ; `ÉQUIVALENTE À RH` = `↔` dont un côté est RH (ou tautologie RH ↔ RH signalée) ; statut `SOUS CONDITION` pour les sens « RH → objet » (RH est alors la prémisse nommée).

| théorème | statut exact | prémisse / lecture (en mots) |
|---|---|---|
| `riemann_hypothesis_from_R_and_innovation_window_subexponential` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (sous-exponentialité de l'énergie R en fenêtre et de l'énergie d'innovation) |
| `riemann_hypothesis_from_R_and_zero_reconstructed_innovation_window_subexponential` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (sous-exponentialité de R et de l'innovation reconstruite) |
| `riemann_hypothesis_from_prime_gap_exact_mellin_subexponential` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (sous-exponentialité de la somme exacte de Mellin sur les écarts premiers) ; docstring: non prouvée |
| `riemann_hypothesis_from_midpoint_majorant_subexponential` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (sous-exponentialité de la somme des majorants du point milieu sur les écarts premiers) |
| `riemann_hypothesis_of_annular_accumulation` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (accumulation annulaire d'échelle quatre pour tout zéro non trivial ; docstring dit ⟺ re ≤ 1/2 par zéro, donc non déchargée) |
| `riemannHypothesis_of_symmetric_budget` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (budget symétrique de régularité du canal premier : résidu échelonné sous 1 hors ligne) ; docstring: RIEMANN_HYPOTHESIS_PROVED=false |
| `riemannHypothesis_of_budget` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (budget de régularité à droite de la ligne + fait de bande NontrivialZeroInStrip) |
| `riemannHypothesis_of_budgetFamily` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (famille de budgets de régularité + fait de bande) |
| `riemannHypothesis_of_chebyshevFamily` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (pont exposant→borne de logDeriv pour tout θ>1/2, famille d'exposants de Chebyshev, fait de bande) |
| `trueZeroPrimePowerIntervalRealization_forces_rh` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (TrueZeroPrimePowerIntervalRealization A : porteur zéro réalisant holonomie première et module de tour) ; prémisse ⟺ RH par trueZeroPrimePowerIntervalRealization_iff_rh |
| `trueZeroPrimePowerIntervalRealization_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (caractérisation, docstring : DETECTOR_EQUIVALENCE, pas une réfutation) |
| `trueZeroLoopPowerBoundedCofinal_forces_rh` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (bornitude cofinale des puissances de boucle pour tout vrai zéro, M<N) |
| `trueZeroLoopPowerBounded_forces_rh` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (bornitude des puissances de boucle pour tout vrai zéro) |
| `trueZeroLoopPowerBounded_canonicalBlock_forces_rh` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (bornitude des puissances de boucle sur le bloc canonique) |
| `trueZeroLoopPowerBounded_of_rh` | CONFIRMÉE SOUS CONDITION | hypothèse RiemannHypothesis (sens RH → objet) |
| `trueZeroLoopPowerBounded_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (M<N) |
| `trueZeroRightHalfPlane_forces_rh` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (cible demi-plan droit pour tout vrai zéro) ; réciproque dans trueZeroRightHalfPlane_iff_riemannHypothesis |
| `riemannHypothesis_of_noRightZetaZero` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (aucun zéro à droite de la ligne) ; réciproque compilée |
| `noRightZetaZero_of_riemannHypothesis` | CONFIRMÉE SOUS CONDITION | hypothèse RiemannHypothesis (RH → NoRightZetaZero) |
| `noRightZetaZero_iff_riemannHypothesis` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (aucun zéro non trivial à droite de la ligne) |
| `primeChannelRegularityBudget_iff_riemannHypothesis` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (budget de régularité du canal premier) |
| `trueZeroRightHalfPlane_iff_riemannHypothesis` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (demi-plan droit pour tout vrai zéro) |
| `trueZeroPrimeChannelEnergyBounded_iff_riemannHypothesis` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (énergie du canal premier bornée pour tout vrai zéro) |
| `trueZeroTowerTransportBounded_iff_riemannHypothesis` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (transport de tour borné pour tout vrai zéro) |
| `trueZeroLoopPowerBounded_canonicalBlock_iff_riemannHypothesis` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (bornitude de boucle sur le bloc canonique) |
| `primeGrammarChannelAnalyticRightOfHalf_iff_riemannHypothesis` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (analyticité du canal grammatical premier à droite de 1/2) |
| `riemannHypothesis_of_chebyshevFamily_unconditionalStrip` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (famille d'exposants de Chebyshev donnant la borne de log-dérivée) ; fait de bande déchargé |
| `riemannHypothesis_of_budget_unconditionalStrip` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (budget de régularité du canal premier) ; sans prémisse de bande |
| `riemannHypothesis_of_idealTerminalObject` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (objet terminal idéal = famille d'exposants de Chebyshev + pont) ; docstring: une seule prémisse |
| `idealTerminalObject_forces_rh` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (objet terminal idéal) |
| `rh_is_only_conditional_here` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (objet terminal idéal, non habité) ; docstring: sans contenu mathématique nouveau |
| `riemannHypothesis_of_chebyshevFamily_only` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (famille d'exposants de Chebyshev) |
| `uniformCarrierBound_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (borne uniforme du carrier sur tous les vrais zéros) |
| `uniformCarrierBound_forces_rh` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (borne uniforme du carrier sur tous les vrais zéros) |
| `riemannHypothesis_of_primeHeightSquareBridge` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (existence d'une fonction W de la hauteur vérifiant l'identité ‖W(Im ρ)‖² = (11/5)^(re ρ−1/2)−1 sur tout zéro) |
| `riemannHypothesis_of_primeHeightSquareBridge_reflection` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (idem, route indépendante par réflexion) |
| `primeHeightSquareBridge_zero_of_rh` | CONFIRMÉE SOUS CONDITION | hypothèse RiemannHypothesis (RH → objet habité par 0) |
| `primeHeightSquareBridge_zero_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (pont hauteur-carré réalisé par la fonction nulle) |
| `all_trueZero_cross_operators_normal_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (côté gauche : *-normalité pour tout zéro non trivial) ; docstring: reformulation exacte de RH |
| `all_trueZero_cross_operators_eq_swap_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (côté gauche : opérateur = swap pour tout zéro) |
| `riemannHypothesis_of_primeHeightCrossClosureObject` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (objet de clôture : un certificat par vrai zéro, dont l'égalité orientée des entrées) |
| `riemannHypothesis_of_primeHeightCrossClosureObject_via_swap` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (objet de clôture) |
| `primeHeightCrossClosureObject_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (prémisse d'objet terminal ↔ RH) |
| `riemannHypothesis_of_orientedBalance` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (égalité des entrées croisées pour tout zéro non trivial ; ⟺ RH par orientedFidelity_at_rho_iff_critical) |
| `riemannHypothesis_of_grammarTowerZeroFidelityObject` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (objet de fidélité grammaire-tour-zéro, dont l'égalité orientée pour tout zéro) ; docstring dit « aucune prémisse externe » : le type porte l'objet comme hypothèse (docstring ≠ type) |
| `riemannHypothesis_of_grammarTowerZeroFidelityObject_via_swap` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (objet de fidélité) |
| `riemannHypothesis_of_orientedFidelity_alone` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (égalité orientée des entrées croisées pour tout zéro) |
| `fidelity_is_strictly_necessary` | CONFIRMÉE | type mentionne RiemannHypothesis mais est une tautologie RH↔RH sous l'objet amputé (habité) ; ne ferme rien ; nom plus fort que le type (docstring : champ terminal strictement nécessaire) |
| `rh_of_commonFactorWeld_everywhere` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (existence de la soudure à facteur commun en chaque zéro non trivial, F51 à pôle partout ; la docstring dit purement conditionnelle) |
| `core_alone_cannot_close` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (côté gauche = RH précédé d'un ∀ sur un type habité) ; sonde de retrait : fermer RH depuis le core seul = prouver RH |
| `sectorContinuation_pointwise_not_a_lock` | ÉQUIVALENTE À RH | type P → (RH ↔ RH) ; tautologie, aucune information sur RH ; la prémisse P est prouvée vraie par le théorème précédent |
| `commonFactorWeld_everywhere_is_rh` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (soudure à facteur commun en tout zéro non trivial) ; nom « is_rh » suggère l'équivalence, le type n'est qu'une implication ; même type que rh_of_commonFactorWeld_everywhere |
| `rh_of_orientedFidelitySurface` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (surface de fidélité orientée, prouvée ⟺ RH ; donc ne ferme rien) |
| `orientedFidelitySurface_of_rh` | CONFIRMÉE SOUS CONDITION | RH est prémisse, non conclusion |
| `orientedFidelitySurface_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (prémisse OrientedFidelitySurface) |
| `re_eq_half_of_rh` | CONFIRMÉE SOUS CONDITION | hypothèse RH (prémisse), conclusion re=1/2 par zéro |
| `rh_of_h1` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (H1Determinant, prouvée ⟺ RH) |
| `h1Determinant_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (prémisse H1Determinant : déterminant du croisement réfléchi) |
| `rh_of_h2` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (H2, prouvée ⟺ RH) ; docstring vide |
| `h2_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (prémisse H2 : facteur de réflexion indépendant de la base) |
| `rh_of_h5` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (H5 rang un, prouvée ⟺ RH) ; docstring vide |
| `h5_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (prémisse H5 : rang un de la Gram à deux bases) |
| `rh_of_h3` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (H3 compatibilité de changement, prouvée ⟺ RH) ; docstring vide |
| `h3_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (prémisse H3) |
| `rh_of_h4` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (H4 réalisation de phase, prouvée ⟺ RH) ; docstring vide |
| `h4_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (prémisse H4) |
| `rh_of_h6` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (H6 annulation du second moment, prouvée ⟺ RH) ; docstring vide |
| `h6_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (prémisse H6) |
| `sixWay_matrix_is_one_reformulation` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (conjonction de sept équivalences) |
| `canonicalFiberedPartnershipProvenance_no_terminal_strength` | CONFIRMÉE | type = tautologie RH ↔ RH sous prémisse CanonicalFiberedPartnershipProvenance (vraie, canonicalFiberedPartnershipProvenance_holds) ; ne donne pas RH ; le nom promet « pas de force terminale » que le type n'énonce pas plus qu'une tautologie |
| `canonicalFiberedPartnershipOrientedCoherence_iff_rh` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH (cohérence orientée du partenariat fibré canonique, pour tout zéro) |
| `riemann_hypothesis_from_thetaMellin_subexponential` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (sous-exponentialité de thetaMellinLocalEnergy ; docstring: théorème conditionnel, prémisse non prouvée) |
| `riemann_hypothesis_from_left_half_bound` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (tout zéro non trivial est de partie réelle ≤ 1/2, c'est-à-dire aucun zéro de côté strictement droit) |
| `riemann_hypothesis_from_scale_four_subexponential` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE (sous-exponentialité de thetaScaleFourMellinEnergy) |
| `riemannHypothesis_of_fiberedPartnershipTDD` | IMPLIQUE RH SOUS PRÉMISSE | IMPLIQUE RH SOUS PRÉMISSE ; prémisse = le TDD à 33 champs vaut pour le partenariat localisé canonique de chaque vrai zéro sur tout bloc ; champ 33 ⟺ criticité (field33_iff_critical) ; docstring dit « aucune prémisse externe » mais le type contient cette hypothèse universelle |
| `fidelity_is_strictly_necessary_for_partnership` | ÉQUIVALENTE À RH | ÉQUIVALENTE À RH ; côté gauche = « TDD amputé pour tout partenariat ⟹ RH », équivalent à RH nue (le champ 33 est nécessaire) |

### Conclusions « tout zéro non trivial a re = 1/2 » (RH déroulé, `mentions_RH` = 0)

Ces théorèmes ne portent pas le terme `RiemannHypothesis` mais concluent ou équivalent à son énoncé déroulé ; même règle de statut.

| théorème | statut | prémisse / lecture |
|---|---|---|
| `offline_grammatical_defect_is_exactly_rh` | ÉQUIVALENTE À RH | condition: ¬D(F p gnat) ; côté droit = RH déroulé (pas le terme RiemannHypothesis) |
| `lock_two_grammatical_route_closed_negatively` | ÉQUIVALENTE À RH | condition: ¬D(F p gnat) ; côté droit = RH déroulé |
| `all_reflectedPairRatioScaleInvariant_gives_critical_line` | IMPLIQUE RH SOUS PRÉMISSE | conclusion = RH déroulé (pas le terme RiemannHypothesis) ; prémisse: invariance d'échelle du rapport pour tout zéro |
| `all_nontrivial_zeros_re_le_half_of_annular_accumulation` | IMPLIQUE RH SOUS PRÉMISSE | conclusion = côté bas de RH déroulé (re≤1/2) ; prémisse: accumulation annulaire pour tout zéro ; docstring vide |
| `round27_all_zeros_on_critical_line_of_annular_accumulation` | IMPLIQUE RH SOUS PRÉMISSE | conclusion = RH déroulé (re=1/2 pour tout zéro, pas le terme RiemannHypothesis) ; prémisse: accumulation annulaire pour tout zéro ; docstring vide |
| `independent_passage_law_scheme_gives_global_critical_line` | IMPLIQUE RH SOUS PRÉMISSE | conclusion = RH déroulé (pas le terme RiemannHypothesis) ; prémisse: loi de rigidité de passage indépendante pour toute fenêtre K=1 de toute hauteur |
| `reflected_change_family_compatibility_is_target_strength` | ÉQUIVALENTE À RH | RH: ÉQUIVALENTE À RH (côté droit = prédicat projet RhGap.RH, mentions_RH=0) ; via reflectedChangeFamilyCompatibility_iff_RH |
| `bf_reconstructed_grammar_defect_is_target_strength` | ÉQUIVALENTE À RH | condition: ¬D(G p gnat) ; côté droit = RH déroulé |
| `bf_oneStepReflectedGrammarCompatibility_iff_global_critical_line` | ÉQUIVALENTE À RH | RH: ÉQUIVALENTE À RH déroulé (pas le terme RiemannHypothesis) |
| `sound_complete_member_detector_iff_critical_line` | ÉQUIVALENTE À RH | condition: P correcte (vraie sur la ligne) et détectrice (fausse hors ligne) ; côté droit = RH déroulé |
| `global_critical_line_of_sound_complete_detector` | IMPLIQUE RH SOUS PRÉMISSE | conclusion = RH déroulé ; prémisses: P correcte, P détectrice, P pour tout zéro |
| `cross_not_coboundary` | RÉFUTATION COMPILÉE | réfute la route « canal croisé = cobord orienté » (piste du dépôt ; ni maître Vi/Oi) |
| `no_symmetry_package_law_forces_critical_line` | RÉFUTATION COMPILÉE | conclusion False ; réfute l'espoir d'une loi de symétrie seule (piste, non nommée par le maître ; V125 : aucune loi posée ne remplace l'isolement) |
| `chebyshevHalf_forces_critical_line` | IMPLIQUE RH SOUS PRÉMISSE | conclusion = RH déroulé sur les zéros (pas le terme RiemannHypothesis) ; prémisse: exposant de Chebyshev 1/2 et pont vers la borne de logDeriv |
| `trueZeroPrimePowerIntervalRealization_asset_independent` | ÉQUIVALENTE À RH | équivalence entre deux prémisses, chacune ⟺ RH par trueZeroPrimePowerIntervalRealization_iff_rh |
| `involution_alone_does_not_force_zero_defect` | RÉFUTATION COMPILÉE | réfute la voie « involution seule ⟹ RH » (docstring INVOLUTION_ALONE_FORCES_RH=false) ; pas un énoncé du maître |
| `h1Determinant_iff_h1Ratio` | ÉQUIVALENTE À RH | H1Determinant ⟺ RH par h1Determinant_iff_rh, donc H1Ratio aussi ; docstring vide |
| `h5_iff_h1` | ÉQUIVALENTE À RH | via h1Determinant_iff_rh, H5 ⟺ RH |
| `changeFamilyCompatibility_is_target_strength` | ÉQUIVALENTE À RH | RH: ÉQUIVALENTE À RH au sens de la définition RhGap.RH du projet (non le terme RiemannHypothesis de Mathlib) ; mentions_RH=0 |
| `centralPivotWeightTransport_two_is_target_strength` | IMPLIQUE RH SOUS PRÉMISSE | conclusion = RH déroulé (pas le terme RiemannHypothesis) ; prémisse: transport de poids central en 2 |
| `centralPivotResidualZeroBlind_iff_defect_zero_blind` | ÉQUIVALENTE À RH | équivalence de deux prémisses ; l'implication vers RH est dans centralPivotResidualZeroBlind_is_target_strength (pas ↔ RH établie) |
| `centralPivotResidualZeroBlind_is_target_strength` | IMPLIQUE RH SOUS PRÉMISSE | conclusion = RH déroulé ; prémisse: résidu aveugle au zéro (docstring : de force cible) |
| `round27_from_left_half_bound` | IMPLIQUE RH SOUS PRÉMISSE | conclusion = RH déroulé (pas le terme RiemannHypothesis) ; prémisse: aucun zéro de côté droit strict (re ≤ 1/2 pour tout zéro) |
| `round27_all_nontrivial_zeros_on_critical_line_from_scale_four` | IMPLIQUE RH SOUS PRÉMISSE | conclusion = RH déroulé ; prémisse: sous-exponentialité de l'énergie de Mellin d'échelle quatre |

## 1. Table vérité → théorèmes

Rattachements prudents ; certains relecteurs ont signalé des rattachements « lâches » (V158, V161, V162, V167, V172 sur les surfaces Tour/réflexion). Le statut affiché est le plus fort atteint (CONFIRMÉE > SOUS CONDITION > autres). Listes tronquées à 10 noms + nombre d'autres.

| Vi | nb | statut le plus fort | théorèmes |
|---|---|---|---|
| I4 | 4 | ÉQUIV. RH | `core_alone_cannot_close`, `commonFactorWeld_everywhere_is_rh`, `sixWay_matrix_is_one_reformulation`, `riemannHypothesis_of_fiberedPartnershipTDD` |
| I12 | 3 | CONFIRMÉE | `no_symmetry_package_law_forces_critical_line`, `sectorContinuation_pointwise_is_vacuous`, `sectorContinuation_pointwise_not_a_lock` |
| I13 | 4 | SOUS CONDITION | `edgeCurvature_eq_one_forces_critical`, `centralPivotWeightTransport_forces_edgeCurvature_one`, `centralPivotWeightTransport_two_is_target_strength`, `centralPivotResidualZeroBlind_is_target_strength` |
| O5 | 20 | CONFIRMÉE | `all_reflectedPairRatioScaleInvariant_gives_critical_line`, `all_nontrivial_zeros_re_le_half_of_annular_accumulation`, `round27_all_zeros_on_critical_line_of_annular_accumulation`, `independent_passage_law_scheme_forces_bounded_critical_line`, `independent_passage_law_scheme_gives_global_critical_line`, `independent_passage_law_scheme_excludes_offline`, `chebyshevHalf_forces_critical_line`, `riemannHypothesis_of_symmetric_budget`, `riemannHypothesis_of_budget`, `riemannHypothesis_of_budgetFamily` et 10 autres |
| O6 | 7 | SOUS CONDITION | `smoothedZeroPrimitive_eq_left_add_right_add_rest`, `smoothedZeroPrimitive_eq_sum_of_gt_one`, `psiRecoveredFromZeros_eq_left_add_right_add_rest`, `zerosWeightedCount_eq_left_add_right_add_rest`, `zerosPrimeCountReal_eq_left_add_right_add_rest`, `chebyshev_theta_eq_left_add_right_add_rest`, `chebyshev_theta_at_prime_eq_left_add_right_add_rest` |
| O10 | 24 | CONFIRMÉE | `offline_grammatical_defect_is_exactly_rh`, `passageProgressionTransfer_iff_critical_line`, `r11_is_exactly_local_critical_line`, `reflected_change_family_compatibility_is_target_strength`, `bf_oneStepReflectedGrammarCompatibility_iff_global_critical_line`, `sound_complete_member_detector_iff_critical_line`, `global_critical_line_of_sound_complete_detector`, `trueZeroPrimePowerIntervalRealization_iff_rh`, `all_trueZero_cross_operators_normal_iff_rh`, `all_trueZero_cross_operators_eq_swap_iff_rh` et 14 autres |
| O16 | 1 | CONFIRMÉE | `decoupled_capture_indices_are_free` |
| O17 | 1 | SOUS CONDITION | `offline_R1_R10_local_snapshot` |
| O19 | 3 | CONFIRMÉE | `independent_passage_law_scheme_forces_bounded_critical_line`, `independent_passage_law_scheme_gives_global_critical_line`, `independent_passage_law_scheme_excludes_offline` |
| O21 | 2 | CONFIRMÉE | `fidelity_is_strictly_necessary`, `fidelity_is_strictly_necessary_for_partnership` |
| V6 | 5 | CONFIRMÉE | `rightHalfPositiveZeros_finite`, `rightHalf_zero_nontrivial (privé)`, `re_le_neg_two_of_isTrivialZetaZero`, `mem_constellationHeightFiber_canonical`, `LocalZeroContext.mem_members_isZero` |
| V7 | 15 | CONFIRMÉE | `mem_orderedPositiveRepresentatives`, `mem_orderedPositiveRepresentatives_iff_lt`, `reflectedPoleProduct_last_factor_neg`, `rightHalf_zero_nontrivial (privé)`, `zetaZero_re_lt_one`, `re_pos_of_nontrivial_zeta_zero`, `nontrivialZeroInStrip_holds`, `interfaceBand_iff`, `interfaceBand_of_trueZero`, `interfaceBand_canonicalBlock_of_trueZero` et 5 autres |
| V8 | 14 | CONFIRMÉE | `zeroOrderKey_injective`, `instIsTransSubtypeComplexIsNontrivialZetaZeroZeroLe`, `instAntisymmSubtypeComplexIsNontrivialZetaZeroZeroLe`, `instTotalSubtypeComplexIsNontrivialZetaZeroZeroLe`, `mem_orderedPositiveRepresentatives`, `mem_orderedPositiveRepresentatives_iff_lt`, `orderedPositiveRepresentatives_pairwise_lt`, `orderedPositiveRepresentatives_pairwise_lt_human`, `orderedPositiveRepresentatives_nodup`, `orderedPositiveRepresentatives_toFinset` et 4 autres |
| V10 | 1 | CONFIRMÉE | `uniformTowerBoundAt_iff_half_le_re` |
| V12 | 1 | CONFIRMÉE | `rightHalfPositiveZero_order_pos` |
| V13 | 20 | CONFIRMÉE | `one_le_gnat`, `gnat_ne_zero`, `gnat_pos`, `thetaErrorReal_eq_sub_chebyshev_on_gap`, `p_pos_real`, `p_lt_p_succ_real`, `realOrderedBlock_occurrences_prime`, `realOrderedBlock_order_strictMono`, `primeCounting'_p`, `prime_cast_pos (privé)` et 10 autres |
| V15 | 1 | CONFIRMÉE | `fiberedCanonicalZeroPrimePartnership_exists` |
| V16 | 10 | CONFIRMÉE | `im_reflectedPoleProduct`, `hasDerivAt_towerMode`, `towerMode_eq_normalized_zeroRow`, `towerCharacter_pow`, `towerCharacter_eq_modulus_mul_phase`, `twistedTowerCharacter_modulus_phase`, `norm_floorTowerPrimitive`, `floorTowerPrimitive_eq_modulus_mul_phase`, `blockCrossTransport_zero_one`, `towerCharacter_block_self` |
| V20 | 1 | CONFIRMÉE | `abs_deriv_towerMode_at_contact` |
| V23 | 1 | CONFIRMÉE | `contact_succ` |
| V34 | 1 | CONFIRMÉE | `oriented_lift_inversion_acts_on_grammar_only` |
| V35 | 18 | CONFIRMÉE | `reflect_conj_im_eq`, `reflect_conj_re_eq`, `contactRatio_reflect_mul`, `zeroRow_contactRatio_reflect_mul`, `towerCharacter_reflected_eq`, `floorTowerPrimitive_reflect_ratio`, `floorTowerPrimitive_reflect`, `orientedTau_trailingCoeff_eq`, `residue_orientedTau15_eq_tau51`, `primeCell_towerCharacter_reflected` et 8 autres |
| V45 | 12 | CONFIRMÉE | `abs_deriv_towerMode_at_contact`, `contact_slope_ratio_eq_contactRatio`, `contactRatio_eq_one_iff`, `contact_slope_ratio_towerMode`, `contact_slope_ratio_floor_independent`, `contact_slope_ratio_eq_one_iff_critical_line`, `zeroRow_contactRatio_eq_one_iff_critical_line`, `re_sub_half_eq_im_div_pi_mul_log_contactRatio`, `rightHalf_weighted_defect_eq_contactRatio_sum`, `rightHalf_weighted_defect_eq_zero_iff_all_contactRatio_one` et 2 autres |
| V46 | 3 | CONFIRMÉE | `scale_transport_separates_zeros`, `voiceScaleCharacter_injective`, `CanonicalLocalizedZeroPrimePartnership.radial_defect_recovered_from_operator` |
| V48 | 64 | CONFIRMÉE | `zero_reconstructed_grammatical_property_iff`, `zero_reconstructed_count_grammatical_property_iff`, `zeroReconstructed_blockEntryState_eq`, `zeroReconstructed_blockExitState_eq`, `zeroReconstructed_changeCount_eq`, `zeroReconstructed_block_change_imbalance_boundary`, `zeroReconstructed_blocks_join_eq`, `zeroReconstructed_order_strict_and_prime`, `zeroReconstructed_family_succession_eq`, `thetaErrorReal_eq_sub_chebyshev_on_gap` et 54 autres |
| V49 | 4 | CONFIRMÉE | `zeroReconstructed_order_strict_and_prime`, `rankedPrimePlace_injective`, `SemanticStructuralRaccord.r5_passage_place_bijective`, `GlobalZeroPrimePartnership.reconstructs_prime_history` |
| V50 | 18 | CONFIRMÉE | `zeroPassageWindow_length`, `SemanticStructuralRaccord.r1_members_preserved`, `SemanticStructuralRaccord.r1_member_count`, `FiberedCanonicalZeroPrimePartnership.directFiber_eq_canonical`, `FiberedCanonicalZeroPrimePartnership.reflectedFiber_eq_canonical`, `FiberedCanonicalPartnershipCertificate.directFiberCanonical`, `FiberedCanonicalPartnershipCertificate.reflectedFiberCanonical`, `mem_constellationHeightFiber`, `mem_constellationHeightFiber_canonical`, `constellationHeightFiber_subset` et 8 autres |
| V56 | 7 | CONFIRMÉE | `zeroPassageWindow_length`, `zeroPassageGaps_length`, `zeroPassageGaps_are_successive`, `SemanticStructuralRaccord.r4_successive_passages_exact`, `SemanticStructuralRaccord.r4_passage_count`, `SemanticStructuralRaccord.r5_passage_place_bijective`, `SemanticStructuralRaccord.r5_passage_place_order` |
| V58 | 3 | CONFIRMÉE | `passageProgressionTransfer_iff_critical_line`, `offline_refutes_passageProgressionTransfer`, `r11_is_exactly_local_critical_line` |
| V60 | 5 | CONFIRMÉE | `coupledGrammar_carries_heights_and_prime_block`, `coupledGrammar_zeroGap_and_primeColumn_same_bundle`, `FiberedCanonicalZeroPrimePartnership.reflectedCarrier_grammarState`, `FiberedCanonicalPartnershipCertificate.sameGrammar`, `decoupled_capture_indices_are_free` |
| V61 | 4 | CONFIRMÉE | `SemanticStructuralRaccord.prime_place_progresses`, `SemanticStructuralRaccord.family_zero_still_progresses`, `central_prime_unique`, `canonical_center_unique` |
| V62 | 28 | CONFIRMÉE | `offline_reflected_pair_orderKeys_differ`, `lossless_offline_rigidity_spine`, `reflect_conj_ne_self_of_re_ne_half`, `reflectedPair_left_ne_right_iff`, `reflectedPair_left_ne_right`, `reflectedPair_members_are_nontrivial_zeros`, `reflectionOrbit_card_eq_two_iff`, `offline_positive_zero_yields_rightHalf`, `primeHeightSquareBridge_heightOnly`, `primeHeightCrossFiber_reflected_same_height` et 18 autres |
| V63 | 61 | CONFIRMÉE | `zeroPrimeStepContribution_conjugateMate`, `grammarVoiceStep_conjugateMate`, `grammarVoiceRow_conjugateMate`, `orderedPositiveRepresentatives_conjugate_distinct`, `conjugateMate_coe`, `conjugateMate_involutive`, `conjugateMate_injective`, `conjugateMate_ne_self`, `conjugateMate_im`, `conjugateMate_mem_heightConstellation` et 51 autres |
| V64 | 11 | CONFIRMÉE | `orderedPositiveRepresentatives_conjugate_distinct`, `heightConstellation_mem_ordered_or_conjugate`, `conjugateMate_ne_self`, `conjugateMate_mem_heightConstellation`, `heightConstellation_eq_pos_union_neg`, `negativeRepresentatives_eq_image`, `heightConstellation_sum_eq_pair_sum`, `reflectedPair_card_eq_two`, `reflectedPairFinset_subset_heightConstellation`, `reflectionOrbit_subset_heightConstellation` et 1 autres |
| V65 | 61 | CONFIRMÉE | `offline_reflected_pair_orderKeys_differ`, `lossless_offline_rigidity_spine`, `reflect_conj_im_eq`, `reflect_conj_re_eq`, `reflect_conj_ne_self_of_re_ne_half`, `reflectConjZero_eq_anonymous`, `reflectedPair_members_have_same_height`, `reflectedPair_right_height_eq_left`, `reflectedPair_members_have_same_multiplicity`, `zeroHeight_constant_on_reflectionOrbit` et 51 autres |
| V66 | 4 | CONFIRMÉE | `offline_produces_indexed_zero_gap`, `offline_produces_degenerate_successive_passage`, `semantic_chain_A_B_D_without_C`, `MirrorPairDefect.verticalGap_eq_zero` |
| V67 | 2 | CONFIRMÉE | `FiberedCanonicalZeroPrimePartnership.reflectedCarrier_eq_canonical`, `CanonicalLocalizedZeroPrimePartnership.reflectedCarrier_eq` |
| V68 | 2 | CONFIRMÉE | `orderedPositiveRepresentatives_pairwise_lt_human`, `zeroPassageWindow_ordered` |
| V74 | 8 | CONFIRMÉE | `offline_reflected_pair_orderKeys_differ`, `reflect_conj_ne_self_of_re_ne_half`, `reflectedPair_members_are_nontrivial_zeros`, `carrier_reflectedZeroSurface`, `LocalZeroContext.mirror_mem_members`, `MirrorPairDefect.pair_mem_localContext`, `CanonicalLocalizedZeroPrimePartnership.mirror_mem_context`, `CanonicalLocalizedZeroPrimePartnership.localizes_true_pair` |
| V77 | 6 | CONFIRMÉE | `critical_line_gives_reflectedPairRatioScaleInvariant`, `reflect_conj_eq_self_of_re_eq_half`, `reflect_conj_eq_self_iff`, `criticalLine_orbit_no_internal_defect`, `reflectionOrbit_card_eq_one_iff`, `MirrorPairDefect.distinct_iff_radial_ne_zero` |
| V80 | 7 | CONFIRMÉE | `trueZeroQReturn_reflect`, `interfaceRatio_reflect`, `canonicalCarrier_reflectedPoint`, `canonicalCarrier_reflected_toBlockHolonomy_eq_crossTransport_one_zero`, `canonicalCarrier_toBlockHolonomy_reflect`, `zetaLogDerivRegularDatum_reflectConj`, `towerCharacter_block_reflected` |
| V81 | 1 | SOUS CONDITION | `orientedTau_trailingCoeff_eq` |
| V83 | 3 | CONFIRMÉE | `offline_R1_R10_local_snapshot`, `semantic_chain_A_B_D_without_C`, `MirrorPairDefect.verticalGap_eq_zero` |
| V100 | 33 | CONFIRMÉE | `canonicalScaleFourThetaZeroAmplitude_eq_neg_explicit_div`, `nontrivialZeroResidueTerm_scale`, `nontrivialZeroResidueTerm_ne_zero`, `norm_nontrivialZeroResidueTerm_eq`, `towerMode_eq_normalized_zeroRow`, `primeDirichletWeight_eq_vonMangoldt_mul_towerCharacter`, `grammarSectorPrimeDirichlet_eq_tsum_towerCharacter`, `sectorChi3Coord_eq_tsum_towerCharacter`, `centeredTrueZeroRow_eq`, `trueZeroReturnTransport_eq` et 23 autres |
| V101 | 9 | CONFIRMÉE | `nontrivialZeroResidueTerm_conjugateMate`, `collective_projection_eq_two_re_over_positive`, `towerCharacter_reflect`, `trueZeroQReturn_reflect`, `floorTowerPrimitive_reflect`, `towerCharacter_mul_edgeCocycle`, `towerCharacter_div_edgeCocycle`, `coboundaryPartial_conj`, `blockCrossTransport_one_zero` |
| V102 | 81 | CONFIRMÉE | `offlineZeroAmplitude_conj_ne_zero`, `tail_norm_lower_bound_of_windowRemainderNonCancellation`, `canonicalScaleFourThetaZeroAmplitude_eq_neg_explicit_div`, `canonicalThetaZeroMode_ne_zero`, `projectedGrammarResidueState_global_shift`, `projectedScaleFourShift_eq_smul`, `canonicalThetaZeroMode_scale_four_iterate`, `norm_canonicalThetaZeroMode_orbit`, `round26_grammar_spectral_scale_rigidity_of_annular_accumulation`, `projected_annular_accumulation_of_re_le_half` et 71 autres |
| V116 | 4 | IMPLIQUE RH SS PRÉMISSE | `riemannHypothesis_of_symmetric_budget`, `riemannHypothesis_of_budget`, `riemannHypothesis_of_budgetFamily`, `riemannHypothesis_of_chebyshevFamily` |
| V117 | 1 | ÉQUIV. RH | `trueZeroLoopPowerBounded_iff_rh` |
| V119 | 1 | IMPLIQUE RH SS PRÉMISSE | `rh_is_only_conditional_here` |
| V121 | 24 | CONFIRMÉE | `tsum_eq_reflectedPairFinset_add_rest`, `tsum_eq_reflectedPair_left_add_right_add_rest`, `primitivePsiPart_smoothedZeroPrimitive`, `primitiveThetaPart_smoothedZeroPrimitive`, `psiRecoveredFromZeros_eq_left_add_right_add_rest`, `chebyshev_theta_eq_left_add_right_add_rest`, `chebyshev_theta_at_prime_eq_left_add_right_add_rest`, `SemanticStructuralRaccord.r10_global_transport`, `primePowerCorrectionMellin_eq_integral`, `hasSum_primeThetaMellinValueTerm` et 14 autres |
| V124 | 4 | CONFIRMÉE | `tsum_eq_reflectedPairFinset_add_rest`, `tsum_eq_reflectedPair_left_add_right_add_rest`, `smoothedZeroPrimitive_eq_left_add_right_add_rest`, `totalColumnBridge_value_is_member_free` |
| V125 | 4 | CONFIRMÉE | `exists_symmetric_witness_at_every_radius`, `no_symmetry_package_law_forces_critical_line`, `sectorContinuation_pointwise_is_vacuous`, `sectorContinuation_pointwise_not_a_lock` |
| V126 | 81 | CONFIRMÉE | `offline_grammatical_defect_is_exactly_rh`, `lock_two_grammatical_route_closed_negatively`, `all_reflectedPairRatioScaleInvariant_gives_critical_line`, `all_nontrivial_zeros_re_le_half_of_annular_accumulation`, `round27_all_zeros_on_critical_line_of_annular_accumulation`, `offline_member_contradicts_prime_side_uniqueness`, `reflected_change_family_compatibility_is_target_strength`, `bf_direct_gap_defect_capture_is_target_strength`, `bf_reconstructed_grammar_defect_is_target_strength`, `bf_oneStepReflectedGrammarCompatibility_iff_global_critical_line` et 71 autres |
| V140 | 17 | CONFIRMÉE | `carrier_orientedFidelity_iff_holonomy_eq`, `carrier_holonomy_eq_iff_critical`, `carrier_critical_iff_accumulationConstant_ratio_eq`, `core_toMinusFidelity`, `core_alone_cannot_close`, `source_eq_reflectedSource_iff_critical`, `orientedFidelity_at_rho_iff_centeredPerronResidue_ratio_eq`, `rh_of_orientedFidelitySurface`, `orientedFidelitySurface_of_rh`, `orientedFidelitySurface_iff_rh` et 7 autres |
| V141 | 1 | IMPLIQUE RH SS PRÉMISSE | `rh_is_only_conditional_here` |
| V145 | 1 | CONFIRMÉE | `trueZeroPrimePowerIntervalWeld` |
| V149 | 1 | CONFIRMÉE | `SemanticStructuralRaccord.prime_place_progresses` |
| V156 | 4 | CONFIRMÉE | `uniformTowerBoundAt_iff_half_le_re`, `canonicalCarrier_source_ne_zero`, `canonicalCore_source_ne_zero`, `residue_primeGrammarChannelContinuation_ne_zero` |
| V158 | 69 | CONFIRMÉE | `zeroMode_norm_blind_to_height`, `grammarZeroModeEnergy_blind_to_height`, `voiceScaleCharacter_separates_conjugate_zeros`, `norm_towerCharacter`, `towerCharacter_eq_modulus_mul_phase`, `norm_twistedTowerCharacter`, `norm_twistedTower_ratio`, `radialDeform_im`, `radialDeform_re`, `towerCharacter_radialDeform` et 59 autres |
| V159 | 27 | CONFIRMÉE | `zero_reconstructed_grammatical_property_iff`, `zero_reconstructed_count_grammatical_property_iff`, `derived_object_invariant_under_any_zero_hypothesis`, `no_grammatical_property_separates_reflected_pair`, `offline_difference_stays_outside_the_grammar`, `lock_two_grammatical_route_closed_negatively`, `reflected_pair_cells_same_labels_different_entries`, `grammarZeroModeEnergy_blind_to_height`, `grammarZeroModeEnergy_cannot_separate_conjugate_zeros`, `any_column_label_predicate_is_row_blind` et 17 autres |
| V161 | 73 | CONFIRMÉE | `reflectedPairRatioScaleInvariant_forces_reflect_fixed`, `critical_line_gives_reflectedPairRatioScaleInvariant`, `reflectedPairRatioScaleInvariant_iff_critical_line`, `reflect_conj_eq_self_of_re_eq_half`, `reflect_conj_eq_self_iff`, `criticalLine_orbit_no_internal_defect`, `orbit_internal_defect_iff_off_critical_line`, `reflectedPair_left_ne_right_iff`, `reflectionOrbit_card_eq_one_iff`, `reflectionOrbit_card_eq_one_or_two` et 63 autres |
| V162 | 53 | CONFIRMÉE | `no_grammatical_property_separates_reflected_pair`, `offline_difference_stays_outside_the_grammar`, `reflectConjZero_heightDetermined_eq`, `not_injOn_of_heightDetermined_of_off_critical_line`, `not_injOn_heightConstellation_of_heightDetermined_of_off_critical_line`, `injOn_placement_separates_reflected_pair`, `not_heightDetermined_of_injOn_of_off_critical_line`, `offline_reflected_pair_scale_characters_differ`, `lossless_offline_rigidity_spine`, `reflectedPairRatioScaleInvariant_iff_critical_line` et 43 autres |
| V163 | 2 | SOUS CONDITION | `offline_difference_stays_outside_the_grammar`, `lossless_offline_rigidity_spine` |
| V165 | 5 | SOUS CONDITION | `exists_zero_gap_of_off_critical_line`, `exists_position_with_zero_internal_gap_of_off_critical_line`, `offline_produces_indexed_zero_gap`, `offline_produces_degenerate_successive_passage`, `CanonicalLocalizedZeroPrimePartnership.defect_two_manifestations` |
| V167 | 25 | CONFIRMÉE | `offline_reflected_pair_scale_characters_differ`, `offline_orbit_internal_defect`, `offline_member_gives_labelled_table_entry_defect`, `reflectedPair_primitive_difference_unbounded`, `reflectedPair_psi_separated`, `orbitStepContribution_of_off_critical_line`, `reflectedFloor_pos_of_offline`, `reflectedDefect_pos_at_every_prime_column`, `contactRatio_symmetric_defect_pos`, `norm_towerCharacter_pow_mul_reflect` et 15 autres |
| V170 | 1 | SOUS CONDITION | `rawHermitian_reflect_eq_two_products_forces_critical` |
| V172 | 19 | CONFIRMÉE | `floorNormalizedZeroRow_at_primePower`, `floorNormalizedZeroRow_floor_independent_at_primePower`, `floorNormalizedZeroRow_return_quotient`, `master_identity_couples_all_floors_and_primes`, `rawZeroPrimeSignature_eq_floorNormalizedZeroRow`, `rawZeroPrimeSignature_floor_independent`, `rawZeroPrimeSignature_eq_coeff_mul_character`, `rawZeroPrimeSignature_ne_zero`, `norm_rawZeroPrimeSignature`, `crossScaleSignature_eq` et 9 autres |
| V174 | 98 | CONFIRMÉE | `zero_reconstructed_grammatical_property_iff`, `derived_object_invariant_under_any_zero_hypothesis`, `zeroReconstructed_blockEntryState_eq`, `zeroReconstructed_blockExitState_eq`, `zeroReconstructed_changeCount_eq`, `zeroReconstructed_block_change_imbalance_boundary`, `zeroReconstructed_change_skeleton_alternates`, `zeroReconstructed_family_succession_eq`, `signed_change_eq`, `real_block_change_imbalance_boundary` et 88 autres |
| V177 | 1 | CONFIRMÉE | `zeroReconstructed_change_skeleton_alternates` |
| V180 | 3 | CONFIRMÉE | `reflectedPairEnergy_eq_zero_iff`, `reflectedPairEnergy_pos_of_off_line`, `primeChannelEnergyBounded_iff_critical` |
| V181 | 1 | CONFIRMÉE | `case_critical` |

## 2. Ajouts proposés

Vérités nouvelles (aucune Vi du maître ne les porte), rédigées à la manière du maître ; toutes sont des théorèmes compilés de ce lot, dans une base hors hiérarchie RHV6.

1. Toute propriété d'un objet dérivé déterministiquement de la grammaire reconstruite depuis les zéros vaut si et seulement si elle vaut de l'objet dérivé de l'histoire première ; aucune hypothèse sur un zéro, hors ligne ou non, ne modifie cet objet. — établi par : `zero_reconstructed_grammatical_property_iff`, `derived_object_invariant_under_any_zero_hypothesis`, `no_grammatical_property_separates_reflected_pair`.
2. Si une loi première interdit un défaut grammatical D, exiger de tout zéro hors ligne que l'objet reconstruit porte D équivaut, en énoncé déroulé, à « tout zéro non trivial a re = 1/2 » ; la route grammaticale est équivalente à RH et fermée négativement. — établi par : `grammatical_defect_route_equivalent_to_absence`, `offline_grammatical_defect_is_exactly_rh`, `lock_two_grammatical_route_closed_negatively`.
3. Une application déterminée par la hauteur seule ne peut pas être injective sur une constellation de hauteur T contenant un zéro hors ligne ; un placement injectif doit séparer le zéro hors ligne de son réfléchi-conjugué. — établi par : `reflectConjZero_heightDetermined_eq`, `not_injOn_heightConstellation_of_heightDetermined_of_off_critical_line`, `not_heightDetermined_of_injOn_of_off_critical_line`.
4. Un zéro hors ligne force, dans les écarts de constellation de sa hauteur, un écart exactement nul, à une position déterminée de l'énumération ordonnée. — établi par : `exists_zero_gap_of_off_critical_line`, `exists_position_with_zero_internal_gap_of_off_critical_line`.
5. Le défaut interne d'orbite (deux contributions zéro-premier distinctes entre ρ et son réfléchi-conjugué) existe si et seulement si re ρ ≠ 1/2 ; l'invariance d'échelle du rapport de la paire réfléchie équivaut, pour un zéro, à re ρ = 1/2 (équivalences par zéro, non RH). — établi par : `orbit_internal_defect_iff_off_critical_line`, `reflectedPairRatioScaleInvariant_iff_critical_line`.
6. La hiérarchie mod 6 (état d'entrée/sortie de bloc, imbalance des familles 4 et 2 égale à la différence des poids de bord, alternance du squelette, jonction de blocs) tient sur les blocs de premiers réels et, à l'identique, sur les blocs reconstruits depuis les zéros. — établi par : `real_block_change_imbalance_boundary`, `real_block_change_skeleton_alternates`, `zeroReconstructed_change_skeleton_alternates`, `zeroReconstructed_block_change_imbalance_boundary`.
7. Le module du caractère de tour ne voit que le défaut horizontal re ρ − 1/2 : ‖towerCharacter P ρ‖ = P^{−(re ρ − 1/2)} ; l'opérateur croisé du zéro réfléchi est l'opérateur radial de défaut re − 1/2. — établi par : `norm_towerCharacter`, `trueZeroReflectedCrossOperator_eq_radial_matrix`.
8. Six prémisses de clôture (H1 à H6, déterminant du croisement réfléchi, facteur de réflexion, compatibilité, phase, rang un, second moment) sont chacune démontrée équivalente à RH ; la matrice à six voies n'est qu'une reformulation de RH. — établi par : `h1Determinant_iff_rh`, `h2_iff_rh`, `h3_iff_rh`, `h4_iff_rh`, `h5_iff_rh`, `h6_iff_rh`, `sixWay_matrix_is_one_reformulation`.
9. Les prémisses « budget de régularité du canal premier », « bornitude des puissances de boucle », « énergie du canal premier bornée », « transport de tour borné », « borne uniforme du carrier », « objet de clôture hauteur-croisement », « cohérence orientée du partenariat fibré » sont chacune équivalentes à RH ; les implications vers RH qui en partent ne déchargent donc rien. — établi par : `primeChannelRegularityBudget_iff_riemannHypothesis`, `trueZeroLoopPowerBounded_iff_rh`, `trueZeroPrimeChannelEnergyBounded_iff_riemannHypothesis`, `trueZeroTowerTransportBounded_iff_riemannHypothesis`, `uniformCarrierBound_iff_rh`, `primeHeightCrossClosureObject_iff_rh`, `canonicalFiberedPartnershipOrientedCoherence_iff_rh`.
10. La sous-exponentialité de l'énergie de Mellin de θ (aussi sous ses formes échelle quatre, écarts premiers exacts, majorant du point milieu) entraîne RH ; le majorant élémentaire est équivalent, sans perte, à la sous-exponentialité exacte ; aucune de ces prémisses n'est établie. — établi par : `riemann_hypothesis_from_thetaMellin_subexponential`, `riemann_hypothesis_from_scale_four_subexponential`, `riemann_hypothesis_from_prime_gap_exact_mellin_subexponential`, `riemann_hypothesis_from_midpoint_majorant_subexponential`, `primeGapExactMellinSubexponential_iff_midpoint_majorant`.
11. Sous la prémisse d'accumulation annulaire d'échelle quatre pour un zéro, re ρ ≤ 1/2 ; la prémisse est, par zéro, équivalente à re ρ ≤ 1/2 : c'est le verrou lui-même, non une réduction. — établi par : `round26_grammar_spectral_scale_rigidity_of_annular_accumulation`, `projected_annular_accumulation_iff_re_le_half`, `riemann_hypothesis_of_annular_accumulation`.
12. Le terme de fidélité (objet grammaire-tour-zéro, partenariat fibré à 33 champs) est strictement nécessaire à RH : privé de son champ terminal, l'objet est habité sans condition et ne donne rien ; l'implication vers RH exige donc l'objet complet. — établi par : `riemannHypothesis_of_grammarTowerZeroFidelityObject`, `fidelity_is_strictly_necessary`, `riemannHypothesis_of_fiberedPartnershipTDD`, `fidelity_is_strictly_necessary_for_partnership`.
13. Une loi qui ne consomme que les symétries (paquet de symétries) ne peut forcer la criticité : cette route est réfutée comme théorème. — établi par : `no_symmetry_package_law_forces_critical_line`.

## 3. Cascades

Dépendances inverses calculées sur tout `rh_gap_criterion.jsonl` (`deps_project`). Pour les dépendants situés hors du lot, l'énoncé est la première phrase de la docstring, à défaut le début du type (mention « hors lot »). Trois des fondations les plus utilisées sont des faits élémentaires (positivité de p m, monotonie des coupures), ce qui est attendu d'un lot où la plupart des théorèmes sont des identités de sommes.

- **`p_pos_real`** (Le m-ième premier réel est strictement positif) — CONFIRMÉE. Cette vérité est confirmée (80 dépendants) et provoque la série de conséquences suivantes : `ScientificRebuild20260829.canonicalPrimeEdgeLogWidth_pos` (Every canonical prime edge has strictly positive logarithmic width. (hors lot)) ; `ScientificRebuild20260829.canonicalPrimeEdge_ratio_eq_one_add_gap` (The prime-edge ratio is exactly `1 + g_n / p_n`. (hors lot)) ; `SelectedPrimeBlock.one_lt_ratio` (Le rapport d'un bloc sélectionné est >1) ; `SelectedPrimeBlock.ratio_pos` (Le rapport p(fin)/p(début) d'un bloc est >0) ; `accumulationConstant_reflection_ratio_exact` (Le rapport des constantes d'accumulation = (source réfléchie/source) × \|caractère de tour\|²) ; `arg_twistedTower_ratio_radialDeform_invariant` (L'argument du rapport de bloc est invariant par déformation radiale) ; `canonicalCarrier_accumulated_constant_ne_zero` (La constante multiplicative source/caractère(p2) du canal accumulé est non nulle) ; `canonicalCarrier_accumulationConstant_ne_zero_at` (La constante d'accumulation du carrier à toute base M est non nulle) ; et 72 autres.
- **`scaleSubBreak_step_nonneg`** (Les points de coupure scaleSubBreak sont croissants en j) — CONFIRMÉE. Cette vérité est confirmée (28 dépendants) et provoque la série de conséquences suivantes : `cellInverseMass_eq_blockWeight_of_overlaps` (Sous les deux recouvrements, la masse inverse de cellule égale blockWeight) ; `cellStateDrift_sq_div_le_cubic_uniform` (Dérive d'état² / poids ≤ (9/64)(longueur)³/e^{2U}) ; `centeredCell_le_two_weighted_plus_two_drift` (Discrépance centrée²/poids ≤ 2·poids·état² + 2·dérive²/poids, par cellule) ; `centeredMeanEnergyRow_eq_rowActiveSupport` (L'énergie de ligne égale sa restriction au support actif exact) ; `centeredMeanEnergy_eq_global_weighted_state_energy` (L'énergie centrée totale égale l'énergie d'état marqué pondéré plus des termes croisés état×dérive (type tronqué)) ; `centeredRowEnergy_eq_rowActiveSupport_canonical` (L'énergie centrée de ligne à l'horizon canonique égale sa restriction au support actif exact) ; `driftContribution_sum_le_of_maxCellLength` (La contribution de dérive totale est ≤ (9/64) L² e^{−U} si toute cellule a longueur ≤ L) ; `dynamicPairCellWeight_nonneg` (Le poids de cellule 1/a − 1/b est ≥ 0) ; et 20 autres.
- **`rightHalfPositiveZeros_finite`** (Le rectangle de demi-plan droit strict de hauteur positive est fini) — CONFIRMÉE. Cette vérité est confirmée (19 dépendants) et provoque la série de conséquences suivantes : `SemanticTransportClosure20260821.FullyAlignedSameEventContext.identifiedRightHalf_mem_finset` (The identified member really occurs in the finite support used by the global defect. (hors lot)) ; `SemanticTransportClosure20260821.FullyAlignedSameEventContext.rightHalfFiniteSummand_nonneg` (Every summand of the strict-right-half radial defect is nonnegative. (hors lot)) ; `SemanticTransportClosure20260821.alignedRightZeroFinset_coe_image_eq_rightHalf` (The coe image of the aligned RIGHT support is literally the existing right-half rectangle finset used by `N'(1/2,T)`. (hors lot)) ; `exists_rightHalfPaddedRectangle` (Pour T>0 il existe un rectangle rembourré strictement intérieur au support droit) ; `nprime_half_eq_finite_order_sum` (N'(1/2,T) est la somme finie des ordres des zéros du rectangle droit) ; `nprime_half_eq_zero_iff_isEmpty` (N'(1/2,T)=0 ⟺ le rectangle droit est vide) ; `nprime_half_nonneg` (Le compteur N'(1/2,T) est ≥ 0) ; `rightHalfMultiplicityNat_cast_eq_nprime_half` (L'enveloppe naturelle rightHalfMultiplicityNat T est le compteur N'(1/2,T)) ; et 11 autres.
- **`towerCharacter_ne_zero`** (Le caractère de tour est non nul pour P>0) — CONFIRMÉE. Cette vérité est confirmée (19 dépendants) et provoque la série de conséquences suivantes : `accumulationConstant_reflection_ratio_exact` (Le rapport des constantes d'accumulation = (source réfléchie/source) × \|caractère de tour\|²) ; `canonicalCarrier_accumulated_constant_ne_zero` (La constante multiplicative source/caractère(p2) du canal accumulé est non nulle) ; `canonicalCarrier_accumulationConstant_ne_zero_at` (La constante d'accumulation du carrier à toute base M est non nulle) ; `canonicalCarrier_toBlockHolonomy_comp` (L'holonomie de bloc du porteur se compose : hol(M,N) = hol(M,K)·hol(K,N)) ; `canonicalCarrier_toBlockHolonomy_eq_accumulationConstant_ratio` (L'holonomie du bloc [M,N) est le rapport des constantes d'accumulation en M et N) ; `centralPivotCarrierFactor_ne_zero` (Le facteur central du porteur canonique n'est jamais nul) ; `edgeCocycle_weight_eq_rightChar_mul_translate` (Poids de Dirichlet tordu par le cocycle d'arête = caractère du bord droit × poids translaté) ; `edgeCurvature_eq_central_log_curvature` (Le rapport des deux arêtes est le caractère de tour de p(n+1)²/(p n·p(n+2))) ; et 11 autres.
- **`gnat_pos`** (L'écart canonique gnat n est strictement positif) — CONFIRMÉE. Cette vérité est confirmée (18 dépendants) et provoque la série de conséquences suivantes : `ScientificRebuild20260828.RealObjectBoundaryState.hasZeroGapAndPositivePrimeGap` (The state simultaneously contains the zero-side zero gap and a positive canonical prime gap. (hors lot)) ; `ScientificRebuild20260828.canonicalPrimeGapPositive` (Every canonical consecutive-prime gap is strictly positive. (hors lot)) ; `ScientificRebuild20260828.localForcedPrimeGapPositive` (The forced arithmetic gap is strictly positive. (hors lot)) ; `ScientificRebuild20260828.weldedCasePrimeGapPositive` (On that exact selected prime column the canonical prime gap is still strictly positive. (hors lot)) ; `ScientificRebuild20260829.FiberedMirrorGapEntry.canonicalPrimeGapPositive` (Canonical consecutive-prime gaps are strictly positive. (hors lot)) ; `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.canonical_axis_gap_pos` (The canonical outgoing gap at the axis is nonzero. (hors lot)) ; `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.event_gap_pos` (Master §11 on the event cell: the canonical consecutive-prime gap is strictly positive. (hors lot)) ; `ScientificRebuild20260829.preOff_twoChannel_zeroPrimeGap_rigidity` (Bundled pre-OFF two-channel rigidity on a canonical prime edge: the arithmetic edge is strictly positive, its scalar Tower factor  (hors lot)) ; et 10 autres.
- **`CanonicalLocalizedZeroPrimePartnership.source_canonical`** (La source de la capture du partenariat est la source canonique) — CONFIRMÉE. Cette vérité est confirmée (16 dépendants) et provoque la série de conséquences suivantes : `CanonicalLocalizedZeroPrimePartnership.block_entry_from_primeSide` (L'état d'entrée du premier ancrage est l'entrée du côté premier) ; `CanonicalLocalizedZeroPrimePartnership.block_exit_from_primeSide` (L'état de sortie du second ancrage est la sortie du côté premier) ; `CanonicalLocalizedZeroPrimePartnership.directCarrier_state_from_primeSide` (L'état du carrier direct au rang i du bloc vaut 1 − 2·potentiel grammatical de la position du côté premier) ; `CanonicalLocalizedZeroPrimePartnership.orientedIndicator_from_primeSide` (L'indicateur orienté au rang i est décidé par la transition du côté premier) ; `CanonicalLocalizedZeroPrimePartnership.reflectedCarrier_state_from_primeSide` (Le carrier miroir a le même état, projeté du même côté premier) ; `CanonicalLocalizedZeroPrimePartnership.tdd_inverseTransition` (Les transitions du côté premier de P sont transformOf des résidus mod 6 consécutifs, et transformOf s t = tau11/15/51/55 équivaut à (s,t) = (1,1)/(1,5)/(5,1)/(5,5)) ; `CanonicalLocalizedZeroPrimePartnership.tdd_primeChannel` (Le canal premier se décompose (tau11 + tau55 + fibre croisée pour σ>1) et le côté premier de P est le bloc de M (piCount,p,gnat) et de M^Z (zerosPrime…) sur les ancrages du bloc de P) ; `LocalizedMirrorPairPrimeWeldCase.capturePrimeSide_eq_pairPrimeGrammar` (The `primeSide` used by the localized partnership is exactly the active prime grammar block of the pair-specific source-sensitive  (hors lot)) ; et 8 autres.
- **`cpow_ofReal_pos_eq_exp`** (Pour P>0, P^z = exp(log P · z) dans ℂ) — CONFIRMÉE. Cette vérité est confirmée (15 dépendants) et provoque la série de conséquences suivantes : `centeredTrueZeroRow_primePow` (À l'étage x=p^m, la ligne centrée vaut reflectedRowCoeff ρ × (caractère de tour^m)⁻¹) ; `cpow_realExp_eq_exp` (Pour u réel et z complexe, (exp u)^z = exp(u·z) dans ℂ) ; `crossScaleSignature_eq_cpow` (La signature inter-échelles vaut (P/Q)^(ρ−1/2)) ; `crossScaleSignature_eq_transformedZeroScaleCocycle` (La signature inter-échelles d'un zéro égale le cocycle d'échelle de la grammaire transformée) ; `floorTowerPrimitive_at_primePower` (Au point u=m·log P, la primitive d'étage égale le caractère de tour towerCharacter P z (m disparaît), pour tout z) ; `h4_iff_rh` (H4PhaseRealization équivaut à RiemannHypothesis) ; `rawZeroPrimeSignature_eq_coeff_mul_character` (La signature brute vaut coefficient propre du membre × caractère d'échelle au log P) ; `towerCharacter_div` (Le caractère de tour est multiplicatif en la base : car(A/B)=car(A)/car(B)) ; et 7 autres.
- **`norm_towerCharacter`** (‖towerCharacter P ρ‖ = P^(−(re ρ − 1/2)) : le module ne voit que le défaut horizontal) — CONFIRMÉE. Cette vérité est confirmée (15 dépendants) et provoque la série de conséquences suivantes : `case_critical` (Pour re ρ = 1/2 (2≤M≤N), toutes les observables valent leur valeur de bord : normes 1, énergie 0, tour bornée) ; `centralPivotCarrierFactor_norm` (La norme du facteur central vaut ‖source‖·p(n+1)^{−(re ρ −1/2)}) ; `grammatical_return_is_not_transport_return` (Pour re ρ ≠ 1/2 et sigma A = sigma B, les modules du carrier en A et B diffèrent) ; `localEdgeDefect_two_eq_reflect_forces_critical` (Si le défaut local en 2 de ρ égale celui de son réfléchi, alors re ρ = 1/2) ; `norm_localEdgeDefect_eq_one_of_critical` (Pour re ρ = 1/2, le défaut local a module 1 à chaque arête) ; `norm_towerCharacter_eq_one_iff` (Pour P>1, ‖towerCharacter P ρ‖=1 ⟺ re ρ = 1/2) ; `norm_towerCharacter_pow` (Le module de l'étage m vaut P^(−m(re ρ −1/2))) ; `norm_towerCharacter_pow_eq_one_of_critical` (Sur la ligne critique, chaque étage m de la tour est de module 1) ; et 7 autres.
- **`CanonicalLocalizedZeroPrimePartnership.radial_eq`** (Le défaut radial du partenariat est re(zéro) − 1/2) — CONFIRMÉE. Cette vérité est confirmée (15 dépendants) et provoque la série de conséquences suivantes : `CanonicalLocalizedZeroPrimePartnership.operator_one_zero_eq_defect` (L'entrée (1,0) de l'opérateur vaut ratio^(radial)) ; `CanonicalLocalizedZeroPrimePartnership.operator_zero_one_eq_defect` (L'entrée (0,1) de l'opérateur vaut ratio^(−radial)) ; `CanonicalLocalizedZeroPrimePartnership.tdd_adjoint` (L'adjoint (conjugué transposé) de l'opérateur de P est l'antidiagonale (0, ratio^(défaut) ; ratio^(−défaut), 0)) ; `CanonicalLocalizedZeroPrimePartnership.tdd_radialDefect` (L'opérateur de P est la matrice antidiagonale (0, ratio^(−défaut radial) ; ratio^(défaut radial), 0)) ; `CanonicalLocalizedZeroPrimePartnership.tdd_radialOperator` (L'opérateur de P égale l'opérateur croisé radial du bloc de P au défaut radial de P) ; `CanonicalLocalizedZeroPrimePartnership.tdd_tStarT` (T†·T de l'opérateur de P vaut diag(ratio^(2·défaut), ratio^(−2·défaut))) ; `CanonicalLocalizedZeroPrimePartnership.tdd_ttStar` (T·T† de l'opérateur de P vaut diag(ratio^(−2·défaut), ratio^(2·défaut))) ; `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.radialDefectSameZero` (Compatibility: the stored radial defect is exactly the same zero's real displacement. (hors lot)) ; et 7 autres.
- **`SelectedPrimeBlock.start_lt_end`** (Début < fin pour un bloc sélectionné) — CONFIRMÉE. Cette vérité est confirmée (14 dépendants) et provoque la série de conséquences suivantes : `CanonicalLocalizedZeroPrimePartnership.block_grammatical_return` (Si entrée = sortie du côté premier, le produit Π(1−2·cross n) sur le bloc vaut 1) ; `CanonicalLocalizedZeroPrimePartnership.tdd_commonTransport` (Le transport de P a pour entrées les quotients du caractère de tour en p_end sur p_start, au membre (0,1) et au miroir (1,0)) ; `CanonicalLocalizedZeroPrimePartnership.tdd_grammarComposition` (Le produit sur le bloc de P des (1 − 2·cross n) vaut sigma(pStart)·sigma(pEnd) (télescopage du canal de changement d'état)) ; `SelectedPrimeBlock.end_ge_two` (La fin d'un bloc sélectionné est ≥ 2) ; `SelectedPrimeBlock.one_lt_ratio` (Le rapport d'un bloc sélectionné est >1) ; `SemanticTransportClosure20260821.DefectAnchoredReturnData.directPerronCarrierWeld` (Perron-to-carrier provenance on the SAME defect-anchored return block, direct member. (hors lot)) ; `SemanticTransportClosure20260821.DefectAnchoredReturnData.reflectedPerronCarrierWeld` (Perron-to-carrier provenance on the same two endpoints, reflected member. (hors lot)) ; `SemanticTransportClosure20260821.FullyAlignedSameEventContext.directPerronCarrierWeld` (Perron -> carrier on the aligned first-return block, direct member. (hors lot)) ; et 6 autres.
- **`prod_one_sub_two_cross`** (Sur [M,N) avec 2≤M≤N, le produit des (1−2·cross n) vaut sigma M · sigma N) — CONFIRMÉE. Cette vérité est confirmée (13 dépendants) et provoque la série de conséquences suivantes : `CanonicalLocalizedZeroPrimePartnership.tdd_grammarComposition` (Le produit sur le bloc de P des (1 − 2·cross n) vaut sigma(pStart)·sigma(pEnd) (télescopage du canal de changement d'état)) ; `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R8_composition` (R8 — exact composition law on the SAME active interval. (hors lot)) ; `SemanticTransportClosure20260821.actualAssembly_grammarComposition` (The real two-transition assembly window has the standard exact prime-grammar composition law. (hors lot)) ; `SemanticTransportClosure20260821.terminalPrimeBlock_actualGrammaticalReturn` (The real prime grammar holonomy of `[2,4)` closes exactly. (hors lot)) ; `abs_prod_one_sub_two_cross` (Ce produit télescopé est de module exactement 1) ; `core_grammarCompositionSurface` (Le produit sur [M,N) de (1−2 cross n) vaut state M × state N) ; `grammarTowerZeroFidelityObjectMinusFidelity_holds` (L'objet de fidélité amputé de son champ terminal (32 surfaces) est habité sans condition) ; `integrated_system_is_zerohood_free` (Pour tout z complexe et 2≤M≤N, le système intégré est une identité algébrique (bloc, rayon, réciprocité sous réflexion, puissance m, énergie ≥0)) ; et 5 autres.
- **`MirrorPairDefect.mirror_eq`** (Le miroir du couple est le réfléchi-conjugué du zéro) — CONFIRMÉE. Cette vérité est confirmée (13 dépendants) et provoque la série de conséquences suivantes : `CanonicalLocalizedZeroPrimePartnership.mirror_mem_context` (Le miroir du partenariat appartient au contexte local) ; `CanonicalLocalizedZeroPrimePartnership.reflected_holonomy` (L'holonomie de la branche miroir sur les mêmes ancrages est l'entrée (1,0) du même transport) ; `CanonicalLocalizedZeroPrimePartnership.tdd_reflectedRadial` (La partie réelle du miroir de P vaut 1 moins celle du membre) ; `MirrorPairDefect.distinct_iff_radial_ne_zero` (Le miroir est distinct du zéro ssi le défaut radial est non nul) ; `MirrorPairDefect.mirror_radial` (Le miroir porte le défaut radial opposé : Re(miroir) − 1/2 = −radial) ; `MirrorPairDefect.pair_mem_localContext` (Le zéro et le miroir d'un couple appartiennent au contexte local du zéro) ; `MirrorPairDefect.same_height` (Le miroir et le zéro d'un couple ont la même hauteur) ; `MirrorPairDefect.signedSeparation_eq_two_mul_radial` (La coordonnée radiale utilisée par la tour est exactement la moitié de la séparation intrinsèque. (hors lot)) ; et 5 autres.

## 4. Points ouverts touchés et tensions éclairées

- **O5 / O10 / O21 (deux lois de l'inversion, caractérisation de la droite critique, prémisse `D(z)=0` ⟺ RH)** : le lot contient un grand nombre de prémisses nommées, chacune prouvée équivalente à RH (H1–H6, budget de régularité, boucle bornée, carrier borné, objet de clôture, partenariat fibré, fidélité orientée) ; il éclaire le même mur que le maître (« toute prémisse P avec P → RH est ⟺ RH ou strictement plus forte », CLAUDE.md §4) dans une base indépendante, sans le lever. Rattachement seulement, aucune résolution.
- **O6 / O9 / O17 (isolement du terme d'un zéro, amplitude `q^β/‖ρ‖`)** : les théorèmes d'amplitude de rh_gap (`norm_nontrivialZeroResidueTerm_eq`, `norm_rawZeroPrimeSignature`, `rawHermitian_reflect_eq_two_products_forces_critical`) instancient dans cette base le canal β-visible ; chaque terme y est un objet propre à un zéro (T9 éclairée : ici aussi rien n'est extrait d'une somme), sans relation de taille aux premiers.
- **O12 / T-mod6** : la rigidité mod 6 est établie sur les blocs réels et reconstruits (V174) ; le lot confirme qu'elle est invisible à la présence hors ligne (objet reconstruit = objet premier, `derived_object_invariant_under_any_zero_hypothesis`) ; aucun lien n'y est démontré avec C_lecture.
- **O10 (« grammaire par membres / hauteurs ») et route « application déterminée par la hauteur ET injective » (CLAUDE.md, plan E096–E100)** : `not_injOn_heightConstellation_of_heightDetermined_of_off_critical_line` et voisins en sont une version compilée dans cette base (impossibilité hors ligne), sans lien démontré avec RHV6Fresh.
- **T9 / T14** : les théorèmes de ce lot sont formulés sur des zéros authentiques (`IsNontrivialZetaZero`), jamais sur des points synthétiques ; les théorèmes « hors ligne » sont donc conditionnels au sens du maître (hypothèse `re ≠ 1/2`), jamais instanciés.

## 5. Incidents

- **sorryAx / axiome non standard** : aucun dans le lot (les sept axiomes `native_decide` du projet sont dans `ScientificRebuild*` et `MasterLeanE58TotalTripleRoute`, hors C4b).
- **Terme RH fermé** : aucun (aucun type exactement `RiemannHypothesis`).
- **docstring ≠ type** : `riemannHypothesis_of_grammarTowerZeroFidelityObject` (docstring « aucune prémisse externe », le type prend l'objet de fidélité en hypothèse) ; même divergence pour `riemannHypothesis_of_fiberedPartnershipTDD` (TDD à 33 champs en hypothèse).
- **nom promettant plus que le type** : `commonFactorWeld_everywhere_is_rh` (type = implication seulement, même type que `rh_of_commonFactorWeld_everywhere`) ; `fidelity_is_strictly_necessary` et `canonicalFiberedPartnershipProvenance_no_terminal_strength` (types = tautologies RH ↔ RH sous prémisse habitée) ; `sectorContinuation_pointwise_not_a_lock` (P → (RH ↔ RH), P prouvée) ; `riemannHypothesis_of_idealTerminalObject` et `_of_chebyshevFamily_only` / `_unconditionalStrip` (noms « seule prémisse », « inconditionnel » : conditionnels) ; `unconditional_theta_mellin_energy_subexponential_from_scale_four` (« unconditional » : implication depuis la sous-exponentialité d'échelle quatre) ; `H2_trivial_rate_no_gain`, `S1_second_diff_sign_undetermined_statement`, `M2_triangularLogKernel_abs_le` (noms négatifs/tentatifs, types = bornes ou identités).
- **Types tronqués (>900 car.)** : 17 entrées glosées à partir de la docstring et des dépendances (mention « type tronqué » dans la cellule).
- **Lignes sans numéro de ligne source** : 3 lemmes `congr_simp` auto-générés (`offlineZeroChannelTail.congr_simp` et deux `.mk.congr_simp`).
- **Noms dupliqués entre modules** : 11 noms de ce lot (`gnat_pos`, `R_eq_centered_add_boundary`, `R_sq_le_card_mul_sum_aT_sq`, `R_succ_sub_R_eq_aT`, `Rseq_sub_eq_sum_dR`, `canonicalTHorizon_monotone`, `centered_R_sq_le_card_mul_sum_aT_sq`, `centered_R_sq_le_card_mul_sum_dR_sq`, `rawRWindowEnergy_scale_chasles`, `young_param_reverse`, `young_param_upper`) existent aussi dans un module hors lot ; le champ « entraîne » est calculé sur le `full_name` commun, donc partagé entre les deux copies.
- **Déclarations privées** : 22 lemmes `_private…` glosés sous leur nom court.
- **Réserves de méthode** : conditions RÉCLASSÉES par script selon le correctif n°1 (voir en-tête) ; les projections de structure de fidélité gardent `SOUS CONDITION (structure)` car l'hypothèse est l'objet-prémisse lui-même.

## 6. Contrôle de complétude

Script : lignes du lot dans `data/rh_gap_criterion.jsonl` (modules de `lots/C4b.txt`) = 2446 ; entrées des tables par module = 2446 ; théorèmes distincts (module, nom) = 2446 ; modules = 140 ; entrées des tables par module par module : toutes non nulles ; comptes de statuts : CONFIRMÉE 2005, ÉQUIV. RH 37, SOUS CONDITION 348, IMPLIQUE RH SS PRÉMISSE 53, RÉFUTATION 3 (total 2446). Résultat : OK, égalité.
