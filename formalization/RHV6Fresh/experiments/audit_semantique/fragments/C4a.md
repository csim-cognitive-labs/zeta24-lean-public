# Fragment C4a — rh_gap_criterion, premier tiers (159 modules, 2467 théorèmes)

Base : `formalization/rh_gap_criterion/` (Mathlib v4.31.0), hors hiérarchie d'autorité RHV6 (CLAUDE.md §2), auditée selon les mêmes règles. Données : `data/rh_gap_criterion.jsonl`, lot `lots/C4a.txt`. Colonne « entraîne » = nombre de théorèmes (sur tout `rh_gap_criterion.jsonl`) dont `deps_project` contient le nom (dépendances inverses calculées par script). Statuts après application du correctif de contrôle n°1 : une hypothèse qui n'est qu'une condition de domaine est notée `CONFIRMÉE (domaine : …)` ; `CONFIRMÉE SOUS CONDITION` est réservé aux restrictions substantielles (hors ligne, prémisse supposée nommée, certificat…). « RH » du projet : les modules Round26/27 emploient souvent le prédicat du projet `RhGap.RH` ou des ensembles Z abstraits ; le type fait foi et la distinction est notée en remarque quand elle a été relevée. Les énoncés sont des lectures du type par relecteur (Sonnet) ; les modules de ports d'analyse générique (`P4Port.*`, `PerronPort.*`) n'instancient aucune vérité du maître : `AJOUT`.

Répartition des statuts : CONFIRMÉE : 2219, CONFIRMÉE SOUS CONDITION : 181, RÉFUTATION COMPILÉE : 26, IMPLIQUE RH SOUS PRÉMISSE : 24, ÉQUIVALENTE À RH : 14, HORS STANDARD : 3.

## Tables par module


### `RhGapCriterion.Audit.AVSourceReplay`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Audit.AVSourceReplay.replay_nontrivialZeroResidueTerm_eq_coeff_mul_cpow` | Pour tout réel x et tout zéro non trivial rho, le terme résiduel du zéro en x égale le coefficient de ligne réfléchie audité de rho multiplié par x puissance rho (complexe). | CONFIRMÉE | AJOUT | 1 |
| `Audit.AVSourceReplay.replay_reflectedResidueDifference_complex_closedForm` | Pour tout x et tout zéro rho, la différence résiduelle réfléchie de rho en x égale (coeff(rho) x^rho) moins (coeff(miroir conjugué de rho) x^(miroir conjugué)), forme close complexe. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Audit.TrustedNativeBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `projectNontrivialZero_to_trusted` | Tout zéro non trivial du projet est un zéro non trivial au sens indépendant Mathlib seul (pont projet vers trusted). | CONFIRMÉE (domaine : rho est un zéro non trivial du projet) | AJOUT | 4 |
| `trustedNontrivialZero_to_project` | Tout zéro non trivial au sens trusted (Mathlib seul) est un zéro non trivial du projet (pont réciproque). | CONFIRMÉE (domaine : rho est un zéro non trivial au sens trusted) | AJOUT | 4 |
| `projectNontrivialZero_iff_trusted` | Le prédicat de zéro non trivial du projet est équivalent au prédicat trusted Mathlib seul. | CONFIRMÉE | AJOUT | 0 |
| `projectMultiplicity_eq_trusted` | La multiplicité de zéro du projet est égale à la multiplicité trusted (ordre analytique Mathlib). | CONFIRMÉE | AJOUT | 4 |
| `projectMirror_coe_eq_trustedMirror` | Le miroir fonctionnel du projet (réflexion conjuguée) d'un zéro a exactement la valeur complexe du miroir trusted spécifié indépendamment. | CONFIRMÉE | V65 | 0 |
| `SemanticTransportClosure20260821.alignedPositive_support_eq_trusted` | Pour tout T, le support positif aligné du projet, coercé dans les complexes, est exactement le support trusted des zéros de partie imaginaire dans 0,T (bornes strictes). | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.alignedLine_support_eq_trusted` | Pour tout T, le support aligné sur la droite critique, coercé dans les complexes, est exactement le support trusted des zéros de la droite de partie imaginaire dans 0,T. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.alignedRight_support_eq_trusted` | Pour tout T, le support aligné strictement à droite de la droite critique est exactement le support trusted correspondant (même coupure stricte). | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.trustedZerosPosBelow_finite` | Pour tout T, l'ensemble trusted des zéros de partie imaginaire dans 0,T est fini. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.trustedZerosLinePosBelow_finite` | Pour tout T, l'ensemble trusted des zéros de la droite critique de partie imaginaire dans 0,T est fini. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.trustedZerosRightPosBelow_finite` | Pour tout T, l'ensemble trusted des zéros strictement à droite de la droite critique de partie imaginaire dans 0,T est fini. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.alignedTotalMultiplicityNat_eq_trustedNcount` | Pour tout T, la multiplicité totale alignée (entier naturel) égale le comptage trusted Ncount T. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.alignedLineMultiplicityNat_eq_trustedNline` | Pour tout T, la multiplicité alignée sur la droite critique égale le comptage trusted Nline T. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.alignedRightMultiplicityNat_eq_trustedWright` | Pour tout T, la multiplicité alignée à droite de la droite égale le comptage trusted Wright T. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.alignedRightWeightedDefect_eq_trustedDright` | Pour tout T, la somme finie pondérée (partie réelle moins 1/2) fois multiplicité sur les zéros alignés à droite égale le défaut pondéré trusted Dright T. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.projectDright_eq_trustedDright` | Pour tout T, la somme pondérée zeroes_sum sur la bande 1/2,1 avec hauteur dans 0,T de (partie réelle moins 1/2) est le Dright T trusted. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.trustedR12Partition` | Pour tout T, l'énoncé trusted R12PartitionStatement T (partition R12 des zéros à hauteur T) est vrai. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.trustedC8Barycentric` | Pour tout T, l'énoncé trusted C8BarycentricStatement T (énoncé barycentrique C8) est vrai. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Basic`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `theoremA` | Pour tout m, le résidu cumulatif de gaps R m égale p m moins p 0 moins θm m (écart de Chebyshev aux points premiers, à normalisation près). | CONFIRMÉE | AJOUT | 1 |
| `θm_succ` | L'incrément de θm est le logarithme du m-ième premier : θm (m+1) = θm m + log (p m). | CONFIRMÉE | AJOUT | 3 |
| `theoremC` | Pour tout m, R m se décompose en somme sur les valeurs de gap d de la somme des résidus g_n moins log p_n sur la famille des n<m de gap d. | CONFIRMÉE | AJOUT | 1 |
| `enumeration_bookkeeping` | La comptabilité d'énumération est vraie : n vers p n est une bijection de range (m+1) sur les premiers inférieurs ou égaux à p m. | CONFIRMÉE | AJOUT | 6 |
| `bridge` | Sous la comptabilité d'énumération, pour tout m, θ(p m) moins p m égale moins (R m + p 0 moins log p m). | CONFIRMÉE (domaine : comptabilité d'énumération, théorème par ailleurs) | AJOUT | 3 |
| `theoremB` | Sous von Koch/Schoenfeld, propagation aux points premiers et comptabilité d'énumération, RH du projet équivaut à l'existence de C>0 tel que pour tout m la valeur absolue de R m + p 0 moins log p m est bornée par C racine(p m) log(p m) au carré. | ÉQUIVALENTE À RH | AJOUT | 1 |
| `gap_criterion` | Sous von Koch/Schoenfeld et propagation aux points premiers, RH du projet équivaut au critère de gaps (existence de C>0 avec borne racine(p m) log carré sur le résidu recentré). | ÉQUIVALENTE À RH | AJOUT | 1 |
| `p_strictMono` | La suite des premiers p est strictement croissante. | CONFIRMÉE | AJOUT | 116 |
| `p_prime` | Pour tout n, p n est premier. | CONFIRMÉE | AJOUT | 58 |
| `two_le_p` | Pour tout n, 2 <= p n. | CONFIRMÉE | AJOUT | 23 |
| `le_p` | Pour tout n, n <= p n. | CONFIRMÉE | AJOUT | 11 |
| `p_zero` | Le plus petit premier est p 0 = 2. | CONFIRMÉE | AJOUT | 13 |
| `p_succ_le_of_prime_gt` | Si q est premier et p m < q alors p (m+1) <= q : p (m+1) est le plus petit premier supérieur à p m. | CONFIRMÉE (domaine : q premier, p m < q) | AJOUT | 8 |
| `exists_enclosing` | Tout x >= 2 est encadré par deux premiers consécutifs : il existe m avec p m <= x < p (m+1). | CONFIRMÉE (domaine : x >= 2) | AJOUT | 1 |
| `theta_locally_const` | θ de Chebyshev est localement constante entre premiers consécutifs : si p m <= x < p (m+1) alors θ x = θ (p m). | CONFIRMÉE (domaine : x dans l'intervalle entre p m et p (m+1)) | AJOUT | 3 |
| `p_succ_le_two_mul` | Postulat de Bertrand sur la suite des premiers : p (m+1) <= 2 p m. | CONFIRMÉE | AJOUT | 6 |
| `gap_identity` | Identité exacte du gap : p(m+1) moins p m = (p(m+1) moins θ(p(m+1))) + log p(m+1) + (θ(p m) moins p m). | CONFIRMÉE | AJOUT | 1 |
| `sqrt_log_sq_mono` | La fonction t vers racine(t) log(t) au carré est croissante sur 1 et au-delà. | CONFIRMÉE (domaine : 1 <= u <= v) | AJOUT | 1 |
| `sqrt_log_sq_double` | Pour X >= 2, racine(2X) log(2X) au carré est majoré par 8 fois racine(X) log(X) au carré. | CONFIRMÉE (domaine : X >= 2) | AJOUT | 1 |
| `prime_point_propagation` | La propagation points-premiers est un théorème : la borne racine(x) log carré sur θ(x) moins x aux arguments premiers l'implique partout, avec constante 10C+4. | CONFIRMÉE | AJOUT | 1 |
| `gap_criterion_vonKoch_only` | Sous la seule hypothèse von Koch/Schoenfeld, RH du projet équivaut au critère de gaps (existence de C>0 avec borne racine(p m) log carré sur le résidu recentré). | ÉQUIVALENTE À RH | AJOUT | 1 |
| `class_partition` | Pour tout m, R m est la somme sur les six classes c<6 de la partie S6 c m (partition exacte des gaps par classe mod 6). | CONFIRMÉE | V174 | 1 |
| `mode_inverse` | Formules inverses exactes des modes : S6 0 = (T+B)/3, S6 2 = (2T-B+3O)/6, S6 4 = (2T-B-3O)/6. | CONFIRMÉE | AJOUT | 0 |
| `mode_energy` | Identité d'énergie ponctuelle : S6 0 carré + S6 2 carré + S6 4 carré = T carré/3 + B carré/6 + O carré/2. | CONFIRMÉE | AJOUT | 0 |
| `p_odd` | Pour n >= 1, p n est impair. | CONFIRMÉE (domaine : 1 <= n) | AJOUT | 1 |
| `gnat_even` | Pour n >= 1, le gap gnat n est pair. | CONFIRMÉE (domaine : 1 <= n) | AJOUT | 1 |
| `gnat_class_even` | Pour n >= 1, la classe mod 6 du gap gnat n est 0, 2 ou 4. | CONFIRMÉE (domaine : 1 <= n) | V174 | 7 |
| `p_one` | Le deuxième premier est p 1 = 3. | CONFIRMÉE | AJOUT | 15 |
| `gnat_zero` | gnat 0 = 1, seul gap impair de la suite des premiers (le type ne dit que gnat 0 = 1). | CONFIRMÉE | AJOUT | 2 |
| `odd_classes` | Pour m >= 1, S6 1 m = g0 moins log p0 et S6 3 m = S6 5 m = 0 (frontière des classes impaires). | CONFIRMÉE (domaine : 1 <= m) | AJOUT | 1 |
| `mode_conservation` | Pour m >= 1, le mode total Tmode m égale R m moins (g0 moins log p0). | CONFIRMÉE (domaine : 1 <= m) | AJOUT | 7 |
| `Tmode_chebyshev_exact` | Pour m >= 1, Tmode m + (g0 moins log p0) + p0 moins log p m = p m moins θ(p m) (pont exact du mode T vers l'erreur de Chebyshev). | CONFIRMÉE (domaine : 1 <= m) | AJOUT | 1 |
| `mode_criterion_vonKoch_only` | Sous von Koch/Schoenfeld, RH du projet équivaut à une borne racine(p m) log carré sur le mode total recentré Tmode m + (g0 moins log p0) + p0 moins log p m, pour m >= 1. | ÉQUIVALENTE À RH | AJOUT | 0 |
| `p_two` | Le troisième premier est p 2 = 5. | CONFIRMÉE | AJOUT | 35 |
| `prime_mod6_state` | Pour n >= 2, p n mod 6 vaut 1 ou 5 (états de la grammaire). | CONFIRMÉE (domaine : 2 <= n) | V174 | 49 |
| `gap_mod6_exhaustive` | Pour n >= 1, la classe mod 6 du gap gnat n est 0, 2 ou 4 (alias de gnat_class_even). | CONFIRMÉE (domaine : 1 <= n) | V174 | 7 |
| `transition_exhaustive` | Pour n >= 2, la transition (p n mod 6, p (n+1) mod 6) est l'une des quatre paires de {1,5} x {1,5}. | CONFIRMÉE (domaine : 2 <= n) | V174 | 0 |
| `class_projection_complete` | Pour n >= 2, classe 0 du gap si et seulement si état mod 6 conservé, classe 2 si et seulement si transition 5 vers 1, classe 4 si et seulement si transition 1 vers 5. | CONFIRMÉE (domaine : 2 <= n) | V174 | 15 |
| `pattern_is_grammar_path` | Pour n >= 2 et tout k, chaque étape i<k du pattern relie deux états de {1,5} et la classe du gap est exactement la projection de la transition. | CONFIRMÉE (domaine : 2 <= n, i < k) | V174,V176 | 1 |
| `pattern_family_closure` | Pour n >= 1, la classe du gap est dans {0,2,4} de manière unique (fermeture des trois familles primitives). | CONFIRMÉE (domaine : 1 <= n) | V174,V176 | 4 |
| `meta_pattern_grammar_finite` | Pour n >= 2 et toute étape i<k, états dans {1,5}, classe du gap dans {0,2,4} et équivalences classe/transition : fermeture de la grammaire finie du méta-pattern. | CONFIRMÉE (domaine : 2 <= n, i < k) | V174,V176 | 1 |
| `growth_contradicts_subexponential` | Pour a>0, une borne sous-exponentielle de E et une croissance exponentielle de taux a le long d'une suite non bornée sont contradictoires (conclusion False). | RÉFUTATION COMPILÉE (conjonction d'une croissance exponentielle de taux a>0 et d'une borne sous-exponentielle) | AJOUT | 3 |
| `local_energy_to_global_discrete` | Si l'énergie locale par fenêtre vérifie Egrid n <= C exp(eps n), alors la somme pondérée des n<N de exp(2n) Egrid n est majorée par N C exp((2+eps)N). | CONFIRMÉE (domaine : C>=0, eps>=0, borne exponentielle sur Egrid) | AJOUT | 0 |
| `functional_symmetry_forces_half` | Si un ensemble Z de complexes est stable par rho vers 1-rho et si tout élément a partie réelle <= 1/2, alors tout élément a partie réelle égale à 1/2. | IMPLIQUE RH SOUS PRÉMISSE (Z stable par la symétrie fonctionnelle et aucun zéro à partie réelle > 1/2) | V62 | 3 |
| `T_cocycle_increment` | Pour 1 <= m1 <= m2, Tmode m2 = 1 * Tmode m1 + (R m2 moins R m1) : bloc T unipotent du cocycle d'échelle. | CONFIRMÉE (domaine : 1 <= m1 <= m2) | AJOUT | 0 |
| `theoremF_offline_exclusion` | Si E est sous-exponentielle et si tout élément de Z à partie réelle > 1/2 force une croissance exponentielle de taux 2 Re moins 1, alors tout élément de Z a partie réelle <= 1/2. | CONFIRMÉE SOUS CONDITION (E sous-exponentielle ; tout zéro hors ligne force une croissance de taux 2 Re moins 1) | AJOUT | 1 |
| `theoremF_RH_from_T_spectral_rigidity` | Sous E sous-exponentielle, croissance forcée par tout zéro à partie réelle > 1/2 et stabilité de Z par rho vers 1-rho, tout élément de Z a partie réelle 1/2. | IMPLIQUE RH SOUS PRÉMISSE (énergie sous-exponentielle, croissance forcée par tout zéro hors ligne, symétrie fonctionnelle) | V62 | 0 |
| `p_three` | Le quatrième premier est p 3 = 7. | CONFIRMÉE | AJOUT | 24 |
| `p_four` | Le cinquième premier est p 4 = 11. | CONFIRMÉE | AJOUT | 28 |
| `p_five` | Le sixième premier est p 5 = 13. | CONFIRMÉE | AJOUT | 9 |
| `T_increment_eq_gap_residual` | Pour n >= 1, Tmode (n+1) moins Tmode n = g n moins log (p n). | CONFIRMÉE (domaine : 1 <= n) | AJOUT | 7 |
| `T_path_sum` | Pour 1 <= a <= b, Tmode b moins Tmode a est la somme sur a <= n < b de (g n moins log p n). | CONFIRMÉE (domaine : 1 <= a <= b) | AJOUT | 2 |
| `T_path_concatenation` | Les incréments de Tmode se concatènent sans terme de jonction : (Tmode b moins Tmode a) + (Tmode c moins Tmode b) = Tmode c moins Tmode a. | CONFIRMÉE | AJOUT | 0 |
| `Tmode_one` | Tmode 1 = 0. | CONFIRMÉE | AJOUT | 2 |
| `Tmode_as_sum_from_one` | Pour m >= 1, Tmode m est la somme sur 1 <= n < m des aT n. | CONFIRMÉE (domaine : 1 <= m) | AJOUT | 4 |
| `TReal_at_prime` | Pour m >= 1, l'extension réelle TReal en p m vaut Tmode m. | CONFIRMÉE (domaine : 1 <= m) | AJOUT | 6 |
| `TReal_between_consecutive_primes` | Pour m >= 1 et p m <= x < p (m+1), TReal x = Tmode m (constance en escalier entre deux premiers consécutifs). | CONFIRMÉE (domaine : 1 <= m, x dans l'intervalle entre p m et p (m+1)) | AJOUT | 1 |
| `T_real_at_prime` | Pour m >= 1, TRealPrimeIndex m = Tmode m (ancien nom Round 9A). | CONFIRMÉE (domaine : 1 <= m) | AJOUT | 0 |
| `T_real_between_primes` | Pour m >= 1 et entiers x avec p m <= x < p (m+1), TReal x = Tmode m (ancien nom). | CONFIRMÉE (domaine : 1 <= m, x entier dans l'intervalle) | AJOUT | 0 |
| `T_real_jump` | Pour n >= 1, Tmode (n+1) moins Tmode n = aT n (saut canonique de T). | CONFIRMÉE (domaine : 1 <= n) | AJOUT | 1 |
| `TReal_jump_at_next_prime` | Pour n >= 1, TReal (p (n+1)) moins TReal (p n) = aT n. | CONFIRMÉE (domaine : 1 <= n) | AJOUT | 0 |
| `TReal_zero_before_five` | Pour tout réel x < 5, TReal x = 0. | CONFIRMÉE (domaine : x < 5) | AJOUT | 0 |
| `T_real_zero_before_first_even_gap` | TRealPrimeIndex 1 = 0 (valeur nulle en p 1 = 3, avant le premier gap pair). | CONFIRMÉE | AJOUT | 0 |
| `T_real_cumulative_identity` | Pour m >= 1, TReal (p m) est la somme des aT n pour 1 <= n < m. | CONFIRMÉE (domaine : 1 <= m) | AJOUT | 0 |
| `TReal_equals_Tmode_at_prime` | Pour m >= 1, TReal (p m) = Tmode m (alias). | CONFIRMÉE (domaine : 1 <= m) | AJOUT | 0 |
| `round9A_signal_eq_Tmode_plus_boundary` | Pour m >= 1, R m = Tmode m + (g0 moins log p0). | CONFIRMÉE (domaine : 1 <= m) | AJOUT | 2 |
| `round9A_signal_eq_T_real_plus_a0` | Pour m >= 1, R m = TReal (p m) + (g0 moins log p0). | CONFIRMÉE (domaine : 1 <= m) | AJOUT | 0 |
| `T_increment_not_grammar_function` | Il existe n1, n2 >= 2 de mêmes états mod 6 (p, p suivant) et même classe de gap mais d'incréments Tmode différents. | CONFIRMÉE | V176 | 1 |
| `T_increment_not_mod6_projection_function` | Même énoncé : il existe n1, n2 >= 2 de même projection mod 6 (p, p suivant, gap) dont les incréments de Tmode diffèrent. | CONFIRMÉE | V176 | 0 |
| `round8_examples_have_distinct_scale` | log (p 2) est différent de log (p 4), soit log 5 différent de log 11. | CONFIRMÉE | AJOUT | 2 |
| `round8_examples_have_distinct_density_state` | 1/log (p 2) est différent de 1/log (p 4). | CONFIRMÉE | AJOUT | 0 |
| `round8_obstruction_does_not_apply_to_full_meta_state` | p 2 et p 4 ont même résidu mod 6 mais log (p 2) différent de log (p 4). | CONFIRMÉE | AJOUT | 0 |
| `ordered_meta_state_injective` | Si p n = p m alors n = m : injectivité de l'indexation des premiers. | CONFIRMÉE | AJOUT | 0 |
| `normalized_T_increment_identity` | Pour n >= 1, Tmode (n+1) moins Tmode n = log p n fois (g n / log p n moins 1). | CONFIRMÉE (domaine : 1 <= n) | AJOUT | 0 |
| `zero_mode_scale_eigenvalue` | Pour tout rho, c, a, U, c exp((rho moins 1/2)(U+a)) = exp((rho moins 1/2) a) fois (c exp((rho moins 1/2) U)) : l'échelle est diagonale de valeur propre exp((rho moins 1/2) a). | CONFIRMÉE | AJOUT | 0 |
| `zero_scale_eigenvalue_abs` | Pour tout rho et a réel, la norme de exp((rho moins 1/2) a) est exp(a (Re rho moins 1/2)). | CONFIRMÉE | V102 | 0 |
| `scale_state_composition` | Pour tout rho, a, b, exp((rho moins 1/2)(a+b)) = exp((rho moins 1/2) a) fois exp((rho moins 1/2) b). | CONFIRMÉE | AJOUT | 0 |
| `density_scale_cocycle` | Pour tout rho, a et entier k, (exp((rho moins 1/2) a))^k = exp(k ((rho moins 1/2) a)). | CONFIRMÉE | AJOUT | 0 |
| `subexponential_operator_excludes_eigenvalue_gt_one` | Si r>0 et si pour tout eps>0 il existe C>0 avec r^k <= C exp(eps k) pour tout k entier, alors r <= 1. | CONFIRMÉE SOUS CONDITION (r>0, borne sous-exponentielle sous itération) | AJOUT | 1 |
| `eigenvalue_modulus_le_one_of_operator_subexp` | Si exp(a (Re rho moins 1/2)) vérifie la borne sous-exponentielle sous itération (pour tout eps), alors exp(a (Re rho moins 1/2)) <= 1. | CONFIRMÉE SOUS CONDITION (borne sous-exponentielle de l'opérateur d'échelle) | AJOUT | 0 |
| `functional_symmetry_forces_exact_half` | Si Z est stable par rho vers 1-rho et si toute partie réelle de Z est <= 1/2, alors toute partie réelle de Z vaut 1/2 (alias). | IMPLIQUE RH SOUS PRÉMISSE (Z stable par la symétrie fonctionnelle et aucun zéro à partie réelle > 1/2) | V62 | 3 |
| `RH_from_density_order_scale_rigidity` | Pour a>0, si Z est stable par rho vers 1-rho et si exp(a (Re rho moins 1/2)) <= 1 pour tout rho de Z, alors toute partie réelle de Z vaut 1/2. | IMPLIQUE RH SOUS PRÉMISSE (symétrie fonctionnelle de Z et module de valeur propre d'échelle <= 1 pour tout zéro) | V62 | 1 |
| `energy_kernel_symm_G` | Le noyau d'énergie energyKernelG est symétrique en ses deux indices de premier. | CONFIRMÉE | AJOUT | 0 |
| `energy_kernel_nonneg_G` | Le noyau d'énergie energyKernelG est positif ou nul en chaque point (positivité ponctuelle, non semi-définie). | CONFIRMÉE | AJOUT | 0 |
| `energy_kernel_eq_zero_of_le_G` | Le noyau d'énergie s'annule dès que X <= max pm pn. | CONFIRMÉE (domaine : X <= max pm pn) | AJOUT | 0 |
| `energy_kernel_geometric_homogeneity_G` | Homogénéité géométrique du noyau : K(cX, c pm, c pn) = c K(X, pm, pn) pour c >= 0. | CONFIRMÉE (domaine : 0 <= c) | AJOUT | 0 |
| `gram_kernel_psd` | Le noyau de Gram discret pondéré (poids w j >= 0) est semi-défini positif : la forme quadratique z m z n G(m,n) est positive ou nulle. | CONFIRMÉE (domaine : poids positifs ou nuls) | AJOUT | 0 |
| `double_sum_symm_split` | Pour un noyau symétrique c sur range N, la somme double égale la diagonale plus deux fois la somme sur m<n. | CONFIRMÉE (domaine : c symétrique) | AJOUT | 1 |
| `local_energy_translation_identity` | L'énergie locale de F translaté de a au centre U égale l'énergie locale de F au centre U+a. | CONFIRMÉE | AJOUT | 0 |
| `energy_transfer_integral` | Pour beta > 1/2, l'intégrale de t^(2 beta moins 2) de a à b vaut (b^(2 beta moins 1) moins a^(2 beta moins 1)) / (2 beta moins 1). | CONFIRMÉE (domaine : beta > 1/2) | AJOUT | 1 |
| `subexponential_of_nonpos_rate` | Si E U <= C exp(a U) pour U >= 0 avec C>0 et a <= 0, alors E est sous-exponentielle. | CONFIRMÉE (domaine : C>0, a <= 0, borne exponentielle de taux non positif) | AJOUT | 1 |
| `pointwise_bound_to_local_energy` | Si la valeur absolue de Q t est bornée par M t^beta L sur a,b (0<a, beta>1/2) et Q^2/t^2 intégrable, alors l'intégrale de Q^2/t^2 est majorée par M^2 L^2 (b^(2 beta moins 1) moins a^(2 beta moins 1)) / (2 beta moins 1). | CONFIRMÉE (domaine : 0<a<=b, beta>1/2, borne ponctuelle sur Q, intégrabilité) | AJOUT | 0 |
| `polynomial_le_exponential` | Pour tout k et eps>0, il existe C>0 avec (1+U)^k <= C exp(eps U) pour tout U >= 0. | CONFIRMÉE (domaine : eps>0) | AJOUT | 2 |
| `polynomial_mul_nonpos_rate_subexponential` | Si E U <= C (1+U)^k exp(a U) pour U >= 0 avec C>0 et a <= 0, alors E est sous-exponentielle. | CONFIRMÉE (domaine : C>0, a <= 0, borne polynôme fois exponentielle) | AJOUT | 4 |
| `critical_polylog_implies_subexponential` | Si E U <= C (1+U)^k pour U >= 0 avec C>0, alors E est sous-exponentielle (régime polylogarithmique critique). | CONFIRMÉE (domaine : C>0, borne polynomiale en 1+U) | AJOUT | 0 |

### `RhGapCriterion.CanonicalRestrictionFinal`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `canonical_prime_datum_immutable17` | Les coordonnées canoniques d'une position déjà connue sont identiques dans une observation plus grande du même objet global (N <= M). | CONFIRMÉE (domaine : N <= M) | AJOUT | 0 |
| `prime_position_immutable17` | La position d'un premier est immuable sous extension du périmètre (N <= M). | CONFIRMÉE (domaine : N <= M) | AJOUT | 0 |
| `prime_relation_immutable17` | La relation parmi les quatre relations primitives est immuable sous extension du périmètre (N <= M). | CONFIRMÉE (domaine : N <= M) | AJOUT | 0 |
| `prime_family_immutable17` | Le code de famille est immuable sous extension du périmètre (N <= M). | CONFIRMÉE (domaine : N <= M) | AJOUT | 0 |
| `T_increment_immutable17` | L'incrément canonique de T attaché à la position est immuable sous extension du périmètre (N <= M). | CONFIRMÉE (domaine : N <= M) | AJOUT | 0 |
| `prime_zero_bridge_restriction17` | Si deux suites (côté premier, côté zéro) sont égales terme à terme, leurs restrictions canoniques à tout périmètre N <= M sont égales. | CONFIRMÉE (domaine : suites primeSide et zeroSide égales terme à terme, N <= M) | V60 | 0 |
| `translated_scale_invariance_closes_RH17` | Pour a>0, si Z est stable par rho vers 1-rho et si exp(a (Re rho moins 1/2)) <= 1 pour tout rho de Z, alors toute partie réelle de Z vaut 1/2. | IMPLIQUE RH SOUS PRÉMISSE (symétrie fonctionnelle de Z et module spectral d'échelle <= 1 pour tout zéro) | V62 | 0 |

### `RhGapCriterion.ChebyshevThetaAbelBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `primeIndicator_zero` | primeIndicator 0 = 0. | CONFIRMÉE | AJOUT | 1 |
| `primeIndicator_one` | primeIndicator 1 = 0. | CONFIRMÉE | AJOUT | 1 |
| `sum_Icc_primeIndicator_eq_piCount` | Pour tout n, la somme sur k de 0 à n de l'indicatrice des premiers est piCount n (nombre de premiers <= n). | CONFIRMÉE | AJOUT | 2 |
| `sum_Icc_log_mul_primeIndicator_eq_chebyshevθ` | Pour tout n, la somme sur k de 0 à n de log k fois l'indicatrice des premiers est chebyshevθ n. | CONFIRMÉE | AJOUT | 3 |
| `piIndicatorSum_eq_piReal` | Pour tout réel x, piIndicatorSum x égale piReal x. | CONFIRMÉE | AJOUT | 1 |
| `chebyshevθ_eq_piIndicatorSum_abel_raw` | Pour x >= 2, θ(partie entière de x) = log x fois piIndicatorSum x moins l'intégrale de 2 à x de piIndicatorSum t / t (sommation d'Abel). | CONFIRMÉE (domaine : x >= 2) | AJOUT | 1 |
| `chebyshevθ_eq_piReal_abel_raw` | Pour x >= 2, θ(partie entière de x) = log x fois piReal x moins l'intégrale de 2 à x de piReal t / t (sommation d'Abel, forme π). | CONFIRMÉE (domaine : x >= 2) | AJOUT | 1 |
| `chebyshevθ_eq_zerosPrimeCountReal_abel_raw` | Pour x >= 2, θ(partie entière de x) = log x fois zerosPrimeCountReal x moins l'intégrale de 2 à x de zerosPrimeCountReal t / t (sommation d'Abel, comptage reconstruit depuis les zéros). | CONFIRMÉE (domaine : x >= 2) | V48 | 2 |
| `chebyshev_theta_orbit_rest_decomposition` | Pour tout zéro non trivial rho et x >= 2, θ(partie entière de x) est la somme de la partie orbite hors ligne et de la partie reste de rho. | CONFIRMÉE (domaine : rho zéro non trivial, x >= 2) | AJOUT | 2 |

### `RhGapCriterion.CompleteStateCirculation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `p_step` | Si p k = a, b est premier, a < b et aucun premier n'existe strictement entre a et b, alors p (k+1) = b (pas élémentaire). | CONFIRMÉE (domaine : p k = a, b premier, a < b, aucun premier strictement entre a et b) | AJOUT | 14 |
| `p_six` | p 6 = 17. | CONFIRMÉE | AJOUT | 8 |
| `p_seven` | p 7 = 19. | CONFIRMÉE | AJOUT | 8 |
| `p_eight` | p 8 = 23. | CONFIRMÉE | AJOUT | 8 |
| `p_nine` | p 9 = 29. | CONFIRMÉE | AJOUT | 9 |
| `p_ten` | p 10 = 31. | CONFIRMÉE | AJOUT | 5 |
| `p_eleven` | p 11 = 37. | CONFIRMÉE | AJOUT | 5 |
| `p_twelve` | p 12 = 41. | CONFIRMÉE | AJOUT | 3 |
| `p_thirteen` | p 13 = 43. | CONFIRMÉE | AJOUT | 1 |
| `p_fourteen` | p 14 = 47. | CONFIRMÉE | AJOUT | 1 |
| `p_fifteen` | p 15 = 53. | CONFIRMÉE | AJOUT | 1 |
| `p_sixteen` | p 16 = 59. | CONFIRMÉE | AJOUT | 2 |
| `p_seventeen` | p 17 = 61. | CONFIRMÉE | AJOUT | 5 |
| `p_eighteen` | p 18 = 67. | CONFIRMÉE | AJOUT | 5 |
| `p_nineteen` | p 19 = 71. | CONFIRMÉE | AJOUT | 2 |
| `path_potential_remainder_identity` | Si J n = Phi (n+1) moins Phi n + r n pour tout n, alors la somme de J sur a <= n < b égale Phi b moins Phi a plus la somme de r sur a <= n < b. | CONFIRMÉE (domaine : J n = Phi(n+1) moins Phi n + r n pour tout n, a <= b) | AJOUT | 0 |
| `witness_profiles_equal_10_17` | Pour toute quantification q confondant (p 10, p 11) avec (p 17, p 18), les profils de circulation en n = 10 et n = 17 coïncident. | CONFIRMÉE (domaine : q confond p 10 avec p 17 et p 11 avec p 18) | AJOUT | 1 |
| `witness_profiles_equal_11_18` | Pour toute quantification q confondant (p 11, p 12) avec (p 18, p 19), les profils de circulation en n = 11 et n = 18 coïncident. | CONFIRMÉE (domaine : q confond p 11 avec p 18 et p 12 avec p 19) | AJOUT | 1 |
| `witness_increments_differ` | Les incréments Tmode 11 moins Tmode 10 et Tmode 18 moins Tmode 17 sont différents. | CONFIRMÉE | AJOUT | 1 |
| `circulation_obstruction_quantized_complete_state` | Pour toute quantification q confondant les états en 10 et 17, 11 et 18, 12 et 19, il n'existe aucun couple (Phi, rho) exprimant l'incrément de Tmode comme différence de potentiel Phi sur profils de circulation plus reste rho. | RÉFUTATION COMPILÉE (existence d'un potentiel Phi et d'un reste rho sur le profil de circulation quantifié) | AJOUT | 1 |
| `circulation_obstruction_decade_cells` | Pour la quantification décimale q = Nat.log 10, il n'existe aucun couple (Phi, rho) exprimant l'incrément de Tmode comme différence de potentiel sur profils de circulation plus reste. | RÉFUTATION COMPILÉE (existence d'un potentiel sur le profil de circulation décimal) | AJOUT | 0 |
| `exact_circulation_transfers_potential_bound_to_T` | Si l'incrément de Tmode est une différence exacte Phi (n+1) moins Phi n et si la valeur absolue de Phi est bornée par K, alors la variation de Tmode entre a et b est bornée par 2K. | CONFIRMÉE (domaine : potentiel exact Phi, borne K sur Phi, 1 <= a <= b) | AJOUT | 0 |
| `tautological_potential_exists` | Il existe un potentiel Phi (Tmode lui-même) dont les différences donnent les incréments de Tmode pour n >= 1. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.CoupledRigidGrammar`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `FullRigidCoupledZeroPrimeGrammar.mk.congr_simp` | Lemme de congruence auto-généré (mk.congr_simp) pour la structure FullRigidCoupledZeroPrimeGrammar : deux structures de même noyau et mêmes champs sont égales. | CONFIRMÉE (domaine : les champs de la structure : partition des transitions, etc.) | AJOUT | 0 |
| `RigidCoupledZeroPrimeGrammar.mk.congr_simp` | Lemme de congruence auto-généré (mk.congr_simp) pour la structure RigidCoupledZeroPrimeGrammar : mêmes blocs premiers et champs égaux donnent des structures égales. | CONFIRMÉE (domaine : les champs de la structure : encodage de la source, lignes de zéros canoniques, etc.) | AJOUT | 0 |
| `CoupledRigidGrammar.reconstructed_block_eq_prime` | Champ de CoupledRigidGrammar : le bloc complet reconstruit depuis les zéros (comptage, position, gap) est le bloc premier du même organisme (M^Z = M). | CONFIRMÉE | V48,V60,V174 | 3 |
| `CoupledRigidGrammar.zero_source_encoding_eq_reconstructed_block` | Champ de CoupledRigidGrammar : l'encodage de la source complète des vrais zéros est le bloc reconstruit M^Z. | CONFIRMÉE | V48,V174 | 2 |
| `CoupledRigidGrammar.prime_history_determines_zero_source` | Champ de CoupledRigidGrammar : toute continuation de zêta déterminée par le produit d'Euler des premiers a pour source de zéros la source canonique. | CONFIRMÉE (domaine : F est une continuation déterminée par les premiers) | V60 | 1 |
| `CoupledRigidGrammar.MZ_eq_M` | Pour tout organisme grammatical couplé G, le bloc reconstruit depuis les zéros égale le bloc premier de G (M^Z = M extrait). | CONFIRMÉE | V48,V60,V174 | 1 |
| `CoupledRigidGrammar.zero_source_encoding_eq_MZ` | Pour tout organisme G, l'encodage de la source canonique des zéros égale le bloc reconstruit M^Z. | CONFIRMÉE | V48,V174 | 0 |
| `CoupledRigidGrammar.zero_source_encoding_eq_M` | Pour tout organisme G, l'encodage de la source canonique des zéros égale le bloc premier rigide de G. | CONFIRMÉE | V48,V60,V174 | 1 |
| `CoupledRigidGrammar.any_count_position_gap_object_eq` | Toute fonction déterministe H du triplet (comptage, position, gap) donne la même valeur sur la version reconstruite depuis les zéros et sur (piCount, p, gnat). | CONFIRMÉE | V60,V174 | 1 |
| `CoupledRigidGrammar.primes_determine_zero_source` | Pour tout organisme G, toute continuation déterminée par les premiers a pour source de zéros la source canonique. | CONFIRMÉE (domaine : F est une continuation déterminée par les premiers) | V60 | 3 |
| `CoupledRigidGrammar.offline_snapshot` | Si un zéro positif de hauteur <= T a une partie réelle différente de 1/2, alors le même organisme porte un gap de zéros nul et M^Z égale le bloc premier. | CONFIRMÉE SOUS CONDITION (existence d'un zéro hors ligne parmi les représentants positifs de hauteur T) | V162,V174 | 0 |

### `RhGapCriterion.E44MirrorPrimeThreshold`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `exists_prime_gt_real_le_two_mul` | Pour x réel >= 2, il existe un premier q avec x < q <= 2x (corollaire de Bertrand, forme réelle). | CONFIRMÉE (domaine : x >= 2) | AJOUT | 1 |
| `primeRightTailSeparation_of_scale_two` | Si Rstar >= 2, L < Rstar, R = lambda Rstar et lambda >= 2, alors la séparation arithmétique PrimeRightTailSeparation L R Rstar est vraie. | CONFIRMÉE (domaine : Rstar >= 2, L < Rstar, R = lambda Rstar avec lambda >= 2) | AJOUT | 1 |
| `primeRightTailSeparation_of_scale_two_swap` | Sous les mêmes hypothèses (Rstar >= 2, L < Rstar, R = lambda Rstar, lambda >= 2), il existe un premier q avec Rstar < q, L < q et q <= R. | CONFIRMÉE (domaine : Rstar >= 2, L < Rstar, R = lambda Rstar avec lambda >= 2) | AJOUT | 0 |

### `RhGapCriterion.E44PrimeThresholdDefectTail`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `exists_prime_rank_gt_of_p_lt_prime` | Tout premier q > p N est égal à p j pour un rang j > N. | CONFIRMÉE (domaine : q premier, p N < q) | AJOUT | 1 |
| `prime_beyond_defect_threshold_has_row_defect` | Pour tout zéro rho de partie réelle différente de 1/2, il existe N tel que tout premier q > p N est p j avec j > N et un défaut de ligne (RowContributionDefect) sur la colonne j. | CONFIRMÉE SOUS CONDITION (rho hors ligne) | AJOUT | 1 |
| `prime_beyond_defect_threshold_changes_reflected_residue` | Pour tout zéro rho de partie réelle différente de 1/2, il existe N tel que pour tout premier q > p N, de rang j, la différence résiduelle réfléchie change entre p j et p (j+1). | CONFIRMÉE SOUS CONDITION (rho hors ligne) | AJOUT | 0 |

### `RhGapCriterion.E44VonMangoldtGrammarBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `e44CriticalDefect_eq_radial` | Sous la loi E44 éliminée, le défaut critique de contact égale le défaut radial exprimé depuis beta. | CONFIRMÉE (domaine : loi E44 éliminée entre L, R, m et beta) | AJOUT | 1 |
| `e44RadialDefectFromBeta_eq_zero_iff` | Pour m >= 1 et beta différent de 0, le défaut radial e44RadialDefectFromBeta m beta est nul si et seulement si beta = 1/2. | CONFIRMÉE (domaine : 1 <= m, beta différent de 0) | AJOUT | 4 |
| `e44CriticalDefect_eq_zero_iff` | Sous la loi E44 éliminée, pour m >= 1 et beta différent de 0, le défaut critique de contact est nul si et seulement si beta = 1/2. | CONFIRMÉE (domaine : loi E44 éliminée, 1 <= m, beta différent de 0) | AJOUT | 1 |
| `e44RadialDefectFromBeta_div_stage` | Pour m >= 1 et beta différent de 0, le défaut radial divisé par m vaut pi (1/beta moins 2), indépendant du stade. | CONFIRMÉE (domaine : 1 <= m, beta différent de 0) | AJOUT | 0 |
| `e44RadialDefect_mirror_sum` | La somme des défauts radiaux en beta et 1-beta vaut m pi (2 beta moins 1) au carré / (beta (1 moins beta)). | CONFIRMÉE (domaine : beta et 1-beta différents de 0) | V65 | 1 |
| `e44RecoveredDeltaPsi_eq_deltaPsi` | Pour L, R >= 2, l'incrément de ψ récupéré depuis le canal complet des zéros égale l'incrément de Chebyshev ΔΨ sur la cellule L,R. | CONFIRMÉE (domaine : 2 <= L, 2 <= R) | V48 | 3 |
| `e44_certified_prime_position` | Pour tout n, la position première reconstruite depuis le canal complet des zéros égale p n. | CONFIRMÉE | V48 | 1 |
| `e44_certified_prime_gap` | Pour tout n, le gap sortant reconstruit depuis le canal complet des zéros égale gnat n. | CONFIRMÉE | V48 | 2 |
| `e44_certified_gap_has_grammar_lift` | Pour n >= 2, le gap reconstruit est 6k plus le résidu de transition (p n mod 6, p (n+1) mod 6) pour un certain k (relèvement métrique de la transition). | CONFIRMÉE (domaine : 2 <= n) | V174 | 1 |
| `E44GrammarArithmeticState.stage_pos` | Champ de E44GrammarArithmeticState : le stade est >= 1. | CONFIRMÉE | AJOUT | 0 |
| `E44GrammarArithmeticState.L_pos` | Champ de E44GrammarArithmeticState : L > 0. | CONFIRMÉE | AJOUT | 0 |
| `E44GrammarArithmeticState.L_lt_R` | Champ de E44GrammarArithmeticState : L < R. | CONFIRMÉE | AJOUT | 0 |
| `E44GrammarArithmeticState.certifiedPrime_eq` | Le premier certifié de l'état typé est p à l'indice primeIndex de l'état. | CONFIRMÉE | AJOUT | 0 |
| `E44GrammarArithmeticState.certifiedGap_eq` | Le gap certifié de l'état typé est gnat à l'indice primeIndex de l'état. | CONFIRMÉE | AJOUT | 0 |
| `E44GrammarArithmeticState.rowContribution_is_consecutive_prime_step` | La contribution de ligne de l'état est le terme résiduel du zéro de l'état en p (index+1) moins celui en p index (pas entre premiers consécutifs). | CONFIRMÉE | AJOUT | 0 |
| `E44GrammarArithmeticState.certifiedGap_has_grammar_lift` | Pour un état d'indice premier >= 2, le gap certifié est 6k plus le résidu de transition mod 6 pour un certain k. | CONFIRMÉE (domaine : 2 <= primeIndex) | V174 | 0 |
| `E44GrammarArithmeticState.recoveredDeltaPsi_exact` | Si L >= 2 et R >= 2 pour un état, l'incrément de ψ récupéré depuis les zéros égale ΔΨ de l'état. | CONFIRMÉE (domaine : 2 <= L, 2 <= R) | V48 | 0 |

### `RhGapCriterion.ExplicitFormulaBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `piCount_eq_primeCounting` | Pour tout n, piCount n est le comptage des nombres premiers de Mathlib (Nat.primeCounting). | CONFIRMÉE | AJOUT | 0 |
| `piReal_eq_primeCounting` | Pour tout réel x, piReal x est le comptage premier de la partie entière de x. | CONFIRMÉE | AJOUT | 1 |
| `primePowerWeight_zero` | primePowerWeight 0 = 0. | CONFIRMÉE | AJOUT | 2 |
| `primePowerWeight_one` | primePowerWeight 1 = 0. | CONFIRMÉE | AJOUT | 1 |
| `log_mul_primePowerWeight` | Pour tout n, log n fois primePowerWeight n égale la fonction de von Mangoldt en n. | CONFIRMÉE | AJOUT | 2 |
| `PiMangoldt_eq_PiWeighted` | Pour x >= 2, PiMangoldt x égale PiWeighted x avec troncature partie entière de log x / log 2. | CONFIRMÉE (domaine : x >= 2) | AJOUT | 3 |
| `PiMangoldt_eq_psi_abel_raw` | Pour x >= 2, PiMangoldt x = (1/log x) ψ(x) moins l'intégrale de 2 à x du noyau de dérivée de 1/log t contre ψ(t) (sommation d'Abel de ψ vers Π). | CONFIRMÉE (domaine : x >= 2) | AJOUT | 2 |
| `psi_eq_PiMangoldt_abel_raw` | Pour x >= 2, ψ(x) = log x fois PiMangoldt x moins l'intégrale de 2 à x de PiMangoldt t / t (Abel de Π vers ψ). | CONFIRMÉE (domaine : x >= 2) | AJOUT | 1 |
| `PiWeighted_eq_psi_abel_raw` | Pour x >= 2, PiWeighted x (troncature log x / log 2) égale (1/log x) ψ(x) moins l'intégrale du noyau contre ψ (Abel). | CONFIRMÉE (domaine : x >= 2) | AJOUT | 0 |

### `RhGapCriterion.HardyCayley`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `harmonic_head_tail_square_identity` | Pour tous réels h et dh, (dh+h/2)² − (h/2−dh)² = 2·h·dh (identité algébrique tête-queue). | CONFIRMÉE | AJOUT | 0 |
| `boundary_mode_rate_identity` | Pour tout réel σ, 1 + 2(σ−1) = 2σ−1 (égalité d'exposants). | CONFIRMÉE | AJOUT | 0 |
| `head_tail_gain_reciprocal` | Pour A et B non nuls, (A/B)·(B/A) = 1. | CONFIRMÉE (A et B non nuls) | AJOUT | 0 |
| `reciprocal_gain_defect` | Pour A et B non nuls, A/B + B/A − 2 = (A−B)²/(A·B). | CONFIRMÉE (A et B non nuls) | AJOUT | 2 |
| `reciprocal_gain_defect_nonneg` | Pour A et B strictement positifs, A/B + B/A − 2 ≥ 0. | CONFIRMÉE (A et B strictement positifs) | AJOUT | 0 |
| `cayley_symmetric_defect_numerator` | Pour tous réels σ et γ, (σ²+γ² − ((σ−1)²+γ²))² = (2σ−1)² (numérateur du défaut symétrique de Cayley). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Harmonic`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `harmonic_prime_jump_cancellation` | Pour p non nul, le correcteur q/p + B/2 est inchangé quand q devient q−l et B devient B+2l/p. | CONFIRMÉE (p non nul) | AJOUT | 0 |
| `harmonic_flux_square_identity` | Pour tous réels h et f, (h−f)² − f² = h² − 2hf. | CONFIRMÉE | AJOUT | 0 |
| `harmonic_block_energy_cascade` | Si chaque bloc n vérifie Eout n + boundary n = Ein n + boundary (n+1), la somme sur N blocs télescope : Σ Eout + boundary 0 = Σ Ein + boundary N. | CONFIRMÉE (domaine : bilan d'énergie vérifié à chaque bloc) | AJOUT | 0 |
| `subexponential_of_harmonic_output_and_boundary` | Si Eout et boundary sont sous-exponentielles et si Ein ≤ Eout + boundary pour U ≥ 0, alors Ein est sous-exponentielle. | CONFIRMÉE SOUS CONDITION (sortie et bord sous-exponentiels, inégalité de flux Ein ≤ Eout + boundary) | AJOUT | 0 |
| `cayley_norm_sq_difference` | Pour tous réels σ et γ, (σ²+γ²) − ((σ−1)²+γ²) = 2σ−1. | CONFIRMÉE | AJOUT | 0 |
| `cayley_expansive_iff_right_of_half` | Le multiplicateur de Cayley est expansif ((σ−1)²+γ² < σ²+γ²) si et seulement si σ > 1/2. | CONFIRMÉE | AJOUT | 0 |
| `cayley_unit_iff_on_half` | Les modules carrés σ²+γ² et (σ−1)²+γ² sont égaux si et seulement si σ = 1/2 (multiplicateur de Cayley isométrique sur la ligne critique). | CONFIRMÉE | AJOUT | 1 |
| `cayley_contracting_iff_left_of_half` | Le multiplicateur de Cayley est contractif (σ²+γ² < (σ−1)²+γ²) si et seulement si σ < 1/2. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.InvariantTransport`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `PrimeRelation16.enumList_getElem?_ctorIdx_eq` | Dans la liste d'énumération des 16 relations premières, l'élément d'indice ctorIdx de x est x. | CONFIRMÉE | AJOUT | 0 |
| `PrimeRelation16.enumList_nodup` | La liste d'énumération des 16 relations premières est sans doublon. | CONFIRMÉE | AJOUT | 0 |
| `PrimeRelation16.ofNat_ctorIdx` | ofNat inverse ctorIdx sur les relations premières à 16 constructeurs. | CONFIRMÉE | AJOUT | 0 |
| `PrimeState16.enumList_getElem?_ctorIdx_eq` | Dans la liste d'énumération des états premiers à 16 constructeurs, l'élément d'indice ctorIdx de x est x. | CONFIRMÉE | AJOUT | 0 |
| `PrimeState16.enumList_nodup` | La liste d'énumération des états premiers à 16 constructeurs est sans doublon. | CONFIRMÉE | AJOUT | 0 |
| `PrimeState16.ofNat_ctorIdx` | ofNat inverse ctorIdx sur les états premiers à 16 constructeurs. | CONFIRMÉE | AJOUT | 0 |
| `four_relations_complete16` | Pour toute paire d'états premiers (s,t), il existe une unique étiquette relationnelle de source s et de cible t. | CONFIRMÉE | AJOUT | 0 |
| `canonical_restriction_compatibility16` | Une position i déjà présente dans un périmètre N garde la même valeur de f dans tout périmètre M ≥ N (restriction canonique compatible). | CONFIRMÉE (périmètre N ≤ M) | AJOUT | 0 |
| `mapped_restriction_compatibility16` | Idem que la compatibilité de restriction, pour toute composante g∘f déterminée position par position. | CONFIRMÉE (périmètre N ≤ M) | AJOUT | 0 |
| `canonical_T_position_immutable16` | À une position donnée, la valeur cumulative canonique de a ne change pas quand le périmètre passe de N à M ≥ N. | CONFIRMÉE (périmètre N ≤ M) | AJOUT | 0 |
| `equality_transports_to_restrictions16` | Une égalité globale primeSide n = zeroSide n pour tout n est conservée par restriction aux périmètres N ≤ M. | CONFIRMÉE (domaine : égalité globale des deux représentations, périmètres emboîtés) | AJOUT | 0 |
| `extension_is_identity_on_known_positions16` | L'extension d'un périmètre N à M ≥ N laisse inchangées les valeurs aux positions déjà connues. | CONFIRMÉE (périmètre N ≤ M) | AJOUT | 0 |

### `RhGapCriterion.InverseSignatureConcrete`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `InverseSignatureConcrete.canonical_meta_arithmetically_defined` | La suite canonique des positions premières p est la fonction n ↦ Nat.nth Nat.Prime n. | CONFIRMÉE | AJOUT | 0 |
| `InverseSignatureConcrete.spectral_meta_independently_defined` | La suite de positions reconstruite depuis les zéros est par définition posOfCount appliquée à zerosPrimeCount. | CONFIRMÉE | AJOUT | 0 |
| `InverseSignatureConcrete.exact_meta_reconstruction_identity` | Position, écart et comptage reconstruits depuis les zéros coïncident exactement avec la position première p, l'écart gnat et le comptage piCount. | CONFIRMÉE | V47,V48,V49 | 0 |
| `InverseSignatureConcrete.central_implies_canonical_signature` | Si ρ est central (partie réelle 1/2), alors ρ satisfait la signature arithmétique canonique à toute échelle U. | CONFIRMÉE (domaine : centralité de ρ) | AJOUT | 0 |
| `InverseSignatureConcrete.canonical_signature_implies_re_le_half` | Pour un zéro non trivial ρ, la signature arithmétique canonique à l'échelle U entraîne Re ρ ≤ 1/2. | CONFIRMÉE (domaine : signature canonique satisfaite) | AJOUT | 0 |
| `InverseSignatureConcrete.signature_iff_re_le_half` | Pour un zéro non trivial ρ et toute échelle U, la signature arithmétique canonique équivaut à Re ρ ≤ 1/2. | CONFIRMÉE | AJOUT | 0 |
| `InverseSignatureConcrete.weak_grammar_signature_holds_regardless_of_real_part` | Pour tout zéro non trivial ρ et toute famille grammaticale F dont le résidu spectral a une coordonnée de cobord nulle, la signature faible de grammaire tient à toute échelle U, sans usage de Re ρ. | CONFIRMÉE (domaine : coordonnée de cobord du résidu spectral nulle) | AJOUT | 0 |

### `RhGapCriterion.InverseSignaturePrototype`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `InverseSignaturePrototype.closure_from_exact_signature` | Si la méta-donnée reconstruite depuis ρ est la méta-donnée canonique, qu'elle satisfait la signature et que la signature force la centralité, alors ρ est central. | CONFIRMÉE (domaine : méta reconstruite égale à la canonique, signature de la canonique, signature implique centralité) | AJOUT | 0 |
| `InverseSignaturePrototype.global_closure_from_exact_signature` | Version quantifiée : si tout point admissible reconstruit la méta canonique, qu'elle satisfait la signature et que la signature force la centralité, alors tout point admissible est central. | CONFIRMÉE (domaine : reconstruction canonique pour tout admissible, signature canonique, signature implique centralité) | AJOUT | 0 |
| `InverseSignaturePrototype.target_signature_equivalence` | Si Central implique Signature et Signature implique Central, alors Central équivaut à Signature pour ρ. | CONFIRMÉE (domaine : les deux implications fournies) | AJOUT | 0 |

### `RhGapCriterion.LiZeroSideAmplification`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `liBase_eq_sub_div` | Pour ρ non nul, la base de Li vaut (ρ−1)/ρ. | CONFIRMÉE (ρ non nul) | AJOUT | 1 |
| `liBase_normSq_formula` | Pour ρ non nul, le module carré de la base de Li vaut ((Re ρ−1)²+(Im ρ)²)/((Re ρ)²+(Im ρ)²). | CONFIRMÉE (ρ non nul) | AJOUT | 2 |
| `liBase_normSq_eq_one_iff` | Pour ρ non nul, le module carré de la base de Li vaut 1 si et seulement si Re ρ = 1/2. | CONFIRMÉE (ρ non nul) | AJOUT | 1 |
| `liBase_norm_eq_one_iff` | Pour ρ non nul, la norme de la base de Li vaut 1 si et seulement si Re ρ = 1/2. | CONFIRMÉE (ρ non nul) | AJOUT | 0 |
| `one_lt_liBase_normSq_iff` | Pour ρ non nul, le module carré de la base de Li dépasse 1 si et seulement si Re ρ < 1/2. | CONFIRMÉE (ρ non nul) | AJOUT | 1 |
| `one_lt_liBase_norm_iff` | Pour ρ non nul, la norme de la base de Li dépasse 1 si et seulement si Re ρ < 1/2. | CONFIRMÉE (ρ non nul) | AJOUT | 1 |
| `reflected_pair_has_expanding_liBase` | Pour ρ différent de 0 et 1 et Re ρ ≠ 1/2, l'une des deux bases de Li de ρ et 1−ρ est de norme strictement supérieure à 1. | CONFIRMÉE (domaine : ρ hors de 0, 1 et de la ligne critique) | AJOUT | 1 |
| `isNontrivialZetaZero_one_sub` | Si ρ est un zéro non trivial de zêta, 1−ρ l'est aussi (réflexion de l'équation fonctionnelle). | CONFIRMÉE (domaine : ρ zéro non trivial) | V62,V63 | 2 |
| `nontrivialZetaZero_ne_zero` | Un zéro non trivial de zêta est différent de 0. | CONFIRMÉE (domaine : ρ zéro non trivial) | V7 | 1 |
| `nontrivialZetaZero_ne_one` | Un zéro non trivial de zêta est différent de 1. | CONFIRMÉE (domaine : ρ zéro non trivial) | V7 | 1 |
| `off_critical_zero_has_expanding_liBase` | Si un zéro non trivial est hors de la ligne critique, il existe un zéro non trivial dont la base de Li est de norme strictement supérieure à 1. | CONFIRMÉE SOUS CONDITION (zéro hors de la ligne critique) | AJOUT | 1 |
| `off_critical_zero_has_divergent_liBase_powers` | Si un zéro non trivial est hors de la ligne critique, il existe un zéro non trivial dont les puissances de la norme de la base de Li tendent vers l'infini. | CONFIRMÉE SOUS CONDITION (zéro hors de la ligne critique) | AJOUT | 0 |
| `liBase_conj` | La base de Li du conjugué de ρ est le conjugué de la base de Li de ρ. | CONFIRMÉE | AJOUT | 2 |
| `one_sub_eq_conj_of_re_eq_half` | Si Re ρ = 1/2, alors 1−ρ est le conjugué complexe de ρ. | CONFIRMÉE SOUS CONDITION (ρ sur la ligne critique) | V77 | 2 |
| `liBase_reflection_eq_inv` | Pour ρ différent de 0 et de 1, la base de Li de 1−ρ est l'inverse multiplicatif de celle de ρ. | CONFIRMÉE (ρ différent de 0 et de 1) | AJOUT | 2 |
| `liBase_inv_eq_conj_of_re_eq_half` | Si Re ρ = 1/2 et ρ différent de 0 et 1, l'inverse de la base de Li est son conjugué. | CONFIRMÉE SOUS CONDITION (ρ sur la ligne critique) | AJOUT | 0 |
| `liZeroTerm_reflected_pair` | Pour ρ différent de 0 et 1, la contribution de Li d'ordre n de ρ plus celle de 1−ρ vaut 2 − b^n − (b⁻¹)^n où b est la base de Li de ρ. | CONFIRMÉE (ρ différent de 0 et de 1) | AJOUT | 0 |
| `liZeroTerm_reflected_pair_on_critical_line` | Si Re ρ = 1/2, la contribution de Li de la paire ρ, 1−ρ est celle de ρ plus son conjugué. | CONFIRMÉE SOUS CONDITION (ρ sur la ligne critique) | AJOUT | 0 |

### `RhGapCriterion.MasterLeanE58TotalTripleRoute`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260901.functionalMirror_gamma` | La hauteur (Gamma) du miroir fonctionnel d'un zéro non trivial égale celle du zéro. | CONFIRMÉE | V65 | 1 |
| `ScientificRebuild20260901.functionalMirror_beta` | La partie réelle (Beta) du miroir fonctionnel d'un zéro non trivial vaut 1 moins celle du zéro. | CONFIRMÉE | V65 | 0 |
| `ScientificRebuild20260901.ZeroPassage.ordered` | Pour un passage de zéros, la hauteur de gauche est strictement inférieure à celle de droite, ou égale avec partie réelle de gauche strictement inférieure (ordre hauteur puis partie réelle). | CONFIRMÉE | V8 | 0 |
| `ScientificRebuild20260901.ThreeZeroWindow.order01` | Dans une fenêtre de trois zéros, z0 précède z1 dans l'ordre hauteur puis partie réelle. | CONFIRMÉE | V8 | 0 |
| `ScientificRebuild20260901.ThreeZeroWindow.order12` | Dans une fenêtre de trois zéros, z1 précède z2 dans l'ordre hauteur puis partie réelle. | CONFIRMÉE | V8 | 0 |
| `ScientificRebuild20260901.ThreeZeroWindow.leftPassage_heightGap` | L'écart de hauteur du passage de gauche d'une fenêtre de trois zéros est l'écart de gauche de la fenêtre. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.ThreeZeroWindow.rightPassage_heightGap` | L'écart de hauteur du passage de droite d'une fenêtre de trois zéros est l'écart de droite de la fenêtre. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.TrueMemberContactCell.stage_pos` | Le nombre d'étapes d'une cellule de contact d'un vrai zéro est au moins 1. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260901.TrueMemberContactCell.contacts_length` | La liste des contacts d'une cellule de contact d'un vrai zéro a exactement deux éléments. | CONFIRMÉE | V20 | 0 |
| `ScientificRebuild20260901.TrueMemberContactCell.contactPair_fst` | La première composante de la paire de contacts est l'échelle gauche de la cellule. | CONFIRMÉE | V26 | 0 |
| `ScientificRebuild20260901.TrueMemberContactCell.contactPair_snd` | La seconde composante de la paire de contacts est l'échelle droite de la cellule. | CONFIRMÉE | V26 | 0 |
| `ScientificRebuild20260901.TrueMemberContactCell.recoversGamma` | Les deux contacts et le nombre d'étapes d'une cellule redonnent exactement la hauteur du zéro par la formule de récupération e44. | CONFIRMÉE | V45 | 0 |
| `ScientificRebuild20260901.TrueMemberContactCell.recoversBeta` | Les deux contacts et le nombre d'étapes d'une cellule redonnent exactement la partie réelle du zéro par la formule tangente e44. | CONFIRMÉE | V45 | 0 |
| `ScientificRebuild20260901.TrueMemberContactCell.contactWidth` | La largeur e44 entre les deux contacts vaut le nombre d'étapes fois π divisé par la hauteur du zéro. | CONFIRMÉE | V17 | 1 |
| `ScientificRebuild20260901.offMirror_leftContact_ne` | Pour un zéro de hauteur strictement positive et de partie réelle différente de 1/2, le contact gauche de tangente de ρ diffère de celui de son miroir fonctionnel pour toute branche. | CONFIRMÉE SOUS CONDITION (hauteur positive, zéro hors de la ligne critique) | V163 | 1 |
| `ScientificRebuild20260901.offMirror_rightContact_ne` | Pour un zéro de hauteur strictement positive et de partie réelle différente de 1/2, le contact droit d'étape stage de ρ diffère de celui de son miroir fonctionnel, pour toute branche. | CONFIRMÉE SOUS CONDITION (hauteur positive, zéro hors de la ligne critique) | V163 | 1 |
| `ScientificRebuild20260901.offMirror_contactPair_deformation` | Pour un zéro de hauteur positive hors de la ligne critique, les deux contacts de sa cellule diffèrent de ceux de son miroir, tandis que la largeur e44 entre les contacts reste la même. | CONFIRMÉE SOUS CONDITION (hauteur positive, zéro hors de la ligne critique) | V163,V17 | 0 |
| `ScientificRebuild20260901.offMirror_zeroHeightGap_but_lossless` | Pour un zéro hors de la ligne critique, l'écart de hauteur entre le zéro et son miroir est nul, et l'écart transformé sur l'arête première n n'est jamais (0,0). | CONFIRMÉE SOUS CONDITION (zéro hors de la ligne critique) | V66 | 0 |
| `ScientificRebuild20260901.off_creates_actual_ordered_zeroPassage` | Pour un zéro de hauteur strictement positive, inférieure en valeur absolue à H et de partie réelle différente de 1/2, la liste des écarts de constellation de hauteur H contient un écart nul. | CONFIRMÉE SOUS CONDITION (hauteur positive bornée par H, zéro hors de la ligne critique) | V66 | 0 |
| `ScientificRebuild20260901.towerSpan_sub` | La différence des envergures de Tour entre deux hauteurs T1 et T0 sur l'arête n vaut (T1−T0)/π fois la largeur logarithmique canonique de l'arête première n. | CONFIRMÉE | V17 | 1 |
| `ScientificRebuild20260901.towerSpanDifference_eq_zero_iff` | La différence des envergures de Tour entre deux hauteurs T1 et T0 sur l'arête n est nulle si et seulement si T1 = T0. | CONFIRMÉE | V17 | 0 |
| `ScientificRebuild20260901.PrimeEventEnvironment.predecessor_lt_pivot` | Dans un environnement d'événement premier, le prédécesseur p(k) est strictement inférieur au pivot p(k+1). | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260901.PrimeEventEnvironment.pivot_lt_successor` | Dans un environnement d'événement premier, le pivot p(k+1) est strictement inférieur au successeur p(k+2). | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260901.PrimeEventEnvironment.incomingGap_pos` | L'écart entrant (pivot moins prédécesseur) d'un environnement d'événement premier est strictement positif. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.PrimeEventEnvironment.outgoingGap_pos` | L'écart sortant (successeur moins pivot) d'un environnement d'événement premier est strictement positif. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.PrimeEventEnvironment.occurrences_ne` | Les occurrences de transition entrante et sortante d'un environnement d'événement premier sont distinctes. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.PrimeEventEnvironment.incoming_vonMangoldt_lock` | La transition reconstruite depuis les zéros à la position eventStart est exactement l'occurrence de transition canonique entrante. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260901.PrimeEventEnvironment.outgoing_vonMangoldt_lock` | La transition reconstruite depuis les zéros à la position eventStart+1 est exactement l'occurrence de transition canonique sortante. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260901.threeZero_twoGap_tower_prime_rigidity` | Pour toute fenêtre de trois zéros et tout n, la rigidité de transition triple (verrou des paires de transitions, écarts et largeurs logarithmiques positifs, lois d'envergure) tient pour les trois hauteurs. | CONFIRMÉE | V17 | 0 |
| `ScientificRebuild20260901.threeZero_twoGap_span_laws` | Pour toute fenêtre de trois zéros, la différence d'envergure de Tour entre z1 et z0 (arête n) et entre z2 et z1 (arête n+1) vaut l'écart correspondant sur π fois la largeur logarithmique de l'arête. | CONFIRMÉE | V17 | 0 |
| `ScientificRebuild20260901.master_has_exactly_99_constraints` | La liste allConstraints contient exactement 99 contraintes. | HORS STANDARD (RhGap.ScientificRebuild20260828.allConstraints_length._native.native_decide.ax_1_1) | AJOUT | 0 |
| `ScientificRebuild20260901.master_99_constraints_nodup` | La liste allConstraints des 99 contraintes est sans doublon. | HORS STANDARD (RhGap.ScientificRebuild20260828.allConstraints_nodup._native.native_decide.ax_1_1) | AJOUT | 0 |
| `ScientificRebuild20260901.master_has_exactly_99_evidence_rows` | La liste des lignes de preuve associées aux contraintes a exactement 99 éléments. | HORS STANDARD (RhGap.ScientificRebuild20260828.constraintEvidenceCoverage_length._native.native_decide.ax_1_1) | AJOUT | 0 |

### `RhGapCriterion.Mellin`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `subexponential_of_le_two_add_polynomial` | Si E est sous-exponentielle, R à croissance polynomiale et H ≤ 2E + 2R pour U ≥ 0, alors H est sous-exponentielle. | CONFIRMÉE SOUS CONDITION (E sous-exponentielle, R polynomiale, majoration H ≤ 2E+2R) | AJOUT | 1 |
| `critical_pointwise_bound_to_local_energy` | Sur [a,b] avec 0<a≤b, si la valeur absolue de Q t est majorée par M·√t·L et Q²/t² est intégrable, alors l'intégrale de Q²/t² est majorée par M²·L²·log(b/a). | CONFIRMÉE (domaine : borne ponctuelle sur Q, intégrabilité) | AJOUT | 1 |
| `exists_admissible_mellin_epsilon` | Pour toute abscisse σ > 1/2, il existe ε > 0 avec ε < 2σ−1. | CONFIRMÉE (σ > 1/2) | AJOUT | 3 |
| `mellin_block_exponent_negative` | Si ε < 2σ−1, alors (ε+1−2σ)/2 < 0. | CONFIRMÉE (ε < 2σ−1) | AJOUT | 3 |
| `mellin_block_decay_iff_zero_free_threshold` | Pour tous a et σ, (a+1−2σ)/2 < 0 si et seulement si (a+1)/2 < σ. | CONFIRMÉE | AJOUT | 0 |
| `mellin_threshold_margin` | Pour δ > 0, (a+1−2((a+1)/2+δ))/2 = −δ. | CONFIRMÉE (δ > 0) | AJOUT | 0 |
| `theoremG_RH_from_mellin_rigidity` | Pour un ensemble Z de complexes stable par ρ↦1−ρ, si Z vérifie l'exclusion de Mellin à droite pour une énergie E sous-exponentielle, tout ρ de Z a partie réelle 1/2. | IMPLIQUE RH SOUS PRÉMISSE (exclusion de Mellin à droite du demi-plan pour Z avec énergie E sous-exponentielle, Z stable par ρ↦1−ρ) | AJOUT | 0 |

### `RhGapCriterion.MemberwiseHeightInverseContradiction`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `injOn_of_leftInverse_on_heightConstellation` | Si Psi est inverse à gauche de Phi sur la constellation des zéros de hauteur T, alors Phi est injective sur cette constellation. | CONFIRMÉE SOUS CONDITION (inverse à gauche de Phi sur la constellation de hauteur T) | AJOUT | 1 |
| `no_offline_of_heightDetermined_leftInverse` | Si Phi est déterminée par la hauteur et possède un inverse à gauche vrai sur la constellation de hauteur T, il n'existe aucun zéro hors ligne dans cette constellation. | RÉFUTATION COMPILÉE (existence d'un zéro hors ligne dans la constellation, sous application déterminée par la hauteur avec inverse à gauche) | V162 | 3 |
| `no_offline_of_heightDetermined_primePlacement_leftInverse` | Spécialisation à des placements dans ℕ : une application vers ℕ déterminée par la hauteur avec inverse à gauche vrai sur la constellation de hauteur T exclut tout zéro hors ligne dans cette constellation. | RÉFUTATION COMPILÉE (existence d'un zéro hors ligne dans la constellation, sous placement premier déterminé par la hauteur avec inverse à gauche) | V162 | 0 |

### `RhGapCriterion.OfflineOrbitModeTraceability`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `offlineOrbitPsiRecovered_eq_offlineOrbitPsiFromMode` | Pour un zéro non trivial ρ et t ≥ 2, offlineOrbitPsiRecovered coïncide avec offlineOrbitPsiFromMode. | CONFIRMÉE (domaine : ρ zéro non trivial, t ≥ 2) | AJOUT | 1 |
| `offlineOrbitWeightedPart_eq_fromMode` | Pour un zéro non trivial ρ et x ≥ 2, offlineOrbitWeightedPart égale offlineOrbitWeightedFromMode. | CONFIRMÉE (domaine : ρ zéro non trivial, x ≥ 2) | AJOUT | 1 |
| `offlineOrbitPrimeCountPart_eq_fromMode` | Pour un zéro non trivial ρ et x ≥ 2, offlineOrbitPrimeCountPart égale offlineOrbitPrimeCountFromMode. | CONFIRMÉE (domaine : ρ zéro non trivial, x ≥ 2) | AJOUT | 1 |
| `offlineOrbitThetaPart_traceable_to_offlineOrbitMode` | Pour un zéro non trivial ρ et x ≥ 2, offlineOrbitThetaPart égale offlineOrbitThetaFromMode, donc ne dépend que du mode d'orbite de ρ. | CONFIRMÉE (domaine : ρ zéro non trivial, x ≥ 2) | AJOUT | 1 |
| `offlineOrbitMode_eq_offlineOrbitModeFromP5` | Pour un zéro non trivial ρ et tout U, offlineOrbitMode ρ U égale offlineOrbitModeFromP5 ρ U. | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 1 |
| `offlineOrbitPsiFromMode_eq_offlineOrbitPsiFromP5` | Pour un zéro non trivial ρ et tout t, offlineOrbitPsiFromMode ρ t égale offlineOrbitPsiFromP5 ρ t. | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 1 |
| `offlineOrbitWeightedFromMode_eq_offlineOrbitWeightedFromP5` | Pour un zéro non trivial ρ et tout x, offlineOrbitWeightedFromMode ρ x égale offlineOrbitWeightedFromP5 ρ x. | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 1 |
| `offlineOrbitPrimeCountFromMode_eq_offlineOrbitPrimeCountFromP5` | Pour un zéro non trivial ρ et tout x, offlineOrbitPrimeCountFromMode ρ x égale offlineOrbitPrimeCountFromP5 ρ x. | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 1 |
| `offlineOrbitThetaFromMode_eq_offlineOrbitThetaFromP5` | Pour un zéro non trivial ρ et tout x, offlineOrbitThetaFromMode ρ x égale offlineOrbitThetaFromP5 ρ x. | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 1 |
| `offlineOrbitThetaPart_traceable_to_P5_projectors` | Pour un zéro non trivial ρ et x ≥ 2, offlineOrbitThetaPart égale offlineOrbitThetaFromP5, donc ne dépend que des deux canaux projetés P5 de ρ et de son conjugué. | CONFIRMÉE (domaine : ρ zéro non trivial, x ≥ 2) | AJOUT | 1 |

### `RhGapCriterion.OfflineZeroIncompatibility`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `offline_zero_orbit_contribution` | Si ρ est un zéro non trivial, son conjugué l'est aussi, avec la même multiplicité, et cette multiplicité est au moins 1. | CONFIRMÉE (domaine : ρ zéro non trivial) | V63 | 0 |
| `offline_zero_channel_eq_zeroMode` | Pour tout zéro non trivial ρ, le terme individuel de ρ dans la formule explicite lissée, remis à l'échelle par exp(−U/2), est exactement le mode zeroMode ρ (offlineZeroAmplitude ρ) en U. | CONFIRMÉE | V157,V172 | 4 |
| `offline_zero_mode_amplitude_ne_zero` | Pour un zéro non trivial ρ avec Re ρ > 1/2, l'amplitude offlineZeroAmplitude ρ est non nulle. | CONFIRMÉE SOUS CONDITION (ρ zéro non trivial avec Re ρ > 1/2) | AJOUT | 5 |
| `round23_global_prime_positions_corollary` | Pour tout n, la position première reconstruite depuis les zéros zerosPrimePosition n égale p n. | CONFIRMÉE | V48 | 0 |
| `round23_global_prime_gaps_corollary` | Pour tout n, l'écart premier reconstruit depuis les zéros zerosPrimeGap n égale gnat n. | CONFIRMÉE | V48 | 0 |
| `round22_global_total_mode_partition_corollary` | Pour 1 ≤ a ≤ b, la somme sur les classes 0, 2, 4 modulo 6 de (g n − log p n) sur [a,b[ vaut Tmode b − Tmode a. | CONFIRMÉE (domaine : 1 ≤ a ≤ b) | AJOUT | 0 |
| `offline_zero_forces_exponential_scale_growth` | Pour un zéro non trivial ρ avec Re ρ > 1/2, la norme du mode isolé de ρ croît exponentiellement au taux exact Re ρ − 1/2. | CONFIRMÉE SOUS CONDITION (ρ zéro non trivial avec Re ρ > 1/2) | V102 | 0 |
| `exact_metapattern_excludes_exponential_scale_growth` | Pour un zéro non trivial ρ avec Re ρ > 1/2, une décomposition WT = mode de ρ + R avec WT sous-exponentielle en norme et R sans annulation de fenêtre au taux Re ρ mène à False. | RÉFUTATION COMPILÉE (existence conjointe d'un zéro hors ligne, d'une fenêtre WT sous-exponentielle et d'un reste R sans annulation) | V102 | 2 |
| `offline_zero_incompatible_with_exact_prime_gap_metapattern_conditional` | Même énoncé que exact_metapattern_excludes_exponential_scale_growth : zéro hors ligne avec Re ρ > 1/2, WT sous-exponentielle et reste R sans annulation, mène à False. | RÉFUTATION COMPILÉE (existence conjointe d'un zéro hors ligne, d'une fenêtre WT sous-exponentielle et d'un reste R sans annulation) | V102 | 0 |
| `explicitFormulaZeroModeAmplitude_eq_add_one_mul_offlineZeroAmplitude` | Pour tout zéro non trivial ρ, l'amplitude P5 non lissée vaut (ρ+1) fois l'amplitude lissée offlineZeroAmplitude. | CONFIRMÉE | AJOUT | 2 |
| `offlineZeroAmplitude_eq_inv_add_one_mul_explicitFormulaZeroModeAmplitude` | Pour tout zéro non trivial ρ, l'amplitude lissée offlineZeroAmplitude vaut (ρ+1)⁻¹ fois l'amplitude P5 non lissée. | CONFIRMÉE | AJOUT | 1 |
| `smoothed_zeroMode_eq_inv_add_one_mul_P5_zeroMode` | Pour tout zéro non trivial ρ et tout U, le mode lissé de ρ vaut (ρ+1)⁻¹ fois le mode P5 non lissé. | CONFIRMÉE | AJOUT | 3 |
| `P5_zeroMode_eq_add_one_mul_smoothed_zeroMode` | Pour tout zéro non trivial ρ et tout U, le mode P5 non lissé vaut (ρ+1) fois le mode lissé. | CONFIRMÉE | AJOUT | 0 |
| `smoothed_formula_projected_channel_eq_zeroMode` | Pour tout zéro non trivial ρ et tout U, le canal projeté de la formule lissée égale le mode lissé de ρ. | CONFIRMÉE | AJOUT | 1 |
| `residue_unsmoothed_eq_add_one_mul_residue_smoothed` | Pour x > 0 et tout zéro non trivial ρ, le résidu de l'intégrande de Perron non lissé en ρ vaut (ρ+1) fois celui de l'intégrande lissé. | CONFIRMÉE (x > 0) | AJOUT | 1 |
| `explicitFormulaProjectedChannel_eq_add_one_mul_smoothed` | Pour tout zéro non trivial ρ et tout U, le canal projeté P5 non lissé vaut (ρ+1) fois le canal projeté lissé. | CONFIRMÉE | AJOUT | 1 |
| `smoothedFormulaProjectedChannel_eq_inv_add_one_mul_P5` | Pour tout zéro non trivial ρ et tout U, le canal projeté lissé vaut (ρ+1)⁻¹ fois le canal projeté P5. | CONFIRMÉE | AJOUT | 0 |
| `smoothedFormulaProjectedChannel_eq_inv_add_one_mul_P5_via_zeroMode` | Même énoncé que smoothedFormulaProjectedChannel_eq_inv_add_one_mul_P5, obtenu par composition des identités de mode (contrôle croisé). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.OfflineZeroOrbitDecomposition`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `activeOfflineOrbitMobiusTerm.congr_simp` | Lemme de congruence : à ρ égal, m égal et t égal, le terme de Möbius d'orbite active est égal. | CONFIRMÉE | AJOUT | 0 |
| `offlineOrbitPrimitivePart.congr_simp` | Lemme de congruence : à ρ égal et x égal, offlineOrbitPrimitivePart est égal. | CONFIRMÉE | AJOUT | 0 |
| `offlineOrbitPsiRecovered.congr_simp` | Lemme de congruence : à ρ égal et t égal, offlineOrbitPsiRecovered est égal. | CONFIRMÉE | AJOUT | 0 |
| `offlineRestPsiRecovered.congr_simp` | Lemme de congruence : à ρ égal et t égal, offlineRestPsiRecovered est égal. | CONFIRMÉE | AJOUT | 0 |
| `offline_zero_orbit_rest_tsum_decomposition` | Pour x > 1 et un zéro non trivial ρ, la somme des termes résiduels sur tous les zéros non triviaux se scinde exactement en somme sur l'orbite {ρ, conjugué} plus somme sur le complémentaire. | CONFIRMÉE (domaine : x > 1, ρ zéro non trivial) | AJOUT | 3 |
| `offline_zero_Pi_orbit_rest_decomposition` | Pour x > 1 et un zéro non trivial ρ, la somme de von Mangoldt lissée égale x/2 plus les termes de pôle et des zéros triviaux, plus la somme sur l'orbite de ρ, plus la somme sur le reste des zéros non triviaux. | CONFIRMÉE (domaine : x > 1, ρ zéro non trivial) | V121 | 1 |
| `offlineZeroOrbitFinset_sum_of_im_ne_zero` | Si ρ est un zéro non trivial de partie imaginaire non nulle, la somme des termes résiduels sur l'orbite est le terme de ρ plus celui de son conjugué. | CONFIRMÉE (domaine : ρ zéro non trivial de partie imaginaire non nulle) | V101 | 2 |
| `zerosPrimeCountReal_orbit_rest_of_weighted_split` | Si le comptage pondéré des zéros se scinde en partie orbite et partie reste aux points x^(1/m), alors zerosPrimeCountReal x se scinde par inversion de Möbius finie en deux sommes correspondantes. | CONFIRMÉE (domaine : scission orbite plus reste du comptage pondéré aux points x^(1/m)) | AJOUT | 2 |
| `offline_zero_channel_decomposition` | Pour tout ρ et tout U, le canal zéro zeroChannel U égale le mode isolé de ρ plus le reste zeroChannelRemainder ρ U. | CONFIRMÉE | AJOUT | 2 |
| `offline_zero_channel_decomposition_instantiates_hdecomp` | Même énoncé : zeroChannel U égale le mode isolé de ρ plus zeroChannelRemainder ρ U, pour tout ρ et U. | CONFIRMÉE | AJOUT | 0 |
| `offline_zero_channel_incompatible_conditional` | Pour un zéro non trivial ρ avec Re ρ > 1/2, si zeroChannel est sous-exponentiel en norme et si le reste zeroChannelRemainder ρ est sans annulation de fenêtre au taux Re ρ, on obtient False. | RÉFUTATION COMPILÉE (existence conjointe d'un zéro hors ligne, d'un canal sous-exponentiel et d'un reste sans annulation) | V102 | 0 |
| `offline_zero_channel_orbit_rest_expansion_of_im_ne_zero` | Pour ρ non trivial de partie imaginaire non nulle et U > 0, le reste du canal vaut le mode du conjugué de ρ plus exp(−U/2) fois la somme sur les zéros hors de l'orbite. | CONFIRMÉE (domaine : ρ zéro non trivial de partie imaginaire non nulle, U > 0) | AJOUT | 1 |
| `intervalIntegrable_kernel_mul_floor_comp` | Sur [a,b], si K est continue et F une suite réelle quelconque, t ↦ K t · F(⌊t⌋) est intégrable sur l'intervalle. | CONFIRMÉE (domaine : a ≤ b, K continue sur [a,b]) | AJOUT | 5 |
| `intervalIntegrable_kernel_mul_floor_continuous_comp` | Sur [a,b], si K et φ sont continues, t ↦ K t · F(⌊φ t⌋) est intégrable sur l'intervalle. | CONFIRMÉE (domaine : a ≤ b, K et φ continues sur [a,b]) | AJOUT | 2 |
| `offline_zero_primitive_orbit_rest_decomposition` | Pour x > 1 et un zéro non trivial ρ, smoothedZeroPrimitive x se scinde exactement en partie orbite plus partie reste. | CONFIRMÉE (domaine : x > 1, ρ zéro non trivial) | AJOUT | 1 |
| `offline_zero_psi_recovered_orbit_rest_decomposition` | Pour t ≥ 2 et un zéro non trivial ρ, psiRecoveredFromZeros t se scinde exactement en partie orbite plus partie reste. | CONFIRMÉE (domaine : t ≥ 2, ρ zéro non trivial) | V121 | 1 |
| `offlineOrbitWeightedKernel_continuousOn` | Pour x ≥ 2, le noyau t ↦ −t⁻¹/(log t)² est continu sur [2,x]. | CONFIRMÉE (x ≥ 2) | AJOUT | 3 |
| `intervalIntegrable_offlineOrbitWeightedKernel` | Pour x ≥ 2 et un zéro non trivial ρ, le noyau d'orbite pondéré fois la partie réelle de offlineOrbitPsiRecovered est intégrable sur [2,x]. | CONFIRMÉE (domaine : x ≥ 2, ρ zéro non trivial) | AJOUT | 1 |
| `continuousOn_offlineOrbitWeightedPrimitive` | Pour x ≥ 2 et un zéro non trivial ρ, la primitive pondérée d'orbite est continue sur [2,x]. | CONFIRMÉE (domaine : x ≥ 2, ρ zéro non trivial) | AJOUT | 1 |
| `rpow_one_div_ge_two_of_pow_le` | Si m ≥ 1 et 2^m ≤ t, alors t^(1/m) ≥ 2. | CONFIRMÉE (m ≥ 1, 2^m ≤ t) | AJOUT | 2 |
| `rpow_one_div_le_of_le` | Si 1 ≤ t ≤ x et m ≥ 1, alors t^(1/m) ≤ x. | CONFIRMÉE (1 ≤ t ≤ x, m ≥ 1) | AJOUT | 2 |
| `intervalIntegrable_inv_mul_offlineOrbitWeightedPart_rpow` | Pour x ≥ 2, m dans la coupure canonique et un zéro non trivial ρ, t ↦ t⁻¹·offlineOrbitWeightedPart(t^(1/m)) est intégrable sur [2^m, x]. | CONFIRMÉE (domaine : x ≥ 2, m dans la coupure canonique, ρ zéro non trivial) | AJOUT | 1 |
| `intervalIntegrable_inv_mul_activeOfflineOrbitMobiusTerm` | Pour x ≥ 2, m dans la coupure canonique et un zéro non trivial ρ, t ↦ t⁻¹·activeOfflineOrbitMobiusTerm est intégrable sur [2,x]. | CONFIRMÉE (domaine : x ≥ 2, m dans la coupure canonique, ρ zéro non trivial) | AJOUT | 1 |
| `offline_zero_weighted_count_orbit_rest_decomposition` | Pour x ≥ 2 et un zéro non trivial ρ, zerosWeightedCount x égale la partie orbite plus la partie reste. | CONFIRMÉE (domaine : x ≥ 2, ρ zéro non trivial) | AJOUT | 1 |
| `offline_zero_prime_count_orbit_rest_decomposition` | Pour x ≥ 2 et un zéro non trivial ρ, zerosPrimeCountReal x se scinde par Möbius en somme finie de parties orbite et de parties reste. | CONFIRMÉE (domaine : x ≥ 2, ρ zéro non trivial) | AJOUT | 1 |
| `offlineZeroAmplitude_conj` | Pour un zéro non trivial ρ, l'amplitude du mode isolé du conjugué de ρ est le conjugué de celle de ρ. | CONFIRMÉE (domaine : ρ zéro non trivial) | V101 | 1 |
| `offlineZeroAmplitude_conj_norm` | Pour un zéro non trivial ρ, les amplitudes de ρ et de son conjugué ont la même norme. | CONFIRMÉE (domaine : ρ zéro non trivial) | V101 | 1 |
| `offline_zero_orbit_energy_eq` | Pour un zéro non trivial ρ, l'énergie quadratique de l'orbite vaut 2·(norme de l'amplitude)²·exp(2(Re ρ − 1/2)U). | CONFIRMÉE (domaine : ρ zéro non trivial) | V102 | 2 |
| `offline_zero_orbit_energy_pos` | Pour un zéro non trivial ρ avec Re ρ > 1/2, l'énergie quadratique de l'orbite est strictement positive pour tout U. | CONFIRMÉE SOUS CONDITION (ρ zéro non trivial avec Re ρ > 1/2) | AJOUT | 0 |
| `smoothed_zeroMode_norm_sq_eq_P5_norm_sq_div` | Pour tout zéro non trivial ρ et tout U, le carré de la norme du mode lissé vaut celui du mode P5 divisé par ‖ρ+1‖². | CONFIRMÉE | AJOUT | 1 |
| `offlineOrbitEnergy_eq_weighted_P5_projection_energy` | Pour un zéro non trivial ρ, l'énergie de l'orbite égale la somme des carrés des normes des deux canaux projetés P5 de ρ et de son conjugué, chacun divisé par ‖ρ'+1‖². | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 1 |
| `offline_zero_orbit_mode_eq_orbit_finset_sum_of_im_ne_zero` | Pour un zéro non trivial ρ de partie imaginaire non nulle, le mode d'orbite égale exp(−U/2) fois la somme des termes résiduels sur l'orbite en exp U. | CONFIRMÉE (domaine : ρ zéro non trivial de partie imaginaire non nulle) | AJOUT | 2 |
| `offline_zero_orbit_mode_eq_orbit_finset_sum` | Pour un zéro non trivial ρ, le mode d'orbite égale exp(−U/2) fois la somme des termes résiduels sur l'orbite en exp U (sans hypothèse sur la partie imaginaire). | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 1 |
| `offlineOrbitPrimitivePart_eq_rescaled_offlineOrbitMode` | Pour un zéro non trivial ρ, la part primitive d'orbite en exp U vaut exp(3U/2) fois le mode d'orbite en U. | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 1 |
| `offlineOrbitPrimitivePart_eq_mode_at_log` | Pour un zéro non trivial ρ et y > 0, la part primitive d'orbite en y vaut exp(3 log y / 2) fois le mode d'orbite en log y. | CONFIRMÉE (domaine : ρ zéro non trivial, y > 0) | AJOUT | 1 |
| `zeroChannel_eq_rescaled_nontrivial_zero_part_of_smoothedVonMangoldtSum` | Pour U > 0, zeroChannel U vaut exp(−U/2) fois la somme de von Mangoldt lissée en exp U privée du fond déterministe, des pôles et de la série des zéros triviaux. | CONFIRMÉE (domaine : U > 0) | V121 | 0 |
| `offline_zero_channel_eq_orbit_mode_add_rest_mode_of_im_ne_zero` | Pour un zéro non trivial ρ de partie imaginaire non nulle et U > 0, zeroChannel U égale le mode d'orbite de ρ plus le mode du reste. | CONFIRMÉE (domaine : ρ zéro non trivial de partie imaginaire non nulle, U > 0) | AJOUT | 1 |
| `offline_zero_channel_norm_sq_decomposition_of_im_ne_zero` | Pour ρ zéro non trivial de partie imaginaire non nulle et U > 0, le carré de la norme de zeroChannel U égale celui du mode d'orbite plus celui du mode du reste plus un terme croisé. | CONFIRMÉE (domaine : ρ zéro non trivial de partie imaginaire non nulle, U > 0) | AJOUT | 0 |
| `offlineZeroChannelCrossTerm_abs_le` | Pour un zéro non trivial ρ, la valeur absolue du terme croisé est majorée par 2 fois le produit des normes du mode d'orbite et du mode du reste. | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 0 |
| `zerosPrimeCountReal_eq_offlineOrbitPrimeCountPart_add_rest` | Pour x ≥ 2 et un zéro non trivial ρ, zerosPrimeCountReal x égale la partie orbite plus la partie reste du comptage premier. | CONFIRMÉE (domaine : x ≥ 2, ρ zéro non trivial) | AJOUT | 2 |
| `offlineOrbitPrimeCountPart_eq_fixed_cutoff` | Pour x ≥ 2, t dans [2,x] et un zéro non trivial ρ, la partie orbite du comptage premier en t égale la même somme de Möbius sur la coupure fixe de x avec indicateur m ≤ coupure de t. | CONFIRMÉE (domaine : x ≥ 2, t dans [2,x], ρ zéro non trivial) | AJOUT | 1 |
| `intervalIntegrable_inv_mul_offlineOrbitPrimeCountPart` | Pour x ≥ 2 et un zéro non trivial ρ, t ↦ t⁻¹·offlineOrbitPrimeCountPart hzero t est intégrable sur [2,x]. | CONFIRMÉE (domaine : x ≥ 2, ρ zéro non trivial) | AJOUT | 2 |
| `intervalIntegrable_inv_mul_zerosPrimeCountReal` | Pour x ≥ 2, t ↦ t⁻¹·zerosPrimeCountReal t est intégrable sur [2,x]. | CONFIRMÉE (x ≥ 2) | V48 | 1 |
| `intervalIntegrable_inv_mul_offlineRestPrimeCountPart` | Pour x ≥ 2 et un zéro non trivial ρ, t ↦ t⁻¹·offlineRestPrimeCountPart hzero t est intégrable sur [2,x]. | CONFIRMÉE (domaine : x ≥ 2, ρ zéro non trivial) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Algebra.Order.Floor.Ring`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Int.fract_abs_le_one` | Dans un anneau ordonné à plancher, la valeur absolue de la partie fractionnaire de a est majorée par 1. | CONFIRMÉE | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Calculus.Deriv.Polynomial`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Polynomial.logDeriv_exp_eval` | La dérivée logarithmique de w ↦ exp(P(w)) en z vaut P'(z) pour un polynôme complexe P. | CONFIRMÉE | AJOUT | 1 |
| `Polynomial.degree_derivative_le_zero_of_degree_le_one` | Si un polynôme complexe est de degré au plus 1, sa dérivée est de degré au plus 0. | CONFIRMÉE (degré au plus 1) | AJOUT | 1 |
| `Polynomial.eval_derivative_eq_eval_derivative_zero_of_degree_le_one` | Si un polynôme complexe est de degré au plus 1, sa dérivée évaluée en z égale sa dérivée évaluée en 0. | CONFIRMÉE (degré au plus 1) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.AbsMax`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.norm_le_of_mem_ball_of_forall_sphere_norm_le` | Si f est holomorphe sur le disque de rayon r et bornée par C sur le cercle de rayon r, alors ‖f z‖ ≤ C pour tout z du disque. | CONFIRMÉE (domaine : f différentiable, r > 0, borne C sur le cercle) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.Basic`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.div_sub_one_eq_one_add_one_div` | Pour z différent de 1, z/(z−1) = 1 + (z−1)⁻¹. | CONFIRMÉE (z différent de 1) | AJOUT | 0 |
| `Complex.exists_norm_bound_on_closedBall` | Une fonction complexe continue sur une boule fermée de rayon R y est bornée en norme par un M ≥ 0. | CONFIRMÉE (domaine : f continue sur la boule fermée) | AJOUT | 2 |
| `Complex.exists_pos_radius_forall_mem_ball_re_ge` | Si a < Re z0, il existe δ > 0 tel que deux boules emboîtées de rayon δ autour de z0 restent dans le demi-plan Re ≥ a. | CONFIRMÉE (a < Re z0) | AJOUT | 3 |

### `RhGapCriterion.P4Port.Analysis.Complex.BorelCaratheodory`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.borelCaratheodory_zero_closedBall` | Si f analytique sur la boule fermée de rayon R, f 0 = 0 et Re f ≤ M sur cette boule, alors ‖f z‖ ≤ 2Mr/(R−r) pour ‖z‖ ≤ r < R. | CONFIRMÉE (domaine : f analytique sur la boule, f 0 = 0, majoration de Re f par M, 0 < r < R, M > 0) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.CanonicalProduct`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.canonicalProduct_def` | Le produit canonique d'ordre m de la suite a en z est le produit infini des facteurs de Weierstrass de z/a n. | CONFIRMÉE | AJOUT | 0 |
| `Complex.hasProdLocallyUniformlyOn_canonicalProduct` | Sous sommabilité des ‖a n‖⁻¹ à la puissance m+1 et a n non nuls, le produit canonique converge localement uniformément sur ℂ. | CONFIRMÉE (domaine : sommabilité de la suite des ‖a n‖⁻¹ à la puissance m+1, a n non nuls) | AJOUT | 3 |
| `Complex.multipliableLocallyUniformlyOn_canonicalProduct` | Sous la même hypothèse de sommabilité, le produit canonique est localement uniformément multipliable sur ℂ. | CONFIRMÉE (domaine : sommabilité de la suite des ‖a n‖⁻¹ à la puissance m+1, a n non nuls) | AJOUT | 2 |
| `Complex.hasProdUniformlyOn_canonicalProduct_compact` | Sous la même hypothèse de sommabilité, le produit canonique converge uniformément sur tout compact. | CONFIRMÉE (domaine : sommabilité de la suite des ‖a n‖⁻¹ à la puissance m+1, a n non nuls) | AJOUT | 1 |
| `Complex.canonicalProduct_converges_uniformOn_compact` | Sous la même hypothèse de sommabilité, les produits partiels finis convergent uniformément sur tout compact vers le produit canonique. | CONFIRMÉE (domaine : sommabilité de la suite des ‖a n‖⁻¹ à la puissance m+1, a n non nuls) | AJOUT | 0 |
| `Complex.differentiable_canonicalProduct` | Sous la même hypothèse de sommabilité, le produit canonique est différentiable sur ℂ. | CONFIRMÉE (domaine : sommabilité de la suite des ‖a n‖⁻¹ à la puissance m+1, a n non nuls) | AJOUT | 1 |
| `Complex.analyticOnNhd_canonicalProduct` | Sous la même hypothèse de sommabilité, le produit canonique est analytique sur ℂ. | CONFIRMÉE (domaine : sommabilité de la suite des ‖a n‖⁻¹ à la puissance m+1, a n non nuls) | AJOUT | 0 |
| `Complex.logDeriv_weierstrassFactor_one_div` | Pour a non nul et z différent de a, la dérivée logarithmique de w ↦ facteur de Weierstrass de genre 1 en w/a, en z, vaut 1/(z−a) + 1/a. | CONFIRMÉE (a non nul, z différent de a) | AJOUT | 2 |
| `Complex.canonicalProduct_apply_eq_zero` | Sous la même hypothèse de sommabilité, le produit canonique s'annule en chaque a n. | CONFIRMÉE (domaine : sommabilité de la suite des ‖a n‖⁻¹ à la puissance m+1, a n non nuls) | AJOUT | 1 |
| `Complex.canonicalProduct_eq_zero_of_mem_range` | Sous la même hypothèse de sommabilité, le produit canonique s'annule en tout point de l'image de a. | CONFIRMÉE (domaine : sommabilité de la suite des ‖a n‖⁻¹ à la puissance m+1, a n non nuls) | AJOUT | 1 |
| `Complex.canonicalProduct_ne_zero` | Sous la même hypothèse de sommabilité, le produit canonique est non nul en tout point hors de l'image de a. | CONFIRMÉE (domaine : sommabilité de la suite des ‖a n‖⁻¹ à la puissance m+1, a n non nuls) | AJOUT | 2 |
| `Complex.differentiableOn_canonicalPartialProduct` | Le produit partiel fini des facteurs de Weierstrass de z/a k, k < N, est différentiable sur ℂ. | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.Analysis.Complex.CanonicalProduct.0.Complex.tendsto_deriv_canonicalPartialProduct` | Sous la même hypothèse de sommabilité, la dérivée en a n des produits partiels tend vers la dérivée en a n du produit canonique. | CONFIRMÉE (domaine : sommabilité de la suite des ‖a n‖⁻¹ à la puissance m+1, a n non nuls) | AJOUT | 0 |
| `Complex.canonicalProduct_eq_zero_iff` | Sous la même hypothèse de sommabilité, le produit canonique s'annule en z si et seulement si z est dans l'image de a. | CONFIRMÉE (domaine : sommabilité de la suite des ‖a n‖⁻¹ à la puissance m+1, a n non nuls) | AJOUT | 1 |
| `Complex.canonicalProduct_ne_zero_iff` | Sous la même hypothèse de sommabilité, le produit canonique est non nul en z si et seulement si z n'est pas dans l'image de a. | CONFIRMÉE (domaine : sommabilité de la suite des ‖a n‖⁻¹ à la puissance m+1, a n non nuls) | AJOUT | 0 |
| `Complex.logDeriv_canonicalProduct_one_eq_tsum` | Pour le produit canonique de genre 1, hors de l'image de a, la dérivée logarithmique en z vaut la somme des 1/(z−a n) + 1/a n. | CONFIRMÉE (domaine : sommabilité de la suite des ‖a n‖⁻² , a n non nuls, z hors de l'image de a, sommabilité de la série des termes) | AJOUT | 0 |

### `RhGapCriterion.P4Port.Analysis.Complex.CartanBound`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `_private.RhGapCriterion.P4Port.Analysis.Complex.CartanBound.0.Complex.CartanBound.neg_log_le_sqrt_two_div` | Pour 0<x≤1, -log x ≤ racine(2/x) | CONFIRMÉE (domaine : 0<x, x≤1) | AJOUT | 1 |
| `Complex.CartanBound.posLog_log_one_div_abs_one_sub_le_sqrt` | Pour tout réel t, posLog(1/valeur absolue de (1-t)) ≤ racine(2/valeur absolue de (1-t)) | CONFIRMÉE | AJOUT | 1 |
| `Complex.CartanBound.posLog_one_div_norm_one_sub_le_posLog_one_div_abs_one_sub_norm` | Pour w complexe de norme différente de 1, posLog(1/norme(1-w)) ≤ posLog(1/valeur absolue(1-norme w)) | CONFIRMÉE (domaine : norme w ≠ 1) | AJOUT | 1 |
| `Complex.CartanBound.posLog_one_div_norm_one_sub_le_posLog_one_div_abs_one_sub` | Si norme w = t avec t≠1, posLog(1/norme(1-w)) ≤ posLog(1/valeur absolue(1-t)) | CONFIRMÉE (domaine : t ≠ 1 et norme w = t) | AJOUT | 0 |
| `Complex.CartanBound.measurable_phi` | La fonction φ de Cartan est mesurable | CONFIRMÉE | AJOUT | 2 |
| `Complex.CartanBound.phi_le_log_two_of_le_half` | Pour t ≤ 1/2, φ(t) ≤ log 2 | CONFIRMÉE (domaine : t ≤ 1/2) | AJOUT | 1 |
| `Complex.CartanBound.phi_eq_zero_of_one_le_abs_one_sub` | Si valeur absolue(1-t) ≥ 1 alors φ(t)=0 | CONFIRMÉE (domaine : 1 ≤ valeur absolue(1-t)) | AJOUT | 1 |
| `Complex.CartanBound.φ_nonneg` | φ est positive ou nulle partout | CONFIRMÉE | AJOUT | 2 |
| `Complex.CartanBound.φ_le_sqrt` | φ(t) ≤ racine(2/valeur absolue(1-t)) pour tout t | CONFIRMÉE | AJOUT | 2 |
| `Complex.CartanBound.ae_restrict_norm_phi_le_of_forall_mem` | Si 0≤g partout et φ≤g sur [A,B] (A≤B), la norme de φ est presque partout majorée par la norme de g sur l'intervalle | CONFIRMÉE (domaine : A≤B, g positive, φ≤g sur [A,B]) | AJOUT | 2 |
| `Complex.CartanBound.log_norm_one_sub_div_ge_neg_phi` | Pour u de norme r, a≠0, r≠norme a : log norme(1-u/a) ≥ -φ(r/norme a) | CONFIRMÉE (domaine : a≠0, r≠norme a, norme u = r) | AJOUT | 1 |
| `Complex.CartanBound.K_nonneg` | La constante K de Cartan est positive ou nulle | CONFIRMÉE | AJOUT | 3 |
| `Complex.CartanBound.Cφ_pos` | La constante Cφ de Cartan est strictement positive | CONFIRMÉE | AJOUT | 3 |
| `Complex.CartanBound.intervalIntegrable_sqrt_two_div_abs_one_sub_Icc` | La fonction racine(2/valeur absolue(1-t)) est intégrable sur [1/4,4] | CONFIRMÉE | AJOUT | 2 |
| `Complex.CartanBound.phi_le_log_two_on_dyadic_of_le_quarter` | Si A ≤ 1/4 et t dans [A,2A], φ(t) ≤ log 2 | CONFIRMÉE (domaine : A ≤ 1/4, t∈[A,2A]) | AJOUT | 2 |
| `Complex.CartanBound.phi_eq_zero_of_two_le` | Pour t ≥ 2, φ(t)=0 | CONFIRMÉE (domaine : 2 ≤ t) | AJOUT | 2 |
| `Complex.CartanBound.intervalIntegrable_phi_dyadic_small` | Pour 0≤A≤1/4, φ est intégrable sur [A,2A] | CONFIRMÉE (domaine : 0≤A≤1/4) | AJOUT | 2 |
| `Complex.CartanBound.intervalIntegrable_phi_dyadic_large` | Pour A≥2, φ est intégrable sur [A,2A] | CONFIRMÉE (domaine : 2≤A) | AJOUT | 1 |
| `Complex.CartanBound.intervalIntegrable_sqrt_two_div_abs_one_sub_dyadic_middle` | Pour 1/4≤A≤2, racine(2/valeur absolue(1-t)) est intégrable sur [A,2A] | CONFIRMÉE (domaine : 1/4≤A≤2) | AJOUT | 2 |
| `Complex.CartanBound.intervalIntegrable_phi_dyadic_middle` | Pour 1/4≤A≤2, φ est intégrable sur [A,2A] | CONFIRMÉE (domaine : 1/4≤A≤2) | AJOUT | 2 |
| `Complex.CartanBound.intervalIntegrable_phi_dyadic` | Pour A≥0, φ est intégrable sur [A,2A] | CONFIRMÉE (domaine : 0≤A) | AJOUT | 1 |
| `Complex.CartanBound.intervalIntegrable_phi_div` | Pour a>0 et R≥0, r↦φ(r/a) est intégrable sur [R,2R] | CONFIRMÉE (domaine : 0<a, 0≤R) | AJOUT | 2 |
| `Complex.CartanBound.log_two_le_Cφ` | log 2 ≤ Cφ | CONFIRMÉE | AJOUT | 1 |
| `Complex.CartanBound.four_mul_K_add_one_le_Cφ` | 4K+1 ≤ Cφ | CONFIRMÉE | AJOUT | 1 |
| `Complex.CartanBound.integral_phi_le_Cφ_mul_small` | Pour 0≤A≤1/4, l'intégrale de φ sur [A,2A] est ≤ Cφ·A | CONFIRMÉE (domaine : 0≤A≤1/4) | AJOUT | 1 |
| `Complex.CartanBound.integral_phi_le_Cφ_mul_large` | Pour A≥2, l'intégrale de φ sur [A,2A] est ≤ Cφ·A | CONFIRMÉE (domaine : 2≤A) | AJOUT | 1 |
| `Complex.CartanBound.integral_sqrt_two_div_abs_one_sub_le_K_dyadic_middle` | Pour 1/4≤A≤2, l'intégrale de racine(2/valeur absolue(1-t)) sur [A,2A] est ≤ K | CONFIRMÉE (domaine : 1/4≤A≤2) | AJOUT | 1 |
| `Complex.CartanBound.K_le_four_mul_K_add_one_mul_of_quarter_le` | Pour A≥1/4, K ≤ (4K+1)·A | CONFIRMÉE (domaine : 1/4≤A) | AJOUT | 1 |
| `Complex.CartanBound.integral_phi_le_Cφ_mul_middle` | Pour 1/4≤A≤2, l'intégrale de φ sur [A,2A] est ≤ Cφ·A | CONFIRMÉE (domaine : 1/4≤A≤2) | AJOUT | 1 |
| `Complex.CartanBound.integral_phi_le_Cφ_mul` | Pour A≥0, l'intégrale de φ sur [A,2A] est ≤ Cφ·A | CONFIRMÉE (domaine : 0≤A) | AJOUT | 1 |
| `Complex.CartanBound.volume_Ioc_two_mul_ne_zero` | Pour R>0, l'intervalle ]R,2R] est de mesure non nulle | CONFIRMÉE (domaine : 0<R) | AJOUT | 1 |
| `Complex.CartanBound.volume_Ioc_two_mul_diff_finset_ne_zero` | Pour R>0 et tout ensemble fini bad, ]R,2R] privé de bad est de mesure non nulle | CONFIRMÉE (domaine : 0<R) | AJOUT | 1 |
| `Complex.CartanBound.restrict_volume_Ioc_two_mul_diff_finset_ne_zero` | Idem avec la mesure restreinte à ]R,2R] : le complément d'un fini y est de mesure non nulle | CONFIRMÉE (domaine : 0<R) | AJOUT | 1 |
| `Complex.CartanBound.integral_phi_div_le_Cφ_mul` | Pour a>0, R≥0, l'intégrale de φ(r/a) sur [R,2R] est ≤ Cφ·R | CONFIRMÉE (domaine : 0<a, 0≤R) | AJOUT | 1 |
| `Complex.CartanBound.intervalIntegrable_sum_mul_phi_div` | Une somme finie pondérée de r↦w_i·φ(r/a_i) est intégrable sur [R,2R] | CONFIRMÉE (domaine : a_i>0, R≥0) | AJOUT | 1 |
| `Complex.CartanBound.integral_sum_mul_phi_div_le_Cφ_mul_sum` | L'intégrale sur [R,2R] de la somme finie pondérée des w_i·φ(r/a_i) est ≤ (Cφ·somme des w_i)·R | CONFIRMÉE (domaine : poids w_i≥0, a_i>0, R≥0) | AJOUT | 1 |
| `Complex.CartanBound.exists_radius_Ioc_sum_mul_phi_div_le_Cφ_mul_sum_avoid` | Il existe r dans ]R,2R] hors d'un ensemble fini bad tel que la somme des w_i·φ(r/a_i) est ≤ Cφ·somme des w_i (rayon de Cartan évitant) | CONFIRMÉE (domaine : poids ≥0, a_i>0, R>0) | AJOUT | 2 |
| `Complex.CartanBound.exists_radius_Ioc_sum_mul_phi_div_le_Cφ_mul_sum` | Il existe r dans ]R,2R] tel que la somme des w_i·φ(r/a_i) est ≤ Cφ·somme des w_i (rayon de Cartan) | CONFIRMÉE (domaine : poids ≥0, a_i>0, R>0) | AJOUT | 0 |

### `RhGapCriterion.P4Port.Analysis.Complex.CartanInverseFactorBound`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.max_one_norm_div_pow_le_one_add_rpow` | Si norme u = r et m ≤ τ, max(1, norme(u/a)^m) ≤ 1 + (r/norme a)^τ | CONFIRMÉE (domaine : norme u = r, m≤τ) | AJOUT | 1 |
| `Complex.Hadamard.norm_inv_weierstrassFactor_le_exp_near` | Borne de Cartan proche : la norme de l'inverse du facteur de Weierstrass d'ordre m en u/a est ≤ exp(φ(r/norme a)+m(1+(r/norme a)^τ)) | CONFIRMÉE (domaine : norme u=r, a≠0, r≠norme a, m≤τ) | AJOUT | 1 |
| `Complex.Hadamard.norm_inv_weierstrassFactor_le_exp_far` | Borne lointaine : si norme(u/a) ≤ 1/2 et τ≤m+1, la norme de l'inverse du facteur de Weierstrass est ≤ exp(2(r/norme a)^τ) | CONFIRMÉE (domaine : norme u=r, a≠0, norme(u/a)≤1/2, τ≤m+1) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.CartanMajorantBound`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `_private.RhGapCriterion.P4Port.Analysis.Complex.CartanMajorantBound.0.Complex.Hadamard.summable_ite_mem_finset` | Une fonction réelle nulle hors d'un ensemble fini s est sommable | CONFIRMÉE | AJOUT | 2 |
| `_private.RhGapCriterion.P4Port.Analysis.Complex.CartanMajorantBound.0.Complex.Hadamard.tsum_ite_mem_finset` | La somme infinie d'une fonction portée par un ensemble fini est la somme finie | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.Analysis.Complex.CartanMajorantBound.0.Complex.Hadamard.tsum_add_four` | Somme infinie de la somme de quatre suites sommables = somme des quatre sommes infinies | CONFIRMÉE (domaine : quatre suites sommables) | AJOUT | 1 |
| `Complex.Hadamard.cartanProductConstant_nonneg` | La constante cartanProductConstant est positive ou nulle si Sτ≥0 | CONFIRMÉE (domaine : 0≤Sτ) | AJOUT | 1 |
| `Complex.Hadamard.rpow_div_norm_divisorZeroIndex₀_eq` | Pour r≥0, (r/norme a_p)^τ = r^τ · (norme a_p inverse)^τ pour tout indice de zéro p | CONFIRMÉE (domaine : 0≤r) | AJOUT | 4 |
| `Complex.Hadamard.tsum_rpow_div_norm_divisorZeroIndex₀_eq` | Pour r≥0, somme infinie sur les indices de zéros de (r/norme a_p)^τ = r^τ · somme des (norme a_p inverse)^τ | CONFIRMÉE (domaine : 0≤r) | AJOUT | 1 |
| `Complex.Hadamard.tsum_two_mul_rpow_div_norm_divisorZeroIndex₀_le` | Majoration de la somme infinie de 2(r/norme a_p)^τ par 2(somme des norme^-τ +1)(1+r)^τ | CONFIRMÉE (domaine : r≥0, τ≥0) | AJOUT | 1 |
| `Complex.Hadamard.sum_rpow_div_norm_divisorZeroIndex₀_le` | Majoration de la somme finie sur small des (r/norme a_p)^τ par une expression en somme des norme^-τ et (1+r)^τ | CONFIRMÉE (domaine : r≥0, τ≥0, sommabilité de norme^-τ) | AJOUT | 1 |
| `Complex.Hadamard.add_four_le_add_two_mul_of_le` | Si x1≤A, x2≤B, x3≤B, x4≤C alors x1+x2+x3+x4 ≤ A+2B+C | CONFIRMÉE (domaine : quatre majorations termes à termes) | AJOUT | 1 |
| `Complex.Hadamard.cartan_majorant_four_term_bound` | Inégalité arithmétique à quatre termes : xφ+x0+xm+xt ≤ (Cφ+2m)qYT+2YT | CONFIRMÉE (domaine : quatre majorations termes à termes) | AJOUT | 1 |
| `Complex.Hadamard.cartan_majorant_add_two_factor` | Identité arithmétique A·Y·T + 2·Y·T = (A+2)·Y·T | CONFIRMÉE | AJOUT | 1 |
| `Complex.Hadamard.cartan_majorant_pad_two_to_three` | (A+2)(S+1)T ≤ (A+3)(S+1)T | CONFIRMÉE (domaine : 0≤S+1, 0≤T) | AJOUT | 1 |
| `Complex.Hadamard.cartan_majorant_nonneg` | Le majorant de Cartan (terme par indice, cas small ou non) est positif ou nul | CONFIRMÉE (domaine : 0≤r) | AJOUT | 1 |
| `Complex.Hadamard.cartan_majorant_summable` | Le majorant de Cartan est sommable | CONFIRMÉE (domaine : r≥0, sommabilité de norme^-τ) | AJOUT | 1 |
| `Complex.Hadamard.cartan_card_small_le` | Le cardinal de small est majoré via la somme des norme^-τ (indices de norme ≤ 4R) | CONFIRMÉE (domaine : R>0, τ≥0, norme ≤ 4R sur small, sommabilité) | AJOUT | 1 |
| `Complex.Hadamard.cartan_rpow_mul_le` | (4R)^τ ≤ 4^τ (1+r)^τ pour 0<R≤r et τ≥0 | CONFIRMÉE (domaine : 0<R≤r, τ≥0) | AJOUT | 1 |
| `Complex.Hadamard.cartan_sum_majorant_le` | Majoration de la somme des majorants de Cartan par une borne en (Cφ+...)·(S+1)·(1+r)^τ | CONFIRMÉE (domaine : 0<R≤r, τ≥0, smallSet fini égal aux indices de norme ≤4R, sommabilité, etc.) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.CartanProductBound`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Finset.prod_le_exp_sum` | Produit fini de a_x ≥ 0 avec a_x ≤ exp(b_x) est ≤ exp de la somme des b_x | CONFIRMÉE (domaine : a_x≥0, a_x≤exp(b_x)) | AJOUT | 1 |
| `hasProd_le_of_prod_le_exp` | Si f a un produit infini de valeur a et tous les produits finis sont ≤ exp B, alors a ≤ exp B | CONFIRMÉE (domaine : HasProd, produits finis ≤ exp B) | AJOUT | 1 |
| `hasProd_inv_unconditional` | Si le produit infini de fac vaut F≠0, le produit des inverses vaut F inverse | CONFIRMÉE (domaine : HasProd fac F, F≠0) | AJOUT | 1 |
| `hasProd_norm_inv_unconditional` | Si le produit infini de fac vaut F≠0, le produit des normes des inverses vaut la norme de F inverse | CONFIRMÉE (domaine : HasProd fac F, F≠0) | AJOUT | 1 |
| `hasProd_norm_inv_le_exp_of_pointwise_le_exp` | Si HasProd fac F et la norme de l'inverse de chaque facteur ≤ exp(b x) avec sommes finies de b ≤ B, alors norme(F inverse) ≤ exp B | CONFIRMÉE (domaine : HasProd, bornes ponctuelles et sommes finies) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.Convex`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.isPathConnected_halfSpace_re_gt_diff_singleton` | Le demi-plan Re z > a privé d'un point p (Re p > a) est connexe par arcs | CONFIRMÉE (domaine : a < Re p) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.Divisor`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero` | Si f entière n'est pas identiquement nulle, l'ordre analytique de f en tout point est fini | CONFIRMÉE (domaine : f entière, ∃ z f z ≠0) | AJOUT | 8 |
| `Complex.Hadamard.no_zero_on_sphere_of_forall_val_norm_ne` | Si f entière non nulle et r ≤ B évite les normes de tous les zéros de norme ≤ B, aucun zéro de f sur la sphère de rayon r | CONFIRMÉE (domaine : f entière non nulle, 0<r≤B, r ≠ norme des zéros) | AJOUT | 1 |
| `Complex.Hadamard.divisorCanonicalProduct_eq_zero_of_exists` | Si un facteur du produit canonique s'annule en z, le produit canonique divisoriel s'annule en z | CONFIRMÉE (domaine : sommabilité, un facteur nul) | AJOUT | 1 |
| `Complex.Hadamard.divisorCanonicalProduct_eq_zero_at_index` | Le produit canonique divisoriel s'annule en la valeur de tout indice de zéro | CONFIRMÉE (domaine : sommabilité de norme^-(m+1)) | AJOUT | 0 |
| `Complex.Hadamard.analyticOrderAt_prod_fiberFinset` | L'ordre analytique du produit fini des facteurs de Weierstrass sur la fibre de z₀ en z₀ est le cardinal de la fibre | CONFIRMÉE | AJOUT | 1 |
| `Complex.Hadamard.analyticOrderNatAt_prod_fiberFinset` | Version en ordre naturel : l'ordre du produit fini des facteurs de la fibre de z₀ en z₀ est le cardinal de la fibre | CONFIRMÉE | AJOUT | 0 |
| `Complex.Hadamard.analyticOrderAt_divisorCanonicalProduct_eq_fiber_card` | L'ordre analytique du produit canonique divisoriel en z₀ est le cardinal de la fibre de z₀ | CONFIRMÉE (domaine : sommabilité de norme^-(m+1)) | AJOUT | 2 |
| `Complex.Hadamard.divisorCanonicalProduct_ne_zero_of_forall_ne` | Hors des valeurs des indices, le produit canonique divisoriel est non nul | CONFIRMÉE (domaine : sommabilité, z différent de toutes les valeurs d'indices) | AJOUT | 2 |
| `Complex.Hadamard.logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne` | Dérivée logarithmique du produit canonique de genre 1 hors des zéros = somme sur les zéros | CONFIRMÉE (domaine : sommabilité de norme^-2, z ≠ valeurs d'indices) | AJOUT | 1 |
| `Complex.Hadamard.analyticOrderAt_divisorCanonicalProduct_at_index` | Ordre analytique du produit canonique en un indice non nul = multiplicité de f | CONFIRMÉE (domaine : f différentiable, sommabilité) | AJOUT | 0 |
| `Complex.Hadamard.eventually_exists_analyticAt_eq_pow_smul_divisorComplementPartialProduct` | Pour z₀, à partir d'un certain ensemble fini s, le produit partiel s'écrit (z-z₀)^card fibre fois une fonction analytique non nulle en z₀ | CONFIRMÉE | AJOUT | 0 |
| `Complex.Hadamard.divisorPartialProduct_ne_zero_on_ball_punctured` | Le produit partiel est non nul sur la boule épointée en z₀ si z₀ est l'unique point du support du diviseur dans la boule | CONFIRMÉE (domaine : boule isolant z₀, z≠z₀) | AJOUT | 0 |

### `RhGapCriterion.P4Port.Analysis.Complex.DivisorComplement`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.divisorComplementFactor_eq_one_of_mem` | Le facteur complémentaire vaut 1 pour les indices de la fibre de z₀ | CONFIRMÉE (domaine : p dans la fibre de z₀) | AJOUT | 3 |
| `Complex.Hadamard.divisorComplementFactor_eq_weierstrassFactor_of_not_mem` | Le facteur complémentaire vaut le facteur de Weierstrass pour les indices hors fibre de z₀ | CONFIRMÉE (domaine : p hors fibre de z₀) | AJOUT | 3 |
| `Complex.Hadamard.divisorComplementFactor_def` | Définition dépliée du facteur complémentaire : 1 si la valeur de l'indice est z₀, sinon le facteur de Weierstrass | CONFIRMÉE | AJOUT | 1 |
| `Complex.Hadamard.divisorPartialProduct_def` | Définition dépliée du produit partiel : produit sur s des facteurs de Weierstrass en z/valeur de l'indice | CONFIRMÉE | AJOUT | 0 |
| `Complex.Hadamard.differentiable_weierstrassFactor_divisorZeroIndex₀` | Chaque facteur de Weierstrass composé à la valeur d'indice est différentiable | CONFIRMÉE | AJOUT | 3 |
| `Complex.Hadamard.differentiable_divisorPartialProduct` | Le produit partiel divisoriel est différentiable | CONFIRMÉE | AJOUT | 2 |
| `Complex.Hadamard.analyticAt_divisorPartialProduct` | Le produit partiel divisoriel est analytique en tout point | CONFIRMÉE | AJOUT | 2 |
| `Complex.Hadamard.divisorComplementPartialProduct_def` | Définition dépliée du produit partiel complémentaire : produit sur s des facteurs complémentaires | CONFIRMÉE | AJOUT | 5 |
| `Complex.Hadamard.differentiable_divisorComplementPartialProduct` | Le produit partiel complémentaire est différentiable | CONFIRMÉE | AJOUT | 1 |
| `Complex.Hadamard.hasProdUniformlyOn_divisorComplementCanonicalProduct_univ` | Le produit complémentaire converge uniformément (HasProdUniformlyOn) sur tout compact | CONFIRMÉE (domaine : K compact, sommabilité) | AJOUT | 1 |
| `Complex.Hadamard.hasProdLocallyUniformlyOn_divisorComplementCanonicalProduct_univ` | Le produit complémentaire converge localement uniformément | CONFIRMÉE (domaine : sommabilité de norme^-(m+1)) | AJOUT | 1 |
| `Complex.Hadamard.tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ` | Les produits partiels complémentaires tendent localement uniformément vers le produit complémentaire | CONFIRMÉE (domaine : sommabilité) | AJOUT | 2 |
| `Complex.Hadamard.differentiableOn_divisorComplementCanonicalProduct_univ` | Le produit canonique complémentaire est différentiable sur C | CONFIRMÉE (domaine : sommabilité) | AJOUT | 3 |
| `Complex.Hadamard.divisorPartialProduct_eq_fiber_mul_complement_of_subset` | Si la fibre de z₀ est contenue dans s, produit partiel = produit sur la fibre × produit partiel complémentaire | CONFIRMÉE (domaine : fibre ⊆ s) | AJOUT | 3 |
| `Complex.Hadamard.divisorComplementPartialProduct_ne_zero_on_ball` | Le produit partiel complémentaire est non nul sur la boule isolant z₀ | CONFIRMÉE (domaine : boule isolant z₀, z dans la boule) | AJOUT | 0 |
| `Complex.Hadamard.eventually_eq_fiber_mul_divisorComplementPartialProduct` | À partir d'un certain s, le produit partiel = produit de la fibre × produit partiel complémentaire (pour tout z) | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.P4Port.Analysis.Complex.DivisorConvergence`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.finite_divisorZeroIndex₀_subtype_norm_le` | Les indices de zéros de norme ≤ B sont en nombre fini (type sous-ensemble) | CONFIRMÉE (domaine : boule fermée de rayon B ⊆ U) | AJOUT | 4 |
| `Complex.Hadamard.divisorZeroIndex₀_norm_le_finite` | L'ensemble des indices de zéros de norme ≤ B est fini | CONFIRMÉE (domaine : boule fermée de rayon B ⊆ U) | AJOUT | 8 |
| `Complex.Hadamard.norm_div_le_half_of_norm_le_of_two_mul_lt` | Si norme z ≤ R et 2R < norme a, alors norme(z/a) ≤ 1/2 | CONFIRMÉE (domaine : R>0, norme z ≤ R, 2R<norme a) | AJOUT | 2 |
| `Complex.Hadamard.summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq` | Les termes 1/(z - a_p) de la dérivée logarithmique sont sommables hors des zéros si norme^-2 est sommable | CONFIRMÉE (domaine : sommabilité, z ≠ valeurs d'indices) | AJOUT | 2 |
| `Complex.Hadamard.hasProdUniformlyOn_divisorCanonicalProduct_univ` | Le produit canonique divisoriel converge uniformément sur tout compact (HasProdUniformlyOn) | CONFIRMÉE (domaine : K compact, sommabilité) | AJOUT | 1 |
| `Complex.Hadamard.hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ` | Le produit canonique divisoriel converge localement uniformément | CONFIRMÉE (domaine : sommabilité) | AJOUT | 5 |
| `Complex.Hadamard.differentiableOn_divisorCanonicalProduct_univ` | Le produit canonique divisoriel est différentiable sur C (DifferentiableOn univ) | CONFIRMÉE (domaine : sommabilité) | AJOUT | 5 |
| `Complex.Hadamard.differentiableAt_divisorCanonicalProduct_univ` | Le produit canonique divisoriel est différentiable en tout point | CONFIRMÉE (domaine : sommabilité) | AJOUT | 1 |
| `Complex.Hadamard.logDeriv_divisorCanonicalProduct_one_eq_tsum` | Dérivée logarithmique du produit canonique de genre 1 = somme sur les zéros | CONFIRMÉE (domaine : sommabilité, z hors zéros, produit non nul en z) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.DivisorFiber`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int` | Pour f entière, le diviseur de f en z est l'ordre analytique naturel de f en z | CONFIRMÉE (domaine : f différentiable) | AJOUT | 4 |
| `Complex.Hadamard.divisorZeroIndex₀_fiber_finite` | La fibre d'une valeur z₀ dans les indices de zéros est finie | CONFIRMÉE | AJOUT | 2 |
| `Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset` | Appartenance à la fibre finie : p dans fiberFinset ssi valeur de p = z₀ | CONFIRMÉE | AJOUT | 8 |
| `Complex.Hadamard.eventually_atTop_subset_fiberFinset` | À partir d'un certain ensemble fini s, la fibre de z₀ est contenue dans s | CONFIRMÉE | AJOUT | 4 |
| `Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_toNat_divisor` | Pour z₀≠0, le cardinal de la fibre de z₀ est la partie naturelle du diviseur de f en z₀ | CONFIRMÉE (domaine : z₀≠0) | AJOUT | 1 |
| `Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt` | Pour f entière et z₀≠0, le cardinal de la fibre de z₀ est l'ordre analytique naturel de f en z₀ | CONFIRMÉE (domaine : f différentiable, z₀≠0) | AJOUT | 4 |
| `Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset_of_val_mem_ball` | Si la valeur d'un indice est dans une boule isolante de z₀, l'indice est dans la fibre de z₀ | CONFIRMÉE (domaine : boule isolant z₀) | AJOUT | 1 |
| `Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset_iff_val_mem_ball` | Pour ε>0 et boule isolant z₀, indice dans la fibre ssi sa valeur est dans la boule | CONFIRMÉE (domaine : 0<ε, boule isolant z₀) | AJOUT | 1 |
| `Complex.Hadamard.not_mem_divisorZeroIndex₀_fiberFinset_iff_val_ne` | Un indice hors fibre de z₀ ssi sa valeur est différente de z₀ | CONFIRMÉE | AJOUT | 2 |
| `Complex.Hadamard.val_not_mem_ball_of_not_mem_fiberFinset` | Si un indice est hors fibre de z₀, sa valeur est hors de la boule isolante | CONFIRMÉE (domaine : 0<ε, boule isolant z₀, p hors fibre) | AJOUT | 0 |
| `Complex.Hadamard.weierstrassFactor_div_ne_zero_on_ball_of_not_mem_fiberFinset` | Un facteur de Weierstrass en z/valeur est non nul sur la boule pour un indice hors fibre | CONFIRMÉE (domaine : boule isolant z₀, p hors fibre, z dans la boule) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.DivisorIndex`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.divisorZeroIndex₀_val_ne_zero` | La valeur d'un indice de zéro est non nulle | CONFIRMÉE | AJOUT | 12 |
| `Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support` | Un indice de zéro a un diviseur non nul en sa valeur | CONFIRMÉE | AJOUT | 1 |
| `Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support'` | La valeur d'un indice de zéro appartient au support du diviseur | CONFIRMÉE | AJOUT | 2 |
| `Complex.Hadamard.exists_ball_inter_divisor_support_eq_singleton_of_index` | Tout indice a une boule autour de sa valeur qui ne rencontre le support du diviseur qu'en cette valeur | CONFIRMÉE | AJOUT | 0 |
| `Complex.Hadamard.divisorCanonicalProduct_eq_tprod_of_equiv` | Le produit canonique divisoriel s'écrit comme produit infini indexé par tout type équivalent à l'ensemble des indices | CONFIRMÉE | AJOUT | 3 |
| `Complex.Hadamard.divisorCanonicalProduct_eq_canonicalProduct_of_equiv` | Le produit canonique divisoriel égale le produit canonique d'une énumération ℕ ≃ indices | CONFIRMÉE | AJOUT | 0 |
| `Complex.Hadamard.divisorCanonicalProduct_zero` | Le produit canonique divisoriel vaut 1 en 0 | CONFIRMÉE | AJOUT | 7 |
| `Complex.Hadamard.divisorCanonicalProduct_ne_zero_at_zero` | Le produit canonique divisoriel est non nul en 0 | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.P4Port.Analysis.Complex.DivisorPartialProductFactor`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀` | Ordre analytique du produit fini des facteurs de Weierstrass sur s en z₀ = cardinal des indices de s de valeur z₀ | CONFIRMÉE | AJOUT | 3 |
| `Complex.Hadamard.analyticOrderNatAt_finset_prod_weierstrassFactor_divisorZeroIndex₀` | Version ordre naturel : ordre du produit fini sur s en z₀ = cardinal des indices de s de valeur z₀ | CONFIRMÉE | AJOUT | 0 |
| `Complex.Hadamard.analyticOrderAt_partialProduct_eq_fiberCard_of_subset` | Si la fibre de z₀ ⊆ s, l'ordre du produit partiel en z₀ est le cardinal de la fibre | CONFIRMÉE (domaine : fibre ⊆ s) | AJOUT | 1 |
| `Complex.Hadamard.exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber` | Si la fibre de z₀ ⊆ s, le produit partiel = (z-z₀)^card fibre × fonction analytique non nulle en z₀ | CONFIRMÉE (domaine : fibre ⊆ s) | AJOUT | 3 |

### `RhGapCriterion.P4Port.Analysis.Complex.DivisorQuotientConvergence`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.tendstoLocallyUniformlyOn_divisorPartialProduct_univ` | Les produits partiels tendent localement uniformément vers le produit canonique sur C | CONFIRMÉE (domaine : sommabilité) | AJOUT | 1 |
| `Complex.Hadamard.tendstoUniformlyOn_divisorPartialProduct_div_pow_sub` | Les produits partiels divisés par (z-z₀)^k tendent uniformément sur tout compact évitant z₀ | CONFIRMÉE (domaine : sommabilité, K compact, z≠z₀ sur K) | AJOUT | 1 |
| `Complex.Hadamard.tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub` | Les produits partiels divisés par (z-z₀)^k tendent localement uniformément sur C privé de z₀ | CONFIRMÉE (domaine : sommabilité) | AJOUT | 2 |
| `Complex.Hadamard.exists_ball_eq_divisorCanonicalProduct_div_pow_eq` | Il existe une boule autour de z₀ où produit canonique/(z-z₀)^card fibre = u·produit complémentaire avec u analytique non nul | CONFIRMÉE (domaine : sommabilité) | AJOUT | 2 |
| `Complex.Hadamard.bddAbove_norm_divisorCanonicalProduct_div_pow_puncturedBall` | Le module du produit canonique divisé par (z-z₀)^card fibre est borné sur une boule épointée en z₀ | CONFIRMÉE (domaine : sommabilité) | AJOUT | 1 |
| `Complex.Hadamard.divisorComplementCanonicalProduct_ne_zero_at` | Le produit canonique complémentaire est non nul en z₀ | CONFIRMÉE (domaine : sommabilité) | AJOUT | 2 |
| `Complex.Hadamard.exists_ball_divisorComplementCanonicalProduct_ne_zero` | Le produit canonique complémentaire est non nul sur une boule autour de z₀ | CONFIRMÉE (domaine : sommabilité) | AJOUT | 0 |
| `Complex.Hadamard.eventually_exists_analyticAt_eq_pow_smul_divisorPartialProduct` | À partir d'un certain s, il existe g analytique non nulle en z₀ avec produit partiel = (z-z₀)^card × g près de z₀ | CONFIRMÉE | AJOUT | 1 |
| `Complex.Hadamard.eventually_eq_punctured_quotient_of_factorization` | À partir d'un certain s, le produit partiel divisé par (z-z₀)^card fibre coïncide avec une fonction analytique en z₀ sur le voisinage épointé | CONFIRMÉE | AJOUT | 1 |
| `Complex.Hadamard.eventually_exists_ball_eq_punctured_quotient_of_factorization` | À partir d'un certain s, sur une boule épointée, le quotient partiel coïncide avec une fonction analytique en z₀ | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.P4Port.Analysis.Complex.DivisorQuotientRemovable`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.differentiableOn_divisorPartialProduct_div_pow_sub` | Le produit partiel divisé par (z-z₀)^k est différentiable sur C privé de z₀ | CONFIRMÉE | AJOUT | 1 |
| `Complex.Hadamard.differentiableOn_divisorCanonicalProduct_div_pow_sub` | Le produit canonique divisé par (z-z₀)^k est différentiable sur C privé de z₀ | CONFIRMÉE (domaine : sommabilité) | AJOUT | 2 |
| `Complex.Hadamard.differentiableOn_update_limUnder_divisorCanonicalProduct_div_pow` | Le prolongement par la limite en z₀ du quotient du produit canonique par (z-z₀)^card fibre est différentiable sur une boule | CONFIRMÉE (domaine : sommabilité) | AJOUT | 1 |
| `Complex.Hadamard.analyticAt_update_limUnder_divisorCanonicalProduct_div_pow` | Le prolongement par la limite en z₀ du quotient du produit canonique est analytique en z₀ | CONFIRMÉE (domaine : sommabilité) | AJOUT | 1 |
| `Complex.Hadamard.exists_analyticAt_divisorCanonicalProduct_quotient` | Il existe un quotient analytique amovible du produit canonique par (z-z₀)^k | CONFIRMÉE (domaine : sommabilité) | AJOUT | 1 |
| `Complex.Hadamard.analyticOrderNatAt_divisorCanonicalProduct_eq_fiber_card` | L'ordre analytique naturel du produit canonique divisoriel en z₀ est le cardinal de la fibre | CONFIRMÉE (domaine : sommabilité) | AJOUT | 2 |
| `Complex.Hadamard.analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt` | Le produit canonique divisoriel a en z₀≠0 le même ordre naturel que f | CONFIRMÉE (domaine : f différentiable, sommabilité, z₀≠0) | AJOUT | 2 |

### `RhGapCriterion.P4Port.Analysis.Complex.DivisorUnits`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.divisorZeroIndex₀_val_eq_of_mem_ball` | Une valeur d'indice dans une boule isolant z₀ est égale à z₀ | CONFIRMÉE (domaine : boule isolant z₀, valeur dans la boule) | AJOUT | 1 |
| `Complex.Hadamard.weierstrassFactor_div_ne_zero_on_ball_of_val_ne` | Le facteur de Weierstrass est non nul sur la boule pour un indice de valeur différente de z₀ | CONFIRMÉE (domaine : boule isolant z₀, valeur ≠ z₀) | AJOUT | 2 |
| `Complex.Hadamard.weierstrassFactor_div_ne_zero_on_ball_punctured` | Le facteur de Weierstrass est non nul sur la boule épointée en z₀ | CONFIRMÉE (domaine : boule isolant z₀, z≠z₀) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.ExpPoly`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.zero_free_polynomial_growth_is_exp_poly` | Une fonction entière sans zéro à croissance polynomiale exp(C(1+norme z)^n) est l'exponentielle d'un polynôme de degré ≤ n | CONFIRMÉE (domaine : entière, sans zéro, borne de croissance) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.ExpPoly.Growth`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `_private.RhGapCriterion.P4Port.Analysis.Complex.ExpPoly.Growth.0.Complex.Hadamard.exists_pow_eq_complex` | Pour n>0, tout complexe w a une racine n-ième | CONFIRMÉE (domaine : 0<n) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.Analysis.Complex.ExpPoly.Growth.0.Complex.Hadamard.mul_conj_div_norm` | Pour a≠0, a·(conj a / norme a) = norme a | CONFIRMÉE (domaine : a≠0) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.Analysis.Complex.ExpPoly.Growth.0.Complex.Hadamard.exists_z_norm_eq_re_eval_ge` | Pour un polynôme de degré >0, il existe R0 tel que pour tout R≥R0 un z de norme R vérifie (norme du coefficient dominant)/2 · R^deg ≤ Re P(z) | CONFIRMÉE (domaine : degré>0) | AJOUT | 1 |
| `Complex.Hadamard.natDegree_le_floor_of_growth_exp_eval` | Si log(1+norme exp(P z)) ≤ C(1+norme z)^ρ alors degré P ≤ partie entière de ρ | CONFIRMÉE (domaine : ρ≥0, borne de croissance) | AJOUT | 1 |
| `Complex.Hadamard.natDegree_le_floor_of_exp_eval_norm_bound` | Si norme exp(P z) ≤ exp(C(1+norme z)^τ) alors degré P ≤ partie entière de τ | CONFIRMÉE (domaine : τ≥0, borne de croissance) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.HadamardFactorization`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.centeredHadamardDenom_center_eq_one` | Le dénominateur de Hadamard centré vaut 1 au centre si f n'y a pas de zéro (ordre 0) | CONFIRMÉE (domaine : ordre de f en c = 0) | AJOUT | 0 |
| `Complex.Hadamard.centeredHadamardDenom_center_eq_zero` | Le dénominateur de Hadamard centré vaut 0 au centre si f s'y annule | CONFIRMÉE (domaine : ordre de f en c ≠ 0) | AJOUT | 0 |
| `Complex.Hadamard.differentiable_divisorCanonicalProduct_univ` | Le produit canonique divisoriel est différentiable sur C | CONFIRMÉE (domaine : sommabilité) | AJOUT | 5 |
| `Complex.Hadamard.analyticAt_divisorCanonicalProduct_univ` | Le produit canonique divisoriel est analytique en tout point | CONFIRMÉE (domaine : sommabilité) | AJOUT | 2 |
| `Complex.Hadamard.differentiable_hadamardDenom` | Le dénominateur de Hadamard est différentiable | CONFIRMÉE (domaine : sommabilité) | AJOUT | 3 |
| `Complex.Hadamard.hadamardDenom_ne_zero_at` | Le dénominateur de Hadamard est non nul là où f est non nulle | CONFIRMÉE (domaine : f entière non nulle, sommabilité, f z ≠ 0) | AJOUT | 2 |
| `Complex.Hadamard.analyticOrderNatAt_divisorCanonicalProduct_zero` | L'ordre naturel du produit canonique en 0 est 0 | CONFIRMÉE (domaine : sommabilité) | AJOUT | 1 |
| `Complex.Hadamard.analyticOrderNatAt_hadamardDenom_eq` | Le dénominateur de Hadamard a en tout point le même ordre naturel que f | CONFIRMÉE (domaine : f différentiable, sommabilité) | AJOUT | 1 |
| `Complex.Hadamard.divisor_hadamardDenom_eq` | Le diviseur du dénominateur de Hadamard égale le diviseur de f | CONFIRMÉE (domaine : f différentiable, sommabilité) | AJOUT | 1 |
| `Complex.Hadamard.divisor_hadamardQuotient_eq_zero` | Le quotient f/dénominateur de Hadamard a un diviseur nul | CONFIRMÉE (domaine : f entière non nulle, sommabilité) | AJOUT | 1 |
| `Complex.Hadamard.exists_entire_nonzero_hadamardQuotient` | Il existe H entière sans zéro avec f = H·z^ordre en 0·produit canonique (quotient de Hadamard) | CONFIRMÉE (domaine : f entière non nulle, sommabilité) | AJOUT | 1 |
| `Complex.Hadamard.bddAbove_norm_divisorCanonicalProduct_div_pow_annulus` | Le module du produit canonique divisé par (z-z₀)^k est borné sur un anneau | CONFIRMÉE (domaine : sommabilité, 0<r1) | AJOUT | 0 |

### `RhGapCriterion.P4Port.Analysis.Complex.HadamardFactorization.Growth`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.no_zero_on_sphere_of_norm_image_avoid` | Si le rayon r évite les normes des zéros de norme ≤ B, f n'a aucun zéro sur la sphère de rayon r (rayon de Cartan) | CONFIRMÉE (domaine : f entière non nulle, 0<r≤B, smallSet fini, évitement, etc.) | AJOUT | 1 |
| `Complex.Hadamard.norm_inv_hadamardDenominator_le_exp_on_cartan_circle` | Sur un cercle de Cartan admissible, l'inverse du dénominateur de Hadamard est majoré en norme par une exponentielle | CONFIRMÉE (domaine : m≤ρ<τ<m+1, sommabilités, cercle de Cartan admissible) | AJOUT | 1 |
| `Complex.Hadamard.hadamardQuotient_norm_le_exp_on_cartan_circle` | Sur un cercle de Cartan admissible, le quotient de Hadamard est majoré par une exponentielle | CONFIRMÉE (domaine : ordre ρ, sommabilités, croissance de f, cercle admissible) | AJOUT | 1 |
| `Complex.Hadamard.hadamardQuotient_norm_le_exp_rpow_of_growth` | Le quotient de Hadamard hérite d'une borne exponentielle d'ordre fini | CONFIRMÉE (domaine : f et H entières, ρ<τ, sommabilités, croissance de f) | AJOUT | 1 |
| `Complex.Hadamard.hadamard_factorization_of_growth` | Factorisation de Hadamard : f à croissance log(1+norme f) ≤ C(1+norme z)^ρ s'écrit exp(P z)·z^ordre·produit canonique, deg P ≤ floor ρ | CONFIRMÉE (domaine : f entière non nulle, ρ≥0, croissance) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.HadamardFactorization.Order`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.analyticOrderNatAt_comp_add_const` | Translation : l'ordre en 0 de w↦f(w+c) est l'ordre de f en c | CONFIRMÉE | AJOUT | 3 |
| `Complex.Hadamard.analyticOrderNatAt_comp_sub_const` | Soustraction : l'ordre en 0 de w↦f(w-c) est l'ordre de f en -c | CONFIRMÉE | AJOUT | 0 |
| `Complex.Hadamard.centeredHadamardDenom_eq_hadamardDenom_translate` | Le dénominateur de Hadamard centré est le dénominateur ordinaire de la fonction translatée | CONFIRMÉE | AJOUT | 0 |
| `Complex.Hadamard.EntireOfOrderAtMost.differentiable` | Une fonction entière d'ordre au plus ρ est différentiable | CONFIRMÉE (domaine : EntireOfOrderAtMost ρ f) | AJOUT | 3 |
| `Complex.Hadamard.EntireOfOrderAtMost.exists_bound` | Une fonction d'ordre au plus ρ vérifie, pour tout ε>0, ‖f z‖ ≤ exp(C(1+‖z‖)^(ρ+ε)) | CONFIRMÉE (domaine : EntireOfOrderAtMost, ε>0) | AJOUT | 3 |
| `Complex.Hadamard.EntireOfOrderAtMost.of_norm_le_exp` | Une borne exponentielle unique d'ordre ρ implique EntireOfOrderAtMost ρ | CONFIRMÉE (domaine : f différentiable, borne exp) | AJOUT | 0 |
| `Complex.Hadamard.EntireOfOrderAtMost.exists_log_growth` | Un ordre fini ρ<τ donne une borne log(1+‖f z‖) ≤ C'(1+‖z‖)^τ | CONFIRMÉE (domaine : EntireOfOrderAtMost ρ, ρ<τ, τ≥0) | AJOUT | 3 |
| `Complex.Hadamard.EntireOfOrderAtMost.comp_add_const` | L'ordre fini est invariant par translation z↦z+c | CONFIRMÉE (domaine : EntireOfOrderAtMost ρ, ρ≥0) | AJOUT | 2 |
| `Complex.Hadamard.EntireOfOrderAtMost.comp_sub_const` | L'ordre fini est invariant par translation z↦z-c | CONFIRMÉE (domaine : EntireOfOrderAtMost ρ, ρ≥0) | AJOUT | 0 |
| `Complex.Hadamard.EntireOfOrderAtMost.summable_norm_inv_pow_divisorZeroIndex₀` | Pour f non nulle d'ordre fini ρ, la somme des ‖a_p‖^-(floor ρ+1) sur les zéros est sommable | CONFIRMÉE (domaine : ρ≥0, f non nulle, EntireOfOrderAtMost) | AJOUT | 1 |
| `Complex.Hadamard.hadamard_factorization_of_order` | Factorisation de Hadamard d'une fonction d'ordre au plus ρ : f = exp(P)·z^ordre·produit canonique de genre floor ρ | CONFIRMÉE (domaine : ρ≥0, f non nulle, ordre fini) | AJOUT | 4 |
| `Complex.Hadamard.hadamard_factorization_of_order_reindex` | Factorisation de Hadamard d'ordre fini, indexée par un type équivalent aux indices de zéros | CONFIRMÉE (domaine : ρ≥0, f non nulle, ordre fini) | AJOUT | 3 |
| `Complex.Hadamard.hadamard_factorization_of_order_sequence` | Factorisation de Hadamard d'ordre fini, indexée par une énumération ℕ des indices de zéros | CONFIRMÉE (domaine : ρ≥0, f non nulle, ordre fini) | AJOUT | 2 |
| `Complex.Hadamard.hadamard_factorization_of_order_centered` | Factorisation de Hadamard centrée en c pour une fonction d'ordre fini | CONFIRMÉE (domaine : ρ≥0, f non nulle, ordre fini) | AJOUT | 1 |
| `Complex.Hadamard.hadamard_factorization_of_order_centered_reindex` | Factorisation de Hadamard centrée, indexée par un type équivalent aux indices de zéros de la translatée | CONFIRMÉE (domaine : ρ≥0, f non nulle, ordre fini) | AJOUT | 1 |
| `Complex.Hadamard.hadamard_factorization_of_order_centered_sequence` | Factorisation de Hadamard centrée, indexée par une énumération ℕ des indices de zéros de la translatée | CONFIRMÉE (domaine : ρ≥0, f non nulle, ordre fini) | AJOUT | 0 |

### `RhGapCriterion.P4Port.Analysis.Complex.HadamardFactorization.Summability`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.Hadamard.jensen_formula_logCounting_eq_circleAverage_sub_log_trailingCoeff` | Formule de Jensen : compteur logarithmique des zéros de f entière au rayon R = moyenne circulaire de log‖f‖ moins log‖coefficient dominant en 0‖ | CONFIRMÉE (domaine : f entière, R≠0) | AJOUT | 0 |
| `Complex.Hadamard.log_two_mul_divisorMassClosedBall₀_le_logCounting_two_mul` | log 2 fois la masse de diviseur dans la boule fermée de rayon R est ≤ compteur logarithmique au rayon 2R | CONFIRMÉE (domaine : f entière, R≥1) | AJOUT | 0 |
| `Complex.Hadamard.divisorMassClosedBall₀_le_of_growth` | La masse de diviseur dans la boule fermée est majorée par une expression en la croissance de f | CONFIRMÉE (domaine : f entière, borne de croissance, R≥1) | AJOUT | 3 |
| `Complex.Hadamard.divisorMassClosedBall₀_mono` | La masse de diviseur de la boule fermée est croissante en R | CONFIRMÉE (domaine : f entière, 0≤R1≤R2) | AJOUT | 0 |
| `Complex.Hadamard.exists_r0_le_norm_divisorZeroIndex₀_val` | Pour f entière non nulle, les zéros non nuls sont à norme ≥ r0>0 | CONFIRMÉE (domaine : f entière non nulle) | AJOUT | 1 |
| `Complex.Hadamard.card_ball_le_divisorMassClosedBall₀` | Le nombre d'indices de zéros de norme ≤ R est majoré par la masse de diviseur de la boule | CONFIRMÉE (domaine : f entière, R>0) | AJOUT | 3 |
| `Complex.Hadamard.card_subtype_le_divisorMassClosedBall₀_of_norm_le` | Une famille finie d'indices de norme ≤ R a un cardinal majoré par la masse de diviseur de la boule | CONFIRMÉE (domaine : f entière, R>0, famille finie dans la boule) | AJOUT | 1 |
| `Complex.Hadamard.divisorZeroIndex₀_dyadicShell_upper_bound` | Borne supérieure de coquille dyadique : la coquille d'un indice est majorée par la partie entière de log2(norme/r0) | CONFIRMÉE (domaine : r0>0, normes ≥ r0, k) | AJOUT | 2 |
| `Complex.Hadamard.divisorZeroIndex₀_dyadicShell_lower_bound` | Borne inférieure de coquille dyadique pour un indice | CONFIRMÉE (domaine : r0>0, normes ≥ r0, k) | AJOUT | 1 |
| `Complex.Hadamard.finite_divisorZeroIndex₀_dyadicShell` | Chaque coquille dyadique des indices de zéros est finie | CONFIRMÉE (domaine : r0>0, normes ≥ r0) | AJOUT | 2 |
| `Complex.Hadamard.tsum_divisorZeroIndex₀_dyadicShell_inv_rpow_le_geometric_of_growth` | La somme sur une coquille dyadique de norme^-τ est majorée par un terme géométrique sous croissance de f | CONFIRMÉE (domaine : ρ≥0, τ>0, f entière, croissance, r0>0, normes ≥ r0, etc.) | AJOUT | 1 |
| `Complex.Hadamard.summable_norm_inv_rpow_divisorZeroIndex₀_of_growth` | Sous croissance d'ordre ρ<τ, la somme des norme^-τ sur les zéros est sommable | CONFIRMÉE (domaine : ρ<τ, f entière non nulle, croissance) | AJOUT | 2 |
| `Complex.Hadamard.summable_norm_inv_pow_divisorZeroIndex₀_of_growth` | Sous croissance d'ordre ρ, la somme des norme^-(floor ρ+1) sur les zéros est sommable | CONFIRMÉE (domaine : ρ≥0, f entière non nulle, croissance) | AJOUT | 2 |

### `RhGapCriterion.P4Port.Analysis.Complex.LocallyUniformLimit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `TendstoUniformlyOn.mul_left_bounded` | Convergence uniforme sur K de F_n vers f implique celle de h·F_n vers h·f si h bornée sur K | CONFIRMÉE (domaine : convergence uniforme, h bornée sur K) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.Norm`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.neg_norm_le_re` | Pour tout complexe z, l'opposé de sa norme est majoré par sa partie réelle. | CONFIRMÉE | AJOUT | 2 |
| `Complex.norm_sub_one_le_one_add_norm` | Pour tout complexe z, la norme de z − 1 est au plus 1 plus la norme de z. | CONFIRMÉE | AJOUT | 2 |
| `Complex.norm_one_sub_le_one_add_norm` | Pour tout complexe z, la norme de 1 − z est au plus 1 plus la norme de z. | CONFIRMÉE | AJOUT | 1 |
| `Complex.one_le_norm_one_sub_of_norm_gt_three` | Si la norme de z dépasse 3, alors la norme de 1 − z est au moins 1. | CONFIRMÉE (domaine : norme de z supérieure à 3) | AJOUT | 1 |
| `Complex.norm_inv_pow_le_one_of_one_le_norm` | Si la norme de u est au moins 1, la norme de l'inverse de u puissance n est au plus 1. | CONFIRMÉE (domaine : norme de u au moins 1) | AJOUT | 1 |
| `Complex.one_sub_ne_one_of_norm_pos` | Si z est de norme strictement positive, alors 1 − z est différent de 1. | CONFIRMÉE (norme de z strictement positive) | AJOUT | 1 |
| `Complex.ne_neg_nat_of_re_pos` | Un complexe de partie réelle strictement positive n'est égal à l'opposé d'aucun entier naturel. | CONFIRMÉE (partie réelle de w strictement positive) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.Trigonometric`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.norm_cos_le_exp_abs_im` | La norme du cosinus complexe est majorée par l'exponentielle de la valeur absolue de la partie imaginaire. | CONFIRMÉE | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.ValueDistribution.LogCounting.Basic`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Function.locallyFinsuppWithin.norm_le_abs_of_mem_toClosedBall_support` | Un point du support de la restriction d'un diviseur à la boule fermée de rayon r a une norme au plus /r/. | CONFIRMÉE (domaine : z dans le support de la troncature à la boule fermée de rayon r) | AJOUT | 3 |
| `Function.locallyFinsuppWithin.toClosedBall_eval_eq_of_norm_le_abs` | Si la norme de z est au plus /r/, la restriction à la boule fermée de rayon r coïncide avec le diviseur D en z. | CONFIRMÉE (domaine : norme de z au plus /r/) | AJOUT | 3 |
| `Function.locallyFinsuppWithin.mem_toClosedBall_support_of_mem_support_of_norm_le_abs` | Un point du support de D situé dans la boule fermée de rayon /r/ reste dans le support de la restriction à cette boule. | CONFIRMÉE (domaine : z dans le support de D et norme de z au plus /r/) | AJOUT | 4 |
| `Function.locallyFinsuppWithin.mem_support_of_mem_toClosedBall_support` | Un point du support de la restriction à la boule fermée appartient au support de D. | CONFIRMÉE (domaine : z dans le support de la restriction à la boule) | AJOUT | 2 |
| `Function.locallyFinsuppWithin.massClosedBall₀_mono` | Pour un diviseur positif, la masse non nulle dans la boule fermée est croissante avec le rayon. | CONFIRMÉE (domaine : D positif, 0 ≤ R1 ≤ R2) | AJOUT | 1 |
| `Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const_of_differentiable` | Formule de Jensen : le comptage logarithmique du diviseur de zéros d'une fonction entière vaut la moyenne circulaire de log‖f‖ moins log du coefficient de queue en 0. | CONFIRMÉE (domaine : f entière, R non nul) | AJOUT | 2 |

### `RhGapCriterion.P4Port.Analysis.Complex.ValueDistribution.LogCounting.Growth`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Function.locallyFinsuppWithin.massClosedBall₀.congr_simp` | Lemme de congruence : la masse de boule fermée ne dépend que de D et R, égaux terme à terme. | CONFIRMÉE (égalité des diviseurs et des rayons) | AJOUT | 0 |
| `Function.locallyFinsuppWithin.logCounting_divisor_le_of_log_growth` | Une croissance logarithmique d'une fonction entière borne le comptage logarithmique de son diviseur sur un disque de rayon R. | CONFIRMÉE (domaine : f entière, croissance logarithmique log(1+‖f‖) ≤ C(1+‖z‖)^ρ, R > 0) | AJOUT | 1 |
| `Function.locallyFinsuppWithin.log_two_mul_massClosedBall₀_le_logCounting` | Pour un diviseur positif, log 2 fois la masse de la boule de rayon R est majoré par le comptage logarithmique au rayon 2R. | CONFIRMÉE (domaine : D positif, R ≥ 1) | AJOUT | 2 |
| `Function.locallyFinsuppWithin.massClosedBall₀_divisor_le_of_log_growth` | La masse de la boule de rayon R du diviseur d'une fonction entière à croissance logarithmique est majorée par (C(1+/2R/)^ρ + /log‖coefficient de queue‖/)/log 2. | CONFIRMÉE (domaine : f entière à croissance logarithmique, R ≥ 1) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.Complex.WeierstrassFactor`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.weierstrassFactor_def` | Le facteur de Weierstrass d'ordre m vaut (1 − z) fois l'exponentielle de la somme partielle logarithmique. | CONFIRMÉE | AJOUT | 2 |
| `Complex.weierstrassFactor_zero` | Le facteur de Weierstrass d'ordre 0 vaut 1 − z. | CONFIRMÉE | AJOUT | 0 |
| `Complex.weierstrassFactor_at_zero` | Le facteur de Weierstrass d'ordre m vaut 1 en 0. | CONFIRMÉE | AJOUT | 3 |
| `Complex.weierstrassFactor_at_one` | Le facteur de Weierstrass d'ordre m vaut 0 en 1. | CONFIRMÉE | AJOUT | 2 |
| `Complex.weierstrassFactor_eq_zero_iff` | Le facteur de Weierstrass d'ordre m s'annule exactement en z = 1. | CONFIRMÉE | AJOUT | 6 |
| `Complex.weierstrassFactor_ne_zero_iff` | Le facteur de Weierstrass d'ordre m est non nul exactement quand z ≠ 1. | CONFIRMÉE | AJOUT | 2 |
| `Complex.weierstrassFactor_ne_zero_of_ne_one` | Le facteur de Weierstrass d'ordre m est non nul en tout z différent de 1. | CONFIRMÉE (z différent de 1) | AJOUT | 3 |
| `Complex.weierstrassFactor_div_eq_zero_iff` | Le facteur de Weierstrass évalué en z/a s'annule si et seulement si z = a. | CONFIRMÉE (a non nul) | AJOUT | 1 |
| `Complex.weierstrassFactor_div_ne_zero_iff` | Le facteur de Weierstrass évalué en z/a est non nul si et seulement si z différent de a. | CONFIRMÉE (a non nul) | AJOUT | 1 |
| `Complex.differentiable_weierstrassFactor` | Le facteur de Weierstrass d'ordre m est différentiable sur tout ℂ. | CONFIRMÉE | AJOUT | 10 |
| `Complex.hasDerivAt_weierstrassFactor_at_one` | Le facteur de Weierstrass d'ordre m a en 1 la dérivée moins l'exponentielle de la somme partielle logarithmique en 1. | CONFIRMÉE | AJOUT | 2 |
| `Complex.deriv_weierstrassFactor_at_one` | La dérivée en 1 du facteur de Weierstrass d'ordre m vaut moins l'exponentielle de la somme partielle logarithmique en 1. | CONFIRMÉE | AJOUT | 1 |
| `Complex.deriv_weierstrassFactor_at_one_ne_zero` | La dérivée en 1 du facteur de Weierstrass d'ordre m est non nulle. | CONFIRMÉE | AJOUT | 0 |
| `Complex.hasDerivAt_weierstrassFactor_div_at_self` | Le facteur de Weierstrass en z/a a en a la dérivée −exp(partialLogSum m 1)/a. | CONFIRMÉE (a non nul) | AJOUT | 1 |
| `Complex.deriv_weierstrassFactor_div_at_self` | La dérivée en a de z ↦ facteur de Weierstrass en z/a vaut −exp(partialLogSum m 1)/a. | CONFIRMÉE (a non nul) | AJOUT | 1 |
| `Complex.deriv_weierstrassFactor_div_at_self_ne_zero` | La dérivée en a de z ↦ facteur de Weierstrass en z/a est non nulle. | CONFIRMÉE (a non nul) | AJOUT | 0 |
| `Complex.analyticOrderAt_weierstrassFactor_div_self` | Le facteur de Weierstrass en z/a a un ordre analytique égal à 1 en a (zéro simple). | CONFIRMÉE (a non nul) | AJOUT | 2 |
| `Complex.analyticOrderNatAt_weierstrassFactor_div_self` | L'ordre analytique à valeur naturelle de z ↦ facteur de Weierstrass en z/a en a vaut 1. | CONFIRMÉE (a non nul) | AJOUT | 0 |
| `Complex.weierstrassFactor_eq_exp_neg_tail` | Sur le disque unité ouvert privé de 1, le facteur de Weierstrass vaut exp(−queue logarithmique d'ordre m). | CONFIRMÉE (domaine : norme de z < 1 et z ≠ 1) | AJOUT | 2 |
| `Complex.weierstrassFactor_sub_one_pow_bound` | Si la norme de z est au plus 1/2, la norme de E_m(z) − 1 est au plus 4‖z‖^(m+1). | CONFIRMÉE (domaine : norme de z au plus 1/2) | AJOUT | 4 |
| `Complex.log_norm_weierstrassFactor_ge_log_norm_one_sub_sub` | log‖1 − z‖ moins la norme de la somme partielle logarithmique minore log‖E_m(z)‖. | CONFIRMÉE | AJOUT | 2 |
| `Complex.log_norm_weierstrassFactor_ge_neg_two_pow` | Si la norme de z est au plus 1/2, log‖E_m(z)‖ est au moins −2‖z‖^(m+1). | CONFIRMÉE (domaine : norme de z au plus 1/2) | AJOUT | 1 |
| `Complex.log_norm_weierstrassFactor_ge_log_norm_one_sub_nat_mul_max_one_norm_pow` | log‖1 − z‖ − m·max(1,‖z‖^m) minore log‖E_m(z)‖ pour tout z. | CONFIRMÉE | AJOUT | 0 |
| `_private.RhGapCriterion.P4Port.Analysis.Complex.WeierstrassFactor.0.Complex.eventually_le_norm_div_two_of_summable_inv_pow` | Lemme privé : sous sommabilité des inverses de puissance, ‖a_n‖/2 dépasse R à partir d'un certain rang. | CONFIRMÉE (domaine : série des ‖a_n‖^{-(m+1)} sommable, a_n non nuls, R ≥ 0) | AJOUT | 2 |
| `_private.RhGapCriterion.P4Port.Analysis.Complex.WeierstrassFactor.0.Complex.summable_scaled_bound_of_summable_inv_pow` | Lemme privé : la série 4R^(m+1)/‖a_n‖^(m+1) est sommable. | CONFIRMÉE (domaine : série des ‖a_n‖^{-(m+1)} sommable, R ≥ 0) | AJOUT | 2 |
| `Complex.continuousOn_weierstrassFactor_div` | La fonction z ↦ facteur de Weierstrass en z/a est continue sur tout ensemble. | CONFIRMÉE | AJOUT | 1 |
| `Complex.norm_weierstrassFactor_div_sub_one_le_pow_div` | Si ‖z‖ ≤ ‖a‖/2, la norme de E_m(z/a) − 1 est au plus 4‖z‖^(m+1)/‖a‖^(m+1). | CONFIRMÉE (domaine : norme de z au plus ‖a‖/2) | AJOUT | 2 |
| `Complex.summable_norm_weierstrassFactor_div_sub_one_of_summable_inv_pow` | La série des normes de E_m(z/a_n) − 1 est sommable pour tout z. | CONFIRMÉE (domaine : sommabilité des inverses de puissance, a_n non nuls) | AJOUT | 1 |
| `Complex.hasProdUniformlyOn_weierstrassFactor_div_of_bound` | Le produit des facteurs de Weierstrass E_{m_n}(z/a_n) converge uniformément sur le compact K. | CONFIRMÉE (domaine : K compact, borne R sur K, ‖a_n‖ ≥ 2R à terme, série 4R^(m_n+1)/‖a_n‖^(m_n+1) sommable) | AJOUT | 1 |
| `Complex.hasProdLocallyUniformlyOn_weierstrassFactor_div` | Le produit des facteurs de Weierstrass converge localement uniformément sur l'ouvert s. | CONFIRMÉE (domaine : ouvert s, minoration de ‖a_n‖ et sommabilité pour tout R) | AJOUT | 2 |
| `Complex.hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow` | Le produit des E_m(z/a_n) converge localement uniformément sur tout ℂ. | CONFIRMÉE (domaine : sommabilité des inverses de puissance, a_n non nuls) | AJOUT | 3 |
| `Complex.multipliableLocallyUniformlyOn_weierstrassFactor_div` | Le produit des facteurs de Weierstrass est multipliable localement uniformément sur l'ouvert s. | CONFIRMÉE SOUS CONDITION (ouvert s, mêmes hypothèses de croissance et de sommabilité) | AJOUT | 0 |
| `Complex.multipliableLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow` | Le produit des E_m(z/a_n) est multipliable localement uniformément sur ℂ. | CONFIRMÉE (domaine : sommabilité des inverses de puissance, a_n non nuls) | AJOUT | 0 |

### `RhGapCriterion.P4Port.Analysis.Meromorphic.DivisorHolomorphic`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Differentiable.divisor_nonneg` | Le diviseur d'une fonction entière est positif ou nul. | CONFIRMÉE (domaine : f différentiable sur ℂ) | AJOUT | 5 |

### `RhGapCriterion.P4Port.Analysis.Meromorphic.DivisorSupport`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `MeromorphicOn.divisor_support_discrete` | Le support du diviseur méromorphe est discret. | CONFIRMÉE | AJOUT | 3 |
| `MeromorphicOn.divisor_support_countable` | Le support du diviseur méromorphe est dénombrable. | CONFIRMÉE | AJOUT | 2 |
| `MeromorphicOn.divisor_support_inter_compact_finite` | L'intersection d'un compact K inclus dans U avec le support du diviseur est finie. | CONFIRMÉE (domaine : K compact inclus dans U) | AJOUT | 1 |
| `MeromorphicOn.exists_ball_inter_divisor_support_eq_singleton` | Tout point du support du diviseur a une boule dans laquelle il est l'unique point du support. | CONFIRMÉE (domaine : z0 dans le support du diviseur) | AJOUT | 0 |
| `MeromorphicOn.exists_seq_eq_range_divisor_support` | Le support d'un diviseur non vide est l'image d'une suite. | CONFIRMÉE (domaine : support non vide) | AJOUT | 0 |
| `MeromorphicOn.exists_nonzero_seq_divisor_support_diff_zero` | Il existe une suite de termes non nuls dont l'image contient le support du diviseur privé de 0. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.P4Port.Analysis.SpecialFunctions.CompletedXi`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.riemannXi_zero` | La fonction xi de Riemann complétée vaut 1/2 en 0. | CONFIRMÉE | AJOUT | 2 |
| `Complex.riemannXi_nontrivial` | La fonction xi de Riemann n'est pas identiquement nulle. | CONFIRMÉE | AJOUT | 5 |
| `Complex.differentiable_riemannXi` | La fonction xi de Riemann est entière. | CONFIRMÉE | AJOUT | 6 |
| `Complex.riemannXi_eq_mul_completedRiemannZeta` | Hors des pôles, xi(s) = s(s−1)·(zêta complétée en s)/2. | CONFIRMÉE (s différent de 0 et de 1) | AJOUT | 2 |
| `Complex.riemannXi_one_sub` | Équation fonctionnelle : xi(1 − s) = xi(s) pour tout s. | CONFIRMÉE | AJOUT | 2 |

### `RhGapCriterion.P4Port.Analysis.SpecialFunctions.Complex.LogBounds`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Real.pow_div_one_sub_le_two_mul` | Si 0 ≤ r ≤ 1/2, r^(m+1)/(1−r) est majoré par 2r^(m+1). | CONFIRMÉE (domaine : 0 ≤ r ≤ 1/2) | AJOUT | 1 |
| `Complex.neg_log_one_sub_eq_tsum` | Sur le disque unité ouvert, −log(1−z) est la série des z^(n+1)/(n+1). | CONFIRMÉE (domaine : norme de z < 1) | AJOUT | 1 |
| `Complex.partialLogSum_zero` | La somme partielle logarithmique d'ordre 0 est nulle. | CONFIRMÉE | AJOUT | 3 |
| `Complex.partialLogSum_at_zero` | La somme partielle logarithmique d'ordre m est nulle en 0. | CONFIRMÉE | AJOUT | 1 |
| `Complex.logTaylor_succ_neg` | Récurrence de logTaylor en −z : logTaylor(n+1)(−z) = logTaylor n (−z) − z^n/n. | CONFIRMÉE | AJOUT | 2 |
| `Complex.partialLogSum_succ` | Récurrence de la somme partielle logarithmique : ordre m+1 = ordre m plus z^(m+1)/(m+1). | CONFIRMÉE | AJOUT | 0 |
| `Complex.logTaylor_neg_eq_neg_sum` | logTaylor(m+1)(−z) est l'opposé de la somme finie des z^(k+1)/(k+1) pour k < m. | CONFIRMÉE | AJOUT | 1 |
| `Complex.partialLogSum_eq_sum` | La somme partielle logarithmique d'ordre m est la somme sur k < m des z^(k+1)/(k+1). | CONFIRMÉE | AJOUT | 3 |
| `Complex.hasDerivAt_partialLogSum` | La somme partielle logarithmique d'ordre m a pour dérivée la somme finie des z^j pour j < m. | CONFIRMÉE | AJOUT | 2 |
| `Complex.differentiable_partialLogSum` | La somme partielle logarithmique d'ordre m est différentiable. | CONFIRMÉE | AJOUT | 2 |
| `Complex.summable_logTail` | La série de queue logarithmique est sommable sur le disque unité ouvert. | CONFIRMÉE (domaine : norme de z < 1) | AJOUT | 1 |
| `Complex.norm_logTail_le` | La queue logarithmique d'ordre m est de norme au plus ‖z‖^(m+1)/(1−‖z‖). | CONFIRMÉE (domaine : norme de z < 1) | AJOUT | 1 |
| `Complex.norm_logTail_le_two_mul_norm_pow` | La queue logarithmique d'ordre m est de norme au plus 2‖z‖^(m+1). | CONFIRMÉE (domaine : norme de z < 1 et ≤ 1/2) | AJOUT | 2 |
| `Complex.norm_partialLogSum_le_nat_mul_max_one_norm_pow` | La norme de la somme partielle logarithmique d'ordre m est majorée par m·max(1,‖z‖^m). | CONFIRMÉE | AJOUT | 2 |
| `Complex.neg_log_one_sub_eq_partialLogSum_add_logTail` | Sur le disque unité, −log(1−z) est la somme partielle d'ordre m plus la queue d'ordre m. | CONFIRMÉE (domaine : norme de z < 1) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.SpecialFunctions.Exp`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Real.le_exp_self` | Pour tout réel x, x est majoré par exp x. | CONFIRMÉE | AJOUT | 4 |
| `Real.mul_four_le_exp_add` | Le produit a·b·c·d est majoré par exp(A+B+C+D) quand chaque facteur est majoré par exp de sa borne et b, c, d sont positifs. | CONFIRMÉE (domaine : trois positivités et quatre majorations exponentielles) | AJOUT | 1 |
| `Real.two_mul_le_exp_two_mul_sq` | Si x ≤ A et 1 ≤ A, alors 2x est majoré par exp(2A²). | CONFIRMÉE (domaine : x ≤ A et 1 ≤ A) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.SpecialFunctions.Gamma.DigammaSeries`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.norm_natCast_add_one` | La norme de n+1 (entier naturel plongé dans ℂ) est n+1. | CONFIRMÉE | AJOUT | 3 |
| `Complex.sum_inv_natCast_add_one` | La somme des 1/(m+1) pour m < n est le nombre harmonique d'ordre n (dans ℂ). | CONFIRMÉE | AJOUT | 1 |
| `Complex.sum_inv_natCast_add_one_real` | La somme des 1/(m+1) pour m < n est le nombre harmonique d'ordre n (version réelle). | CONFIRMÉE | AJOUT | 1 |
| `Complex.inv_add_one_sub_inv_eq` | Terme de la série du digamma : 1/(m+1) − 1/(z+m) = (z−1)/((m+1)(z+m)). | CONFIRMÉE (z + m non nul) | AJOUT | 1 |
| `Complex.norm_inv_add_one_sub_inv_le` | Borne de Weierstrass sur le terme de la série du digamma dans une sous-bande bornée du demi-plan droit : au plus (R+1)/(a(m+1)²). | CONFIRMÉE (domaine : 0 < a ≤ 1, a ≤ Re z, ‖z‖ ≤ R) | AJOUT | 4 |
| `Complex.norm_inv_add_one_sub_inv_le'` | Borne à décroissance linéaire du terme de la série du digamma sur un demi-plan droit : au plus 2/(a(m+1)). | CONFIRMÉE (domaine : 0 < a ≤ 1, a ≤ Re z) | AJOUT | 1 |
| `Complex.summable_one_div_natCast_add_one_sq` | La série des 1/(m+1)² est sommable. | CONFIRMÉE | AJOUT | 7 |
| `Complex.hasSum_sub_succ_of_tendsto_zero` | Une série télescopique sommable dont les termes tendent vers 0 a pour somme son premier terme. | CONFIRMÉE (domaine : a_n tend vers 0 et la série télescopique est sommable) | AJOUT | 2 |
| `Complex.tsum_one_div_natCast_add_add_one_sq_le` | La queue de la série des 1/(m+1)² au-delà de N est au plus 1/N. | CONFIRMÉE (N ≥ 1) | AJOUT | 1 |
| `Complex.logGammaSeq_succ_sub` | Incrément de logGammaSeq en forme close : z·(log(n+1) − log n) − log(1 + z/(n+1)). | CONFIRMÉE (Re z > 0) | AJOUT | 1 |
| `Complex.cauchySeq_logGammaSeq` | Pour Re z > 0, la suite logGammaSeq z est de Cauchy. | CONFIRMÉE (Re z > 0) | AJOUT | 1 |
| `Complex.exp_logGammaSeq` | Sur le demi-plan droit, exp(logGammaSeq z n) = GammaSeq z n pour n non nul. | CONFIRMÉE (Re z > 0 et n non nul) | AJOUT | 1 |
| `Complex.hasSum_digamma_of_re_pos` | Sur le demi-plan droit, la série des 1/(m+1) − 1/(z0+m) a pour somme digamma z0 + γ. | CONFIRMÉE (Re z0 > 0) | AJOUT | 1 |
| `Complex.hasSum_digamma` | Représentation en série du digamma : somme des 1/(n+1) − 1/(n+z) égale digamma z + γ. | CONFIRMÉE (z hors des pôles de Gamma) | AJOUT | 2 |
| `Complex.digamma_eq_tsum` | digamma z = −γ + somme des (1/(n+1) − 1/(n+z)). | CONFIRMÉE (z hors des pôles de Gamma) | AJOUT | 2 |
| `Complex.continuousOn_digamma_of_re_ge_norm_le` | Le digamma est continu sur les sous-bandes fermées bornées {Re z ≥ a, ‖z‖ ≤ R}. | CONFIRMÉE (domaine : 0 < a ≤ 1) | AJOUT | 1 |
| `Complex.continuousAt_digamma_of_re_pos` | Le digamma est continu en tout point du demi-plan droit ouvert. | CONFIRMÉE (Re z0 > 0) | AJOUT | 0 |
| `Complex.differentiableOn_digamma_of_re_gt_norm_lt` | Le digamma est différentiable sur les sous-bandes ouvertes bornées {Re z > a, ‖z‖ < R}. | CONFIRMÉE (domaine : 0 < a ≤ 1) | AJOUT | 1 |
| `Complex.differentiableAt_digamma_of_re_pos` | Le digamma est différentiable en tout point du demi-plan droit ouvert. | CONFIRMÉE (Re z0 > 0) | AJOUT | 0 |
| `Complex.exists_norm_digamma_le_log` | Sur la bande a ≤ Re z ≤ b, la norme de digamma est au plus C·log(/Im z/+2) pour une constante C > 0. | CONFIRMÉE (0 < a) | AJOUT | 4 |
| `Complex.exists_norm_digamma_div_two_le_log` | Sur la bande a ≤ Re w ≤ b, la norme de digamma(w/2) est au plus C·log(/Im w/+2). | CONFIRMÉE (0 < a) | AJOUT | 0 |

### `RhGapCriterion.P4Port.Analysis.SpecialFunctions.Gamma.GammaStirlingAux`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Stirling.GammaAux.norm_sub_real_le` | Si 0 < a < Re s, ‖s − a‖ ≤ ‖s‖. | CONFIRMÉE (domaine : 0 < a < Re s) | AJOUT | 1 |
| `Stirling.GammaAux.norm_shift_le` | Si k+1 < Re s, ‖s − 1 − k‖ ≤ ‖s‖. | CONFIRMÉE (domaine : k+1 < Re s) | AJOUT | 1 |
| `Stirling.GammaAux.prod_norm_le_pow` | La norme du produit des (s−1−k) pour k < m est au plus ‖s‖^m. | CONFIRMÉE (domaine : k+1 < Re s pour tout k < m) | AJOUT | 1 |
| `Stirling.GammaAux.Gamma_iterate` | Gamma s = Gamma(s − n) fois le produit des (s−1−k) pour k < n. | CONFIRMÉE (domaine : s − 1 − k non nul pour k < n) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.SpecialFunctions.Gamma.IntegralBounds`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Real.Gamma.le_one_of_mem_Icc` | Pour x dans [1,2], Gamma réel de x est au plus 1. | CONFIRMÉE (domaine : 1 ≤ x ≤ 2) | AJOUT | 1 |
| `Complex.Gamma.norm_le_Gamma_re` | Pour Re z > 0, la norme de Gamma z est au plus Gamma(Re z). | CONFIRMÉE (Re z > 0) | AJOUT | 2 |
| `Complex.Gamma.norm_le_one` | Pour 1 ≤ Re z ≤ 2, la norme de Gamma z est au plus 1. | CONFIRMÉE (domaine : 1 ≤ Re z ≤ 2) | AJOUT | 1 |
| `Complex.Gamma.norm_sq_le_Gamma_re_sq` | Forme carrée de ‖Gamma z‖ ≤ Gamma(Re z). | CONFIRMÉE (Re z > 0) | AJOUT | 1 |
| `Complex.Gamma.norm_sq_le_norm_sq_Gamma_re` | Le carré de ‖Gamma z‖ est au plus le carré de ‖Gamma(Re z)‖ (valeur sur l'axe réel). | CONFIRMÉE (Re z ≥ 1/2) | AJOUT | 0 |

### `RhGapCriterion.P4Port.Analysis.SpecialFunctions.Gamma.StripBounds`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Real.Stirling.log_one_add_ge_log_two` | Pour x ≥ 1, log 2 ≤ log(1+x). | CONFIRMÉE (x ≥ 1) | AJOUT | 4 |
| `Real.Stirling.log_one_add_pos` | Pour x ≥ 1, log(1+x) > 0. | CONFIRMÉE (x ≥ 1) | AJOUT | 0 |
| `Real.Stirling.sqrt_pi_lt_two` | √π < 2. | CONFIRMÉE | AJOUT | 1 |
| `Real.Stirling.log_two_le_mul_log_one_add` | Pour x ≥ 1, log 2 ≤ x·log(1+x). | CONFIRMÉE (x ≥ 1) | AJOUT | 1 |
| `Real.Stirling.log_three_le_coef_mul_log_one_add` | Pour x ≥ 1, log 3 ≤ (log 3/log 2)·log(1+x). | CONFIRMÉE (x ≥ 1) | AJOUT | 1 |
| `Real.Stirling.half_shift_log_constant_pos` | La constante half_shift_log_constant est strictement positive. | CONFIRMÉE | AJOUT | 1 |
| `Complex.Gamma.norm_add_one_le_two_mul_norm` | Si ‖s‖ ≥ 1, ‖s+1‖ ≤ 2‖s‖. | CONFIRMÉE (‖s‖ ≥ 1) | AJOUT | 1 |
| `Complex.Gamma.norm_div_two_add_one_le_three_halves_mul` | Si ‖s‖ ≥ 1, ‖s/2+1‖ ≤ (3/2)‖s‖. | CONFIRMÉE (‖s‖ ≥ 1) | AJOUT | 2 |
| `Complex.Gamma.log_one_add_norm_add_one_le` | Si ‖s‖ ≥ 1, log(1+‖s+1‖) ≤ log 2 + log(1+‖s‖). | CONFIRMÉE (‖s‖ ≥ 1) | AJOUT | 1 |
| `Complex.Gamma.log_one_add_norm_div_two_add_one_le` | Si ‖s‖ ≥ 1, log(1+‖s/2+1‖) ≤ log 3 + log(1+‖s‖). | CONFIRMÉE (‖s‖ ≥ 1) | AJOUT | 1 |
| `Complex.Gamma.norm_mul_log_shift_add_one_bound` | Si ‖s‖ ≥ 1, ‖s+1‖·log(1+‖s+1‖) ≤ 4·‖s‖·log(1+‖s‖). | CONFIRMÉE (‖s‖ ≥ 1) | AJOUT | 1 |
| `Complex.Gamma.norm_mul_log_shift_half_bound` | Si ‖s‖ ≥ 1, ‖s/2+1‖·log(1+‖s/2+1‖) est majoré par une constante fois ‖s‖·log(1+‖s‖). | CONFIRMÉE (‖s‖ ≥ 1) | AJOUT | 1 |
| `Complex.Gamma.norm_Gamma_le_two_mul_norm_Gamma_add_one` | Si z ≠ 0 et ‖z‖ ≥ 1/2, ‖Gamma z‖ ≤ 2‖Gamma(z+1)‖. | CONFIRMÉE (domaine : z non nul et ‖z‖ ≥ 1/2) | AJOUT | 1 |
| `Complex.Gamma.norm_bounded_on_compact_of_no_poles` | Gamma est bornée sur tout compact ne contenant aucun entier négatif ou nul. | CONFIRMÉE (domaine : K compact sans entier négatif ou nul) | AJOUT | 0 |
| `Complex.Gamma.norm_le_strip` | Sur la bande 0 < a ≤ Re w ≤ 1, ‖Gamma w‖ ≤ 1/a + √π. | CONFIRMÉE (domaine : 0 < a ≤ Re w ≤ 1) | AJOUT | 1 |
| `Complex.Gamma.norm_le_four_of_re_half_to_one` | Sur 1/2 ≤ Re w ≤ 1, ‖Gamma w‖ ≤ 4. | CONFIRMÉE (domaine : 1/2 ≤ Re w ≤ 1) | AJOUT | 0 |
| `Complex.Gamma.floor_shift_re_in_strip` | Pour tout s, la partie réelle de s − ⌊Re s⌋ est dans [0,1). | CONFIRMÉE | AJOUT | 0 |
| `Complex.Gamma.norm_bound_re_ge_one` | Il existe C > 0 tel que pour Re s ≥ 1, ‖Gamma s‖ ≤ C(1+‖s‖)^(‖s‖+1). | CONFIRMÉE | AJOUT | 1 |
| `Complex.Gamma.stirling_bound_re_ge_zero` | Borne de Stirling : il existe C > 0 tel que, pour Re s ≥ 0 et ‖s‖ ≥ 1, ‖Gamma s‖ ≤ exp(C‖s‖log(1+‖s‖)). | CONFIRMÉE | AJOUT | 2 |
| `Complex.Gamma.half_bound_re_ge_zero` | Il existe C > 0 tel que, pour Re s ≥ 0 et ‖s‖ ≥ 1, ‖Gamma(s/2)‖ ≤ exp(C‖s‖log(1+‖s‖)). | CONFIRMÉE | AJOUT | 1 |
| `Complex.Gammaℝ.Stirling.norm_cpow_pi_neg_half_le_one` | Si Re s ≥ 0, la norme de π^(−s/2) est au plus 1. | CONFIRMÉE (Re s ≥ 0) | AJOUT | 1 |
| `Complex.Gammaℝ.Stirling.norm_cpow_two_mul_pi_neg_le_one` | Si Re w ≥ 0, la norme de (2π)^(−w) est au plus 1. | CONFIRMÉE (Re w ≥ 0) | AJOUT | 1 |
| `Complex.Gammaℝ.Stirling.bound_re_ge_zero` | Il existe C > 0 tel que, pour Re s ≥ 0 et ‖s‖ ≥ 1, ‖Gamma_R(s)‖ ≤ exp(C‖s‖log(1+‖s‖)). | CONFIRMÉE | AJOUT | 2 |
| `Complex.Gammaℝ.Stirling.finite_order` | Gamma_R est d'ordre fini : il existe A, B > 0 avec ‖Gamma_R(s)‖ ≤ exp(A‖s‖^B) pour Re s ≥ 0 et ‖s‖ ≥ 1. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.P4Port.Analysis.SpecialFunctions.GammaBounds`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `_private.RhGapCriterion.P4Port.Analysis.SpecialFunctions.GammaBounds.0.Real.Gamma.le_Gamma_one_half` | Lemme privé : Gamma réel en a est au plus Gamma(1/2) pour a dans [1/2,1]. | CONFIRMÉE (domaine : 1/2 ≤ a ≤ 1) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.Analysis.SpecialFunctions.GammaBounds.0.integral_exp_neg_rpow_Ioi_one_le` | Lemme privé : l'intégrale de exp(−t)·t^(a−1) sur ]1,∞[ est au plus √π pour a dans [1/2,1]. | CONFIRMÉE (domaine : 1/2 ≤ a ≤ 1) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.Analysis.SpecialFunctions.GammaBounds.0.integral_rpow_Ioc_zero_one` | Lemme privé : l'intégrale de t^(s−1) sur ]0,1] vaut 1/s. | CONFIRMÉE (s > 0) | AJOUT | 1 |
| `Complex.Gamma.norm_le_one_div_add_sqrt_pi_of_re_ge_of_re_le` | Si 0 < a ≤ Re w ≤ 1, ‖Gamma w‖ ≤ 1/a + √π. | CONFIRMÉE (domaine : 0 < a ≤ Re w ≤ 1) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.SpecialFunctions.ImproperIntegrals`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `integral_interval_rpow_neg_one_sub` | L'intégrale de u^(−1−ε) sur [m,n] vaut (m^(−ε) − n^(−ε))/ε. | CONFIRMÉE (domaine : ε > 0, 1 ≤ m ≤ n) | AJOUT | 1 |
| `integral_interval_rpow_neg_le` | L'intégrale de u^(−1−ε) sur [m,n] est au plus m^(−ε)/ε. | CONFIRMÉE (domaine : ε > 0, 1 ≤ m ≤ n) | AJOUT | 0 |
| `intervalIntegral.tendsto_integral_Ioi_of_ae_norm_le` | Les intégrales de c à N de f tendent vers l'intégrale sur ]c,∞[ quand N tend vers l'infini. | CONFIRMÉE (domaine : f mesurable, /f/ ≤ g presque partout, g intégrable sur ]c,∞[) | AJOUT | 1 |
| `integral_Ioi_rpow_neg_re_sub_one` | Pour Re s > 0, l'intégrale de u^(−Re s − 1) sur ]1,∞[ vaut 1/Re s. | CONFIRMÉE (Re s > 0) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.SpecialFunctions.Log.Dyadic`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Real.two_pow_floor_logb_le` | Pour x ≥ 1, 2^⌊log2 x⌋ ≤ x. | CONFIRMÉE (x ≥ 1) | AJOUT | 1 |
| `Real.lt_two_pow_floor_logb_add_one` | Pour x ≥ 1, x < 2^(⌊log2 x⌋+1). | CONFIRMÉE (x ≥ 1) | AJOUT | 1 |
| `Real.dyadicShell_lower_bound` | Si k = ⌊log2(x/r0)⌋, alors r0·2^k ≤ x. | CONFIRMÉE (domaine : r0 > 0, r0 ≤ x, plancher égal à k) | AJOUT | 1 |
| `Real.dyadicShell_upper_bound` | Si k = ⌊log2(x/r0)⌋, alors x ≤ r0·2^(k+1). | CONFIRMÉE (domaine : r0 > 0, r0 ≤ x, plancher égal à k) | AJOUT | 1 |
| `Real.exists_nat_le_two_pow` | Pour tout réel A, il existe k0 tel que A ≤ 2^n pour tout n ≥ k0. | CONFIRMÉE | AJOUT | 1 |
| `Real.one_le_dyadicRadius_succ_of_inv_le_two_pow` | Passée l'échelle 1/r0, le rayon dyadique r0·2^(k+1) est au moins 1. | CONFIRMÉE (domaine : échelle dyadique passée 1/r0, k0 ≤ k+1) | AJOUT | 1 |
| `Real.one_add_abs_two_mul_dyadicRadius_rpow_le` | (1+/2·r0·2^(k+1)/)^ρ est majoré par (1+4r0)^ρ·(2^ρ)^k. | CONFIRMÉE (domaine : r0 > 0, ρ ≥ 0) | AJOUT | 1 |
| `Real.tsum_inv_rpow_le_card_mul_of_lower_bound` | Une coquille finie de rayons minorés par R contribue au plus card·(R⁻¹)^τ à la somme des puissances inverses. | CONFIRMÉE (domaine : type fini, R > 0, τ > 0, a_x ≥ R) | AJOUT | 1 |
| `Real.inv_dyadicRadius_rpow_eq` | (r0·2^k)⁻¹^τ = r0⁻¹^τ·(2^(−τ))^k. | CONFIRMÉE (r0 ≥ 0) | AJOUT | 2 |
| `Real.two_rpow_sub_eq_mul_neg` | 2^(ρ−τ) = 2^ρ·2^(−τ). | CONFIRMÉE | AJOUT | 1 |
| `Real.two_rpow_sub_pow_eq_mul_pow` | (2^(ρ−τ))^k = (2^ρ)^k·(2^(−τ))^k. | CONFIRMÉE | AJOUT | 1 |
| `Real.dyadic_growth_inv_term_eq` | Identité de terme inverse dyadique : C/L·(M·(2^ρ)^k)·(r0·2^k)⁻¹^τ = C/L·M·r0⁻¹^τ·(2^(ρ−τ))^k. | CONFIRMÉE (r0 ≥ 0) | AJOUT | 1 |
| `Real.dyadic_trailing_inv_term_le` | Le terme de queue C/L·(r0·2^k)⁻¹^τ est majoré par (C/L+1)·r0⁻¹^τ·(2^(−τ))^k. | CONFIRMÉE (r0 ≥ 0) | AJOUT | 1 |
| `Real.dyadic_growth_mass_mul_inv_le_geometric` | Sous ces majorations, T est majoré par un terme géométrique en 2^(ρ−τ) plus un terme géométrique en 2^(−τ). | CONFIRMÉE (domaine : L > 0, C ≥ 0, r0 ≥ 0, X ≤ M(2^ρ)^k, T ≤ (CX+Ctrail)/L·(r0 2^k)⁻¹^τ) | AJOUT | 1 |
| `Real.two_geometric_shift_add` | A·q^(k+k0) + B·qσ^(k+k0) = A·q^k0·q^k + B·qσ^k0·qσ^k. | CONFIRMÉE | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.SpecialFunctions.Log.ExpGrowth`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Real.log_norm_le_log_one_add_norm` | Pour tout w, log‖w‖ ≤ log(1+‖w‖). | CONFIRMÉE | AJOUT | 1 |
| `Real.log_nonneg_mul_inv_norm_of_norm_le` | Si ‖z‖ ≤ r, alors log(r·‖z‖⁻¹) ≥ 0. | CONFIRMÉE (domaine : ‖z‖ ≤ r) | AJOUT | 1 |
| `Real.log_two_le_log_two_mul_mul_inv_norm_of_norm_le` | Si z ≠ 0 et ‖z‖ ≤ R, log 2 ≤ log(2R‖z‖⁻¹). | CONFIRMÉE (domaine : z non nul, ‖z‖ ≤ R) | AJOUT | 1 |
| `Real.norm_le_exp_mul_rpow_of_exponent_le` | Une borne ‖f‖ ≤ exp(C r^ρ) s'affaiblit en exposant τ ≥ ρ quand r ≥ 1. | CONFIRMÉE (domaine : C ≥ 0, r_x ≥ 1, ρ ≤ τ, borne exponentielle d'exposant ρ) | AJOUT | 2 |
| `Real.norm_le_exp_mul_rpow_of_log_growth` | Une borne log(1+‖f‖) ≤ C r^ρ donne ‖f‖ ≤ exp(C r^τ) pour tout τ ≥ ρ. | CONFIRMÉE (domaine : C ≥ 0, r_x ≥ 1, ρ ≤ τ, croissance logarithmique d'exposant ρ) | AJOUT | 1 |
| `Real.log_growth_of_norm_le_exp_mul_rpow` | Une borne ‖f‖ ≤ exp(C r^τ) donne une borne log(1+‖f‖) ≤ C' r^τ avec C' > 0. | CONFIRMÉE (domaine : C > 0, τ ≥ 0, r_x ≥ 1, borne exponentielle) | AJOUT | 2 |
| `Real.exists_norm_le_exp_mul_pow_of_rpow_bound` | Une borne exponentielle d'exposant réel τ s'affaiblit en un exposant entier n > τ. | CONFIRMÉE (domaine : r_x ≥ 1, τ < n, borne exponentielle d'exposant réel τ) | AJOUT | 1 |
| `Real.sq_le_exp_const_mul_rpow` | Pour b > 0 et r ≥ 1, r² ≤ exp((4/b)·r^b). | CONFIRMÉE (domaine : b > 0, r ≥ 1) | AJOUT | 1 |
| `Real.one_add_le_three_mul_one_add_of_le_two_mul_max` | Si r ≤ 2·max(x,1), alors 1 + r ≤ 3(1+x). | CONFIRMÉE (domaine : x ≥ 0, r ≤ 2·max(x,1)) | AJOUT | 1 |
| `Real.exp_mul_rpow_le_exp_mul_rpow_of_le_mul` | Si x ≤ B·y, alors exp(A·x^τ) ≤ exp(A·B^τ·y^τ). | CONFIRMÉE (domaine : A, B, x, y, τ ≥ 0 et x ≤ B·y) | AJOUT | 1 |
| `Real.exists_between_self_and_floor_add_one_same_floor` | Pour ρ ≥ 0, il existe τ > ρ, τ < ⌊ρ⌋+1, de même plancher que ρ. | CONFIRMÉE (ρ ≥ 0) | AJOUT | 3 |
| `Real.log_norm_le_of_log_one_add_growth_on_sphere` | Sur la sphère de rayon /R/, log‖f z‖ ≤ C(1+/R/)^ρ. | CONFIRMÉE (domaine : croissance log(1+‖f‖) ≤ C(1+‖z‖)^ρ, z sur la sphère de rayon /R/) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.SpecialFunctions.Log.PosLog`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Real.log_one_add_exp_le_add_log_two` | Pour x ≥ 0, log(1+exp x) ≤ x + log 2. | CONFIRMÉE (x ≥ 0) | AJOUT | 1 |
| `Real.log_one_add_le_add_log_two_of_le_exp` | Si y ≤ exp x avec x, y ≥ 0, log(1+y) ≤ x + log 2. | CONFIRMÉE (domaine : y ≥ 0, x ≥ 0, y ≤ exp x) | AJOUT | 2 |
| `Real.le_exp_of_log_one_add_le` | Si y ≥ 0 et log(1+y) ≤ x, alors y ≤ exp x. | CONFIRMÉE (domaine : y ≥ 0, log(1+y) ≤ x) | AJOUT | 1 |
| `Real.neg_posLog_inv_le_log` | −log⁺(x⁻¹) ≤ log x pour tout réel x. | CONFIRMÉE | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.SpecialFunctions.Pow.Deriv`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.continuousOn_ofReal_cpow` | u ↦ u^r (u réel dans ℂ) est continue sur [a,b] pour a > 0. | CONFIRMÉE (a > 0) | AJOUT | 3 |
| `Complex.deriv_ofReal_cpow_neg` | La dérivée de t ↦ t^(−s) en x > 0 vaut −s·x^(−s−1). | CONFIRMÉE (x > 0) | AJOUT | 2 |
| `Complex.continuousOn_deriv_ofReal_cpow_neg` | La dérivée de t ↦ t^(−s) est continue sur [a,b] pour a > 0. | CONFIRMÉE (a > 0) | AJOUT | 1 |
| `Complex.ofReal_cpow_mul_cpow_neg_sub_one` | Pour u > 0, u·u^(−s−1) = u^(−s). | CONFIRMÉE (u > 0) | AJOUT | 1 |
| `Complex.natCast_mul_cpow_neg_eq_cpow_one_sub` | Pour N entier non nul, N·N^(−s) = N^(1−s). | CONFIRMÉE (N non nul) | AJOUT | 1 |
| `Complex.HasDerivAt.const_mul_ofReal_cpow_neg_sub_one` | La dérivée en z de w ↦ a·u^(−w−1) vaut −a·log u·u^(−z−1). | CONFIRMÉE (u > 0) | AJOUT | 1 |

### `RhGapCriterion.P4Port.Analysis.SpecialFunctions.Pow.Real`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Real.log_mul_rpow_neg_le_two_div_mul_rpow_neg` | Pour u > 1, log u·u^(−1−ε) ≤ (2/ε)·u^(−1−ε/2). | CONFIRMÉE (domaine : ε > 0, u > 1) | AJOUT | 1 |
| `Complex.one_le_one_add_norm_rpow` | Pour p ≥ 0, 1 ≤ (1+‖z‖)^p. | CONFIRMÉE (p ≥ 0) | AJOUT | 1 |

### `RhGapCriterion.P4Port.IEANTN.HadamardLogDerivative`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Kadiri.hadamardGenusOneFactor_pair_cancellation` | Pour α non nul, le produit des facteurs de genre un en w/α et w/(-α) vaut 1 - w²/α². | CONFIRMÉE (domaine : α ≠ 0) | AJOUT | 1 |
| `Kadiri.centeredHadamardOrbitBlock_base` | Le bloc quadratique centré d'orbite de Hadamard vaut 1 au point de base w₀. | CONFIRMÉE (domaine : α² - w₀² ≠ 0) | AJOUT | 0 |
| `Kadiri.centeredHadamardOrbitBlock_zero_pos` | Le bloc centré d'orbite s'annule en w = α. | CONFIRMÉE | AJOUT | 0 |
| `Kadiri.centeredHadamardOrbitBlock_zero_neg` | Le bloc centré d'orbite s'annule en w = -α. | CONFIRMÉE | AJOUT | 0 |
| `Kadiri.centeredHadamardOrbitBlock_ne_zero` | Le bloc centré d'orbite est non nul hors de w² = α². | CONFIRMÉE (domaine : α² ≠ w₀² et w² ≠ α²) | AJOUT | 1 |
| `Kadiri.normalized_hadamardGenusOneFactor_pair_cancellation` | Le produit apparié des facteurs de genre un, normalisé par sa valeur en w₀, égale le bloc quadratique centré d'orbite. | CONFIRMÉE (domaine : α ≠ 0 et α² ≠ w₀²) | AJOUT | 0 |
| `Kadiri.logDeriv_centeredHadamardOrbitBlock` | La dérivée logarithmique du bloc centré d'orbite en w vaut 2w/(w² - α²). | CONFIRMÉE (domaine : α² ≠ w₀² et w² ≠ α²) | AJOUT | 1 |
| `Kadiri.logDeriv_finiteCenteredHadamardOrbitProduct` | La dérivée logarithmique d'un produit fini de blocs centrés égale la somme finie des dérivées logarithmiques. | CONFIRMÉE (domaine : non-annulation de α² - w₀² et w² - α² pour chaque α de la famille) | AJOUT | 0 |
| `Kadiri.logDeriv_zetaPoleFactor` | La dérivée logarithmique du facteur de pôle de zêta vaut 1/(s-1). | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.logDeriv_zetaPiFactor` | La dérivée logarithmique du facteur π^(-s/2) vaut -(1/2)·log π. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.logDeriv_zetaGammaFactor` | La dérivée logarithmique du facteur gamma de zêta vaut (1/2)·digamma(s/2+1). | CONFIRMÉE (domaine : s/2+1 n'est pas un entier négatif ou nul) | AJOUT | 1 |
| `Kadiri.logDeriv_completedZetaFactor` | La dérivée logarithmique du facteur complété de zêta vaut 1/(s-1) - (1/2)log π + (1/2)digamma(s/2+1) + ζ'/ζ. | CONFIRMÉE (domaine : s ≠ 1, pôles de gamma évités, facteur gamma non nul, ζ(s) ≠ 0) | AJOUT | 1 |
| `Kadiri.neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv` | -ζ'/ζ(s) s'exprime par la dérivée logarithmique du facteur complété plus les termes de pôle, de π et de digamma. | CONFIRMÉE (domaine : s ≠ 1, pôles de gamma évités, facteur gamma non nul, ζ(s) ≠ 0) | AJOUT | 3 |
| `Kadiri.neg_zeta_logDeriv_eq_of_completed_hadamard_logDeriv` | Si la dérivée logarithmique du facteur complété vaut B + Z, alors -ζ'/ζ(s) = -B - Z + 1/(s-1) - (1/2)log π + (1/2)digamma(s/2+1). | CONFIRMÉE SOUS CONDITION (formule de Hadamard B+Z fournie en hypothèse, s ≠ 1, gamma non nul, ζ(s) ≠ 0) | AJOUT | 2 |
| `Kadiri.neg_zeta_logDeriv_eq_of_genusOne_hadamard` | Sous une formule de Hadamard de genre un B + somme sur une famille de zéros donnée, -ζ'/ζ prend l'expression explicite classique avec cette somme. | CONFIRMÉE SOUS CONDITION (formule de Hadamard de genre un supposée pour le facteur complété, s ≠ 1, gamma non nul, ζ(s) ≠ 0) | AJOUT | 0 |
| `Kadiri.neg_zeta_logDeriv_eq_of_centered_orbit_hadamard` | Sous une formule de Hadamard par orbites centrées supposée, -ζ'/ζ prend l'expression explicite classique avec la somme sur les orbites. | CONFIRMÉE SOUS CONDITION (formule de Hadamard par orbites centrées supposée, s ≠ 1, gamma non nul, ζ(s) ≠ 0) | AJOUT | 0 |
| `_private.RhGapCriterion.P4Port.IEANTN.HadamardLogDerivative.0.Kadiri.zetaPiFactor_eq_cpow` | Le facteur π de zêta égale π^(-s/2) en puissance complexe. | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.IEANTN.HadamardLogDerivative.0.Kadiri.completedZetaFactor_eq_mul_completedRiemannZeta` | Le facteur complété égale s(s-1)/2 fois la fonction zêta complétée de Mathlib. | CONFIRMÉE (domaine : s ≠ 0 et Γ(s/2) ≠ 0) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.IEANTN.HadamardLogDerivative.0.Kadiri.gamma_half_avoid_neg_nat_of_shift` | Si s/2+1 n'est pas un entier négatif ou nul, alors s/2 non plus. | CONFIRMÉE (domaine : s ≠ 0 et s/2+1 hors des pôles) | AJOUT | 3 |
| `_private.RhGapCriterion.P4Port.IEANTN.HadamardLogDerivative.0.Kadiri.gamma_half_ne_zero_of_shift` | Γ(s/2) est non nul dès que s/2+1 évite les pôles. | CONFIRMÉE (domaine : s ≠ 0 et s/2+1 hors des pôles) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.IEANTN.HadamardLogDerivative.0.Kadiri.completedZetaFactor_one_sub` | Le facteur complété est invariant par s ↦ 1-s (équation fonctionnelle). | CONFIRMÉE (domaine : s ≠ 0, s ≠ 1, Γ(s/2) et Γ((1-s)/2) non nuls) | V62 | 1 |
| `_private.RhGapCriterion.P4Port.IEANTN.HadamardLogDerivative.0.Kadiri.differentiableAt_completedZetaFactor` | Le facteur complété est dérivable en tout s ≠ 1 hors des pôles de gamma. | CONFIRMÉE (domaine : s ≠ 1 et pôles de gamma évités) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.IEANTN.HadamardLogDerivative.0.Kadiri.logDeriv_completedZetaFactor_one_sub` | La dérivée logarithmique du facteur complété est antisymétrique sous s ↦ 1-s. | CONFIRMÉE (domaine : s ≠ 0, s ≠ 1, pôles de gamma évités en s et 1-s) | V62 | 1 |
| `_private.RhGapCriterion.P4Port.IEANTN.HadamardLogDerivative.0.Kadiri.neg_logDeriv_zeta_left_eq_reflected` | -ζ'/ζ en z égale ζ'/ζ en 1-z plus des termes de pôle, de log π et de digamma (équation fonctionnelle pour la dérivée logarithmique). | CONFIRMÉE (domaine : z ∉ {0,1}, ζ(z) et ζ(1-z) non nuls, pôles de gamma évités, facteurs gamma non nuls) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.IEANTN.HadamardLogDerivative.0.Kadiri.zetaGammaFactor_shift_avoid_of_not_zero` | Si s n'est pas un zéro de zêta au sens de l'ensemble riemannZeta.zeroes, s/2+1 n'est jamais un entier négatif ou nul. | CONFIRMÉE (domaine : s hors de l'ensemble des zéros de zêta) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.IEANTN.HadamardLogDerivative.0.Kadiri.functional_eq_correct_sign` | Équation fonctionnelle de -ζ'/ζ avec signe corrigé : -ζ'/ζ(s) = -log π + ζ'/ζ(1-s) + (1/2)(digamma(s/2)+digamma((1-s)/2)). | CONFIRMÉE (domaine : s ∉ {0,1}, ζ(s) et ζ(1-s) non nuls, pôles de gamma évités) | AJOUT | 1 |
| `Kadiri.kadiri_thm_3_1_q1_functional_eq` | Équation fonctionnelle de -ζ'/ζ, cas q=1 du théorème 3.1 de Kadiri : même identité que la précédente sans les hypothèses de pôles de gamma. | CONFIRMÉE (domaine : s ∉ {0,1}, ζ(s) ≠ 0, ζ(1-s) ≠ 0) | AJOUT | 1 |

### `RhGapCriterion.P4Port.IEANTN.KadiriZeroCounting`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Kadiri.riemannZetaConjZeroSource_of_riemannZeta_conj` | Si ζ(z)=0 alors ζ(conj z)=0 : les zéros de zêta sont stables par conjugaison. | CONFIRMÉE | V63,V64 | 1 |
| `Kadiri.nontrivialZero_ne_one` | Tout zéro non trivial est différent de 1. | CONFIRMÉE | AJOUT | 6 |
| `Kadiri.riemannZeta_analyticAt_nontrivialZero` | Zêta est analytique en tout zéro non trivial. | CONFIRMÉE | AJOUT | 3 |
| `Kadiri.riemannZeta_nontrivialZero_zero` | Zêta s'annule en tout zéro non trivial (par définition du sous-type). | CONFIRMÉE | AJOUT | 3 |
| `Kadiri.riemannZeta_eventually_ne_zero_punctured_nontrivialZero` | Zêta est non nulle sur un voisinage épointé de tout zéro non trivial (isolement des zéros). | CONFIRMÉE | AJOUT | 0 |
| `Kadiri.riemannZeta_meromorphicOrderAt_ne_top_nontrivialZero` | L'ordre méromorphe de zêta en un zéro non trivial est fini. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.riemannZeta_order_pos_nontrivialZero` | L'ordre (multiplicité) de zêta en un zéro non trivial est strictement positif. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.riemannZeta_one_le_order_nontrivialZero` | L'ordre de zêta en un zéro non trivial est au moins 1. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.zeroes_rect_Ioo_critical_positive_height_finite` | L'ensemble des zéros de zêta de partie réelle dans ]0,1[ et de partie imaginaire dans ]0,T[ est fini. | CONFIRMÉE | AJOUT | 5 |
| `Kadiri.zeroes_rect_positive_height_card_le_zeroes_sum_order` | Le nombre de zéros dans la bande ]0,1[ x ]0,T[ est majoré par la somme de leurs multiplicités (poids 1). | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.positive_height_nontrivial_zero_count_le_NPrime` | Le nombre de zéros non triviaux de hauteur dans ]0,T[ est majoré par N'(0,T). | CONFIRMÉE | AJOUT | 2 |
| `Kadiri.positiveHeightZero_ne_one` | Un zéro de zêta de hauteur strictement positive est différent de 1. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.riemannZeta_analyticAt_positiveHeightZero` | Zêta est analytique en tout zéro de hauteur dans ]0,T[. | CONFIRMÉE | AJOUT | 3 |
| `Kadiri.riemannZeta_positiveHeightZero_zero` | Zêta s'annule en tout élément de l'ensemble des zéros de hauteur dans ]0,T[. | CONFIRMÉE | AJOUT | 3 |
| `Kadiri.riemannZeta_eventually_ne_zero_punctured_positiveHeightZero` | Zêta est non nulle sur un voisinage épointé de tout zéro de hauteur positive. | CONFIRMÉE | AJOUT | 0 |
| `Kadiri.riemannZeta_meromorphicOrderAt_ne_top_positiveHeightZero` | L'ordre méromorphe de zêta en un zéro de hauteur positive est fini. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.riemannZeta_order_pos_positiveHeightZero` | L'ordre de zêta en un zéro de hauteur positive est strictement positif. | CONFIRMÉE | AJOUT | 3 |
| `Kadiri.riemannZeta_one_le_order_positiveHeightZero` | L'ordre de zêta en un zéro de hauteur positive est au moins 1. | CONFIRMÉE | AJOUT | 0 |
| `Kadiri.riemannZeta_one_sub_ne_zero_of_one_le_re` | Si Re w ≥ 1 et cos(πw/2) ≠ 0, alors ζ(1-w) ≠ 0. | CONFIRMÉE (domaine : cos(πw/2) ≠ 0) | AJOUT | 3 |
| `Kadiri.riemannZeta_ne_zero_of_real_neg` | Zêta est non nulle sur le segment réel ]-1,0]. | CONFIRMÉE (domaine : σ dans ]-1,0]) | AJOUT | 2 |
| `Kadiri.riemannZeta_ne_zero_of_re_nonpos_im_ne_zero` | Zêta est non nulle en tout point de partie réelle négative ou nulle et de partie imaginaire non nulle. | CONFIRMÉE (domaine : Re z ≤ 0 et Im z ≠ 0) | V7 | 2 |
| `Kadiri.positiveHeightZero_re_mem_Ioo` | Tout zéro de zêta de hauteur strictement positive a sa partie réelle strictement entre 0 et 1. | CONFIRMÉE | V7 | 1 |
| `Kadiri.zeroes_rect_univ_positive_height_finite` | Il n'y a qu'un nombre fini de zéros de zêta de hauteur dans ]0,T[. | CONFIRMÉE | AJOUT | 2 |
| `Kadiri.zeroImagDyadicNOrderSummableSource_of_positive_height_zero_free` | Pour chaque k, la série des ordres des zéros de hauteur dans ]0,2^(k+1)[ est sommable (la Source Prop dépliée). | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.zeroes_rect_Ioo_critical_zero_height_finite` | L'ensemble des zéros dans la bande ]0,1[ de hauteur exactement 0 est fini. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.zeroHeightNontrivialZeros_finite` | L'ensemble des zéros non triviaux de hauteur nulle est fini (en fait vide en pratique, mais seule la finitude est établie). | CONFIRMÉE | AJOUT | 2 |
| `Kadiri.dyadicShellToCumulative_injective` | L'inclusion de la coquille dyadique k dans l'ensemble cumulé de même bord supérieur est injective. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.nontrivialZero_ne_zero` | Un zéro non trivial est différent de 0. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.nontrivialZeros_norm_lt_finite` | Il n'y a qu'un nombre fini de zéros non triviaux de module inférieur à R. | CONFIRMÉE | AJOUT | 5 |
| `Kadiri.nontrivialZeros_abs_im_lt_one_finite` | Il n'y a qu'un nombre fini de zéros non triviaux de ∣Im∣ < 1. | CONFIRMÉE | AJOUT | 3 |
| `Kadiri.nontrivialZeros_abs_im_lt_finite` | Il n'y a qu'un nombre fini de zéros non triviaux de ∣Im∣ < T. | CONFIRMÉE | AJOUT | 5 |
| `Kadiri.nontrivialZeros_dyadic_shell_finite` | Chaque coquille dyadique de hauteur contient un nombre fini de zéros non triviaux. | CONFIRMÉE | AJOUT | 5 |
| `Kadiri.nontrivialZeros_shifted_abs_im_lt_one_finite` | Pour tout s, il n'y a qu'un nombre fini de zéros non triviaux avec ∣Im(s-ρ)∣ < 1. | CONFIRMÉE | AJOUT | 0 |
| `Kadiri.highZeroToDyadicShell_injective` | L'assignation d'un zéro de hauteur au moins 1 à sa coquille dyadique est injective. | CONFIRMÉE | AJOUT | 2 |
| `Kadiri.sub_nontrivialZero_ne_zero` | Si Re s > 1, alors s - ρ est non nul pour tout zéro non trivial ρ. | CONFIRMÉE (domaine : Re s > 1) | AJOUT | 0 |
| `Kadiri.zeroSquareTail_shift_le_four_zero` | Pour 2‖s‖ ≤ ‖ρ‖, la queue carrée décalée en s est majorée par 4 fois la queue non décalée. | CONFIRMÉE (domaine : 2‖s‖ ≤ ‖ρ‖) | AJOUT | 1 |
| `Kadiri.zeroSquareTailSummable_shift_of_zero` | La sommabilité de la queue carrée non décalée sur les zéros implique celle de la queue décalée en tout s. | CONFIRMÉE (domaine : queue carrée non décalée sommable) | AJOUT | 0 |
| `Kadiri.zeroSquareTail_le_imagSquareTail_of_large_im` | Pour ∣Im ρ∣ ≥ 1, la queue en norme carrée en 0 est majorée par la queue en hauteur carrée. | CONFIRMÉE (domaine : ∣Im ρ∣ ≥ 1) | AJOUT | 1 |
| `Kadiri.zeroSquareTailSummable_of_imag_tail` | La sommabilité de la queue en hauteur carrée sur les zéros implique celle de la queue en norme carrée en 0. | CONFIRMÉE (domaine : queue en hauteur carrée sommable) | AJOUT | 0 |
| `Kadiri.zeroHeightDyadicShellMass_nonneg` | La masse (somme des 1/Im²) d'une coquille dyadique est positive ou nulle. | CONFIRMÉE | AJOUT | 2 |
| `Kadiri.zeroImagSquareTail_le_dyadic_inv_sq` | Dans la coquille dyadique k, chaque terme 1/Im² est majoré par (2^k)^(-2). | CONFIRMÉE (domaine : ρ appartient à la coquille k) | AJOUT | 2 |
| `Kadiri.zeroHeightDyadicShellMass_le_count_inv_sq` | La masse d'une coquille dyadique est majorée par son cardinal fois (2^k)^(-2). | CONFIRMÉE | AJOUT | 2 |
| `Kadiri.zeroHeightDyadicShellCount_le_cumulative_count` | Le cardinal d'une coquille dyadique est majoré par le nombre de zéros de ∣Im∣ < 2^(k+1). | CONFIRMÉE | AJOUT | 2 |
| `Kadiri.zetaCounting_abs_N_le_backlund_majorant` | Toute estimation de Riemann-von Mangoldt de constantes b₁,b₂,b₃ donne ∣N(T)∣ ≤ majorant de Backlund pour T ≥ 2. | CONFIRMÉE SOUS CONDITION (estimation RvM (b₁,b₂,b₃) supposée et T ≥ 2) | AJOUT | 2 |
| `Kadiri.zetaCountingDyadic_abs_N_le_backlund_majorant` | Sous l'estimation RvM aux constantes de Backlund (0,137 ; 0,443 ; 6,1), ∣N(2^(k+1))∣ est majoré par le majorant dyadique explicite. | CONFIRMÉE SOUS CONDITION (estimation RvM de Backlund supposée) | AJOUT | 2 |
| `Kadiri.dyadicCountScale_ge_one` | Pour tout k, (k+1)·2^k ≥ 1. | CONFIRMÉE | AJOUT | 2 |
| `Kadiri.log_dyadic_le_count_scale` | Pour tout k, log(2^(k+1)) ≤ (k+1)·2^k. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.log_dyadic_le_nat_succ` | Pour tout k, log(2^(k+1)) ≤ k+1. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.dyadic_div_two_pi_abs_eq` | Identité ∣2^(k+1)/(2π)∣ = 2·∣(2π)^(-1)∣·2^k. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.abs_log_dyadic_div_two_pi_le` | ∣log(2^(k+1)/(2π))∣ ≤ (1+∣log 2π∣)(k+1). | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.abs_zetaCountingMainTerm_core_le` | ∣A log A - A + 7/8∣ ≤ ∣A log A∣ + ∣A∣ + 1 (inégalité triangulaire sur le terme principal RvM). | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.zetaCountingMainTermDyadicGrowthSource_of_elementary` | Le terme principal RvM à hauteur dyadique 2^(k+1) est majoré par C(k+1)2^k pour une constante C ≥ 0. | CONFIRMÉE | AJOUT | 4 |
| `Kadiri.zetaCountingRvM_dyadic_le` | Le terme d'erreur RvM de constantes de Backlund à hauteur 2^(k+1) est majoré par 7(k+1)2^k. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.zetaCountingDyadicMajorantGrowthSource_of_main_term_growth` | Si le terme principal RvM a une croissance dyadique en C(k+1)2^k, le majorant de Backlund complet a la même croissance. | CONFIRMÉE SOUS CONDITION (croissance dyadique du terme principal supposée) | AJOUT | 4 |
| `Kadiri.summable_rpow_three_halves_shift` | La série des C/(n+3)^(3/2) est sommable pour tout réel C. | CONFIRMÉE | AJOUT | 0 |
| `Kadiri.summable_linear_geometric_inv_two` | La série des C(k+1)2^(-k) est sommable pour tout réel C. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.zeroImagDyadicShellSummableSource_of_mass_bound` | Une borne géométrique de la masse des coquilles dyadiques implique la sommabilité de la masse 1/Im² par coquilles. | CONFIRMÉE SOUS CONDITION (borne de masse dyadique supposée) | AJOUT | 1 |
| `Kadiri.zeroImagDyadicShellCountBoundSource_of_cumulative_count_bound` | Une borne cumulative C(k+1)2^k sur le nombre de zéros de ∣Im∣<2^(k+1) donne la même borne pour chaque coquille. | CONFIRMÉE SOUS CONDITION (borne cumulative supposée) | AJOUT | 3 |
| `Kadiri.zeroImagDyadicCumulativeCountByNSource_of_positive_bridge` | Le comptage cumulé par N(T) découle de deux ponts : réduction des hauteurs absolues aux hauteurs positives et comparaison de N'(0,T) à N(T). | CONFIRMÉE SOUS CONDITION (deux ponts de comptage supposés) | AJOUT | 0 |
| `Kadiri.zeroImagDyadicCumulativeCountByNWithZeroHeightSource_of_positive_bridge` | Idem avec seau additif de hauteur nulle : deux ponts (avec seau) donnent le comptage cumulé par N(T) plus constante. | CONFIRMÉE SOUS CONDITION (deux ponts de comptage supposés) | AJOUT | 1 |
| `Kadiri.zeroImagDyadicAbsToPositiveCountWithZeroHeightSource_of_conj` | La stabilité par conjugaison réduit le comptage en hauteur absolue à deux seaux de hauteur positive plus le seau de hauteur nulle. | CONFIRMÉE SOUS CONDITION (stabilité par conjugaison des zéros supposée) | V63,V64 | 1 |
| `Kadiri.zeroImagDyadicAbsToPositiveCountWithZeroHeightSource_of_riemannZeta_conj` | Le comptage des zéros non triviaux de ∣Im∣<2^(k+1) est majoré par A fois le comptage de hauteur positive plus une constante D (réduction par conjugaison). | CONFIRMÉE | V64 | 1 |
| `Kadiri.zeroImagDyadicNPrimeToNSource_of_order_summable` | La comparaison de N'(0,T) à N(T) sur les hauteurs dyadiques découle de la sommabilité des ordres. | CONFIRMÉE SOUS CONDITION (sommabilité des ordres supposée) | AJOUT | 1 |
| `Kadiri.zeroImagDyadicCumulativeCountByNWithZeroHeightSource_of_conj_and_order_summable` | Conjugaison et sommabilité des ordres donnent le comptage cumulé par N(T) avec seau additif de hauteur nulle. | CONFIRMÉE SOUS CONDITION (sommabilité des ordres supposée) | V63,V64 | 1 |
| `Kadiri.zeroImagDyadicCumulativeCountByNWithZeroHeightSource_of_conj_and_positive_height_zero_free` | Le comptage cumulé des zéros non triviaux de ∣Im∣<2^(k+1) est majoré par A∣N(2^(k+1))∣ + D (Source dépliée, établie sans hypothèse). | CONFIRMÉE | AJOUT | 2 |
| `Kadiri.zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_and_backlund_growth` | Sous RvM de Backlund, comptage par N(T) et croissance dyadique du majorant de Backlund, le nombre de zéros de ∣Im∣<2^(k+1) est ≤ C(k+1)2^k. | CONFIRMÉE SOUS CONDITION (estimation RvM de Backlund, comptage par N(T) et croissance du majorant supposés) | AJOUT | 2 |
| `Kadiri.zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_with_zero_height_and_backlund_growth` | Même conclusion, avec le comptage par N(T) à seau additif de hauteur nulle. | CONFIRMÉE SOUS CONDITION (estimation RvM de Backlund, comptage par N(T) avec seau et croissance du majorant supposés) | AJOUT | 2 |
| `Kadiri.zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_and_main_term_growth` | Même conclusion à partir de la croissance dyadique du terme principal RvM au lieu du majorant complet. | CONFIRMÉE SOUS CONDITION (estimation RvM de Backlund, comptage par N(T) et croissance du terme principal supposés) | AJOUT | 1 |
| `Kadiri.zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_with_zero_height_and_main_term_growth` | Même conclusion, comptage par N(T) avec seau additif et croissance du terme principal. | CONFIRMÉE SOUS CONDITION (estimation RvM de Backlund, comptage avec seau et croissance du terme principal supposés) | AJOUT | 1 |
| `Kadiri.zeroImagDyadicCumulativeCountBoundSource_of_count_by_N` | Sous RvM de Backlund, le comptage par N(T) donne la borne cumulative C(k+1)2^k sur le nombre de zéros. | CONFIRMÉE SOUS CONDITION (estimation RvM de Backlund et comptage par N(T) supposés) | AJOUT | 0 |
| `Kadiri.zeroImagDyadicCumulativeCountBoundSource_of_count_by_N_with_zero_height` | Idem avec seau additif de hauteur nulle. | CONFIRMÉE SOUS CONDITION (estimation RvM de Backlund et comptage avec seau supposés) | AJOUT | 0 |
| `Kadiri.zeroImagDyadicShellMassBoundSource_of_count_bound` | Une borne C(k+1)2^k sur le nombre de zéros par coquille donne une borne géométrique de la masse dyadique. | CONFIRMÉE SOUS CONDITION (borne de comptage par coquille supposée) | AJOUT | 2 |
| `Kadiri.zeroImagDyadicShellMassBoundSource_of_cumulative_count_bound` | Une borne cumulative de comptage donne la borne géométrique de la masse dyadique. | CONFIRMÉE SOUS CONDITION (borne cumulative de comptage supposée) | AJOUT | 0 |
| `Kadiri.zeroImagDyadicShellSummableSource_of_count_bound` | Une borne de comptage par coquille donne la sommabilité de la hauteur carrée par coquilles. | CONFIRMÉE SOUS CONDITION (borne de comptage par coquille supposée) | AJOUT | 2 |
| `Kadiri.zeroImagDyadicShellSummableSource_of_cumulative_count_bound` | Une borne cumulative de comptage donne la sommabilité de la hauteur carrée par coquilles. | CONFIRMÉE SOUS CONDITION (borne cumulative de comptage supposée) | AJOUT | 0 |
| `Kadiri.zeroImagSquareTailSummable_of_dyadic_shell_source` | La sommabilité par coquilles dyadiques donne celle de la série des 1/Im² sur les zéros non triviaux. | CONFIRMÉE SOUS CONDITION (sommabilité par coquilles supposée) | AJOUT | 2 |
| `Kadiri.zeroImagSquareTailSummable_of_dyadic_count_bound` | Une borne de comptage par coquille dyadique donne la sommabilité de la série des 1/Im² sur les zéros non triviaux. | CONFIRMÉE SOUS CONDITION (borne de comptage par coquille supposée) | AJOUT | 1 |
| `Kadiri.zeroImagSquareTailSummable_of_cumulative_dyadic_count_bound` | Une borne de comptage cumulative dyadique donne la sommabilité de la série des 1/Im². | CONFIRMÉE SOUS CONDITION (borne cumulative de comptage supposée) | AJOUT | 2 |
| `Kadiri.zeroImagSquareTailSummable_of_count_by_N_and_backlund_growth` | Sous RvM de Backlund, comptage par N(T) et croissance du majorant, la série des 1/Im² sur les zéros non triviaux est sommable. | CONFIRMÉE SOUS CONDITION (RvM de Backlund, comptage par N(T) et croissance du majorant supposés) | AJOUT | 1 |
| `Kadiri.zeroImagSquareTailSummable_of_count_by_N_and_main_term_growth` | Même sommabilité à partir du comptage par N(T) et de la croissance du terme principal. | CONFIRMÉE SOUS CONDITION (RvM de Backlund, comptage par N(T) et croissance du terme principal supposés) | AJOUT | 1 |
| `Kadiri.zeroImagSquareTailSummable_of_count_by_N` | Sous RvM de Backlund et comptage par N(T), la série des 1/Im² est sommable. | CONFIRMÉE SOUS CONDITION (RvM de Backlund et comptage par N(T) supposés) | AJOUT | 0 |
| `Kadiri.zeroImagSquareTailSummable_of_count_by_N_with_zero_height_and_backlund_growth` | Même sommabilité, comptage avec seau de hauteur nulle et croissance du majorant de Backlund. | CONFIRMÉE SOUS CONDITION (RvM de Backlund, comptage avec seau et croissance du majorant supposés) | AJOUT | 1 |
| `Kadiri.zeroImagSquareTailSummable_of_count_by_N_with_zero_height_and_main_term_growth` | Même sommabilité, comptage avec seau de hauteur nulle et croissance du terme principal. | CONFIRMÉE SOUS CONDITION (RvM de Backlund, comptage avec seau et croissance du terme principal supposés) | AJOUT | 1 |
| `Kadiri.zeroImagSquareTailSummable_of_count_by_N_with_zero_height` | Sous RvM de Backlund et comptage par N(T) avec seau additif, la série des 1/Im² est sommable. | CONFIRMÉE SOUS CONDITION (RvM de Backlund et comptage avec seau supposés) | AJOUT | 1 |
| `Kadiri.zeroImagSquareTail_shifted_le_four` | Pour 2∣Im s∣+2 ≤ ∣Im ρ∣, le terme 1/∣Im(s-ρ)∣² est majoré par 4 fois 1/∣Im ρ∣². | CONFIRMÉE (domaine : 2∣Im s∣+2 ≤ ∣Im ρ∣) | AJOUT | 2 |
| `Kadiri.summable_zeroImagSquareTail_shifted` | Si la série des 1/Im² est sommable, alors la série décalée 1/∣Im(s-ρ)∣² l'est pour tout s. | CONFIRMÉE SOUS CONDITION (sommabilité de la série non décalée supposée) | AJOUT | 2 |
| `Kadiri.zeroImagSquareTailSummable_of_RvM` | Sous l'estimation RvM de Backlund, la série des 1/Im² sur les zéros non triviaux est sommable. | CONFIRMÉE SOUS CONDITION (estimation RvM de Backlund supposée) | AJOUT | 1 |
| `Kadiri.summable_zeroImagSquareTail_shifted_of_RvM` | Sous l'estimation RvM de Backlund, la série décalée 1/∣Im(s-ρ)∣² est sommable pour tout s. | CONFIRMÉE SOUS CONDITION (estimation RvM de Backlund supposée) | AJOUT | 0 |
| `Kadiri.zeroImagSquareTailSummable_of_cumulative_count_le` | Si g(k)·4^(-k) est sommable et le nombre de zéros de ∣Im∣<2^(k+1) est ≤ g(k), la série des 1/Im² est sommable. | CONFIRMÉE SOUS CONDITION (majorant g sommable pondéré et borne de comptage supposés) | AJOUT | 1 |
| `Kadiri.zetaCountingDyadic_abs_N_le_geometric` | Il existe E>0 avec ∣N(2^(k+1))∣ ≤ E·3^k pour tout k (majorant grossier géométrique). | CONFIRMÉE | AJOUT | 2 |
| `Kadiri.zeroImagSquareTailSummable_of_crude_majorant` | La série des 1/Im² sur les zéros non triviaux est sommable, sans hypothèse (majorant grossier). | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.summable_zeroImagSquareTail_shifted_unconditional` | Pour tout s, la série décalée des 1/∣Im(s-ρ)∣² sur les zéros non triviaux est sommable, sans hypothèse. | CONFIRMÉE | AJOUT | 0 |
| `_private.RhGapCriterion.P4Port.IEANTN.KadiriZeroCounting.0.Kadiri.hasDerivAt_conj_conj` | Si f a la dérivée f' en conj z₀, la fonction w ↦ conj(f(conj w)) a la dérivée conj f' en z₀. | CONFIRMÉE (domaine : f dérivable en conj z₀) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.IEANTN.KadiriZeroCounting.0.Kadiri.analyticAt_conj_conj` | Si f est analytique en conj z₀, alors w ↦ conj(f(conj w)) est analytique en z₀. | CONFIRMÉE (domaine : f analytique en conj z₀) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.IEANTN.KadiriZeroCounting.0.Kadiri.analyticOrderAt_conj_conj` | L'ordre analytique de w ↦ conj(f(conj w)) en z₀ égale celui de f en conj z₀. | CONFIRMÉE (domaine : f analytique en conj z₀) | AJOUT | 0 |
| `Kadiri.riemannZeta_order_conj` | En un zéro ρ de zêta, l'ordre en conj ρ égale l'ordre en ρ. | CONFIRMÉE (domaine : ρ zéro de zêta) | V63 | 1 |
| `Kadiri.riemannZeta_order_nonneg` | Pour ρ ≠ 1, l'ordre de zêta en ρ est positif ou nul. | CONFIRMÉE (domaine : ρ ≠ 1) | AJOUT | 5 |
| `_private.RhGapCriterion.P4Port.IEANTN.KadiriZeroCounting.0.Kadiri.riemannZeta_N_eq_tsum_order` | N(T) égale la somme des ordres sur les zéros de hauteur dans ]0,T[. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.weightedZeroHeightBucket_nonneg` | Le seau pondéré des zéros non triviaux de hauteur nulle est positif ou nul. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.weighted_cumulative_count_le` | La somme pondérée par l'ordre sur les zéros de ∣Im∣<2^(k+1) est majorée par 2∣N(2^(k+1))∣ plus le seau de hauteur nulle. | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.IEANTN.KadiriZeroCounting.0.Kadiri.weighted_shell_mass_le` | La masse pondérée d'une coquille dyadique est majorée par (2∣N(2^(k+1))∣ + seau)·(2^k)^(-2). | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.IEANTN.KadiriZeroCounting.0.Kadiri.weighted_shell_sigma_summable` | La somme sur les coquilles dyadiques des ordres pondérés par 1/Im² est sommable, sans hypothèse. | CONFIRMÉE | AJOUT | 1 |
| `Kadiri.weighted_zeroImagSquareTail_summable` | La série des ordres pondérés par 1/Im² sur les zéros non triviaux est sommable, sans hypothèse. | CONFIRMÉE | AJOUT | 2 |
| `Kadiri.weighted_zeroImagSquareTail_shifted_summable` | Pour tout s, la série des ordres pondérés par 1/∣Im(s-ρ)∣² est sommable, sans hypothèse. | CONFIRMÉE | AJOUT | 1 |

### `RhGapCriterion.P4Port.IEANTN.ZetaDefinitions`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `riemannZeta.zeroes_rect_eq` | Le rectangle de zéros zeroes_rect I J égale l'intersection de re⁻¹ I, im⁻¹ J et de l'ensemble des zéros de zêta. | CONFIRMÉE | AJOUT | 3 |
| `riemannZeta.zeroes_rect_disjoint₁` | Si I₁ et I₂ sont disjoints, les rectangles de zéros correspondants de même J sont disjoints. | CONFIRMÉE (domaine : I₁ et I₂ disjoints) | AJOUT | 0 |
| `riemannZeta.zeroes_rect_union` | L'union de deux rectangles de zéros de même J égale le rectangle sur I₁ ∪ I₂. | CONFIRMÉE | AJOUT | 0 |
| `riemannZeta_differentiableOn_compl_one` | Zêta est différentiable sur ℂ privé de 1. | CONFIRMÉE | AJOUT | 1 |
| `riemannZeta_analyticOn_compl_one` | Zêta est analytique en tout point de ℂ privé de 1. | CONFIRMÉE | AJOUT | 7 |
| `riemannZeta.zeroes_codiscreteWithin_compl_one` | Le complémentaire des zéros de zêta est codiscret dans ℂ privé de 1 (zéros isolés). | CONFIRMÉE | AJOUT | 1 |
| `riemannZeta.zeroes_on_Compact_finite` | Un compact ne contenant pas 1 ne contient qu'un nombre fini de zéros de zêta. | CONFIRMÉE (domaine : S compact et 1 ∉ S) | AJOUT | 1 |
| `riemannZeta_eventually_ne_zero` | Zêta est non nulle sur un voisinage épointé de 1. | CONFIRMÉE | AJOUT | 1 |
| `riemannZeta_no_zeroes_near_one` | Il existe une boule autour de 1 sur laquelle zêta ne s'annule pas. | CONFIRMÉE | AJOUT | 1 |
| `riemannZeta.zeroes_on_Compact_finite'` | Un compact ne contient qu'un nombre fini de zéros de zêta. | CONFIRMÉE (domaine : S compact) | AJOUT | 4 |
| `zero_density_bound.bound` | Champ d'une structure de borne de densité de zéros : pour T ≥ T₀ et σ dans la plage, N'(σ,T) ≤ c₁(σ)T^p(σ)(log T)^q(σ) + c₂(σ)(log T)². | CONFIRMÉE SOUS CONDITION (champ de structure : la borne est une donnée supposée) | AJOUT | 0 |

### `RhGapCriterion.P4Port.MeasureTheory.Integral.IntegrableOn`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `MeasureTheory.IntegrableOn.mono'` | Si ‖f‖ ≤ g p.p. sur s, g intégrable sur s et f fortement mesurable, alors f est intégrable sur s. | CONFIRMÉE (domaine : domination presque partout, g intégrable et f mesurable) | AJOUT | 2 |

### `RhGapCriterion.P4Port.MeasureTheory.Integral.IntervalIntegral.Basic`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `intervalIntegral.integral_congr_Ioc_of_le` | Deux fonctions égales sur Ioc a b ont même intégrale sur l'intervalle a..b. | CONFIRMÉE (domaine : a ≤ b et égalité sur Ioc a b) | AJOUT | 4 |

### `RhGapCriterion.P4Port.NumberTheory.AbelSummation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Finset.sum_Icc_one_eq_sum_range` | La somme de f k sur Icc 1 N égale la somme de f(n+1) sur range N. | CONFIRMÉE | AJOUT | 1 |
| `Finset.sum_Icc_zero_eq_sum_Icc_one` | Si f 0 = 0, la somme sur Icc 0 N égale la somme sur Icc 1 N. | CONFIRMÉE (domaine : f 0 = 0) | AJOUT | 1 |
| `Finset.sum_Icc_zero_eq_sum_range_succ` | Si f 0 = 0, la somme de f k sur Icc 0 m égale la somme de f(n+1) sur range m. | CONFIRMÉE (domaine : f 0 = 0) | AJOUT | 2 |
| `sum_Icc_zero_floor_eq_sum_range` | Si c 0 = 0, la somme de c k sur Icc 0 ⌊t⌋ égale la somme de c(n+1) sur range ⌊t⌋. | CONFIRMÉE (domaine : c 0 = 0) | AJOUT | 1 |

### `RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZeta`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `verticalLine_re` | La partie réelle du point σ + it de la droite verticale vaut σ. | CONFIRMÉE | AJOUT | 5 |
| `verticalLine_im` | La partie imaginaire du point σ + it vaut t. | CONFIRMÉE | AJOUT | 2 |
| `verticalLine_add_const` | s + h + t·i égale le point vertical de coordonnées (Re s + h, Im s + t). | CONFIRMÉE | AJOUT | 1 |
| `Nat.Primes.norm_cpow_neg_lt_one` | Pour un premier p et Re s > 1, ‖p^(-s)‖ < 1. | CONFIRMÉE (domaine : Re s > 1) | AJOUT | 2 |
| `Nat.Primes.norm_cpow_neg_eq_rpow_neg_re` | Pour un premier p, ‖p^(-s)‖ = p^(-Re s). | CONFIRMÉE | AJOUT | 1 |
| `Nat.Primes.cpow_neg_ofReal` | Pour un premier p et r réel, la puissance réelle p^(-r) se transporte à la puissance complexe p^(-r). | CONFIRMÉE | AJOUT | 1 |
| `Nat.Primes.cast_inv_one_add` | Pour un premier p et r réel, (1+p^(-r))⁻¹ dans ℂ égale le transfert du réel (1+p^(-r))⁻¹. | CONFIRMÉE | AJOUT | 2 |
| `Nat.Primes.norm_cast_inv_one_add` | Pour un premier p et r réel, ‖(1+p^(-r))⁻¹‖ = (1+p^(-r))⁻¹. | CONFIRMÉE | AJOUT | 1 |
| `Nat.Primes.norm_one_sub_cpow_neg_vertical_le` | Sur la droite σ + it, ‖1 - p^(-s)‖ ≤ 1 + p^(-σ). | CONFIRMÉE | AJOUT | 1 |
| `Nat.Primes.one_sub_cpow_neg_vertical_ne_zero` | Sur la droite σ + it avec σ > 1, le facteur d'Euler 1 - p^(-s) est non nul. | CONFIRMÉE (domaine : σ > 1) | AJOUT | 2 |
| `Nat.Primes.inv_one_add_rpow_le_inv_norm_one_sub_cpow_neg_vertical` | Pour σ > 1, (1+p^(-σ))⁻¹ ≤ ‖1 - p^(-(σ+it))‖⁻¹ (comparaison de facteurs d'Euler inverses). | CONFIRMÉE (domaine : σ > 1) | AJOUT | 1 |
| `Nat.Primes.multipliable_inv_one_add` | Pour r > 1, le produit sur les premiers des (1+p^(-r))⁻¹ est multipliable. | CONFIRMÉE (domaine : r > 1) | AJOUT | 2 |
| `Nat.Primes.multipliable_complex_inv_one_add` | Pour r > 1, le produit complexe des (1+p^(-r))⁻¹ est multipliable. | CONFIRMÉE (domaine : r > 1) | AJOUT | 2 |
| `Nat.Primes.inv_one_sub_sq_eq_mul_inv_one_sub_one_add` | Pour ‖z‖ < 1, (1-z²)⁻¹ = (1-z)⁻¹(1+z)⁻¹. | CONFIRMÉE (domaine : ‖z‖ < 1) | AJOUT | 1 |
| `Nat.Primes.eulerFactor_two_mul` | Pour Re s > 1, (1-p^(-2s))⁻¹ = (1-p^(-s))⁻¹(1+p^(-s))⁻¹. | CONFIRMÉE (domaine : Re s > 1) | AJOUT | 1 |
| `riemannZeta_eq_mul_tprod_inv_one_add` | Pour r réel > 1, ζ(2r) = ζ(r)·produit sur les premiers de (1+p^(-r))⁻¹. | CONFIRMÉE (domaine : r > 1) | AJOUT | 1 |
| `riemannZeta_div_riemannZeta_eq_tprod_inv_one_add` | Pour r réel > 1, ζ(2r)/ζ(r) = produit sur les premiers de (1+p^(-r))⁻¹. | CONFIRMÉE (domaine : r > 1) | AJOUT | 1 |
| `norm_riemannZeta_eulerProduct` | Pour Re s > 1, ‖ζ(s)‖ égale le produit sur les premiers des ‖1-p^(-s)‖⁻¹. | CONFIRMÉE (domaine : Re s > 1) | AJOUT | 1 |
| `norm_riemannZeta_div_riemannZeta` | Pour r réel > 1, ‖ζ(2r)/ζ(r)‖ égale le produit sur les premiers des (1+p^(-r))⁻¹. | CONFIRMÉE (domaine : r > 1) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZeta.0.multipliable_norm_eulerFactor_inv` | Si le produit des (1-g i)⁻¹ est multipliable, celui des ‖1-g i‖⁻¹ l'est. | CONFIRMÉE (domaine : multipliabilité du produit complexe) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZeta.0.hasProd_nonneg_of_pos` | Un produit infini de réels strictement positifs, s'il a une valeur a, a a ≥ 0. | CONFIRMÉE (domaine : termes strictement positifs) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZeta.0.hasProd_nnreal_of_coe` | Un HasProd réel sur des NNReal coerces se relève en HasProd dans NNReal. | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZeta.0.multipliable_toNNReal` | Une famille réelle strictement positive multipliable l'est aussi comme famille de NNReal. | CONFIRMÉE (domaine : termes strictement positifs et multipliabilité) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZeta.0.nnreal_coe_tprod` | Pour f à valeurs NNReal multipliable, le produit infini coercé égale la coercion du produit. | CONFIRMÉE (domaine : multipliabilité de f) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZeta.0.nnreal_tprod_le_coe` | Une inégalité de produits infinis dans NNReal se transporte aux coercions réelles. | CONFIRMÉE (domaine : f et g multipliables et inégalité dans NNReal) | AJOUT | 1 |
| `tprod_inv_one_add_real_le_riemannZeta_norm_on_verticalLine` | Pour σ > 1, le produit réel des (1+p^(-σ))⁻¹ est majoré par le produit d'Euler des ‖1-p^(-(σ+it))‖⁻¹. | CONFIRMÉE (domaine : σ > 1) | AJOUT | 1 |
| `one_div_natCast_cpow_eq_ite_cpow_neg` | Pour s ≠ 0, 1/n^s = si n=0 alors 0 sinon n^(-s). | CONFIRMÉE (domaine : s ≠ 0) | AJOUT | 1 |

### `RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaAbelContinuation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `zetaAbelContinuationReLower_pos` | Le seuil réel zetaAbelContinuationReLower est strictement positif. | CONFIRMÉE | AJOUT | 4 |
| `one_lt_zetaAbelContinuationReLower` | Le seuil zetaAbelContinuationReLower est strictement inférieur à 1 (nom inversé par rapport au type). | CONFIRMÉE | AJOUT | 1 |
| `one_sub_zetaAbelContinuationReLower` | 1 - seuil = 9/10. | CONFIRMÉE | AJOUT | 1 |
| `zetaAbelContinuationReLower_lt_half` | Le seuil zetaAbelContinuationReLower est strictement inférieur à 1/2. | CONFIRMÉE | AJOUT | 2 |
| `isOpen_zetaAbelContinuationDomain` | Le domaine de continuation d'Abel est ouvert. | CONFIRMÉE | AJOUT | 1 |
| `isPreconnected_zetaAbelContinuationDomain` | Le domaine de continuation d'Abel est préconnexe. | CONFIRMÉE | AJOUT | 1 |
| `two_mem_zetaAbelContinuationDomain` | Le point 2 appartient au domaine de continuation d'Abel. | CONFIRMÉE | AJOUT | 1 |
| `zetaAbelContinuationDomain_re_pos` | Tout point du domaine de continuation d'Abel a une partie réelle strictement positive. | CONFIRMÉE (domaine : s dans le domaine) | AJOUT | 1 |
| `mem_zetaAbelContinuationDomain_of_re` | Tout s ≠ 1 de partie réelle supérieure au seuil appartient au domaine de continuation d'Abel. | CONFIRMÉE (domaine : s ≠ 1 et Re s > seuil) | AJOUT | 3 |
| `norm_div_re_le_ten_mul_norm_of_mem` | Sur le domaine, ‖z‖/Re z ≤ 10‖z‖. | CONFIRMÉE (domaine : z dans le domaine) | AJOUT | 1 |
| `riemannZeta_abel_integral` | Pour Re s > 1, ζ(s) égale la formule de continuation d'Abel. | CONFIRMÉE (domaine : Re s > 1) | AJOUT | 1 |
| `norm_zetaAbelContinuationFormula_le` | Sur le domaine, ‖formule d'Abel‖ ≤ 1 + ‖1/(s-1)‖ + ‖s‖/Re s. | CONFIRMÉE (domaine : s dans le domaine) | AJOUT | 1 |
| `analyticOn_zetaAbelContinuationFormula` | La formule de continuation d'Abel est analytique sur son domaine. | CONFIRMÉE | AJOUT | 1 |
| `riemannZeta_eq_zetaAbelContinuationFormula` | Sur le domaine de continuation d'Abel, ζ égale la formule d'Abel. | CONFIRMÉE (domaine : s dans le domaine) | AJOUT | 1 |

### `RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaAbelKernel`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `norm_zetaAbelFractKernel_le` | Pour u ≥ 1 et tout s complexe, la norme du noyau de partie fractionnaire {u}·u^(-s-1) est majorée par u^(-re s - 1). | CONFIRMÉE (domaine : u ≥ 1) | AJOUT | 5 |
| `ZetaAbelFractKernel.aestronglyMeasurable` | Pour tout s et tout ensemble mesurable S, le noyau fractionnaire d'Abel est presque partout fortement mesurable pour la mesure de Lebesgue restreinte à S. | CONFIRMÉE (domaine : S mesurable) | AJOUT | 4 |
| `ZetaAbelFractKernel.ae_bound_Ioi` | Pour tout s, presque partout sur (1,∞), la norme du noyau fractionnaire est majorée par u^(-re s - 1). | CONFIRMÉE | AJOUT | 1 |
| `ZetaAbelFractKernel.intervalIntegrable` | Pour tout s et 1 ≤ a ≤ b, le noyau fractionnaire d'Abel est intégrable sur [a,b]. | CONFIRMÉE (domaine : bornes 1 ≤ a ≤ b) | AJOUT | 1 |
| `ZetaAbelFractKernel.tendsto_integral_Ioi` | Pour re s > 1, les intégrales du noyau fractionnaire sur [1,N] tendent vers l'intégrale sur (1,∞) quand N tend vers l'infini. | CONFIRMÉE (domaine : re s > 1) | AJOUT | 1 |
| `ZetaAbelFractKernel.integrableOn_Ioi` | Pour re s > 0, le noyau fractionnaire d'Abel est intégrable sur (1,∞). | CONFIRMÉE (domaine : re s > 0) | AJOUT | 1 |
| `ZetaAbelFractKernel.aestronglyMeasurable_param_deriv` | Pour tout z, la fonction u ↦ -log u · noyau(z,u) est presque partout fortement mesurable sur (1,∞). | CONFIRMÉE | AJOUT | 1 |
| `ZetaAbelFractKernel.eventually_aestronglyMeasurable_param` | Pour tout s, pour z assez proche de s, le noyau en z est presque partout fortement mesurable sur (1,∞). | CONFIRMÉE | AJOUT | 1 |
| `ZetaAbelFractKernel.hasDerivAt_in_param` | Pour u > 1, la dérivée en z du noyau fractionnaire vaut -log u fois le noyau. | CONFIRMÉE (domaine : u > 1) | AJOUT | 1 |
| `ZetaAbelFractKernel.kernel_deriv_norm_bound_on_ball` | Pour u > 1 et re x ≥ ε, la norme de -log u · noyau(x,u) est majorée par log u · u^(-1-ε). | CONFIRMÉE (domaine : u > 1 et re x ≥ ε) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaAbelKernel.0.ZetaAbelFractKernel.ae_on_Ioi_of_all` | Une propriété vraie en tout point de (1,∞) est vraie presque partout sur (1,∞). | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaAbelKernel.0.ZetaAbelFractKernel.dist_lt_of_mem_ball_half` | Si z est dans la boule de centre s et rayon δ/2 avec δ > 0, alors dist z s < δ. | CONFIRMÉE (domaine : δ > 0 ; z dans la boule) | AJOUT | 1 |
| `ZetaAbelFractKernel.hasDerivAt_integral_param_dominated_Ioi` | Dérivation sous l'intégrale sur (1,∞) : sous mesurabilité, intégrabilité, domination de la dérivée par une fonction intégrable et dérivabilité ponctuelle sur une boule, z ↦ ∫ F z est dérivable en s de dérivée ∫ F' s. | CONFIRMÉE (domaine : mesurabilité, intégrabilité, domination par une majorante intégrable, dérivabilité ponctuelle) | AJOUT | 1 |
| `ZetaAbelFractKernel.integral_analytic` | Pour re s > 0, z ↦ ∫_{(1,∞)} noyau(z,u) du est analytique en s. | CONFIRMÉE (domaine : re s > 0) | AJOUT | 1 |

### `RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaConvexity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `norm_riemannZeta_ratio_le_on_verticalLine` | Pour σ > 1, la norme de ζ(2σ)/ζ(σ) est majorée par la norme de ζ sur la droite verticale d'abscisse σ (produit d'Euler). | CONFIRMÉE (domaine : σ > 1) | AJOUT | 1 |
| `norm_riemannZeta_ratio_le_on_vertical_line` | Pour tout t, la norme de ζ(3)/ζ(3/2) est majorée par la norme de ζ(3/2 + it). | CONFIRMÉE | AJOUT | 0 |
| `norm_riemannZeta_le` | Sur le domaine de continuation d'Abel, la norme de ζ(s) est majorée par 1 + ‖1/(s-1)‖ + ‖s‖/re s. | CONFIRMÉE (domaine : s dans le domaine de continuation d'Abel) | AJOUT | 3 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaConvexity.0.StripBounds.three_sq_add_sq_le_sq_add_abs` | Pour tout réel t, 3² + t² ≤ (3 + ∣t∣)². | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaConvexity.0.StripBounds.norm_lt_three_add_abs_im` | Dans la bande 1/2 ≤ re s < 3, ‖s‖ < 3 + ∣im s∣. | CONFIRMÉE (domaine : bande 1/2 ≤ re s < 3) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaConvexity.0.StripBounds.one_div_re_le_two` | Dans la bande 1/2 ≤ re s < 3, 1/re s ≤ 2. | CONFIRMÉE (domaine : bande 1/2 ≤ re s < 3) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaConvexity.0.StripBounds.one_le_norm_sub_one` | Si ∣im s∣ ≥ 1 alors ‖s-1‖ ≥ 1. | CONFIRMÉE (domaine : /im s/ ≥ 1) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaConvexity.0.StripBounds.norm_lt_linear_im` | Dans la bande 1/2 ≤ re s < 3 avec ∣im s∣ ≥ 1, ‖ζ(s)‖ < 2 + 2(3 + ∣im s∣). | CONFIRMÉE (domaine : bande et /im s/ ≥ 1) | AJOUT | 1 |
| `norm_riemannZeta_lt_linear_im_on_strip` | Pour re z dans [1/2,3) et ∣im z∣ ≥ 1, ‖ζ(z)‖ < 8 + 2∣im z∣. | CONFIRMÉE (domaine : bande et /im z/ ≥ 1) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaConvexity.0.shift_mem_strip` | Si ‖s‖ ≤ 1 et ∣t∣ > 2, le point (re s + 3/2) + i(im s + t) est dans la bande re ∈ [1/2,3) avec ∣im∣ ≥ 1. | CONFIRMÉE (domaine : ‖s‖ ≤ 1 et /t/ > 2) | AJOUT | 1 |
| `norm_riemannZeta_shift_le` | Si ‖s‖ ≤ 1 et ∣t∣ > 2, ‖ζ(s + 3/2 + it)‖ < 10 + 2∣t∣. | CONFIRMÉE (domaine : ‖s‖ ≤ 1 et /t/ > 2) | AJOUT | 0 |

### `RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaHadamard`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `completedRiemannZeta₀_entireOfOrderAtMost_one` | La fonction zêta complétée Λ₀ est entière d'ordre au plus 1 (au sens de Hadamard). | CONFIRMÉE | AJOUT | 4 |
| `riemannXi_entireOfOrderAtMost_one` | La fonction ξ de Riemann est entière d'ordre au plus 1. | CONFIRMÉE | AJOUT | 5 |
| `summable_riemannXi_divisorZeroIndex₀_norm_inv_sq` | La somme des ‖ρ‖^(-2) sur les zéros non nuls de ξ (indexés par le diviseur) converge. | CONFIRMÉE | AJOUT | 5 |
| `analyticOrderNatAt_riemannXi_zero` | L'ordre d'annulation de ξ en 0 vaut 0. | CONFIRMÉE | AJOUT | 3 |
| `analyticOrderNatAt_completedRiemannZeta₀_zero` | L'ordre d'annulation de Λ₀ en 0 vaut 0. | CONFIRMÉE | AJOUT | 3 |
| `summable_riemannXi_logDerivTerms_divisorZeroIndex₀` | Hors de l'ensemble des zéros de ξ, la série des termes 1/(z-ρ)+1/ρ sur les zéros converge. | CONFIRMÉE (domaine : z n'est pas un zéro de ξ) | AJOUT | 1 |
| `logDeriv_riemannXi_divisorCanonicalProduct_one_eq_tsum` | Hors des zéros de ξ, la dérivée logarithmique du produit canonique de genre 1 de ξ égale la somme sur les zéros de 1/(z-ρ)+1/ρ. | CONFIRMÉE (domaine : z n'est pas un zéro de ξ) | AJOUT | 1 |
| `logDeriv_riemannXi_eq_polynomial_derivative_add_tsum` | Si ξ = exp(P)·produit canonique de genre 1 et z n'est pas un zéro, alors ξ'/ξ(z) = P'(z) + somme sur les zéros de 1/(z-ρ)+1/ρ. | CONFIRMÉE (domaine : factorisation de Hadamard donnée de ξ ; z hors des zéros) | AJOUT | 3 |
| `riemannXi_hadamard_polynomial_derivative_eval_eq` | Deux polynômes de Hadamard de ξ pour le même produit canonique ont même dérivée en tout point hors des zéros. | CONFIRMÉE (domaine : deux factorisations de Hadamard ; z hors des zéros) | AJOUT | 1 |
| `riemannXi_hadamard_polynomial_derivative_eval_zero_eq` | Deux polynômes de Hadamard de ξ ont même dérivée en 0. | CONFIRMÉE (domaine : deux factorisations de Hadamard de ξ) | AJOUT | 1 |
| `riemannXi_hadamard_factorization` | ξ(z) = exp(P(z))·z^(ordre en 0)·produit canonique de genre 1 avec P de degré ≤ 1. | CONFIRMÉE | AJOUT | 1 |
| `riemannXi_hadamard_factorization_no_monomial` | ξ(z) = exp(P(z))·produit canonique de genre 1 avec P de degré ≤ 1 (monôme d'origine retiré). | CONFIRMÉE | AJOUT | 3 |
| `existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero` | Il existe un unique complexe B égal à P'(0) pour une factorisation de Hadamard de ξ de degré ≤ 1 (constante de Hadamard de Kadiri). | CONFIRMÉE | AJOUT | 0 |
| `exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum` | Hors des zéros de ξ, il existe P de degré ≤ 1 tel que ξ'/ξ(z) = P'(z) + somme sur les zéros de 1/(z-ρ)+1/ρ. | CONFIRMÉE (domaine : z hors des zéros de ξ) | AJOUT | 0 |
| `riemannXi_hadamard_factorization_reindex` | Factorisation de Hadamard de ξ avec produit de facteurs de Weierstrass de genre 1 indexé par toute équivalence avec l'ensemble des zéros. | CONFIRMÉE | AJOUT | 1 |
| `riemannXi_hadamard_factorization_reindex_no_monomial` | Idem, sans monôme d'origine, produit de Weierstrass réindexé. | CONFIRMÉE | AJOUT | 0 |
| `riemannXi_hadamard_factorization_sequence` | Factorisation de Hadamard de ξ avec produit canonique indexé par une énumération ℕ des zéros. | CONFIRMÉE | AJOUT | 1 |
| `riemannXi_hadamard_factorization_sequence_no_monomial` | Idem, sans monôme d'origine, énumération ℕ des zéros. | CONFIRMÉE | AJOUT | 0 |
| `completedRiemannZeta₀_hadamard_factorization` | Λ₀(z) = exp(P(z))·z^(ordre en 0)·produit canonique de genre 1, P de degré ≤ 1. | CONFIRMÉE | AJOUT | 1 |
| `completedRiemannZeta₀_hadamard_factorization_no_monomial` | Λ₀(z) = exp(P(z))·produit canonique de genre 1, sans monôme d'origine. | CONFIRMÉE | AJOUT | 0 |
| `completedRiemannZeta₀_hadamard_factorization_reindex` | Factorisation de Hadamard de Λ₀ avec produit de Weierstrass indexé par toute équivalence avec l'ensemble des zéros. | CONFIRMÉE | AJOUT | 1 |
| `completedRiemannZeta₀_hadamard_factorization_reindex_no_monomial` | Idem, sans monôme d'origine. | CONFIRMÉE | AJOUT | 0 |
| `completedRiemannZeta₀_hadamard_factorization_sequence` | Factorisation de Hadamard de Λ₀ avec produit canonique indexé par une énumération ℕ des zéros. | CONFIRMÉE | AJOUT | 1 |
| `completedRiemannZeta₀_hadamard_factorization_sequence_no_monomial` | Idem, sans monôme d'origine. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaPartialSum`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaPartialSum.0.ZetaPartialSum.natCast_floor_eq_sub_fract` | Pour u ≥ 0, ⌊u⌋ = u - fract(u) dans ℂ. | CONFIRMÉE (domaine : u ≥ 0) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaPartialSum.0.ZetaPartialSum.intervalIntegrable_mul_cpow_id` | Pour 1 ≤ a ≤ b, u ↦ u·u^(-s-1) est intégrable sur [a,b]. | CONFIRMÉE (domaine : 1 ≤ a ≤ b) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaPartialSum.0.ZetaPartialSum.abel_summation` | Pour N ≥ 1, la somme partielle de zêta vaut N·N^(-s) - ∫_1^N ⌊u⌋·(-s·u^(-s-1)) (sommation d'Abel). | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaPartialSum.0.ZetaPartialSum.abel_split` | Pour N ≥ 1, la somme partielle de zêta vaut N^(1-s) + s·∫_1^N ⌊u⌋·u^(-s-1). | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaPartialSum.0.ZetaPartialSum.integral_split_fract` | Pour N ≥ 1, ∫_1^N ⌊u⌋ u^(-s-1) = ∫_1^N u^(-s) - ∫_1^N noyau fractionnaire. | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaPartialSum.0.ZetaPartialSum.cpow_integral` | Pour s ≠ 1 et N ≥ 1, s·∫_1^N u^(-s) = s/(1-s)·(N^(1-s) - 1). | CONFIRMÉE (domaine : s ≠ 1 et N ≥ 1) | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaPartialSum.0.ZetaPartialSum.abel_sub_fract` | Pour N ≥ 1, la somme partielle vaut N^(1-s) + s∫_1^N u^(-s) - s∫_1^N noyau fractionnaire. | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 1 |
| `ZetaPartialSum.abel_formula` | Pour s ≠ 1 et N ≥ 1, somme partielle = N^(1-s)/(1-s) + 1 + 1/(s-1) - s∫_1^N noyau fractionnaire (formule d'Abel). | CONFIRMÉE (domaine : s ≠ 1 et N ≥ 1) | AJOUT | 1 |
| `ZetaPartialSum.tendsto_natCast_cpow_zero_of_neg_re` | Si re w < 0, N^w tend vers 0 quand N tend vers l'infini. | CONFIRMÉE (domaine : re w < 0) | AJOUT | 1 |
| `ZetaPartialSum.tendsto_riemannZeta` | Pour re s > 1, les sommes partielles de zêta convergent vers ζ(s). | CONFIRMÉE (domaine : re s > 1) | AJOUT | 1 |

### `RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaValues`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaValues.0.twenty_seven_div_fifty_lt_eulerMascheroniConstant` | La constante d'Euler-Mascheroni est strictement supérieure à 27/50. | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaValues.0.exp_one_hundred_twenty_seven_div_fifty_gt` | exp(127/50) > 7854/625. | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.P4Port.NumberTheory.LSeries.RiemannZetaValues.0.log_four_mul_pi_lt_one_hundred_twenty_seven_div_fifty` | log(4π) < 127/50. | CONFIRMÉE | AJOUT | 1 |
| `completedRiemannZeta_two` | La zêta complétée Λ vaut π/6 en 2. | CONFIRMÉE | AJOUT | 1 |
| `completedRiemannZeta₀_two` | Λ₀(2) = (π-3)/6. | CONFIRMÉE | AJOUT | 1 |
| `completedRiemannZeta₀_nontrivial` | Λ₀ n'est pas identiquement nulle. | CONFIRMÉE | AJOUT | 3 |
| `completedRiemannZeta₀_zero_eq_one` | Λ₀(0) = Λ₀(1) (équation fonctionnelle). | CONFIRMÉE | AJOUT | 1 |
| `completedRiemannZeta₀_one_ne_zero` | Λ₀(1) ≠ 0. | CONFIRMÉE | AJOUT | 1 |
| `completedRiemannZeta₀_zero_ne_zero` | Λ₀(0) ≠ 0. | CONFIRMÉE | AJOUT | 1 |

### `RhGapCriterion.P4Port.NumberTheory.LSeries.ZetaFiniteOrder`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.completedRiemannZeta₀_bounded_on_closedBall` | Pour tout rayon R > 0, Λ₀ est bornée par une constante M sur la boule fermée de rayon R. | CONFIRMÉE (domaine : R > 0) | AJOUT | 1 |
| `Complex.exists_completedRiemannZeta₀_right_halfPlane` | Pour tout z, il existe w de même valeur de Λ₀ avec re w ≥ 1/2 et ‖w‖ ≤ 1 + ‖z‖ (via l'équation fonctionnelle). | CONFIRMÉE | AJOUT | 1 |
| `Complex.one_sub_re_ge_one_sub_zetaAbelContinuationReLower_of_re_le` | Si re z ≤ σ₀ (borne inférieure du domaine d'Abel), alors 1 - σ₀ ≤ re(1 - z). | CONFIRMÉE (domaine : re z ≤ σ₀) | AJOUT | 1 |
| `Complex.riemannZeta_eq_reflected` | Avec w = 1 - z, w hors des entiers négatifs ou nuls et w ≠ 1, ζ(z) = 2(2π)^(-w)Γ(w)cos(πw/2)ζ(w) (équation fonctionnelle réfléchie). | CONFIRMÉE (domaine : w = 1 - z, w ≠ -n, w ≠ 1) | AJOUT | 1 |
| `Complex.reflected_zeta_coefficient_le` | Inégalité arithmétique : si CΓ ≥ 0 et max(40, 20·CΓ+500) ≤ C alors 2 + CΓ + 2 + 40 ≤ C. | CONFIRMÉE (domaine : CΓ ≥ 0 ; C assez grand) | AJOUT | 1 |
| `Complex.norm_mul_riemannZeta_le_exp_of_reflected` | Sous l'équation réfléchie et des majorations de (2π)^(-w), Γ(w), cos et ζ(w) par des exponentielles en A², ‖(z-1)ζ(z)‖ ≤ exp(C·A²). | CONFIRMÉE (domaine : équation réfléchie, majorations de chaque facteur, A ≥ 1, constantes compatibles) | AJOUT | 1 |
| `Complex.completedRiemannZeta₀_order_one` | Pour tout ε > 0, il existe C > 0 avec ‖Λ₀(z)‖ ≤ exp(C(1+‖z‖)^(1+ε)) : Λ₀ est d'ordre au plus 1. | CONFIRMÉE (domaine : ε > 0) | AJOUT | 1 |
| `Complex.zetaTimesSMinusOne_entire_one` | Le prolongement entier de (s-1)ζ(s) vaut 1 au pôle s = 1. | CONFIRMÉE | AJOUT | 1 |
| `Complex.zetaTimesSMinusOne_entire_eq_mul_riemannZeta` | Pour s ≠ 1, le prolongement entier de (s-1)ζ(s) coïncide avec (s-1)ζ(s). | CONFIRMÉE (domaine : s ≠ 1) | AJOUT | 3 |
| `Complex.completedRiemannZeta_ne_zero_of_one_lt_re` | Pour re s > 1, la zêta complétée Λ(s) ne s'annule pas. | CONFIRMÉE (domaine : re s > 1) | AJOUT | 1 |
| `Complex.eq_zetaTimesSMinusOne_entire_of_eq_on_compl_singleton` | Toute g valant 1 en 1 et (s-1)ζ(s) ailleurs égale le prolongement entier (unicité). | CONFIRMÉE (domaine : g(1) = 1 et g = (s-1)ζ hors de 1) | AJOUT | 0 |
| `Complex.zetaTimesSMinusOne_entire_differentiableOn_compl_singleton` | Le prolongement de (s-1)ζ(s) est holomorphe hors de 1. | CONFIRMÉE | AJOUT | 1 |
| `Complex.zetaTimesSMinusOne_entire_continuousAt_one` | Le prolongement de (s-1)ζ(s) est continu en 1. | CONFIRMÉE | AJOUT | 1 |
| `Complex.zetaTimesSMinusOne_entire_differentiable` | Le prolongement de (s-1)ζ(s) est entier. | CONFIRMÉE | AJOUT | 1 |
| `Complex.zeta_minus_pole_entire_growth` | Il existe C > 0 tel que log(1+‖(s-1)ζ(s)‖) ≤ C(1+‖z‖)² pour tout z (croissance grossière). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.P4Port.NumberTheory.LSeries.ZetaFunctionalEquation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.zeta_functional_equation` | Équation fonctionnelle : Λ(s) = Λ(1-s) pour la zêta complétée de Mathlib. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.P4Port.Topology.MetricSpace.Annulus`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Metric.annulusIoo_eq` | L'annulus Ioo de centre x est la boule ouverte de rayon R privée de la boule fermée de rayon r (espace pseudo-métrique). | CONFIRMÉE | AJOUT | 0 |
| `Metric.annulusIoc_eq` | L'annulus Ioc de centre x est la boule fermée de rayon R privée de la boule fermée de rayon r (espace pseudo-métrique). | CONFIRMÉE | AJOUT | 0 |
| `Metric.annulusIco_eq` | L'annulus Ico de centre x est la boule ouverte de rayon R privée de la boule ouverte de rayon r (espace pseudo-métrique). | CONFIRMÉE | AJOUT | 0 |
| `Metric.annulusIcc_eq` | L'annulus Icc de centre x est la boule fermée de rayon R privée de la boule ouverte de rayon r (espace pseudo-métrique). | CONFIRMÉE | AJOUT | 1 |
| `Metric.annulusIoi_eq` | L'annulus Ioi de centre x est le complémentaire de la boule fermée de rayon r (espace pseudo-métrique). | CONFIRMÉE | AJOUT | 0 |
| `Metric.annulusIci_eq` | L'annulus Ici de centre x est le complémentaire de la boule ouverte de rayon r (espace pseudo-métrique). | CONFIRMÉE | AJOUT | 0 |
| `Metric.annulusIoo_eq_empty` | Si R ≤ r, l'annulus Ioo de centre x et de rayons r,R est vide (espace pseudo-métrique). | CONFIRMÉE (domaine : R ≤ r) | AJOUT | 0 |
| `Metric.annulusIoc_eq_empty` | Si R ≤ r, l'annulus Ioc de centre x et de rayons r,R est vide (espace pseudo-métrique). | CONFIRMÉE (domaine : R ≤ r) | AJOUT | 0 |
| `Metric.annulusIco_eq_empty` | Si R ≤ r, l'annulus Ico de centre x et de rayons r,R est vide (espace pseudo-métrique). | CONFIRMÉE (domaine : R ≤ r) | AJOUT | 0 |
| `Metric.annulusIcc_eq_empty` | Si R < r, l'annulus Icc de centre x et de rayons r,R est vide (espace pseudo-métrique). | CONFIRMÉE (domaine : R < r) | AJOUT | 0 |
| `Metric.annulusIoo_mono` | Monotonie : si r₂ ≤ r₁ et R₁ ≤ R₂, l'annulus Ioo de rayons (r₁,R₁) est inclus dans celui de rayons (r₂,R₂) (espace pseudo-métrique). | CONFIRMÉE (domaine : r₂ ≤ r₁ et R₁ ≤ R₂) | AJOUT | 0 |
| `Metric.annulusIoc_mono` | Monotonie : si r₂ ≤ r₁ et R₁ ≤ R₂, l'annulus Ioc de rayons (r₁,R₁) est inclus dans celui de rayons (r₂,R₂) (espace pseudo-métrique). | CONFIRMÉE (domaine : r₂ ≤ r₁ et R₁ ≤ R₂) | AJOUT | 0 |
| `Metric.annulusIco_mono` | Monotonie : si r₂ ≤ r₁ et R₁ ≤ R₂, l'annulus Ico de rayons (r₁,R₁) est inclus dans celui de rayons (r₂,R₂) (espace pseudo-métrique). | CONFIRMÉE (domaine : r₂ ≤ r₁ et R₁ ≤ R₂) | AJOUT | 0 |
| `Metric.annulusIcc_mono` | Monotonie : si r₂ ≤ r₁ et R₁ ≤ R₂, l'annulus Icc de rayons (r₁,R₁) est inclus dans celui de rayons (r₂,R₂) (espace pseudo-métrique). | CONFIRMÉE (domaine : r₂ ≤ r₁ et R₁ ≤ R₂) | AJOUT | 0 |
| `Metric.annulusIoo_subset_ball` | L'annulus Ioo de rayons r,R est inclus dans la boule ouverte de rayon R. | CONFIRMÉE | AJOUT | 0 |
| `Metric.annulusIoc_subset_closedBall` | L'annulus Ioc de rayons r,R est inclus dans la boule fermée de rayon R. | CONFIRMÉE | AJOUT | 0 |
| `Metric.annulusIco_subset_ball` | L'annulus Ico de rayons r,R est inclus dans la boule ouverte de rayon R. | CONFIRMÉE | AJOUT | 0 |
| `Metric.annulusIcc_subset_closedBall` | L'annulus Icc de rayons r,R est inclus dans la boule fermée de rayon R. | CONFIRMÉE | AJOUT | 0 |
| `Metric.annulusIoc_union_annulusIoo` | Recollement : l'union des annulus Ioc (r,r') et Ioo (r',R) est un annulus de rayons (r,R) de type le type fusionné, sous les ordres r≤r' ou r<r' et r'≤R ou r'<R exigés par les bords. | CONFIRMÉE (domaine : ordre des rayons r, r', R adapté aux bords) | AJOUT | 0 |
| `Metric.annulusIoc_union_annulusIoc` | Recollement : l'union des annulus Ioc (r,r') et Ioc (r',R) est un annulus de rayons (r,R) de type le type fusionné, sous les ordres r≤r' ou r<r' et r'≤R ou r'<R exigés par les bords. | CONFIRMÉE (domaine : ordre des rayons r, r', R adapté aux bords) | AJOUT | 0 |
| `Metric.annulusIoo_union_annulusIco` | Recollement : l'union des annulus Ioo (r,r') et Ico (r',R) est un annulus de rayons (r,R) de type le type fusionné, sous les ordres r≤r' ou r<r' et r'≤R ou r'<R exigés par les bords. | CONFIRMÉE (domaine : ordre des rayons r, r', R adapté aux bords) | AJOUT | 0 |
| `Metric.annulusIoo_union_annulusIcc` | Recollement : l'union des annulus Ioo (r,r') et Icc (r',R) est un annulus de rayons (r,R) de type le type fusionné, sous les ordres r≤r' ou r<r' et r'≤R ou r'<R exigés par les bords. | CONFIRMÉE (domaine : ordre des rayons r, r', R adapté aux bords) | AJOUT | 0 |
| `Metric.annulusIcc_union_annulusIoo` | Recollement : l'union des annulus Icc (r,r') et Ioo (r',R) est un annulus de rayons (r,R) de type le type fusionné, sous les ordres r≤r' ou r<r' et r'≤R ou r'<R exigés par les bords. | CONFIRMÉE (domaine : ordre des rayons r, r', R adapté aux bords) | AJOUT | 0 |
| `Metric.annulusIcc_union_annulusIoc` | Recollement : l'union des annulus Icc (r,r') et Ioc (r',R) est un annulus de rayons (r,R) de type le type fusionné, sous les ordres r≤r' ou r<r' et r'≤R ou r'<R exigés par les bords. | CONFIRMÉE (domaine : ordre des rayons r, r', R adapté aux bords) | AJOUT | 0 |
| `Metric.annulusIco_union_annulusIco` | Recollement : l'union des annulus Ico (r,r') et Ico (r',R) est un annulus de rayons (r,R) de type le type fusionné, sous les ordres r≤r' ou r<r' et r'≤R ou r'<R exigés par les bords. | CONFIRMÉE (domaine : ordre des rayons r, r', R adapté aux bords) | AJOUT | 0 |
| `Metric.annulusIco_union_annulusIcc` | Recollement : l'union des annulus Ico (r,r') et Icc (r',R) est un annulus de rayons (r,R) de type le type fusionné, sous les ordres r≤r' ou r<r' et r'≤R ou r'<R exigés par les bords. | CONFIRMÉE (domaine : ordre des rayons r, r', R adapté aux bords) | AJOUT | 0 |
| `Metric.annulusIoc_union_annulusIoi` | Recollement : l'union des annulus Ioc (r,r') et Ioi (r',R) est un annulus de rayons (r,R) de type le type fusionné, sous les ordres r≤r' ou r<r' et r'≤R ou r'<R exigés par les bords. | CONFIRMÉE (domaine : ordre des rayons r, r', R adapté aux bords) | AJOUT | 0 |
| `Metric.annulusIoo_union_annulusIci` | Recollement : l'union des annulus Ioo (r,r') et Ici (r',R) est un annulus de rayons (r,R) de type le type fusionné, sous les ordres r≤r' ou r<r' et r'≤R ou r'<R exigés par les bords. | CONFIRMÉE (domaine : ordre des rayons r, r', R adapté aux bords) | AJOUT | 0 |
| `Metric.annulusIcc_union_annulusIoi` | Recollement : l'union des annulus Icc (r,r') et Ioi (r',R) est un annulus de rayons (r,R) de type le type fusionné, sous les ordres r≤r' ou r<r' et r'≤R ou r'<R exigés par les bords. | CONFIRMÉE (domaine : ordre des rayons r, r', R adapté aux bords) | AJOUT | 0 |
| `Metric.annulusIco_union_annulusIci` | Recollement : l'union des annulus Ico (r,r') et Ici (r',R) est un annulus de rayons (r,R) de type le type fusionné, sous les ordres r≤r' ou r<r' et r'≤R ou r'<R exigés par les bords. | CONFIRMÉE (domaine : ordre des rayons r, r', R adapté aux bords) | AJOUT | 0 |
| `Metric.iUnion_annulusIco_eq_annulusIci` | Pour une suite de rayons f minorée par f 0 et non majorée, l'union des annulus Ico (f n, f (n+1)) est l'annulus Ici de rayon f 0 (recouvrement de l'espace hors de la boule). | CONFIRMÉE (domaine : f 0 ≤ f n pour tout n ; f non majorée) | AJOUT | 0 |
| `Metric.iUnion_annulusIoc_eq_annulusIoi` | Pour une suite de rayons f minorée par f 0 et non majorée, l'union des annulus Ioc (f n, f (n+1)) est l'annulus Ioi de rayon f 0 (recouvrement de l'espace hors de la boule). | CONFIRMÉE (domaine : f 0 ≤ f n pour tout n ; f non majorée) | AJOUT | 0 |
| `Metric.pairwise_disjoint_on_annulusIco_succ` | Si f est monotone, les annulus Ico de rayons (f i, f (succ i)) sont deux à deux disjoints (espace pseudo-métrique). | CONFIRMÉE (domaine : f monotone ; ordre linéaire avec successeur) | AJOUT | 0 |
| `Metric.pairwise_disjoint_on_annulusIoc_succ` | Si f est monotone, les annulus Ioc de rayons (f i, f (succ i)) sont deux à deux disjoints (espace pseudo-métrique). | CONFIRMÉE (domaine : f monotone ; ordre linéaire avec successeur) | AJOUT | 0 |
| `Metric.pairwise_disjoint_on_annulusIoo_succ` | Si f est monotone, les annulus Ioo de rayons (f i, f (succ i)) sont deux à deux disjoints (espace pseudo-métrique). | CONFIRMÉE (domaine : f monotone ; ordre linéaire avec successeur) | AJOUT | 0 |
| `Metric.eannulusIoo_eq_preimage` | L'e-annulus Ioo de centre x est la préimage de l'intervalle Ioo par y ↦ edist y x. | CONFIRMÉE | AJOUT | 0 |
| `Metric.eannulusIoc_eq_preimage` | L'e-annulus Ioc de centre x est la préimage de l'intervalle Ioc par y ↦ edist y x. | CONFIRMÉE | AJOUT | 0 |
| `Metric.eannulusIco_eq_preimage` | L'e-annulus Ico de centre x est la préimage de l'intervalle Ico par y ↦ edist y x. | CONFIRMÉE | AJOUT | 0 |
| `Metric.eannulusIcc_eq_preimage` | L'e-annulus Icc de centre x est la préimage de l'intervalle Icc par y ↦ edist y x. | CONFIRMÉE | AJOUT | 0 |
| `Metric.eannulusIoi_eq_preimage` | L'e-annulus Ioi de centre x est la préimage de l'intervalle Ioi par y ↦ edist y x. | CONFIRMÉE | AJOUT | 0 |
| `Metric.eannulusIci_eq_preimage` | L'e-annulus Ici de centre x est la préimage de l'intervalle Ici par y ↦ edist y x. | CONFIRMÉE | AJOUT | 0 |
| `Metric.eannulusIoo_eq_empty` | Si R ≤ r, l'e-annulus Ioo de centre x et de rayons r,R est vide (espace pseudo-émétrique, distances dans [0,∞]). | CONFIRMÉE (domaine : R ≤ r) | AJOUT | 0 |
| `Metric.eannulusIoc_eq_empty` | Si R ≤ r, l'e-annulus Ioc de centre x et de rayons r,R est vide (espace pseudo-émétrique, distances dans [0,∞]). | CONFIRMÉE (domaine : R ≤ r) | AJOUT | 0 |
| `Metric.eannulusIco_eq_empty` | Si R ≤ r, l'e-annulus Ico de centre x et de rayons r,R est vide (espace pseudo-émétrique, distances dans [0,∞]). | CONFIRMÉE (domaine : R ≤ r) | AJOUT | 0 |
| `Metric.eannulusIcc_eq_empty` | Si R < r, l'e-annulus Icc de centre x et de rayons r,R est vide (espace pseudo-émétrique, distances dans [0,∞]). | CONFIRMÉE (domaine : R < r) | AJOUT | 0 |
| `Metric.eannulusIoo_mono` | Monotonie : si r₂ ≤ r₁ et R₁ ≤ R₂, l'e-annulus Ioo de rayons (r₁,R₁) est inclus dans celui de rayons (r₂,R₂) (espace pseudo-émétrique, distances dans [0,∞]). | CONFIRMÉE (domaine : r₂ ≤ r₁ et R₁ ≤ R₂) | AJOUT | 0 |
| `Metric.eannulusIoc_mono` | Monotonie : si r₂ ≤ r₁ et R₁ ≤ R₂, l'e-annulus Ioc de rayons (r₁,R₁) est inclus dans celui de rayons (r₂,R₂) (espace pseudo-émétrique, distances dans [0,∞]). | CONFIRMÉE (domaine : r₂ ≤ r₁ et R₁ ≤ R₂) | AJOUT | 0 |
| `Metric.eannulusIco_mono` | Monotonie : si r₂ ≤ r₁ et R₁ ≤ R₂, l'e-annulus Ico de rayons (r₁,R₁) est inclus dans celui de rayons (r₂,R₂) (espace pseudo-émétrique, distances dans [0,∞]). | CONFIRMÉE (domaine : r₂ ≤ r₁ et R₁ ≤ R₂) | AJOUT | 0 |
| `Metric.eannulusIcc_mono` | Monotonie : si r₂ ≤ r₁ et R₁ ≤ R₂, l'e-annulus Icc de rayons (r₁,R₁) est inclus dans celui de rayons (r₂,R₂) (espace pseudo-émétrique, distances dans [0,∞]). | CONFIRMÉE (domaine : r₂ ≤ r₁ et R₁ ≤ R₂) | AJOUT | 0 |
| `Metric.pairwise_disjoint_on_eannulusIco_succ` | Si f est monotone, les e-annulus Ico de rayons (f i, f (succ i)) sont deux à deux disjoints (espace pseudo-émétrique, distances dans [0,∞]). | CONFIRMÉE (domaine : f monotone ; ordre linéaire avec successeur) | AJOUT | 0 |
| `Metric.pairwise_disjoint_on_eannulusIoc_succ` | Si f est monotone, les e-annulus Ioc de rayons (f i, f (succ i)) sont deux à deux disjoints (espace pseudo-émétrique, distances dans [0,∞]). | CONFIRMÉE (domaine : f monotone ; ordre linéaire avec successeur) | AJOUT | 0 |
| `Metric.pairwise_disjoint_on_eannulusIoo_succ` | Si f est monotone, les e-annulus Ioo de rayons (f i, f (succ i)) sont deux à deux disjoints (espace pseudo-émétrique, distances dans [0,∞]). | CONFIRMÉE (domaine : f monotone ; ordre linéaire avec successeur) | AJOUT | 0 |
| `Metric.eannulusIoo_ofReal` | L'e-annulus Ioo de rayons ofReal r, ofReal R égale l'annulus Ioo réel de rayons r,R. | CONFIRMÉE (domaine : 0 ≤ r) | AJOUT | 0 |
| `Metric.eannulusIoc_ofReal` | L'e-annulus Ioc de rayons ofReal r, ofReal R égale l'annulus Ioc réel de rayons r,R. | CONFIRMÉE (domaine : 0 ≤ r) | AJOUT | 0 |
| `Metric.eannulusIco_ofReal` | L'e-annulus Ico de rayons ofReal r, ofReal R égale l'annulus Ico réel de rayons r,R. | CONFIRMÉE | AJOUT | 0 |
| `Metric.eannulusIcc_ofReal` | L'e-annulus Icc de rayons ofReal r, ofReal R égale l'annulus Icc réel de rayons r,R. | CONFIRMÉE (domaine : 0 < r ou 0 ≤ R) | AJOUT | 0 |
| `Metric.eannulusIoi_ofReal` | L'e-annulus Ioi de rayons ofReal r, ofReal R égale l'annulus Ioi réel de rayons r,R. | CONFIRMÉE (domaine : 0 ≤ r) | AJOUT | 0 |
| `Metric.eannulusIci_ofReal` | L'e-annulus Ici de rayons ofReal r, ofReal R égale l'annulus Ici réel de rayons r,R. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.PerronPort.Asymptotics.Asymptotics`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Asymptotics.isLittleO_const_id_cocompact` | Une constante est un o de l'identité au filtre cocompact d'un espace propre. | CONFIRMÉE (domaine : espace propre) | AJOUT | 2 |
| `Asymptotics.isLittleO_const_id_atTop2` | Une constante est un o de l'identité en +∞ (ordre sans maximum, espace propre). | CONFIRMÉE (domaine : ordre sans maximum, espace propre) | AJOUT | 2 |
| `Asymptotics.isLittleO_const_id_atBot2` | Une constante est un o de l'identité en -∞. | CONFIRMÉE (domaine : ordre sans minimum, espace propre) | AJOUT | 2 |
| `Filter.Eventually.natCast` | Une propriété vraie pour x réel assez grand est vraie pour les entiers n assez grands. | CONFIRMÉE | AJOUT | 0 |
| `Asymptotics.IsBigO.natCast` | Si f = O(g) en +∞ sur ℝ, alors n ↦ f(n) = O(n ↦ g(n)) sur ℕ. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.PerronPort.Asymptotics.Uniformly`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Asymptotics.isBigO_of_isBigOUniformly` | Si f = O(g) uniformément sur s, alors f_i = O(g) pour tout i de s. | CONFIRMÉE (domaine : uniformité sur s ; i dans s) | AJOUT | 1 |
| `Asymptotics.isBigO_rev_of_isBigOUniformly_rev` | Si g = O(f) uniformément sur s, alors g = O(f_i) pour tout i de s. | CONFIRMÉE (domaine : uniformité sur s ; i dans s) | AJOUT | 1 |
| `Asymptotics.isTheta_of_isThetaUniformly` | Si f = Θ(g) uniformément sur s, alors f_i = Θ(g) pour tout i de s. | CONFIRMÉE (domaine : uniformité sur s ; i dans s) | AJOUT | 1 |
| `Asymptotics.isLittleO_const_fst_atBot` | Une constante est un o de la première projection au filtre produit (atBot, ly). | CONFIRMÉE | AJOUT | 0 |
| `Asymptotics.isLittleO_const_snd_atBot` | Une constante est un o de la seconde projection au filtre produit (lx, atBot). | CONFIRMÉE | AJOUT | 1 |
| `Asymptotics.isLittleO_const_fst_atTop` | Une constante est un o de la première projection au filtre produit (atTop, ly). | CONFIRMÉE | AJOUT | 0 |
| `Asymptotics.isLittleO_const_snd_atTop` | Une constante est un o de la seconde projection au filtre produit (lx, atTop). | CONFIRMÉE | AJOUT | 1 |
| `ContinuousOn.const_isBigOWithUniformlyOn_isCompact` | Une famille de constantes C(i) continue sur un compact s est uniformément bornée par sup‖C‖/‖c‖ relativement à c. | CONFIRMÉE (domaine : C continue sur s compact ; c non nul) | AJOUT | 1 |
| `ContinuousOn.const_isBigOUniformlyOn_isCompact` | Une famille de constantes C(i) continue sur un compact est uniformément O(1). | CONFIRMÉE (domaine : C continue sur s compact ; c non nul) | AJOUT | 2 |
| `ContinuousOn.const_isBigOWithUniformlyOn_isCompact_rev` | Minoration uniforme d'une famille C(i) continue, sans zéro, sur un compact par inf‖C‖ : c = O_avec(C). | CONFIRMÉE (domaine : C continue sans zéro sur s compact) | AJOUT | 1 |
| `ContinuousOn.const_isBigOUniformlyOn_isCompact_rev` | Une constante est uniformément O de C(i), si C est continue sans zéro sur un compact. | CONFIRMÉE (domaine : C continue sans zéro sur s compact) | AJOUT | 1 |
| `ContinuousOn.const_isThetaUniformlyOn_isCompact` | Une famille C(i) continue sans zéro sur un compact est uniformément Θ(1). | CONFIRMÉE (domaine : C continue sans zéro sur s compact ; c non nul) | AJOUT | 1 |

### `RhGapCriterion.PerronPort.Auxiliary`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Complex.hasDerivAt_ofReal` | L'injection ℝ → ℂ a pour dérivée 1 en tout point. | CONFIRMÉE | AJOUT | 2 |
| `Complex.deriv_ofReal` | La dérivée de l'injection ℝ → ℂ vaut 1. | CONFIRMÉE | AJOUT | 1 |
| `Complex.differentiableAt_ofReal` | L'injection ℝ → ℂ est ℝ-dérivable en tout point. | CONFIRMÉE | AJOUT | 2 |
| `Complex.differentiable_ofReal` | L'injection ℝ → ℂ est ℝ-dérivable. | CONFIRMÉE | AJOUT | 0 |
| `DifferentiableAt.comp_ofReal` | Si e est ℂ-dérivable en ↑z, alors x ↦ e(↑x) est ℝ-dérivable en z. | CONFIRMÉE (domaine : e ℂ-dérivable en ↑z) | AJOUT | 2 |
| `deriv.comp_ofReal` | Si e est ℂ-dérivable en ↑z, la dérivée réelle de x ↦ e(↑x) en z égale la dérivée complexe de e en ↑z. | CONFIRMÉE (domaine : e ℂ-dérivable en ↑z) | AJOUT | 0 |
| `Differentiable.comp_ofReal` | Si e est entière, x ↦ e(↑x) est ℝ-dérivable. | CONFIRMÉE (domaine : e ℂ-dérivable partout) | AJOUT | 0 |
| `DifferentiableAt.ofReal_comp` | Si f réelle est dérivable en z, y ↦ ↑(f y) l'est aussi. | CONFIRMÉE (domaine : f dérivable en z) | AJOUT | 2 |
| `Differentiable.ofReal_comp` | Si f réelle est dérivable, y ↦ ↑(f y) l'est aussi. | CONFIRMÉE (domaine : f dérivable) | AJOUT | 0 |
| `HasDerivAt.of_hasDerivAt_ofReal_comp` | Si y ↦ ↑(f y) a pour dérivée u en z, alors u = ↑u' avec f de dérivée u' en z. | CONFIRMÉE (domaine : dérivabilité de la composée complexe) | AJOUT | 1 |
| `DifferentiableAt.ofReal_comp_iff` | y ↦ ↑(f y) est dérivable en z si et seulement si f l'est. | CONFIRMÉE | AJOUT | 2 |
| `Differentiable.ofReal_comp_iff` | y ↦ ↑(f y) est dérivable si et seulement si f l'est. | CONFIRMÉE | AJOUT | 0 |
| `deriv.ofReal_comp` | La dérivée de y ↦ ↑(f y) en z vaut ↑(f'(z)). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.PerronPort.EulerMaclaurin`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `aestronglyMeasurable_B1` | La fonction B1 (fonction de Bernoulli d'ordre 1) est presque partout fortement mesurable. | CONFIRMÉE | AJOUT | 1 |
| `abs_B1_le_half` | Pour x ≥ 0, ∣B1(x)∣ ≤ 1/2. | CONFIRMÉE (domaine : x ≥ 0) | AJOUT | 1 |
| `integral_deriv_mul_add_const` | Intégration par parties : ∫_a^b (t+c)·f'(t) = (b+c)f(b) - (a+c)f(a) - ∫_a^b f. | CONFIRMÉE (domaine : a ≤ b ; f' intégrable ; f dérivable sur [a,b]) | AJOUT | 1 |
| `intervalIntegrable_deriv_mul_B1` | Si f' est continue sur [a,b] et 0 ≤ a ≤ b, alors f'·B1 est intégrable sur [a,b]. | CONFIRMÉE (domaine : 0 ≤ a ≤ b ; f' continue) | AJOUT | 1 |
| `integral_deriv_mul_floor_add_one` | ∫_a^b f'(t)(⌊t⌋+1) = (b+1/2)f(b) - (a+1/2)f(a) - ∫_a^b f - ∫_a^b f'·B1. | CONFIRMÉE (domaine : 0 ≤ a ≤ b ; f dérivable sur [a,b] ; f' continue) | AJOUT | 1 |
| `sum_eq_integral_add_integral_deriv` | Formule d'Euler-Maclaurin : somme de f(k) pour k dans (⌊a⌋,⌊b⌋] = f(a)B1(a) - f(b)B1(b) + ∫_a^b f + ∫_a^b f'·B1. | CONFIRMÉE (domaine : 0 ≤ a ≤ b ; f dérivable ; f' continue) | AJOUT | 1 |

### `RhGapCriterion.PerronPort.LogBasic`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Real.tendsto_pow_log_div_pow_atTop` | Pour a > 0, (log x)^b / x^a tend vers 0 en +∞. | CONFIRMÉE (domaine : a > 0) | AJOUT | 1 |

### `RhGapCriterion.PerronPort.PerronFormula`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `zeroTendstoDiff` | Si f est nulle pour T assez grand et tend vers L₂ − L₁ quand T tend vers l'infini, alors L₁ = L₂. | CONFIRMÉE (domaine : f eventuellement nulle et de limite L₂ − L₁) | AJOUT | 1 |
| `RectangleIntegral_tendsTo_VerticalIntegral` | Si les intégrales horizontales de f entre σ et σ' tendent vers 0 en ±∞ et si f est intégrable sur les deux droites verticales, l'intégrale de f sur le rectangle de hauteur ±T tend vers VerticalIntegral f σ' − VerticalIntegral f σ quand T → ∞. | CONFIRMÉE (domaine : décroissance des côtés horizontaux et intégrabilité sur les deux verticales) | AJOUT | 2 |
| `verticalIntegral_eq_verticalIntegral` | Si f est holomorphe sur la bande entre σ et σ', que ses intégrales horizontales tendent vers 0 en ±∞ et qu'elle est intégrable sur les deux verticales, les deux intégrales verticales sont égales. | CONFIRMÉE (domaine : holomorphie de f sur la bande, décroissance horizontale et intégrabilité) | AJOUT | 1 |
| `verticalIntegral_sub_verticalIntegral_eq_squareIntegral` | Avec un unique pôle p entre les deux verticales, f holomorphe hors de p et des hypothèses de décroissance et d'intégrabilité, la différence des intégrales verticales égale l'intégrale sur un petit carré centré en p, pour tout côté c assez petit. | CONFIRMÉE (domaine : holomorphie hors du pôle, décroissance horizontale, intégrabilité) | AJOUT | 2 |
| `tendsto_truncated_vertical_shift_with_simple_pole` | Pour f holomorphe hors d'un pôle simple p (de résidu A) dans la bande, avec décroissance horizontale et intégrabilité à droite, l'intégrale verticale tronquée symétrique en σ (normalisée 1/(2πi)) tend vers l'intégrale verticale normalisée en σ' moins A. | CONFIRMÉE (domaine : pôle simple de résidu A, décroissance horizontale, intégrabilité à droite) | AJOUT | 1 |
| `tendsto_truncated_vertical_shift_with_simple_pole_Ioo` | Même énoncé que le décalage tronqué avec pôle simple, écrit avec l'intégrale ensembliste (2π)⁻¹ ∫ sur Ioo(−T,T) de f(σ+it) dt. | CONFIRMÉE (domaine : pôle simple de résidu A, décroissance horizontale, intégrabilité à droite) | AJOUT | 0 |
| `RectangleIntegral_tendsTo_UpperU` | Si l'intégrale horizontale tend vers 0 vers le haut et f est intégrable sur les deux verticales, l'intégrale du rectangle de hauteur T à U tend vers l'intégrale en U (UpperUIntegral) quand U → ∞. | CONFIRMÉE (domaine : décroissance horizontale vers le haut et intégrabilité sur les verticales) | AJOUT | 1 |
| `RectangleIntegral_tendsTo_LowerU` | Symétrique vers le bas : si l'intégrale horizontale tend vers 0 en −∞ et f est intégrable sur les deux verticales, l'intégrale du rectangle tend vers −LowerUIntegral quand U → ∞. | CONFIRMÉE (domaine : décroissance horizontale vers le bas et intégrabilité sur les verticales) | AJOUT | 1 |
| `limitOfConstant` | Une fonction a de σ constante sur σ > 0 et de limite 0 en +∞ est nulle en tout σ > 0. | CONFIRMÉE (domaine : constance sur les σ positifs et limite nulle) | AJOUT | 1 |
| `limitOfConstantLeft` | Une fonction a constante sur σ ≤ −3/2 et de limite 0 en −∞ est nulle en tout σ ≤ −3/2. | CONFIRMÉE (domaine : constance sur σ ≤ −3/2 et limite nulle) | AJOUT | 1 |
| `tendsto_rpow_atTop_nhds_zero_of_norm_lt_one` | Pour 0 < x < 1 et tout C, x^σ·C tend vers 0 quand σ → +∞. | CONFIRMÉE (0 < x < 1) | AJOUT | 2 |
| `tendsto_rpow_atTop_nhds_zero_of_norm_gt_one` | Pour x > 1 et tout C, x^σ·C tend vers 0 quand σ → −∞. | CONFIRMÉE (x > 1) | AJOUT | 1 |
| `Complex.cpow_eq_exp_log_ofReal` | Pour x réel strictement positif, x^y = exp(log x · y) en puissance complexe. | CONFIRMÉE (x > 0) | AJOUT | 0 |
| `Complex.cpow_neg_eq_inv_pow_ofReal_pos` | Pour a réel strictement positif, a^(−r) = (a⁻¹)^r en puissance complexe. | CONFIRMÉE (a > 0) | AJOUT | 1 |
| `Perron.f_mul_eq_f` | Pour t, x > 0, Perron.f t s · x^(−s) = Perron.f (t/x) s : changement d'échelle du noyau de Perron. | CONFIRMÉE (t > 0 et x > 0) | AJOUT | 1 |
| `Perron.isHolomorphicOn` | Pour x > 0, le noyau de Perron Perron.f x est holomorphe sur le complémentaire de {0, −1}. | CONFIRMÉE (x > 0) | AJOUT | 6 |
| `Perron.integral_one_div_const_add_sq_pos` | Pour c > 0, l'intégrale sur ℝ de 1/(c + t²) est strictement positive. | CONFIRMÉE (c > 0) | AJOUT | 2 |
| `Perron.Integrable.one_div_const_add_sq` | Pour c > 0, t ↦ 1/(c + t²) est intégrable sur ℝ. | CONFIRMÉE (c > 0) | AJOUT | 1 |
| `Perron.integralPosAux'_of_le` | Pour 0 < c₁ ≤ c₂, l'intégrale de 1/(√(c₁+t²)·√(c₂+t²)) sur ℝ est strictement positive. | CONFIRMÉE (0 < c₁ ≤ c₂) | AJOUT | 1 |
| `Perron.integralPosAux'` | Pour c₁, c₂ > 0, l'intégrale de 1/(√(c₁+t²)·√(c₂+t²)) sur ℝ est strictement positive. | CONFIRMÉE (c₁, c₂ > 0) | AJOUT | 2 |
| `Perron.integralPosAux` | L'intégrale de 1/(√(1+t²)·√(2+t²)) sur ℝ est strictement positive. | CONFIRMÉE | AJOUT | 2 |
| `Perron.vertIntBound` | Pour x > 0 et σ > 1, la norme de l'intégrale verticale de Perron.f x en σ est majorée par x^σ fois une constante explicite (intégrale de 1/(√(1+t²)√(2+t²))). | CONFIRMÉE (x > 0 et σ > 1) | AJOUT | 1 |
| `Perron.vertIntBoundLeft` | Pour x > 0, il existe C tel que pour tout σ < −3/2 la norme de l'intégrale verticale normalisée de Perron.f x en σ soit ≤ C·x^σ. | CONFIRMÉE (x > 0) | AJOUT | 1 |
| `Perron.map_conj` | Pour x ≥ 0, Perron.f x (conj s) = conj (Perron.f x s) : symétrie de conjugaison du noyau. | CONFIRMÉE (x ≥ 0) | AJOUT | 2 |
| `Perron.isTheta_uniformlyOn_uIcc` | Pour x > 0 et deux abscisses σ', σ'', Perron.f x (σ+iy) est de l'ordre exact 1/y² uniformément pour σ dans l'intervalle fermé quand /y/ → ∞. | CONFIRMÉE (x > 0) | AJOUT | 2 |
| `Perron.isTheta_uniformlyOn_uIoc` | Même énoncé que la version uIcc, avec l'intervalle semi-ouvert uIoc : Perron.f x (σ+iy) = Θ(1/y²) uniformément quand /y/ → ∞. | CONFIRMÉE (x > 0) | AJOUT | 1 |
| `Perron.isTheta` | Pour x > 0 et σ fixé, Perron.f x (σ+iy) est Θ(1/y²) quand y → −∞ et quand y → +∞. | CONFIRMÉE (x > 0) | AJOUT | 1 |
| `Perron.isIntegrable` | Pour x > 0 et σ ∉ {0, −1}, t ↦ Perron.f x (σ+it) est intégrable sur ℝ. | CONFIRMÉE (x > 0, σ ≠ 0, σ ≠ −1) | AJOUT | 6 |
| `Perron.horizontal_integral_isBigO` | Pour x > 0, l'intégrale horizontale de Perron.f x entre σ' et σ'' (mesure localement finie) est O(1/y²) quand /y/ → ∞. | CONFIRMÉE (x > 0) | AJOUT | 2 |
| `Perron.tendsto_zero_Lower` | Pour x > 0, l'intégrale horizontale de Perron.f x entre σ' et σ'' tend vers 0 quand la hauteur tend vers −∞. | CONFIRMÉE (x > 0) | AJOUT | 3 |
| `Perron.tendsto_zero_Upper` | Pour x > 0, l'intégrale horizontale de Perron.f x entre σ' et σ'' tend vers 0 quand la hauteur tend vers +∞. | CONFIRMÉE (x > 0) | AJOUT | 3 |
| `Perron.contourPull` | Pour x > 0, si l'intervalle entre σ' et σ'' ne contient ni 0 ni −1, les intégrales verticales de Perron.f x en σ' et σ'' sont égales. | CONFIRMÉE (domaine : x > 0, l'intervalle évite les pôles 0 et −1) | AJOUT | 2 |
| `Perron.formulaLtOne` | Pour 0 < x < 1 et σ > 0, l'intégrale verticale de Perron.f x en σ vaut 0. | CONFIRMÉE (0 < x < 1 et σ > 0) | AJOUT | 1 |
| `Perron.HolomorphicOn.upperUIntegral_eq_zero` | Si f est holomorphe sur la bande semi-infinie {σ ≤ Re ≤ σ', Im ≥ T}, décroît horizontalement vers le haut et est intégrable sur les deux verticales, l'intégrale en U supérieure (UpperUIntegral) est nulle. | CONFIRMÉE (domaine : holomorphie sur la bande supérieure, décroissance horizontale, intégrabilité) | AJOUT | 0 |
| `Perron.HolomorphicOn.lowerUIntegral_eq_zero` | Si f est holomorphe sur la bande semi-infinie {σ ≤ Re ≤ σ', Im ≤ −T}, décroît horizontalement vers le bas et est intégrable sur les deux verticales, l'intégrale en U inférieure (LowerUIntegral) est nulle. | CONFIRMÉE (domaine : holomorphie sur la bande inférieure, décroissance horizontale, intégrabilité) | AJOUT | 0 |
| `Perron.sPlusOneNeZero` | Si s ≠ −1 alors s + 1 ≠ 0. | CONFIRMÉE (s ≠ −1) | AJOUT | 1 |
| `Perron.keyIdentity` | Pour s ∉ {0, −1}, x^s/(s(s+1)) = x^s/s − x^s/(s+1) : décomposition en fractions simples du noyau de Perron. | CONFIRMÉE (s ≠ 0 et s ≠ −1) | AJOUT | 3 |
| `Filter.Tendsto.eventually_bddAbove` | Si f tend vers y le long d'un filtre l, alors, pour l-presque tout ensemble s, l'image f''s est majorée. | CONFIRMÉE SOUS CONDITION (f a une limite (hypothèse Tendsto)) | AJOUT | 1 |
| `Perron.bddAbove_square_of_tendsto` | Si f a une limite y en x (hors x), alors pour tout côté c > 0 assez petit l'image de f sur le carré épointé Square x c \ {x} est majorée. | CONFIRMÉE (domaine : f a une limite en x épointé) | AJOUT | 2 |
| `Perron.diffBddAtZero` | Pour x > 0 et c > 0 assez petit, la norme de x^s/(s(s+1)) − 1/s est bornée sur le carré épointé centré en 0. | CONFIRMÉE (x > 0) | AJOUT | 1 |
| `Perron.diffBddAtNegOne` | Pour x > 0 et c > 0 assez petit, la norme de x^s/(s(s+1)) + x⁻¹/(s+1) est bornée sur le carré épointé centré en −1. | CONFIRMÉE (x > 0) | AJOUT | 1 |
| `Perron.residueAtZero` | Pour x > 0 et c assez petit, l'intégrale normalisée de Perron.f x sur le petit carré centré en 0 vaut 1 (résidu 1 en 0). | CONFIRMÉE (x > 0) | AJOUT | 1 |
| `Perron.residueAtNegOne` | Pour x > 0 et c assez petit, l'intégrale normalisée de Perron.f x sur le petit carré centré en −1 vaut −x⁻¹ (résidu −1/x en −1). | CONFIRMÉE (x > 0) | AJOUT | 1 |
| `Perron.residuePull1` | Pour x > 1 et σ > 0, l'intégrale verticale normalisée de Perron.f x en σ vaut 1 plus celle en −1/2 (résidu en 0). | CONFIRMÉE (x > 1 et σ > 0) | AJOUT | 1 |
| `Perron.residuePull2` | Pour x > 1, l'intégrale verticale normalisée de x^s/(s(s+1)) en −1/2 vaut −1/x plus celle en −3/2 (résidu en −1). | CONFIRMÉE (x > 1) | AJOUT | 1 |
| `Perron.contourPull3` | Pour x > 1, l'intégrale verticale normalisée de x^s/(s(s+1)) est la même en tout σ' et σ'' ≤ −3/2. | CONFIRMÉE (x > 1, σ' et σ'' ≤ −3/2) | AJOUT | 1 |
| `Perron.formulaGtOne` | Pour x > 1 et σ > 0, l'intégrale verticale normalisée de x^s/(s(s+1)) en σ vaut 1 − 1/x (formule de Perron). | CONFIRMÉE (x > 1 et σ > 0) | AJOUT | 1 |

### `RhGapCriterion.PerronPort.Rectangle`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Rectangle.symm` | Le rectangle de coins z et w est le même que celui de coins w et z. | CONFIRMÉE | AJOUT | 1 |
| `Rectangle.symm_re` | Le rectangle de coins (Re w + i Im z) et (Re z + i Im w) est le même que celui de coins z et w. | CONFIRMÉE | AJOUT | 0 |
| `Square_apply` | Pour c > 0, le carré Square p c est le produit Icc(−c+Re p, c+Re p) ×ℂ Icc(−c+Im p, c+Im p). | CONFIRMÉE (c > 0) | AJOUT | 0 |
| `preimage_equivRealProdCLM_reProdIm` | La préimage d'un produit s ×ℂ t par l'équivalence ℂ ≃ ℝ×ℝ inverse est le produit s ×ˢ t. | CONFIRMÉE | AJOUT | 0 |
| `ContinuousLinearEquiv.coe_toLinearEquiv_symm` | Le coefficient de l'inverse de l'équivalence linéaire sous-jacente à e coïncide avec celui de e.symm (lemme générique Mathlib). | CONFIRMÉE | AJOUT | 0 |
| `segment_reProdIm_segment_eq_convexHull` | Le rectangle à côtés parallèles aux axes de coins z et w (produit des deux intervalles) est l'enveloppe convexe de ses quatre coins. | CONFIRMÉE | AJOUT | 1 |
| `rectangle_in_convex` | Si un ensemble convexe U contient les quatre coins d'un rectangle, il contient le rectangle. | CONFIRMÉE (domaine : U convexe contenant les quatre coins) | AJOUT | 0 |
| `mem_Rect` | Si Re z ≤ Re w et Im z ≤ Im w, alors p est dans le rectangle de coins z, w ssi Re z ≤ Re p ≤ Re w et Im z ≤ Im p ≤ Im w. | CONFIRMÉE (coins ordonnés) | AJOUT | 14 |
| `square_neg` | Square p (−c) = Square p c. | CONFIRMÉE | AJOUT | 1 |
| `Set.left_not_mem_uIoo` | L'extrémité gauche a n'appartient pas à l'intervalle ouvert non orienté uIoo a b. | CONFIRMÉE | AJOUT | 1 |
| `Set.right_not_mem_uIoo` | L'extrémité droite b n'appartient pas à uIoo a b. | CONFIRMÉE | AJOUT | 1 |
| `Set.ne_left_of_mem_uIoo` | Si c appartient à uIoo a b, alors c ≠ a. | CONFIRMÉE (c ∈ uIoo a b) | AJOUT | 1 |
| `Set.ne_right_of_mem_uIoo` | Si c appartient à uIoo a b, alors c ≠ b. | CONFIRMÉE (c ∈ uIoo a b) | AJOUT | 1 |
| `left_mem_rect` | Le coin z appartient au rectangle de coins z, w. | CONFIRMÉE | AJOUT | 1 |
| `right_mem_rect` | Le coin w appartient au rectangle de coins z, w. | CONFIRMÉE | AJOUT | 1 |
| `rect_subset_iff` | Le rectangle de coins z', w' est inclus dans celui de coins z, w ssi z' et w' y appartiennent. | CONFIRMÉE | AJOUT | 2 |
| `RectSubRect` | Si x₀ ≤ x₁ ≤ x₂ ≤ x₃ et y₀ ≤ y₁ ≤ y₂ ≤ y₃, le rectangle de coins (x₁,y₁), (x₂,y₂) est inclus dans celui de coins (x₀,y₀), (x₃,y₃). | CONFIRMÉE (domaine : chaînes d'inégalités des coordonnées) | AJOUT | 1 |
| `RectSubRect'` | Même énoncé que RectSubRect, écrit avec des coins complexes z₀..z₃ dont les parties réelle et imaginaire sont ordonnées. | CONFIRMÉE (domaine : chaînes d'inégalités des coordonnées) | AJOUT | 4 |
| `rectangleBorder_subset_rectangle` | Le bord d'un rectangle est inclus dans le rectangle. | CONFIRMÉE | AJOUT | 11 |
| `rectangle_disjoint_singleton` | Si p est strictement à l'extérieur du rectangle de coins z, w dans l'une des quatre directions, le rectangle est disjoint de {p}. | CONFIRMÉE (domaine : p strictement hors du rectangle dans une direction) | AJOUT | 1 |
| `rectangleBorder_disjoint_singleton` | Si p n'a en commun ni la partie réelle ni la partie imaginaire d'aucun des deux coins, le bord du rectangle est disjoint de {p}. | CONFIRMÉE (domaine : p évite les quatre droites des côtés) | AJOUT | 2 |
| `rectangle_subset_punctured_rect` | Pour des coins ordonnés z₀..z₃, si p est strictement à l'extérieur du rectangle intérieur (z₁,z₂) dans une direction, ce rectangle est inclus dans le grand rectangle (z₀,z₃) privé de p. | CONFIRMÉE (domaine : coins ordonnés et p hors du rectangle intérieur) | AJOUT | 1 |
| `rectangleBorder_subset_punctured_rect` | Pour des coins ordonnés z₀..z₃, si p évite les droites des côtés du rectangle intérieur (z₁,z₂), son bord est inclus dans le grand rectangle (z₀,z₃) privé de p. | CONFIRMÉE (domaine : coins ordonnés et p évitant les côtés) | AJOUT | 1 |
| `rectangle_mem_nhds_iff` | Le rectangle de coins z, w est un voisinage de p ssi p est dans le produit des intervalles ouverts uIoo(Re z, Re w) ×ℂ uIoo(Im z, Im w). | CONFIRMÉE | AJOUT | 4 |
| `mapsTo_rectangle_left_re` | Le côté vertical gauche (Re z fixé, Im dans uIcc) est envoyé dans le rectangle de coins z, w. | CONFIRMÉE | AJOUT | 1 |
| `mapsTo_rectangle_right_re` | Le côté vertical droit (Re w fixé, Im dans uIcc) est envoyé dans le rectangle de coins z, w. | CONFIRMÉE | AJOUT | 1 |
| `mapsTo_rectangle_left_im` | Le côté horizontal inférieur (Im z fixé, Re dans uIcc) est envoyé dans le rectangle de coins z, w. | CONFIRMÉE | AJOUT | 1 |
| `mapsTo_rectangle_right_im` | Le côté horizontal supérieur (Im w fixé, Re dans uIcc) est envoyé dans le rectangle de coins z, w. | CONFIRMÉE | AJOUT | 1 |
| `mapsTo_rectangleBorder_left_re` | Le côté vertical gauche est envoyé dans le bord du rectangle de coins z, w. | CONFIRMÉE | AJOUT | 2 |
| `mapsTo_rectangleBorder_right_re` | Le côté vertical droit est envoyé dans le bord du rectangle de coins z, w. | CONFIRMÉE | AJOUT | 2 |
| `mapsTo_rectangleBorder_left_im` | Le côté horizontal inférieur est envoyé dans le bord du rectangle de coins z, w. | CONFIRMÉE | AJOUT | 2 |
| `mapsTo_rectangleBorder_right_im` | Le côté horizontal supérieur est envoyé dans le bord du rectangle de coins z, w. | CONFIRMÉE | AJOUT | 2 |
| `mapsTo_rectangle_left_re_NoP` | Si p n'est pas sur le bord du rectangle, le côté vertical gauche est envoyé dans le rectangle privé de p. | CONFIRMÉE (domaine : p hors du bord du rectangle) | AJOUT | 0 |
| `mapsTo_rectangle_right_re_NoP` | Si p n'est pas sur le bord du rectangle, le côté vertical droit est envoyé dans le rectangle privé de p. | CONFIRMÉE (domaine : p hors du bord du rectangle) | AJOUT | 0 |
| `mapsTo_rectangle_left_im_NoP` | Si p n'est pas sur le bord du rectangle, le côté horizontal inférieur est envoyé dans le rectangle privé de p. | CONFIRMÉE (domaine : p hors du bord du rectangle) | AJOUT | 0 |
| `mapsTo_rectangle_right_im_NoP` | Si p n'est pas sur le bord du rectangle, le côté horizontal supérieur est envoyé dans le rectangle privé de p. | CONFIRMÉE (domaine : p hors du bord du rectangle) | AJOUT | 0 |
| `not_mem_rectangleBorder_of_rectangle_mem_nhds` | Si le rectangle de coins z, w est un voisinage de p, alors p n'est pas sur son bord. | CONFIRMÉE (domaine : le rectangle est un voisinage de p) | AJOUT | 2 |
| `Complex.nhds_hasBasis_square` | Les carrés Square p x, pour x > 0, forment une base de voisinages de p dans ℂ. | CONFIRMÉE | AJOUT | 4 |
| `square_mem_nhds` | Pour c ≠ 0, Square p c est un voisinage de p. | CONFIRMÉE (c ≠ 0) | AJOUT | 4 |
| `square_subset_square` | Pour 0 < c₁ ≤ c₂, Square p c₁ ⊆ Square p c₂. | CONFIRMÉE (0 < c₁ ≤ c₂) | AJOUT | 3 |
| `SmallSquareInRectangle` | Si un rectangle est voisinage de p, alors pour c > 0 assez petit Square p c est inclus dans le rectangle. | CONFIRMÉE (domaine : le rectangle est un voisinage de p) | AJOUT | 1 |

### `RhGapCriterion.PerronPort.ResidueCalcOnRectangles`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `HIntegral_symm` | L'intégrale horizontale HIntegral f x₁ x₂ y est antisymétrique en (x₁, x₂). | CONFIRMÉE | AJOUT | 1 |
| `VIntegral_symm` | L'intégrale verticale VIntegral f x y₁ y₂ est antisymétrique en (y₁, y₂). | CONFIRMÉE | AJOUT | 0 |
| `verticalIntegral_split_three` | Si t ↦ f(σ+it) est intégrable, l'intégrale verticale se scinde en trois : i·∫ sur Iic a, VIntegral entre a et b, et i·∫ sur Ici b. | CONFIRMÉE (domaine : intégrabilité de f sur la verticale) | AJOUT | 2 |
| `DiffVertRect_eq_UpperLowerUs` | Si f est intégrable sur les deux verticales en σ et σ', alors VerticalIntegral f σ' − VerticalIntegral f σ − RectangleIntegral (hauteur ±T) = UpperUIntegral − LowerUIntegral. | CONFIRMÉE (domaine : intégrabilité sur les deux verticales) | AJOUT | 0 |
| `existsDifferentiableOn_of_bddAbove` | Théorème de Riemann de singularité effaçable : si f est holomorphe sur s \ {c} (s voisinage de c) et bornée, alors elle coïncide hors de c avec une fonction holomorphe sur s. | CONFIRMÉE (domaine : f holomorphe épointée et bornée près de c) | AJOUT | 4 |
| `HolomorphicOn.vanishesOnRectangle` | Si f est holomorphe sur U contenant le rectangle de coins z, w, son intégrale sur le rectangle est nulle (Cauchy–Goursat). | CONFIRMÉE (domaine : holomorphie sur un ouvert contenant le rectangle) | AJOUT | 5 |
| `RectangleIntegral_congr` | Si f et g coïncident sur le bord du rectangle, leurs intégrales de rectangle sont égales. | CONFIRMÉE (domaine : f = g sur le bord) | AJOUT | 1 |
| `RectangleIntegral'_congr` | Si f et g coïncident sur le bord du rectangle, leurs intégrales de rectangle normalisées sont égales. | CONFIRMÉE (domaine : f = g sur le bord) | AJOUT | 2 |
| `rectangleIntegral_symm` | L'intégrale de rectangle est symétrique en les deux coins z, w. | CONFIRMÉE | AJOUT | 0 |
| `rectangleIntegral_symm_re` | Échanger les coins en (Re w + i Im z), (Re z + i Im w) change le signe de l'intégrale de rectangle. | CONFIRMÉE | AJOUT | 0 |
| `RectangleBorderIntegrable.add` | Si f et g sont intégrables sur le bord, l'intégrale de rectangle de f + g est la somme des intégrales. | CONFIRMÉE (domaine : intégrabilité de f et g sur le bord) | AJOUT | 3 |
| `ContinuousOn.rectangleBorder_integrable` | Une fonction continue sur le bord d'un rectangle y est intégrable (au sens RectangleBorderIntegrable). | CONFIRMÉE (domaine : continuité sur le bord) | AJOUT | 5 |
| `ContinuousOn.rectangleBorderIntegrable` | Une fonction continue sur le rectangle est intégrable sur son bord. | CONFIRMÉE (domaine : continuité sur le rectangle) | AJOUT | 1 |
| `ContinuousOn.rectangleBorderNoPIntegrable` | Si f est continue sur le rectangle privé de p et p n'est pas sur le bord, f est intégrable sur le bord. | CONFIRMÉE (domaine : continuité hors de p et p hors du bord) | AJOUT | 1 |
| `HolomorphicOn.rectangleBorderIntegrable'` | Si f est holomorphe sur le rectangle privé de p et que le rectangle est voisinage de p, f est intégrable sur le bord. | CONFIRMÉE (domaine : holomorphie épointée, rectangle voisinage de p) | AJOUT | 1 |
| `HolomorphicOn.rectangleBorderIntegrable` | Si f est holomorphe sur le rectangle, elle est intégrable sur son bord. | CONFIRMÉE (domaine : holomorphie sur le rectangle) | AJOUT | 2 |
| `RectangleIntegralHSplit` | Découpage horizontal : sous intégrabilité des côtés horizontaux sur les deux moitiés, l'intégrale du rectangle est la somme de celles des deux sous-rectangles séparés à l'abscisse a. | CONFIRMÉE (domaine : intégrabilité des côtés horizontaux sur chaque morceau) | AJOUT | 1 |
| `RectangleIntegralHSplit'` | Découpage horizontal à l'abscisse a ∈ uIcc x₀ x₁ : sous intégrabilité du bord, l'intégrale de rectangle est la somme de celles des deux sous-rectangles. | CONFIRMÉE (domaine : intégrabilité du bord) | AJOUT | 1 |
| `RectangleIntegralVSplit` | Découpage vertical : sous intégrabilité des côtés verticaux sur les deux moitiés, l'intégrale du rectangle est la somme de celles des deux sous-rectangles séparés à la hauteur b. | CONFIRMÉE (domaine : intégrabilité des côtés verticaux sur chaque morceau) | AJOUT | 1 |
| `RectangleIntegralVSplit'` | Découpage vertical à la hauteur b ∈ uIcc y₀ y₁ : sous intégrabilité du bord, l'intégrale de rectangle est la somme de celles des deux sous-rectangles. | CONFIRMÉE (domaine : intégrabilité du bord) | AJOUT | 1 |
| `RectanglePullToNhdOfPole'` | Si f est holomorphe sur le grand rectangle privé de p et qu'un sous-rectangle voisinage de p est inclus dedans, les deux intégrales de rectangle sont égales. | CONFIRMÉE (domaine : holomorphie épointée, sous-rectangle voisinage de p, espace complet) | AJOUT | 2 |
| `RectanglePullToNhdOfPole` | Si f est holomorphe sur le rectangle privé de p et que le rectangle est voisinage de p, son intégrale égale, pour c assez petit, celle sur le petit carré centré en p. | CONFIRMÉE (domaine : holomorphie épointée, rectangle voisinage de p) | AJOUT | 1 |
| `RectanglePullToNhdOfPole''` | Version normalisée : si f est holomorphe sur le rectangle privé de p et que le rectangle est voisinage de p, l'intégrale normalisée égale, pour c assez petit, celle sur le petit carré centré en p. | CONFIRMÉE (domaine : holomorphie épointée, rectangle voisinage de p) | AJOUT | 0 |
| `ResidueTheoremAtOrigin_aux1c` | La fonction y ↦ (y + i)⁻¹ est intégrable sur tout intervalle [a, b]. | CONFIRMÉE | AJOUT | 0 |
| `ResidueTheoremAtOrigin_aux1c'` | La fonction y ↦ (y − i)⁻¹ est intégrable sur tout intervalle [a, b]. | CONFIRMÉE | AJOUT | 0 |
| `ResidueTheoremAtOrigin_aux2c` | La fonction y ↦ (1 + iy)⁻¹ est intégrable sur tout intervalle [a, b]. | CONFIRMÉE | AJOUT | 0 |
| `ResidueTheoremAtOrigin_aux2c'` | La fonction y ↦ (−1 + iy)⁻¹ est intégrable sur tout intervalle [a, b]. | CONFIRMÉE | AJOUT | 0 |
| `RectangleIntegral.const_smul` | L'intégrale de rectangle de c • f égale c • l'intégrale de rectangle de f. | CONFIRMÉE | AJOUT | 1 |
| `RectangleIntegral.const_mul'` | L'intégrale de rectangle normalisée de c • f égale c • celle de f. | CONFIRMÉE | AJOUT | 0 |
| `RectangleIntegral.translate` | L'intégrale de rectangle de s ↦ f(s − p) sur (z, w) égale celle de f sur (z − p, w − p) : invariance par translation. | CONFIRMÉE | AJOUT | 1 |
| `RectangleIntegral.translate'` | Invariance par translation de l'intégrale de rectangle normalisée : celle de s ↦ f(s − p) sur (z, w) égale celle de f sur (z − p, w − p). | CONFIRMÉE | AJOUT | 1 |
| `Complex.inv_re_add_im` | Pour x, y réels, (x + iy)⁻¹ = (x − iy)/(x² + y²). | CONFIRMÉE | AJOUT | 1 |
| `sq_add_sq_ne_zero` | Si y ≠ 0 alors x² + y² ≠ 0. | CONFIRMÉE (y ≠ 0) | AJOUT | 3 |
| `continuous_self_div_sq_add_sq` | Si y ≠ 0, x ↦ x/(x² + y²) est continue. | CONFIRMÉE (y ≠ 0) | AJOUT | 2 |
| `integral_self_div_sq_add_sq` | Si y ≠ 0, ∫ de x₁ à x₂ de x/(x²+y²) dx = (log(x₂²+y²) − log(x₁²+y²))/2. | CONFIRMÉE (y ≠ 0) | AJOUT | 1 |
| `integral_const_div_sq_add_sq` | Si y ≠ 0, ∫ de x₁ à x₂ de y/(x²+y²) dx = arctan(x₂/y) − arctan(x₁/y). | CONFIRMÉE (y ≠ 0) | AJOUT | 1 |
| `integral_const_div_self_add_im` | Si y ≠ 0, ∫ de x₁ à x₂ de A/(x+iy) dx = A(log(x₂²+y²) − log(x₁²+y²))/2 − A·i(arctan(x₂/y) − arctan(x₁/y)). | CONFIRMÉE (y ≠ 0) | AJOUT | 2 |
| `integral_const_div_re_add_self` | Si x ≠ 0, ∫ de y₁ à y₂ de A/(x+iy) dy s'exprime par un logarithme de y²+x² et un arctan(y/(−x)) (primitive explicite). | CONFIRMÉE (x ≠ 0) | AJOUT | 2 |
| `ResidueTheoremAtOrigin'` | Si le rectangle de coins z, w contient 0 strictement à l'intérieur (Re z<0, Im z<0, Re w>0, Im w>0), l'intégrale de c/s sur ce rectangle vaut 2πi·c. | CONFIRMÉE (domaine : 0 strictement à l'intérieur du rectangle) | AJOUT | 2 |
| `ResidueTheoremInRectangle` | Si le rectangle est voisinage de p, l'intégrale de rectangle normalisée de c/(s − p) vaut c. | CONFIRMÉE (domaine : coins ordonnés et rectangle voisinage de p) | AJOUT | 2 |
| `ResidueTheoremAtOrigin` | L'intégrale de rectangle normalisée de 1/s sur le rectangle (−1−i, 1+i) vaut 1. | CONFIRMÉE | AJOUT | 0 |
| `ResidueTheoremOnRectangleWithSimplePole` | Si f − A/(s − p) coïncide hors de p avec une g holomorphe sur le rectangle voisinage de p, l'intégrale de rectangle normalisée de f vaut A. | CONFIRMÉE (domaine : partie singulière A/(s−p) et g holomorphe sur le rectangle) | AJOUT | 3 |
| `IsBigO_to_BddAbove` | Si f = O(1) au voisinage épointé de p, il existe un voisinage U de p sur lequel ‖f‖ est borné hors de p. | CONFIRMÉE (domaine : f = O(1) épointé en p) | AJOUT | 3 |
| `BddAbove_on_rectangle_of_bdd_near` | Si f est continue sur le rectangle privé de p et O(1) près de p, alors ‖f‖ est borné sur tout le rectangle privé de p. | CONFIRMÉE (domaine : continuité épointée et f = O(1) près de p) | AJOUT | 1 |
| `ResidueTheoremOnRectangleWithSimplePole'` | Si f est holomorphe sur le rectangle privé de p (voisinage de p) et f − A/(s − p) = O(1) près de p, l'intégrale de rectangle normalisée de f vaut A. | CONFIRMÉE (domaine : holomorphie épointée et f − A/(s−p) = O(1)) | AJOUT | 1 |
| `HasSimplePolesOn.mono` | Avoir des pôles simples sur t entraîne avoir des pôles simples sur tout s ⊆ t. | CONFIRMÉE (domaine : HasSimplePolesOn f t et s ⊆ t) | AJOUT | 2 |
| `residue_eq_of_tendsto` | Si (z − p)·f(z) tend vers c en p (hors p), alors le résidu de f en p vaut c. | CONFIRMÉE (domaine : limite de (z−p)·f(z) égale à c) | AJOUT | 20 |
| `residue_analyticAt_eq_zero` | Si f est analytique en p, son résidu en p est nul. | CONFIRMÉE (domaine : f analytique en p) | AJOUT | 0 |
| `simplePole_sub_residue_isBigO_one` | Si f est méromorphe en p avec ordre −1 (pôle simple), alors f − résidu/(z − p) = O(1) près de p. | CONFIRMÉE (domaine : f méromorphe en p, pôle simple) | AJOUT | 1 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.intervalIntegral_congr_ae_of_codiscreteWithin_along_path` | Si f et g coïncident sur un ensemble codiscret de R et que le chemin p (analytique, non localement constant, à valeurs dans R) parcourt R, les intégrales de f∘p et g∘p sur [a,b] sont égales. | CONFIRMÉE (domaine : coïncidence f = g codiscrète, chemin analytique non localement constant) | AJOUT | 2 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.meromorphicOrderAt_eq_neg_one_of_simplePole` | Si p ∈ U, f a des pôles simples sur U et ordre de f en p < 0, alors cet ordre vaut −1. | CONFIRMÉE (domaine : p ∈ U, pôles simples sur U, ordre négatif) | AJOUT | 2 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.residue_toMeromorphicNFOn_eq_residue` | Si f est méromorphe sur U à pôles simples et p ∈ U est un pôle, le résidu de la forme normale méromorphe de f en p égale celui de f. | CONFIRMÉE (domaine : f méromorphe à pôles simples sur U, p pôle dans U) | AJOUT | 1 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.horizontalPath_not_eventuallyConst` | Le chemin horizontal r ↦ r + ih n'est localement constant en aucun point x. | CONFIRMÉE | AJOUT | 1 |
| `verticalPath_not_eventuallyConst` | Le chemin vertical y ↦ r + iy n'est localement constant en aucun point x. | CONFIRMÉE | AJOUT | 1 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.HIntegral_congr_codiscreteWithin` | Si f = g sur un ensemble codiscret de R et si le segment horizontal reste dans R, leurs intégrales horizontales HIntegral sont égales. | CONFIRMÉE (domaine : coïncidence codiscrète et segment dans R) | AJOUT | 1 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.VIntegral_congr_codiscreteWithin` | Si f = g sur un ensemble codiscret de R et si le segment vertical reste dans R, leurs intégrales verticales VIntegral sont égales. | CONFIRMÉE (domaine : coïncidence codiscrète et segment dans R) | AJOUT | 1 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.rectangleIntegral'_toMeromorphicNFOn_eq` | Pour f méromorphe sur le rectangle, l'intégrale normalisée de f égale celle de sa forme normale méromorphe. | CONFIRMÉE (domaine : f méromorphe sur le rectangle) | AJOUT | 1 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.principalPart_meromorphicOn` | Une somme finie de termes c p/(s − p) est méromorphe sur tout ensemble R. | CONFIRMÉE | AJOUT | 2 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.sub_principalPart_analyticAt_of_not_mem_poles` | Si f est en forme normale méromorphe en x, x n'est pas dans l'ensemble fini de pôles et l'ordre en x est ≥ 0, alors f moins la partie principale (somme des résidus/(s−p)) est analytique en x. | CONFIRMÉE (domaine : forme normale méromorphe en x, x hors des pôles, ordre ≥ 0) | AJOUT | 2 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.meromorphicOrderAt_sub_principalPart_nonneg` | Si p est un pôle simple (ordre −1) de f appartenant à l'ensemble fini de pôles, f moins la somme des parties principales a un ordre ≥ 0 en p. | CONFIRMÉE (domaine : p pôle simple de f dans l'ensemble fini) | AJOUT | 1 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.holoPart_holomorphicOn` | Si f est méromorphe à pôles simples sur le rectangle avec un nombre fini de pôles, f moins sa partie principale (mise en forme normale) est holomorphe sur le rectangle. | CONFIRMÉE (domaine : f méromorphe, pôles simples, finitude des pôles) | AJOUT | 2 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.principalPart_borderIntegrable` | Si le bord du rectangle évite les pôles de f et que les pôles dans le rectangle sont en nombre fini, la partie principale est intégrable sur le bord. | CONFIRMÉE (domaine : bord disjoint des pôles, pôles finis) | AJOUT | 1 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.rectangle_mem_nhds_of_interior` | Pour des coins ordonnés, si p est dans le rectangle sans être sur son bord, le rectangle est un voisinage de p. | CONFIRMÉE (domaine : coins ordonnés, p dans le rectangle hors du bord) | AJOUT | 1 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.sum_div_rectangleBorderIntegrable` | Si le bord du rectangle est disjoint de l'ensemble fini S, toute somme ∑ c p/(s − p) sur S est intégrable sur le bord. | CONFIRMÉE (domaine : bord disjoint de S) | AJOUT | 1 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.rectangleIntegral'_sum_div_sub` | Pour des coins ordonnés, S fini inclus dans le rectangle et disjoint de son bord, l'intégrale normalisée de ∑ c p/(s − p) vaut ∑ c p. | CONFIRMÉE (domaine : coins ordonnés, S dans le rectangle et hors du bord) | AJOUT | 1 |
| `_private.RhGapCriterion.PerronPort.ResidueCalcOnRectangles.0.toMeromorphicNFOn_add_integral` | Pour f méromorphe à pôles simples en nombre fini et évitant le bord, l'intégrale normalisée de f est la somme de celle de sa partie holomorphe et de celle de sa partie principale. | CONFIRMÉE (domaine : f méromorphe, pôles simples finis évitant le bord) | AJOUT | 1 |
| `RectangleIntegral'_eq_sumResiduesIn` | Théorème des résidus sur un rectangle : pour f méromorphe à pôles simples en nombre fini évitant le bord, l'intégrale normalisée de f égale la somme des résidus dans le rectangle. | CONFIRMÉE (domaine : f méromorphe, pôles simples, finis, bord sans pôle) | AJOUT | 3 |
| `residue_eq_zero_of_not_pole_of_meromorphicAt` | Si f est méromorphe en s avec ordre ≥ 0, son résidu en s est nul. | CONFIRMÉE (domaine : f méromorphe en s, ordre ≥ 0) | AJOUT | 1 |
| `sumResiduesIn_inter_eq_of_set_eq` | Si Rn ∩ P = S2 ∩ P et que F a résidu nul en tout point de S2 hors P, alors sumResiduesIn F (Rn ∩ P) = sumResiduesIn F S2. | CONFIRMÉE (domaine : égalité Rn∩P = S2∩P et résidus nuls hors de P) | AJOUT | 1 |

### `RhGapCriterion.PerronPort.Tactic.AdditiveCombination`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Mathlib.Tactic.LinearCombinationPrime.pf_smul_c` | Si a = b, alors a • c = b • c (lemme auxiliaire de tactique). | CONFIRMÉE (domaine : égalité a = b) | AJOUT | 0 |
| `Mathlib.Tactic.LinearCombinationPrime.c_smul_pf` | Si b = c, alors a • b = a • c (lemme auxiliaire de tactique). | CONFIRMÉE (domaine : égalité b = c) | AJOUT | 0 |
| `Mathlib.Tactic.LinearCombinationPrime.smul_pf` | Si a₁ = b₁ et a₂ = b₂, alors a₁ • a₂ = b₁ • b₂ (lemme auxiliaire de tactique). | CONFIRMÉE (domaine : égalités a₁ = b₁ et a₂ = b₂) | AJOUT | 0 |

### `RhGapCriterion.PerronPort.ZetaBounds`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `div_cpow_eq_cpow_neg` | Pour tous complexes a, x, s, a / x^s = a * x^(-s) (puissance complexe). | CONFIRMÉE | AJOUT | 4 |
| `one_div_cpow_eq_cpow_neg` | Pour tous complexes x, s, 1 / x^s = x^(-s). | CONFIRMÉE | AJOUT | 1 |
| `div_rpow_eq_rpow_neg` | Pour a, x, s réels avec 0 ≤ x, a / x^s = a * x^(-s) (puissance réelle). | CONFIRMÉE (domaine : x positif ou nul) | AJOUT | 2 |
| `div_rpow_neg_eq_rpow_div` | Pour x, y réels positifs ou nuls, x^(-s) / y^(-s) = (y/x)^s. | CONFIRMÉE (domaine : x et y positifs ou nuls) | AJOUT | 2 |
| `div_rpow_eq_rpow_div_neg` | Pour x, y réels positifs ou nuls, x^s / y^s = (y/x)^(-s). | CONFIRMÉE (domaine : x et y positifs ou nuls) | AJOUT | 1 |
| `ResidueOfTendsTo` | Si f est holomorphe sur un voisinage épointé de p et que (s-p)*f(s) tend vers A en p, alors f - A/(s-p) est bornée (en norme) sur un voisinage épointé de p (résidu par limite). | CONFIRMÉE (domaine : f holomorphe sur le voisinage épointé, voisinage donné, limite de (s-p)f(s) égale à A) | AJOUT | 1 |
| `analyticAt_riemannZeta` | La fonction zêta est analytique en tout point s différent de 1. | CONFIRMÉE (domaine : s différent de 1) | AJOUT | 1 |
| `differentiableAt_deriv_riemannZeta` | La dérivée de zêta est différentiable en tout point s différent de 1. | CONFIRMÉE (domaine : s différent de 1) | AJOUT | 2 |
| `riemannZetaResidue` | Il existe un voisinage de 1 sur lequel zêta(s) - 1/(s-1) est bornée en norme (pôle simple de résidu 1). | CONFIRMÉE | AJOUT | 0 |
| `deriv_eqOn_of_eqOn_punctured` | Si deux fonctions f, g coïncident sur U privé de p, avec U ouvert, leurs dérivées coïncident sur U privé de p. | CONFIRMÉE (domaine : U ouvert et égalité de f et g sur U privé de p) | AJOUT | 0 |
| `analytic_deriv_bounded_near_point` | Si f est holomorphe sur un ouvert U contenant p, sa dérivée est un O(1) au voisinage épointé de p. | CONFIRMÉE (domaine : U ouvert, p dans U, f holomorphe sur U) | AJOUT | 0 |
| `derivative_const_plus_product` | Formule de dérivation : la dérivée de la fonction constante A plus g(s)(s-p) en x vaut g'(x)(x-p) + g(x). | CONFIRMÉE (domaine : g différentiable en x) | AJOUT | 0 |
| `deriv_inv_sub` | La dérivée de z -> (z-p)^(-1) en x vaut -((x-p)^2)^(-1). | CONFIRMÉE (domaine : x différent de p) | AJOUT | 1 |
| `deriv_f_minus_A_inv_sub_clean` | La dérivée de f - A/(z-p) en x vaut f'(x) + A/(x-p)^2. | CONFIRMÉE (domaine : f différentiable en x et x différent de p) | AJOUT | 0 |
| `nonZeroOfBddAbove` | Si f - A/(s-p) est bornée près de p avec A non nul, alors f ne s'annule pas sur un voisinage ouvert épointé de p. | CONFIRMÉE (domaine : A non nul, f - A/(s-p) bornée sur un voisinage de p, voisinage donné) | AJOUT | 0 |
| `BddAbove_to_IsBigO` | Une fonction bornée en norme sur un voisinage épointé de p est un O(1) au voisinage épointé de p. | CONFIRMÉE (domaine : voisinage donné et borne sur le voisinage épointé) | AJOUT | 0 |
| `ResidueMult` | Si f - A/(s-p) est un O(1) près de p et g holomorphe près de p, alors f*g - A*g(p)/(s-p) est un O(1) près de p (résidu d'un produit). | CONFIRMÉE (domaine : g holomorphe sur un voisinage de p et f - A/(s-p) en O(1)) | AJOUT | 0 |
| `riemannZetaLogDerivResidueBigO` | La dérivée logarithmique -zêta'/zêta moins 1/(z-1) est un O(1) au voisinage épointé de 1. | CONFIRMÉE | AJOUT | 1 |
| `riemannZetaLogDerivResidue` | Il existe un voisinage de 1 sur lequel -(zêta'/zêta)(s) - 1/(s-1) est borné en norme. | CONFIRMÉE | AJOUT | 1 |
| `riemannZeta0_apply` | Formule d'Euler-Maclaurin pour zeta0 N s : somme finie des n^(-s) jusqu'à N plus terme N^(1-s)/(s-1) etc. (définition dépliée de riemannZeta0). | CONFIRMÉE | AJOUT | 1 |
| `Real.differentiableAt_cpow_const_of_ne` | La fonction x -> x^s (x réel, s complexe) est différentiable en tout réel x strictement positif. | CONFIRMÉE (domaine : x strictement positif) | AJOUT | 1 |
| `Complex.one_div_cpow_eq` | Pour x réel non nul, 1 / x^s = x^(-s) (puissance complexe d'un réel). | CONFIRMÉE (domaine : x non nul) | AJOUT | 1 |
| `sum_eq_int_deriv` | Formule de sommation d'Euler : somme de φ(n) pour n dans ]a,b] égale intégrale de φ plus termes de bord en (floor+1/2-x) moins l'intégrale de (floor x + 1/2 - x) φ'. | CONFIRMÉE (domaine : 0 ≤ a < b, φ dérivable sur [a,b], φ' continue sur [a,b]) | AJOUT | 1 |
| `xpos_of_uIcc` | Si a est strictement entre 0 et b et x dans l'intervalle [a,b], alors x > 0. | CONFIRMÉE (domaine : a strictement entre 0 et b) | AJOUT | 3 |
| `ZetaSum_aux1₁` | Pour 1 ≤ a < b, s différent de 1, intégrale de 1/x^s sur [a,b] égale (b^(1-s) - a^(1-s))/(1-s). | CONFIRMÉE (domaine : s différent de 1 et a strictement entre 0 et b) | AJOUT | 1 |
| `ZetaSum_aux1φDiff` | La fonction t -> 1/t^s est dérivable en tout x strictement positif. | CONFIRMÉE (domaine : x strictement positif) | AJOUT | 1 |
| `ZetaSum_aux1φderiv` | La dérivée de t -> 1/t^s en x > 0 vaut -s * x^(-(s+1)). | CONFIRMÉE (domaine : s non nul et x strictement positif) | AJOUT | 2 |
| `ZetaSum_aux1derivφCont` | La dérivée de t -> 1/t^s est continue sur l'intervalle [a,b] avec 0<a<b. | CONFIRMÉE (domaine : s non nul, a strictement entre 0 et b) | AJOUT | 1 |
| `ZetaSum_aux1` | Somme des 1/n^s pour n dans ]a,b] égale (b^(1-s)-a^(1-s))/(1-s) + b^(-s)/2 - a^(-s)/2 + s * intégrale de (floor x + 1/2 - x) x^(-(s+1)). | CONFIRMÉE (domaine : s différent de 0 et de 1, a strictement entre 0 et b) | AJOUT | 1 |
| `ZetaSum_aux1_1'` | Si a > 0 et x dans [a,b] alors x > 0. | CONFIRMÉE (domaine : a strictement positif) | AJOUT | 2 |
| `ZetaSum_aux1_1` | Si a > 0, a < b et x dans l'intervalle non orienté entre a et b, alors x > 0. | CONFIRMÉE (domaine : a strictement positif et a < b) | AJOUT | 3 |
| `ZetaSum_aux1_2` | Pour a > 0, a < b, c non nul et 0 hors de l'intervalle, intégrale de 1/x^(c+1) sur [a,b] égale (a^(-c) - b^(-c))/c. | CONFIRMÉE (domaine : 0 < a < b, c non nul, 0 hors de l'intervalle) | AJOUT | 1 |
| `ZetaSum_aux1_3` | Pour tout réel x, /floor x + 1/2 - x/ ≤ 1/2. | CONFIRMÉE | AJOUT | 6 |
| `ZetaSum_aux1_4'` | Pour x > 0, la norme de (floor x + 1/2 - x)/x^(s+1) vaut /floor x + 1/2 - x/ / x^(re(s+1)). | CONFIRMÉE (domaine : x strictement positif) | AJOUT | 1 |
| `ZetaSum_aux1_4` | Pour 0<a<b, l'intégrale de la norme de (floor x + 1/2 - x)/x^(s+1) égale l'intégrale de /floor x+1/2-x//x^(re(s)+1). | CONFIRMÉE (domaine : 0 < a < b) | AJOUT | 1 |
| `ZetaSum_aux1_5a` | Sur [a,b] avec a > 0, /floor x+1/2-x//x^(re s+1) ≤ 1/x^(re s+1). | CONFIRMÉE (domaine : a strictement positif) | AJOUT | 1 |
| `ZetaSum_aux1_5b` | Si 0<a<b et re(s)>0, 1/u^(re s+1) est intégrable sur [a,b]. | CONFIRMÉE (domaine : 0 < a < b et re(s) > 0) | AJOUT | 2 |
| `measurable_floor_add_half_sub` | La fonction u -> floor u + 1/2 - u est mesurable. | CONFIRMÉE | AJOUT | 2 |
| `ZetaSum_aux1_5c` | La fonction u -> /floor u+1/2-u//u^(re s+1) est fortement mesurable presque partout sur ]a,b]. | CONFIRMÉE | AJOUT | 1 |
| `ZetaSum_aux1_5d` | Si 0<a<b et re(s)>0, u -> /floor u+1/2-u//u^(re s+1) est intégrable sur [a,b]. | CONFIRMÉE (domaine : 0 < a < b et re(s) > 0) | AJOUT | 1 |
| `ZetaSum_aux1_5` | Si 0<a<b et re(s)>0, l'intégrale de /floor x+1/2-x//x^(re s+1) est majorée par l'intégrale de 1/x^(re s+1). | CONFIRMÉE (domaine : 0 < a < b et re(s) > 0) | AJOUT | 1 |
| `ZetaBnd_aux1a` | Si 0<a<b et re(s)>0, l'intégrale de la norme du terme (floor x+1/2-x)/x^(s+1) est majorée par (a^(-re s) - b^(-re s))/re(s). | CONFIRMÉE (domaine : 0 < a < b et re(s) > 0) | AJOUT | 1 |
| `Finset.Ioc_eq_Ico` | Pour naturels M, N, Finset.Ioc N M = Finset.Ico (N+1) (M+1). | CONFIRMÉE | AJOUT | 1 |
| `Finset.Ioc_eq_Icc` | Pour naturels M, N, Finset.Ioc N M = Finset.Icc (N+1) M. | CONFIRMÉE | AJOUT | 0 |
| `Finset.Icc_eq_Ico` | Pour naturels M, N, Finset.Icc N M = Finset.Ico N (M+1). | CONFIRMÉE | AJOUT | 1 |
| `finsetSum_tendsto_tsum` | Si f est sommable, les sommes finies de f sur Ico N k tendent vers la somme infinie de f(n+N) quand k tend vers l'infini. | CONFIRMÉE (domaine : f sommable) | AJOUT | 1 |
| `Complex.cpow_tendsto` | Si re(s) > 1, x^(1-s) tend vers 0 quand x tend vers l'infini. | CONFIRMÉE (domaine : re(s) > 1) | AJOUT | 1 |
| `Complex.cpow_inv_tendsto` | Si re(s) > 0, (x^s)^(-1) tend vers 0 quand x tend vers l'infini. | CONFIRMÉE (domaine : re(s) > 0) | AJOUT | 1 |
| `ZetaSum_aux2a` | Il existe une constante C majorant /floor x+1/2-x/ pour tout réel x. | CONFIRMÉE | AJOUT | 2 |
| `ZetaSum_aux3` | Si re(s) > 1, les sommes de 1/n^s pour n dans ]N,k] tendent vers la somme infinie des 1/(n+N+1)^s. | CONFIRMÉE (domaine : re(s) > 1) | AJOUT | 1 |
| `integrableOn_of_Zeta0_fun` | Si N > 0 et re(s) > 0, (floor x+1/2-x) x^(-(s+1)) est intégrable sur ]N,∞[. | CONFIRMÉE (domaine : N strictement positif et re(s) > 0) | AJOUT | 3 |
| `ZetaSum_aux2` | Si N > 0 et re(s) > 1, la somme infinie des 1/(n+N+1)^s égale -N^(1-s)/(1-s) - N^(-s)/2 + s * intégrale sur ]N,∞[ de (floor x+1/2-x) x^(-(s+1)). | CONFIRMÉE (domaine : N strictement positif et re(s) > 1) | AJOUT | 1 |
| `ZetaBnd_aux1b` | Pour N ≥ 1 et σ > 0, la norme de l'intégrale sur ]N,∞[ de (floor x+1/2-x)/x^(σ+it+1) est majorée par N^(-σ)/σ. | CONFIRMÉE (domaine : N ≥ 1 et σ > 0) | AJOUT | 2 |
| `ZetaBnd_aux1` | Pour N ≥ 1, σ dans ]0,2] et /t/ ≥ 2, la norme de s * intégrale du reste d'Euler-Maclaurin est majorée par 2/t/ N^(-σ)/σ (s = σ+it). | CONFIRMÉE (domaine : N ≥ 1, σ dans ]0,2] et /t/ ≥ 2) | AJOUT | 2 |
| `ZetaBnd_aux1p` | Pour N ≥ 1 et σ dans ]0,2], la norme de s * intégrale du reste est un O(/t/ N^(-σ)/σ) en t sur {/t/ ≥ 2}. | CONFIRMÉE (domaine : N ≥ 1 et σ dans ]0,2]) | AJOUT | 0 |
| `isOpen_aux` | L'ensemble {z / z ≠ 1 et re z > 0} est ouvert. | CONFIRMÉE | AJOUT | 2 |
| `integrable_log_over_pow` | Pour r < 0 et N > 0, x -> ‖x^(r-1)‖ ‖log x‖ est intégrable sur ]N,∞[. | CONFIRMÉE (domaine : r < 0 et N > 0) | AJOUT | 2 |
| `integrableOn_of_Zeta0_fun_log` | Pour N > 0 et re(s) > 0, (floor x+1/2-x) x^(-(s+1)) (-log x) est intégrable sur ]N,∞[. | CONFIRMÉE (domaine : N > 0 et re(s) > 0) | AJOUT | 1 |
| `hasDerivAt_Zeta0Integral` | Pour N > 0 et re(s) > 0, la dérivée en s de l'intégrale de (floor x+1/2-x) x^(-z-1) est l'intégrale du même terme multiplié par -log x. | CONFIRMÉE (domaine : N > 0 et re(s) > 0) | AJOUT | 1 |
| `HasDerivAt_neg_cpow_over2` | La fonction x -> -N^(-x)/2 a pour dérivée -(-log N N^(-s))/2 en s. | CONFIRMÉE (domaine : N > 0) | AJOUT | 1 |
| `HasDerivAt_cpow_over_var` | La fonction z -> -N^z/z a pour dérivée N^z/z^2 - log N N^z / z en tout z non nul. | CONFIRMÉE (domaine : z non nul) | AJOUT | 1 |
| `HasDerivAtZeta0` | La fonction zeta0 N est dérivable en s de dérivée ζ₀' N s. | CONFIRMÉE (domaine : N > 0, re(s) > 0 et s différent de 1) | AJOUT | 2 |
| `HolomorphicOn_riemannZeta0` | zeta0 N est holomorphe sur {s / s ≠ 1 et re s > 0}. | CONFIRMÉE (domaine : N strictement positif) | AJOUT | 1 |
| `HolomorphicOn_riemannZeta` | zêta est holomorphe sur {s / s ≠ 1}. | CONFIRMÉE | AJOUT | 2 |
| `isPathConnected_aux` | L'ensemble {z / z ≠ 1 et re z > 0} est connexe par arcs. | CONFIRMÉE | AJOUT | 1 |
| `Zeta0EqZeta` | Pour N > 0, re(s) > 0 et s ≠ 1, zeta0 N s = zêta(s). | CONFIRMÉE (domaine : N > 0, re(s) > 0 et s différent de 1) | AJOUT | 3 |
| `DerivZeta0EqDerivZeta` | Pour N > 0, re(s) > 0 et s ≠ 1, la dérivée de zeta0 N en s égale la dérivée de zêta en s. | CONFIRMÉE (domaine : N > 0, re(s) > 0 et s différent de 1) | AJOUT | 1 |
| `le_trans₄` | Transitivité en quatre pas : a ≤ b ≤ c ≤ d implique a ≤ d (préordre). | CONFIRMÉE (domaine : les trois inégalités a ≤ b, b ≤ c, c ≤ d) | AJOUT | 1 |
| `lt_trans₄` | Transitivité en quatre pas : a < b < c < d implique a < d. | CONFIRMÉE (domaine : les trois inégalités strictes) | AJOUT | 1 |
| `norm_add₅_le` | Inégalité triangulaire à cinq termes : ‖a+b+c+d+e‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖+‖e‖. | CONFIRMÉE | AJOUT | 1 |
| `norm_add₆_le` | Inégalité triangulaire à six termes. | CONFIRMÉE | AJOUT | 1 |
| `mul_le_mul₃` | Si a ≤ b, c ≤ d, e ≤ f avec c, b, e positifs ou nuls, alors a*c*e ≤ b*d*f (produit de trois inégalités). | CONFIRMÉE (domaine : trois inégalités et trois positivités) | AJOUT | 0 |
| `ZetaBnd_aux2` | Si n ≤ /t/ et 1 - A/log/t/ ≤ σ, alors ‖n^(-(σ+it))‖ ≤ n^(-1) e^A. | CONFIRMÉE (domaine : A > 0, σ > 0, n ≤ /t/ et 1 - A/log/t/ ≤ σ) | AJOUT | 2 |
| `logt_gt_one` | Si t ≥ 3, log t > 1. | CONFIRMÉE (domaine : t ≥ 3) | AJOUT | 8 |
| `UpperBnd_aux` | Pour A dans ]0,1/2], /t/ > 3 et σ ≥ 1 - A/log/t/, N = floor/t/ vérifie N > 0, N ≤ /t/, log/t/ > 1, 1 - A < σ, σ > 0 et σ+it ≠ 1. | CONFIRMÉE (domaine : A dans ]0,1/2], /t/ > 3 et σ ≥ 1 - A/log/t/) | AJOUT | 7 |
| `UpperBnd_aux2` | Si /t/ > 3 et 1 - A/log/t/ ≤ σ, alors /t/^(1-σ) ≤ e^A. | CONFIRMÉE (domaine : /t/ > 3 et 1 - A/log/t/ ≤ σ) | AJOUT | 5 |
| `riemannZeta0_zero_aux` | Pour N > 0, la somme des 1/x sur Ico 0 N égale la somme sur Ico 1 N (le terme x=0 vaut 0 en inverse). | CONFIRMÉE (domaine : N strictement positif) | AJOUT | 1 |
| `UpperBnd_aux3` | Pour A dans ]0,1/2], σ ≥ 1-A/log/t/, /t/ > 3, C ≥ 2, ‖somme des n^(-(σ+it)) pour n ≤ floor/t/‖ ≤ e^A C log/t/. | CONFIRMÉE (domaine : A dans ]0,1/2], σ ≥ 1-A/log/t/, /t/ > 3, C ≥ 2) | AJOUT | 1 |
| `Nat.self_div_floor_bound` | Si /t/ ≥ 1, alors /t//floor/t/ est dans [1,2]. | CONFIRMÉE (domaine : /t/ ≥ 1) | AJOUT | 1 |
| `UpperBnd_aux5` | Si /t/ > 3 et σ ≤ 2, (/t//floor/t/)^σ ≤ 4. | CONFIRMÉE (domaine : /t/ > 3 et σ ≤ 2) | AJOUT | 1 |
| `UpperBnd_aux6` | Pour σ dans ]1/2,2], /t/ > 3 : trois majorations en /t/^(1-σ), /t/^(-σ) pour N^(1-σ)/‖1-s‖, N^(-σ)/2 et N^(-σ)/σ. | CONFIRMÉE (domaine : σ dans ]1/2,2], /t/ > 3, s ≠ 1, N > 0, N ≤ /t/) | AJOUT | 5 |
| `ZetaUpperBnd'` | Borne explicite : la somme des normes des cinq termes de l'expression d'Euler-Maclaurin de zêta(σ+it) est ≤ e^A*(5+16) log/t/. | CONFIRMÉE (domaine : A dans ]0,1/2], /t/ > 3, σ dans [1-A/log/t/,2]) | AJOUT | 1 |
| `ZetaUpperBnd` | Il existe A dans ]0,1/2] et C > 0 tels que /ζ(σ+it)/ ≤ C log/t/ pour /t/ > 3 et σ dans [1-A/log/t/, 2] (borne supérieure classique de zêta près de la droite Re s = 1). | CONFIRMÉE | AJOUT | 3 |
| `norm_complex_log_ofNat` | La norme du logarithme complexe d'un entier naturel n vaut le logarithme réel de n. | CONFIRMÉE | AJOUT | 3 |
| `Real.log_natCast_monotone` | La fonction n -> log n est monotone sur les naturels. | CONFIRMÉE | AJOUT | 0 |
| `Finset.Icc0_eq` | Pour tout naturel N, Icc 0 N = {0} union Icc 1 N. | CONFIRMÉE | AJOUT | 1 |
| `harmonic_eq_sum_Icc0_aux` | Somme des inverses de 0 à N égale somme des inverses de 1 à N. | CONFIRMÉE | AJOUT | 1 |
| `harmonic_eq_sum_Icc0` | Somme des inverses de 0 à N égale le N-ième nombre harmonique (converti en nombre). | CONFIRMÉE | AJOUT | 1 |
| `DerivUpperBnd_aux1` | Pour A dans ]0,1/2], σ ≥ 1-A/log/t/, /t/ > 3, C ≥ 2, ‖somme des -log n / n^(σ+it) pour n ≤ floor/t/‖ ≤ e^A C (log/t/)^2. | CONFIRMÉE (domaine : A dans ]0,1/2], σ ≥ 1-A/log/t/, /t/ > 3, C ≥ 2) | AJOUT | 1 |
| `DerivUpperBnd_aux2` | Majoration ‖-N^(1-s)/(1-s)^2‖ ≤ e^A * 2/3 (s = σ+it, N = floor/t/). | CONFIRMÉE (domaine : /t/ > 3, σ dans [1-A/log/t/,2], N > 0, N ≤ /t/, s ≠ 1, σ > 1/2) | AJOUT | 1 |
| `DerivUpperBnd_aux3` | Majoration ‖log N * N^(1-s)/(1-s)‖ ≤ 2 e^A log/t/. | CONFIRMÉE (domaine : /t/ > 3, σ dans [1-A/log/t/,2], N > 0, N ≤ /t/, s ≠ 1, σ > 1/2) | AJOUT | 1 |
| `DerivUpperBnd_aux4` | Majoration ‖log N * N^(-s)/2‖ ≤ e^A log/t/. | CONFIRMÉE (domaine : /t/ > 3, σ dans [1-A/log/t/,2], N > 0, N ≤ /t/, s ≠ 1, σ > 1/2) | AJOUT | 1 |
| `DerivUpperBnd_aux5` | Majoration de la norme de l'intégrale de (floor x+1/2-x) x^(-s-1) par (1/3) 2/t/ N^(-σ)/σ. | CONFIRMÉE (domaine : /t/ > 3, σ dans [1-A/log/t/,2], N > 0, σ > 1/2) | AJOUT | 1 |
| `DerivUpperBnd_aux6` | Majoration 2/t/ N^(-σ)/σ ≤ 2*(8 e^A). | CONFIRMÉE (domaine : /t/ > 3, σ dans [1-A/log/t/,2], N > 0, N ≤ /t/, s ≠ 1, σ > 1/2) | AJOUT | 1 |
| `DerivUpperBnd_aux7_1` | Pour x ≥ 1, la norme de (floor x+1/2-x) x^(-s-1)(-log x) vaut /floor x+1/2-x/ x^(-σ-1) log x. | CONFIRMÉE (domaine : x ≥ 1) | AJOUT | 1 |
| `DerivUpperBnd_aux7_2` | Pour x ≥ 1, /floor x+1/2-x/ x^(-σ-1) log x ≤ x^(-σ-1) log x. | CONFIRMÉE (domaine : x ≥ 1) | AJOUT | 1 |
| `DerivUpperBnd_aux7_3` | La fonction t -> -(t^(-σ)/σ^2 + t^(-σ) log t/σ) a pour dérivée x^(-σ-1) log x en x. | CONFIRMÉE (domaine : x > 0 et σ non nul) | AJOUT | 1 |
| `DerivUpperBnd_aux7_3'` | Même dérivée sur tout x de [a,∞[ avec a > 0. | CONFIRMÉE (domaine : a > 0, σ non nul) | AJOUT | 2 |
| `DerivUpperBnd_aux7_nonneg` | Pour a ≥ 1, x^(-σ-1) log x est positif ou nul sur ]a,∞[. | CONFIRMÉE (domaine : a ≥ 1) | AJOUT | 2 |
| `DerivUpperBnd_aux7_tendsto` | La primitive -(t^(-σ)/σ^2 + t^(-σ) log t/σ) tend vers 0 à l'infini. | CONFIRMÉE (domaine : σ > 0) | AJOUT | 2 |
| `DerivUpperBnd_aux7_4` | La fonction x^(-σ-1) log x est intégrable sur ]a,∞[. | CONFIRMÉE (domaine : σ > 0 et a ≥ 1) | AJOUT | 2 |
| `DerivUpperBnd_aux7_5` | La fonction /floor x+1/2-x/ x^(-σ-1) log x est intégrable sur ]a,∞[. | CONFIRMÉE (domaine : σ > 0 et a ≥ 1) | AJOUT | 1 |
| `DerivUpperBnd_aux7_integral_eq` | Pour a ≥ 1 et σ > 0, l'intégrale sur ]a,∞[ de x^(-σ-1) log x vaut a^(-σ)/σ^2 + a^(-σ) log a/σ. | CONFIRMÉE (domaine : a ≥ 1 et σ > 0) | AJOUT | 1 |
| `DerivUpperBnd_aux7` | Majoration ‖s * intégrale de (floor x+1/2-x) x^(-s-1)(-log x)‖ ≤ 6/t/ N^(-σ)/σ log/t/. | CONFIRMÉE (domaine : /t/ > 3, σ dans [1-A/log/t/,2], N > 0, N ≤ /t/, s ≠ 1, σ > 1/2) | AJOUT | 1 |
| `ZetaDerivUpperBnd'` | Borne explicite : la somme des normes des six termes de l'expression de zêta'(σ+it) est ≤ e^A*59 (log/t/)^2. | CONFIRMÉE (domaine : A dans ]0,1/2], /t/ > 3, σ dans [1-A/log/t/,2]) | AJOUT | 1 |
| `ZetaDerivUpperBnd` | Il existe A dans ]0,1/2] et C > 0 tels que /ζ'(σ+it)/ ≤ C (log/t/)^2 pour /t/ > 3 et σ dans [1-A/log/t/, 2]. | CONFIRMÉE | AJOUT | 2 |
| `Tendsto_nhdsWithin_punctured_map_add` | Si f est une isométrie strictement monotone de R, y -> f y + a tend vers f x + a en restant à droite quand y tend vers x par la droite. | CONFIRMÉE (domaine : f isométrie strictement monotone) | AJOUT | 1 |
| `Tendsto_nhdsWithin_punctured_add` | Quand y tend vers x par la droite, y + a tend vers x + a par la droite. | CONFIRMÉE | AJOUT | 1 |
| `riemannZeta_isBigO_near_one_horizontal` | ζ(1+x) est un O(1/x) quand x tend vers 0 par la droite. | CONFIRMÉE | AJOUT | 1 |
| `ZetaNear1BndFilter` | ζ(σ) est un O(1/(σ-1)) quand σ tend vers 1 par la droite. | CONFIRMÉE | AJOUT | 1 |
| `ZetaNear1BndExact` | Il existe c > 0 tel que ζ(σ) ≤ c/(σ-1) pour σ dans ]1,2]. | CONFIRMÉE | AJOUT | 2 |
| `norm_zeta_product_ge_one` | Pour x > 0 et tout y, ‖ζ(1+x)^3 ζ(1+x+iy)^4 ζ(1+x+2iy)‖ ≥ 1 (inégalité de Mertens 3-4-1). | CONFIRMÉE (domaine : x strictement positif) | AJOUT | 2 |
| `ZetaLowerBound1_aux1` | Si 1 ≤ ‖ζ(σ)‖^3 ‖ζ(σ+it)‖^4 ‖ζ(σ+2it)‖, alors ‖ζ(σ)‖^(3/4) ‖ζ(σ+2it)‖^(1/4) ‖ζ(σ+it)‖ ≥ 1. | CONFIRMÉE (domaine : la minoration du produit 3-4-1) | AJOUT | 1 |
| `ZetaLowerBound1` | Pour σ > 1, ‖ζ(σ)‖^(3/4) ‖ζ(σ+2it)‖^(1/4) ‖ζ(σ+it)‖ ≥ 1. | CONFIRMÉE (domaine : σ > 1) | AJOUT | 2 |
| `ZetaLowerBound2` | Pour σ > 1, 1/(‖ζ(σ)‖^(3/4) ‖ζ(σ+2it)‖^(1/4)) ≤ ‖ζ(σ+it)‖. | CONFIRMÉE (domaine : σ > 1) | AJOUT | 1 |
| `ZetaLowerBound3_aux1` | Pour A dans ]0,1/2] et /2t/ > 3, A/log/2t/ > 0. | CONFIRMÉE (domaine : A dans ]0,1/2] et /2t/ > 3) | AJOUT | 1 |
| `ZetaLowerBound3_aux2` | Si ‖ζ(σ+2it)‖ ≤ C log/2t/, alors ‖ζ(σ+2it)‖^(1/4) ≤ (C log/2t/)^(1/4). | CONFIRMÉE (domaine : la majoration de ‖ζ(σ+2it)‖) | AJOUT | 1 |
| `ZetaLowerBound3_aux3` | Identité algébrique de réarrangement de puissances : c^(3/4) ((σ-1)^(3/4))^(-1) C^(1/4) log^(1/4) = c^(3/4) C^(1/4) log^(1/4) (σ-1)^(-3/4). | CONFIRMÉE (domaine : σ > 1) | AJOUT | 1 |
| `ZetaLowerBound3_aux4` | Positivité : c^(3/4) (σ-1)^(-3/4) C^(1/4) log/2t/^(1/4) > 0. | CONFIRMÉE (domaine : C > 0, c > 0, /t/ > 3, σ > 1) | AJOUT | 1 |
| `ZetaLowerBound3_aux5` | Si le produit 3/4-1/4-1 est ≥ 1, alors ‖ζ(σ)‖^(3/4) ‖ζ(σ+2it)‖^(1/4) > 0. | CONFIRMÉE (domaine : la minoration du produit ≥ 1) | AJOUT | 1 |
| `ZetaLowerBound3` | Il existe c > 0 tel que, pour σ dans ]1,2] et /t/ > 3, c (σ-1)^(3/4)/(log/t/)^(1/4) ≤ ‖ζ(σ+it)‖ (minoration classique près de la droite Re s = 1). | CONFIRMÉE | AJOUT | 1 |
| `ZetaInvBound1` | Pour σ > 1, 1/‖ζ(σ+it)‖ ≤ ‖ζ(σ)‖^(3/4) ‖ζ(σ+2it)‖^(1/4). | CONFIRMÉE (domaine : σ > 1) | AJOUT | 1 |
| `Ioi_union_Iio_mem_cocompact` | Pour a ≥ 0, ]a,∞[ union ]-∞,-a[ est dans le filtre cocompact de R. | CONFIRMÉE (domaine : a positif ou nul) | AJOUT | 1 |
| `lt_abs_mem_cocompact` | Pour a ≥ 0, {t / a < /t/} est dans le filtre cocompact de R. | CONFIRMÉE (domaine : a positif ou nul) | AJOUT | 0 |
| `ZetaInvBound2` | Il existe C > 0 tel que 1/‖ζ(σ+it)‖ ≤ C (σ-1)^(-3/4) (log/t/)^(1/4) pour σ dans ]1,2] et /t/ > 3. | CONFIRMÉE | AJOUT | 1 |
| `deriv_fun_re` | Si f est différentiable en toute σ+it à t fixé, la dérivée de σ -> f(σ+it) est σ -> f'(σ+it). | CONFIRMÉE (domaine : f différentiable sur toute la droite horizontale à hauteur t) | AJOUT | 1 |
| `Zeta_eq_int_derivZeta` | Pour t non nul, l'intégrale en σ de ζ'(σ+it) entre σ₁ et σ₂ vaut ζ(σ₂+it) - ζ(σ₁+it). | CONFIRMÉE (domaine : t non nul) | AJOUT | 1 |
| `Zeta_diff_Bnd` | Il existe A dans ]0,1/2] et C > 0 tels que /ζ(σ₂+it) - ζ(σ₁+it)/ ≤ C (log/t/)^2 (σ₂-σ₁) pour /t/ > 3, σ₁ ≥ 1-A/log/t/, σ₂ ≤ 2, σ₁ < σ₂. | CONFIRMÉE | AJOUT | 2 |
| `ZetaInvBnd_aux'` | Si log/t/ > 1, alors log/t/ < (log/t/)^9. | CONFIRMÉE (domaine : log/t/ > 1) | AJOUT | 2 |
| `ZetaInvBnd_aux` | Si log/t/ > 1, alors log/t/ ≤ (log/t/)^9. | CONFIRMÉE (domaine : log/t/ > 1) | AJOUT | 2 |
| `ZetaInvBnd_aux2` | Si A ≤ (1/2)(C₁/(2C₂))^4 avec A, C₁, C₂ > 0, alors (C₁ A^(3/4) - 2 C₂ A)^(-1) > 0. | CONFIRMÉE (domaine : A, C₁, C₂ strictement positifs et A ≤ (1/2)(C₁/(2C₂))^4) | AJOUT | 1 |
| `ZetaInvBnd` | Il existe A dans ]0,1/2] et C > 0 tels que 1/‖ζ(σ+it)‖ ≤ C (log/t/)^7 pour /t/ > 3 et σ dans [1-A/(log/t/)^9, 1+A/(log/t/)^9[. | CONFIRMÉE | AJOUT | 1 |
| `ZetaLowerBnd` | Il existe A dans ]0,1/2] et c > 0 tels que ‖ζ(σ+it)‖ ≥ c/(log/t/)^7 pour /t/ > 3 et σ dans [1-A/(log/t/)^9, 1[. | CONFIRMÉE | AJOUT | 1 |
| `ZetaZeroFree` | Il existe A dans ]0,1/2] tel que ζ(σ+it) ≠ 0 pour /t/ > 3 et σ dans [1-A/(log/t/)^9, 1[ (région sans zéro de Vinogradov-Korobov type de la Vallée Poussin). | CONFIRMÉE | AJOUT | 1 |
| `LogDerivZetaBnd` | Il existe A dans ]0,1/2] et C > 0 tels que /ζ'/ζ(σ+it)/ ≤ C (log/t/)^9 pour /t/ > 3 et σ dans [1-A/(log/t/)^9, 1+A/(log/t/)^9[. | CONFIRMÉE | AJOUT | 1 |
| `ZetaNoZerosOn1Line` | ζ ne s'annule jamais sur la droite Re s = 1 : ζ(1+it) ≠ 0 pour tout t réel. | CONFIRMÉE | AJOUT | 0 |
| `ZetaCont` | ζ est continue sur le complémentaire de {1}. | CONFIRMÉE | AJOUT | 1 |
| `ZetaNoZerosInBox` | Pour toute hauteur T, il existe σ < 1 tel que ζ ne s'annule pas sur {σ' + it / σ' ≥ σ, /t/ ≤ T}. | CONFIRMÉE | AJOUT | 2 |
| `LogDerivZetaHoloOn` | Si S ne contient pas 1 et que ζ ne s'annule pas sur S, alors ζ'/ζ est holomorphe sur S. | CONFIRMÉE (domaine : 1 hors de S et ζ sans zéro sur S) | AJOUT | 2 |
| `LogDerivZetaHolcSmallT` | Il existe σ₂ < 1 tel que ζ'/ζ est holomorphe sur le rectangle [σ₂,2] x [-3,3] privé de 1. | CONFIRMÉE | AJOUT | 0 |
| `LogDerivZetaHolcLargeT` | Il existe A dans ]0,1/2] tel que, pour tout T ≥ 3, ζ'/ζ est holomorphe sur le rectangle [1-A/(log T)^9, 2] x [-T,T] privé de 1. | CONFIRMÉE | AJOUT | 0 |
| `summable_complex_then_summable_real_part` | Si f : N -> C est sommable, la suite des parties réelles est sommable. | CONFIRMÉE (domaine : f sommable) | AJOUT | 1 |
| `dlog_riemannZeta_bdd_on_vertical_lines_generalized` | Pour 1 < σ₀ ≤ σ₁, ‖-ζ'/ζ(σ₁+it)‖ ≤ ‖ζ'/ζ(σ₀)‖ (borne de la dérivée logarithmique sur les droites verticales). | CONFIRMÉE (domaine : 1 < σ₀ ≤ σ₁) | AJOUT | 2 |
| `triv_bound_zeta` | Il existe C ≥ 0 tel que ‖-ζ'/ζ(σ₀+it)‖ ≤ 1/(σ₀-1) + C pour σ₀ > 1 et tout t. | CONFIRMÉE | AJOUT | 1 |
| `LogDerivZetaBndUnif` | Il existe A dans ]0,1/2] et C > 0 tels que /ζ'/ζ(σ+it)/ ≤ C (log/t/)^9 pour /t/ > 3 et σ ≥ 1-A/(log/t/)^9 (borne uniforme sans borne supérieure sur σ). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.PrimeDeterminedZeroCompleteGrammar`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `primeDeterminedZeroMember_eq` | Pour toute continuation F déterminée par les premiers, le prédicat « zéro non trivial de F » est le même que « zéro non trivial de zêta ». | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 1 |
| `primeDeterminedZeroMultiplicity_eq` | Pour toute continuation F déterminée par les premiers, la multiplicité de zéros normalisée de F est la multiplicité canonique de zêta. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 1 |
| `primeDeterminedZeroSource_eq_canonical` | Pour toute continuation F déterminée par les premiers, la source de zéros déterminée par F est la source canonique de zêta. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 6 |
| `prime_determined_any_zero_source_object_eq` | Pour toute continuation F déterminée par les premiers et tout constructeur G défini sur les sources de zéros, G appliqué à la source déterminée par F égale G appliqué à la source canonique. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 15 |
| `complexZeroOrderKey_injective` | La clé d'ordre des complexes (partie imaginaire, partie réelle) est injective : elle détermine le complexe. | CONFIRMÉE | AJOUT | 2 |
| `instIsTransComplexComplexZeroLe` | La relation d'ordre générique ComplexZeroLe sur C est transitive. | CONFIRMÉE | AJOUT | 2 |
| `instAntisymmComplexComplexZeroLe` | La relation d'ordre générique ComplexZeroLe sur C est antisymétrique. | CONFIRMÉE | AJOUT | 2 |
| `instTotalComplexComplexZeroLe` | La relation d'ordre générique ComplexZeroLe sur C est totale. | CONFIRMÉE | AJOUT | 2 |
| `complexZeroLe_antisymm` | Si ρ ≤ σ et σ ≤ ρ pour l'ordre générique, alors ρ = σ (antisymétrie explicite). | CONFIRMÉE (domaine : les deux inégalités ρ ≤ σ et σ ≤ ρ) | AJOUT | 1 |
| `zeroHeightSet_canonical` | Pour tout T, l'ensemble de zéros de hauteur bornée de la source canonique est l'ensemble canonique des zéros non triviaux de hauteur bornée par T. | CONFIRMÉE | AJOUT | 0 |
| `zeroHeightSet_canonical_finite` | Pour tout T, l'ensemble de zéros de hauteur bornée de la source canonique est fini. | CONFIRMÉE | AJOUT | 1 |
| `zeroHeightFinset_canonical` | Pour tout T, le finset de zéros de hauteur bornée de la source canonique est le finset canonique des zéros non triviaux de hauteur bornée. | CONFIRMÉE | AJOUT | 2 |
| `mem_zeroHeightFinset_canonical` | Un complexe ρ est dans le finset de zéros de hauteur bornée de la source canonique si et seulement si c'est un zéro non trivial de zêta avec /Im ρ/ < T. | CONFIRMÉE | AJOUT | 4 |
| `zeroPositiveMembers_canonical` | Pour tout T, les représentants positifs génériques de la source canonique sont l'image (par coercition en complexes) des représentants positifs canoniques. | CONFIRMÉE | AJOUT | 1 |
| `mem_zeroOrderedMembers_canonical` | Un complexe ρ est dans la vue ordonnée générique de la source canonique si et seulement si c'est un zéro non trivial de zêta avec 0 < Im ρ < T. | CONFIRMÉE | AJOUT | 2 |
| `zeroOrderedMembers_canonical` | Pour tout T, la vue ordonnée générique de la source canonique est la liste des représentants positifs ordonnés canoniques (transportée en complexes). | CONFIRMÉE | AJOUT | 3 |
| `zeroMemberState_eq_one_or_five` | L'état canonique d'un complexe ρ vaut 1 ou 5. | CONFIRMÉE | AJOUT | 3 |
| `zeroMemberState_eq_one_iff_critical_line` | L'état canonique d'un complexe ρ vaut 1 si et seulement si Re ρ = 1/2. | CONFIRMÉE | AJOUT | 5 |
| `zeroMemberState_eq_five_iff_off_critical_line` | L'état canonique d'un complexe ρ vaut 5 si et seulement si Re ρ ≠ 1/2. | CONFIRMÉE | AJOUT | 2 |
| `zeroMemberTransition_exactly_four` | Pour tous complexes ρ, σ, la transition de membres vaut l'une des quatre transformations tau11, tau15, tau51, tau55, avec unicité triviale de la valeur. | CONFIRMÉE | AJOUT | 0 |
| `zeroMemberTransition_depends_on_both` | Si les états de ρ et σ sont distincts, la transition de (ρ,σ) est différente de celle de (σ,ρ). | CONFIRMÉE (domaine : les états de ρ et de σ sont distincts) | AJOUT | 0 |
| `zeroMemberTransition_self_eq_tau11_iff_critical_line` | La transition d'un complexe avec lui-même vaut tau11 si et seulement si Re ρ = 1/2. | CONFIRMÉE | AJOUT | 0 |
| `zeroCountUpTo_canonical_mono` | Le comptage global des zéros de la source canonique jusqu'à la hauteur t est croissant au sens large en t. | CONFIRMÉE (domaine : t ≤ u) | AJOUT | 1 |
| `zeroCountUpTo_prime_determined_mono` | Le comptage global des zéros de la source déterminée par F jusqu'à la hauteur t est croissant au sens large en t. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers et t ≤ u) | AJOUT | 0 |
| `prime_determined_zero_complete_grammar_eq_canonical` | Pour toute borne T, position n et longueur k, le bloc de grammaire complète de la constellation de zéros déterminée par F égale celui de la source canonique. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 19 |
| `prime_determined_zero_members_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « membres » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_heights_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « hauteurs » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_multiplicities_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « multiplicités » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_symmetries_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « symétries » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_gaps_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « écarts de hauteur » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 1 |
| `prime_determined_zero_transitions_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « transitions » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_patterns_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « pattern » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_families_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « famille » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_entry_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « entrée » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_exit_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « sortie » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_member_order_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « ordre des membres » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_transition_order_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « ordre des transitions » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_pattern_order_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « ordre des patterns » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_family_order_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « ordre des familles » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_global_density_eq_canonical` | Pour toute continuation F déterminée par les premiers, le champ « densité globale » du bloc de grammaire de zéros déterminé par F égale celui du bloc canonique (idem, projection du théorème central). | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_pattern_occurrence_eq` | Pour toute F déterminée par les premiers, l'ensemble des positions n où un pattern P donné apparaît (largeur w) est le même pour la source déterminée par F et pour la source canonique. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_family_occurrence_eq` | Pour toute F déterminée par les premiers, l'ensemble des positions n où une famille f donnée apparaît est le même des deux côtés. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_pattern_succession_eq` | Pour toute F déterminée par les premiers, la succession finie de patterns (n, k, w) est la même des deux côtés. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 1 |
| `prime_determined_zero_family_succession_eq` | Pour toute F déterminée par les premiers, la succession finie de familles (n, k, w) est la même des deux côtés. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 1 |
| `prime_determined_zero_transition_succession_eq` | Pour toute F déterminée par les premiers, la succession finie de transitions (n, k) est la même des deux côtés. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 1 |
| `prime_determined_zero_ordered_members_eq` | Pour toute F déterminée par les premiers, la vue ordonnée complète des membres jusqu'à T est la même des deux côtés. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 1 |
| `prime_determined_zero_count_eq` | Pour toute F déterminée par les premiers, le comptage global des zéros jusqu'à la hauteur t est le même des deux côtés. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 1 |
| `primeDeterminedZeroEquiv_coe` | La valeur complexe du membre transporté par l'équivalence primeDeterminedZeroEquiv est celle du membre de départ. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `primeDeterminedZeroMultiplicity_transport` | L'ordre analytique de F en un membre transporté égale la multiplicité canonique de zêta de son image par l'équivalence. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |
| `prime_determined_zero_grammar_bridge` | Paquet terminal : conjonction de l'égalité du bloc de grammaire complet, de la vue ordonnée, du comptage, des successions de transitions et de leurs variantes entre la source déterminée par F et la source canonique. | CONFIRMÉE (domaine : F est une continuation de zêta déterminée par l'histoire des nombres premiers) | AJOUT | 0 |

### `RhGapCriterion.PrimeDeterminedZeroRecovery`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `prime_determined_first_five_zero_members_eq_canonical` | Pour toute continuation F déterminée par les nombres premiers, la fenêtre de 5 membres (à partir de l'indice 0) de la constellation ordonnée des zéros issue de F égale celle de la source canonique des zéros de zêta, pour tout T. | CONFIRMÉE (domaine : F est une continuation déterminée par l'histoire des nombres premiers) | AJOUT | 1 |
| `prime_determined_first_five_zero_heights_eq_canonical` | Idem pour les hauteurs des 5 premiers membres de la constellation issue de F (égales aux hauteurs canoniques). | CONFIRMÉE (domaine : F continuation déterminée par les premiers) | AJOUT | 0 |
| `prime_determined_first_five_zero_grammar_eq_canonical` | Idem pour le bloc de grammaire complet des 5 premiers membres (égal à celui de la source canonique). | CONFIRMÉE (domaine : F continuation déterminée par les premiers) | AJOUT | 0 |
| `prime_determined_first_hundred_zero_members_eq_canonical` | Idem instance k=100 : la fenêtre de 100 membres issue de F égale la fenêtre canonique. | CONFIRMÉE (domaine : F continuation déterminée par les premiers) | AJOUT | 1 |
| `prime_determined_first_hundred_zero_heights_eq_canonical` | Idem pour les hauteurs des 100 premiers membres. | CONFIRMÉE (domaine : F continuation déterminée par les premiers) | AJOUT | 0 |
| `prime_determined_first_hundred_zero_grammar_eq_canonical` | Idem pour le bloc de grammaire complet des 100 premiers membres. | CONFIRMÉE (domaine : F continuation déterminée par les premiers) | AJOUT | 0 |
| `prime_determined_zero_window_eq_canonical_any_length` | Pour toute continuation F déterminée par les premiers, toute fenêtre (début n, longueur k) de la constellation issue de F égale la fenêtre canonique, pour tout T. | CONFIRMÉE (domaine : F continuation déterminée par les premiers) | AJOUT | 3 |
| `prime_determined_first_five_is_an_instance` | Les fenêtres à 5 membres sont des instances du théorème universel : l'énoncé (types abrégés ⋯ = ⋯) est l'égalité des fenêtres à 5 membres pour F déterminée par les premiers. | CONFIRMÉE (domaine : F continuation déterminée par les premiers) | AJOUT | 0 |
| `prime_determined_first_hundred_is_an_instance` | Les fenêtres à 100 membres sont des instances du théorème universel : l'énoncé (types abrégés ⋯ = ⋯) est l'égalité des fenêtres à 100 membres pour F déterminée par les premiers. | CONFIRMÉE (domaine : F continuation déterminée par les premiers) | AJOUT | 0 |

### `RhGapCriterion.PrimeDeterminesZetaAndZeros`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `primes_determine_zeta_meromorphic_continuation` | Toute continuation F déterminée par les nombres premiers coïncide avec la fonction zêta de Riemann sur le complémentaire de {1}. | CONFIRMÉE (domaine : F continuation déterminée par les premiers) | AJOUT | 2 |
| `primes_determine_nontrivial_zero_multiset` | Toute continuation F déterminée par les nombres premiers a le même multiensemble de zéros non triviaux que zêta. | CONFIRMÉE (domaine : F continuation déterminée par les premiers) | AJOUT | 4 |

### `RhGapCriterion.PrimeGrammarMemberContactDecoderNoGo`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `GrammarContactReadout.stage_pos` | Le champ stage d'un décodeur de contact de grammaire est au moins 1. | CONFIRMÉE | AJOUT | 2 |
| `no_shared_completeGrammar_contact_readout_for_true_offline` | Pour un zéro nontrivial ρ de partie réelle différente de 1/2 et tout décodeur de contact lisant un bloc de grammaire complet, la loi E44 ne peut être satisfaite à la fois pour Re ρ et pour 1 − Re ρ par la même lecture (no-go local ρ et son miroir). | RÉFUTATION COMPILÉE (lecture commune du bloc de grammaire décodant à la fois le membre hors ligne et son miroir selon la loi E44) | AJOUT | 2 |
| `no_prime_completeGrammar_memberwise_common_contact_for_true_offline` | Spécialisation au bloc de grammaire complet canonique des premiers : pour ρ de partie réelle différente de 1/2, aucun décodeur ne satisfait la loi E44 à la fois pour Re ρ et 1 − Re ρ. | RÉFUTATION COMPILÉE (lecture commune du bloc canonique premier pour les deux membres miroirs hors ligne selon la loi E44) | AJOUT | 0 |
| `no_zero_reconstructed_completeGrammar_memberwise_common_contact_for_true_offline` | Même no-go après reconstruction exacte du bloc de grammaire depuis le canal des zéros (M^Z=M ne crée pas d'identité de membre) : pas de décodeur satisfaisant E44 pour Re ρ et 1 − Re ρ si Re ρ différent de 1/2. | RÉFUTATION COMPILÉE (lecture commune du bloc reconstruit depuis les zéros pour les deux membres miroirs selon la loi E44) | AJOUT | 0 |
| `critical_of_prime_completeGrammar_common_member_contact` | Si un même bloc de grammaire canonique premier décode par la loi E44 à la fois Re ρ et 1 − Re ρ, alors Re ρ = 1/2. | CONFIRMÉE (domaine : loi E44 satisfaite pour ρ et son miroir par le même décodeur) | AJOUT | 0 |

### `RhGapCriterion.PrimeZeroIntertwining`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `zeroMode_add` | Le mode d'un zéro ρ est additif en son amplitude. | CONFIRMÉE | AJOUT | 0 |
| `zeroMode_smul_amplitude` | Le mode d'un zéro ρ est homogène (multiplication scalaire) en son amplitude. | CONFIRMÉE | AJOUT | 2 |
| `windowedPairing_add` | L'appariement fenêtré est additif en le signal. | CONFIRMÉE | AJOUT | 0 |
| `windowedPairing_window_union` | L'appariement fenêtré sur l'union de deux fenêtres disjointes est la somme des appariements. | CONFIRMÉE (domaine : fenêtres disjointes) | AJOUT | 0 |
| `windowed_identity_exact` | Identité fenêtrée définitionnelle : WT(U) = S(U) + reste(U), le reste étant défini par cette égalité. | CONFIRMÉE | AJOUT | 1 |
| `windowed_mode_scale_intertwining` | L'appariement fenêtré d'un mode de zéro ρ décalé de a vaut exp((ρ − 1/2)a) fois l'appariement non décalé (entrelacement mode par mode). | CONFIRMÉE | AJOUT | 2 |
| `spectral_sum_scale_action_modewise` | Sur une somme spectrale finie de modes, l'action d'échelle U ↦ U+a agit mode par mode avec la valeur propre exp((ρ − 1/2)a) de chaque mode. | CONFIRMÉE | AJOUT | 0 |
| `zeroMode_norm` | La norme d'un mode de zéro ρ d'amplitude A vaut ‖A‖·exp((Re ρ − 1/2)U). | CONFIRMÉE | V102 | 13 |
| `subexponential_mode_forces_re_le_half` | Si A ≠ 0 et que la norme du mode de ρ est sous-exponentielle, alors Re ρ ≤ 1/2. | CONFIRMÉE SOUS CONDITION (amplitude non nulle et norme du mode sous-exponentielle) | AJOUT | 1 |
| `RH_from_windowed_identity_and_remainder_bound` | Pour un ensemble Z de zéros stable par ρ ↦ 1 − ρ, si chaque composante fenêtrée se décompose en mode d'amplitude non nulle plus reste et que composante et reste sont sous-exponentiels, alors tout ρ de Z a Re ρ = 1/2. | IMPLIQUE RH SOUS PRÉMISSE (décomposition mode plus reste de la composante fenêtrée, sous-exponentialité de la composante et du reste, amplitudes non nulles, stabilité de Z par 1 − ρ) | AJOUT | 1 |
| `classed_path_sum_partition` | Sur toute fenêtre [a,b) avec 1 ≤ a ≤ b, la somme sur les classes {0,2,4} des sommes partielles classées de (g n − log p n) vaut Tmode b − Tmode a. | CONFIRMÉE (domaine : 1 ≤ a ≤ b) | AJOUT | 2 |
| `classed_path_sum_translation_commute` | Idem après translation de la fenêtre de k : somme classée sur [a+k, b+k) égale Tmode(b+k) − Tmode(a+k). | CONFIRMÉE (domaine : 1 ≤ a ≤ b) | AJOUT | 0 |

### `RhGapCriterion.Round23TerminalClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `round23_zero_prime_gap_reconstruction` | Conjonction : comptage pondéré des zéros = π pondéré au seuil canonique, et comptage, position, écart premiers reconstruits depuis les zéros égalent ceux de l'histoire première, et toute continuation déterminée par les premiers égale zêta hors de 1 et a les mêmes zéros non triviaux. | CONFIRMÉE | V48 | 2 |

### `RhGapCriterion.Round25G2CCorrectedTEmbedding`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `correctedTAtPrime_eq_p_sub_chebyshev` | Le signal T corrigé au m-ième premier (m ≥ 1) vaut p_m − θ(p_m), l'erreur de Chebyshev. | CONFIRMÉE (domaine : 1 ≤ m) | AJOUT | 4 |
| `two_le_p_real` | Pour tout m, 2 ≤ p_m (en réel). | CONFIRMÉE | AJOUT | 16 |
| `corrected_T_at_prime_orbit_rest_decomposition` | Pour un zéro nontrivial ρ et m ≥ 1, le signal T corrigé au m-ième premier se décompose en contribution d'orbite plus contribution du reste. | CONFIRMÉE (domaine : ρ zéro nontrivial, 1 ≤ m) | AJOUT | 1 |
| `orbitTContribution_eq_fromP5` | La contribution d'orbite au m-ième premier égale celle définie via les projecteurs P5 (traçabilité), pour ρ zéro nontrivial et m ≥ 1. | CONFIRMÉE (domaine : ρ zéro nontrivial, 1 ≤ m) | AJOUT | 1 |
| `corrected_T_at_prime_P5_orbit_rest_decomposition` | Le signal T corrigé au m-ième premier égale la contribution d'orbite via P5 plus la contribution du reste (m ≥ 1, ρ zéro nontrivial). | CONFIRMÉE (domaine : ρ zéro nontrivial, 1 ≤ m) | AJOUT | 2 |
| `zeroReconstructedCorrectedTAtPrime_eq_correctedTAtPrime` | Le signal T corrigé reconstruit depuis les zéros égale le signal T corrigé canonique, pour tout m. | CONFIRMÉE | V48 | 1 |
| `zero_reconstructed_corrected_T_orbit_rest_decomposition` | Le signal reconstruit depuis les zéros se décompose en orbite P5 plus reste (ρ zéro nontrivial, m ≥ 1). | CONFIRMÉE (domaine : ρ zéro nontrivial, 1 ≤ m) | V48 | 0 |
| `correctedTAtPrime_eq_Tmode_add_boundaryCorrection` | Le signal T corrigé au m-ième premier égale Tmode m plus la correction de bord de Chebyshev. | CONFIRMÉE | AJOUT | 2 |
| `TChebyshevBoundaryCorrection_increment` | L'incrément de la correction de bord vaut −(log p_{m+1} − log p_m). | CONFIRMÉE | AJOUT | 1 |
| `correctedTAtPrime_increment` | L'incrément du signal T corrigé vaut aT m moins (log p_{m+1} − log p_m), pour m ≥ 1. | CONFIRMÉE (domaine : 1 ≤ m) | AJOUT | 1 |
| `zeroReconstructedTChebyshevBoundaryCorrection_eq` | La correction de bord de Chebyshev reconstruite depuis les zéros égale la correction canonique. | CONFIRMÉE | V48 | 0 |
| `zeroReconstructedCorrectedTAtPrime_eq_mode_add_correction` | Le signal T corrigé reconstruit depuis les zéros égale Tmode reconstruit plus la correction de bord reconstruite. | CONFIRMÉE | V48 | 0 |
| `TChebyshevBoundaryCorrection_abs_le_log` | La correction de bord de Chebyshev est bornée en valeur absolue par abs(3 − log 2) + log p_m. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Round25G2CEnergyBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `p_ge_add_two` | Pour tout n, n + 2 ≤ p_n (la suite des premiers indexée croît au moins comme n+2). | CONFIRMÉE | AJOUT | 7 |
| `energyTerm_eq_zero_of_snd_dominates` | Si X ≤ p_{N+1}, le terme d'énergie energyTerm a X m N est nul. | CONFIRMÉE (domaine : fenêtre X inférieure ou égale à p_{N+1}) | AJOUT | 1 |
| `energyTerm_eq_zero_of_fst_dominates` | Si X ≤ p_{N+1}, le terme d'énergie energyTerm a X N n est nul (version symétrique). | CONFIRMÉE (domaine : fenêtre X inférieure ou égale à p_{N+1}) | AJOUT | 1 |
| `VTkernel_succ_eq_of_dominates` | Si X ≤ p_{N+1}, étendre l'horizon de troncature de N à N+1 ne change pas VTkernel a X. | CONFIRMÉE (domaine : X inférieure ou égale à p_{N+1}) | AJOUT | 1 |
| `VTkernel_eq_of_ge_horizon` | Si X ≤ p_{N+1}, VTkernel a X est stable pour tout horizon N' ≥ N. | CONFIRMÉE (domaine : X ≤ p_{N+1}, N ≤ N') | AJOUT | 2 |
| `canonicalTHorizon_dominates` | L'horizon explicite canonicalTHorizon U domine la fenêtre exp U : exp U ≤ p_{canonicalTHorizon U + 1}. | CONFIRMÉE | AJOUT | 15 |
| `canonicalTLocalEnergy_eq_VTkernel_of_ge_horizon` | L'énergie locale T canonique égale VTkernel a (exp U) N pour tout horizon N au moins canonicalTHorizon U. | CONFIRMÉE (domaine : N au moins égal à l'horizon canonique) | AJOUT | 1 |
| `canonicalTEnergy_eq_VTkernel_aT_of_ge_horizon` | L'énergie T canonique égale VTkernel aT (exp U) N pour tout horizon N au moins canonicalTHorizon U. | CONFIRMÉE (domaine : N au moins égal à l'horizon canonique) | AJOUT | 2 |
| `offlineOrbitEnergy_eq_weightedP5OrbitProjectionEnergy` | Pour ρ zéro nontrivial, l'énergie de l'orbite hors ligne égale l'énergie de projection P5 pondérée. | CONFIRMÉE (domaine : ρ zéro nontrivial) | AJOUT | 1 |
| `weightedP5OrbitProjectionEnergy_eq_exp_growth` | L'énergie de projection P5 pondérée d'un zéro nontrivial ρ vaut 2·‖amplitude hors ligne‖²·exp(2(Re ρ − 1/2)U). | CONFIRMÉE (domaine : ρ zéro nontrivial) | AJOUT | 0 |

### `RhGapCriterion.Round25G2CGrammarBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `zero_reconstructed_canonical_T_energy_eq_canonicalTEnergy` | L'énergie T canonique reconstruite depuis les zéros égale l'énergie T canonique. | CONFIRMÉE | V48 | 0 |
| `zeroReconstructedRelationOf_eq` | La relation reconstruite depuis les zéros à l'indice n égale transformOf(p_n mod 6, p_{n+1} mod 6). | CONFIRMÉE | V48 | 1 |
| `zeroReconstructedGrammarPairClass_eq_canonicalGrammarPairClass` | Le classificateur de paires de grammaire reconstruit depuis les zéros égale le classificateur canonique, point par point. | CONFIRMÉE | V48 | 3 |
| `canonicalTEnergy_eq_sum_grammar_pair_classes` | L'énergie T canonique se partitionne exactement en la somme, sur les classes de paires de grammaire, des termes d'énergie sur l'horizon canonique. | CONFIRMÉE | AJOUT | 0 |
| `zero_reconstructed_canonical_T_energy_grammar_partition_eq` | L'énergie T reconstruite depuis les zéros se partitionne exactement selon les mêmes classes de paires de grammaire. | CONFIRMÉE | V48 | 0 |
| `zero_reconstructed_transformation_conditioned_increment_decomposition` | Pour n ≥ 2, l'incrément de Tmode reconstruit depuis les zéros se décompose selon la transformation (transformOf des résidus mod 6) en 6k + 3·croisement − log p_n + variation de potentiel de grammaire. | CONFIRMÉE (domaine : 2 ≤ n) | V174 | 0 |

### `RhGapCriterion.Round25G2CNormalizedWindowEnergy`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `canonicalTHorizon_dominates_div` | Pour r ≥ 1, exp U / r ≤ p_{canonicalTHorizon U + 1}. | CONFIRMÉE (domaine : r ≥ 1) | AJOUT | 4 |
| `min_sub_min_eq_min_sub_max_zero_sub` | Pour a ≤ b, min(b,t) − min(a,t) = min(b−a, max(0, t−a)) (longueur de [a,b] ∩ (−∞,t]). | CONFIRMÉE (domaine : a ≤ b) | AJOUT | 1 |
| `gramWeight_eq_min_sub` | gramWeight X j est la longueur tronquée min(p_{j+2} − p_{j+1}, max(0, X − p_{j+1})). | CONFIRMÉE | AJOUT | 1 |
| `gramWeight_monotone` | gramWeight X j est monotone croissante en X. | CONFIRMÉE | AJOUT | 2 |
| `gramWindowWeight_nonneg` | Pour r ≥ 1, le poids de fenêtre gramWindowWeight r U j est positif ou nul. | CONFIRMÉE (domaine : r ≥ 1) | AJOUT | 18 |
| `gramWeight_pos_imp_lt` | Si gramWeight X j > 0 alors p_{j+1} < X. | CONFIRMÉE | AJOUT | 1 |
| `gramWindowWeight_ne_zero_imp_lt` | Pour r ≥ 1, si gramWindowWeight r U j ≠ 0 alors p_{j+1} < exp U. | CONFIRMÉE (domaine : r ≥ 1) | AJOUT | 1 |
| `gramWindowWeight_sum_le_exp` | Pour r ≥ 1, la somme des poids de fenêtre sur l'horizon canonique est au plus exp U. | CONFIRMÉE (domaine : r ≥ 1) | AJOUT | 6 |
| `rawRWindowEnergy_eq_sum_weighted_R_sq` | Pour r ≥ 1, l'énergie brute rawRWindowEnergy est la somme sur l'horizon canonique de gramWindowWeight · R(j+1)². | CONFIRMÉE (domaine : r ≥ 1) | AJOUT | 5 |
| `rawRWindowEnergy_nonneg` | Pour r ≥ 1, rawRWindowEnergy r U est positive ou nulle. | CONFIRMÉE (domaine : r ≥ 1) | AJOUT | 1 |
| `normalizedRWindowEnergy_nonneg` | Pour r ≥ 1, l'énergie normalisée normalizedRWindowEnergy r U est positive ou nulle. | CONFIRMÉE (domaine : r ≥ 1) | AJOUT | 0 |
| `normalizedRWindowEnergy_bound_of_power_bound` | Si sur les indices de poids non nul abs(R(j+1)) ≤ M·exp(βU), alors l'énergie normalisée est au plus M²·exp((2β−1)U) (U ≥ 0, M ≥ 0, r ≥ 1). | CONFIRMÉE (domaine : borne ponctuelle puissance sur R aux indices de poids non nul, r ≥ 1, M ≥ 0, U ≥ 0) | AJOUT | 0 |
| `sq_add_le_two_mul_add_two_mul` | (a+b)² ≤ 2a² + 2b² pour tous réels a, b. | CONFIRMÉE | AJOUT | 6 |
| `normalizedCorrectedSampleEnergy_le` | Pour r ≥ 1, l'énergie normalisée de l'échantillon corrigé est au plus 2·(énergie de fenêtre R) + 2·(énergie de correction de Chebyshev). | CONFIRMÉE (domaine : r ≥ 1) | AJOUT | 1 |
| `normalizedRWindowEnergy_le_corrected` | Pour r ≥ 1, l'énergie de fenêtre R normalisée est au plus 2·(énergie de l'échantillon corrigé) + 2·(énergie de correction). | CONFIRMÉE (domaine : r ≥ 1) | AJOUT | 0 |
| `normalizedRChebyshevCorrectionEnergy_le_core` | Pour r ≥ 1 et tout réel U, l'énergie de correction de Chebyshev normalisée est au plus exp(−U)(2+U)². | CONFIRMÉE (domaine : r ≥ 1) | AJOUT | 2 |
| `normalizedRChebyshevCorrectionEnergy_le` | Pour r ≥ 1 et U ≥ log 2, l'énergie de correction de Chebyshev normalisée est au plus exp(−U)(2+U)². | CONFIRMÉE (domaine : r ≥ 1, U ≥ log 2) | AJOUT | 0 |
| `normalizedRChebyshevCorrectionEnergy_subexponential` | Pour r ≥ 1, l'énergie de correction de Chebyshev normalisée est sous-exponentielle en U. | CONFIRMÉE (domaine : r ≥ 1) | AJOUT | 1 |
| `normalizedRWindowEnergy_eq_sum_grammar_pair_classes` | Pour r ≥ 1, la somme sur les classes de paires de grammaire de l'énergie normalisée par classe égale l'énergie de fenêtre R normalisée. | CONFIRMÉE (domaine : r ≥ 1) | AJOUT | 1 |
| `zeroReconstructedNormalizedGrammarClassEnergy_eq_normalizedGrammarClassEnergy` | L'énergie par classe de paires de grammaire normalisée, reconstruite depuis les zéros, égale l'énergie canonique par classe. | CONFIRMÉE | V48 | 1 |
| `zero_reconstructed_normalized_R_window_energy_grammar_partition_eq` | Pour r ≥ 1, la somme sur les classes de l'énergie par classe reconstruite depuis les zéros égale l'énergie de fenêtre R normalisée. | CONFIRMÉE (domaine : r ≥ 1) | V48 | 1 |

### `RhGapCriterion.Round25G2CVTkernelGramRepresentation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `fullATCumulative_at_prime_eq_R` | Pour tout m, fullATCumulative au réel p_m égale R m. | CONFIRMÉE | AJOUT | 4 |
| `correctedTAtPrime_eq_R_add_RChebyshevCorrection` | Pour m ≥ 1, le signal T corrigé au m-ième premier égale R m plus RChebyshevCorrection m. | CONFIRMÉE (domaine : 1 ≤ m) | AJOUT | 5 |
| `RChebyshevCorrection_abs_le_log` | abs(RChebyshevCorrection m) ≤ 2 + log p_m. | CONFIRMÉE | AJOUT | 1 |
| `gramWeight_nonneg` | gramWeight X j est positif ou nul. | CONFIRMÉE | AJOUT | 6 |
| `gramWeight_sum_Ico` | Pour k ≤ N, la somme des gramWeight X j sur [k,N) vaut min(p_{N+1}, X) − min(p_{k+1}, X). | CONFIRMÉE (domaine : k ≤ N) | AJOUT | 4 |
| `gramIndicator_mul` | Le produit de deux indicateurs de Gram gramIndicator m j · gramIndicator n j égale gramIndicator (max m n) j. | CONFIRMÉE | AJOUT | 1 |
| `sub_min_eq_max_zero_sub` | X − min(t, X) = max(0, X − t) pour tous réels. | CONFIRMÉE | AJOUT | 2 |
| `energyKernelG_eq_gram_sum` | Pour m, n < N et X ≤ p_{N+1}, energyKernelG X (p_{m+1}) (p_{n+1}) est la somme sur j < N de gramWeight X j · gramIndicator m j · gramIndicator n j. | CONFIRMÉE (domaine : m, n < N et X ≤ p_{N+1}) | AJOUT | 1 |
| `gram_double_sum_eq_weighted_sum_sq` | Identité générique de Gram : la double somme Σ z_m z_n Σ_j w_j ψ_m(j) ψ_n(j) égale Σ_j w_j (Σ_m z_m ψ_m(j))². | CONFIRMÉE | AJOUT | 2 |
| `energyTerm_eq_mul_energyKernelG` | energyTerm a X m n = a m · a n · energyKernelG X (p_{m+1}) (p_{n+1}). | CONFIRMÉE | AJOUT | 1 |
| `partial_cumulative_sum_eq` | Pour j < N, la somme sur m < N de a_m·gramIndicator m j égale la somme partielle cumulée des a_m pour m ≤ j. | CONFIRMÉE (domaine : j < N) | AJOUT | 1 |
| `VTkernel_eq_sum_weighted_cumulative_sq` | Si X ≤ p_{N+1}, VTkernel a X N est la somme pondérée par gramWeight des carrés des sommes cumulées partielles de a. | CONFIRMÉE (domaine : X ≤ p_{N+1}) | AJOUT | 2 |
| `VTkernel_aT_eq_sum_weighted_R_sq` | Si X ≤ p_{N+1}, VTkernel aT X N est la somme sur j < N de gramWeight X j · R(j+1)². | CONFIRMÉE (domaine : X ≤ p_{N+1}) | AJOUT | 5 |

### `RhGapCriterion.Round25M50TerminalMellinEnergy`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `chebyshevθ_eq_theta_nat` | chebyshevθ n coïncide avec la fonction θ de Chebyshev de Mathlib en n entier. | CONFIRMÉE | AJOUT | 1 |
| `chebyshevθ_floor_eq_theta` | Pour tout réel x, chebyshevθ ⌊x⌋ = θ(x) (Mathlib). | CONFIRMÉE | AJOUT | 5 |
| `thetaErrorReal_eq` | thetaErrorReal x = x − θ(x). | CONFIRMÉE | AJOUT | 7 |
| `terminal_theta_mellin_energy_identified` | Énoncé trivial True (marqueur documentaire sans contenu mathématique de clôture). | CONFIRMÉE | AJOUT | 0 |
| `mellin_window_lower_eq_M49` | Pour tout U, exp U = exp(U + log 2)/2 (borne basse de la fenêtre [e^U, 2e^U] identique à la fenêtre M.49 avec r = 2). | CONFIRMÉE | AJOUT | 1 |
| `mellin_window_upper_eq_M49` | Pour tout U, 2·exp U = exp(U + log 2). | CONFIRMÉE | AJOUT | 4 |
| `bounded_measurable_sq_div_sq_intervalIntegrable` | Si f est mesurable et bornée par M sur [a,b] avec 0 < a ≤ b, alors f(t)²/t² est intégrable sur l'intervalle [a,b]. | CONFIRMÉE (domaine : 0 < a ≤ b, f mesurable, f bornée par M sur [a,b]) | AJOUT | 7 |
| `sq_div_sq_integral_nonneg` | Si a ≤ b et f²/t² est intégrable sur [a,b], son intégrale est positive ou nulle. | CONFIRMÉE (domaine : a ≤ b, f²/t² intégrable) | AJOUT | 3 |
| `thetaErrorReal_measurable` | thetaErrorReal est mesurable. | CONFIRMÉE | AJOUT | 5 |
| `thetaErrorReal_bound_on_window` | Pour U ≥ 0 et t dans [e^U, 2e^U], abs(x−θ(t)) ≤ 2·log 4·e^U. | CONFIRMÉE (domaine : U ≥ 0) | AJOUT | 5 |
| `thetaErrorReal_intervalIntegrable` | Pour U ≥ 0, thetaErrorReal²/t² est intégrable sur [e^U, 2e^U]. | CONFIRMÉE (domaine : U ≥ 0) | AJOUT | 9 |
| `thetaMellinLocalEnergy_nonneg` | Pour U ≥ 0, l'énergie locale de Mellin de θ est positive ou nulle. | CONFIRMÉE (domaine : U ≥ 0) | AJOUT | 1 |
| `psiErrorReal_measurable` | psiErrorReal est mesurable. | CONFIRMÉE | AJOUT | 7 |
| `psiErrorReal_bound_on_window` | Pour U ≥ 0 et t dans [e^U, 2e^U], abs(psiErrorReal t) ≤ 2(log 4 + 4)e^U. | CONFIRMÉE (domaine : U ≥ 0) | AJOUT | 6 |
| `psiErrorReal_intervalIntegrable` | Pour U ≥ 0, psiErrorReal²/t² est intégrable sur [e^U, 2e^U]. | CONFIRMÉE (domaine : U ≥ 0) | AJOUT | 2 |
| `psiMellinLocalEnergy_nonneg` | Pour U ≥ 0, l'énergie locale de Mellin de ψ est positive ou nulle. | CONFIRMÉE (domaine : U ≥ 0) | AJOUT | 2 |
| `thetaPsiPrimePowerCorrection_eq_sub` | La correction θ-ψ des puissances de premiers vaut thetaErrorReal x − psiErrorReal x. | CONFIRMÉE | AJOUT | 3 |
| `thetaPsiPrimePowerCorrection_nonneg` | La correction θ-ψ des puissances de premiers est positive ou nulle. | CONFIRMÉE | AJOUT | 3 |
| `thetaPsiPrimePowerCorrection_le_sqrt_mul_log` | Pour x ≥ 1, la correction θ-ψ est au plus 2·√x·log x. | CONFIRMÉE (domaine : 1 ≤ x) | AJOUT | 3 |
| `thetaPsiPrimePowerCorrection_measurable` | La correction θ-ψ est mesurable. | CONFIRMÉE | AJOUT | 4 |
| `thetaPsiPrimePowerCorrection_bound_on_window` | Pour U ≥ 0 et t dans [e^U, 2e^U], la correction θ-ψ est bornée par (4 log 4 + 8)e^U. | CONFIRMÉE (domaine : U ≥ 0) | AJOUT | 1 |
| `thetaPsiPrimePowerCorrection_intervalIntegrable` | Pour U ≥ 0, correction²/t² est intégrable sur [e^U, 2e^U]. | CONFIRMÉE (domaine : U ≥ 0) | AJOUT | 2 |
| `thetaPsiPrimePowerCorrection_local_energy_polynomial` | Pour U ≥ 0, l'intégrale de correction²/t² sur [e^U, 2e^U] est au plus 4 log2 (1+log2)² (1+U)². | CONFIRMÉE (domaine : U ≥ 0) | AJOUT | 1 |
| `thetaPsiCorrectionMellinLocalEnergy_polynomialGrowth` | L'énergie locale de Mellin de la correction θ-ψ est à croissance polynomiale de degré 2. | CONFIRMÉE | AJOUT | 1 |
| `psiErrorReal_sq_le_two_add` | Pour tout t, psiErrorReal(t)² ≤ 2·thetaErrorReal(t)² + 2·correction(t)². | CONFIRMÉE | AJOUT | 1 |
| `psiMellinLocalEnergy_le_two_add_correction` | Pour U ≥ 0, l'énergie locale de Mellin de ψ est au plus 2·(énergie de θ) + 2·(énergie de correction). | CONFIRMÉE (domaine : U ≥ 0) | AJOUT | 1 |
| `theta_energy_subexponential_implies_psi_energy_subexponential` | Si l'énergie locale de Mellin de θ est sous-exponentielle, celle de ψ l'est aussi. | CONFIRMÉE SOUS CONDITION (énergie de Mellin de θ sous-exponentielle) | AJOUT | 1 |

### `RhGapCriterion.Round25M52MellinBlocks`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `mellinDyadicU_nonneg` | mellinDyadicU n est positif ou nul pour tout n. | CONFIRMÉE | AJOUT | 7 |
| `exp_mellinDyadicU` | Pour tout n, exp(mellinDyadicU n) = 2^n. | CONFIRMÉE | AJOUT | 3 |
| `intervalIntegral_mul_le_sqrt_mul_sqrt` | Cauchy-Schwarz élémentaire d'intégrales de segment : ∫fg ≤ √∫f² √∫g² sur [a,b] avec f², g², fg intégrables et ∫g² > 0. | CONFIRMÉE (domaine : a ≤ b, f², g², fg intégrables, ∫g² > 0) | AJOUT | 2 |
| `sqrt_exp` | √(exp t) = exp(t/2). | CONFIRMÉE | AJOUT | 3 |
| `integral_rpow_neg_two_sigma_le` | Pour a > 0 et σ > 0, ∫ de x^(−2σ) sur [a,2a] est au plus a^(1−2σ). | CONFIRMÉE (domaine : a > 0, σ > 0) | AJOUT | 2 |
| `bounded_measurable_intervalIntegrable` | Une fonction mesurable bornée par M sur [a,b] (a ≤ b) est intégrable sur [a,b]. | CONFIRMÉE (domaine : a ≤ b, mesurable, bornée sur [a,b]) | AJOUT | 2 |
| `norm_cpow_neg_s_sub_one` | Pour t réel strictement positif et s complexe, ‖t^(−s−1)‖ = t^(−Re s − 1). | CONFIRMÉE (domaine : t > 0) | AJOUT | 12 |
| `norm_psiMellinBlock_le` | Pour Re s > 1/2, la norme du bloc de Mellin dyadique psiMellinBlock n s est au plus √(énergie locale de ψ en U_n)·√(e^{U_n})^(1−2Re s). | CONFIRMÉE (domaine : Re s supérieure à 1/2) | AJOUT | 2 |
| `psiErrorMellin_summable` | Si l'énergie locale de Mellin de ψ est sous-exponentielle, alors pour Re s > 1/2 la série des blocs de Mellin dyadiques est sommable. | CONFIRMÉE SOUS CONDITION (énergie de Mellin de ψ sous-exponentielle, Re s supérieure à 1/2) | AJOUT | 1 |

### `RhGapCriterion.Round25M52MellinHolomorphy`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `bounded_measurable_intervalIntegrable_complex` | Une fonction complexe mesurable bornée sur [a,b] (a ≤ b) est intégrable sur [a,b]. | CONFIRMÉE (domaine : a ≤ b, mesurable, bornée sur [a,b]) | AJOUT | 2 |
| `continuousOn_cpow_kernel` | Pour 0 < a ≤ b et s fixé, t ↦ t^(−s−1) est continue sur [a,b]. | CONFIRMÉE (domaine : 0 < a ≤ b) | AJOUT | 2 |
| `psiMellinBlock_integrand_intervalIntegrable` | L'intégrande du bloc de Mellin dyadique ψ(t)·t^(−s−1) est intégrable sur la fenêtre [e^{U_n}, 2e^{U_n}], pour tout s complexe. | CONFIRMÉE | AJOUT | 2 |
| `hasDerivAt_cpow_kernel` | Pour t > 0, la dérivée en s de t^(−s−1) est t^(−s−1)·log t·(−1). | CONFIRMÉE (domaine : t > 0) | AJOUT | 3 |
| `hasDerivAt_psiMellinBlock` | Le bloc de Mellin psiMellinBlock n est dérivable en tout x₀ complexe, de dérivée l'intégrale sur la fenêtre de ψ(t)·(−t^(−x₀−1) log t). | CONFIRMÉE | AJOUT | 1 |
| `differentiable_psiMellinBlock` | psiMellinBlock n est différentiable sur ℂ tout entier. | CONFIRMÉE | AJOUT | 1 |
| `norm_psiMellinBlock_le_uniform` | Si l'énergie de Mellin de ψ est sous-exponentielle, alors pour σK > 1/2 et ε admissible il existe C > 0 et r dans [0,1) tels que ‖psiMellinBlock n s‖ ≤ C r^n pour tout n et tout s avec Re s ≥ σK. | CONFIRMÉE SOUS CONDITION (énergie de Mellin de ψ sous-exponentielle, σK supérieur à 1/2, ε dans (0, 2σK−1)) | AJOUT | 1 |
| `differentiableOn_psiErrorMellin_of_ge` | Si l'énergie de Mellin de ψ est sous-exponentielle, la transformée psiErrorMellin est différentiable sur le demi-plan {Re s > σK} pour σK > 1/2. | CONFIRMÉE SOUS CONDITION (énergie de Mellin de ψ sous-exponentielle, σK supérieur à 1/2) | AJOUT | 1 |
| `psiErrorMellin_analyticOn_right_half_plane` | Si l'énergie de Mellin de ψ est sous-exponentielle, psiErrorMellin est analytique sur le demi-plan Re s > 1/2. | CONFIRMÉE SOUS CONDITION (énergie de Mellin de ψ sous-exponentielle) | AJOUT | 2 |

### `RhGapCriterion.Round25M52MellinZetaIdentity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `integral_Ioi_one_cpow_neg` | Pour Re s > 1, ∫_{1}^{∞} x^(−s) dx = 1/(s−1). | CONFIRMÉE (domaine : Re s supérieure à 1) | AJOUT | 2 |

### `RhGapCriterion.Round25M53MellinZetaIdentity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `mellinDyadicWindow_disjoint` | Pour n < m, les fenêtres dyadiques (2^n, 2^{n+1}] et (2^m, 2^{m+1}] sont disjointes. | CONFIRMÉE (domaine : n < m) | AJOUT | 1 |
| `mellinDyadicWindow_pairwise` | Les fenêtres dyadiques (2^n, 2^{n+1}] sont deux à deux disjointes (forme Pairwise). | CONFIRMÉE | AJOUT | 1 |
| `iUnion_mellinDyadicWindow_eq_Ioi_one` | L'union des fenêtres dyadiques (2^n, 2^{n+1}] pour n dans ℕ est exactement ]1, ∞[. | CONFIRMÉE | AJOUT | 2 |
| `psiMellinBlock_eq_setIntegral` | psiMellinBlock n s est l'intégrale d'ensemble de ψ(t)·t^(−s−1) sur (2^n, 2^{n+1}]. | CONFIRMÉE | AJOUT | 1 |
| `integral_norm_psiMellinBlock_le` | Pour Re s > 1/2, l'intégrale de la norme de l'intégrande sur la fenêtre dyadique est au plus √(énergie locale de ψ)·√(e^{U_n})^(1−2Re s). | CONFIRMÉE (domaine : Re s supérieure à 1/2) | AJOUT | 1 |
| `summable_integral_norm_psiMellinBlock` | Si l'énergie de Mellin de ψ est sous-exponentielle et Re s > 1/2, la suite des intégrales de normes sur les fenêtres dyadiques est sommable. | CONFIRMÉE SOUS CONDITION (énergie de Mellin de ψ sous-exponentielle, Re s supérieure à 1/2) | AJOUT | 1 |
| `psiErrorMellinIntegrand_integrableOn_window` | L'intégrande de Mellin de ψ est intégrable sur chaque fenêtre dyadique (2^n, 2^{n+1}], pour tout s. | CONFIRMÉE | AJOUT | 1 |
| `psiErrorMellinIntegrand_integrableOn_Ioi_one` | Si l'énergie de Mellin de ψ est sous-exponentielle et Re s > 1/2, l'intégrande ψ(x)·x^(−s−1) est intégrable sur ]1, ∞[. | CONFIRMÉE SOUS CONDITION (énergie de Mellin de ψ sous-exponentielle, Re s supérieure à 1/2) | AJOUT | 2 |
| `psiErrorMellin_eq_integral_Ioi` | Si l'énergie de Mellin de ψ est sous-exponentielle et Re s > 1/2, psiErrorMellin s égale l'intégrale impropre de ψ(x) x^(−s−1) sur ]1, ∞[. | CONFIRMÉE SOUS CONDITION (énergie de Mellin de ψ sous-exponentielle, Re s supérieure à 1/2) | AJOUT | 1 |
| `hasSum_indicator_vonMangoldt_eq_psi` | Pour x ≥ 0, la série des indicatrices de Λ(n) sur n ≤ x a pour somme ψ(x). | CONFIRMÉE (domaine : x ≥ 0) | AJOUT | 1 |
| `hasSum_vonMangoldtMellinTerm` | Pour x ≥ 0, la série des termes de Mellin de von Mangoldt a pour somme ψ(x)·x^(−s−1). | CONFIRMÉE (domaine : x ≥ 0) | AJOUT | 1 |
| `integral_Ioi_cpow_neg_s_sub_one` | Pour Re s > 0 et c > 0, ∫_c^∞ x^(−s−1) dx = c^(−s)/s. | CONFIRMÉE (domaine : Re s > 0, c > 0) | AJOUT | 3 |
| `integral_Ioi_rpow_neg_sigma_sub_one` | Pour σ > 0 et c > 0, ∫_c^∞ x^(−σ−1) dx = c^(−σ)/σ (analogue réel). | CONFIRMÉE (domaine : σ > 0, c > 0) | AJOUT | 2 |
| `vonMangoldtMellinTerm_integrableOn` | Pour Re s > 1, chaque terme de Mellin de von Mangoldt est intégrable sur ]1, ∞[. | CONFIRMÉE (domaine : Re s supérieure à 1) | AJOUT | 1 |
| `norm_vonMangoldtMellinTerm` | Pour x > 0, la norme du terme de Mellin de von Mangoldt vaut Λ(n) x^(−Re s − 1) si n ≤ x, 0 sinon. | CONFIRMÉE (domaine : x > 0) | AJOUT | 1 |
| `integral_vonMangoldtMellinTerm` | Pour Re s > 1, l'intégrale sur ]1, ∞[ du terme de Mellin d'indice n vaut le terme de la série L de Λ divisé par s. | CONFIRMÉE (domaine : Re s supérieure à 1) | AJOUT | 1 |
| `integral_norm_vonMangoldtMellinTerm` | Pour Re s > 1, l'intégrale de la norme du terme d'indice n sur ]1, ∞[ vaut Λ(n) max(n,1)^(−Re s)/Re s. | CONFIRMÉE (domaine : Re s supérieure à 1) | AJOUT | 1 |
| `summable_integral_norm_vonMangoldtMellinTerm` | Pour Re s > 1, la série des intégrales de normes des termes de Mellin de von Mangoldt sur ]1, ∞[ est sommable. | CONFIRMÉE (domaine : Re s supérieure à 1) | AJOUT | 1 |
| `integral_psi_Ioi_one_eq` | Pour Re s > 1, ∫_1^∞ ψ(x) x^(−s−1) dx = LSeries(Λ, s)/s. | CONFIRMÉE (domaine : Re s supérieure à 1) | AJOUT | 3 |
| `psiErrorMellin_eq_zeta_logDeriv` | Si l'énergie de Mellin de ψ est sous-exponentielle et Re s > 1, psiErrorMellin s = 1/(s−1) + (ζ'/ζ)(s)/s. | CONFIRMÉE SOUS CONDITION (énergie de Mellin de ψ sous-exponentielle, Re s supérieure à 1) | AJOUT | 2 |
| `differentiableAt_zetaPoleFactor` | zetaPoleFactor est différentiable en tout s ≠ 0. | CONFIRMÉE (domaine : s ≠ 0) | AJOUT | 1 |
| `differentiableOn_zetaPoleFactor_right_half_plane` | zetaPoleFactor est différentiable sur le demi-plan Re s > 1/2. | CONFIRMÉE | AJOUT | 1 |
| `analyticOnNhd_zetaPoleFactor_right_half_plane` | zetaPoleFactor est analytique sur le demi-plan Re s > 1/2. | CONFIRMÉE | AJOUT | 2 |
| `analyticOnNhd_mellinPoleRHS` | Si l'énergie de Mellin de ψ est sous-exponentielle, s ↦ (s·psiErrorMellin s − 1)·zetaPoleFactor s est analytique sur Re s > 1/2. | CONFIRMÉE SOUS CONDITION (énergie de Mellin de ψ sous-exponentielle) | AJOUT | 1 |
| `zetaPoleFactor_eq_sub_one_mul_zeta` | Pour s ∉ {0,1}, zetaPoleFactor s = (s−1)·ζ(s). | CONFIRMÉE (domaine : s différent de 0 et de 1) | AJOUT | 2 |
| `zetaPoleFactor_deriv_eq_mellin_mul_on_gt_one` | Si l'énergie de Mellin de ψ est sous-exponentielle et Re s > 1, deriv zetaPoleFactor s = (s·psiErrorMellin s − 1)·zetaPoleFactor s. | CONFIRMÉE SOUS CONDITION (énergie de Mellin de ψ sous-exponentielle, Re s supérieure à 1) | AJOUT | 1 |
| `zetaPoleFactor_deriv_eq_mellin_mul` | Même identité pour tout s avec Re s > 1/2 (prolongement analytique). | CONFIRMÉE SOUS CONDITION (énergie de Mellin de ψ sous-exponentielle, Re s supérieure à 1/2) | AJOUT | 1 |
| `riemannZeta_add_sub_one_mul_deriv_eq` | Si l'énergie de Mellin de ψ est sous-exponentielle, pour Re s > 1/2 et s ≠ 1 : ζ(s) + (s−1)ζ'(s) = (s·psiErrorMellin s − 1)·(s−1)ζ(s). | CONFIRMÉE SOUS CONDITION (énergie de Mellin de ψ sous-exponentielle, Re s supérieure à 1/2, s différent de 1) | AJOUT | 1 |
| `psi_mellin_subexponential_excludes_right_nontrivial_zeros` | Si l'énergie de Mellin de ψ est sous-exponentielle, tout zéro non trivial ρ de ζ vérifie Re ρ ≤ 1/2. | IMPLIQUE RH SOUS PRÉMISSE (énergie locale de Mellin de ψ sous-exponentielle ; demi-RH Re ρ ≤ 1/2, RH complète par la symétrie ρ ↦ 1−ρ) | AJOUT | 1 |
| `theta_mellin_subexponential_excludes_right_nontrivial_zeros` | Si l'énergie de Mellin de θ est sous-exponentielle, tout zéro non trivial ρ de ζ vérifie Re ρ ≤ 1/2. | IMPLIQUE RH SOUS PRÉMISSE (énergie locale de Mellin de θ sous-exponentielle ; demi-RH Re ρ ≤ 1/2, RH complète par la symétrie ρ ↦ 1−ρ) | AJOUT | 1 |

### `RhGapCriterion.Round26ACorrectedBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `min_sub_min_two_scale` | Pour a ≤ b et X1 ≤ X2, la différence de deux rampes tronquées imbriquées vaut max(0, min(b,X2) − max(a,X1)). | CONFIRMÉE (domaine : a ≤ b, X1 ≤ X2) | AJOUT | 1 |
| `gramWindowWeight_two_shift_eq_prime_gap_window_length` | gramWindowWeight 2 (U + log 2) j = max(0, min(p_{j+2}, 2e^U) − max(p_{j+1}, e^U)), longueur de [p_{j+1}, p_{j+2}] ∩ [e^U, 2e^U]. | CONFIRMÉE | AJOUT | 1 |
| `thetaErrorReal_sq_le_corrected_sq_add_aT_sq` | Pour k ≥ 1 et t dans [p_k, p_{k+1}) avec t < 2e^U, thetaErrorReal(t)² ≤ 2·correctedTAtPrime(k)² + 4·aT(k)² + 4(U + log 2)². | CONFIRMÉE (domaine : 1 ≤ k, p_k ≤ t < p_{k+1}, t < 2e^U) | AJOUT | 1 |
| `normalizedATWindowEnergy_nonneg` | Pour r ≥ 1, l'énergie normalisée de la fenêtre aT est positive ou nulle. | CONFIRMÉE (domaine : r ≥ 1) | AJOUT | 0 |
| `max_min_clamp_diff` | Pour a1 ≤ a2 et X1 ≤ X2 : max(X1, min(a2,X2)) − max(X1, min(a1,X2)) = max(0, min(a2,X2) − max(a1,X1)). | CONFIRMÉE (domaine : a1 ≤ a2, X1 ≤ X2) | AJOUT | 3 |
| `clamp_diff_pos_bounds` | Si le plafonnement de a2 dépasse strictement celui de a1 dans [X1,X2], alors a1 ≤ clamp(a1) et clamp(a2) ≤ a2. | CONFIRMÉE (domaine : a1 ≤ a2, X1 ≤ X2, plafonnement de a2 strictement supérieur à celui de a1) | AJOUT | 4 |
| `windowBreak_diff_eq_gramWindowWeight` | La différence de deux points de rupture de fenêtre consécutifs vaut gramWindowWeight 2 (U + log 2) i. | CONFIRMÉE | AJOUT | 2 |
| `windowBreak_step_nonneg` | Les points de rupture de fenêtre sont croissants au sens large : windowBreak U i ≤ windowBreak U (i+1). | CONFIRMÉE | AJOUT | 14 |
| `windowBreak_zero_eq` | Pour U ≥ log 3, le premier point de rupture windowBreak U 0 égale e^U. | CONFIRMÉE (domaine : U ≥ log 3) | AJOUT | 6 |
| `windowBreak_horizon_eq` | Au rang de l'horizon canonique de U + log 2, le point de rupture égale 2e^U. | CONFIRMÉE | AJOUT | 9 |
| `windowBreak_ge` | Tout point de rupture de fenêtre est au moins e^U. | CONFIRMÉE | AJOUT | 21 |
| `windowBreak_le_two` | Tout point de rupture de fenêtre est au plus 2e^U. | CONFIRMÉE | AJOUT | 14 |
| `windowBreak_intervalIntegrable` | La densité d'énergie de Mellin de θ est intégrable sur chaque morceau entre deux points de rupture consécutifs. | CONFIRMÉE | AJOUT | 2 |
| `windowPiece_energy_le` | Sur chaque morceau de fenêtre, l'énergie de θ est au plus gramWindowWeight·(2 correctedTAtPrime(i+1)² + 4 aT(i+1)² + 4(U+log 2)²)/e^{2U}. | CONFIRMÉE | AJOUT | 1 |
| `thetaMellinLocalEnergy_le_M49_discrete_energy` | Pour U ≥ log 3, l'énergie locale de Mellin de θ est au plus 8·énergie de l'échantillon corrigé normalisée + 16·énergie normalisée de la fenêtre aT + 8(U+log 2)² e^(−U). | CONFIRMÉE (domaine : U ≥ log 3) | AJOUT | 1 |
| `subexponential_of_le_sum_subexponential` | Si F ≤ c1 G1 + c2 G2 + c3 G3 + c4 G4 pour u ≥ 0 (ci > 0) et les Gi sont sous-exponentielles, alors F est sous-exponentielle. | CONFIRMÉE SOUS CONDITION (majoration ponctuelle par quatre fonctions sous-exponentielles à coefficients positifs) | AJOUT | 0 |
| `thetaMellinLocalEnergy_le_crude` | Pour U ≥ 0, l'énergie locale de Mellin de θ est au plus (1 + log 4)²·e^U. | CONFIRMÉE (domaine : U ≥ 0) | AJOUT | 1 |
| `log_two_le_one` | log 2 ≤ 1. | CONFIRMÉE | AJOUT | 1 |
| `shiftedLogSq_mul_expNeg_subexponential` | La fonction U ↦ (U + log 2)²·e^(−U) est sous-exponentielle. | CONFIRMÉE | AJOUT | 1 |
| `R_and_aT_window_subexponential_implies_theta_mellin` | Si l'énergie normalisée de la fenêtre R (r = 2, argument U + log 2) et celle de la fenêtre aT sont sous-exponentielles, alors l'énergie locale de Mellin de θ est sous-exponentielle. | CONFIRMÉE SOUS CONDITION (énergies normalisées des fenêtres R et aT sous-exponentielles) | AJOUT | 1 |

### `RhGapCriterion.Round26ADiscreteMellinBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `thetaErrorReal_between_primes` | Pour m ≥ 1 et p_m ≤ t < p_{m+1}, thetaErrorReal t = (t − p_m) + correctedTAtPrime m. | CONFIRMÉE (domaine : 1 ≤ m, p_m ≤ t < p_{m+1}) | AJOUT | 6 |
| `thetaErrorReal_at_prime` | Pour m ≥ 1, thetaErrorReal(p_m) = correctedTAtPrime m. | CONFIRMÉE (domaine : 1 ≤ m) | AJOUT | 1 |
| `gReal_eq` | Pour tout m, (g m : ℝ) = p_{m+1} − p_m. | CONFIRMÉE | AJOUT | 5 |
| `gReal_nonneg` | Pour tout m, 0 ≤ (g m : ℝ). | CONFIRMÉE | AJOUT | 4 |
| `thetaErrorReal_bound_on_prime_gap` | Pour m ≥ 1 et t dans [p_m, p_{m+1}], abs(thetaErrorReal t) ≤ g m + abs(correctedTAtPrime m) + abs(correctedTAtPrime (m+1)). | CONFIRMÉE (domaine : 1 ≤ m, t dans [p_m, p_{m+1}]) | AJOUT | 1 |
| `thetaErrorReal_measurable'` | thetaErrorReal est mesurable (doublon de thetaErrorReal_measurable). | CONFIRMÉE | AJOUT | 0 |
| `thetaLocalEnergy_prime_gap_intervalIntegrable` | Pour m ≥ 1, thetaErrorReal²/t² est intégrable sur [p_m, p_{m+1}]. | CONFIRMÉE (domaine : 1 ≤ m) | AJOUT | 5 |
| `thetaLocalEnergy_prime_gap_le` | Pour m ≥ 1, l'énergie locale de θ sur [p_m, p_{m+1}] est au plus (2 g_m² + 2 correctedTAtPrime(m)²)·g_m / p_m². | CONFIRMÉE (domaine : 1 ≤ m) | AJOUT | 1 |
| `thetaErrorReal_bound_global` | Pour t ≥ 0, abs(thetaErrorReal t) ≤ (1 + log 4)·t. | CONFIRMÉE (domaine : t ≥ 0) | AJOUT | 2 |
| `primeGapDiscreteEnergy_nonneg` | primeGapDiscreteEnergy U est positive ou nulle. | CONFIRMÉE | AJOUT | 0 |
| `thetaMellinLocalEnergy_le_canonical_discrete_energy` | Pour U ≥ log 3, l'énergie locale de Mellin de θ est au plus primeGapDiscreteEnergy U, somme discrète explicite sur les écarts de premiers. | CONFIRMÉE (domaine : U ≥ log 3) | AJOUT | 0 |

### `RhGapCriterion.Round26AGSignedCrossDecomposition`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `blockKernelWeight_eq_gramWeight_tail` | Pour k ≤ N et X ≤ p(N+1), le poids de noyau de bloc en k est la somme des poids de Gram sur les indices j de k à N-1. | CONFIRMÉE (domaine : k ≤ N et horizon N dominant la fenêtre X ≤ p(N+1)) | AJOUT | 0 |
| `energyTerm_symm` | Le terme d'énergie de paire canonique est symétrique en (m,n) pour toute suite a et tout X. | CONFIRMÉE | AJOUT | 1 |
| `VTkernel_eq_diagonal_add_signed_cross` | Pour toute suite a, le noyau double somme VTkernel vaut la masse diagonale pondérée par les poids de queue plus deux fois la fonctionnelle croisée ordonnée signée. | CONFIRMÉE | AJOUT | 1 |
| `VTkernel_aT_eq_diagonal_add_signed_correlation` | Pour la suite aT, VTkernel se scinde en masse diagonale pondérée plus deux fois la corrélation signée accroissement-primitive (aT n * R n). | CONFIRMÉE | AJOUT | 3 |
| `gram_weighted_R_sq_eq_diagonal_add_signed_correlation` | Pour X ≤ p(N+1), l'énergie de Gram pondérée de la primitive R vaut la masse diagonale des accroissements plus deux fois la corrélation signée. | CONFIRMÉE (domaine : horizon X ≤ p(N+1)) | AJOUT | 1 |
| `rawRWindowEnergy_eq_diagonal_add_signed_correlation` | L'énergie brute de fenêtre rawRWindowEnergy se scinde exactement en diagonale plus deux fois la corrélation signée, avec les poids de queue soustraits indice par indice entre exp U et exp U / r. | CONFIRMÉE | AJOUT | 0 |
| `signed_correlation_ge_neg_half_diagonal` | Pour X ≤ p(N+1), la corrélation signée pondérée est minorée par moins la moitié de la masse diagonale pondérée des accroissements. | CONFIRMÉE (domaine : horizon X ≤ p(N+1)) | AJOUT | 0 |
| `zero_reconstructed_signed_correlation_eq` | La corrélation signée construite depuis la paire (position, écart) reconstruite depuis les zéros égale la corrélation signée canonique aT·R, pour tout X et N. | CONFIRMÉE | V49,V60 | 1 |
| `zero_reconstructed_diagonal_increment_mass_eq` | La masse diagonale des accroissements calculée sur la réalisation reconstruite depuis les zéros égale la masse diagonale canonique terme à terme. | CONFIRMÉE | V49,V60 | 1 |
| `gram_weighted_R_sq_eq_zero_reconstructed_diagonal_add_signed_correlation` | Pour X ≤ p(N+1), l'énergie de Gram pondérée de R égale la diagonale plus deux fois la corrélation signée, lues sur la réalisation reconstruite depuis les zéros. | CONFIRMÉE (domaine : horizon X ≤ p(N+1)) | V49,V60 | 0 |

### `RhGapCriterion.Round26AKPrimeForcedRatioRecurrence`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `reflectedPairRatio_exponent_eq_ofReal` | Pour tout zéro non trivial ρ, (1 - conj ρ) - ρ égale le complexe réel 1 - 2 Re ρ. | CONFIRMÉE | V63,V65 | 2 |
| `reflectedPairRatio_scale_rpow` | Pour lam, x > 0, le rapport de la paire réfléchie en lam·x vaut lam^(1 - 2 Re ρ) fois sa valeur en x (facteur réel sans phase). | CONFIRMÉE (domaine : 0<lam et 0<x) | V102 | 1 |
| `reflectedPairRatio_eq_rpow_mul_one` | Pour x > 0, le rapport réfléchi en x vaut x^(1 - 2 Re ρ) fois sa valeur en 1. | CONFIRMÉE (domaine : 0<x) | V102 | 1 |
| `rpow_eq_rpow_of_ne_forces_exponent_zero` | Pour x, y > 0 distincts, x^e = y^e force e = 0. | CONFIRMÉE (domaine : x, y > 0 et distincts) | AJOUT | 1 |
| `reflectedPairRatio_eq_at_distinct_positive_scales_forces_critical_line` | Si le rapport réfléchi d'un zéro non trivial prend la même valeur à deux échelles positives distinctes, alors Re ρ = 1/2. | CONFIRMÉE (domaine : deux échelles positives distinctes et égalité du rapport réfléchi aux deux) | V102 | 3 |
| `reflectedPairRatio_eq_one_of_critical_line` | Si Re ρ = 1/2, le rapport réfléchi vaut 1 à toute échelle x > 0. | CONFIRMÉE (domaine : Re ρ = 1/2 et x>0) | V102,V161 | 3 |
| `reflectedPairRatio_eq_at_distinct_positive_scales_iff_critical_line` | Pour deux échelles positives distinctes fixées, l'égalité du rapport réfléchi aux deux échelles équivaut à Re ρ = 1/2. | CONFIRMÉE (domaine : deux échelles positives distinctes fixées) | V102 | 3 |
| `reflectedPairRatio_eq_at_distinct_primes_forces_critical_line` | Si le rapport réfléchi de ρ prend la même valeur aux deux premiers p m et p n distincts, alors Re ρ = 1/2. | CONFIRMÉE (domaine : indices m ≠ n et égalité du rapport aux deux premiers) | V102 | 2 |
| `two_scale_ratio_relation_depends_only_on_re` | Deux zéros non triviaux de même partie réelle satisfont la relation d'égalité à deux échelles pour exactement les mêmes couples d'échelles positives distinctes. | CONFIRMÉE (domaine : même Re et échelles positives distinctes) | AJOUT | 1 |
| `two_scale_ratio_relation_height_and_multiplicity_blind` | Même avec hauteurs et multiplicités distinctes, deux zéros de même Re ont la même valeur de vérité pour la relation à deux échelles. | CONFIRMÉE (domaine : même Re, hauteurs distinctes, multiplicités distinctes, échelles positives distinctes) | AJOUT | 0 |
| `two_scale_ratio_relation_scale_arithmetic_blind` | Pour un zéro fixé, la relation à deux échelles a même valeur de vérité sur un couple de premiers distincts et sur un couple quelconque d'échelles positives distinctes. | CONFIRMÉE (domaine : indices premiers distincts et échelles positives distinctes) | AJOUT | 0 |
| `critical_line_of_primeForcedTwoScaleRatioRecurrence` | Le verrou PrimeForcedTwoScaleRatioRecurrence entraîne que tout zéro non trivial est sur la ligne Re = 1/2. | IMPLIQUE RH SOUS PRÉMISSE (verrou PrimeForcedTwoScaleRatioRecurrence, équivalent à RH) | V110 | 1 |
| `riemann_hypothesis_of_primeForcedTwoScaleRatioRecurrence` | Le verrou PrimeForcedTwoScaleRatioRecurrence entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE (verrou PrimeForcedTwoScaleRatioRecurrence, équivalent à RH) | V116 | 1 |
| `riemann_hypothesis_of_primeScaleForcedRatioRecurrence` | Le verrou PrimeScaleForcedRatioRecurrence (forme aux échelles premières) entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE (verrou PrimeScaleForcedRatioRecurrence, équivalent à RH) | V116 | 1 |
| `primeForcedTwoScaleRatioRecurrence_iff_riemannHypothesis` | Le verrou PrimeForcedTwoScaleRatioRecurrence équivaut à RiemannHypothesis. | ÉQUIVALENTE À RH | V116 | 2 |
| `primeScaleForcedRatioRecurrence_iff_riemannHypothesis` | Le verrou PrimeScaleForcedRatioRecurrence équivaut à RiemannHypothesis. | ÉQUIVALENTE À RH | V116 | 2 |
| `primeScaleForcedRatioRecurrence_iff_primeForcedTwoScaleRatioRecurrence` | Les deux formes du verrou (échelles premières et deux échelles positives) sont équivalentes entre elles, toutes deux étant équivalentes à RH dans le même lot. | ÉQUIVALENTE À RH | AJOUT | 0 |
| `two_scale_ratio_relation_reflection_blind` | La relation d'égalité du rapport réfléchi à deux échelles a même valeur de vérité pour ρ et pour reflectConjZero ρ. | CONFIRMÉE (domaine : échelles positives distinctes) | V63,V180 | 0 |
| `primeForcedTwoScaleRatioRecurrence_of_scale_four_subexponential` | Si l'énergie de Mellin thetaScaleFourMellinEnergy est sous-exponentielle, alors le verrou PrimeForcedTwoScaleRatioRecurrence tient. | IMPLIQUE RH SOUS PRÉMISSE (sous-exponentialité de thetaScaleFourMellinEnergy) | AJOUT | 0 |
| `primeScaleForcedRatioRecurrence_of_scale_four_subexponential` | Si l'énergie de Mellin thetaScaleFourMellinEnergy est sous-exponentielle, alors le verrou PrimeScaleForcedRatioRecurrence tient. | IMPLIQUE RH SOUS PRÉMISSE (sous-exponentialité de thetaScaleFourMellinEnergy) | AJOUT | 0 |

### `RhGapCriterion.Round26ALSpineRestGrowthReduction`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `rescaledZeroSideChannel_eq_left_add_right_add_rest` | Pour un zéro hors ligne ρ et U > 0, le canal côté zéros réétalonné égale le mode de ρ plus le mode de son miroir reflectConjZero ρ plus le reste réfléchi réétalonné. | CONFIRMÉE SOUS CONDITION (U>0 et ρ hors ligne) | V63,V121 | 2 |
| `norm_left_mode` | La norme du mode d'un zéro ρ vaut la norme de son amplitude hors ligne fois exp((Re ρ - 1/2)U). | CONFIRMÉE | V102 | 0 |
| `norm_right_mode_le` | Pour U ≥ 0 et Re ρ > 1/2, la norme du mode du miroir reflectConjZero ρ est bornée par la norme de son amplitude. | CONFIRMÉE SOUS CONDITION (U ≥ 0 et Re ρ > 1/2) | V102 | 2 |
| `offline_forces_total_plus_rest_exponential_lower_bound` | Pour Re ρ > 1/2 et U > 0, ‖A ρ‖·exp((Re ρ - 1/2)U) - ‖A(miroir)‖ est minoré par la somme des normes du canal total réétalonné et du reste réfléchi réétalonné. | CONFIRMÉE SOUS CONDITION (Re ρ > 1/2 et U>0) | V102,V124 | 0 |
| `offline_reflected_pair_forces_rest_exponential_growth` | Si Re ρ > 1/2 et le canal côté zéros est sous-exponentiel, alors le reste réfléchi croît exponentiellement au taux Re ρ - 1/2. | CONFIRMÉE SOUS CONDITION (Re ρ > 1/2 et sous-exponentialité du canal côté zéros) | V124 | 1 |
| `no_offline_zero_of_channel_and_rest_subexponential` | Si le canal total et le reste réfléchi sont sous-exponentiels, aucun zéro non trivial n'a Re ρ > 1/2. | RÉFUTATION COMPILÉE (existence d'un zéro avec Re ρ > 1/2, sous les deux sous-exponentialités) | V110 | 1 |
| `re_le_half_of_channel_and_rest_subexponential` | Sous les deux sous-exponentialités, tout zéro non trivial vérifie Re ρ ≤ 1/2. | CONFIRMÉE SOUS CONDITION (canal total et reste réfléchi sous-exponentiels) | V110 | 1 |
| `critical_line_of_channel_and_rest_subexponential` | Sous les deux sous-exponentialités, tout zéro non trivial vérifie Re ρ = 1/2. | IMPLIQUE RH SOUS PRÉMISSE (canal total et reste réfléchi sous-exponentiels) | V110 | 1 |
| `riemannHypothesis_of_channel_and_rest_subexponential` | Le canal total côté zéros sous-exponentiel et le reste réfléchi sous-exponentiel entraînent RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE (canal total et reste réfléchi sous-exponentiels) | V116 | 0 |

### `RhGapCriterion.Round26AMPrimeScaleCharacterFaithfulness`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `nat_prime_log_relation_absurd` | Pour deux premiers distincts a et b et M > 0, la relation N·log b = M·log a est impossible (conclusion False). | RÉFUTATION COMPILÉE (relation entière N log b = M log a entre logarithmes de premiers distincts avec M>0) | AJOUT | 1 |
| `int_prime_log_relation_forces_zero` | Pour deux premiers distincts a et b, n·log b = m·log a avec n, m entiers force n = 0 et m = 0. | CONFIRMÉE (domaine : a et b premiers distincts) | AJOUT | 1 |
| `voiceScaleCharacter_two_prime_scales_injective` | Deux complexes ayant le même caractère d'échelle aux deux échelles log a et log b de deux premiers distincts sont égaux. | CONFIRMÉE (domaine : a et b premiers distincts, mêmes caractères aux deux échelles) | AJOUT | 4 |
| `generic_two_scales_do_not_separate_scale_characters` | Il existe deux complexes distincts et deux échelles positives distinctes où les deux caractères d'échelle coïncident. | CONFIRMÉE | AJOUT | 1 |
| `prime_hypothesis_is_load_bearing_in_two_scale_faithfulness` | Conjonction : l'injectivité aux deux échelles premières est vraie et l'énoncé analogue pour deux échelles positives distinctes quelconques est faux. | CONFIRMÉE | AJOUT | 0 |
| `real_exponent_scale_character_eq_forces_zero` | Pour t réel et L ≠ 0, exp(t·L) = 1 (complexe) force t = 0. | CONFIRMÉE (domaine : L ≠ 0) | AJOUT | 2 |
| `reflectedPair_single_scale_character_eq_forces_critical_line` | Si les caractères d'échelle de ρ et de son miroir coïncident à une échelle x > 0, x ≠ 1, alors Re ρ = 1/2. | CONFIRMÉE (domaine : échelle x>0, x≠1 où les caractères coïncident) | V102 | 4 |
| `reflectedPair_single_scale_character_eq_forces_reflect_fixed` | Si les caractères d'échelle de ρ et de son miroir coïncident à une échelle x > 0, x ≠ 1, alors reflectConjZero ρ = ρ. | CONFIRMÉE (domaine : échelle x>0, x≠1 où les caractères coïncident) | V161 | 1 |
| `reflectedPair_prime_hypothesis_not_needed` | Pour tout zéro ρ et toute échelle x > 0, x ≠ 1, la coïncidence des caractères d'échelle de ρ et de son miroir à log x force reflectConjZero ρ = ρ. | CONFIRMÉE (domaine : x>0, x≠1 où les caractères coïncident) | V161 | 0 |
| `critical_line_of_singlePrimeScaleCharacterCoincidence` | Le verrou SinglePrimeScaleCharacterCoincidence entraîne que tout zéro non trivial vérifie Re = 1/2. | IMPLIQUE RH SOUS PRÉMISSE (verrou SinglePrimeScaleCharacterCoincidence, équivalent à RH) | V110 | 1 |
| `riemannHypothesis_of_singlePrimeScaleCharacterCoincidence` | Le verrou SinglePrimeScaleCharacterCoincidence entraîne RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE (verrou SinglePrimeScaleCharacterCoincidence, équivalent à RH) | V116 | 1 |
| `singlePrimeScaleCharacterCoincidence_of_riemannHypothesis` | RiemannHypothesis entraîne le verrou SinglePrimeScaleCharacterCoincidence (caractères d'échelle de ρ et de son miroir coïncidents à l'échelle p 0 = 2). | CONFIRMÉE SOUS CONDITION (RH supposée en hypothèse) | V161 | 1 |
| `singlePrimeScaleCharacterCoincidence_iff_riemannHypothesis` | Le verrou SinglePrimeScaleCharacterCoincidence équivaut à RiemannHypothesis. | ÉQUIVALENTE À RH | V116 | 0 |

### `RhGapCriterion.Round26ANGrammarRigidityRestoration`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `GrammarRigid.state_binary` | Dans un bloc de grammaire rigide, tous les états d'indice ≤ k valent 1 ou 5. | CONFIRMÉE SOUS CONDITION (bloc de grammaire rigide) | V174 | 1 |
| `GrammarRigid.family_closure` | Dans un bloc rigide, chaque écart appartient à exactement une classe mod 6 parmi {0,2,4}. | CONFIRMÉE SOUS CONDITION (bloc de grammaire rigide) | V174 | 0 |
| `GrammarRigid.class_projection` | Dans un bloc rigide, la classe de l'écart mod 6 (0, 2, 4) équivaut à la transition d'états correspondante (inchangé, 5 vers 1, 1 vers 5). | CONFIRMÉE SOUS CONDITION (bloc de grammaire rigide) | V174 | 1 |
| `GrammarRigid.transition_edge` | Dans un bloc rigide, le champ transitions est exactement l'arête du graphe d'états {1,5} (tau11, tau15, tau51, tau55) entre états consécutifs. | CONFIRMÉE SOUS CONDITION (bloc de grammaire rigide) | V174 | 0 |
| `GrammarRigid.boundary_law` | Dans un bloc rigide, le déséquilibre entre familles 4 et 2 égale la différence des poids d'état de sortie et d'entrée (quantité de bord). | CONFIRMÉE SOUS CONDITION (bloc de grammaire rigide) | V174 | 0 |
| `prime_blockState_eq` | Pour i ≤ k, l'état i du bloc canonique premier est la classe mod 6 du premier p(n+i). | CONFIRMÉE (domaine : i ≤ k) | V174 | 4 |
| `prime_blockState_zero` | L'état initial du bloc canonique premier est le bord d'entrée blockEntryState n. | CONFIRMÉE | V174 | 1 |
| `prime_blockState_last` | L'état terminal du bloc canonique premier est le bord de sortie blockExitState n k. | CONFIRMÉE | V174 | 1 |
| `prime_blockFamilyCount_eq_changeCount` | Le comptage de famille c du bloc canonique premier égale le compteur changeCount c n k déjà défini sur le porteur réel. | CONFIRMÉE | V174 | 1 |
| `prime_completeGrammarBlock_rigid` | Pour n ≥ 2, le bloc de grammaire complet premier canonique est rigide. | CONFIRMÉE (domaine : n ≥ 2, domaine hors cas exceptionnels 2 et 3) | V174 | 4 |
| `zero_completeGrammarBlock_rigid` | Pour n ≥ 2, le bloc de grammaire complet reconstruit depuis les zéros est rigide. | CONFIRMÉE (domaine : n ≥ 2, domaine hors cas exceptionnels 2 et 3) | V48,V60,V174 | 1 |
| `grammarRigid_not_automatic` | Le bloc construit sur les fonctions nulles (compte, position, écart) n'est pas rigide, pour tout n. | RÉFUTATION COMPILÉE (rigidité automatique de completeGrammarBlockOf) | V174 | 0 |
| `zeroGrammar_family_eq_transitions` | Dans la grammaire de constellation zéro, le champ famille est égal au champ transitions. | CONFIRMÉE | V127 | 0 |
| `zeroMemberTransition_height_blind` | La transition zeroMemberTransition de deux membres ne dépend que de leur statut (sur la ligne ou non), pas de leurs hauteurs. | CONFIRMÉE (domaine : mêmes statuts critiques respectifs des deux couples de membres) | V159 | 1 |
| `GZ_transition_does_not_determine_internal_gap` | Il existe deux couples de membres de même transition zéro et d'écarts de hauteur internes différents. | CONFIRMÉE | V159 | 0 |
| `GZ_internal_gap_does_not_determine_transition` | Il existe deux couples de membres de même écart de hauteur interne et de transitions zéro différentes. | CONFIRMÉE | V159 | 0 |
| `offline_blindness_coexists_with_restored_rigidity` | Pour n ≥ 2 et un représentant positif ρ hors ligne de hauteur T, le bloc reconstruit depuis les zéros égale le bloc premier canonique et est rigide. | CONFIRMÉE SOUS CONDITION (n ≥ 2, ρ représentant positif hors ligne à la hauteur T) | V48,V159,V174 | 0 |

### `RhGapCriterion.Round26AORigidCoupledGrammar`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RigidPrimeGrammarBlock.mk.congr_simp` | Lemme de congruence auto-généré : deux RigidPrimeGrammarBlock construits sur des blocs égaux sont égaux. | CONFIRMÉE (domaine : égalité des blocs) | AJOUT | 0 |
| `RigidPrimeGrammarBlock.canonical` | Le bloc d'un RigidPrimeGrammarBlock est le bloc de grammaire complet canonique premier. | CONFIRMÉE | V48 | 5 |
| `RigidPrimeGrammarBlock.rigid` | Le bloc d'un RigidPrimeGrammarBlock est GrammarRigid. | CONFIRMÉE | V174 | 2 |
| `RigidPrimeGrammarBlock.has_rigidity` | Le bloc d'un RigidPrimeGrammarBlock est GrammarRigid (rigidité donnée intrinsèquement). | CONFIRMÉE | V174 | 1 |
| `RigidPrimeGrammarBlock.class_projection` | Dans un RigidPrimeGrammarBlock, la classe mod 6 de chaque écart équivaut à la transition d'états correspondante. | CONFIRMÉE | V174 | 1 |
| `RigidCoupledZeroPrimeGrammar.prime_start_ge_two` | Pour toute grammaire couplée zéro-premier rigide, l'indice de départ premier n vérifie 2 ≤ n. | CONFIRMÉE | AJOUT | 1 |
| `RigidCoupledZeroPrimeGrammar.source_encodes_prime` | La grammaire encodée depuis la source canonique de zéros sur (n,K) égale le bloc premier de la grammaire couplée. | CONFIRMÉE | V48,V60 | 1 |
| `RigidCoupledZeroPrimeGrammar.zeroRows_eq_canonical` | Les lignes zéro d'une grammaire couplée sont les représentants positifs ordonnés à la hauteur T. | CONFIRMÉE | V8,V64 | 1 |
| `RigidCoupledZeroPrimeGrammar.zeroHeights_from_rows` | Les hauteurs zéro de la grammaire couplée sont l'image des lignes zéro par zeroHeight. | CONFIRMÉE | AJOUT | 2 |
| `RigidCoupledZeroPrimeGrammar.zeroGaps_from_heights` | Les écarts zéro sont les différences de hauteurs consécutives (zipWith b - a sur la liste et sa queue). | CONFIRMÉE | AJOUT | 2 |
| `RigidCoupledZeroPrimeGrammar.zeroRows_ordered` | Les lignes zéro sont deux à deux ordonnées par partie imaginaire croissante, puis partie réelle croissante à égalité. | CONFIRMÉE | V8 | 0 |
| `RigidCoupledZeroPrimeGrammar.zeroGaps_nonneg` | Tout écart de hauteur zéro de la grammaire couplée est ≥ 0. | CONFIRMÉE (domaine : g appartient à la liste des écarts) | V8 | 0 |
| `RigidCoupledZeroPrimeGrammar.internalGapWithNext_exact` | L'écart interne au suivant de la ligne r égale orderedInternalGapWithNext T r. | CONFIRMÉE | AJOUT | 0 |
| `RigidCoupledZeroPrimeGrammar.internalGap_matches_zeroGaps` | Pour r dont l'indice est dans les écarts, l'écart interne de la ligne r vaut some de l'écart zéro correspondant. | CONFIRMÉE (domaine : indice r dans la longueur de zeroGaps) | AJOUT | 1 |
| `RigidCoupledZeroPrimeGrammar.primeGap_exact` | Les écarts premiers de la grammaire couplée sont les écarts du bloc premier. | CONFIRMÉE | V48 | 6 |
| `RigidCoupledZeroPrimeGrammar.primeTransition_exact` | Les transitions premières de la grammaire couplée sont celles du bloc premier. | CONFIRMÉE | V48 | 1 |
| `RigidCoupledZeroPrimeGrammar.primePattern_exact` | Le pattern premier de la grammaire couplée est celui du bloc premier. | CONFIRMÉE | V48 | 2 |
| `RigidCoupledZeroPrimeGrammar.primeFamily_exact` | La famille première de la grammaire couplée est celle du bloc premier. | CONFIRMÉE | V48 | 1 |
| `RigidCoupledZeroPrimeGrammar.tableEntry_exact` | Chaque case de la table zéro×colonne est la contribution zeroPrimeStepContribution de la ligne zéro correspondante à (n, c). | CONFIRMÉE | V127 | 2 |
| `RigidCoupledZeroPrimeGrammar.weightedEntry_exact` | Chaque case pondérée vaut le poids grammarWeight n c fois la case de la table. | CONFIRMÉE | AJOUT | 1 |
| `RigidCoupledZeroPrimeGrammar.totalColumnBridge` | La somme (tsum) sur tous les zéros non triviaux de leur contribution à la colonne c égale la différence lissée de sommes de Von Mangoldt moins fonds entre p(n+c+1) et p(n+c). | CONFIRMÉE | V121,V48 | 1 |
| `RigidCoupledZeroPrimeGrammar.prime_class_projection` | Dans la grammaire couplée, la classe mod 6 de chaque écart premier équivaut à la transition d'états correspondante. | CONFIRMÉE | V174 | 3 |
| `RigidCoupledZeroPrimeGrammar.primeGap_ne_zero` | Chaque écart premier de la grammaire couplée est non nul. | CONFIRMÉE | AJOUT | 4 |
| `RigidCoupledZeroPrimeGrammar.pattern_gap_eq` | Le gap du pattern premier stocké égale l'écart premier de même indice. | CONFIRMÉE | AJOUT | 1 |
| `RigidCoupledZeroPrimeGrammar.pattern_transition_eq` | La relation du pattern premier stocké égale la transition première de même indice. | CONFIRMÉE | AJOUT | 1 |
| `RigidCoupledZeroPrimeGrammar.family_eq_gap_class` | La famille première de chaque indice est la classe mod 6 de l'écart premier de même indice. | CONFIRMÉE | V174 | 1 |
| `RigidCoupledZeroPrimeGrammar.grammarWeight_eq_family_signed` | Le poids grammarWeight n i vaut 1 si l'écart est de classe 4 moins 1 si l'écart est de classe 2 (sinon 0). | CONFIRMÉE | V174 | 0 |
| `RigidCoupledZeroPrimeGrammar.weightedEntry_eq_grammarVoiceStep` | Chaque case pondérée de la table est la grammarVoiceStep de la ligne zéro correspondante à (n, c). | CONFIRMÉE | AJOUT | 1 |
| `RigidCoupledZeroPrimeGrammar.offline_forces_zero_gap` | S'il existe un représentant positif hors ligne à la hauteur T, alors la liste des écarts de hauteur zéro contient un écart nul. | CONFIRMÉE SOUS CONDITION (existence d'un représentant positif hors ligne à la hauteur T) | V66,V162 | 2 |
| `rigid_coupled_offline_snapshot` | Pour n ≥ 2 et un représentant positif hors ligne à la hauteur T, la grammaire couplée canonique contient à la fois un écart de hauteur nul, des écarts premiers tous non nuls et la loi classe mod 6 ↔ transition. | CONFIRMÉE SOUS CONDITION (n ≥ 2 et existence d'un représentant positif hors ligne à la hauteur T) | V162,V174,V159 | 0 |

### `RhGapCriterion.Round26APFullRigidCoupledGrammar`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `FullRigidCoupledZeroPrimeGrammar.transition_partition` | Sur chaque colonne, la transition première est exactement l'une des quatre transformations tau11, tau15, tau51, tau55 (existence et unicité). | CONFIRMÉE | V174 | 2 |
| `FullRigidCoupledZeroPrimeGrammar.meta_pattern_finite` | À chaque position du bloc, p(n+i) et p(n+i+1) sont congrus à 1 ou 5 mod 6, l'écart est de classe 0, 2 ou 4, et chaque classe équivaut à la transition d'états correspondante. | CONFIRMÉE | V174,V176 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.family_change_skeleton_alternates` | Entre deux écarts non nuls mod 6 séparés seulement par des écarts de classe 0, les classes valent (2 puis 4) ou (4 puis 2). | CONFIRMÉE (domaine : i<j, écarts d'indices i et j de classe non nulle, écarts intermédiaires de classe 0) | V174 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.block_occurrences_prime` | Toutes les positions du pattern premier de la grammaire couplée sont des nombres premiers. | CONFIRMÉE | V48 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.block_order_strict` | Les positions du pattern premier sont strictement croissantes avec l'indice de colonne. | CONFIRMÉE (domaine : i<j) | V48 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.adjacent_boundary` | L'état de sortie du bloc (n,K) égale l'état d'entrée du bloc suivant (n+K). | CONFIRMÉE | V174 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.family_boundary_law` | Le nombre de changements de classe 4 moins celui de classe 2 vaut la différence des poids d'état de sortie et d'entrée. | CONFIRMÉE | V174 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.family_imbalance_le_one` | Le déséquilibre absolu entre changements de classe 4 et de classe 2 est ≤ 1. | CONFIRMÉE | V174 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.rank_density_exact` | La densité de rang de la colonne i vaut n + i + 1. | CONFIRMÉE | V27 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.rank_density_strict` | La densité de rang est strictement croissante avec l'indice de colonne. | CONFIRMÉE (domaine : i<j) | V27 | 0 |
| `FullRigidCoupledZeroPrimeGrammar.theta_density_exact` | La densité θ de la colonne i est θm(n+i) canonique. | CONFIRMÉE | AJOUT | 1 |
| `FullRigidCoupledZeroPrimeGrammar.theta_density_step` | La densité θ de la colonne i+1 vaut celle de la colonne i plus le log de la position en i. | CONFIRMÉE (domaine : i+1<K) | AJOUT | 0 |
| `FullRigidCoupledZeroPrimeGrammar.transition_succession_exact` | La succession ordonnée des transitions du bloc premier est transitionSuccession p n K. | CONFIRMÉE | V176 | 0 |
| `FullRigidCoupledZeroPrimeGrammar.family_succession_exact` | La succession ordonnée des familles du bloc premier est familySuccession gnat n K. | CONFIRMÉE | V176 | 0 |
| `FullRigidCoupledZeroPrimeGrammar.pattern_succession_exact` | La succession de patterns de largeur w de la grammaire couplée est patternSuccession p gnat n K w. | CONFIRMÉE | V176 | 0 |
| `FullRigidCoupledZeroPrimeGrammar.reconstructed_transition_succession` | La succession de transitions calculée depuis les positions reconstruites depuis les zéros égale celle des vrais premiers. | CONFIRMÉE | V48,V60,V176 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.reconstructed_family_succession` | La succession de familles calculée depuis les écarts reconstruits depuis les zéros égale celle des vrais écarts premiers. | CONFIRMÉE | V48,V60,V176 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.reconstructed_pattern_succession` | La succession de patterns de largeur w calculée depuis les positions et écarts reconstruits égale celle des vrais premiers. | CONFIRMÉE | V48,V60,V176 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.pattern_occurrence_transport` | L'ensemble des occurrences d'une forme de pattern calculé depuis la reconstruction zéro égale celui des vrais premiers. | CONFIRMÉE | V48,V60,V176 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.family_occurrence_transport` | L'ensemble des occurrences d'une suite de familles calculé depuis les écarts reconstruits égale celui des vrais écarts. | CONFIRMÉE | V48,V60,V176 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.transition_occurrence_transport` | L'ensemble des occurrences d'une liste de transitions calculé depuis les positions reconstruites égale celui des vrais premiers. | CONFIRMÉE | V48,V60,V176 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.reconstructed_order` | Les positions reconstruites depuis les zéros sont p, strictement croissantes, et les écarts reconstruits sont gnat. | CONFIRMÉE | V48,V49 | 0 |
| `FullRigidCoupledZeroPrimeGrammar.reconstructed_density` | Le comptage, π, θ et ψ reconstruits depuis les zéros (ψ pour x ≥ 2) sont les canoniques. | CONFIRMÉE (domaine : 2 ≤ x pour la partie ψ) | V48,V121 | 0 |
| `FullRigidCoupledZeroPrimeGrammar.reconstructed_gap_innovation` | Pour tout m, écart reconstruit moins log de la position reconstruite égale gnat m moins log de p m. | CONFIRMÉE | V48 | 0 |
| `FullRigidCoupledZeroPrimeGrammar.reconstructed_modes` | Les modes T, B et O reconstruits depuis les zéros égalent les modes canoniques. | CONFIRMÉE | V48,V176 | 0 |
| `FullRigidCoupledZeroPrimeGrammar.universal_position_gap_transport` | Toute fonction F des positions et écarts vaut la même chose sur les données reconstruites depuis les zéros et sur les canoniques. | CONFIRMÉE | V48,V60,V159 | 0 |
| `FullRigidCoupledZeroPrimeGrammar.universal_count_position_gap_transport` | Toute fonction F du comptage, des positions et des écarts vaut la même chose sur les données reconstruites depuis les zéros et sur les canoniques. | CONFIRMÉE | V48,V60,V159 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.only_four_transitions` | Toute transition première de la grammaire couplée est l'une des quatre transformations tau11, tau15, tau51, tau55. | CONFIRMÉE | V174 | 2 |
| `FullRigidCoupledZeroPrimeGrammar.change_skeleton_alternates` | Entre deux écarts non nuls mod 6 séparés seulement par des écarts de classe 0, les classes valent (2 puis 4) ou (4 puis 2). | CONFIRMÉE (domaine : i<j, écarts d'indices i et j de classe non nulle, écarts intermédiaires de classe 0) | V174 | 0 |
| `FullRigidCoupledZeroPrimeGrammar.has_finite_metapattern` | À chaque position, p(n+i) et p(n+i+1) sont 1 ou 5 mod 6, l'écart est de classe 0, 2 ou 4, chaque classe équivalant à la transition correspondante. | CONFIRMÉE | V174,V176 | 1 |
| `FullRigidCoupledZeroPrimeGrammar.offline_forces_zero_gap` | S'il existe un représentant positif hors ligne à la hauteur T, la liste des écarts de hauteur zéro de la grammaire pleinement rigide contient un écart nul. | CONFIRMÉE SOUS CONDITION (existence d'un représentant positif hors ligne à la hauteur T) | V66,V162 | 3 |

### `RhGapCriterion.Round26AQTerminalRigidityClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `full_coupled_rigidity_exclusion_iff_offline_exclusion` | FullCoupledRigidityOfflineExclusion équivaut à l'exclusion, à toute hauteur T, de tout représentant positif de partie réelle différente de 1/2. | ÉQUIVALENTE À RH | V116,V117 | 0 |
| `all_positiveRepresentatives_on_critical_line_of_exclusion` | Sous FullCoupledRigidityOfflineExclusion, tout représentant positif à toute hauteur T est sur la ligne critique. | IMPLIQUE RH SOUS PRÉMISSE (FullCoupledRigidityOfflineExclusion, équivalente à l'exclusion hors ligne) | V110 | 1 |
| `all_constellation_gaps_strictly_positive_of_exclusion` | Sous FullCoupledRigidityOfflineExclusion, tout écart de hauteur d'une constellation positive est strictement positif. | CONFIRMÉE SOUS CONDITION (FullCoupledRigidityOfflineExclusion, équivalente à l'exclusion hors ligne) | V162,V188 | 0 |
| `riemann_hypothesis_of_full_coupled_rigidity_exclusion` | FullCoupledRigidityOfflineExclusion entraîne que tout zéro non trivial vérifie Re = 1/2. | IMPLIQUE RH SOUS PRÉMISSE (FullCoupledRigidityOfflineExclusion, équivalente à l'exclusion hors ligne) | V110,V116 | 1 |
| `all_height_constellations_preserve_height_cardinality_of_exclusion` | Sous FullCoupledRigidityOfflineExclusion, pour tout T, le nombre de hauteurs distinctes de la constellation égale son cardinal. | CONFIRMÉE SOUS CONDITION (FullCoupledRigidityOfflineExclusion, équivalente à l'exclusion hors ligne) | V162,V188 | 0 |
| `full_coupled_rigidity_offline_snapshot` | Pour un représentant positif hors ligne ρ à la hauteur T, le paquet RelationalRigidityBundle T ρ est établi. | CONFIRMÉE SOUS CONDITION (ρ représentant positif à la hauteur T et hors ligne) | V162 | 0 |

### `RhGapCriterion.Round26ARRelationalRigidityRecovery`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `offline_orbit_internal_defect_ge_two` | Pour un zéro hors ligne ρ, il existe une colonne j ≥ 2 où les contributions de pas de ρ et de son miroir reflectConjZero ρ diffèrent. | CONFIRMÉE SOUS CONDITION (ρ hors ligne) | V127,V162 | 3 |
| `offline_defect_column_grammar_dichotomy` | Pour ρ hors ligne, il existe n ≥ 2 avec défaut de contribution de ligne, et soit la classe de gnat n est 0 avec poids nul, soit elle est 2 ou 4 avec poids non nul et voix de ρ et de son miroir différentes. | CONFIRMÉE SOUS CONDITION (ρ hors ligne) | V127,V162 | 1 |
| `relational_rigidity_recovery` | Pour un représentant positif hors ligne ρ à la hauteur T, le paquet RelationalRigidityBundle T ρ est établi sans autre hypothèse. | CONFIRMÉE SOUS CONDITION (ρ représentant positif à la hauteur T et hors ligne) | V162 | 5 |
| `relational_bundle_no_strength_gain` | Pour tout prédicat Q, demander Q sous (hors ligne + paquet relationnel) équivaut à demander Q sous hors ligne seul. | CONFIRMÉE | V159,V189 | 1 |
| `relational_bundle_exclusion_iff_offline_exclusion` | Exclure toute configuration hors ligne portant le paquet relationnel équivaut à exclure toute configuration hors ligne. | ÉQUIVALENTE À RH | V189,V117 | 1 |
| `rh_of_relational_bundle_exclusion` | Si toute configuration hors ligne portant le paquet relationnel est exclue, tout zéro non trivial vérifie Re = 1/2. | IMPLIQUE RH SOUS PRÉMISSE (exclusion de toute configuration hors ligne portant le paquet relationnel, équivalente à l'exclusion hors ligne) | V110,V189 | 1 |

### `RhGapCriterion.Round26ASTerminalJunctionBoundary`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `nonempty_alignedOfflinePrimeJunction_iff` | Il existe un témoin AlignedOfflinePrimeJunction T ρ si et seulement si ρ est représentant positif à la hauteur T et hors ligne. | CONFIRMÉE | AJOUT | 0 |
| `auditedAlignedOfflineExclusion_iff_truncated_critical_line` | À la hauteur T, l'exclusion des témoins alignés équivaut à ce que tout représentant positif à T soit sur la ligne critique. | CONFIRMÉE | V161 | 0 |
| `not_auditedAlignedOfflineExclusion_of_offline` | Si ρ est représentant positif à T et hors ligne, l'exclusion alignée à la hauteur T est fausse. | RÉFUTATION COMPILÉE (AuditedAlignedOfflineExclusion T, en présence d'un représentant positif hors ligne à T) | AJOUT | 0 |
| `junctionExhaustionCertificate_exists_of_offline` | Si ρ est représentant positif à T et hors ligne, il existe une jonction J munie d'un certificat d'épuisement. | CONFIRMÉE SOUS CONDITION (ρ représentant positif à T et hors ligne) | AJOUT | 0 |

### `RhGapCriterion.Round26ASTerminalJunctionExhaustion`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ConstellationPrimePatternCrosswalkCell.mk.congr_simp` | Lemme de congruence auto-généré : deux cellules de croisement constellation/pattern sont égales dès que leurs index de ligne et de colonne sont égaux. | CONFIRMÉE (domaine : égalité des index de ligne et de colonne) | AJOUT | 0 |
| `_private.RhGapCriterion.Round26ASTerminalJunctionExhaustion.0.reflectConjZero_mem_positiveRepresentatives` | Si ρ est représentant positif à la hauteur T, alors reflectConjZero ρ l'est aussi. | CONFIRMÉE (domaine : ρ représentant positif à la hauteur T) | V63,V64,V162 | 1 |
| `_private.RhGapCriterion.Round26ASTerminalJunctionExhaustion.0.mem_orderedPositiveRepresentatives_of_mem_positive` | Tout représentant positif à T appartient à la liste ordonnée des représentants positifs à T. | CONFIRMÉE (domaine : ρ représentant positif à T) | V8 | 1 |
| `AlignedOfflinePrimeJunction.member` | Le zéro d'un AlignedOfflinePrimeJunction T ρ est représentant positif à la hauteur T. | CONFIRMÉE | AJOUT | 7 |
| `AlignedOfflinePrimeJunction.offline` | Le zéro ρ d'une jonction alignée hors ligne a une partie réelle différente de 1/2. | CONFIRMÉE | V162 | 9 |
| `AlignedOfflinePrimeJunction.primeIndex_ge_two` | L'indice premier d'une jonction alignée est ≥ 2. | CONFIRMÉE | AJOUT | 5 |
| `AlignedOfflinePrimeJunction.row_member` | La ligne d'indice rowIndex dans la liste ordonnée des représentants positifs à T est ρ. | CONFIRMÉE | V8 | 3 |
| `AlignedOfflinePrimeJunction.reflected_row_member` | La ligne d'indice reflectedRowIndex dans la liste ordonnée des représentants positifs à T est reflectConjZero ρ. | CONFIRMÉE | V8,V63,V64 | 3 |
| `AlignedOfflinePrimeJunction.rows_distinct` | Les indices de ligne de ρ et de son miroir dans la liste ordonnée sont différents. | CONFIRMÉE | V162,V74 | 2 |
| `AlignedOfflinePrimeJunction.defect` | Il existe un défaut de contribution de ligne entre ρ et son miroir à l'indice premier de la jonction, colonne 0. | CONFIRMÉE | V127 | 9 |
| `alignedOfflinePrimeJunction_exists` | Pour un représentant positif hors ligne ρ à la hauteur T, il existe un témoin de jonction alignée AlignedOfflinePrimeJunction T ρ. | CONFIRMÉE SOUS CONDITION (ρ représentant positif à T et hors ligne) | AJOUT | 7 |
| `AlignedOfflinePrimeJunction.leftCell_member` | Le membre de croisement de la cellule gauche est ρ. | CONFIRMÉE | AJOUT | 4 |
| `AlignedOfflinePrimeJunction.rightCell_member` | Le membre de croisement de la cellule droite est reflectConjZero ρ. | CONFIRMÉE | V63 | 4 |
| `AlignedOfflinePrimeJunction.cell_rows_distinct` | Les indices de ligne des cellules gauche et droite sont différents. | CONFIRMÉE | V162 | 4 |
| `AlignedOfflinePrimeJunction.active_table_entries_differ` | Sur la colonne active, les entrées de table des lignes de ρ et de son miroir diffèrent. | CONFIRMÉE | V127,V162 | 3 |
| `AlignedOfflinePrimeJunction.same_column_same_prime_labels_different_entries` | Les deux cellules sont distinctes et portent le même écart premier, la même transition, le même bloc de pattern, le même poids et la même famille, mais leurs entrées diffèrent. | CONFIRMÉE | V159,V162 | 2 |
| `AlignedOfflinePrimeJunction.active_prime_grammar_rigid` | Le bloc premier de la grammaire active de la jonction est GrammarRigid. | CONFIRMÉE | V174 | 1 |
| `AlignedOfflinePrimeJunction.active_prime_gap_ne_zero` | L'écart premier de la colonne active est non nul. | CONFIRMÉE | AJOUT | 2 |
| `AlignedOfflinePrimeJunction.active_prime_class_projection` | Sur la colonne active, la classe mod 6 de l'écart premier équivaut à la transition d'états correspondante. | CONFIRMÉE | V174 | 0 |
| `AlignedOfflinePrimeJunction.active_pattern_family_links` | Sur la colonne active, le gap et la relation du pattern premier égalent l'écart et la transition premiers, et la famille est l'écart mod 6. | CONFIRMÉE | V174 | 0 |
| `AlignedOfflinePrimeJunction.active_transition_is_one_of_four` | La transition première de la colonne active est l'une de tau11, tau15, tau51, tau55. | CONFIRMÉE | V174 | 0 |
| `AlignedOfflinePrimeJunction.active_defect_weight_dichotomy` | Au rang de la jonction, soit gnat est de classe 0 avec poids nul, soit de classe 2 ou 4 avec poids non nul et voix de ρ et de son miroir différentes. | CONFIRMÉE | V127,V162 | 1 |
| `AlignedOfflinePrimeJunction.active_MZ_eq_M` | Le bloc de grammaire complet reconstruit depuis les zéros à l'indice de la jonction (K=1) égale le bloc premier actif. | CONFIRMÉE | V48,V60,V174 | 2 |
| `AlignedOfflinePrimeJunction.active_zero_source_encoding_eq_M` | L'encodage de la source canonique des zéros à l'indice de la jonction (K=1) égale le bloc premier actif. | CONFIRMÉE | V48,V49,V60 | 2 |
| `AlignedOfflinePrimeJunction.active_primes_determine_exact_zero_source` | Pour toute continuation F déterminée par les premiers, la source de zéros déterminée par F est la source canonique des zéros de zêta. | CONFIRMÉE (domaine : F continuation de zêta déterminée par les premiers) | V48,V121 | 1 |
| `AlignedOfflinePrimeJunction.active_zero_height_gap_and_prime_gap_coexist` | La grammaire active contient à la fois un écart de hauteur zéro nul et un écart premier non nul sur la colonne active. | CONFIRMÉE | V162,V159 | 0 |
| `AlignedOfflinePrimeJunction.zero_gap_position_and_prime_defect_column_coexist` | Il existe un indice i où l'écart interne de hauteur au suivant vaut some 0, et il existe un défaut de contribution de ligne à la colonne première de la jonction. | CONFIRMÉE | V162,V127 | 0 |
| `AlignedOfflinePrimeJunction.active_total_column_bridge` | La somme (tsum) sur tous les zéros de leur contribution à la colonne active égale la différence lissée de Von Mangoldt moins fonds entre p(n+1) et p(n). | CONFIRMÉE | V121,V48 | 3 |
| `AlignedOfflinePrimeJunction.individual_defect_and_collective_prime_bridge_coexist` | Le défaut de contribution de ligne de ρ et de son miroir coexiste avec le pont collectif sur la colonne première (somme sur tous les zéros égale la différence lissée). | CONFIRMÉE | V121,V124,V127 | 0 |
| `AlignedOfflinePrimeJunction.active_finite_collective_projection_row_swap_invariant` | La somme finie sur la constellation de hauteur T des contributions de pas est invariante par échange des lignes ρ et reflectConjZero ρ. | CONFIRMÉE | V124,V162 | 1 |
| `AlignedOfflinePrimeJunction.naive_prime_label_entry_uniqueness_is_impossible_under_offline` | Sous un témoin hors ligne, PrimeSideLabelledEntryUniqueness (unicité d'entrée individuelle depuis les labels premiers) est fausse. | RÉFUTATION COMPILÉE (PrimeSideLabelledEntryUniqueness sous témoin hors ligne) | V159 | 1 |
| `AlignedOfflinePrimeJunction.injective_placement_cannot_be_height_only` | Sous un témoin hors ligne, si Φ est injective sur la constellation de hauteur T, alors Φ n'est pas déterminée par la hauteur seule. | RÉFUTATION COMPILÉE (Φ injectif sur la constellation et déterminé par la hauteur seule, sous témoin hors ligne) | V162,V158 | 0 |
| `AlignedOfflinePrimeJunction.reflected_pair_ratio_recurrence_fails_at_distinct_primes` | Sous un témoin hors ligne, le rapport réfléchi de ρ prend des valeurs différentes en deux premiers distincts p m et p n. | RÉFUTATION COMPILÉE (égalité du rapport réfléchi en deux premiers distincts, sous témoin hors ligne) | V102 | 0 |
| `AlignedOfflinePrimeJunction.two_prime_scale_character_faithfulness_separates_reflected_pair` | Sous un témoin hors ligne, les caractères d'échelle de ρ et de son miroir ne coïncident pas simultanément aux échelles log p m et log p n distincts. | RÉFUTATION COMPILÉE (coïncidence des caractères d'échelle de ρ et de son miroir aux deux échelles premières, sous témoin hors ligne) | V102 | 0 |
| `AlignedOfflinePrimeJunction.window_all_transitions_are_canonical` | Toute transition première de la fenêtre étendue de longueur K+1 est l'une de tau11, tau15, tau51, tau55. | CONFIRMÉE | V174 | 0 |
| `AlignedOfflinePrimeJunction.window_finite_metapattern` | À chaque colonne de la fenêtre étendue, p et p suivant sont 1 ou 5 mod 6, l'écart est de classe 0, 2 ou 4 et chaque classe équivaut à la transition correspondante (énoncé tronqué à 700 car., fin lue dans la docstring). | CONFIRMÉE | V174,V176 | 0 |
| `AlignedOfflinePrimeJunction.window_occurrences_are_real_and_ordered` | Dans la fenêtre étendue, toutes les positions de pattern sont premières et strictement croissantes. | CONFIRMÉE | V48 | 0 |
| `AlignedOfflinePrimeJunction.window_boundary_rigidity` | Sur la fenêtre étendue, l'état de sortie égale l'état d'entrée du bloc suivant, le déséquilibre 4 moins 2 égale la différence des poids d'état de bord, et il est borné en valeur absolue par 1. | CONFIRMÉE | V174 | 0 |
| `AlignedOfflinePrimeJunction.window_rank_theta_rigidity` | Sur la fenêtre étendue, la densité de rang vaut n + i + 1 et la densité θ vaut θm(n+i) à chaque colonne. | CONFIRMÉE | V27 | 0 |
| `AlignedOfflinePrimeJunction.window_ordered_successions_transport` | Sur la fenêtre étendue, les successions de transitions, de familles et de patterns calculées depuis les données reconstruites depuis les zéros égalent celles des vrais premiers. | CONFIRMÉE | V48,V60,V176 | 0 |
| `AlignedOfflinePrimeJunction.window_occurrence_transport` | Les ensembles d'occurrences de patterns, de familles et de transitions calculés depuis la reconstruction zéro égalent ceux des vrais premiers. | CONFIRMÉE | V48,V60,V176 | 0 |
| `AlignedOfflinePrimeJunction.window_universal_MZ_transport` | Toute construction déterministe F du comptage, des positions et des écarts a même valeur sur les données reconstruites depuis les zéros et sur les canoniques. | CONFIRMÉE | V48,V60,V159 | 0 |
| `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.table_defect` | Un certificat d'épuisement donne que les entrées de table des lignes de ρ et de son miroir diffèrent sur la colonne active. | CONFIRMÉE SOUS CONDITION (certificat d'épuisement de la jonction) | V127,V162 | 0 |
| `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.prime_gap_nonzero` | Un certificat d'épuisement donne que l'écart premier de la colonne active est non nul. | CONFIRMÉE SOUS CONDITION (certificat d'épuisement de la jonction) | AJOUT | 0 |
| `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.zero_height_gap` | Un certificat d'épuisement donne un écart de hauteur nul dans la liste des écarts zéro. | CONFIRMÉE SOUS CONDITION (certificat d'épuisement de la jonction) | V162,V66 | 0 |
| `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.mz_eq_m` | Un certificat d'épuisement donne que le bloc reconstruit depuis les zéros à l'indice de la jonction égale le bloc premier actif. | CONFIRMÉE SOUS CONDITION (certificat d'épuisement de la jonction) | V48,V60 | 0 |
| `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.source_encodes_m` | Un certificat d'épuisement donne que l'encodage de la source canonique des zéros égale le bloc premier actif. | CONFIRMÉE SOUS CONDITION (certificat d'épuisement de la jonction) | V48,V60 | 0 |
| `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.source_roundtrip` | Un certificat d'épuisement donne que toute continuation de zêta déterminée par les premiers a pour source de zéros la source canonique. | CONFIRMÉE SOUS CONDITION (certificat d'épuisement de la jonction et continuation F déterminée par les premiers) | V48,V121 | 0 |
| `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.weight_dichotomy` | Un certificat d'épuisement donne la dichotomie poids nul (classe 0) ou poids non nul avec voix différentes (classes 2 ou 4). | CONFIRMÉE SOUS CONDITION (certificat d'épuisement de la jonction) | V127,V162 | 0 |
| `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.total_bridge` | Un certificat d'épuisement donne le pont collectif : somme sur tous les zéros de la contribution égale la différence lissée de Von Mangoldt moins fonds. | CONFIRMÉE SOUS CONDITION (certificat d'épuisement de la jonction) | V121,V124 | 0 |
| `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.finite_collective_swap_blind` | Un certificat d'épuisement donne l'invariance de la somme finie sur la constellation par échange de ρ et de son miroir. | CONFIRMÉE SOUS CONDITION (certificat d'épuisement de la jonction) | V124,V162 | 0 |
| `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.naive_label_uniqueness_rejected` | Un certificat d'épuisement donne que PrimeSideLabelledEntryUniqueness est fausse. | RÉFUTATION COMPILÉE (PrimeSideLabelledEntryUniqueness, sous certificat d'épuisement) | V159 | 0 |
| `AlignedOfflinePrimeJunction.certify_compiled_junction_exhaustion` | Toute jonction alignée hors ligne J porte un certificat d'épuisement de jonction JunctionExhaustionCertificate. | CONFIRMÉE | AJOUT | 1 |

### `RhGapCriterion.Round26ATCompiledTerminalJunctionAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `offline_orbit_internal_defect_cofinal` | Pour tout zéro non trivial hors ligne, pour tout rang N, il existe un rang j au-delà de N où la paire réfléchie (ρ, réflexion conjuguée) présente un défaut de contribution de ligne en colonne 0. | CONFIRMÉE SOUS CONDITION (le zéro est hors ligne, partie réelle différente de 1/2) | AJOUT | 1 |
| `alignedOfflinePrimeJunction_exists_ge` | Pour un zéro hors ligne représentant positif de la hauteur T, pour tout N, il existe une jonction première alignée dont l'indice premier dépasse N. | CONFIRMÉE SOUS CONDITION (zéro hors ligne, représentant positif de T) | AJOUT | 0 |
| `_private.RhGapCriterion.Round26ATCompiledTerminalJunctionAudit.0.exists_prime_index_gt_with_residue` | Pour toute classe a inversible modulo 6 et tout rang N, il existe un rang m > N dont le premier canonique p m est congru à a modulo 6 (Dirichlet). | CONFIRMÉE (domaine : a est une unité, donc premier avec 6) | AJOUT | 1 |
| `exists_gap_class_ne_zero_ge` | Pour tout N, il existe un rang n au-delà de N dont l'écart premier gnat n n'est pas divisible par 6 (classe d'écart 2 ou 4). | CONFIRMÉE | AJOUT | 2 |
| `two_cofinal_predicates_need_not_meet` | Il existe deux prédicats sur les entiers, chacun non borné, qui n'ont aucun rang commun (contre-modèle abstrait). | CONFIRMÉE | AJOUT | 0 |
| `AlignedOfflinePrimeJunction.orbit_projection_already_row_swap_blind` | Sur une jonction alignée hors ligne, la contribution d'orbite du zéro est la somme des contributions premières de ρ et de son réfléchi, l'orbite du réfléchi égale celle de ρ, et pourtant les deux contributions individuelles diffèrent. | CONFIRMÉE | AJOUT | 0 |
| `crosswalkInternalGap_depends_only_on_row` | Deux cellules de la table de correspondance de même indice de ligne ont le même écart interne de hauteur avec la suivante. | CONFIRMÉE (domaine : les deux cellules ont la même ligne) | AJOUT | 0 |
| `crosswalkPrimeGap_depends_only_on_column` | Deux cellules de la table de correspondance de même colonne ont le même écart premier au rang n. | CONFIRMÉE (domaine : les deux cellules ont la même colonne) | AJOUT | 1 |
| `AlignedOfflinePrimeJunction.zero_gap_and_prime_gap_live_on_disjoint_coordinates` | Sur une jonction alignée, les cellules gauche et droite ont le même écart premier, leurs écarts internes de hauteur sont les écarts ordonnés de leurs lignes respectives, et leurs lignes sont distinctes. | CONFIRMÉE | AJOUT | 0 |
| `strong_dichotomy_branch_of_defectColumnMeetsChangeFamily` | Si la colonne de défaut rencontre la famille de changement, tout zéro hors ligne admet un rang n ≥ 2 de poids grammatical non nul où le pas de voix grammatical de ρ diffère de celui de son réfléchi. | CONFIRMÉE SOUS CONDITION (interface DefectColumnMeetsChangeFamily supposée ; zéro hors ligne) | AJOUT | 1 |
| `defectColumnMeetsChangeFamily_is_not_the_exclusion` | Pour toute hauteur T, si l'exclusion alignée auditée à T tient, alors aucun représentant positif de T n'est hors ligne. | CONFIRMÉE SOUS CONDITION (exclusion hors ligne alignée auditée à la hauteur T) | AJOUT | 0 |

### `RhGapCriterion.Round26AUReflectedDefectEventuality`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `rowContributionDefect_iff_reflectedResidueDifference_changes` | Un défaut de contribution de ligne en colonne 0 au rang n équivaut à ce que la différence résiduelle réfléchie change entre les échelles premières p n et p (n+1). | CONFIRMÉE | AJOUT | 2 |
| `rowContributionDefect_of_reflectedDifference_norm_lt` | Si la norme de la différence résiduelle réfléchie croît strictement entre p n et p (n+1), alors le défaut de contribution de ligne en colonne 0 a lieu au rang n. | CONFIRMÉE (domaine : croissance stricte de la norme sur ce pas) | AJOUT | 4 |
| `reflectedDifferenceEventuallyStrict_gives_defect_tail` | Si la différence réfléchie est eventuellement strictement croissante en norme sur les échelles premières, tout zéro hors ligne a un seuil N au-delà duquel tout rang porte un défaut de ligne. | CONFIRMÉE SOUS CONDITION (ReflectedDifferenceEventuallyStrictOnPrimes supposée ; zéro hors ligne) | AJOUT | 2 |
| `defectColumnMeetsChangeFamily_of_reflectedDifferenceEventuallyStrict` | La croissance stricte finale de la différence réfléchie sur les échelles premières implique l'interface DefectColumnMeetsChangeFamily. | CONFIRMÉE SOUS CONDITION (ReflectedDifferenceEventuallyStrictOnPrimes supposée) | AJOUT | 3 |
| `strong_change_family_defect_of_reflectedDifferenceEventuallyStrict` | Sous la croissance stricte finale de la différence réfléchie, tout zéro hors ligne admet un rang n ≥ 2 de poids non nul où le pas de voix de ρ diffère de celui de son réfléchi. | CONFIRMÉE SOUS CONDITION (ReflectedDifferenceEventuallyStrictOnPrimes supposée ; zéro hors ligne) | AJOUT | 1 |
| `critical_line_of_defectColumnMeetsChangeFamily_and_compatibility` | Si DefectColumnMeetsChangeFamily et ReflectedChangeFamilyCompatibility tiennent, tout zéro non trivial a partie réelle 1/2. | IMPLIQUE RH SOUS PRÉMISSE (DefectColumnMeetsChangeFamily et ReflectedChangeFamilyCompatibility, cette dernière équivalente à RH) | AJOUT | 1 |
| `riemannHypothesis_of_defectColumnMeetsChangeFamily_and_compatibility` | Si DefectColumnMeetsChangeFamily et ReflectedChangeFamilyCompatibility tiennent, alors RH (énoncé Mathlib). | IMPLIQUE RH SOUS PRÉMISSE (DefectColumnMeetsChangeFamily et ReflectedChangeFamilyCompatibility, cette dernière équivalente à RH) | AJOUT | 1 |
| `riemannHypothesis_of_reflectedDifferenceEventuallyStrict_and_compatibility` | Si la différence réfléchie est finalement strictement croissante en norme et que ReflectedChangeFamilyCompatibility tient, alors RH. | IMPLIQUE RH SOUS PRÉMISSE (croissance stricte finale, prouvée ailleurs, et ReflectedChangeFamilyCompatibility équivalente à RH) | AJOUT | 1 |
| `reflectedChangeFamilyCompatibility_of_RH` | RH implique ReflectedChangeFamilyCompatibility. | CONFIRMÉE SOUS CONDITION (RH supposée) | AJOUT | 1 |
| `reflectedChangeFamilyCompatibility_iff_RH_of_eventualStrict` | Sous la croissance stricte finale de la différence réfléchie, ReflectedChangeFamilyCompatibility équivaut à RH. | ÉQUIVALENTE À RH (ReflectedChangeFamilyCompatibility ↔ RH, sous une hypothèse que le lot établit inconditionnellement dans reflectedDifferenceEventuallyStrictOnPrimes_proved) | AJOUT | 1 |

### `RhGapCriterion.Round26AVReflectedDifferenceClosedForm`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `nontrivialZeroResidueTerm_eq_coeff_mul_cpow` | Le terme résiduel de Perron d'un zéro non trivial en x vaut son coefficient d'amplitude réfléchi fois x puissance complexe ρ. | CONFIRMÉE | AJOUT | 8 |
| `nontrivialZero_ne_zero` | Tout zéro non trivial est non nul. | CONFIRMÉE | AJOUT | 6 |
| `nontrivialZero_add_one_ne_zero` | Pour tout zéro non trivial ρ, ρ + 1 est non nul. | CONFIRMÉE | AJOUT | 6 |
| `reflectedRowCoeff_ne_zero` | Le coefficient d'amplitude réfléchi d'un zéro non trivial n'est jamais nul. | CONFIRMÉE | AJOUT | 19 |
| `conj_cpow_ofReal_pos` | Pour x réel strictement positif et s complexe, le conjugué de x^s vaut x^(conjugué de s). | CONFIRMÉE (domaine : 0 < x, simple domaine) | AJOUT | 1 |
| `cpow_mul_conj_cpow_reflect` | Pour x > 0 et un zéro non trivial ρ, x^ρ fois le conjugué de x^(réfléchi conjugué de ρ) vaut x. | CONFIRMÉE (domaine : 0 < x, simple domaine) | AJOUT | 2 |
| `reflectedCoeffA_pos` | Le coefficient A de la différence réfléchie d'un zéro non trivial est strictement positif. | CONFIRMÉE | AJOUT | 4 |
| `reflectedCoeffB_pos` | Le coefficient B de la différence réfléchie d'un zéro non trivial est strictement positif. | CONFIRMÉE | AJOUT | 4 |
| `_private.RhGapCriterion.Round26AVReflectedDifferenceClosedForm.0.rpow_sq` | Pour x > 0 et r réel, (x^r)^2 = x^(2r). | CONFIRMÉE (domaine : 0 < x, simple domaine) | AJOUT | 1 |
| `norm_reflectedResidueDifference_sq` | Pour x > 0 et un zéro non trivial ρ, le carré de la norme de la différence résiduelle réfléchie vaut le profil de norme carrée réfléchi (somme de deux puissances réelles à coefficients positifs plus un terme linéaire). | CONFIRMÉE (domaine : 0 < x, simple domaine) | AJOUT | 4 |
| `exists_strictMonoOn_rpow_pair_add_linear` | Pour A, B > 0, e > 1, f > 0 et C quelconque, la fonction A x^e + B x^f + 2 C x est strictement croissante sur une demi-droite [X, ∞) avec X ≥ 1. | CONFIRMÉE (domaine : A, B, f positifs et e > 1, données numériques) | AJOUT | 1 |
| `exists_strictMonoOn_reflectedNormSqProfile` | Pour un zéro hors ligne, le profil de norme carrée réfléchi est strictement croissant sur une demi-droite [X, ∞) avec X ≥ 1. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 1 |
| `_private.RhGapCriterion.Round26AVReflectedDifferenceClosedForm.0.prime_scale_pos` | Pour tout k, l'échelle première p k (vue dans les réels) est strictement positive. | CONFIRMÉE | AJOUT | 1 |
| `reflectedDifferenceEventuallyStrictOnPrimes_proved` | Sans hypothèse, ReflectedDifferenceEventuallyStrictOnPrimes tient : hors ligne, la norme de la différence réfléchie croît strictement à toute échelle première consécutive suffisamment grande. | CONFIRMÉE | AJOUT | 7 |
| `defectColumnMeetsChangeFamily_proved` | Sans hypothèse, l'interface DefectColumnMeetsChangeFamily est vraie. | CONFIRMÉE | AJOUT | 1 |
| `strong_change_family_defect_proved` | Pour tout zéro hors ligne, il existe un rang n ≥ 2 de poids grammatical non nul où le pas de voix de ρ diffère de celui de son réfléchi. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 3 |
| `reflectedDefectTail_proved` | Pour tout zéro hors ligne, il existe N tel que tout rang n ≥ N porte un défaut de contribution de ligne en colonne 0. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 1 |
| `reflectedChangeFamilyCompatibility_iff_RH` | ReflectedChangeFamilyCompatibility équivaut à RH, sans hypothèse. | ÉQUIVALENTE À RH | AJOUT | 2 |
| `grammarVoiceRow_reflected_difference` | La différence des voix grammaticales de ρ et de son réfléchi sur la fenêtre (n, K) vaut une combinaison linéaire, à poids et variations indépendants de la ligne, des différences résiduelles réfléchies aux échelles premières p(n+K), p(n+i+1) et p n. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Round26AWMultiLevelDisturbanceLadder`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `weightedRowWindow_sum_eq_grammarVoiceRow` | La somme des composantes de la fenêtre pondérée de ligne vaut la voix grammaticale de la ligne. | CONFIRMÉE | AJOUT | 0 |
| `weightedRowWindow_ne_of_zero_step_ne` | Si les pas de voix en colonne 0 de deux zéros diffèrent au rang n, leurs fenêtres pondérées non vides diffèrent. | CONFIRMÉE (domaine : 0 < K et pas de voix différents) | AJOUT | 1 |
| `canonicalFamilyMaskedWindow_ne_of_zero_step_ne` | Si les pas de voix en colonne 0 de deux zéros diffèrent au rang n, leurs fenêtres masquées par la famille canonique diffèrent. | CONFIRMÉE (domaine : 0 < K et pas de voix différents) | AJOUT | 1 |
| `canonical_family_occurs_in_both_histories` | Pour tout n, la famille singleton canonique en n est une occurrence à la position n à la fois dans l'histoire première gnat et dans l'histoire reconstruite depuis les zéros. | CONFIRMÉE | V174,V175 | 1 |
| `canonicalPatternMaskedWindow_ne_of_zero_step_ne` | Si les pas de voix en colonne 0 de deux zéros diffèrent au rang n, leurs fenêtres masquées par le motif canonique diffèrent. | CONFIRMÉE (domaine : 0 < K et pas de voix différents) | AJOUT | 1 |
| `canonical_pattern_occurs_in_both_histories` | Pour tous n et w, le motif canonique choisi en n apparaît à la même position dans M et dans M^Z, pour toute largeur. | CONFIRMÉE | V174,V175 | 1 |
| `grammarWeight_ne_zero_of_change_family` | Pour n ≥ 2 dont l'écart premier gnat n est congru à 2 ou 4 modulo 6, le poids grammatical en colonne 0 est non nul. | CONFIRMÉE (domaine : n ≥ 2 et classe d'écart 2 ou 4) | AJOUT | 4 |
| `change_family_weighted_step_defect_proved` | Pour tout zéro hors ligne, il existe n ≥ 2 avec écart congru à 2 ou 4 modulo 6, poids non nul et pas de voix de ρ différent de celui de son réfléchi. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 4 |
| `EarlyMultiLevelDisturbance.primeIndex_ge_two` | Le rang premier d'une perturbation précoce multi-niveaux est au moins 2. | CONFIRMÉE | AJOUT | 0 |
| `EarlyMultiLevelDisturbance.changeFamily` | Le rang premier d'une perturbation précoce a un écart congru à 2 ou 4 modulo 6. | CONFIRMÉE | AJOUT | 0 |
| `EarlyMultiLevelDisturbance.weight_ne_zero` | Le poids grammatical en colonne 0 au rang premier de la perturbation est non nul. | CONFIRMÉE | AJOUT | 0 |
| `EarlyMultiLevelDisturbance.weightedStepDefect` | Au rang de la perturbation, le pas de voix grammatical de ρ diffère de celui de son réfléchi en colonne 0. | CONFIRMÉE | AJOUT | 0 |
| `EarlyMultiLevelDisturbance.everyLabelledWindowDefect` | Pour toute largeur K > 0, la fenêtre pondérée étiquetée de ρ diffère de celle de son réfléchi au rang de la perturbation. | CONFIRMÉE (domaine : 0 < K, simple domaine) | AJOUT | 0 |
| `EarlyMultiLevelDisturbance.everyFamilyMaskedWindowDefect` | Pour toute largeur K > 0, la fenêtre masquée par la famille canonique de ρ diffère de celle de son réfléchi au rang de la perturbation. | CONFIRMÉE (domaine : 0 < K, simple domaine) | AJOUT | 0 |
| `EarlyMultiLevelDisturbance.everyPatternMaskedWindowDefect` | Pour toutes largeurs w et K > 0, la fenêtre masquée par le motif canonique de ρ diffère de celle de son réfléchi au rang de la perturbation. | CONFIRMÉE (domaine : 0 < K, simple domaine) | AJOUT | 0 |
| `EarlyMultiLevelDisturbance.familyOccursPrime` | Le rang de la perturbation est une occurrence de la famille singleton canonique dans l'histoire première gnat. | CONFIRMÉE | V174,V175 | 0 |
| `EarlyMultiLevelDisturbance.familyOccursReconstructed` | Le rang de la perturbation est une occurrence de la famille singleton canonique dans l'histoire reconstruite depuis les zéros. | CONFIRMÉE | V174,V175 | 0 |
| `EarlyMultiLevelDisturbance.patternOccursPrime` | Pour tout w, le motif canonique au rang de la perturbation apparaît en ce rang dans l'histoire première. | CONFIRMÉE | V174,V175 | 0 |
| `EarlyMultiLevelDisturbance.patternOccursReconstructed` | Pour tout w, le motif canonique au rang de la perturbation apparaît en ce rang dans l'histoire reconstruite depuis les zéros. | CONFIRMÉE | V174,V175 | 0 |
| `earlyMultiLevelDisturbance_exists` | Tout zéro hors ligne fournit un certificat de perturbation précoce multi-niveaux (type habité). | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 2 |
| `ComplexPsiDisturbance.psiIndex_ge_two` | L'indice psi d'une perturbation psi complexe est au moins 2. | CONFIRMÉE | AJOUT | 0 |
| `ComplexPsiDisturbance.leftRightSeparated` | À l'indice psi de la perturbation, les parties psi des primitives gauche et droite de la paire réfléchie de ρ sont différentes. | CONFIRMÉE | AJOUT | 0 |
| `ComplexPsiDisturbance.exactTotalDecomposition` | À l'indice psi de la perturbation, psi reconstruit depuis les zéros égale la somme des parties psi des primitives gauche, droite et reste de la paire réfléchie. | CONFIRMÉE | AJOUT | 0 |
| `complexPsiDisturbance_exists` | Tout zéro hors ligne fournit une perturbation psi complexe (type habité). | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 3 |
| `complexPsi_attack_survives_before_real_projection` | Pour un zéro hors ligne, une perturbation psi complexe existe et la projection partie réelle sur les complexes n'est pas injective. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 0 |
| `offline_has_multiple_preserved_disturbance_levels` | Pour un zéro hors ligne, il existe une perturbation précoce multi-niveaux, une perturbation psi complexe, et la partie réelle n'est pas injective. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 0 |

### `RhGapCriterion.Round26AXCarrierValueFreedom`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `weightedRowWindow_eq_generic` | La fenêtre pondérée de ligne de ρ égale la fenêtre générique construite sur ses pas de voix. | CONFIRMÉE | AJOUT | 0 |
| `canonicalFamilyMaskedWindow_eq_generic` | La fenêtre masquée par la famille canonique de ρ égale la fenêtre générique masquée construite sur ses pas de voix. | CONFIRMÉE | AJOUT | 0 |
| `canonicalPatternMaskedWindow_eq_generic` | La fenêtre masquée par le motif canonique de ρ égale la fenêtre générique masquée construite sur ses pas de voix. | CONFIRMÉE | AJOUT | 0 |
| `rowOfVector_apply` | La ligne construite à partir d'un vecteur v prend la valeur v k à la colonne k. | CONFIRMÉE | AJOUT | 3 |
| `genericRowWindow_attains` | La fenêtre générique de largeur K de la ligne construite depuis v est exactement v : elle atteint tout vecteur. | CONFIRMÉE | AJOUT | 2 |
| `genericFamilyMaskedWindow_free_on_retained` | Sur toute colonne retenue par le masque de famille (écart congru modulo 6 à celui de n), la fenêtre masquée de la ligne construite depuis v vaut v k. | CONFIRMÉE (domaine : colonne retenue par le masque de famille) | AJOUT | 2 |
| `genericPatternMaskedWindow_free_on_retained` | Sur toute colonne retenue par le masque de motif (même forme de motif de largeur w), la fenêtre masquée de la ligne construite depuis v vaut v k. | CONFIRMÉE (domaine : colonne retenue par le masque de motif) | AJOUT | 2 |
| `row_blind_law_forbids_nothing` | Si une propriété P vaut pour la fenêtre étiquetée de toute ligne, alors P vaut pour tout vecteur de Fin K vers ℂ. | CONFIRMÉE (domaine : P vraie sur toute fenêtre de ligne) | AJOUT | 1 |
| `row_blind_functional_law_forbids_nothing` | Si une propriété Q d'une fonctionnelle Φ de la fenêtre vaut pour toute ligne, alors Q (Φ v) vaut pour tout vecteur v. | CONFIRMÉE (domaine : Q vraie sur toute fenêtre de ligne) | AJOUT | 0 |
| `pattern_route_values_unconstrained` | Pour tout vecteur v, il existe une ligne dont la fenêtre masquée par le motif vaut v sur toute colonne retenue. | CONFIRMÉE | AJOUT | 0 |
| `family_route_values_unconstrained` | Pour tout vecteur v, il existe une ligne dont la fenêtre masquée par la famille vaut v sur toute colonne retenue. | CONFIRMÉE | AJOUT | 0 |
| `carrier_routes_require_row_specific_input` | Pour tout vecteur v, la ligne construite depuis v réalise v sur la fenêtre non masquée et sur toutes les colonnes retenues par les masques de famille et de motif. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Round26AXPsiConjugationRigidity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `psiRecoveredFromZeros_conj_eq_self` | Pour t ≥ 2, psi reconstruit depuis les zéros est égal à son conjugué complexe. | CONFIRMÉE (domaine : t ≥ 2, simple domaine) | V48,V121 | 1 |
| `psiRecoveredFromZeros_im_eq_zero` | Pour t ≥ 2, la partie imaginaire de psi reconstruit depuis les zéros est nulle. | CONFIRMÉE (domaine : t ≥ 2, simple domaine) | V48,V121 | 1 |
| `nontrivialZero_ne_conj` | Aucun zéro non trivial n'est égal à son conjugué complexe. | CONFIRMÉE | AJOUT | 1 |
| `reflectConjZero_ne_conj` | Pour un zéro hors ligne, son réfléchi (1 − conjugué) n'est pas le conjugué de ρ. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V63 | 1 |
| `psi_conj_not_carried_by_reflected_pair` | Pour un zéro hors ligne, aucun membre du support de la paire réfléchie n'est égal au conjugué de ρ. | CONFIRMÉE SOUS CONDITION (zéro hors ligne ; deuxième hypothèse d'appartenance au support) | V63 | 1 |
| `reflected_pair_psi_im_absorbed_by_rest` | Pour t ≥ 2 et un zéro hors ligne, la partie imaginaire de la composante reste vaut l'opposé de la somme des parties imaginaires des composantes gauche et droite de la paire. | CONFIRMÉE SOUS CONDITION (t ≥ 2 ; zéro hors ligne) | AJOUT | 2 |
| `psi_absorption_is_purely_algebraic` | Pour trois fonctions arbitraires f g h et t, si la somme des trois a partie imaginaire nulle, la partie imaginaire de h t vaut l'opposé de celles de f t et g t. | CONFIRMÉE (domaine : somme de partie imaginaire nulle) | AJOUT | 0 |
| `psi_reality_does_not_constrain_pair` | Il existe des complexes L R REST dont la somme est réelle mais dont L + R n'est pas réel (contre-modèle). | CONFIRMÉE | AJOUT | 0 |
| `restPsiImaginaryRigidity_forces_real_pair` | Sous RestPsiImaginaryRigidity, pour t ≥ 2 et un zéro hors ligne, la somme des parties imaginaires des composantes gauche et droite de la paire est nulle. | CONFIRMÉE SOUS CONDITION (RestPsiImaginaryRigidity supposée ; t ≥ 2 ; zéro hors ligne) | AJOUT | 0 |
| `psi_route_state` | Pour t ≥ 2 et un zéro hors ligne : psi reconstruit est réel (auto-conjugué), aucun membre de la paire réfléchie n'est le conjugué de ρ, la partie imaginaire du reste absorbe celle de la paire, et une perturbation psi complexe existe. | CONFIRMÉE SOUS CONDITION (t ≥ 2 ; zéro hors ligne) | AJOUT | 0 |

### `RhGapCriterion.Round26AYReflectedPairMirrorInvariance`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `reflectedPairLeft_reflect` | L'étiquette gauche de la paire réfléchie du réfléchi de ρ est l'étiquette droite de celle de ρ. | CONFIRMÉE | AJOUT | 2 |
| `reflectedPairRight_reflect` | L'étiquette droite de la paire réfléchie du réfléchi de ρ est l'étiquette gauche de celle de ρ. | CONFIRMÉE | AJOUT | 2 |
| `reflectedPairFinset_mirror_invariant` | Le support fini de la paire réfléchie de ρ égale celui de son réfléchi. | CONFIRMÉE | AJOUT | 1 |
| `reflect_signed_distance` | La distance signée du réfléchi de ρ à la droite critique est l'opposée de celle de ρ (Re' − 1/2 = −(Re − 1/2)). | CONFIRMÉE | V65,V180 | 1 |
| `offline_mirror_invariant` | Le réfléchi de ρ est hors ligne si et seulement si ρ l'est. | CONFIRMÉE | V65 | 1 |
| `reflectedPairPsi_mirror_invariant` | La valeur psi de la paire réfléchie est la même en ρ et en son réfléchi, pour tout t. | CONFIRMÉE | AJOUT | 4 |
| `no_pair_law_separates_the_two_sides` | Toute propriété Q de la valeur psi de la paire a la même valeur de vérité en ρ et en son réfléchi. | CONFIRMÉE | AJOUT | 0 |
| `pair_measurement_is_mirror_blind` | Toute mesure Φ de la valeur psi de la paire prend la même valeur en ρ et en son réfléchi. | CONFIRMÉE | AJOUT | 0 |
| `reflectedPairPsiSizeLaw_mirror_consistent` | Si une loi de taille de constante C sur psi de la paire vaut, alors pour tout ρ et t ≥ 2 la norme de psi de la paire du réfléchi est majorée par C fois racine de t. | CONFIRMÉE SOUS CONDITION (loi de taille ReflectedPairPsiSizeLaw C supposée ; t ≥ 2) | AJOUT | 0 |
| `mirror_effect_is_a_symmetry_not_a_detector` | Pour tout ρ et t : le support de la paire, la valeur psi de la paire et le fait d'être hors ligne sont tous invariants par passage au réfléchi. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Round26AZZeroGapGrammarRigidity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `offline_member_realises_zero_gap` | Un membre hors ligne de la constellation de hauteur T a son réfléchi dans la même constellation, distinct de lui, avec un écart de hauteur exactement nul. | CONFIRMÉE SOUS CONDITION (membre de la constellation de hauteur T ; hors ligne) | V62,V65,V162 | 2 |
| `offline_member_violates_zeroGapRigidity` | Si la constellation de hauteur T contient un membre hors ligne, la rigidité d'écart nul ZeroGapRigidity T est violée. | CONFIRMÉE SOUS CONDITION (membre hors ligne dans la constellation) | V162 | 2 |
| `zeroGapRigidity_of_critical_line` | Si tous les membres de la constellation de hauteur T sont sur la ligne critique, la rigidité ZeroGapRigidity T tient. | CONFIRMÉE SOUS CONDITION (tous les membres de la constellation sur la ligne critique) | V161 | 2 |
| `not_zeroGapRigidity_iff_offline_member` | La rigidité ZeroGapRigidity T est violée si et seulement si la constellation de hauteur T contient un membre hors ligne. | CONFIRMÉE | V162 | 1 |
| `zeroGapRigidity_iff_critical_line` | La rigidité ZeroGapRigidity T équivaut à ce que tous les membres de la constellation de hauteur T soient sur la ligne critique. | CONFIRMÉE | V161,V162 | 1 |
| `all_zeroGapRigidity_iff_global_critical_line` | La rigidité ZeroGapRigidity T pour tout T équivaut à ce que tout zéro non trivial ait partie réelle 1/2. | ÉQUIVALENTE À RH | V162,V188 | 0 |
| `zero_gap_grammar_state` | Pour tout T : tout membre hors ligne de la constellation a son réfléchi dans la constellation avec écart de hauteur nul, et la rigidité est violée si et seulement s'il existe un membre hors ligne. | CONFIRMÉE | V162 | 0 |

### `RhGapCriterion.Round26B1ATGrammarPartition`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `normalizedATWindowEnergy_eq_sum_grammar_classes` | L'énergie normalisée de la fenêtre aT est la somme, sur les quatre classes de grammaire Transform6, des énergies de classe. | CONFIRMÉE | AJOUT | 0 |
| `normalizedATClassEnergy_nonneg` | Pour r ≥ 1, l'énergie de classe normalisée aT est positive ou nulle pour tout U et toute classe τ. | CONFIRMÉE (domaine : 1 ≤ r, simple domaine) | AJOUT | 0 |

### `RhGapCriterion.Round26B2B3ATCoboundary`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `aT_eq_completeInnovation_add_coboundary` | Pour n ≥ 2, il existe une classe τ et un entier k tels que transformOf des résidus modulo 6 de p n et p (n+1) vaut τ et aT n = 6k + 3·grammarCrossV2 − log(p n) + (potentiel de p(n+1) − potentiel de p n) modulo 6. | CONFIRMÉE (domaine : n ≥ 2) | V174 | 1 |
| `grammarPotentialV2_prime_mem_zero_one` | Pour tout n, le potentiel grammatical du résidu modulo 6 de p n est compris entre 0 et 1. | CONFIRMÉE | V174 | 1 |
| `aT_sub_coboundary_eq_innovation` | Pour n ≥ 2, aT n moins la différence de potentiels grammaticaux (cobord borné) vaut exactement 6k + 3·grammarCrossV2 − log(p n) pour un entier k et la classe de transition τ réalisée. | CONFIRMÉE (domaine : n ≥ 2) | V174 | 1 |

### `RhGapCriterion.Round26B4AdjacentBlockKernelPrototype`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `chasles_two_blocks` | La somme de a sur [i,k) est la somme sur [i,j) plus la somme sur [j,k). | CONFIRMÉE (domaine : i ≤ j ≤ k, simple domaine) | AJOUT | 0 |
| `chasles_two_blocks_weighted` | Même découpage en deux blocs adjacents pour la somme pondérée de a n · w n. | CONFIRMÉE (domaine : i ≤ j ≤ k, simple domaine) | AJOUT | 0 |
| `sum_Ico_by_parts_real` | Sommation par parties discrète : la somme pondérée de w i · a i sur [m,n) égale un terme de bord dans le cumul de a moins la somme des différences de w fois le cumul. | CONFIRMÉE (domaine : m < n, simple domaine) | AJOUT | 1 |
| `kernel_difference_summation_by_parts` | La différence de deux sommes pondérées de noyaux w1 et w0 sur [m,n) égale une différence de bords dans le cumul moins une somme du cumul contre la différence des dérivées discrètes des deux noyaux. | CONFIRMÉE (domaine : m < n, simple domaine) | AJOUT | 2 |
| `weighted_block_difference_bound` | Si le cumul de a est majoré en valeur absolue par M sur [m,n] et la différence des dérivées discrètes des deux noyaux par V sur [m,n−1), alors la différence des deux sommes pondérées est majorée par (/bord final/ + /bord initial/)·M + (n−1−m)·M·V. | CONFIRMÉE SOUS CONDITION (m < n ; M, V positifs ; bornes de cumul et de dérivée supposées) | AJOUT | 0 |
| `cumulative_aT_eq_R` | Le cumul de aT jusqu'à m égale R m. | CONFIRMÉE | AJOUT | 0 |
| `gramWeight_eq_windowKernel_deriv` | Le poids de Gram à l'échelle X au rang j égale la dérivée discrète du noyau de fenêtre i ↦ min(p(i+1), X). | CONFIRMÉE | AJOUT | 0 |
| `gramWindowWeight_eq_kernel_deriv_diff` | Le poids de fenêtre de Gram (r,U) au rang j égale la différence des dérivées discrètes des noyaux min(p(i+1), exp U) et min(p(i+1), exp U / r). | CONFIRMÉE | AJOUT | 0 |
| `scale_two_style_linear_window_difference_eq_gramWindowWeight_sum` | Pour m < n, la différence linéaire de fenêtres à deux échelles sur aT s'exprime par des termes de bord en R et une somme de poids gramWindowWeight contre R. | CONFIRMÉE (domaine : m < n, simple domaine) | AJOUT | 0 |
| `weighted_sum_abs_le_sqrt_mass_mul_sqrt_energy` | Pour a positif sur un ensemble fini s et tout signal Rsig, /Σ a i · Rsig i/ est majoré par la racine de la masse fois la racine de l'énergie Σ a i · Rsig i². | CONFIRMÉE (domaine : poids a positifs sur s) | AJOUT | 3 |
| `gramWindowWeight_R_sum_le_energy` | Pour tous r, U, N, la valeur absolue de la somme de gramWindowWeight contre R est majorée par la somme des deux produits racine-de-masse fois racine-d'énergie aux deux échelles exp U et exp U / r. | CONFIRMÉE | AJOUT | 1 |
| `gramWindowWeight_R_sum_le_sqrt_VTkernel` | Pour r ≥ 1, la même majoration à l'horizon canonique s'écrit avec l'énergie VTkernel de aT aux deux échelles. | CONFIRMÉE (domaine : 1 ≤ r, simple domaine) | AJOUT | 0 |
| `gramWeight_sum_range_eq` | La somme des poids de Gram à l'échelle X sur range N vaut min(p(N+1), X) − min(3, X). | CONFIRMÉE | AJOUT | 2 |
| `gramWeight_sum_range_bounds` | Pour X ≥ 3, la somme des poids de Gram sur range N est positive et majorée par X − 3. | CONFIRMÉE (domaine : 3 ≤ X, simple domaine) | AJOUT | 0 |
| `abs_diff_le_sum_of_nonneg` | Pour a, b positifs ou nuls, /a − b/ ≤ a + b. | CONFIRMÉE (domaine : a, b positifs, simple domaine) | AJOUT | 1 |
| `sq_div_sum_le_sum_of_nonneg` | Pour a, b positifs ou nuls, (a − b)² / (a + b) ≤ a + b. | CONFIRMÉE (domaine : a, b positifs, simple domaine) | AJOUT | 1 |
| `abs_sum_mul_le_sqrt_mul_sqrt` | Inégalité de Cauchy-Schwarz : /Σ f i · h i/ ≤ racine(Σ f i²) · racine(Σ h i²) sur un ensemble fini. | CONFIRMÉE | AJOUT | 1 |
| `weighted_diff_sum_abs_le_sqrt_combined_mass_mul_sqrt_combined_energy` | Pour a, b positifs sur s et tout signal Rsig, /Σ (a i − b i)·Rsig i/ ≤ racine(Σ(a i + b i)) · racine(Σ (a i + b i)·Rsig i²). | CONFIRMÉE (domaine : a, b positifs sur s) | AJOUT | 1 |
| `gramWindowWeight_R_sum_le_combined_sqrt` | Pour tous r, U, N, /Σ gramWindowWeight · R/ est majorée par la racine de la masse combinée fois la racine de l'énergie combinée aux deux échelles. | CONFIRMÉE | AJOUT | 0 |
| `squared_state_forward_recurrence` | Si D(n+2)² ≤ a·D(n+1)² + b·D(n)² + F n pour tout n, alors D(n+2)² + D(n+1)² ≤ max(a+1, b)·(D(n+1)² + D(n)²) + F n. | CONFIRMÉE SOUS CONDITION (récurrence quadratique supposée pour tout n) | AJOUT | 0 |
| `am_gm_cross_term_bound` | Si /D(n+1)·D(n)/ ≤ α·D(n)² + F alors 2·D(n+1)·D(n) ≤ 2α·D(n)² + 2F. | CONFIRMÉE SOUS CONDITION (α positif ; borne du produit supposée) | AJOUT | 0 |
| `generalized_linear_recurrence_bound` | Si lam n ≥ 0 et Q(n+1) ≤ lam n · Q n + F n pour tout n, alors Q n est majoré par le produit des lam fois Q 0 plus la somme pondérée des forçages F k (variation des constantes). | CONFIRMÉE SOUS CONDITION (lam positif ; récurrence supposée) | AJOUT | 2 |
| `linear_recurrence_bound_constant_one` | Si Q(n+1) ≤ Q n + F n pour tout n, alors Q n ≤ Q 0 + Σ_{k<n} F k. | CONFIRMÉE SOUS CONDITION (récurrence supposée) | AJOUT | 2 |
| `linear_recurrence_bound_constant_forcing` | Si Q(n+1) ≤ Q n + C pour tout n, alors Q n ≤ Q 0 + n·C. | CONFIRMÉE SOUS CONDITION (récurrence supposée) | AJOUT | 0 |
| `linear_recurrence_bound_polynomial_forcing` | Si Q(n+1) ≤ Q n + C·(n+1)^d pour tout n, alors Q n ≤ Q 0 + C·Σ_{k<n}(k+1)^d. | CONFIRMÉE SOUS CONDITION (récurrence supposée) | AJOUT | 0 |
| `linear_recurrence_bound_geometric` | Si λ ≥ 0 et Q(n+1) ≤ λ·Q n + F n pour tout n, alors Q n ≤ λ^n·Q 0 + Σ_{k<n} λ^(n−1−k)·F k. | CONFIRMÉE SOUS CONDITION (λ positif ; récurrence supposée) | AJOUT | 1 |
| `scaleBlockInnovationSum_eq_b0_add_b1` | Pour x ≥ 0, la somme d'innovation sur l'annulus de facteur 4 en x est la somme sur (x/4, x/2] plus celle sur (x/2, x]. | CONFIRMÉE (domaine : 0 ≤ x, simple domaine) | AJOUT | 2 |
| `scaleBlockInnovationSum_two_mul_eq_b1_add_b2` | Pour x ≥ 0, la somme d'innovation sur l'annulus de facteur 4 en 2x est la somme sur (x/2, x] plus celle sur (x, 2x]. | CONFIRMÉE (domaine : 0 ≤ x, simple domaine) | AJOUT | 0 |
| `scaleBlockInnovationSum_four_mul_eq_b2_add_b3` | Pour x ≥ 0, la somme d'innovation sur l'annulus de facteur 4 en 4x est la somme sur (x, 2x] plus celle sur (2x, 4x]. | CONFIRMÉE (domaine : 0 ≤ x, simple domaine) | AJOUT | 0 |
| `A0_mul_A2_eq_four_cross_terms` | (b0 + b1)(b2 + b3) = b0·b2 + b0·b3 + b1·b2 + b1·b3 (identité algébrique). | CONFIRMÉE | AJOUT | 0 |
| `gram_bilinear_cross_le_avg_diag` | Pour un noyau de Gram à poids positifs, deux fois la forme bilinéaire croisée de z1 et z2 est majorée par la somme des énergies diagonales de z1 et de z2. | CONFIRMÉE (domaine : poids w positifs sur J) | AJOUT | 1 |
| `gram_bilinear_cross_le_avg_diag_indicator_form` | Pour deux sous-ensembles s1 et s2 de range N, deux fois l'énergie croisée des indicatrices sous le noyau de Gram est majorée par la somme des énergies diagonales de s1 et de s2. | CONFIRMÉE | AJOUT | 0 |
| `finite_enter_leave_decomposition` | Pour deux ensembles finis Sold et Snew, la différence des sommes de a vaut la somme sur les entrants moins la somme sur les sortants. | CONFIRMÉE | AJOUT | 0 |
| `scaleBlockIndex_intersection_empty` | Pour tout x, les indices des blocs d'échelle en 4x et en x ont une intersection vide. | CONFIRMÉE | AJOUT | 0 |
| `gramWindowWeight_abs_sum_eq_sum` | Pour r ≥ 1, la somme des valeurs absolues de gramWindowWeight sur range N égale leur somme signée. | CONFIRMÉE (domaine : 1 ≤ r, simple domaine) | AJOUT | 1 |
| `gramWindowWeight_abs_sum_eq_telescoped` | Pour r ≥ 1, la somme des valeurs absolues de gramWindowWeight sur range N vaut la différence télescopée des minima min(p(N+1), exp U), min(3, exp U) et de leurs analogues à l'échelle exp U / r. | CONFIRMÉE (domaine : 1 ≤ r, simple domaine) | AJOUT | 0 |
| `wide_window_abs_le_sum_annuli_abs_add_two` | Pour x ≥ 0, l'écart en valeur absolue du cumul complet aT entre 4x et x/4 est majoré par la somme des valeurs absolues des deux sommes d'annulus plus 2. | CONFIRMÉE (domaine : 0 ≤ x, simple domaine) | AJOUT | 0 |
| `gramWindowWeight_R_sum_le_sqrt_rawRWindowEnergy` | Pour r ≥ 1 et tout U, la valeur absolue de la somme de gramWindowWeight contre R à l'horizon canonique est majorée par la racine de la masse de gramWindowWeight fois la racine de l'énergie brute de fenêtre de R. | CONFIRMÉE (domaine : 1 ≤ r, simple domaine) | AJOUT | 1 |
| `rawRWindowEnergy_eq_exp_two_mul_normalizedRWindowEnergy` | L'énergie brute de fenêtre de R vaut exp(2U) fois l'énergie normalisée. | CONFIRMÉE | AJOUT | 1 |
| `sqrt_exp_eq_exp_half` | La racine carrée de exp x vaut exp(x/2). | CONFIRMÉE | AJOUT | 1 |
| `gramWindowWeight_R_sum_le_exp_three_halves_mul_sqrt_normalized` | Pour r ≥ 1, la valeur absolue de la somme de gramWindowWeight contre R à l'horizon canonique est majorée par exp(3U/2) fois la racine de l'énergie normalisée de fenêtre de R. | CONFIRMÉE (domaine : 1 ≤ r, simple domaine) | AJOUT | 0 |
| `weighted_quadratic_energy_exponent_dictionary` | Pour X > 0, X^(1+2β) / X² = X^(2β−1). | CONFIRMÉE (domaine : 0 < X, simple domaine) | AJOUT | 0 |
| `exp_two_beta_sub_one_mul_eq_rpow` | Pour tous U et β réels, exp((2β−1)·U) = (exp U)^(2β−1). | CONFIRMÉE | AJOUT | 0 |
| `canonicalTHorizon_monotone` | L'horizon canonique canonicalTHorizon est monotone en U. | CONFIRMÉE | AJOUT | 2 (nom dupliqué dans 2 modules) |
| `rawRWindowEnergy_scale_chasles` | Pour r ≥ 1, rawRWindowEnergy r (U + log r) + rawRWindowEnergy r U = rawRWindowEnergy (r²) (U + log r). | CONFIRMÉE (domaine : 1 ≤ r, simple domaine) | AJOUT | 0 (nom dupliqué dans 2 modules) |
| `Rseq_sub_eq_sum_dR` | Pour toute suite réelle et m ≤ k, Rseq k − Rseq m est la somme des incréments sur [m,k). | CONFIRMÉE (domaine : m ≤ k, simple domaine) | AJOUT | 1 (nom dupliqué dans 2 modules) |
| `centered_R_sq_le_card_mul_sum_dR_sq` | Pour toute suite réelle et m ≤ k, (Rseq k − Rseq m)² ≤ (k−m)·Σ des carrés des incréments sur [m,k) (Cauchy-Schwarz discret). | CONFIRMÉE (domaine : m ≤ k, simple domaine) | AJOUT | 1 (nom dupliqué dans 2 modules) |
| `R_succ_sub_R_eq_aT` | R(n+1) − R n = aT n. | CONFIRMÉE | AJOUT | 3 (nom dupliqué dans 2 modules) |
| `centered_R_sq_le_card_mul_sum_aT_sq` | Pour m ≤ k, (R k − R m)² ≤ (k−m)·Σ_{j∈[m,k)} aT j². | CONFIRMÉE (domaine : m ≤ k, simple domaine) | AJOUT | 2 (nom dupliqué dans 2 modules) |
| `R_sq_le_card_mul_sum_aT_sq` | Pour tout k, (R k)² ≤ k·Σ_{j<k} aT j². | CONFIRMÉE | AJOUT | 0 (nom dupliqué dans 2 modules) |
| `young_param_upper` | Pour η > 0, (a+b)² ≤ (1+η)a² + (1+1/η)b². | CONFIRMÉE (domaine : η > 0, simple domaine) | AJOUT | 2 (nom dupliqué dans 2 modules) |
| `young_param_reverse` | Pour η > 0, (1−η)c² − (1/η −1)a² ≤ (a+c)². | CONFIRMÉE (domaine : η > 0, simple domaine) | AJOUT | 1 (nom dupliqué dans 2 modules) |
| `R_eq_centered_add_boundary` | Pour tous m, k, R k = (R k − R m) + R m. | CONFIRMÉE | AJOUT | 0 (nom dupliqué dans 2 modules) |
| `R_sq_le_param_young_centered_add_boundary` | Pour η > 0, (R k)² ≤ (1+η)(R k − R m)² + (1+1/η)(R m)². | CONFIRMÉE (domaine : η > 0, simple domaine) | AJOUT | 1 |
| `R_sq_le_param_young_aT_energy_add_boundary` | Pour η > 0 et m ≤ k, (R k)² ≤ (1+η)(k−m)Σ_{j∈[m,k)} aT j² + (1+1/η)(R m)². | CONFIRMÉE (domaine : η > 0 ; m ≤ k, simple domaine) | AJOUT | 0 |
| `integral_inv_sq_eq` | Pour 0 < a ≤ b, l'intégrale de 1/t² sur [a,b] vaut 1/a − 1/b. | CONFIRMÉE (domaine : 0 < a ≤ b, simple domaine) | AJOUT | 3 |
| `intervalIntegrable_const_div_sq` | Pour 0 < a ≤ b et K réel, t ↦ K/t² est intégrable sur [a,b]. | CONFIRMÉE (domaine : 0 < a ≤ b, simple domaine) | AJOUT | 2 |
| `thetaLocalEnergy_prime_gap_ge` | Pour m ≥ 1 et η dans ]0,1[, l'énergie locale de l'erreur theta sur [p m, p(m+1)] est minorée par une fonction affine de correctedTAtPrime(m)² et de g(m)² multipliée par 1/p m − 1/p(m+1). | CONFIRMÉE (domaine : m ≥ 1 ; η dans ]0,1[, simples domaines) | AJOUT | 0 |
| `quadratic_energy_generically_reaches_X_sq` | Pour tout X entier, une masse de X termes égaux à 1 vaut X et l'énergie quadratique de signal √X vaut exactement X². | CONFIRMÉE | AJOUT | 0 |
| `R_sq_single_step_recurrence` | Pour η > 0 et tout n, R(n+1)² ≤ (1+η)·aT n² + (1+1/η)·R n². | CONFIRMÉE (domaine : η > 0, simple domaine) | AJOUT | 1 |
| `R_sq_iterated_bound` | Pour η > 0 et tout n, R n² ≤ Σ_{k<n} (1+1/η)^(n−1−k)·(1+η)·aT k². | CONFIRMÉE (domaine : η > 0, simple domaine) | AJOUT | 0 |
| `geometric_multiplier_gt_one` | Pour η > 0, 1 < 1 + 1/η. | CONFIRMÉE (domaine : η > 0, simple domaine) | AJOUT | 0 |
| `geometric_multiplier_approaches_one` | Pour tout ε > 0, il existe η > 0 tel que 1 + 1/η < 1 + ε. | CONFIRMÉE (domaine : ε > 0, simple domaine) | AJOUT | 0 |
| `lambda_forcing_tradeoff_exact` | Pour η > 0, (1 + 1/η − 1)(1 + η − 1) = 1. | CONFIRMÉE (domaine : η > 0, simple domaine) | AJOUT | 0 |

### `RhGapCriterion.Round26B4CollectiveDecoderAbsorptionAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `reflectConjZeroEquiv_apply` | L'application sous-jacente de l'équivalence reflectConjZeroEquiv est reflectConjZero. | CONFIRMÉE | V63 | 0 |
| `tsum_reflectConjZero` | Pour toute fonction f sur les zéros non triviaux à valeurs dans un monoïde additif commutatif séparé, la somme totale de f ∘ réfléchi égale la somme totale de f. | CONFIRMÉE | V124 | 1 |
| `zero_channel_reflection_invariant` | Pour tout x, la somme totale des termes résiduels des zéros non triviaux est inchangée quand chaque zéro est remplacé par son réfléchi. | CONFIRMÉE | V124,V63 | 1 |
| `smoothedZeroFormula_sub_background_reflection_invariant` | Pour x > 1, la somme totale des termes résiduels aux zéros réfléchis égale la formule lissée des zéros moins son fond. | CONFIRMÉE (domaine : 1 < x, simple domaine) | V121,V124 | 0 |
| `decoder_output_is_prime_side` | Pour x ≥ 2, psi reconstruit depuis les zéros égale la fonction psi de Chebyshev. | CONFIRMÉE (domaine : 2 ≤ x, simple domaine) | V48,V121 | 0 |
| `decoder_prime_gaps_are_canonical` | Pour tout n, l'écart premier reconstruit depuis les zéros égale l'écart premier canonique gnat n. | CONFIRMÉE | V48 | 0 |

### `RhGapCriterion.Round26B4CompleteGrammarOfflineBlindness`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `offline_member_leaves_complete_grammar_unchanged` | Pour un zéro hors ligne représentant positif de T, le bloc de grammaire complet (n,k) construit depuis le triplet reconstruit (comptage, positions, écarts) égale celui construit depuis pi, p, gnat. | CONFIRMÉE SOUS CONDITION (zéro hors ligne représentant positif de T) | V48,V175 | 11 |
| `offline_member_leaves_any_count_position_gap_object_unchanged` | Pour toute fonction F du triplet (comptage, positions, écarts), F du triplet reconstruit égale F du triplet canonique, dès qu'un zéro hors ligne représentant positif de T existe. | CONFIRMÉE SOUS CONDITION (zéro hors ligne représentant positif de T) | V48,V175 | 0 |
| `offline_transitions_unchanged` | Sous un zéro hors ligne représentant positif de T, les transitions du bloc de grammaire reconstruit égalent celles du bloc canonique. | CONFIRMÉE SOUS CONDITION (zéro hors ligne représentant positif de T) | V175 | 0 |
| `offline_pattern_unchanged` | Sous un zéro hors ligne représentant positif de T, le motif du bloc de grammaire reconstruit égale celui du bloc canonique. | CONFIRMÉE SOUS CONDITION (zéro hors ligne représentant positif de T) | V175 | 0 |
| `offline_family_unchanged` | Sous un zéro hors ligne représentant positif de T, la famille du bloc de grammaire reconstruit égale celle du bloc canonique. | CONFIRMÉE SOUS CONDITION (zéro hors ligne représentant positif de T) | V175 | 0 |
| `offline_positions_order_unchanged` | Sous un zéro hors ligne représentant positif de T, les positions ordonnées du bloc de grammaire reconstruit égalent celles du bloc canonique. | CONFIRMÉE SOUS CONDITION (zéro hors ligne représentant positif de T) | V175 | 0 |
| `offline_transitionOrder_unchanged` | Sous un zéro hors ligne représentant positif de T, la succession de transitions du bloc reconstruit égale celle du bloc canonique. | CONFIRMÉE SOUS CONDITION (zéro hors ligne représentant positif de T) | V175 | 0 |
| `offline_patternOrder_unchanged` | Sous un zéro hors ligne représentant positif de T, la succession de motifs du bloc reconstruit égale celle du bloc canonique. | CONFIRMÉE SOUS CONDITION (zéro hors ligne représentant positif de T) | V175 | 0 |
| `offline_familyOrder_unchanged` | Sous un zéro hors ligne représentant positif de T, la succession de familles du bloc reconstruit égale celle du bloc canonique. | CONFIRMÉE SOUS CONDITION (zéro hors ligne représentant positif de T) | V175 | 0 |
| `offline_entry_unchanged` | Sous un zéro hors ligne représentant positif de T, l'entrée du bloc de grammaire reconstruit égale celle du bloc canonique. | CONFIRMÉE SOUS CONDITION (zéro hors ligne représentant positif de T) | V175 | 0 |
| `offline_exit_unchanged` | Sous un zéro hors ligne représentant positif de T, l'état de sortie du bloc de grammaire reconstruit égale celui du bloc canonique. | CONFIRMÉE SOUS CONDITION (zéro hors ligne représentant positif de T) | V175 | 0 |
| `offline_shape_assembly_unchanged` | Sous un zéro hors ligne représentant positif de T, la forme (assemblage) du bloc de grammaire reconstruit égale celle du bloc canonique. | CONFIRMÉE SOUS CONDITION (zéro hors ligne représentant positif de T) | V175 | 0 |

### `RhGapCriterion.Round26B4ConstellationCollisionRigidity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `positiveRepresentatives_mem_heightConstellation` | Tout représentant positif de la constellation des hauteurs T appartient à la constellation des hauteurs complète T. | CONFIRMÉE (appartenance à la constellation positive) | AJOUT | 3 |
| `off_critical_line_gives_table_height_collision` | Pour un représentant positif ρ de hauteur T, hors ligne critique dans la bande ouverte, il existe un autre représentant positif σ, distinct de ρ, de même hauteur, et tous deux appartiennent à la constellation des hauteurs. | CONFIRMÉE (domaine : ρ représentant positif de partie réelle dans ]0,1[ et différente de 1/2) | V62,V162 | 0 |
| `rowContributionDefect_refinementEntry_iff` | Deux entrées étiquetées de la table de raffinement (ρ,k) et (σ,k) diffèrent si et seulement si les lignes ρ et σ présentent un défaut de contribution en (n,k). | CONFIRMÉE | AJOUT | 1 |
| `rowContributionDefect_grammarVoiceStep_iff_of_weight_ne_zero` | Si le poids de grammaire n k est non nul, les pas de voix de grammaire de ρ et σ diffèrent exactement lorsque leurs contributions présentent un défaut de ligne. | CONFIRMÉE (domaine : poids de grammaire non nul) | AJOUT | 9 |
| `_private.RhGapCriterion.Round26B4ConstellationCollisionRigidity.0.swap_mem_of_mem` | Une transposition de deux éléments d'un ensemble fini préserve l'appartenance d'un troisième élément à cet ensemble. | CONFIRMÉE (a, b, x dans s) | AJOUT | 1 |
| `finset_sum_comp_swap_of_mem` | Une somme finie sur un ensemble est invariante par permutation de deux éléments de l'ensemble. | CONFIRMÉE (a et b dans s) | AJOUT | 3 |
| `collective_column_projection_row_swap_invariant` | La somme collective des contributions de pas sur la constellation est invariante par échange de deux lignes ρ et σ de la constellation. | CONFIRMÉE (ρ et σ dans la constellation) | AJOUT | 1 |
| `collective_block_projection_row_swap_invariant` | La somme collective de blocs étiquetés du domaine de raffinement est invariante par échange de deux lignes de la constellation. | CONFIRMÉE (ρ et σ dans la constellation) | AJOUT | 1 |
| `collective_grammarVoiceRow_row_swap_invariant` | La somme collective des lignes de voix de grammaire sur la constellation est invariante par échange de deux lignes de la constellation. | CONFIRMÉE (ρ et σ dans la constellation) | AJOUT | 0 |
| `not_collectiveTableRowFaithfulnessObligation_of_window_defect` | S'il existe deux lignes distinctes de la constellation avec un défaut de contribution sur la fenêtre (n,K), l'obligation de fidélité de ligne de la projection collective de table est fausse. | RÉFUTATION COMPILÉE (l'obligation de fidélité de ligne de la table collective, en présence d'un défaut de fenêtre) | AJOUT | 0 |
| `reflectConj_re` | Le réfléchi-conjugué 1 - conj ρ a pour partie réelle 1 - Re ρ. | CONFIRMÉE | V65 | 1 |
| `reflectConj_im` | Le réfléchi-conjugué 1 - conj ρ a la même partie imaginaire que ρ. | CONFIRMÉE | V65,V63 | 0 |
| `zetaZeroMultiplicity_reflectConj` | La multiplicité analytique de zêta est conservée par le passage de ρ à 1 - conj ρ pour un zéro non trivial dans la bande ouverte. | CONFIRMÉE (domaine : zéro non trivial de partie réelle dans ]0,1[) | V65,V63 | 1 |
| `_private.RhGapCriterion.Round26B4ConstellationCollisionRigidity.0.norm_nontrivialZeroResidueTerm_eq_amplitude_rpow` | La norme du terme résiduel individuel d'un zéro non trivial en x>0 vaut une amplitude déterminée fois x puissance Re τ. | CONFIRMÉE (0<x) | V102 | 2 |
| `_private.RhGapCriterion.Round26B4ConstellationCollisionRigidity.0.residueAmplitude_pos` | L'amplitude résiduelle exacte d'un zéro non trivial est strictement positive. | CONFIRMÉE | AJOUT | 1 |
| `tendsto_prime_cast_atTop` | La suite des premiers canoniques vue dans ℝ tend vers l'infini. | CONFIRMÉE | AJOUT | 8 |
| `_private.RhGapCriterion.Round26B4ConstellationCollisionRigidity.0.tendsto_dominant_rpow_gap_atTop` | Si c1>0, 0<b<a, alors c1 x^a - c2 x^b tend vers +∞ quand x tend vers +∞. | CONFIRMÉE (domaine : c1>0 et 0<b<a) | AJOUT | 1 |
| `_private.RhGapCriterion.Round26B4ConstellationCollisionRigidity.0.exists_prime_index_rpow_gap_gt` | Si c1>0 et 0<b<a, pour tout seuil M il existe un indice premier j tel que c1 p_j^a - c2 p_j^b dépasse M. | CONFIRMÉE (domaine : c1>0 et 0<b<a) | AJOUT | 1 |
| `_private.RhGapCriterion.Round26B4ConstellationCollisionRigidity.0.prime_cast_pos'` | Tout premier canonique p_j vu dans ℝ est strictement positif. | CONFIRMÉE | AJOUT | 1 |
| `reflected_residue_difference_unbounded` | Pour un zéro non trivial ρ strictement dans la bande et hors ligne critique, la norme de la différence des termes résiduels de ρ et de son réfléchi-conjugué aux premiers canoniques dépasse tout seuil. | CONFIRMÉE SOUS CONDITION (zéro dans la bande ouverte et hors ligne critique) | V102 | 4 |
| `constant_reflected_difference_of_equal_steps` | Si les contributions de pas de ρ et σ coïncident pour tout j (colonne 0), alors la différence de leurs termes résiduels aux premiers p_j est constante et égale à celle en p_0. | CONFIRMÉE (domaine : contributions de pas égales pour tout j) | AJOUT | 1 |
| `reflected_offline_rows_have_contribution_defect` | Pour un zéro non trivial dans la bande ouverte hors ligne critique, il existe un j tel que les contributions de pas de ρ et de son réfléchi-conjugué diffèrent. | CONFIRMÉE SOUS CONDITION (zéro dans la bande ouverte et hors ligne critique) | V102,V162 | 2 |

### `RhGapCriterion.Round26B4ConstellationGapElementLocalisation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `off_critical_line_gives_constellation_heights_not_nodup` | Si un représentant positif de la constellation est dans la bande ouverte et hors ligne critique, la liste des hauteurs de la constellation n'est pas sans doublon. | CONFIRMÉE SOUS CONDITION (représentant positif dans la bande ouverte hors ligne critique) | V162,V63 | 0 |
| `off_critical_line_gives_zero_constellation_gap` | Si tous les représentants positifs sont dans la bande ouverte et l'un est hors ligne critique, l'un des écarts de la constellation vaut exactement 0. | CONFIRMÉE SOUS CONDITION (constellation dans la bande ouverte, un membre hors ligne critique) | V162,V50 | 1 |
| `critical_line_constellation_has_no_zero_gap` | Si tous les représentants positifs sont sur la ligne critique, aucun écart de la constellation n'est nul. | CONFIRMÉE SOUS CONDITION (tous les représentants positifs sur la ligne critique) | V161 | 1 |
| `offline_member_leaves_reconstructed_grammar_unchanged` | Si un représentant positif est hors ligne critique, tout objet F construit de façon déterministe depuis les positions et écarts premiers reconstruits depuis les zéros est égal à F appliqué aux positions et écarts des premiers canoniques. | CONFIRMÉE SOUS CONDITION (membre hors ligne critique dans la constellation) | V48,V131 | 2 |
| `offline_member_leaves_reconstructed_pattern_block_unchanged` | Si un représentant positif est hors ligne critique, le bloc de pattern reconstruit depuis les zéros égale le bloc de pattern canonique pour tous n et k. | CONFIRMÉE SOUS CONDITION (membre hors ligne critique dans la constellation) | V48,V131 | 0 |
| `offline_member_leaves_reconstructed_prime_gap_unchanged` | Si un représentant positif est hors ligne critique, l'écart premier reconstruit depuis les zéros égale l'écart premier canonique en toute position. | CONFIRMÉE SOUS CONDITION (membre hors ligne critique dans la constellation) | V48,V131 | 0 |

### `RhGapCriterion.Round26B4ConstellationGapPattern`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `zeroHeight_def` | La hauteur d'un zéro est sa partie imaginaire. | CONFIRMÉE | AJOUT | 0 |
| `constellationHeights_length` | La liste des hauteurs de la constellation a pour longueur le cardinal des représentants positifs. | CONFIRMÉE | AJOUT | 1 |
| `constellationGaps_length` | La liste des écarts de la constellation a pour longueur le cardinal des représentants positifs moins 1. | CONFIRMÉE | AJOUT | 2 |
| `constellationHeights_pairwise_le` | La liste des hauteurs de la constellation est croissante au sens large. | CONFIRMÉE | V8,V50 | 2 |
| `_private.RhGapCriterion.Round26B4ConstellationGapPattern.0.gaps_forall_iff_chain'` | Une propriété portant sur chaque écart de la liste des différences successives équivaut à la même propriété sur chaque pas d'une chaîne. | CONFIRMÉE | AJOUT | 2 |
| `_private.RhGapCriterion.Round26B4ConstellationGapPattern.0.gaps_forall_of_chain'` | Si la chaîne des pas vérifie P sur chaque différence, alors toute différence successive de la liste vérifie P. | CONFIRMÉE (domaine : la chaîne vérifie P sur chaque pas) | AJOUT | 3 |
| `constellationGaps_nonneg` | Tout écart de la constellation est positif ou nul. | CONFIRMÉE | V8 | 4 |
| `_private.RhGapCriterion.Round26B4ConstellationGapPattern.0.sum_gaps_telescope` | La somme des différences successives d'une liste a::l est le dernier élément moins a. | CONFIRMÉE | AJOUT | 2 |
| `constellationGaps_sum` | Si la liste des hauteurs de la constellation est a::l, la somme de ses écarts vaut dernier moins premier. | CONFIRMÉE (domaine : liste des hauteurs de forme a::l) | AJOUT | 0 |
| `constellationWindowHeights_eq` | Les hauteurs de la fenêtre sont les hauteurs (zeroHeight) des zéros de la fenêtre. | CONFIRMÉE | AJOUT | 1 |
| `constellationWindow_length` | Une fenêtre contenue dans la constellation a exactement la longueur L. | CONFIRMÉE SOUS CONDITION (i+L au plus égal au cardinal de la constellation positive) | AJOUT | 3 |
| `constellationWindowHeights_length` | La liste des hauteurs d'une fenêtre contenue dans la constellation a longueur L. | CONFIRMÉE SOUS CONDITION (i+L au plus égal au cardinal de la constellation positive) | AJOUT | 1 |
| `constellationWindowGaps_length` | La liste des écarts d'une fenêtre contenue dans la constellation a longueur L-1. | CONFIRMÉE SOUS CONDITION (i+L au plus égal au cardinal de la constellation positive) | AJOUT | 2 |
| `constellationWindowHeights_pairwise_le` | Les hauteurs d'une fenêtre sont croissantes au sens large. | CONFIRMÉE | V8 | 1 |
| `constellationWindowGaps_nonneg` | Les écarts d'une fenêtre sont positifs ou nuls. | CONFIRMÉE | V8 | 0 |
| `constellationWindowGaps_sum` | Si les hauteurs de la fenêtre sont a::l, la somme des écarts de la fenêtre vaut dernier moins premier. | CONFIRMÉE (domaine : hauteurs de fenêtre de forme a::l) | AJOUT | 0 |
| `five_zero_window_is_complete` | Si la constellation positive compte au moins cinq représentants, la fenêtre de cinq zéros à partir du rang 0 a longueur 5 et 4 écarts. | CONFIRMÉE (domaine : au moins cinq représentants positifs) | AJOUT | 0 |
| `distinct_same_height_off_critical_line` | Deux zéros distincts de même hauteur ne peuvent être tous deux sur la ligne critique. | CONFIRMÉE (domaine : zéros distincts de même partie imaginaire) | V162,V161 | 1 |
| `constellationHeights_pairwise_lt_of_critical_line` | Si tous les représentants positifs sont sur la ligne critique, leurs hauteurs sont strictement croissantes. | CONFIRMÉE SOUS CONDITION (tous les représentants positifs sur la ligne critique) | V161,V8 | 1 |
| `constellationGaps_pos_of_critical_line` | Si tous les représentants positifs sont sur la ligne critique, tous les écarts de la constellation sont strictement positifs. | CONFIRMÉE SOUS CONDITION (tous les représentants positifs sur la ligne critique) | V161,V8 | 3 |
| `isNontrivialZetaZero_reflectConj` | Si ρ est un zéro non trivial dans la bande ouverte, 1 - conj ρ est un zéro non trivial. | CONFIRMÉE (domaine : zéro non trivial de partie réelle dans ]0,1[) | V63,V65 | 10 |
| `off_critical_line_gives_height_collision` | Pour un représentant positif hors ligne critique dans la bande ouverte, il existe un second représentant positif distinct de même hauteur. | CONFIRMÉE SOUS CONDITION (représentant positif dans la bande ouverte hors ligne critique) | V62,V162 | 4 |
| `constellation_gaps_pos_iff_critical_line` | Si la constellation est dans la bande ouverte, tous ses écarts sont strictement positifs si et seulement si tous ses zéros sont sur la ligne critique. | CONFIRMÉE SOUS CONDITION (constellation dans la bande ouverte) | V161,V162 | 5 |

### `RhGapCriterion.Round26B4ConstellationOffLinePairSplit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `mem_onLineMembers` | Un zéro appartient aux membres sur la ligne de la constellation si et seulement s'il est dans la constellation des hauteurs et de partie réelle 1/2. | CONFIRMÉE | AJOUT | 1 |
| `mem_offLineMembers` | Un zéro appartient aux membres hors ligne de la constellation si et seulement s'il est dans la constellation des hauteurs et de partie réelle différente de 1/2. | CONFIRMÉE | AJOUT | 2 |
| `onLineMembers_eq_fixedPoints` | Les membres sur la ligne critique de la constellation sont exactement les membres de la constellation fixes par l'involution de réflexion-conjugaison. | CONFIRMÉE | V161,V65 | 0 |
| `offLineMembers_reflect_mem` | L'involution de réflexion-conjugaison stabilise l'ensemble des membres hors ligne de la constellation. | CONFIRMÉE SOUS CONDITION (ρ membre hors ligne de la constellation) | V63,V162 | 1 |
| `offLineMembers_reflect_ne` | L'involution de réflexion-conjugaison n'a aucun point fixe parmi les membres hors ligne de la constellation. | CONFIRMÉE SOUS CONDITION (ρ membre hors ligne de la constellation) | V62,V162 | 0 |
| `heightConstellation_sum_split` | Toute somme sur la constellation se décompose en somme sur les membres sur la ligne plus somme sur les membres hors ligne. | CONFIRMÉE | AJOUT | 1 |
| `offLineMembers_image_reflectConjZero` | L'image des membres hors ligne d'une constellation par l'involution est cet ensemble lui-même. | CONFIRMÉE | V63 | 1 |
| `sum_offLineMembers_reflectConjZero` | La somme d'une fonction f sur les membres hors ligne est invariante par précomposition avec l'involution de réflexion-conjugaison. | CONFIRMÉE | V63 | 1 |
| `two_nsmul_sum_offLineMembers_eq_sum_reflected_pairs` | Deux fois la somme de f sur les membres hors ligne égale la somme sur les mêmes membres de f ρ + f(réfléchi ρ). | CONFIRMÉE | V63 | 1 |
| `two_nsmul_heightConstellation_sum_eq_onLine_and_reflected_pairs` | Deux fois la somme de f sur toute la constellation égale deux fois la somme sur la ligne critique plus la somme hors ligne des paires f ρ + f(réfléchi ρ). | CONFIRMÉE | V63 | 0 |
| `offLineMembers_eq_empty_iff_critical_line` | L'ensemble des membres hors ligne de la constellation T est vide si et seulement si toute la constellation est sur la ligne critique. | CONFIRMÉE | V161,V162 | 0 |

### `RhGapCriterion.Round26B4ConstellationPrimeHistoryBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `one_lt_prime_cast` | Tout premier canonique p_j vu dans ℝ est strictement supérieur à 1. | CONFIRMÉE | AJOUT | 3 |
| `summable_zeroPrimeStepContribution` | Pour tous n et k, la famille ρ ↦ contribution de pas entre p(n+k) et p(n+k+1) est sommable sur les zéros non triviaux. | CONFIRMÉE | V121 | 0 |
| `tsum_zeroPrimeStepContribution_eq_zero_channel_increment` | La somme sur tous les zéros non triviaux de la contribution de pas entre deux premiers consécutifs vaut la différence des sommes de termes résiduels non triviaux en p(n+k+1) et p(n+k). | CONFIRMÉE | V121 | 2 |
| `tsum_zeroPrimeStepContribution_eq_prime_history_increment` | La somme sur tous les zéros non triviaux de la contribution de pas entre p(n+k) et p(n+k+1) vaut l'incrément de la somme de von Mangoldt lissée moins l'incrément du fond zéro lissé. | CONFIRMÉE | V121,V48 | 2 |
| `prime_history_increment_eq_tsum_zeroPrimeStepContribution_add_background` | L'incrément de la somme de von Mangoldt lissée entre p(n+k) et p(n+k+1) vaut la somme sur les zéros des contributions de pas plus l'incrément du fond spectral lissé. | CONFIRMÉE | V121,V48 | 0 |

### `RhGapCriterion.Round26B4ConstellationPrimePatternCrosswalk`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ConstellationPrimePatternCrosswalkCell.rowIndex_lt` | L'indice de ligne d'une cellule de croisement constellation-pattern est strictement inférieur à la longueur des représentants positifs ordonnés. | CONFIRMÉE | AJOUT | 2 |
| `ConstellationPrimePatternCrosswalkCell.column_lt` | La colonne d'une cellule de croisement est strictement inférieure à K. | CONFIRMÉE | AJOUT | 2 |
| `crosswalk_refinementEntry_eq` | L'entrée de raffinement de la cellule de croisement est la contribution de pas du membre de la cellule à sa colonne. | CONFIRMÉE | AJOUT | 4 |
| `crosswalk_left_prime_is_prime` | Le premier gauche associé à une cellule de croisement est un nombre premier. | CONFIRMÉE | AJOUT | 0 |
| `crosswalk_right_prime_is_prime` | Le premier droit associé à une cellule de croisement est un nombre premier. | CONFIRMÉE | AJOUT | 0 |
| `crosswalk_prime_gap_eq_right_sub_left` | L'écart premier de la cellule de croisement égale premier droit moins premier gauche. | CONFIRMÉE | AJOUT | 0 |
| `crosswalk_pattern_column_gap_eq` | L'écart stocké par le bloc de pattern canonique à la colonne de la cellule est l'écart premier de la cellule. | CONFIRMÉE | AJOUT | 0 |
| `crosswalk_pattern_column_transition_eq` | La transition stockée par le bloc de pattern canonique à la colonne de la cellule est la transition de la cellule. | CONFIRMÉE | AJOUT | 0 |
| `crosswalk_family_is_canonical` | Si 1 ≤ n + colonne, il existe une unique classe a dans {0,2,4} égale à l'écart premier de la cellule modulo 6. | CONFIRMÉE (domaine : 1 ≤ n + colonne) | V174 | 0 |
| `crosswalk_labels_row_independent` | Deux cellules de même colonne ont mêmes écart premier, transition, bloc de pattern et poids de grammaire, indépendamment de la ligne de constellation. | CONFIRMÉE (domaine : même colonne) | V159,V131 | 6 |
| `crosswalk_family_row_independent` | Pour deux cellules de même colonne, l'existence d'une unique classe de {0,2,4} pour l'écart modulo 6 est équivalente d'une cellule à l'autre. | CONFIRMÉE (domaine : même colonne) | V174 | 1 |
| `crosswalk_distinct_positions_give_distinct_cells` | Deux cellules dont les indices de ligne diffèrent sont distinctes. | CONFIRMÉE (domaine : indices de ligne différents) | AJOUT | 2 |
| `crosswalk_height_collision_labels_row_independent` | Pour deux cellules de lignes distinctes, de même hauteur de membre et de même colonne, les cellules sont distinctes et portent les mêmes écart, transition, bloc de pattern et poids de grammaire. | CONFIRMÉE (domaine : lignes distinctes, membres de même hauteur, même colonne) | V162,V131 | 0 |

### `RhGapCriterion.Round26B4ConstellationRefinementTable`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `heightConstellation_eq` | La constellation des hauteurs égale par définition l'ensemble canonique des zéros non triviaux de hauteur bornée par T. | CONFIRMÉE | AJOUT | 0 |
| `mem_heightConstellation` | Un zéro appartient à la constellation des hauteurs T si et seulement si la valeur absolue de sa partie imaginaire est strictement inférieure à T. | CONFIRMÉE | AJOUT | 18 |
| `heightConstellation_mono` | La constellation des hauteurs est croissante (inclusion) en T. | CONFIRMÉE (T ≤ T') | AJOUT | 2 |
| `refinementColumn_left_prime` | La borne gauche p(n+t) d'une transition de la table est un nombre premier. | CONFIRMÉE | AJOUT | 1 |
| `refinementColumn_right_prime` | La borne droite p(n+t+1) d'une transition de la table est un nombre premier. | CONFIRMÉE | AJOUT | 1 |
| `refinementColumn_strictMono` | Pour tous n et t, p(n+t) < p(n+t+1). | CONFIRMÉE | AJOUT | 0 |
| `refinementColumn_order` | Si t<u, alors p(n+t) < p(n+u). | CONFIRMÉE (t<u) | AJOUT | 0 |
| `zeroPrimeStepContribution_eq_block_step` | La contribution de pas de ρ égale l'incrément du bloc de contribution : bloc(k+1) moins bloc(k). | CONFIRMÉE | AJOUT | 2 |
| `row_telescoping_zero` | La somme de zéro contributions de pas vaut 0 et le bloc à 0 colonne vaut 0. | CONFIRMÉE | AJOUT | 1 |
| `row_telescoping_one` | La somme d'une seule contribution de pas égale le bloc à 1 colonne. | CONFIRMÉE | AJOUT | 0 |
| `row_telescoping` | La somme des k premières contributions de pas d'une ligne égale le bloc de contribution à k colonnes (télescopage). | CONFIRMÉE | AJOUT | 4 |
| `constellationRefinementDomain_succ` | Le domaine de raffinement à k+1 colonnes est le domaine à k colonnes union la nouvelle colonne à hauteur fixée. | CONFIRMÉE | AJOUT | 0 |
| `constellationRefinementDomain_mono_col` | Le domaine de raffinement croît avec le nombre de colonnes. | CONFIRMÉE (k ≤ k') | AJOUT | 1 |
| `constellationRefinementEntry_indep` | L'entrée de raffinement en (ρ,k) est la contribution de pas de ρ en (n,k), sans dépendre de T ni de k au titre de paramètres. | CONFIRMÉE | AJOUT | 0 |
| `constellationRefinementDomain_mono_row` | Le domaine de raffinement croît avec la hauteur T, à nombre de colonnes fixé. | CONFIRMÉE (T ≤ T') | AJOUT | 2 |
| `constellationRefinementDomain_height_restrict` | L'intersection du domaine de hauteur T' et du domaine de hauteur T redonne le domaine de hauteur T. | CONFIRMÉE (T ≤ T') | AJOUT | 0 |
| `double_refinement_commutes` | L'intersection du domaine (T',k) avec le domaine (T,k+1) égale le domaine (T,k). | CONFIRMÉE (T ≤ T') | AJOUT | 0 |
| `double_refinement_union_le` | L'union des domaines (T',k) et (T,k+1) est contenue dans le domaine (T',k+1). | CONFIRMÉE (T ≤ T') | AJOUT | 0 |
| `collective_column_projection` | La somme sur la constellation de la contribution de pas en colonne k égale la différence des sommes collectives des termes résiduels en p(n+k+1) et p(n+k). | CONFIRMÉE | V121,V124 | 0 |
| `collective_block_projection` | La somme des entrées de raffinement sur le domaine étiqueté égale la somme sur la constellation des blocs de contribution. | CONFIRMÉE | V121,V124 | 0 |
| `collective_block_projection_columns` | La somme des entrées de raffinement sur le domaine étiqueté égale la somme, colonne par colonne, des projections collectives sur la constellation. | CONFIRMÉE | V121,V124 | 0 |
| `heightConstellation_sum_eq_canonical` | La somme des termes résiduels sur la constellation égale la somme canonique des moins multiplicité fois Perron.f sur les zéros de hauteur bornée. | CONFIRMÉE | V121 | 0 |
| `heightConstellation_empty_of_nonpos` | La constellation des hauteurs est vide pour T ≤ 0. | CONFIRMÉE (T ≤ 0) | AJOUT | 1 |
| `constellationRefinementDomain_zero` | Le domaine de raffinement à zéro colonne est vide. | CONFIRMÉE | AJOUT | 0 |
| `constellationRefinementDomain_empty_of_nonpos` | Le domaine de raffinement est vide pour T ≤ 0, quel que soit le nombre de colonnes. | CONFIRMÉE (T ≤ 0) | AJOUT | 0 |
| `conjugate_rows_distinct` | Un zéro de la constellation de partie imaginaire non nulle admet son conjugué comme membre distinct de la même constellation. | CONFIRMÉE SOUS CONDITION (ρ dans la constellation, partie imaginaire non nulle) | V63,V64 | 1 |
| `row_total_is_boundary_only` | Si deux blocs (n1,k1),(n2,k2) ont mêmes premiers de bord, les totaux de ligne des contributions de pas de ρ sont égaux. | CONFIRMÉE (domaine : mêmes premiers de bord p n1 = p n2 et p(n1+k1) = p(n2+k2)) | AJOUT | 0 |
| `entry_recovers_from_table` | La contribution de pas en (n,k) est la différence des totaux de ligne à k+1 et k colonnes. | CONFIRMÉE | AJOUT | 0 |
| `boundary_hyps_force_equal_blocks` | Deux blocs de mêmes premiers de bord sont le même bloc : n1=n2 et k1=k2. | CONFIRMÉE (domaine : mêmes premiers de bord) | AJOUT | 1 |
| `no_distinct_same_boundary_blocks` | Il n'existe aucun couple de blocs premiers distincts partageant les deux mêmes premiers de bord. | RÉFUTATION COMPILÉE (l'existence de deux blocs premiers canoniques distincts de mêmes premiers de bord) | AJOUT | 0 |
| `nontrivialZeroResidueTerm_conj` | Pour x>0, le conjugué du terme résiduel individuel de ρ en x est le terme résiduel du zéro conjugué en x. | CONFIRMÉE (0<x) | V101 | 2 |
| `_private.RhGapCriterion.Round26B4ConstellationRefinementTable.0.heightConstellation_conj_mem` | Le conjugué d'un membre de la constellation est encore un membre de la constellation. | CONFIRMÉE SOUS CONDITION (ρ dans la constellation) | V63,V64 | 1 |
| `collective_projection_conj_invariant` | Pour x>0, la somme des termes résiduels individuels sur la constellation est invariante par conjugaison complexe. | CONFIRMÉE (0<x) | V101 | 1 |
| `collective_projection_im_eq_zero` | Pour x>0, la somme des termes résiduels sur la constellation a une partie imaginaire nulle. | CONFIRMÉE (0<x) | V101 | 0 |

### `RhGapCriterion.Round26B4ConstellationReflectionInvolution`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `reflectConjZero_coe` | La valeur sous-jacente du réfléchi-conjugué d'un zéro non trivial ρ est 1 - conj ρ. | CONFIRMÉE | V65 | 16 |
| `reflectConjZero_re` | La partie réelle du réfléchi-conjugué d'un zéro non trivial ρ vaut 1 - Re ρ. | CONFIRMÉE | V65,V63 | 30 |
| `reflectConjZero_im` | La partie imaginaire du réfléchi-conjugué d'un zéro non trivial ρ est celle de ρ. | CONFIRMÉE | V65,V63 | 31 |
| `reflectConjZero_involutive` | La réflexion-conjugaison sur les zéros non triviaux est une involution. | CONFIRMÉE | V63 | 9 |
| `reflectConjZero_injective` | La réflexion-conjugaison sur les zéros non triviaux est injective. | CONFIRMÉE | V63 | 3 |
| `reflectConjZero_eq_self_iff` | Un zéro non trivial est fixe par la réflexion-conjugaison si et seulement si sa partie réelle vaut 1/2. | CONFIRMÉE | V161,V65 | 26 |
| `reflectConjZero_ne_self_iff` | Un zéro non trivial n'est pas fixe par la réflexion-conjugaison si et seulement si sa partie réelle est différente de 1/2. | CONFIRMÉE | V162,V65 | 21 |
| `reflectConjZero_zeroHeight` | La hauteur du réfléchi-conjugué d'un zéro non trivial égale la hauteur de ce zéro. | CONFIRMÉE | V65,V63 | 15 |
| `reflectConjZero_multiplicity` | La multiplicité analytique de zêta au réfléchi-conjugué d'un zéro non trivial égale celle du zéro. | CONFIRMÉE | V65,V63 | 11 |
| `reflectConjZero_mem_heightConstellation` | Le réfléchi-conjugué d'un zéro non trivial appartient à la constellation de hauteur T si et seulement si le zéro y appartient. | CONFIRMÉE | V65,V63 | 15 |
| `heightConstellation_image_reflectConjZero` | L'image de la constellation des hauteurs T par la réflexion-conjugaison est la constellation elle-même. | CONFIRMÉE | V63 | 1 |
| `sum_reflectConjZero` | Une somme sur la constellation de f précomposée par la réflexion-conjugaison égale la somme de f. | CONFIRMÉE | V63 | 0 |
| `heightConstellation_reflection_trivial_iff_critical_line` | Tous les membres de la constellation T sont fixes par la réflexion-conjugaison si et seulement si tous sont de partie réelle 1/2. | CONFIRMÉE | V161 | 0 |
| `zeroHeight_injOn_of_critical_line` | Si tous les zéros d'un ensemble fini S sont de partie réelle 1/2, la hauteur est injective sur S. | CONFIRMÉE SOUS CONDITION (S entièrement sur la ligne critique) | V161,V8 | 2 |
| `card_image_zeroHeight_eq_of_critical_line` | Si tous les zéros d'un ensemble fini S sont sur la ligne critique, le nombre de hauteurs distinctes de S égale le cardinal de S. | CONFIRMÉE SOUS CONDITION (S entièrement sur la ligne critique) | V161,V8 | 2 |
| `card_image_zeroHeight_lt_of_offline_member` | Si un ensemble fini S est stable par réflexion-conjugaison et contient un zéro hors ligne critique, le nombre de hauteurs distinctes est strictement inférieur à son cardinal. | CONFIRMÉE SOUS CONDITION (S stable par réflexion-conjugaison et contenant un membre hors ligne critique) | V62,V162 | 3 |
| `no_comparable_constellations_differing_only_by_off_line_membership` | Il n'existe pas d'ensemble S sur la ligne critique et d'ensemble T' stable par réflexion contenant un membre hors ligne, de même cardinal et de mêmes hauteurs. | RÉFUTATION COMPILÉE (deux constellations comparables de même cardinal et mêmes hauteurs, l'une sur la ligne, l'autre stable par réflexion avec un membre hors ligne) | V162,V161 | 1 |
| `no_on_line_constellation_comparable_to_offline_heightConstellation` | Aucun ensemble S sur la ligne critique n'a même cardinal et mêmes hauteurs que la constellation T contenant un membre hors ligne. | RÉFUTATION COMPILÉE (un ensemble sur la ligne critique comparable à une constellation contenant un membre hors ligne) | V162,V161 | 1 |
| `not_comparableOffLineConstellationPairExists` | Si la constellation T contient un membre hors ligne critique, aucune paire de constellations comparables hors ligne n'existe pour T. | RÉFUTATION COMPILÉE (l'existence d'une paire de constellations comparables hors ligne pour T, sous hypothèse de membre hors ligne) | V162,V161 | 0 |
| `card_image_zeroHeight_eq_iff_critical_line` | Le nombre de hauteurs distinctes de la constellation T égale son cardinal si et seulement si tous ses membres sont sur la ligne critique. | CONFIRMÉE | V161,V162 | 2 |
| `card_image_zeroHeight_lt_iff_offline_member` | Le nombre de hauteurs distinctes de la constellation T est strictement inférieur à son cardinal si et seulement si elle contient un membre hors ligne critique. | CONFIRMÉE | V162,V161 | 0 |
| `exists_mem_heightConstellation` | Tout zéro non trivial appartient à la constellation de hauteur /Im ρ/ + 1. | CONFIRMÉE | AJOUT | 2 |
| `all_height_card_equal_iff_global_critical_line` | Pour toute hauteur T, le nombre de hauteurs distinctes de la constellation égale son cardinal si et seulement si tout zéro non trivial est de partie réelle 1/2. | ÉQUIVALENTE À RH (le membre droit est l'énoncé de RiemannHypothesis pour les zéros non triviaux) | V161,V162 | 1 |

### `RhGapCriterion.Round26B4DiscreteVariationIdentity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `grammarVariation_partial_sum` | La somme partielle des variations de grammaire sur m pas égale poids(n,m) moins poids(n,0). | CONFIRMÉE | AJOUT | 2 |
| `grammarVariation_partial_sum_abs_le` | La valeur absolue de toute somme partielle de variations de grammaire est au plus 2. | CONFIRMÉE | AJOUT | 1 |
| `grammarVariation_abs_le_two` | La valeur absolue de toute variation de grammaire est au plus 2. | CONFIRMÉE | AJOUT | 1 |
| `grammarVoiceRow_linear_form` | La ligne de voix de grammaire de ρ est un terme de bord de sortie moins une somme de termes intérieurs pondérés par la variation discrète moins un terme de bord d'entrée (sommation d'Abel). | CONFIRMÉE | AJOUT | 3 |
| `_private.RhGapCriterion.Round26B4DiscreteVariationIdentity.0.grammarWeight_abs_le_one` | La valeur absolue du poids de grammaire est au plus 1. | CONFIRMÉE | AJOUT | 1 |
| `grammarVoiceRow_norm_le` | La norme de la ligne de voix de grammaire est majorée par la norme du terme de sortie plus 2 fois la somme des normes des termes intérieurs plus la norme du terme d'entrée. | CONFIRMÉE | V102 | 1 |
| `grammarVoiceRow_norm_le_trivial_size` | Si tous les termes résiduels de ρ aux p(n+m), m ≤ K, sont de norme au plus M, la norme de la ligne de voix est au plus (2K+2) M. | CONFIRMÉE (domaine : termes résiduels de norme majorée par M pour m ≤ K) | AJOUT | 0 |

### `RhGapCriterion.Round26B4ForwardRecurrenceAttempt`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `scale_four_canonical_grammar_pair_cross_eq_product_form` | Pour x ≥ 0, la somme croisée des classes de paires de grammaire canonique aux échelles x et x/4 égale un produit de la forme (D(x) - bord)(D(x/4) - bord précédent), avec bords de valeur absolue au plus 1. | CONFIRMÉE (0 ≤ x) | AJOUT | 1 |
| `delta4FullATCumulative_exp_eq_critical` | La cumulée delta4 en e^U égale e^(U/2) fois la quantité critique criticalDelta4U en U. | CONFIRMÉE | AJOUT | 2 |
| `delta4FullATCumulative_exp_div_four_eq_critical` | La cumulée delta4 en e^U/4 égale e^((U - log 4)/2) fois criticalDelta4U en U - log 4. | CONFIRMÉE | AJOUT | 1 |
| `normalized_delta4_cross_eq_critical_cross` | La somme croisée normalisée à l'échelle U égale (1/2) criticalDelta4U(U) criticalDelta4U(U - log 4) à des termes de bord près de taille e^(-U/2) et e^(-U). | CONFIRMÉE (0 ≤ e^U, toujours vrai) | AJOUT | 1 |
| `normalized_delta4_cross_eq_critical_cross_shifted` | Même identité de somme croisée normalisée, décalée de log 4 (échelle U + log 4). | CONFIRMÉE (0 ≤ e^(U + log 4), toujours vrai) | AJOUT | 0 |
| `scaleBlockIndex_four_mul_disjoint` | Les blocs d'échelle en 4x et en x sont disjoints. | CONFIRMÉE | AJOUT | 1 |
| `chebyshev_error_two_sided_elementary` | Pour x ≥ 1, x - θ(x) est encadré : (1 - log 4) x ≤ x - θ(x) ≤ x - (x-1) log 2 + log(x+2) + 2 √x log x. | CONFIRMÉE (1 ≤ x) | AJOUT | 1 |
| `elementary_bound_lower_side_normalized_is_exponential` | Pour U ≥ 0, (1 - log 4) e^(U/2) ≤ e^(-U/2) (e^U - θ(e^U)). | CONFIRMÉE (0 ≤ U) | AJOUT | 0 |
| `gramWeight_R_sq_le_VTkernel_aT` | Si X ≤ p(N+1) et j < N, un terme gramWeight(X,j) R(j+1)^2 est majoré par le noyau VTkernel aT X N. | CONFIRMÉE (domaine : X ≤ p(N+1) et j dans range N) | AJOUT | 0 |
| `scaleBlockInnovationSum_four_mul_add_self_eq_wide_annulus_add_boundary` | La différence cumulée sur la fenêtre large (x/4, 4x] égale la somme des deux sommes d'innovation de blocs adjacents plus un bord de valeur absolue au plus 2. | CONFIRMÉE (0 ≤ x) | AJOUT | 1 |
| `delta4FullATCumulative_four_mul_add_self_eq_wide_window` | La somme delta4 aux échelles 4x et x égale la différence cumulée sur la fenêtre large (x/4, 4x]. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Round26B4GlobalPrimeLawConstructiveAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RhGapCriterion.one_sub_cos_nonneg` | Pour tout réel x, 1 - cos x est positif ou nul. | CONFIRMÉE | AJOUT | 2 |
| `RhGapCriterion.weightedCosineCertificate_nonneg` | Un certificat de cosinus pondéré, sur un ensemble fini à poids positifs ou nuls, est positif ou nul. | CONFIRMÉE (domaine : poids positifs ou nuls) | AJOUT | 1 |
| `RhGapCriterion.pairedCosineContribution_nonneg` | La contribution 2(1 - cos(nθ)) est positive ou nulle. | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.globalLaw_of_positiveMeasureRepresentation` | Si L n égale le certificat de cosinus pondéré pour tout n et les poids sont positifs ou nuls, alors L n ≥ 0 pour tout n. | CONFIRMÉE SOUS CONDITION (poids positifs ou nuls et L représentée par le certificat pondéré) | AJOUT | 0 |
| `RhGapCriterion.sum_range_succ_sub` | La somme des différences b(k+1) - b(k) sur range N vaut b(N) - b(0). | CONFIRMÉE | AJOUT | 2 |
| `RhGapCriterion.block_boundary_decomposition` | Si c k = b(k+1) - b(k) + r k pour k < N, alors la somme des c égale b(N) - b(0) plus la somme des r. | CONFIRMÉE (domaine : décomposition c k = b(k+1) - b k + r k pour tout k < N) | AJOUT | 1 |
| `RhGapCriterion.block_sum_nonneg_of_boundary_and_residual` | Si c k = b(k+1) - b k + r k pour k < N, b 0 ≤ b N et r k ≥ 0, alors la somme des c est positive ou nulle. | CONFIRMÉE (domaine : décomposition frontière-résidu, b 0 ≤ b N, résidus positifs) | AJOUT | 0 |
| `RhGapCriterion.sum_forwardDiff` | La somme des différences avant d'une suite a sur range N vaut a N - a 0. | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.list_sum_eq_of_perm` | Deux listes de réels permutées ont la même somme. | CONFIRMÉE (xs et ys permutées) | AJOUT | 0 |
| `RhGapCriterion.orderBlindPredicate_invariant` | Un prédicat portant sur la somme d'une liste est invariant par permutation de la liste. | CONFIRMÉE (xs et ys permutées) | AJOUT | 0 |
| `RhGapCriterion.positionIndependentCertificate_invariant` | Une somme d'une valeur fonction des éléments d'une liste est invariante par permutation de la liste. | CONFIRMÉE (xs et ys permutées) | AJOUT | 0 |
| `RhGapCriterion.twoBlockScore_sub_swapped` | Le score à deux blocs moins le score à blocs échangés vaut a (P(x+d) - P(x+d+e)) - b (P(x+e) - P(x+d+e)). | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.twoBlockScore_sub_swapped_affine` | Pour un noyau affine, le score à deux blocs moins le score échangé vaut a e - b d. | CONFIRMÉE | AJOUT | 1 |
| `RhGapCriterion.affine_real_order_preferred_iff` | Pour un noyau affine, le score échangé est majoré par le score à deux blocs si et seulement si b d ≤ a e. | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.finiteRegularizedScore_succ_sub` | L'incrément du score régularisé fini de n à n+1 égale la différence de tendance moins la somme pondérée des incréments de P moins l'incrément de L. | CONFIRMÉE | AJOUT | 2 |
| `RhGapCriterion.finiteRegularizedScore_mono_step` | Si l'incrément pondéré de P plus l'incrément de L est majoré par l'incrément de tendance, le score régularisé fini est croissant de n à n+1. | CONFIRMÉE (domaine : majoration de l'incrément pondéré par l'incrément de tendance) | AJOUT | 0 |
| `RhGapCriterion.logarithmicOrderMargin_succ_sub` | L'incrément de la marge d'ordre logarithmique de N à N+1 vaut step N moins l'incrément de log log θ. | CONFIRMÉE | AJOUT | 1 |
| `RhGapCriterion.logarithmicOrderMargin_succ_le_iff` | La marge d'ordre logarithmique décroît de N à N+1 si et seulement si step N ≤ log log θ(N+1) - log log θ(N). | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.nonneg_of_antitone_tendsto_zero` | Une suite réelle antitone tendant vers 0 est positive ou nulle en tout n. | CONFIRMÉE (domaine : u antitone et tendant vers 0) | AJOUT | 1 |
| `RhGapCriterion.pos_of_strictAnti_tendsto_zero` | Une suite réelle strictement antitone tendant vers 0 est strictement positive en tout n. | CONFIRMÉE (domaine : u strictement antitone et tendant vers 0) | AJOUT | 0 |

### `RhGapCriterion.Round26B4GlobalPrimeLawLaguerreReduction`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RhGapCriterion.finiteRegularizedScore_succ_sub_of_kernel_relations` | Sous les relations de noyau P(n+1) y - P n y = L n y et L(n+1) X - L n X = -(X/(n+1)) P(n+1) X, l'incrément du score régularisé se réécrit en termes du noyau L. | CONFIRMÉE (domaine : relations de noyau entre P et L) | AJOUT | 2 |
| `RhGapCriterion.finiteRegularizedScore_mono_of_kernel_domination` | Sous les relations de noyau et une domination de la somme pondérée de L n par l'incrément de tendance plus X/(n+1) P(n+1) X, le score régularisé fini est croissant de n à n+1. | CONFIRMÉE (domaine : relations de noyau et domination du noyau) | AJOUT | 1 |
| `RhGapCriterion.nonneg_limit_of_finite_nonneg` | Si u N ≥ 0 pour tout N et u tend vers a, alors a ≥ 0. | CONFIRMÉE (domaine : u N ≥ 0 pour tout N et u tend vers a) | AJOUT | 1 |
| `RhGapCriterion.nonneg_limit_of_eventually_nonneg` | Si u N ≥ 0 pour N assez grand et u tend vers a, alors a ≥ 0. | CONFIRMÉE (domaine : u N ≥ 0 à partir d'un rang et u tend vers a) | AJOUT | 1 |
| `RhGapCriterion.nonneg_from_four_of_mono` | Si u 4 ≥ 0 et u est croissante à partir de 4, alors u n ≥ 0 pour tout n ≥ 4. | CONFIRMÉE (domaine : u 4 ≥ 0 et croissance pour n ≥ 4) | AJOUT | 2 |
| `RhGapCriterion.limit_nonneg_from_finite_four_and_mono` | Si F 4 N ≥ 0 pour tout N, F n N ≤ F (n+1) N pour n ≥ 4 et F n N tend vers a n, alors a n ≥ 0 pour n ≥ 4. | CONFIRMÉE (domaine : positivité en 4, croissance en n, convergence en N) | AJOUT | 0 |
| `RhGapCriterion.limit_nonneg_from_eventual_finite_four_and_mono` | Même conclusion a n ≥ 0 pour n ≥ 4 avec positivité en 4 et croissance en n valables seulement pour N assez grand. | CONFIRMÉE (domaine : positivité en 4 et croissance en n éventuelles, convergence en N) | AJOUT | 1 |
| `RhGapCriterion.all_nonneg_of_first_four_and_tail` | Si a 0, a 1, a 2, a 3 sont positifs ou nuls et a n ≥ 0 pour n ≥ 4, alors a n ≥ 0 pour tout n. | CONFIRMÉE (domaine : a 0 à a 3 positifs et queue positive) | AJOUT | 0 |

### `RhGapCriterion.Round26B4GlobalPrimeLawLowDegree`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RhGapCriterion.recursiveLaguerreL_two` | Le polynôme de Laguerre récursif L_2(x) vaut 1 - 2x + x^2/2. | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.recursiveLaguerreP_three` | Le polynôme récursif P_3(x) vaut 3 - 3x + x^2/2. | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.recursiveLaguerreL_three` | Le polynôme de Laguerre récursif L_3(x) vaut 1 - 3x + 3x^2/2 - x^3/6. | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.recursiveLaguerreP_four` | Le polynôme récursif P_4(x) vaut 4 - 6x + 2x^2 - x^3/6. | CONFIRMÉE | AJOUT | 1 |
| `RhGapCriterion.recursiveLaguerreL_four` | Le polynôme de Laguerre récursif L_4(x) vaut 1 - 4x + 3x^2 - 2x^3/3 + x^4/24. | CONFIRMÉE | AJOUT | 2 |
| `RhGapCriterion.finitePrimeLaguerreScore_four_eq` | Le score de Laguerre premier fini de degré 4 se réécrit comme la tendance en 4 moins une somme explicite pondérée en les positions de premiers plus un terme en log N. | CONFIRMÉE | AJOUT | 1 |
| `RhGapCriterion.finitePrimeLaguerreScore_five_sub_four` | La différence des scores de Laguerre premiers finis de degrés 5 et 4 se réécrit comme différence de tendance moins une somme explicite pondérée en les positions premières. | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.finitePrimeLaguerreScore_four_nonneg_iff` | Le score de Laguerre premier fini de degré 4 est positif ou nul si et seulement si une somme explicite pondérée plus un terme en log N est majorée par la tendance. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Round26B4GlobalPrimeLawPointwiseStaircase`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RhGapCriterion.eventually_nonneg_of_pointwise_eventual_staircase` | Si F 4 N ≥ 0 pour N assez grand et si, pour tout n ≥ 4, F n N ≤ F (n+1) N pour N assez grand, alors pour tout n ≥ 4, F n N ≥ 0 pour N assez grand. | CONFIRMÉE (domaine : positivité éventuelle en 4 et croissance éventuelle en n) | AJOUT | 1 |
| `RhGapCriterion.limit_nonneg_from_pointwise_eventual_staircase` | Même hypothèse d'escalier ponctuel éventuel plus convergence de F n N vers a n : a n ≥ 0 pour tout n ≥ 4. | CONFIRMÉE (domaine : positivité en 4, croissance en n éventuelles, convergence en N) | AJOUT | 1 |
| `RhGapCriterion.eventually_nonneg_of_pos_limit` | Si u tend vers a > 0, alors u N ≥ 0 pour N assez grand. | CONFIRMÉE (domaine : u tend vers a et a > 0) | AJOUT | 0 |
| `RhGapCriterion.eventually_le_of_lt_limits` | Si u tend vers a, v tend vers b et a < b, alors u N ≤ v N pour N assez grand. | CONFIRMÉE (domaine : limites a < b) | AJOUT | 0 |
| `RhGapCriterion.le_of_eventually_le_limits` | Si u N ≤ v N pour N assez grand et u tend vers a, v vers b, alors a ≤ b. | CONFIRMÉE (domaine : u N ≤ v N éventuellement, convergences) | AJOUT | 0 |
| `RhGapCriterion.canonicalPrimeLaguerreLimit_nonneg_of_eventual_staircase` | Si les prédicats nommés PrimeLaguerreBaseFourEventually, PrimeLaguerreStepEventually et CanonicalPrimeLaguerreLimit a sont vérifiés, alors a n ≥ 0 pour tout n ≥ 4. | CONFIRMÉE (domaine : bases éventuelle et pas éventuel de Laguerre premier et limite canonique a) | AJOUT | 0 |
| `RhGapCriterion.primeLaguerreBaseFourEventually_of_universal` | Le prédicat PrimeLaguerreBaseFour universel implique sa forme éventuelle PrimeLaguerreBaseFourEventually. | CONFIRMÉE (domaine : PrimeLaguerreBaseFour) | AJOUT | 0 |
| `RhGapCriterion.primeLaguerreStepEventually_of_domination` | Le prédicat PrimeLaguerreDomination implique PrimeLaguerreStepEventually. | CONFIRMÉE (domaine : PrimeLaguerreDomination) | AJOUT | 0 |

### `RhGapCriterion.Round26B4GlobalPrimeLawPositiveMeasureObstruction`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RhGapCriterion.one_sub_cos_le_two` | Pour tout réel x, 1 - cos x est majoré par 2. | CONFIRMÉE | AJOUT | 1 |
| `RhGapCriterion.weightedCosineCertificate_le_two_mul_sum` | Pour tout ensemble fini de poids positifs, le certificat cosinus pondéré à l'indice n est majoré par deux fois la masse totale des poids. | CONFIRMÉE (poids positifs ou nuls) | AJOUT | 1 |
| `RhGapCriterion.fixedPositiveMeasureRepresentation_uniformlyBounded` | Si une suite L est représentée pour tout n par un certificat cosinus pondéré à poids positifs fixé, alors L n est majorée par 2 fois la masse des poids, uniformément en n. | CONFIRMÉE SOUS CONDITION (poids positifs et suite égale au certificat pour tout n) | AJOUT | 1 |
| `RhGapCriterion.no_fixedPositiveMeasureRepresentation_of_unbounded` | Une suite L non bornée (pour tout C il existe n avec C < L n) n'est pas égale, pour tout n, à un certificat cosinus pondéré à poids positifs fixé. | RÉFUTATION COMPILÉE (représentation d'une suite non bornée par une mesure positive finie fixe) | AJOUT | 0 |

### `RhGapCriterion.Round26B4GlobalPrimeLawRecursiveLaguerre`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RhGapCriterion.recursiveLaguerreL_zero` | Le noyau de Laguerre récursif ordinaire d'indice 0 vaut 1 en tout x. | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.recursiveLaguerreP_one` | Le noyau de Laguerre récursif associé d'indice 1 vaut 1 en tout x. | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.recursiveLaguerreP_succ_sub` | Le noyau associé d'indice n+1 moins celui d'indice n égale le noyau ordinaire d'indice n, en tout x. | CONFIRMÉE | AJOUT | 2 |
| `RhGapCriterion.recursiveLaguerreL_succ_sub` | Le noyau ordinaire d'indice n+1 moins celui d'indice n égale moins x/(n+1) fois le noyau associé d'indice n+1. | CONFIRMÉE | AJOUT | 2 |
| `RhGapCriterion.recursiveLaguerreL_one` | Le noyau ordinaire d'indice 1 vaut 1 - x (normalisation de Laguerre standard). | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.recursiveLaguerreP_two` | Le noyau associé d'indice 2 vaut 2 - x. | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.recursiveLaguerreScore_succ_sub` | Récurrence exacte du score régularisé fini (noyaux de Laguerre récursifs) : la différence des scores aux indices n+1 et n vaut la différence des tendances moins la somme pondérée du noyau ordinaire plus X/(n+1) fois le noyau associé en X. | CONFIRMÉE | AJOUT | 1 |
| `RhGapCriterion.recursiveLaguerreScore_mono_of_domination` | Si la somme pondérée du noyau ordinaire est majorée par l'écart de tendance plus X/(n+1) fois le noyau associé, alors le score récursif à l'indice n est majoré par celui à l'indice n+1. | CONFIRMÉE (domaine : inégalité de domination concrète) | AJOUT | 1 |

### `RhGapCriterion.Round26B4GlobalPrimeLawTrend`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RhGapCriterion.canonicalFinitePrimeLaguerreScore_eq` | Le score canonique fini de Laguerre sur les premiers vaut la tendance archimédienne moins (somme sur m de 1 à N du poids fois le noyau associé plus le noyau ordinaire en log N moins 1). | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.canonicalFinitePrimeLaguerreScore_succ_sub` | Identité exacte des accroissements successifs (indice n+1 moins n) du score canonique fini, sans paramètre abstrait restant. | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.canonicalPrimeLaguerreLimit_nonneg` | Si les deux obligations finies (base en indice quatre et domination) tiennent et que le score canonique converge vers a n pour tout n, alors a n est positif ou nul dès l'indice 4. | CONFIRMÉE (domaine : base en indice quatre, domination, identité de limite) | AJOUT | 0 |

### `RhGapCriterion.Round26B4GlobalPrimeLawVonMangoldt`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RhGapCriterion.primeLaguerreWeight_nonneg` | Les poids de von Mangoldt normalisés sont positifs ou nuls pour tout m. | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.finitePrimeLaguerreScore_eq` | Le score fini de Laguerre côté premiers se développe exactement comme tendance moins (somme pondérée plus noyau ordinaire en log N moins 1). | CONFIRMÉE | AJOUT | 2 |
| `RhGapCriterion.finitePrimeLaguerreSum_eq_primePower_filter` | La somme finie sur 1..N des poids fois noyau associé est égale à la même somme restreinte aux puissances de nombres premiers (les autres termes sont nuls). | CONFIRMÉE | AJOUT | 0 |
| `RhGapCriterion.finitePrimeLaguerreScore_succ_sub` | Formule exacte d'accroissement (indice n+1 moins n) du score fini de Laguerre côté premiers, avec tendance générique. | CONFIRMÉE | AJOUT | 2 |
| `RhGapCriterion.finitePrimeLaguerreScore_mono_of_domination` | Si la somme pondérée du noyau ordinaire est majorée par l'écart de tendance plus (log N)/(n+1) fois le noyau associé, alors le score fini est croissant de l'indice n à n+1. | CONFIRMÉE (domaine : inégalité de domination en (n,N)) | AJOUT | 2 |
| `RhGapCriterion.primeLaguerreLimit_nonneg_from_base_four_and_domination` | Clôture abstraite : si le score fini à l'indice 4 est positif pour N au moins 2, si la domination tient pour N au moins 2 et n au moins 4, et si le score converge vers a n, alors a n est positif ou nul pour n au moins 4. | CONFIRMÉE (domaine : positivité en indice 4, domination, convergence) | AJOUT | 1 |

### `RhGapCriterion.Round26B4GrammarSpectralClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `offlineOrbitThetaPart.congr_simp` | Lemme de congruence auto-généré : la partie thêta hors-orbite du zéro dépend seulement de l'égalité des zéros et des réels x égaux. | CONFIRMÉE (lemme congr_simp auto-généré) | AJOUT | 0 |
| `offlineRestThetaPart.congr_simp` | Lemme de congruence auto-généré : la partie thêta du reste pour un zéro dépend seulement de l'égalité des zéros et des réels x égaux. | CONFIRMÉE (lemme congr_simp auto-généré) | AJOUT | 0 |
| `mem_activeGramWindow_iff` | Un indice j appartient à la fenêtre de Gram active (r,U) si et seulement s'il est inférieur à l'horizon T canonique de U et si son poids de fenêtre de Gram est non nul. | CONFIRMÉE | AJOUT | 1 |
| `gramWindowWeight_pos_of_mem_active` | Pour r au moins 1, tout indice de la fenêtre de Gram active a un poids de fenêtre strictement positif. | CONFIRMÉE (r au moins 1) | AJOUT | 0 |
| `weighted_cauchy_schwarz_gram` | Cauchy-Schwarz pondéré fini : la norme au carré de la somme des c_i y_i est majorée par (somme des norme c_i au carré divisé par w_i) fois la somme des w_i fois norme y_i au carré. | CONFIRMÉE (poids strictement positifs) | AJOUT | 0 |
| `thetaScaleFourDefectReal_eq_affine_sub_orbit_rest_thetaScaleFour` | Pour un zéro non trivial ρ et t au moins 2 (t/4 au moins 2), le défaut thêta réel à l'échelle quatre vaut 3t/4 moins la partie d'orbite du zéro moins la partie de reste. | CONFIRMÉE (ρ zéro non trivial, t au moins 2 et t/4 au moins 2) | AJOUT | 0 |
| `R_eq_P5_orbit_add_rest_sub_correction` | Pour un zéro non trivial ρ et m au moins 1, le signal R m vaut la contribution d'orbite P5 du zéro plus le terme de reste moins la correction de Tchebychev. | CONFIRMÉE (ρ zéro non trivial, m au moins 1) | AJOUT | 2 |
| `fullATCumulative_at_prime_eq_P5_orbit_add_rest_sub_correction` | Même pont P5 écrit dans la coordonnée cumulative fullATCumulative évaluée au premier p m. | CONFIRMÉE (ρ zéro non trivial, m au moins 1) | AJOUT | 1 |
| `delta4_fullATCumulative_at_prime_eq_P5_orbit_add_rest_sub_correction` | La différence de fullATCumulative entre p m et p m/4 vaut la contribution d'orbite P5 plus le reste moins la correction de Tchebychev moins fullATCumulative(p m/4). | CONFIRMÉE (ρ zéro non trivial, m au moins 1) | AJOUT | 0 |
| `P5_R_bridge_and_zero_reconstructed_grammar_partition` | Pour un zéro non trivial ρ, m au moins 1 et r au moins 1 : R m égale contribution P5 plus reste moins correction, et la somme des énergies de classes de grammaire reconstruites depuis les zéros égale l'énergie normalisée de la fenêtre R. | CONFIRMÉE (ρ zéro non trivial, m au moins 1, r au moins 1) | AJOUT | 0 |
| `explicitFormulaProjectedChannel_eq_perronResidueProjection` | Le canal projeté de la formule explicite pour un zéro ρ est exactement la projection de résidu de Perron locale de l'intégrande de Perron non lissé. | CONFIRMÉE | AJOUT | 1 |
| `perronResidueProjection_eq_P5_zeroMode` | La projection de résidu de Perron d'un zéro est égale au mode de zéro P5 (zeroMode) d'amplitude de la formule explicite. | CONFIRMÉE | AJOUT | 0 |
| `continuousAt_psiScaleFourBoundaryOneToFour` | Le terme de bord compact [1,4] du changement de variable psi à l'échelle quatre est continu en tout paramètre de Mellin ρ. | CONFIRMÉE | AJOUT | 1 |
| `psiScaleFourBoundaryOneToFour_residue_zero_of_continuousAt` | Si le terme de bord compact est continu en ρ, alors (z-ρ) fois ce terme tend vers 0 quand z tend vers ρ (résidu nul). | CONFIRMÉE (domaine : continuité locale du terme de bord en ρ) | AJOUT | 1 |
| `residue_scaleFourThetaMellinContinuation_of_boundary_vanishing` | Pour un zéro non trivial ρ de partie réelle supérieure à 1/2, si le terme de bord a résidu nul en ρ, alors le résidu de la continuation de Mellin thêta à l'échelle quatre en ρ égale l'amplitude thêta canonique. | CONFIRMÉE SOUS CONDITION (résidu nul du terme de bord en ρ; ρ zéro non trivial avec Re ρ > 1/2) | AJOUT | 1 |
| `residue_scaleFourThetaMellinContinuation` | Pour un zéro non trivial ρ avec Re ρ > 1/2, le résidu de la continuation de Mellin thêta à l'échelle quatre en ρ égale l'amplitude thêta canonique du zéro. | CONFIRMÉE (ρ zéro non trivial avec Re ρ > 1/2) | AJOUT | 1 |
| `residue_scaleFourThetaMellinContinuation_eq_factor_mul_P5` | Pour un zéro non trivial ρ avec Re ρ > 1/2, le même résidu vaut -(1 - 4^(-ρ)) fois l'amplitude de la formule explicite du zéro (facteur P5). | CONFIRMÉE (ρ zéro non trivial avec Re ρ > 1/2) | AJOUT | 0 |
| `exp_log_four_eigenvalue` | Pour tout complexe ρ, exp((ρ - 1/2) log 4) égale 4^(ρ - 1/2). | CONFIRMÉE | AJOUT | 2 |
| `canonicalThetaZeroMode_scale_four` | Le mode thêta de zéro canonique se décale de log 4 en U en se multipliant par la valeur propre 4^(ρ - 1/2). | CONFIRMÉE | AJOUT | 2 |
| `criticalDelta4U_shift_log_four` | Décalage de log 4 dans criticalDelta4U : criticalDelta4U(U - log 4) égale exp(-(U - log 4)/2) fois delta4FullATCumulative(exp U/4). | CONFIRMÉE | AJOUT | 0 |
| `scaleFourState_shift` | L'état à l'échelle quatre au point x/4 est la paire (delta4FullATCumulative(x/4), delta4FullATCumulative(x/16)). | CONFIRMÉE | AJOUT | 0 |
| `scaleStateQ_shift` | scaleStateQ(x/4) égale delta4FullATCumulative(x/4) au carré plus delta4FullATCumulative(x/16) au carré. | CONFIRMÉE | AJOUT | 0 |
| `delta4FullATCumulative_add_next` | fullATCumulative(x) moins fullATCumulative(x/16) égale delta4FullATCumulative(x) plus delta4FullATCumulative(x/4). | CONFIRMÉE | AJOUT | 0 |
| `scale_four_canonical_grammar_pair_cross_reindexed` | Repartition exacte de la partition en classes de paires de grammaire canoniques, par réindexation à l'échelle quatre : la somme sur les classes du produit des innovations J vaut le produit des sommes d'innovation par bloc d'échelle en x et x/4. | CONFIRMÉE | AJOUT | 1 |
| `scale_four_canonical_grammar_pair_cross_eq_polarized_endpoints` | Pour x positif ou nul, la somme croisée par classes de paires de grammaire canoniques égale un demi de (différence des cumulatives)^2 moins deux carrés analogues, corrigé par deux termes de bord bornés par 1 (polarisation des extrémités fullATCumulative). | CONFIRMÉE (x positif ou nul; conclusion existentielle sur deux bords bornés par 1) | AJOUT | 1 |
| `scale_four_canonical_grammar_pair_cross_eq_delta4_state` | Même polarisation, exprimée sur l'état à deux coordonnées (delta4FullATCumulative en x et x/4), avec deux termes de bord bornés par 1. | CONFIRMÉE (x positif ou nul; conclusion existentielle sur deux bords bornés par 1) | AJOUT | 1 |
| `scale_four_m49_cross_term_eq_normalized_vtkernel_polarization` | Le terme croisé fenêtré normalisé M49 est égal, pour tout triplet de signaux a,b,c, à une polarisation finie de noyaux VT sur les différences a-c, a-b, b-c. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Round26B4GrammarSpectralSectors`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `card_Transform6` | Le type fini Transform6 a exactement 4 éléments. | CONFIRMÉE | AJOUT | 0 |
| `card_Transform6_prod` | Le type produit Transform6 x Transform6 a exactement 16 éléments. | CONFIRMÉE | AJOUT | 0 |
| `grammarClassOfPrimeValue_p` | En une valeur première canonique p n, la classification par valeur donne la transition linéaire p n mod 6 vers p(n+1) mod 6. | CONFIRMÉE | V174 | 1 |
| `sum_grammarPrimeIndicator_eq_primeIndicator` | Pour tout q, la somme sur les transformations de l'indicateur de secteur de grammaire premier égale l'indicateur des nombres premiers. | CONFIRMÉE | AJOUT | 2 |
| `grammarPotentialV2_prime_eq_zero_iff` | Pour n au moins 2, le potentiel de grammaire du premier p n mod 6 vaut 0 si et seulement si p n mod 6 vaut 1 (état B). | CONFIRMÉE (n au moins 2) | V174 | 0 |
| `grammarPotentialV2_prime_eq_one_iff` | Pour n au moins 2, le potentiel de grammaire du premier p n mod 6 vaut 1 si et seulement si p n mod 6 vaut 5 (état A). | CONFIRMÉE (n au moins 2) | V174 | 0 |
| `grammarTransformIndicator_tau11_eq` | Pour n au moins 2, l'indicateur de la transformation 1-vers-1 est le produit (1 - potentiel(p n mod 6)) fois (1 - potentiel(p(n+1) mod 6)). | CONFIRMÉE (n au moins 2) | V174 | 1 |
| `grammarTransformIndicator_tau15_eq` | Pour n au moins 2, l'indicateur de la transformation 1-vers-5 est (1 - potentiel(p n mod 6)) fois potentiel(p(n+1) mod 6). | CONFIRMÉE (n au moins 2) | V174 | 1 |
| `grammarTransformIndicator_tau51_eq` | Pour n au moins 2, l'indicateur de la transformation 5-vers-1 est potentiel(p n mod 6) fois (1 - potentiel(p(n+1) mod 6)). | CONFIRMÉE (n au moins 2) | V174 | 1 |
| `grammarTransformIndicator_tau55_eq` | Pour n au moins 2, l'indicateur de la transformation 5-vers-5 est le produit potentiel(p n mod 6) fois potentiel(p(n+1) mod 6). | CONFIRMÉE (n au moins 2) | V174 | 1 |
| `grammar_tau15_sub_tau51_eq_potential_coboundary` | Pour n au moins 2, indicateur(1-vers-5) moins indicateur(5-vers-1) égale potentiel(p(n+1) mod 6) moins potentiel(p n mod 6) (cobord). | CONFIRMÉE (n au moins 2) | AJOUT | 7 |
| `grammar_tau15_add_tau51_eq_cross` | Pour n au moins 2, indicateur(1-vers-5) plus indicateur(5-vers-1) égale le terme croisé grammarCrossV2 de (p n mod 6, p(n+1) mod 6). | CONFIRMÉE (n au moins 2) | AJOUT | 5 |
| `grammar_tau15_eq_cross_add_coboundary_half` | Pour n au moins 2, l'indicateur 1-vers-5 vaut (croisé plus cobord)/2. | CONFIRMÉE (n au moins 2) | AJOUT | 1 |
| `grammar_tau51_eq_cross_sub_coboundary_half` | Pour n au moins 2, l'indicateur 5-vers-1 vaut (croisé moins cobord)/2. | CONFIRMÉE (n au moins 2) | AJOUT | 1 |
| `grammar_tau11_add_tau15_eq_one_sub_potential` | Pour n au moins 2, indicateur(1-vers-1) plus indicateur(1-vers-5) égale 1 moins le potentiel de p n mod 6. | CONFIRMÉE (n au moins 2) | AJOUT | 1 |
| `grammar_tau51_add_tau55_eq_potential` | Pour n au moins 2, indicateur(5-vers-1) plus indicateur(5-vers-5) égale le potentiel de p n mod 6. | CONFIRMÉE (n au moins 2) | AJOUT | 1 |
| `four_transform_indicators_basis_decomposition` | Pour n au moins 2, les quatre indicateurs de transformation s'expriment dans la base (global, état, croisé, cobord) : 1-vers-5 et 5-vers-1 par croisé plus ou moins cobord sur 2, 1-vers-1 par 1 moins potentiel moins le premier de ces deux, et 5-vers-5 par le potentiel moins le second (conjonction; type tronqué à la source). | CONFIRMÉE (n au moins 2) | AJOUT | 0 |
| `grammarPrimeIndicator_at_p` | L'indicateur de secteur de grammaire premier évalué au premier p n est l'indicateur de transformation à l'indice n. | CONFIRMÉE | AJOUT | 0 |
| `p_index_le_prime_value` | Pour tout n, n est majoré par le n-ième premier p n. | CONFIRMÉE | AJOUT | 1 |
| `grammarTransformIndicator_abs_le_one` | La valeur absolue de l'indicateur de transformation est majorée par 1, pour toute transformation et tout n. | CONFIRMÉE | AJOUT | 1 |
| `grammarCrossV2_abs_le_one` | La valeur absolue du terme croisé grammarCrossV2 (s,t) est majorée par 1 pour tous s,t. | CONFIRMÉE | AJOUT | 1 |
| `sum_grammarTransformIndicator_eq_one` | Pour tout n, la somme sur les quatre transformations des indicateurs de transformation vaut 1. | CONFIRMÉE | AJOUT | 2 |
| `grammarSectorPrimeDirichlet_summable_re_gt_one` | Pour Re s > 1, la série n -> indicateur * log(p n) * p n ^ (-s) est sommable, pour chaque transformation. | CONFIRMÉE (Re s > 1) | AJOUT | 8 |
| `grammarSectorPrimeDirichlet_eq_tsum_weight` | La série de Dirichlet de secteur premier d'une transformation égale la somme infinie des indicateurs fois les poids de Dirichlet premiers. | CONFIRMÉE | AJOUT | 5 |
| `primeDirichletWeight_summable_re_gt_one` | Pour Re s > 1, la suite des poids de Dirichlet premiers est sommable. | CONFIRMÉE (Re s > 1) | AJOUT | 7 |
| `grammarSectorPrimeDirichlet_initial_tail_re_gt_one` | Pour Re s > 1, la série de Dirichlet de secteur égale sa partie initiale (indices 0 et 1) plus sa queue. | CONFIRMÉE (Re s > 1) | AJOUT | 1 |
| `grammarSectorPrimeDirichletInitial_explicit` | La partie initiale de la série de Dirichlet de secteur est explicitement indicateur(0) fois poids(0) plus indicateur(1) fois poids(1). | CONFIRMÉE | AJOUT | 1 |
| `grammarPrimeStateChi3_eq_one_iff` | Pour n au moins 2, l'état chi3 du premier p n vaut 1 si et seulement si p n mod 6 vaut 1. | CONFIRMÉE (n au moins 2) | V174 | 0 |
| `grammarPrimeStateChi3_eq_neg_one_iff` | Pour n au moins 2, l'état chi3 du premier p n vaut -1 si et seulement si p n mod 6 vaut 5. | CONFIRMÉE (n au moins 2) | V174 | 0 |
| `grammarPrimeStateChi3_sq` | Pour n au moins 2, le carré de l'état chi3 du premier p n vaut 1. | CONFIRMÉE (n au moins 2) | V174 | 1 |
| `grammarPrimeStateChi3_abs` | Pour n au moins 2, la valeur absolue de l'état chi3 du premier p n vaut 1. | CONFIRMÉE (n au moins 2) | V174 | 3 |
| `grammarCrossV2_eq_character_correlation` | Pour n au moins 2, le terme croisé de (p n mod 6, p(n+1) mod 6) égale (1 - chi3(n) chi3(n+1))/2, une corrélation de caractères consécutifs. | CONFIRMÉE (n au moins 2) | V174 | 2 |
| `grammarCross_weighted_character_correlation_term` | Pour n au moins 2 et tout s, le terme croisé fois le poids de Dirichlet en n égale (1 - chi3(n) chi3(n+1))/2 fois le poids. | CONFIRMÉE (n au moins 2) | AJOUT | 2 |
| `grammarCrossV2_eq_zero_iff_state_sign_eq` | Pour n au moins 2, le terme croisé de deux premiers consécutifs est nul si et seulement si leurs états chi3 sont égaux. | CONFIRMÉE (n au moins 2) | V174 | 0 |
| `grammarCrossV2_eq_one_iff_state_sign_ne` | Pour n au moins 2, le terme croisé est 1 si et seulement si les états chi3 des deux premiers consécutifs diffèrent. | CONFIRMÉE (n au moins 2) | V174 | 0 |
| `grammarPrimeStateChi3_mul_eq_one_iff_cross_zero` | Pour n au moins 2, le produit chi3(n) chi3(n+1) vaut 1 si et seulement si le terme croisé est nul. | CONFIRMÉE (n au moins 2) | V174 | 0 |
| `grammarPrimeStateChi3_mul_eq_neg_one_iff_cross_one` | Pour n au moins 2, le produit chi3(n) chi3(n+1) vaut -1 si et seulement si le terme croisé vaut 1. | CONFIRMÉE (n au moins 2) | V174 | 0 |
| `globalPrimeDirichletTail_summable_re_gt_one` | Pour Re s > 1, la queue globale (indices n+2) de la série de Dirichlet des poids premiers est sommable. | CONFIRMÉE (Re s > 1) | AJOUT | 1 |
| `consecutivePrimeCharacterCorrelation_summable_re_gt_one` | Pour Re s > 1, la série de corrélation de caractères entre premiers consécutifs, pondérée par le poids de Dirichlet, est sommable. | CONFIRMÉE (Re s > 1) | AJOUT | 1 |
| `grammarCrossPrimeDirichletTail_summable_re_gt_one` | Pour Re s > 1, la queue de Dirichlet du terme croisé de grammaire est sommable. | CONFIRMÉE (Re s > 1) | AJOUT | 3 |
| `finite_cross_tail_eq_global_tail_sub_character_correlation` | Somme finie sur n de 0 à N-1 : la queue croisée égale un demi de la queue globale moins un demi de la corrélation de caractères consécutifs. | CONFIRMÉE | AJOUT | 0 |
| `grammarCrossPrimeDirichletTail_eq_global_tail_sub_character_correlation_re_gt_one` | Pour Re s > 1, la queue de Dirichlet du terme croisé égale un demi de la queue globale moins un demi de la corrélation de caractères consécutifs. | CONFIRMÉE (Re s > 1) | AJOUT | 2 |
| `grammar_tau15_sub_tau51_weighted_term_eq_coboundary` | Pour n au moins 2, le terme pondéré (indicateur 1-vers-5 moins indicateur 5-vers-1) fois le poids égale la différence des potentiels fois le poids (cobord). | CONFIRMÉE (n au moins 2) | AJOUT | 2 |
| `grammar_tau15_add_tau51_weighted_term_eq_cross` | Pour n au moins 2, le terme pondéré (indicateur 1-vers-5 plus indicateur 5-vers-1) fois le poids égale le terme croisé fois le poids. | CONFIRMÉE (n au moins 2) | AJOUT | 2 |
| `transition_residue_weighted_cross_coboundary_term` | Pour n au moins 2, le résidu de transition pondéré vaut 3 fois le terme croisé pondéré plus la différence des potentiels pondérée. | CONFIRMÉE (n au moins 2) | AJOUT | 4 |
| `finite_weighted_coboundary_summation_by_parts` | Sommation par parties finie : la somme de 0 à N de (phi(n+1) - phi n) w n égale phi(N+1) w N - phi 0 w 0 plus la somme de 0 à N-1 de phi(n+1)(w n - w(n+1)). | CONFIRMÉE | AJOUT | 0 |
| `finite_tau15_sub_tau51_weighted_tail_eq_coboundary` | Somme finie sur n de 0 à N-1 (indices n+2) : la somme des termes pondérés (indicateur 1-vers-5 moins indicateur 5-vers-1) égale la somme des différences de potentiel pondérées. | CONFIRMÉE | AJOUT | 0 |
| `finite_tau15_add_tau51_weighted_tail_eq_cross` | Somme finie (indices n+2) : la somme des termes pondérés (1-vers-5 plus 5-vers-1) égale la somme des termes croisés pondérés. | CONFIRMÉE | AJOUT | 0 |
| `finite_transition_residue_weighted_tail_eq_cross_coboundary` | Somme finie (indices n+2) : la somme des résidus de transition pondérés égale la somme de 3 fois le croisé pondéré plus le cobord pondéré. | CONFIRMÉE | AJOUT | 0 |
| `transition_residue_weighted_cross_solved_term` | Pour n au moins 2, 3 fois le terme croisé pondéré égale le résidu de transition pondéré moins la différence de potentiels pondérée. | CONFIRMÉE (n au moins 2) | AJOUT | 0 |
| `grammarSectorPrimeDirichlet_tail_summable_re_gt_one` | Pour Re s > 1, la queue de la série de Dirichlet de secteur (indices n+2) est sommable, pour chaque transformation. | CONFIRMÉE (Re s > 1) | AJOUT | 2 |
| `grammarPotentialCoboundaryDirichletTail_summable_re_gt_one` | Pour Re s > 1, la queue de Dirichlet du cobord de potentiel est sommable. | CONFIRMÉE (Re s > 1) | AJOUT | 3 |
| `grammarTransitionResiduePrimeDirichletTail_summable_re_gt_one` | Pour Re s > 1, la queue de Dirichlet du résidu de transition est sommable. | CONFIRMÉE (Re s > 1) | AJOUT | 0 |
| `grammarTransitionResiduePrimeDirichletTail_eq_cross_coboundary_re_gt_one` | Pour Re s > 1, la queue de Dirichlet du résidu de transition égale 3 fois la queue croisée plus la queue du cobord de potentiel. | CONFIRMÉE (Re s > 1) | AJOUT | 1 |
| `grammarCrossPrimeDirichletTail_eq_transition_sub_coboundary_re_gt_one` | Pour Re s > 1, la queue croisée égale un tiers de (queue du résidu de transition moins queue du cobord de potentiel). | CONFIRMÉE (Re s > 1) | AJOUT | 0 |
| `transformation_conditioned_increment_weighted_cross_identity` | Pour n au moins 2 et tout complexe w, il existe un entier k tel que 3 fois le terme croisé fois w égale (Tmode(n+1) - Tmode n) w - 6k w + log(p n) w - (différence de potentiels) w. | CONFIRMÉE (n au moins 2) | AJOUT | 0 |
| `sector_tau15_from_cross_coboundary` | Pour tout vecteur v de secteurs, la composante 1-vers-5 vaut (coordonnée croisée + coordonnée de cobord)/2. | CONFIRMÉE | AJOUT | 3 |
| `sector_tau51_from_cross_coboundary` | Pour tout vecteur v de secteurs, la composante 5-vers-1 vaut (coordonnée croisée - coordonnée de cobord)/2. | CONFIRMÉE | AJOUT | 3 |
| `sector_tau55_from_state_cross_coboundary` | Pour tout vecteur v de secteurs, la composante 5-vers-5 vaut la coordonnée d'état moins (croisée - cobord)/2. | CONFIRMÉE | AJOUT | 2 |
| `sector_tau11_from_global_state_cross_coboundary` | Pour tout vecteur v de secteurs, la composante 1-vers-1 vaut coordonnée globale moins coordonnée d'état moins (croisée + cobord)/2. | CONFIRMÉE | AJOUT | 2 |
| `sector_tau15_eq_tau51_of_coboundary_zero` | Si la coordonnée de cobord d'un vecteur de secteurs est nulle, ses composantes 1-vers-5 et 5-vers-1 sont égales. | CONFIRMÉE (domaine : coordonnée de cobord nulle) | AJOUT | 3 |
| `sector_eq_of_basis_coords_eq` | Deux vecteurs de secteurs dont les quatre coordonnées de base (globale, état, croisée, cobord) coïncident sont égaux. | CONFIRMÉE (égalité des quatre coordonnées, injectivité) | AJOUT | 1 |
| `sector_eq_of_global_state_cross_eq_of_coboundary_zero` | Deux vecteurs de secteurs qui ont mêmes coordonnées globale, d'état et croisée et dont les cobords sont tous deux nuls sont égaux. | CONFIRMÉE (domaine : cobords nuls des deux vecteurs) | AJOUT | 0 |
| `sum_grammarPrimeCount_eq_piReal` | La somme sur les transformations des décomptes de premiers par secteur de grammaire égale le décompte réel π(x). | CONFIRMÉE | AJOUT | 0 |
| `hasSum_indicator_grammarSector_eq_theta` | Pour x positif ou nul, la somme (sur les entiers q inférieurs ou égaux à x) de log q fois l'indicateur de secteur a pour valeur le thêta de secteur en x (sommation à support fini). | CONFIRMÉE (x positif ou nul) | AJOUT | 1 |
| `hasSum_grammarSectorMellinValueTerm` | Pour x positif ou nul, la somme sur q des termes de valeur de Mellin de secteur vaut thêta de secteur en x fois x^(-s-1) (identité pointwise de couche-gâteau). | CONFIRMÉE (x positif ou nul) | AJOUT | 0 |
| `grammarSectorMellinValueTerm_integrableOn` | Pour Re s > 1, le terme de valeur de Mellin de secteur pour un q fixé est intégrable sur (1,+inf). | CONFIRMÉE (Re s > 1) | AJOUT | 0 |
| `integral_grammarSectorMellinValueTerm` | Pour Re s > 1, l'intégrale sur (1,+inf) du terme de Mellin de secteur en q vaut log q fois l'indicateur en q fois max(q,1)^(-s) divisé par s. | CONFIRMÉE (Re s > 1) | AJOUT | 0 |
| `sum_grammarThetaSector_eq_chebyshevTheta` | La somme des thêta de secteurs de grammaire égale la fonction thêta de Tchebychev, en tout x. | CONFIRMÉE | AJOUT | 2 |
| `sum_grammarScaleFourThetaSector` | La somme des thêta de secteurs à l'échelle quatre égale thêta(t) - thêta(t/4), pour tout t. | CONFIRMÉE | AJOUT | 1 |
| `thetaScaleFourDefectReal_eq_affine_sub_grammar_sectors` | Le défaut thêta réel à l'échelle quatre vaut 3t/4 moins la somme sur les secteurs des thêta de secteur à l'échelle quatre. | CONFIRMÉE | AJOUT | 1 |
| `thetaScaleFourDefectMellinBlock_eq_grammar_sum` | Recomposition linéaire du bloc de Mellin dyadique : le bloc du défaut thêta égale le bloc affine moins la somme sur les secteurs des blocs de secteur. | CONFIRMÉE (domaine : intégrabilité locale de la partie affine et de chaque secteur sur le bloc dyadique) | AJOUT | 1 |
| `canonicalGrammarThetaDyadicMellinBlock_eq_sector_recomposition` | Même recomposition en indice n+2 (bloc de Mellin dyadique canonique du défaut thêta égale bloc affine moins somme des blocs de secteur). | CONFIRMÉE (domaine : intégrabilité locale de la partie affine et de chaque secteur sur le bloc dyadique) | AJOUT | 0 |
| `thetaScaleFourDefectReal_four` | Récurrence centrée : le défaut thêta à l'échelle quatre en 4y vaut 4 fois celui en y plus le forçage de second échelle en y. | CONFIRMÉE | AJOUT | 0 |
| `sum_grammarSecondScaleForcing_eq_chebyshev` | La somme sur les secteurs du forçage de second échelle égale thêta(4y) - 5 thêta(y) + 4 thêta(y/4). | CONFIRMÉE | AJOUT | 1 |
| `thetaSecondScaleForcingReal_eq_theta_combination` | Le forçage de second échelle égale 5 thêta(y) - thêta(4y) - 4 thêta(y/4). | CONFIRMÉE | AJOUT | 2 |
| `thetaSecondScaleForcingReal_eq_neg_grammar_sum` | Le forçage de second échelle est l'opposé de la somme sur les secteurs du forçage de grammaire. | CONFIRMÉE | AJOUT | 0 |
| `thetaSecondScaleForcingReal_le_trivial` | Pour y positif ou nul, le forçage de second échelle est majoré par 5 log 4 fois y (borne triviale d'ordre O(y)). | CONFIRMÉE (y positif ou nul) | AJOUT | 0 |
| `psiErrorReal_linear_bound_on_Ioi_one` | Pour x dans (1,+inf), la valeur absolue de l'erreur psi est majorée par (log 4 + 5) x. | CONFIRMÉE (x dans (1,+inf)) | AJOUT | 3 |
| `psiErrorMellinIntegrand_aestronglyMeasurable_restrict_Ioi_one` | Pour tout s, l'intégrande de Mellin de l'erreur psi est presque partout fortement mesurable sur (1,+inf). | CONFIRMÉE | AJOUT | 2 |
| `psiErrorMellinIntegrand_integrableOn_Ioi_one_re_gt_one` | Pour Re s > 1, l'intégrande de Mellin de l'erreur psi est intégrable sur (1,+inf). | CONFIRMÉE (Re s > 1) | AJOUT | 4 |
| `psiErrorIntegral_eq_zeta_logDeriv_re_gt_one` | Pour Re s > 1, l'intégrale de l'erreur psi fois x^(-s-1) sur (1,+inf) vaut 1/(s-1) plus (dérivée logarithmique de zêta en s)/s. | CONFIRMÉE (Re s > 1) | AJOUT | 1 |
| `psiError_scale_four_change_of_variables_re_gt_one` | Pour Re s > 1, l'intégrale sur (4,+inf) de erreur psi(t/4) fois t^(-s-1) vaut 4^(-s) fois l'intégrale de l'erreur psi sur (1,+inf). | CONFIRMÉE (Re s > 1) | AJOUT | 1 |
| `psiError_integral_Ioi_four_eq_integral_Ioi_one_sub_boundary` | Pour Re s > 1, l'intégrale de l'erreur psi sur (4,+inf) est égale à l'intégrale sur (1,+inf) moins le terme de bord psiScaleFourBoundaryOneToFour(s). | CONFIRMÉE (Re s > 1) | AJOUT | 1 |
| `psiErrorScaledMellinIntegrand_aestronglyMeasurable_restrict_Ioi_four` | Pour tout s, l'intégrande de Mellin mis à l'échelle (psi en t/4) est presque partout fortement mesurable sur (4,+inf). | CONFIRMÉE | AJOUT | 1 |
| `psiErrorScaledMellinIntegrand_integrableOn_Ioi_four_re_gt_one` | Pour Re s > 1, l'intégrande de Mellin mis à l'échelle (erreur psi(t/4)) est intégrable sur (4,+inf). | CONFIRMÉE (Re s > 1) | AJOUT | 2 |
| `psiScaleFourMellinAboveFour_eq_integral_re_gt_one` | Pour Re s > 1, psiScaleFourMellinAboveFour(s) vaut (1 - 4^(-s)) fois l'intégrale de l'erreur psi sur (1,+inf) moins le terme de bord. | CONFIRMÉE (Re s > 1) | AJOUT | 1 |
| `psiScaleFourMellinAboveFour_eq_scaleFourPsiMellinContinuation_re_gt_one` | Pour Re s > 1, la transformée de Mellin psi à l'échelle quatre au-dessus de quatre est égale à la continuation de Mellin psi à l'échelle quatre. | CONFIRMÉE (Re s > 1) | AJOUT | 1 |
| `primePowerScaleFourCorrection_measurable` | La correction de puissances de nombres premiers à l'échelle quatre est mesurable. | CONFIRMÉE | AJOUT | 2 |
| `abs_primePowerScaleFourCorrection_le` | Pour t > 4, la correction de puissances premières à l'échelle quatre est majorée en valeur absolue par 4 racine(t) (1 + log t). | CONFIRMÉE (t > 4) | AJOUT | 2 |
| `primePowerScaleFourCorrectionMellinIntegrand_aestronglyMeasurable_restrict_Ioi_four` | Pour tout s, l'intégrande de Mellin de la correction de puissances premières est presque partout fortement mesurable sur (4,+inf). | CONFIRMÉE | AJOUT | 2 |
| `primePowerScaleFourCorrectionMellinIntegrand_integrableOn_Ioi_four` | Pour Re s > 1/2, l'intégrande de Mellin de la correction de puissances premières est intégrable sur (4,+inf). | CONFIRMÉE (Re s > 1/2) | AJOUT | 2 |
| `primePowerScaleFourCorrectionMellinDeriv_aestronglyMeasurable_restrict_Ioi_four` | Pour tout s, l'intégrande dérivé (en s) de Mellin de la correction est presque partout fortement mesurable sur (4,+inf). | CONFIRMÉE | AJOUT | 1 |
| `hasDerivAt_primePowerScaleFourCorrectionMellin_integrand` | Pour t > 0 et tout s, l'intégrande de Mellin de la correction est dérivable en s de dérivée correction(t) t^(-s-1) log t fois -1. | CONFIRMÉE (t > 0) | AJOUT | 1 |
| `_private.RhGapCriterion.Round26B4GrammarSpectralSectors.0.ae_on_Ioi_four_of_all` | Lemme privé : une propriété vraie en tout point de (4,+inf) est vraie presque partout sur (4,+inf). | CONFIRMÉE (lemme privé, prémisse universelle sur (4,+inf)) | AJOUT | 1 |
| `_private.RhGapCriterion.Round26B4GrammarSpectralSectors.0.dist_lt_of_mem_ball_half` | Lemme privé : si z est dans la boule de centre s et de rayon δ/2 et si δ > 0, alors la distance de z à s est strictement inférieure à δ. | CONFIRMÉE (δ > 0) | AJOUT | 1 |
| `analyticAt_primePowerScaleFourCorrectionMellinAboveFour` | Pour Re s > 1/2, la transformée de Mellin de la correction de puissances premières à l'échelle quatre est analytique en s. | CONFIRMÉE (Re s > 1/2) | AJOUT | 2 |
| `analyticOnNhd_primePowerScaleFourCorrectionMellinAboveFour` | La transformée de Mellin de la correction est analytique sur tout le demi-plan ouvert Re s > 1/2. | CONFIRMÉE | AJOUT | 1 |
| `thetaScaleFourDefectReal_eq_psi_add_primePowerScaleFourCorrection` | Le défaut thêta réel à l'échelle quatre égale le défaut psi plus la correction de puissances premières. | CONFIRMÉE | AJOUT | 2 |
| `thetaScaleFourDefectReal_sub_psi_eq_primePowerScaleFourCorrection` | Le défaut thêta moins le défaut psi égale la correction de puissances premières à l'échelle quatre. | CONFIRMÉE | AJOUT | 0 |
| `psiScaleFourMellinIntegrand_integrableOn_Ioi_four_re_gt_one` | Pour Re s > 1, l'intégrande de Mellin du défaut psi à l'échelle quatre est intégrable sur (4,+inf). | CONFIRMÉE (Re s > 1) | AJOUT | 1 |
| `thetaScaleFourMellinAboveFour_eq_psi_add_primePower_re_gt_one` | Pour Re s > 1, la transformée de Mellin thêta au-dessus de quatre vaut celle de psi plus celle de la correction de puissances premières. | CONFIRMÉE (Re s > 1) | AJOUT | 1 |
| `thetaScaleFourMellinAboveFour_eq_scaleFourThetaMellinContinuation_re_gt_one` | Pour Re s > 1, la transformée de Mellin thêta au-dessus de quatre est égale à la continuation de Mellin thêta à l'échelle quatre. | CONFIRMÉE (Re s > 1) | AJOUT | 0 |
| `analyticOnNhd_scaleFourTheta_minus_scaleFourPsi` | La différence des continuations de Mellin thêta et psi à l'échelle quatre est analytique sur le demi-plan Re s > 1/2. | CONFIRMÉE | AJOUT | 0 |
| `psiScaleFourMellinAboveFour_eq_of_change_of_variables` | Si l'énergie locale de Mellin psi est sous-exponentielle et si le changement de variable de bord (psiScaleFourMellinAboveFour s = (1 - 4^(-s)) fois psiErrorMellin s moins terme de bord) tient pour Re s > 1, alors psiScaleFourMellinAboveFour s égale la continuation de Mellin psi à l'échelle quatre. | CONFIRMÉE SOUS CONDITION (énergie locale psi sous-exponentielle et identité de changement de variable de bord hchange) | AJOUT | 0 |
| `one_sub_four_cpow_neg_zero_ne_zero` | Pour tout zéro non trivial ρ de zêta, 1 - 4^(-ρ) est non nul. | CONFIRMÉE (ρ zéro non trivial) | AJOUT | 2 |
| `explicitNonzeroScaleFourResidue_ne_zero` | Pour tout zéro non trivial ρ, le résidu non nul à l'échelle quatre (explicitNonzeroScaleFourResidue ρ) est non nul. | CONFIRMÉE (ρ zéro non trivial) | AJOUT | 2 |
| `scaleFour_frozen_negLogDeriv_has_nonzero_zero_principal_part` | Pour un zéro non trivial ρ, (1 - 4^(-ρ)) fois l'opposé de la dérivée logarithmique de zêta, moins résidu/(s - ρ), est un grand O de 1 au voisinage épointé de ρ. | CONFIRMÉE (ρ zéro non trivial) | AJOUT | 0 |
| `canonicalScaleFourThetaZeroAmplitude_ne_zero` | Pour un zéro non trivial ρ, l'amplitude thêta canonique à l'échelle quatre du zéro est non nulle. | CONFIRMÉE (ρ zéro non trivial) | AJOUT | 3 |
| `canonicalScaleFourThetaZeroAmplitude_eq_factor_mul_P5` | Pour un zéro non trivial ρ, l'amplitude thêta canonique à l'échelle quatre vaut -(1 - 4^(-ρ)) fois l'amplitude de la formule explicite du zéro (facteur P5). | CONFIRMÉE (ρ zéro non trivial) | AJOUT | 1 |
| `scaleFourTheta_logDeriv_mobile_factor_sub_principal_isBigO` | Pour un zéro non trivial ρ, (1 - 4^(-s))/s fois la dérivée logarithmique de zêta moins amplitude thêta canonique/(s - ρ) est un grand O de 1 au voisinage épointé de ρ. | CONFIRMÉE (ρ zéro non trivial) | AJOUT | 0 |
| `GrammarSectorMeromorphicContinuationAt.meromorphicAt` | Le champ de continuation d'un secteur de grammaire en ρ est méromorphe en ρ (projection de structure). | CONFIRMÉE | AJOUT | 0 |
| `GrammarSectorMeromorphicFamilyAt.residue_sum_eq_global` | Pour une famille méromorphe de secteurs de grammaire en ρ, la somme des résidus des continuations de secteur égale le résidu global non nul à l'échelle quatre (projection de structure). | CONFIRMÉE | AJOUT | 1 |
| `grammar_sector_residue_sum_eq_global_residue` | Pour toute famille méromorphe de secteurs en ρ, la somme des résidus de secteur égale le résidu global à l'échelle quatre. | CONFIRMÉE | AJOUT | 3 |
| `exists_nonzero_grammar_sector_residue_at_zero` | Pour un zéro non trivial ρ et toute famille méromorphe de secteurs, il existe un secteur dont le résidu en ρ est non nul. | CONFIRMÉE (ρ zéro non trivial) | AJOUT | 0 |
| `grammarSpectralResidue_sum` | Pour un zéro non trivial ρ et toute famille méromorphe de secteurs, la somme des résidus spectraux de grammaire égale le résidu global à l'échelle quatre. | CONFIRMÉE (ρ zéro non trivial) | AJOUT | 1 |
| `grammarSpectralResidue_ne_zero` | Pour un zéro non trivial ρ et toute famille méromorphe de secteurs, le vecteur de résidus spectraux de grammaire est non nul. | CONFIRMÉE (ρ zéro non trivial) | AJOUT | 1 |
| `grammarZeroModeState_scale_four` | L'état de mode de zéro de grammaire est multiplié par la valeur propre exp((ρ - 1/2) log 4) lors du décalage U -> U + log 4, pour tout ρ complexe et tout v. | CONFIRMÉE | AJOUT | 1 |
| `grammarResidueEnergy_nonneg` | L'énergie de résidu de grammaire d'un vecteur de secteurs est positive ou nulle. | CONFIRMÉE | AJOUT | 0 |
| `exists_nonzero_sector_of_vector_ne_zero` | Si un vecteur de secteurs est non nul, un de ses secteurs est non nul. | CONFIRMÉE (vecteur non nul) | AJOUT | 1 |
| `grammarResidueEnergy_pos_of_nonzero` | L'énergie de résidu de grammaire d'un vecteur non nul est strictement positive. | CONFIRMÉE (vecteur non nul) | AJOUT | 3 |
| `grammarZeroModeEnergy_nonneg` | L'énergie de mode de zéro de grammaire est positive ou nulle, pour tout ρ, v et U. | CONFIRMÉE | AJOUT | 0 |
| `grammarZeroModeEnergy_exact_growth` | L'énergie de mode de zéro de grammaire vaut exactement l'énergie de résidu fois exp(2 (Re ρ - 1/2) U), pour tout ρ complexe, v et U. | CONFIRMÉE | AJOUT | 3 |
| `sectorGlobalCoord_norm_sq_le_four_mul_energy` | La norme au carré de la coordonnée globale d'un vecteur de secteurs est majorée par 4 fois son énergie de résidu. | CONFIRMÉE | AJOUT | 1 |
| `grammarResidueEnergy_basis_formula_of_coboundary_zero` | Si la coordonnée de cobord d'un vecteur est nulle, son énergie de résidu vaut norme(globale - état - croisée/2)^2 plus norme(état - croisée/2)^2 plus norme(croisée)^2/2. | CONFIRMÉE (domaine : coordonnée de cobord nulle) | AJOUT | 1 |
| `grammarResidueEnergy_pos_of_globalCoord_ne_zero` | Si la coordonnée globale d'un vecteur de secteurs est non nulle, son énergie de résidu est strictement positive. | CONFIRMÉE (coordonnée globale non nulle) | AJOUT | 1 |
| `grammar_residue_state_ne_zero_of_theta_global` | Pour un zéro non trivial ρ, tout vecteur de secteurs dont la coordonnée globale égale l'amplitude thêta canonique du zéro est non nul. | CONFIRMÉE (domaine : coordonnée globale égale à l'amplitude thêta canonique de ρ) | AJOUT | 1 |
| `grammar_residue_energy_pos_of_theta_global` | Pour un zéro non trivial ρ, tout vecteur dont la coordonnée globale égale l'amplitude thêta canonique du zéro a une énergie de résidu strictement positive. | CONFIRMÉE (domaine : coordonnée globale égale à l'amplitude thêta canonique de ρ) | AJOUT | 0 |
| `grammar_residue_energy_basis_formula_of_theta_global_coboundary_zero` | Pour un zéro non trivial ρ et un vecteur dont la coordonnée globale égale l'amplitude thêta canonique et le cobord est nul, l'énergie de résidu vaut norme(amplitude - état - croisée/2)^2 plus norme(état - croisée/2)^2 plus norme(croisée)^2/2. | CONFIRMÉE (domaine : coordonnée globale égale à l'amplitude thêta canonique de ρ, coordonnée de cobord nulle) | AJOUT | 0 |
| `sectorGlobalZeroModeEnergy_le_four_mul_grammarZeroModeEnergy` | L'énergie du mode de zéro global (coordonnée globale) est majorée par 4 fois l'énergie de mode de zéro de grammaire, pour tout ρ, v et U. | CONFIRMÉE | AJOUT | 0 |
| `grammarZeroModeEnergy_subexponential_forces_re_le_half` | Si un vecteur v est non nul et si l'énergie de mode de zéro de grammaire est sous-exponentielle en U, alors Re ρ est majorée par 1/2. | CONFIRMÉE SOUS CONDITION (v non nul, énergie de mode sous-exponentielle en U) | AJOUT | 0 |
| `residue_amplitude_to_zeroMode` | Une amplitude résiduelle A multipliant exp(ρ U), après normalisation exp(-U/2), est exactement le mode de zéro zeroMode ρ A U. | CONFIRMÉE | AJOUT | 0 |
| `grammarSpectralResidue_zeroModeState_nonzero` | Pour un zéro non trivial ρ et toute famille méromorphe de secteurs, l'état de mode de zéro construit sur le résidu spectral de grammaire est non nul en tout U. | CONFIRMÉE (ρ zéro non trivial) | AJOUT | 0 |
| `real_norm_le_one_of_pow_bounded` | Si les puissances r^n d'un réel r sont bornées par une constante C, alors r est majoré par 1. | CONFIRMÉE (domaine : puissances r^n uniformément bornées) | AJOUT | 1 |
| `scale_eigenvalue_norm_le_one_of_power_bounded` | Si les puissances de la norme d'une valeur propre complexe lam sont bornées, alors sa norme est au plus 1. | CONFIRMÉE (domaine : puissances de la norme de lam bornées) | AJOUT | 1 |
| `scale_eigenvector_bounded_orbit_forces_norm_le_one` | Pour un vecteur v non nul de C, si l'orbite ‖lam^n v‖ est bornée, alors la norme de lam est au plus 1. | CONFIRMÉE (domaine : orbite bornée; v non nul) | AJOUT | 0 |
| `scale4_eigenvalue_norm_le_one_implies_re_le_half` | Si la norme de 4^(ρ - 1/2) est au plus 1, alors Re ρ est au plus 1/2. | CONFIRMÉE (domaine : norme de 4^(ρ - 1/2) au plus 1) | AJOUT | 0 |

## Correspondance avec RHV6Fresh

Nom RHV6Fresh vérifié présent dans `data/RHV6Fresh.jsonl` (colonne « existe »). Rapprochement de types fait par le relecteur ; « approximative » quand la remarque du relecteur le dit.

| théorème rh_gap_criterion | énoncé | théorème RHV6Fresh | existe |
|---|---|---|---|
| `prime_mod6_state` | Pour n >= 2, p n mod 6 vaut 1 ou 5 (états de la grammaire). | `RHV6Fresh.prime_goodMod6` | oui |
| `gap_mod6_exhaustive` | Pour n >= 1, la classe mod 6 du gap gnat n est 0, 2 ou 4 (alias de gnat_class_even). | `RHV6Fresh.gapClass6_mem` | oui |
| `class_projection_complete` | Pour n >= 2, classe 0 du gap si et seulement si état mod 6 conservé, classe 2 si et seulement si transition 5 vers 1, classe 4 si et seulement si transition 1 vers 5. | `RHV6Fresh.gapClass6_eq_zero_iff` | oui |
| `ScientificRebuild20260901.functionalMirror_gamma` | La hauteur (Gamma) du miroir fonctionnel d'un zéro non trivial égale celle du zéro. | `RHV6Fresh.mirrorMember_ordinate` | oui |
| `ScientificRebuild20260901.functionalMirror_beta` | La partie réelle (Beta) du miroir fonctionnel d'un zéro non trivial vaut 1 moins celle du zéro. | `RHV6Fresh.mirrorMember_radial` | oui |
| `ScientificRebuild20260901.TrueMemberContactCell.recoversGamma` | Les deux contacts et le nombre d'étapes d'une cellule redonnent exactement la hauteur du zéro par la formule de récupération e44. | `RHV6Fresh.AnalyticContactPair.recovers_T` | oui |
| `ScientificRebuild20260901.TrueMemberContactCell.recoversBeta` | Les deux contacts et le nombre d'étapes d'une cellule redonnent exactement la partie réelle du zéro par la formule tangente e44. | `RHV6Fresh.AnalyticContactPair.recovers_beta` | oui |
| `ScientificRebuild20260901.offMirror_leftContact_ne` | Pour un zéro de hauteur strictement positive et de partie réelle différente de 1/2, le contact gauche de tangente de ρ diffère de celui de son miroir fonctionnel pour toute branche. | `RHV6Fresh.mirror_contacts_never_coincide` | oui |
| `Kadiri.riemannZetaConjZeroSource_of_riemannZeta_conj` | Si ζ(z)=0 alors ζ(conj z)=0 : les zéros de zêta sont stables par conjugaison. | `RHV6Fresh.analyticOrderAt_zeta_conj` | oui |
| `Kadiri.zeroes_rect_Ioo_critical_positive_height_finite` | L'ensemble des zéros de zêta de partie réelle dans ]0,1[ et de partie imaginaire dans ]0,T[ est fini. | `RHV6Fresh.zeta_window_finite` | oui |
| `Kadiri.zeroes_rect_univ_positive_height_finite` | Il n'y a qu'un nombre fini de zéros de zêta de hauteur dans ]0,T[. | `RHV6Fresh.zeta_window_finite` | oui |
| `_private.RhGapCriterion.P4Port.IEANTN.KadiriZeroCounting.0.Kadiri.analyticAt_conj_conj` | Si f est analytique en conj z₀, alors w ↦ conj(f(conj w)) est analytique en z₀. | `RHV6Fresh.analyticAt_conj_conj` | NON TROUVÉ |
| `_private.RhGapCriterion.P4Port.IEANTN.KadiriZeroCounting.0.Kadiri.analyticOrderAt_conj_conj` | L'ordre analytique de w ↦ conj(f(conj w)) en z₀ égale celui de f en conj z₀. | `RHV6Fresh.analyticOrderAt_conj_conj` | oui |
| `Kadiri.riemannZeta_order_conj` | En un zéro ρ de zêta, l'ordre en conj ρ égale l'ordre en ρ. | `RHV6Fresh.analyticOrderAt_zeta_conj` | oui |
| `FullRigidCoupledZeroPrimeGrammar.family_change_skeleton_alternates` | Entre deux écarts non nuls mod 6 séparés seulement par des écarts de classe 0, les classes valent (2 puis 4) ou (4 puis 2). | `RHV6Fresh.primeGapClass6_alternates` | oui |
| `FullRigidCoupledZeroPrimeGrammar.change_skeleton_alternates` | Entre deux écarts non nuls mod 6 séparés seulement par des écarts de classe 0, les classes valent (2 puis 4) ou (4 puis 2). | `RHV6Fresh.primeGapClass6_alternates` | oui |
| `nontrivialZero_ne_zero` | Tout zéro non trivial est non nul. | `RHV6Fresh.zeroPoint_ne_zero` | oui |
| `nontrivialZero_add_one_ne_zero` | Pour tout zéro non trivial ρ, ρ + 1 est non nul. | `RHV6Fresh.zeroPoint_add_one_ne_zero` | oui |
| `reflect_signed_distance` | La distance signée du réfléchi de ρ à la droite critique est l'opposée de celle de ρ (Re' − 1/2 = −(Re − 1/2)). | `RHV6Fresh.mirror_beta` | oui |
| `reflectConj_re` | Le réfléchi-conjugué 1 - conj ρ a pour partie réelle 1 - Re ρ. | `RHV6Fresh.zetaReflect_re` | oui |
| `reflectConj_im` | Le réfléchi-conjugué 1 - conj ρ a la même partie imaginaire que ρ. | `RHV6Fresh.zetaReflect_im` | oui |
| `zetaZeroMultiplicity_reflectConj` | La multiplicité analytique de zêta est conservée par le passage de ρ à 1 - conj ρ pour un zéro non trivial dans la bande ouverte. | `RHV6Fresh.analyticOrderAt_zeta_reflect` | oui |
| `_private.RhGapCriterion.Round26B4ConstellationCollisionRigidity.0.norm_nontrivialZeroResidueTerm_eq_amplitude_rpow` | La norme du terme résiduel individuel d'un zéro non trivial en x>0 vaut une amplitude déterminée fois x puissance Re τ. | `RHV6Fresh.zeroTerm_norm` | oui |
| `onLineMembers_eq_fixedPoints` | Les membres sur la ligne critique de la constellation sont exactement les membres de la constellation fixes par l'involution de réflexion-conjugaison. | `RHV6Fresh.zetaReflect_eq_self_iff` | oui |
| `nontrivialZeroResidueTerm_conj` | Pour x>0, le conjugué du terme résiduel individuel de ρ en x est le terme résiduel du zéro conjugué en x. | `RHV6Fresh.conjugate_term_eq_conj` | oui |
| `reflectConjZero_re` | La partie réelle du réfléchi-conjugué d'un zéro non trivial ρ vaut 1 - Re ρ. | `RHV6Fresh.zetaReflect_re` | oui |
| `reflectConjZero_im` | La partie imaginaire du réfléchi-conjugué d'un zéro non trivial ρ est celle de ρ. | `RHV6Fresh.zetaReflect_im` | oui |
| `reflectConjZero_eq_self_iff` | Un zéro non trivial est fixe par la réflexion-conjugaison si et seulement si sa partie réelle vaut 1/2. | `RHV6Fresh.zetaReflect_eq_self_iff` | oui |
| `reflectConjZero_ne_self_iff` | Un zéro non trivial n'est pas fixe par la réflexion-conjugaison si et seulement si sa partie réelle est différente de 1/2. | `RHV6Fresh.zetaReflect_eq_self_iff` | oui |
| `reflectConjZero_zeroHeight` | La hauteur du réfléchi-conjugué d'un zéro non trivial égale la hauteur de ce zéro. | `RHV6Fresh.zetaReflect_im` | oui |
| `reflectConjZero_multiplicity` | La multiplicité analytique de zêta au réfléchi-conjugué d'un zéro non trivial égale celle du zéro. | `RHV6Fresh.analyticOrderAt_zeta_reflect` | oui |

## Théorèmes mentionnant RiemannHypothesis / RH (statut exact)

Sélection : drapeau `mentions_RH` du jsonl, ou statut ÉQUIVALENTE/IMPLIQUE, ou nom contenant riemann/RH. La colonne `mRH` vaut oui si le type contient littéralement `RiemannHypothesis` (drapeau du jsonl) ; sinon il s'agit du prédicat du projet, d'un verrou équivalent, ou d'un ensemble Z abstrait.

| théorème | module | mRH | statut exact | énoncé |
|---|---|---|---|---|
| `theoremB` | Basic | non | ÉQUIVALENTE À RH | Sous von Koch/Schoenfeld, propagation aux points premiers et comptabilité d'énumération, RH du projet équivaut à l'existence de C>0 tel que pour tout m la valeur absolue de R m + p 0 moins log p m est bornée par C racine(p m) log(p m) au carré. |
| `gap_criterion` | Basic | non | ÉQUIVALENTE À RH | Sous von Koch/Schoenfeld et propagation aux points premiers, RH du projet équivaut au critère de gaps (existence de C>0 avec borne racine(p m) log carré sur le résidu recentré). |
| `gap_criterion_vonKoch_only` | Basic | non | ÉQUIVALENTE À RH | Sous la seule hypothèse von Koch/Schoenfeld, RH du projet équivaut au critère de gaps (existence de C>0 avec borne racine(p m) log carré sur le résidu recentré). |
| `mode_criterion_vonKoch_only` | Basic | non | ÉQUIVALENTE À RH | Sous von Koch/Schoenfeld, RH du projet équivaut à une borne racine(p m) log carré sur le mode total recentré Tmode m + (g0 moins log p0) + p0 moins log p m, pour m >= 1. |
| `functional_symmetry_forces_half` | Basic | non | IMPLIQUE RH SOUS PRÉMISSE (Z stable par la symétrie fonctionnelle et aucun zéro à partie réelle > 1/2) | Si un ensemble Z de complexes est stable par rho vers 1-rho et si tout élément a partie réelle <= 1/2, alors tout élément a partie réelle égale à 1/2. |
| `theoremF_RH_from_T_spectral_rigidity` | Basic | non | IMPLIQUE RH SOUS PRÉMISSE (énergie sous-exponentielle, croissance forcée par tout zéro hors ligne, symétrie fonctionnelle) | Sous E sous-exponentielle, croissance forcée par tout zéro à partie réelle > 1/2 et stabilité de Z par rho vers 1-rho, tout élément de Z a partie réelle 1/2. |
| `functional_symmetry_forces_exact_half` | Basic | non | IMPLIQUE RH SOUS PRÉMISSE (Z stable par la symétrie fonctionnelle et aucun zéro à partie réelle > 1/2) | Si Z est stable par rho vers 1-rho et si toute partie réelle de Z est <= 1/2, alors toute partie réelle de Z vaut 1/2 (alias). |
| `RH_from_density_order_scale_rigidity` | Basic | non | IMPLIQUE RH SOUS PRÉMISSE (symétrie fonctionnelle de Z et module de valeur propre d'échelle <= 1 pour tout zéro) | Pour a>0, si Z est stable par rho vers 1-rho et si exp(a (Re rho moins 1/2)) <= 1 pour tout rho de Z, alors toute partie réelle de Z vaut 1/2. |
| `translated_scale_invariance_closes_RH17` | CanonicalRestrictionFinal | non | IMPLIQUE RH SOUS PRÉMISSE (symétrie fonctionnelle de Z et module spectral d'échelle <= 1 pour tout zéro) | Pour a>0, si Z est stable par rho vers 1-rho et si exp(a (Re rho moins 1/2)) <= 1 pour tout rho de Z, alors toute partie réelle de Z vaut 1/2. |
| `theoremG_RH_from_mellin_rigidity` | Mellin | non | IMPLIQUE RH SOUS PRÉMISSE (exclusion de Mellin à droite du demi-plan pour Z avec énergie E sous-exponentielle, Z stable par ρ↦1−ρ) | Pour un ensemble Z de complexes stable par ρ↦1−ρ, si Z vérifie l'exclusion de Mellin à droite pour une énergie E sous-exponentielle, tout ρ de Z a partie réelle 1/2. |
| `RH_from_windowed_identity_and_remainder_bound` | PrimeZeroIntertwining | non | IMPLIQUE RH SOUS PRÉMISSE (décomposition mode plus reste de la composante fenêtrée, sous-exponentialité de la composante et du reste, amplitudes non nulles, stabilité de Z par 1 − ρ) | Pour un ensemble Z de zéros stable par ρ ↦ 1 − ρ, si chaque composante fenêtrée se décompose en mode d'amplitude non nulle plus reste et que composante et reste sont sous-exponentiels, alors tout ρ de Z a Re ρ = 1/2. |
| `psi_mellin_subexponential_excludes_right_nontrivial_zeros` | Round25M53MellinZetaIdentity | non | IMPLIQUE RH SOUS PRÉMISSE (énergie locale de Mellin de ψ sous-exponentielle ; demi-RH Re ρ ≤ 1/2, RH complète par la symétrie ρ ↦ 1−ρ) | Si l'énergie de Mellin de ψ est sous-exponentielle, tout zéro non trivial ρ de ζ vérifie Re ρ ≤ 1/2. |
| `theta_mellin_subexponential_excludes_right_nontrivial_zeros` | Round25M53MellinZetaIdentity | non | IMPLIQUE RH SOUS PRÉMISSE (énergie locale de Mellin de θ sous-exponentielle ; demi-RH Re ρ ≤ 1/2, RH complète par la symétrie ρ ↦ 1−ρ) | Si l'énergie de Mellin de θ est sous-exponentielle, tout zéro non trivial ρ de ζ vérifie Re ρ ≤ 1/2. |
| `critical_line_of_primeForcedTwoScaleRatioRecurrence` | Round26AKPrimeForcedRatioRecurrence | non | IMPLIQUE RH SOUS PRÉMISSE (verrou PrimeForcedTwoScaleRatioRecurrence, équivalent à RH) | Le verrou PrimeForcedTwoScaleRatioRecurrence entraîne que tout zéro non trivial est sur la ligne Re = 1/2. |
| `riemann_hypothesis_of_primeForcedTwoScaleRatioRecurrence` | Round26AKPrimeForcedRatioRecurrence | oui | IMPLIQUE RH SOUS PRÉMISSE (verrou PrimeForcedTwoScaleRatioRecurrence, équivalent à RH) | Le verrou PrimeForcedTwoScaleRatioRecurrence entraîne RiemannHypothesis. |
| `riemann_hypothesis_of_primeScaleForcedRatioRecurrence` | Round26AKPrimeForcedRatioRecurrence | oui | IMPLIQUE RH SOUS PRÉMISSE (verrou PrimeScaleForcedRatioRecurrence, équivalent à RH) | Le verrou PrimeScaleForcedRatioRecurrence (forme aux échelles premières) entraîne RiemannHypothesis. |
| `primeForcedTwoScaleRatioRecurrence_iff_riemannHypothesis` | Round26AKPrimeForcedRatioRecurrence | oui | ÉQUIVALENTE À RH | Le verrou PrimeForcedTwoScaleRatioRecurrence équivaut à RiemannHypothesis. |
| `primeScaleForcedRatioRecurrence_iff_riemannHypothesis` | Round26AKPrimeForcedRatioRecurrence | oui | ÉQUIVALENTE À RH | Le verrou PrimeScaleForcedRatioRecurrence équivaut à RiemannHypothesis. |
| `primeScaleForcedRatioRecurrence_iff_primeForcedTwoScaleRatioRecurrence` | Round26AKPrimeForcedRatioRecurrence | non | ÉQUIVALENTE À RH | Les deux formes du verrou (échelles premières et deux échelles positives) sont équivalentes entre elles, toutes deux étant équivalentes à RH dans le même lot. |
| `primeForcedTwoScaleRatioRecurrence_of_scale_four_subexponential` | Round26AKPrimeForcedRatioRecurrence | non | IMPLIQUE RH SOUS PRÉMISSE (sous-exponentialité de thetaScaleFourMellinEnergy) | Si l'énergie de Mellin thetaScaleFourMellinEnergy est sous-exponentielle, alors le verrou PrimeForcedTwoScaleRatioRecurrence tient. |
| `primeScaleForcedRatioRecurrence_of_scale_four_subexponential` | Round26AKPrimeForcedRatioRecurrence | non | IMPLIQUE RH SOUS PRÉMISSE (sous-exponentialité de thetaScaleFourMellinEnergy) | Si l'énergie de Mellin thetaScaleFourMellinEnergy est sous-exponentielle, alors le verrou PrimeScaleForcedRatioRecurrence tient. |
| `critical_line_of_channel_and_rest_subexponential` | Round26ALSpineRestGrowthReduction | non | IMPLIQUE RH SOUS PRÉMISSE (canal total et reste réfléchi sous-exponentiels) | Sous les deux sous-exponentialités, tout zéro non trivial vérifie Re ρ = 1/2. |
| `riemannHypothesis_of_channel_and_rest_subexponential` | Round26ALSpineRestGrowthReduction | oui | IMPLIQUE RH SOUS PRÉMISSE (canal total et reste réfléchi sous-exponentiels) | Le canal total côté zéros sous-exponentiel et le reste réfléchi sous-exponentiel entraînent RiemannHypothesis. |
| `critical_line_of_singlePrimeScaleCharacterCoincidence` | Round26AMPrimeScaleCharacterFaithfulness | non | IMPLIQUE RH SOUS PRÉMISSE (verrou SinglePrimeScaleCharacterCoincidence, équivalent à RH) | Le verrou SinglePrimeScaleCharacterCoincidence entraîne que tout zéro non trivial vérifie Re = 1/2. |
| `riemannHypothesis_of_singlePrimeScaleCharacterCoincidence` | Round26AMPrimeScaleCharacterFaithfulness | oui | IMPLIQUE RH SOUS PRÉMISSE (verrou SinglePrimeScaleCharacterCoincidence, équivalent à RH) | Le verrou SinglePrimeScaleCharacterCoincidence entraîne RiemannHypothesis. |
| `singlePrimeScaleCharacterCoincidence_of_riemannHypothesis` | Round26AMPrimeScaleCharacterFaithfulness | oui | CONFIRMÉE SOUS CONDITION (RH supposée en hypothèse) | RiemannHypothesis entraîne le verrou SinglePrimeScaleCharacterCoincidence (caractères d'échelle de ρ et de son miroir coïncidents à l'échelle p 0 = 2). |
| `singlePrimeScaleCharacterCoincidence_iff_riemannHypothesis` | Round26AMPrimeScaleCharacterFaithfulness | oui | ÉQUIVALENTE À RH | Le verrou SinglePrimeScaleCharacterCoincidence équivaut à RiemannHypothesis. |
| `full_coupled_rigidity_exclusion_iff_offline_exclusion` | Round26AQTerminalRigidityClosure | non | ÉQUIVALENTE À RH | FullCoupledRigidityOfflineExclusion équivaut à l'exclusion, à toute hauteur T, de tout représentant positif de partie réelle différente de 1/2. |
| `all_positiveRepresentatives_on_critical_line_of_exclusion` | Round26AQTerminalRigidityClosure | non | IMPLIQUE RH SOUS PRÉMISSE (FullCoupledRigidityOfflineExclusion, équivalente à l'exclusion hors ligne) | Sous FullCoupledRigidityOfflineExclusion, tout représentant positif à toute hauteur T est sur la ligne critique. |
| `riemann_hypothesis_of_full_coupled_rigidity_exclusion` | Round26AQTerminalRigidityClosure | non | IMPLIQUE RH SOUS PRÉMISSE (FullCoupledRigidityOfflineExclusion, équivalente à l'exclusion hors ligne) | FullCoupledRigidityOfflineExclusion entraîne que tout zéro non trivial vérifie Re = 1/2. |
| `relational_bundle_exclusion_iff_offline_exclusion` | Round26ARRelationalRigidityRecovery | non | ÉQUIVALENTE À RH | Exclure toute configuration hors ligne portant le paquet relationnel équivaut à exclure toute configuration hors ligne. |
| `rh_of_relational_bundle_exclusion` | Round26ARRelationalRigidityRecovery | non | IMPLIQUE RH SOUS PRÉMISSE (exclusion de toute configuration hors ligne portant le paquet relationnel, équivalente à l'exclusion hors ligne) | Si toute configuration hors ligne portant le paquet relationnel est exclue, tout zéro non trivial vérifie Re = 1/2. |
| `critical_line_of_defectColumnMeetsChangeFamily_and_compatibility` | Round26AUReflectedDefectEventuality | non | IMPLIQUE RH SOUS PRÉMISSE (DefectColumnMeetsChangeFamily et ReflectedChangeFamilyCompatibility, cette dernière équivalente à RH) | Si DefectColumnMeetsChangeFamily et ReflectedChangeFamilyCompatibility tiennent, tout zéro non trivial a partie réelle 1/2. |
| `riemannHypothesis_of_defectColumnMeetsChangeFamily_and_compatibility` | Round26AUReflectedDefectEventuality | non | IMPLIQUE RH SOUS PRÉMISSE (DefectColumnMeetsChangeFamily et ReflectedChangeFamilyCompatibility, cette dernière équivalente à RH) | Si DefectColumnMeetsChangeFamily et ReflectedChangeFamilyCompatibility tiennent, alors RH (énoncé Mathlib). |
| `riemannHypothesis_of_reflectedDifferenceEventuallyStrict_and_compatibility` | Round26AUReflectedDefectEventuality | non | IMPLIQUE RH SOUS PRÉMISSE (croissance stricte finale, prouvée ailleurs, et ReflectedChangeFamilyCompatibility équivalente à RH) | Si la différence réfléchie est finalement strictement croissante en norme et que ReflectedChangeFamilyCompatibility tient, alors RH. |
| `reflectedChangeFamilyCompatibility_of_RH` | Round26AUReflectedDefectEventuality | non | CONFIRMÉE SOUS CONDITION (RH supposée) | RH implique ReflectedChangeFamilyCompatibility. |
| `reflectedChangeFamilyCompatibility_iff_RH_of_eventualStrict` | Round26AUReflectedDefectEventuality | non | ÉQUIVALENTE À RH (ReflectedChangeFamilyCompatibility ↔ RH, sous une hypothèse que le lot établit inconditionnellement dans reflectedDifferenceEventuallyStrictOnPrimes_proved) | Sous la croissance stricte finale de la différence réfléchie, ReflectedChangeFamilyCompatibility équivaut à RH. |
| `reflectedChangeFamilyCompatibility_iff_RH` | Round26AVReflectedDifferenceClosedForm | non | ÉQUIVALENTE À RH | ReflectedChangeFamilyCompatibility équivaut à RH, sans hypothèse. |
| `all_zeroGapRigidity_iff_global_critical_line` | Round26AZZeroGapGrammarRigidity | non | ÉQUIVALENTE À RH | La rigidité ZeroGapRigidity T pour tout T équivaut à ce que tout zéro non trivial ait partie réelle 1/2. |
| `all_height_card_equal_iff_global_critical_line` | Round26B4ConstellationReflectionInvolution | non | ÉQUIVALENTE À RH (le membre droit est l'énoncé de RiemannHypothesis pour les zéros non triviaux) | Pour toute hauteur T, le nombre de hauteurs distinctes de la constellation égale son cardinal si et seulement si tout zéro non trivial est de partie réelle 1/2. |

## 1. Table vérité → théorèmes

Pour chaque Vi touchée : effectif, statut le plus fort atteint (ordre : ÉQUIVALENTE > IMPLIQUE > RÉFUTATION > CONFIRMÉE) et théorèmes (12 premiers, puis « et N autres »). Attribution des Vi = celle posée par le relecteur à la lecture du type.

| Vi | énoncé du maître (abrégé) | nb | statut le plus fort | théorèmes |
|---|---|---|---|---|
| V7 | Chaque zéro considéré a partie réelle strictement entre 0 et 1, partie imaginaire strictement positive, et existence issue de la seule théorie analytique de zêta. | 4 | CONFIRMÉE | `nontrivialZetaZero_ne_zero`, `nontrivialZetaZero_ne_one`, `Kadiri.riemannZeta_ne_zero_of_re_nonpos_im_ne_zero`, `Kadiri.positiveHeightZero_re_mem_Ioo` |
| V8 | L'ensemble des vrais zéros est ordonné par partie imaginaire croissante puis partie réelle croissante ; cet ordre est celui de l'énumération et n'est jamais un argument s | 17 | CONFIRMÉE SOUS CONDITION | `ScientificRebuild20260901.ZeroPassage.ordered`, `ScientificRebuild20260901.ThreeZeroWindow.order01`, `ScientificRebuild20260901.ThreeZeroWindow.order12`, `RigidCoupledZeroPrimeGrammar.zeroRows_eq_canonical`, `RigidCoupledZeroPrimeGrammar.zeroRows_ordered`, `RigidCoupledZeroPrimeGrammar.zeroGaps_nonneg`, `_private.RhGapCriterion.Round26ASTerminalJunctionExhaustion.0.mem_orderedPositiveRepresentatives_of_mem_positive`, `AlignedOfflinePrimeJunction.row_member`, `AlignedOfflinePrimeJunction.reflected_row_member`, `constellationHeights_pairwise_le`, `constellationGaps_nonneg`, `constellationWindowHeights_pairwise_le` et 5 autres |
| V17 | Le pas de log-rayon entre deux croisements consécutifs ne dépend que de T ; il n'est pas un écart entre nombres premiers. | 6 | CONFIRMÉE SOUS CONDITION | `ScientificRebuild20260901.TrueMemberContactCell.contactWidth`, `ScientificRebuild20260901.offMirror_contactPair_deformation`, `ScientificRebuild20260901.towerSpan_sub`, `ScientificRebuild20260901.towerSpanDifference_eq_zero_iff`, `ScientificRebuild20260901.threeZero_twoGap_tower_prime_rigidity`, `ScientificRebuild20260901.threeZero_twoGap_span_laws` |
| V20 | La Tour a exactement deux contacts avec l'axe algébrique : l'incidence d'entrée et le dernier rayon ; ils délimitent l'unique cellule de l'état propre, contenant un ou pl | 1 | CONFIRMÉE | `ScientificRebuild20260901.TrueMemberContactCell.contacts_length` |
| V26 | L'état propre est précisément (incidence d'entrée, dernier rayon) ; ce sont des rayons, pas des premiers ; ils délimitent un intervalle algébrique unique contenant un ou  | 2 | CONFIRMÉE | `ScientificRebuild20260901.TrueMemberContactCell.contactPair_fst`, `ScientificRebuild20260901.TrueMemberContactCell.contactPair_snd` |
| V27 | Le zéro a un rang dans la source des zéros ; la grammaire première reconstruite lui assigne son occurrence (le premier de ce rang) ; ce lien est établi et n'est pas un ch | 3 | CONFIRMÉE | `FullRigidCoupledZeroPrimeGrammar.rank_density_exact`, `FullRigidCoupledZeroPrimeGrammar.rank_density_strict`, `AlignedOfflinePrimeJunction.window_rank_theta_rigidity` |
| V45 | Propriété centrale, l'inversion : les deux contacts redonnent exactement T par leur rapport, puis β par la loi tangentielle ; elle certifie que les contacts appartiennent | 2 | CONFIRMÉE | `ScientificRebuild20260901.TrueMemberContactCell.recoversGamma`, `ScientificRebuild20260901.TrueMemberContactCell.recoversBeta` |
| V47 | On applique le comptage de Von Mangoldt et Chebyshev à l'unique histoire première. — §6, l. 61 — définition d'usage. | 1 | CONFIRMÉE | `InverseSignatureConcrete.exact_meta_reconstruction_identity` |
| V48 | La première partie de la démonstration reconstruit la grammaire première depuis les zéros : le canal Chebyshev/Von Mangoldt redonne exactement l'unique histoire (poids, p | 72 | CONFIRMÉE SOUS CONDITION | `chebyshevθ_eq_zerosPrimeCountReal_abel_raw`, `CoupledRigidGrammar.reconstructed_block_eq_prime`, `CoupledRigidGrammar.zero_source_encoding_eq_reconstructed_block`, `CoupledRigidGrammar.MZ_eq_M`, `CoupledRigidGrammar.zero_source_encoding_eq_MZ`, `CoupledRigidGrammar.zero_source_encoding_eq_M`, `e44RecoveredDeltaPsi_eq_deltaPsi`, `e44_certified_prime_position`, `e44_certified_prime_gap`, `E44GrammarArithmeticState.recoveredDeltaPsi_exact`, `InverseSignatureConcrete.exact_meta_reconstruction_identity`, `ScientificRebuild20260901.PrimeEventEnvironment.incoming_vonMangoldt_lock` et 60 autres |
| V49 | Cette reconstruction rigidifie la relation zéros/premiers : chaque zéro porte sa place dans l'ordre des zéros ; la grammaire lui assigne à cette place et à nulle autre so | 6 | CONFIRMÉE | `InverseSignatureConcrete.exact_meta_reconstruction_identity`, `zero_reconstructed_signed_correlation_eq`, `zero_reconstructed_diagonal_increment_mass_eq`, `gram_weighted_R_sq_eq_zero_reconstructed_diagonal_add_signed_correlation`, `FullRigidCoupledZeroPrimeGrammar.reconstructed_order`, `AlignedOfflinePrimeJunction.active_zero_source_encoding_eq_M` |
| V50 | Lorsque plusieurs zéros partagent la même partie imaginaire, la fibre de cette partie imaginaire est finie, ordonne ces zéros et fournit leur passage consécutif. | 2 | CONFIRMÉE SOUS CONDITION | `off_critical_line_gives_zero_constellation_gap`, `constellationHeights_pairwise_le` |
| V60 | Il ne faut jamais décorréler la grammaire des zéros de la grammaire première : elles sont liées indéfectiblement. | 27 | CONFIRMÉE SOUS CONDITION | `prime_zero_bridge_restriction17`, `CoupledRigidGrammar.reconstructed_block_eq_prime`, `CoupledRigidGrammar.prime_history_determines_zero_source`, `CoupledRigidGrammar.MZ_eq_M`, `CoupledRigidGrammar.zero_source_encoding_eq_M`, `CoupledRigidGrammar.any_count_position_gap_object_eq`, `CoupledRigidGrammar.primes_determine_zero_source`, `zero_reconstructed_signed_correlation_eq`, `zero_reconstructed_diagonal_increment_mass_eq`, `gram_weighted_R_sq_eq_zero_reconstructed_diagonal_add_signed_correlation`, `zero_completeGrammarBlock_rigid`, `RigidCoupledZeroPrimeGrammar.source_encodes_prime` et 15 autres |
| V62 | Hors droite critique, la symétrie fonctionnelle produit un second vrai zéro distinct ; les points clés sont ceux de zeta23. | 13 | IMPLIQUE RH SOUS PRÉMISSE | `functional_symmetry_forces_half`, `theoremF_RH_from_T_spectral_rigidity`, `functional_symmetry_forces_exact_half`, `RH_from_density_order_scale_rigidity`, `translated_scale_invariance_closes_RH17`, `isNontrivialZetaZero_one_sub`, `_private.RhGapCriterion.P4Port.IEANTN.HadamardLogDerivative.0.Kadiri.completedZetaFactor_one_sub`, `_private.RhGapCriterion.P4Port.IEANTN.HadamardLogDerivative.0.Kadiri.logDeriv_completedZetaFactor_one_sub`, `offline_member_realises_zero_gap`, `off_critical_line_gives_table_height_collision`, `off_critical_line_gives_height_collision`, `offLineMembers_reflect_ne` et 1 autres |
| V63 | D'un zéro hors ligne naissent quatre zéros de même multiplicité : ρ, son conjugué, son miroir fonctionnel (1 − conjugué), et le zéro réfléchi (1 − ρ, conjugué du miroir). | 36 | CONFIRMÉE SOUS CONDITION | `isNontrivialZetaZero_one_sub`, `offline_zero_orbit_contribution`, `Kadiri.riemannZetaConjZeroSource_of_riemannZeta_conj`, `Kadiri.zeroImagDyadicAbsToPositiveCountWithZeroHeightSource_of_conj`, `Kadiri.zeroImagDyadicCumulativeCountByNWithZeroHeightSource_of_conj_and_order_summable`, `Kadiri.riemannZeta_order_conj`, `reflectedPairRatio_exponent_eq_ofReal`, `two_scale_ratio_relation_reflection_blind`, `rescaledZeroSideChannel_eq_left_add_right_add_rest`, `_private.RhGapCriterion.Round26ASTerminalJunctionExhaustion.0.reflectConjZero_mem_positiveRepresentatives`, `AlignedOfflinePrimeJunction.reflected_row_member`, `AlignedOfflinePrimeJunction.rightCell_member` et 24 autres |
| V64 | L'énumération de la source ne compte que les zéros de partie imaginaire positive ; parmi les quatre, deux sont membres (le zéro et son miroir) et portent deux événements  | 9 | CONFIRMÉE SOUS CONDITION | `Kadiri.riemannZetaConjZeroSource_of_riemannZeta_conj`, `Kadiri.zeroImagDyadicAbsToPositiveCountWithZeroHeightSource_of_conj`, `Kadiri.zeroImagDyadicAbsToPositiveCountWithZeroHeightSource_of_riemannZeta_conj`, `Kadiri.zeroImagDyadicCumulativeCountByNWithZeroHeightSource_of_conj_and_order_summable`, `RigidCoupledZeroPrimeGrammar.zeroRows_eq_canonical`, `_private.RhGapCriterion.Round26ASTerminalJunctionExhaustion.0.reflectConjZero_mem_positiveRepresentatives`, `AlignedOfflinePrimeJunction.reflected_row_member`, `conjugate_rows_distinct`, `_private.RhGapCriterion.Round26B4ConstellationRefinementTable.0.heightConstellation_conj_mem` |
| V65 | Le miroir a la même partie imaginaire que le zéro, partie réelle complément à un, même multiplicité ; cette contrainte est créée par zêta et compilée. | 21 | CONFIRMÉE SOUS CONDITION | `projectMirror_coe_eq_trustedMirror`, `e44RadialDefect_mirror_sum`, `ScientificRebuild20260901.functionalMirror_gamma`, `ScientificRebuild20260901.functionalMirror_beta`, `reflectedPairRatio_exponent_eq_ofReal`, `reflect_signed_distance`, `offline_mirror_invariant`, `offline_member_realises_zero_gap`, `reflectConj_re`, `reflectConj_im`, `zetaZeroMultiplicity_reflectConj`, `isNontrivialZetaZero_reflectConj` et 9 autres |
| V66 | Cette contrainte rend nulle la progression de T entre les deux zéros de la paire (le suivant d'un OFF est son miroir) et donne deux parties réelles dont l'une est un moin | 5 | CONFIRMÉE SOUS CONDITION | `ScientificRebuild20260901.offMirror_zeroHeightGap_but_lossless`, `ScientificRebuild20260901.off_creates_actual_ordered_zeroPassage`, `RigidCoupledZeroPrimeGrammar.offline_forces_zero_gap`, `FullRigidCoupledZeroPrimeGrammar.offline_forces_zero_gap`, `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.zero_height_gap` |
| V74 | Hors ligne, le miroir est un membre authentique et distinct : vrai zéro, différent, strictement postérieur, d'index avancé, d'occurrence au moins le minimum attendu ; « t | 1 | CONFIRMÉE | `AlignedOfflinePrimeJunction.rows_distinct` |
| V77 | Sur la droite, le zéro et son miroir sont confondus ; la seconde orientation y est la Tour du conjugué, sur le même anneau, lue par le bas : rien ne se contredit. | 1 | CONFIRMÉE SOUS CONDITION | `one_sub_eq_conj_of_re_eq_half` |
| V101 | L'inversion est la conjugaison de ce terme (terme du conjugué = conjugué du terme, partie imaginaire opposée, somme réelle) : le nombre imaginaire, source de l'inversion. | 6 | CONFIRMÉE | `offlineZeroOrbitFinset_sum_of_im_ne_zero`, `offlineZeroAmplitude_conj`, `offlineZeroAmplitude_conj_norm`, `nontrivialZeroResidueTerm_conj`, `collective_projection_conj_invariant`, `collective_projection_im_eq_zero` |
| V102 | La position radiale entre dans l'amplitude du terme : hors ligne l'amplitude du miroir domine celle du zéro original ; sur la droite elles sont égales. | 23 | RÉFUTATION COMPILÉE | `zero_scale_eigenvalue_abs`, `offline_zero_forces_exponential_scale_growth`, `exact_metapattern_excludes_exponential_scale_growth`, `offline_zero_incompatible_with_exact_prime_gap_metapattern_conditional`, `offline_zero_channel_incompatible_conditional`, `offline_zero_orbit_energy_eq`, `zeroMode_norm`, `reflectedPairRatio_scale_rpow`, `reflectedPairRatio_eq_rpow_mul_one`, `reflectedPairRatio_eq_at_distinct_positive_scales_forces_critical_line`, `reflectedPairRatio_eq_one_of_critical_line`, `reflectedPairRatio_eq_at_distinct_positive_scales_iff_critical_line` et 11 autres |
| V110 | « Donc aucun zéro distinct ne peut exister hors de la droite critique. Tout vrai zéro a sa partie réelle égale à un demi. C'est l'hypothèse de Riemann. » — §9, l. 115 — c | 8 | IMPLIQUE RH SOUS PRÉMISSE | `critical_line_of_primeForcedTwoScaleRatioRecurrence`, `no_offline_zero_of_channel_and_rest_subexponential`, `re_le_half_of_channel_and_rest_subexponential`, `critical_line_of_channel_and_rest_subexponential`, `critical_line_of_singlePrimeScaleCharacterCoincidence`, `all_positiveRepresentatives_on_critical_line_of_exclusion`, `riemann_hypothesis_of_full_coupled_rigidity_exclusion`, `rh_of_relational_bundle_exclusion` |
| V116 | Ce qui définit une preuve : terme final `RiemannHypothesis` dépendant des seuls axiomes standard, sans `sorry`, `admit`, axiome ajouté ni hypothèse non déchargée. | 9 | ÉQUIVALENTE À RH | `riemann_hypothesis_of_primeForcedTwoScaleRatioRecurrence`, `riemann_hypothesis_of_primeScaleForcedRatioRecurrence`, `primeForcedTwoScaleRatioRecurrence_iff_riemannHypothesis`, `primeScaleForcedRatioRecurrence_iff_riemannHypothesis`, `riemannHypothesis_of_channel_and_rest_subexponential`, `riemannHypothesis_of_singlePrimeScaleCharacterCoincidence`, `singlePrimeScaleCharacterCoincidence_iff_riemannHypothesis`, `full_coupled_rigidity_exclusion_iff_offline_exclusion`, `riemann_hypothesis_of_full_coupled_rigidity_exclusion` |
| V117 | Une hypothèse exigée de tout zéro de côté β < 1/2 dont le corps est insatisfiable est RH elle-même et ne ferme rien. | 2 | ÉQUIVALENTE À RH | `full_coupled_rigidity_exclusion_iff_offline_exclusion`, `relational_bundle_exclusion_iff_offline_exclusion` |
| V121 | La fonction de Tchebychev, sa reconstruction exacte depuis les zéros et la formule explicite lissée qui l'exprime comme somme sur tous les zéros sont pleinement compilées | 23 | CONFIRMÉE SOUS CONDITION | `offline_zero_Pi_orbit_rest_decomposition`, `offline_zero_psi_recovered_orbit_rest_decomposition`, `zeroChannel_eq_rescaled_nontrivial_zero_part_of_smoothedVonMangoldtSum`, `rescaledZeroSideChannel_eq_left_add_right_add_rest`, `RigidCoupledZeroPrimeGrammar.totalColumnBridge`, `FullRigidCoupledZeroPrimeGrammar.reconstructed_density`, `AlignedOfflinePrimeJunction.active_primes_determine_exact_zero_source`, `AlignedOfflinePrimeJunction.active_total_column_bridge`, `AlignedOfflinePrimeJunction.individual_defect_and_collective_prime_bridge_coexist`, `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.source_roundtrip`, `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.total_bridge`, `psiRecoveredFromZeros_conj_eq_self` et 11 autres |
| V124 | La formule explicite compilée ne contraint que la somme de tous les termes de tous les zéros, jamais un terme isolé. | 12 | CONFIRMÉE SOUS CONDITION | `offline_forces_total_plus_rest_exponential_lower_bound`, `offline_reflected_pair_forces_rest_exponential_growth`, `AlignedOfflinePrimeJunction.individual_defect_and_collective_prime_bridge_coexist`, `AlignedOfflinePrimeJunction.active_finite_collective_projection_row_swap_invariant`, `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.total_bridge`, `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.finite_collective_swap_blind`, `tsum_reflectConjZero`, `zero_channel_reflection_invariant`, `smoothedZeroFormula_sub_background_reflection_invariant`, `collective_column_projection`, `collective_block_projection`, `collective_block_projection_columns` |
| V127 | Compilé : le côté premier de la formule explicite compte les membres et non les événements, un terme par zéro ; une paire hors ligne y est deux termes distincts à même fr | 11 | CONFIRMÉE SOUS CONDITION | `zeroGrammar_family_eq_transitions`, `RigidCoupledZeroPrimeGrammar.tableEntry_exact`, `offline_orbit_internal_defect_ge_two`, `offline_defect_column_grammar_dichotomy`, `AlignedOfflinePrimeJunction.defect`, `AlignedOfflinePrimeJunction.active_table_entries_differ`, `AlignedOfflinePrimeJunction.active_defect_weight_dichotomy`, `AlignedOfflinePrimeJunction.zero_gap_position_and_prime_defect_column_coexist`, `AlignedOfflinePrimeJunction.individual_defect_and_collective_prime_bridge_coexist`, `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.table_defect`, `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.weight_dichotomy` |
| V131 | La grammaire par hauteurs est déjà la représentation non bifurquée et tolère un zéro hors ligne (même premier au membre et à son miroir) : la non-bifurcation ne force pas | 5 | CONFIRMÉE SOUS CONDITION | `offline_member_leaves_reconstructed_grammar_unchanged`, `offline_member_leaves_reconstructed_pattern_block_unchanged`, `offline_member_leaves_reconstructed_prime_gap_unchanged`, `crosswalk_labels_row_independent`, `crosswalk_height_collision_labels_row_independent` |
| V157 | Cette chaîne est garantie par les théorèmes du maître : identité Tour ↔ terme du zéro dans la formule explicite compilée (§9, §11) et lien contacts ↔ comptage Tchebychev/ | 1 | CONFIRMÉE | `offline_zero_channel_eq_zeroMode` |
| V158 | Les deux coordonnées jouent des rôles différents : la hauteur gouverne le rythme et l'échelle de la progression ; la position radiale déplace phase, contacts et amplitude | 1 | RÉFUTATION COMPILÉE | `AlignedOfflinePrimeJunction.injective_placement_cannot_be_height_only` |
| V159 | En projetant la Tour sur la grammaire première (rangs, occurrences, écarts, transitions, ordre) une partie de l'information disparaît ; la grammaire décrit correctement l | 14 | RÉFUTATION COMPILÉE | `zeroMemberTransition_height_blind`, `GZ_transition_does_not_determine_internal_gap`, `GZ_internal_gap_does_not_determine_transition`, `offline_blindness_coexists_with_restored_rigidity`, `rigid_coupled_offline_snapshot`, `FullRigidCoupledZeroPrimeGrammar.universal_position_gap_transport`, `FullRigidCoupledZeroPrimeGrammar.universal_count_position_gap_transport`, `relational_bundle_no_strength_gain`, `AlignedOfflinePrimeJunction.same_column_same_prime_labels_different_entries`, `AlignedOfflinePrimeJunction.active_zero_height_gap_and_prime_gap_coexist`, `AlignedOfflinePrimeJunction.naive_prime_label_entry_uniqueness_is_impossible_under_offline`, `AlignedOfflinePrimeJunction.window_universal_MZ_transport` et 2 autres |
| V161 | Sur la ligne critique, l'image d'un zéro par la symétrie retombe sur lui-même : un seul point à cette hauteur, une seule Tour ; la composante horizontale (séparation zéro | 24 | ÉQUIVALENTE À RH | `reflectedPairRatio_eq_one_of_critical_line`, `reflectedPair_single_scale_character_eq_forces_reflect_fixed`, `reflectedPair_prime_hypothesis_not_needed`, `singlePrimeScaleCharacterCoincidence_of_riemannHypothesis`, `auditedAlignedOfflineExclusion_iff_truncated_critical_line`, `zeroGapRigidity_of_critical_line`, `zeroGapRigidity_iff_critical_line`, `critical_line_constellation_has_no_zero_gap`, `distinct_same_height_off_critical_line`, `constellationHeights_pairwise_lt_of_critical_line`, `constellationGaps_pos_of_critical_line`, `constellation_gaps_pos_iff_critical_line` et 12 autres |
| V162 | Hors ligne, la symétrie produit réellement un second zéro à la même hauteur (jamais un point recopié) ; les deux ont chacun leur Tour, même hauteur, positions radiales di | 52 | ÉQUIVALENTE À RH | `CoupledRigidGrammar.offline_snapshot`, `no_offline_of_heightDetermined_leftInverse`, `no_offline_of_heightDetermined_primePlacement_leftInverse`, `RigidCoupledZeroPrimeGrammar.offline_forces_zero_gap`, `rigid_coupled_offline_snapshot`, `FullRigidCoupledZeroPrimeGrammar.offline_forces_zero_gap`, `all_constellation_gaps_strictly_positive_of_exclusion`, `all_height_constellations_preserve_height_cardinality_of_exclusion`, `full_coupled_rigidity_offline_snapshot`, `offline_orbit_internal_defect_ge_two`, `offline_defect_column_grammar_dichotomy`, `relational_rigidity_recovery` et 40 autres |
| V163 | Théorème compilé : hors ligne, aucun contact du miroir ne coïncide avec un contact du zéro original ; le raccord entre leurs occurrences est une égalité d'entiers, jamais | 3 | CONFIRMÉE SOUS CONDITION | `ScientificRebuild20260901.offMirror_leftContact_ne`, `ScientificRebuild20260901.offMirror_rightContact_ne`, `ScientificRebuild20260901.offMirror_contactPair_deformation` |
| V172 | Le terme énergétique de chaque zéro est déjà un objet isolé propre à ce zéro, jamais mélangé aux autres ; le pointeur zéro → premier de référence est établi sans conditio | 1 | CONFIRMÉE | `offline_zero_channel_eq_zeroMode` |
| V174 | L'énoncé de M^Z = M / rigidité mod 6 : (i) tout premier > 3 est en état A (6k−1, résidu 5) ou B (6k+1, résidu 1) ; (ii) l'écart mod 6 entre deux tels premiers ne prend qu | 83 | RÉFUTATION COMPILÉE | `class_partition`, `gnat_class_even`, `prime_mod6_state`, `gap_mod6_exhaustive`, `transition_exhaustive`, `class_projection_complete`, `pattern_is_grammar_path`, `pattern_family_closure`, `meta_pattern_grammar_finite`, `CoupledRigidGrammar.reconstructed_block_eq_prime`, `CoupledRigidGrammar.zero_source_encoding_eq_reconstructed_block`, `CoupledRigidGrammar.MZ_eq_M` et 71 autres |
| V175 | La grammaire historique (regroupement en motifs, familles, ordre, méta-pattern visant `M^Z = M`) existe dans la recherche historique du dépôt depuis l'origine ; note E094 | 18 | CONFIRMÉE SOUS CONDITION | `canonical_family_occurs_in_both_histories`, `canonical_pattern_occurs_in_both_histories`, `EarlyMultiLevelDisturbance.familyOccursPrime`, `EarlyMultiLevelDisturbance.familyOccursReconstructed`, `EarlyMultiLevelDisturbance.patternOccursPrime`, `EarlyMultiLevelDisturbance.patternOccursReconstructed`, `offline_member_leaves_complete_grammar_unchanged`, `offline_member_leaves_any_count_position_gap_object_unchanged`, `offline_transitions_unchanged`, `offline_pattern_unchanged`, `offline_family_unchanged`, `offline_positions_order_unchanged` et 6 autres |
| V176 | La hiérarchie plus large (motifs, familles, méta-pattern) demeure descriptive et historique, jamais portée dans le code compilé RHV6Fresh ; seule la première couche (état | 20 | CONFIRMÉE | `pattern_is_grammar_path`, `pattern_family_closure`, `meta_pattern_grammar_finite`, `T_increment_not_grammar_function`, `T_increment_not_mod6_projection_function`, `FullRigidCoupledZeroPrimeGrammar.meta_pattern_finite`, `FullRigidCoupledZeroPrimeGrammar.transition_succession_exact`, `FullRigidCoupledZeroPrimeGrammar.family_succession_exact`, `FullRigidCoupledZeroPrimeGrammar.pattern_succession_exact`, `FullRigidCoupledZeroPrimeGrammar.reconstructed_transition_succession`, `FullRigidCoupledZeroPrimeGrammar.reconstructed_family_succession`, `FullRigidCoupledZeroPrimeGrammar.reconstructed_pattern_succession` et 8 autres |
| V180 | Vérité 1 : un zéro et son miroir tirent horizontalement en sens opposés ; résultante nulle pour tout zéro ; tension propre (2δ²) nulle seulement sur la ligne. | 2 | CONFIRMÉE | `two_scale_ratio_relation_reflection_blind`, `reflect_signed_distance` |
| V188 | Échelle `premise_ladder_tfae` : pas de passage nul ⟺ exclusion horizontale ⟺ superposition ⟺ absence d'entrelacement strict ⟺ D ≡ 0 ⟺ RH. — l. 207 — théorème compilé. Lea | 3 | ÉQUIVALENTE À RH | `all_constellation_gaps_strictly_positive_of_exclusion`, `all_height_constellations_preserve_height_cardinality_of_exclusion`, `all_zeroGapRigidity_iff_global_critical_line` |
| V189 | Verdict honnête : la prémisse est remplacée par sa forme la plus atomique (un réel par zéro, D(z) = 0), mais reste équivalente à RH ; la géométrie des Tours n'en décharge | 3 | ÉQUIVALENTE À RH | `relational_bundle_no_strength_gain`, `relational_bundle_exclusion_iff_offline_exclusion`, `rh_of_relational_bundle_exclusion` |

Théorèmes sans Vi (`AJOUT`) : 2082 sur 2467.

## 2. Ajouts proposés

Formulations candidates, chacune adossée à des théorèmes compilés du lot (lecture du type ; prémisses conservées dans l'énoncé).

- (AJ1) Le critère de gaps `RhGap.RH` (prédicat du projet, distinct du `RiemannHypothesis` de Mathlib) équivaut, sous von Koch/Schoenfeld, à une borne en racine(p_m)·log² sur le résidu recentré, puis sur le mode total recentré. Établissent : `gap_criterion`, `gap_criterion_vonKoch_only`, `mode_criterion_vonKoch_only`, `theoremB` (module `Basic`) — statut ÉQUIVALENTE À RH (au sens du prédicat du projet).
- (AJ2) Les verrous `PrimeForcedTwoScaleRatioRecurrence`, `PrimeScaleForcedRatioRecurrence` et `SinglePrimeScaleCharacterCoincidence` sont chacun équivalents à `RiemannHypothesis` (donc entre eux) : `primeForcedTwoScaleRatioRecurrence_iff_riemannHypothesis`, `primeScaleForcedRatioRecurrence_iff_riemannHypothesis`, `singlePrimeScaleCharacterCoincidence_iff_riemannHypothesis`, `primeScaleForcedRatioRecurrence_iff_primeForcedTwoScaleRatioRecurrence`.
- (AJ3) `ReflectedChangeFamilyCompatibility` équivaut à RH sans hypothèse (`reflectedChangeFamilyCompatibility_iff_RH`) ; toute conclusion RH tirée de cette prémisse est donc circulaire (`riemannHypothesis_of_defectColumnMeetsChangeFamily_and_compatibility`, `riemannHypothesis_of_reflectedDifferenceEventuallyStrict_and_compatibility`).
- (AJ4) Exclure toute configuration hors ligne (avec ou sans paquet relationnel, ou sous `FullCoupledRigidityOfflineExclusion`) équivaut à l'exclusion hors ligne quantifiée en T et ρ : `full_coupled_rigidity_exclusion_iff_offline_exclusion`, `relational_bundle_exclusion_iff_offline_exclusion`.
- (AJ5) La rigidité de gaps de zéros à toute hauteur et l'égalité, à toute hauteur, du nombre de hauteurs distinctes et du cardinal de la constellation équivalent chacune à « tout zéro non trivial a Re = 1/2 » : `all_zeroGapRigidity_iff_global_critical_line`, `all_height_card_equal_iff_global_critical_line`.
- (AJ6) Hors ligne, aucune constellation sur la ligne critique n'est comparable (même cardinal, mêmes hauteurs) à une constellation contenant un membre hors ligne : `no_comparable_constellations_differing_only_by_off_line_membership`, `no_on_line_constellation_comparable_to_offline_heightConstellation`, `not_comparableOffLineConstellationPairExists`.
- (AJ7) Avec un témoin hors ligne : l'unicité d'entrée par labels premiers est fausse, un placement injectif ne peut pas être déterminé par la seule hauteur, et le rapport réfléchi/les caractères d'échelle se séparent à deux premiers distincts : `naive_prime_label_entry_uniqueness_is_impossible_under_offline`, `injective_placement_cannot_be_height_only`, `reflected_pair_ratio_recurrence_fails_at_distinct_primes`, `two_prime_scale_character_faithfulness_separates_reflected_pair` (module `Round26ASTerminalJunctionExhaustion`).
- (AJ8) Pour un zéro de partie réelle ≠ 1/2, aucun décodeur de contact ne lit un bloc de grammaire complet (canonique premier, ou reconstruit depuis les zéros) de façon à satisfaire la loi E44 à la fois pour Re ρ et 1−Re ρ : `no_shared_completeGrammar_contact_readout_for_true_offline`, `no_prime_completeGrammar_memberwise_common_contact_for_true_offline`, `no_zero_reconstructed_completeGrammar_memberwise_common_contact_for_true_offline`.
- (AJ9) Deux premiers distincts ne satisfont jamais N·log b = M·log a avec M>0 : `nat_prime_log_relation_absurd`.
- (AJ10) Le bloc construit sur les fonctions nulles n'est pas rigide (`grammarRigid_not_automatic`) ; la circulation quantifiée d'états n'admet aucun potentiel-plus-reste (`circulation_obstruction_quantized_complete_state`, `circulation_obstruction_decade_cells`).

## 3. Cascades

Les 12 théorèmes du lot les plus utilisés (dépendances inverses sur tout `rh_gap_criterion.jsonl`). Énoncé des conséquences : glose du lot quand le théorème y figure, sinon première phrase de la docstring (aide, marquée « doc. ») ou « sans docstring ».

**`p_strictMono`** (`Basic`) — La suite des premiers p est strictement croissante.  
Cette vérité est confirmée (CONFIRMÉE) et provoque la série de conséquences suivantes (116 théorèmes au total) : `le_p` (Pour tout n, n <= p n.); `p_odd` (Pour n >= 1, p n est impair.); `gnat_even` (Pour n >= 1, le gap gnat n est pair.); `p_one` (Le deuxième premier est p 1 = 3.); `p_two` (Le troisième premier est p 2 = 5.); `prime_mod6_state` (Pour n >= 2, p n mod 6 vaut 1 ou 5 (états de la grammaire).); `class_projection_complete` (Pour n >= 2, classe 0 du gap si et seulement si état mod 6 conservé, classe 2 si et seulement si transition 5 vers 1, classe 4 si et seulement si tran); `p_three` (Le quatrième premier est p 3 = 7.); `p_four` (Le cinquième premier est p 4 = 11.); `p_five` (Le sixième premier est p 5 = 13.) ; et 106 autres.

**`p_prime`** (`Basic`) — Pour tout n, p n est premier.  
Cette vérité est confirmée (CONFIRMÉE) et provoque la série de conséquences suivantes (58 théorèmes au total) : `two_le_p` (Pour tout n, 2 <= p n.); `p_succ_le_of_prime_gt` (Si q est premier et p m < q alors p (m+1) <= q : p (m+1) est le plus petit premier supérieur à p m.); `p_succ_le_two_mul` (Postulat de Bertrand sur la suite des premiers : p (m+1) <= 2 p m.); `p_odd` (Pour n >= 1, p n est impair.); `p_two` (Le troisième premier est p 2 = 5.); `prime_mod6_state` (Pour n >= 2, p n mod 6 vaut 1 ou 5 (états de la grammaire).); `p_three` (Le quatrième premier est p 3 = 7.); `p_four` (Le cinquième premier est p 4 = 11.); `p_five` (Le sixième premier est p 5 = 13.); `p_step` (Si p k = a, b est premier, a < b et aucun premier n'existe strictement entre a et b, alors p (k+1) = b (pas élémentaire).) ; et 48 autres.

**`prime_mod6_state`** (`Basic`) — Pour n >= 2, p n mod 6 vaut 1 ou 5 (états de la grammaire).  
Cette vérité est confirmée (CONFIRMÉE (domaine : 2 <= n)) et provoque la série de conséquences suivantes (49 théorèmes au total) : `transition_exhaustive` (Pour n >= 2, la transition (p n mod 6, p (n+1) mod 6) est l'une des quatre paires de {1,5} x {1,5}.); `class_projection_complete` (Pour n >= 2, classe 0 du gap si et seulement si état mod 6 conservé, classe 2 si et seulement si transition 5 vers 1, classe 4 si et seulement si tran); `pattern_is_grammar_path` (Pour n >= 2 et tout k, chaque étape i<k du pattern relie deux états de {1,5} et la classe du gap est exactement la projection de la transition.); `prime_completeGrammarBlock_rigid` (Pour n ≥ 2, le bloc de grammaire complet premier canonique est rigide.); `grammarPotentialV2_prime_eq_zero_iff` (Pour n au moins 2, le potentiel de grammaire du premier p n mod 6 vaut 0 si et seulement si p n mod 6 vaut 1 (état B).); `grammarPotentialV2_prime_eq_one_iff` (Pour n au moins 2, le potentiel de grammaire du premier p n mod 6 vaut 1 si et seulement si p n mod 6 vaut 5 (état A).); `grammarTransformIndicator_tau11_eq` (Pour n au moins 2, l'indicateur de la transformation 1-vers-1 est le produit (1 - potentiel(p n mod 6)) fois (1 - potentiel(p(n+1) mod 6)).); `grammarTransformIndicator_tau15_eq` (Pour n au moins 2, l'indicateur de la transformation 1-vers-5 est (1 - potentiel(p n mod 6)) fois potentiel(p(n+1) mod 6).); `grammarTransformIndicator_tau51_eq` (Pour n au moins 2, l'indicateur de la transformation 5-vers-1 est potentiel(p n mod 6) fois (1 - potentiel(p(n+1) mod 6)).); `grammarTransformIndicator_tau55_eq` (Pour n au moins 2, l'indicateur de la transformation 5-vers-5 est le produit potentiel(p n mod 6) fois potentiel(p(n+1) mod 6).) ; et 39 autres.

**`p_two`** (`Basic`) — Le troisième premier est p 2 = 5.  
Cette vérité est confirmée (CONFIRMÉE) et provoque la série de conséquences suivantes (35 théorèmes au total) : `prime_mod6_state` (Pour n >= 2, p n mod 6 vaut 1 ou 5 (états de la grammaire).); `p_three` (Le quatrième premier est p 3 = 7.); `TReal_zero_before_five` (Pour tout réel x < 5, TReal x = 0.); `T_increment_not_grammar_function` (Il existe n1, n2 >= 2 de mêmes états mod 6 (p, p suivant) et même classe de gap mais d'incréments Tmode différents.); `round8_examples_have_distinct_scale` (log (p 2) est différent de log (p 4), soit log 5 différent de log 11.); `round8_obstruction_does_not_apply_to_full_meta_state` (p 2 et p 4 ont même résidu mod 6 mais log (p 2) différent de log (p 4).); `grammarWeight_two_zero` (doc. : (F1) Valeur explicite du poids en `(n, k) = (2, 0)`, calculée à partir des vrais premiers `p 2 = 5`, `p 3 = 7`.); `certification_prime_block_values` (sans docstring); `certification_prime_block_gaps` (sans docstring); `certification_prime_block_families` (sans docstring) ; et 25 autres.

**`reflectConjZero_im`** (`Round26B4ConstellationReflectionInvolution`) — La partie imaginaire du réfléchi-conjugué d'un zéro non trivial ρ est celle de ρ.  
Cette vérité est confirmée (CONFIRMÉE) et provoque la série de conséquences suivantes (31 théorèmes au total) : `ScientificRebuild20260901.functionalMirror_gamma` (La hauteur (Gamma) du miroir fonctionnel d'un zéro non trivial égale celle du zéro.); `reflectConjZero_zeroHeight` (La hauteur du réfléchi-conjugué d'un zéro non trivial égale la hauteur de ce zéro.); `reflectConjZero_mem_heightConstellation` (Le réfléchi-conjugué d'un zéro non trivial appartient à la constellation de hauteur T si et seulement si le zéro y appartient.); `offline_positive_zero_yields_rightHalf` (doc. : Every positive-height off-line non-trivial zero has a representative in the strict right-half rectangle: itself if it is on the right, its refl); `reflectConjZero_im_of_bridge` (doc. : Le zéro réfléchi a exactement la même hauteur.); `grammarTowerZeroFidelityObjectMinusFidelity_holds` (doc. : Les 32 surfaces non terminales sont INCONDITIONNELLEMENT vraies.); `carrier_sameHeightSurface` (doc. : Champ 4 `sameHeightSurface`, dérivé : les deux points de base du carrier sont à la même hauteur.); `core_commonHeightPhaseSurface` (doc. : Champ 23 `commonHeightPhaseSurface`, exposé : la phase de hauteur est la MÊME aux deux points de base du core, elle est non nulle, et elle reli); `height_only_is_blind_to_reflection` (doc. : HEIGHT_ONLY_BLIND_TO_REFLECTION = true.); `height_list_is_blind_to_memberwise_reflection` (doc. : OLD_TRIPLET_GRAMMAR_BLIND = true.) ; et 21 autres.

**`reflectConjZero_re`** (`Round26B4ConstellationReflectionInvolution`) — La partie réelle du réfléchi-conjugué d'un zéro non trivial ρ vaut 1 - Re ρ.  
Cette vérité est confirmée (CONFIRMÉE) et provoque la série de conséquences suivantes (30 théorèmes au total) : `ScientificRebuild20260901.functionalMirror_beta` (La partie réelle (Beta) du miroir fonctionnel d'un zéro non trivial vaut 1 moins celle du zéro.); `two_scale_ratio_relation_reflection_blind` (La relation d'égalité du rapport réfléchi à deux échelles a même valeur de vérité pour ρ et pour reflectConjZero ρ.); `norm_right_mode_le` (Pour U ≥ 0 et Re ρ > 1/2, la norme du mode du miroir reflectConjZero ρ est bornée par la norme de son amplitude.); `norm_reflectedResidueDifference_sq` (Pour x > 0 et un zéro non trivial ρ, le carré de la norme de la différence résiduelle réfléchie vaut le profil de norme carrée réfléchi (somme de deux); `reflectConjZero_ne_conj` (Pour un zéro hors ligne, son réfléchi (1 − conjugué) n'est pas le conjugué de ρ.); `reflect_signed_distance` (La distance signée du réfléchi de ρ à la droite critique est l'opposée de celle de ρ (Re' − 1/2 = −(Re − 1/2)).); `offline_mirror_invariant` (Le réfléchi de ρ est hors ligne si et seulement si ρ l'est.); `offLineMembers_reflect_mem` (L'involution de réflexion-conjugaison stabilise l'ensemble des membres hors ligne de la constellation.); `offline_positive_zero_yields_rightHalf` (doc. : Every positive-height off-line non-trivial zero has a representative in the strict right-half rectangle: itself if it is on the right, its refl); `rest_decomposition_permits_two_radii` (sans docstring) ; et 20 autres.

**`p_four`** (`Basic`) — Le cinquième premier est p 4 = 11.  
Cette vérité est confirmée (CONFIRMÉE) et provoque la série de conséquences suivantes (28 théorèmes au total) : `p_five` (Le sixième premier est p 5 = 13.); `T_increment_not_grammar_function` (Il existe n1, n2 >= 2 de mêmes états mod 6 (p, p suivant) et même classe de gap mais d'incréments Tmode différents.); `round8_examples_have_distinct_scale` (log (p 2) est différent de log (p 4), soit log 5 différent de log 11.); `round8_obstruction_does_not_apply_to_full_meta_state` (p 2 et p 4 ont même résidu mod 6 mais log (p 2) différent de log (p 4).); `grammarWeight_two_one` (doc. : (F2) Valeur explicite du poids en `(n, k) = (2, 1)`, calculée à partir des vrais premiers `p 3 = 7`, `p 4 = 11`.); `certification_prime_block_values` (sans docstring); `certification_prime_block_gaps` (sans docstring); `certification_prime_block_families` (sans docstring); `certification_change_indicator_block` (sans docstring); `certification_adjacent_sign_block` (sans docstring) ; et 18 autres.

**`reflectConjZero_eq_self_iff`** (`Round26B4ConstellationReflectionInvolution`) — Un zéro non trivial est fixe par la réflexion-conjugaison si et seulement si sa partie réelle vaut 1/2.  
Cette vérité est confirmée (CONFIRMÉE) et provoque la série de conséquences suivantes (26 théorèmes au total) : `reflectedPairRatio_eq_one_of_critical_line` (Si Re ρ = 1/2, le rapport réfléchi vaut 1 à toute échelle x > 0.); `reflectedPair_single_scale_character_eq_forces_reflect_fixed` (Si les caractères d'échelle de ρ et de son miroir coïncident à une échelle x > 0, x ≠ 1, alors reflectConjZero ρ = ρ.); `singlePrimeScaleCharacterCoincidence_of_riemannHypothesis` (RiemannHypothesis entraîne le verrou SinglePrimeScaleCharacterCoincidence (caractères d'échelle de ρ et de son miroir coïncidents à l'échelle p 0 = 2)); `reflectedChangeFamilyCompatibility_of_RH` (RH implique ReflectedChangeFamilyCompatibility.); `onLineMembers_eq_fixedPoints` (Les membres sur la ligne critique de la constellation sont exactement les membres de la constellation fixes par l'involution de réflexion-conjugaison.); `reflectConjZero_ne_self_iff` (Un zéro non trivial n'est pas fixe par la réflexion-conjugaison si et seulement si sa partie réelle est différente de 1/2.); `heightConstellation_reflection_trivial_iff_critical_line` (Tous les membres de la constellation T sont fixes par la réflexion-conjugaison si et seulement si tous sont de partie réelle 1/2.); `critical_line_gives_reflectedPairRatioScaleInvariant` (doc. : §3.c — ARÊTE TERMINALE, réciproque.); `reflectedPairRatioScaleInvariant_iff_critical_line` (doc. : §3.d — ÉQUIVALENCE TERMINALE COMPILÉE, SANS PERTE.); `criticalLine_orbit_no_internal_defect` (doc. : Aucun défaut interne sur une orbite fixée par l'involution.) ; et 16 autres.

**`p_three`** (`Basic`) — Le quatrième premier est p 3 = 7.  
Cette vérité est confirmée (CONFIRMÉE) et provoque la série de conséquences suivantes (24 théorèmes au total) : `p_four` (Le cinquième premier est p 4 = 11.); `T_increment_not_grammar_function` (Il existe n1, n2 >= 2 de mêmes états mod 6 (p, p suivant) et même classe de gap mais d'incréments Tmode différents.); `grammarWeight_two_zero` (doc. : (F1) Valeur explicite du poids en `(n, k) = (2, 0)`, calculée à partir des vrais premiers `p 2 = 5`, `p 3 = 7`.); `grammarWeight_two_one` (doc. : (F2) Valeur explicite du poids en `(n, k) = (2, 1)`, calculée à partir des vrais premiers `p 3 = 7`, `p 4 = 11`.); `certification_prime_block_values` (sans docstring); `certification_prime_block_gaps` (sans docstring); `certification_prime_block_families` (sans docstring); `certification_change_indicator_block` (sans docstring); `certification_adjacent_sign_block` (sans docstring); `certification_numeric_real_prime_block_V` (sans docstring) ; et 14 autres.

**`two_le_p`** (`Basic`) — Pour tout n, 2 <= p n.  
Cette vérité est confirmée (CONFIRMÉE) et provoque la série de conséquences suivantes (23 théorèmes au total) : `prime_point_propagation` (La propagation points-premiers est un théorème : la borne racine(x) log carré sur θ(x) moins x aux arguments premiers l'implique partout, avec constan); `normalized_T_increment_identity` (Pour n >= 1, Tmode (n+1) moins Tmode n = log p n fois (g n / log p n moins 1).); `critical_line_of_singlePrimeScaleCharacterCoincidence` (Le verrou SinglePrimeScaleCharacterCoincidence entraîne que tout zéro non trivial vérifie Re = 1/2.); `one_lt_prime_cast` (Tout premier canonique p_j vu dans ℝ est strictement supérieur à 1.); `grammarSectorPrimeDirichlet_summable_re_gt_one` (Pour Re s > 1, la série n -> indicateur * log(p n) * p n ^ (-s) est sommable, pour chaque transformation.); `zeroPrimeStepContribution_conjugateMate` (doc. : (C1) La contribution individuelle de colonne se conjugue exactement sous `conjugateMate`.); `chebyshev_theta_at_prime_eq_left_add_right_add_rest` (doc. : `REFLECTED_PAIR_PROPAGATED_TO_PRIME_EVALUATIONS`.); `reflectedPair_primitive_difference_unbounded` (doc. : §5.a — La différence des deux membres est non bornée au niveau des primitives.); `reflectedPair_psi_separated` (doc. : §5.b — `LEFT ≠ RIGHT` au niveau `psi`, DERNIER niveau complexe étiqueté.); `log_p_monotone` (doc. : `Real.log (p ·)` is monotone: uses `p_strictMono.monotone` for `p m ≤ p n` and `two_le_p` for positivity of `p m`.) ; et 13 autres.

**`windowBreak_ge`** (`Round26ACorrectedBridge`) — Tout point de rupture de fenêtre est au moins e^U.  
Cette vérité est confirmée (CONFIRMÉE) et provoque la série de conséquences suivantes (21 théorèmes au total) : `windowPiece_energy_le` (Sur chaque morceau de fenêtre, l'énergie de θ est au plus gramWindowWeight·(2 correctedTAtPrime(i+1)² + 4 aT(i+1)² + 4(U+log 2)²)/e^{2U}.); `thetaScaleFourMellinLinearSignal_eq_double_partition_sum` (sans docstring); `dynamicPairKernelClosedForm_le_inv_windowBreak` (doc. : H1.1 (first half): the closed-form kernel never exceeds the reciprocal of the outer window breakpoint — the clamp term contributes a nonnegativ); `dynamicPairKernelClosedForm_le_exp_neg` (doc. : H1.1 (second half): uniform bound `K_U(m,n) ≤ e^{-U}` — the master-doc's stated trivial horizon rate for the isolated kernel, obtained exactly ); `dynamicPairKernelClosedForm_pos_iff_lt_clamp` (doc. : H1.4: exact positivity characterization of the closed-form kernel (both directions; the forward direction restates the already-compiled `invers); `dynamicPairKernelClosedForm_eq_zero_of_r_zero` (doc. : H1.6: exact endpoint collapse at the lower prime index `r = 0`, using `p 1 = 3` (`p_one`) and `U ≥ log 12`.); `windowBreak_strictly_below_windowBreak_quadruple_shift` (sans docstring); `dynamicPairKernelClosedForm_eq_integral` (doc. : Kernel-as-integral: `dynamicPairKernelClosedForm` is exactly the integral, over the canonical scale-four window `[e^U, 2e^U]`, of the product o); `dynamicPairKernelIntegrand_intervalIntegrable` (doc. : Base integrability brick for G5: the pointwise integrand of the kernel-as-integral identity is `IntervalIntegrable` on the canonical window, fo); `blockCellLeft_pos` (doc. : `blockCellLeft` is always strictly positive: it dominates `dynamicFibreLeft U i ≥ exp U > 0`.) ; et 11 autres.

**`reflectConjZero_ne_self_iff`** (`Round26B4ConstellationReflectionInvolution`) — Un zéro non trivial n'est pas fixe par la réflexion-conjugaison si et seulement si sa partie réelle est différente de 1/2.  
Cette vérité est confirmée (CONFIRMÉE) et provoque la série de conséquences suivantes (21 théorèmes au total) : `alignedOfflinePrimeJunction_exists` (Pour un représentant positif hors ligne ρ à la hauteur T, il existe un témoin de jonction alignée AlignedOfflinePrimeJunction T ρ.); `AlignedOfflinePrimeJunction.two_prime_scale_character_faithfulness_separates_reflected_pair` (Sous un témoin hors ligne, les caractères d'échelle de ρ et de son miroir ne coïncident pas simultanément aux échelles log p m et log p n distincts.); `offline_member_realises_zero_gap` (Un membre hors ligne de la constellation de hauteur T a son réfléchi dans la même constellation, distinct de lui, avec un écart de hauteur exactement ); `offLineMembers_reflect_ne` (L'involution de réflexion-conjugaison n'a aucun point fixe parmi les membres hors ligne de la constellation.); `card_image_zeroHeight_lt_of_offline_member` (Si un ensemble fini S est stable par réflexion-conjugaison et contient un zéro hors ligne critique, le nombre de hauteurs distinctes est strictement i); `not_injOn_heightConstellation_of_heightDetermined_of_off_critical_line` (doc. : La même contrainte sur la véritable constellation de hauteur `heightConstellation T`, obtenue directement à partir de la réflexion-conjugaison ); `injOn_placement_separates_reflected_pair` (doc. : La forme positive de la contrainte.); `offline_reflected_pair_scale_characters_differ` (doc. : Caractères d'échelle distincts.); `offline_reflected_pair_orderKeys_differ` (doc. : Identités ordonnées distinctes.); `offline_member_gives_labelled_table_entry_defect` (doc. : §1.a — Différence d'entrées dans la table étiquetée.) ; et 11 autres.

## 4. Points ouverts touchés et tensions éclairées

Aucune ligne du lot n'a été rattachée par le relecteur à un Oi ou Ti ; les rapprochements ci-dessous sont faits par le rédacteur à partir des statuts, sans résolution.
- O5 / O10 / O21 (prémisses et caractérisations ⟺ RH) : le lot compte 14 théorèmes ÉQUIVALENTE À RH (verrous de récurrence, compatibilité réfléchie, exclusions hors ligne, hauteurs/cardinal) ; chacun est une caractérisation, aucun ne décharge la prémisse.
- O17 / O18 (relation de taille zéro ↔ premier ; amplitude `q^β/‖ρ‖`) : les théorèmes V102 du lot (`zeroMode_norm`, `norm_nontrivialZeroResidueTerm_eq_amplitude_rpow`, no-go conditionnels `exact_metapattern_excludes_exponential_scale_growth`) portent sur l'amplitude du mode d'un zéro ; les no-go restent conditionnels (non-annulation du reste non déchargée).
- O13 / O12 (hiérarchie historique, mod 6) : les 83 lignes V174 et 18 lignes V175 du lot confirment la couche mod 6 / méta-pattern dans cette base historique, hors RHV6Fresh.
- T4 (conclusion RH vs statut) : les théorèmes `riemannHypothesis_of_*` du lot ont tous une prémisse non déchargée, dont plusieurs sont elles-mêmes ⟺ RH (circularité signalée en remarque).
- T9 / O9 (somme vs terme isolé) : lignes V124 et V127 du lot (formule explicite, un terme par zéro) — voir table V.

## 5. Incidents

- **sorryAx** : 0. **Axiomes hors standard** : 3 théorèmes du lot (`master_has_exactly_99_constraints`, `master_99_constraints_nodup`, `master_has_exactly_99_evidence_rows`, module `MasterLeanE58TotalTripleRoute`) reposent sur `native_decide` (axiomes `RhGap.ScientificRebuild20260828.*._native.native_decide.ax_1_1`) ; ils sont marqués HORS STANDARD dans les tables. Les 4 autres théorèmes hors standard de la base (`ConstraintRegistry99`, `ConstraintPreludeCoverage99`) sont dans d'autres lots.
- **Terme `RiemannHypothesis` fermé** : aucun ; les 8 théorèmes littéralement `RiemannHypothesis` du lot ont une prémisse (verrou) ou sont des équivalences.
- **Noms dupliqués** : 12 noms de la base existent dans deux modules (dont 11 avec `Round26B4AdjacentBlockKernelPrototype`/`Round26B4PromotedPrototypeLemmas`) ; les comptes « entraîne » de ces lignes agrègent les deux homonymes (marqué dans les tables).
- **Types tronqués à 700 caractères** dans les entrées données aux relecteurs : glosses fondées sur la docstring ou le début du type là où la remarque le dit.
- **Remarques des relecteurs** (docstring ≠ type, nom promet plus que le type, autres) :

  - `SemanticTransportClosure20260821.trustedR12Partition` (Audit.TrustedNativeBridge) : le type est un énoncé nommé opaque à ce niveau ; sens lu dans le nom, non dans le type
  - `SemanticTransportClosure20260821.trustedC8Barycentric` (Audit.TrustedNativeBridge) : le type est un énoncé nommé opaque à ce niveau ; sens lu dans le nom, non dans le type
  - `enumeration_bookkeeping` (Basic) : type opaque EnumerationBookkeeping, sens lu dans la docstring (non contredite)
  - `theoremB` (Basic) : RH est ici RhGap.RH (prédicat du projet), sous trois hypothèses classiques
  - `gap_criterion` (Basic) : RH est ici RhGap.RH, sous deux hypothèses classiques
  - `prime_point_propagation` (Basic) : type opaque PrimePointPropagation, sens lu dans la docstring
  - `gap_criterion_vonKoch_only` (Basic) : RH est ici RhGap.RH
  - `gnat_zero` (Basic) : le nom et la docstring promettent l'unicité du gap impair, le type ne donne que gnat 0 = 1
  - `mode_criterion_vonKoch_only` (Basic) : RH est ici RhGap.RH
  - `class_projection_complete` (Basic) : correspondance partielle : RHV6Fresh donne les trois équivalences séparément (gapClass6_eq_zero_iff, _two_iff, _four_iff)
  - `pattern_family_closure` (Basic) : le nom parle de familles de patterns, le type ne parle que de la classe mod 6 du gap
  - `functional_symmetry_forces_half` (Basic) : énoncé sur un ensemble abstrait Z, pas sur les zéros de zêta ; RH n'y apparaît que par instanciation
  - `theoremF_RH_from_T_spectral_rigidity` (Basic) : énoncé sur un ensemble abstrait Z
  - `TReal_equals_Tmode_at_prime` (Basic) : idem instance de TReal_at_prime (même type)
  - `T_increment_not_mod6_projection_function` (Basic) : identique par le type à T_increment_not_grammar_function (renommage de portée)
  - `round8_obstruction_does_not_apply_to_full_meta_state` (Basic) : le nom promet que l'obstruction ne s'applique pas à l'état complet ; le type ne dit que : même résidu, logarithmes distincts
  - `ordered_meta_state_injective` (Basic) : le nom parle d'état méta-pattern ordonné, le type est l'injectivité de p
  - `zero_scale_eigenvalue_abs` (Basic) : instanciation partielle de V102 : la norme dépend de Re rho seule
  - `functional_symmetry_forces_exact_half` (Basic) : doublon par le type de functional_symmetry_forces_half ; énoncé sur un ensemble abstrait Z
  - `RH_from_density_order_scale_rigidity` (Basic) : énoncé sur un ensemble abstrait Z
  - `energy_transfer_integral` (Basic) : la docstring ajoute 0<a<b, absent du type
  - `translated_scale_invariance_closes_RH17` (CanonicalRestrictionFinal) : doublon par le type de RH_from_density_order_scale_rigidity ; le nom promet une clôture de RH, le type est conditionnel sur un ensemble abstrait Z
  - `chebyshevθ_eq_zerosPrimeCountReal_abel_raw` (ChebyshevThetaAbelBridge) : la comptabilité via zerosPrimeCountReal est lue dans le nom et la docstring
  - `FullRigidCoupledZeroPrimeGrammar.mk.congr_simp` (CoupledRigidGrammar) : lemme technique sans contenu sémantique propre ; type tronqué (29 hypothèses), sens lu dans le nom
  - `RigidCoupledZeroPrimeGrammar.mk.congr_simp` (CoupledRigidGrammar) : lemme technique sans contenu sémantique propre ; type tronqué (26 hypothèses), sens lu dans le nom
  - `CoupledRigidGrammar.MZ_eq_M` (CoupledRigidGrammar) : même type que CoupledRigidGrammar.reconstructed_block_eq_prime
  - `CoupledRigidGrammar.zero_source_encoding_eq_MZ` (CoupledRigidGrammar) : même type que zero_source_encoding_eq_reconstructed_block
  - `CoupledRigidGrammar.primes_determine_zero_source` (CoupledRigidGrammar) : même type que prime_history_determines_zero_source
  - `InverseSignatureConcrete.weak_grammar_signature_holds_regardless_of_real_part` (InverseSignatureConcrete) : contre-modèle : la signature faible ne force pas la centralité
  - `ScientificRebuild20260901.ZeroPassage.ordered` (MasterLeanE58TotalTripleRoute) : champ de structure ZeroPassage
  - `ScientificRebuild20260901.ThreeZeroWindow.order01` (MasterLeanE58TotalTripleRoute) : champ de structure
  - `ScientificRebuild20260901.ThreeZeroWindow.order12` (MasterLeanE58TotalTripleRoute) : champ de structure
  - `ScientificRebuild20260901.TrueMemberContactCell.stage_pos` (MasterLeanE58TotalTripleRoute) : champ de structure
  - `ScientificRebuild20260901.offMirror_leftContact_ne` (MasterLeanE58TotalTripleRoute) : RHV6Fresh énonce la version β<1/2 sur contactMinusAt
  - `ScientificRebuild20260901.master_has_exactly_99_constraints` (MasterLeanE58TotalTripleRoute) : décompte de la liste du dépôt, aucun énoncé mathématique
  - `ScientificRebuild20260901.master_has_exactly_99_constraints` (MasterLeanE58TotalTripleRoute) : HORS STANDARD (RhGap.ScientificRebuild20260828.allConstraints_length._native.native_decide.ax_1_1)
  - `ScientificRebuild20260901.master_99_constraints_nodup` (MasterLeanE58TotalTripleRoute) : décompte de la liste du dépôt, aucun énoncé mathématique
  - `ScientificRebuild20260901.master_99_constraints_nodup` (MasterLeanE58TotalTripleRoute) : HORS STANDARD (RhGap.ScientificRebuild20260828.allConstraints_nodup._native.native_decide.ax_1_1)
  - `ScientificRebuild20260901.master_has_exactly_99_evidence_rows` (MasterLeanE58TotalTripleRoute) : décompte de la liste du dépôt, aucun énoncé mathématique
  - `ScientificRebuild20260901.master_has_exactly_99_evidence_rows` (MasterLeanE58TotalTripleRoute) : HORS STANDARD (RhGap.ScientificRebuild20260828.constraintEvidenceCoverage_length._native.native_decide.ax_1_1)
  - `theoremG_RH_from_mellin_rigidity` (Mellin) : le nom promet plus que le type : le type porte sur un ensemble Z quelconque, non sur RiemannHypothesis
  - `no_offline_of_heightDetermined_primePlacement_leftInverse` (MemberwiseHeightInverseContradiction) : aucun placement concret n'est construit (docstring) ; la conclusion est conditionnelle
  - `round23_global_prime_positions_corollary` (OfflineZeroIncompatibility) : docstring : corollaire global indépendant de ρ ; le nom historique 'offline' a été retiré
  - `round23_global_prime_gaps_corollary` (OfflineZeroIncompatibility) : docstring : corollaire global indépendant de ρ
  - `round22_global_total_mode_partition_corollary` (OfflineZeroIncompatibility) : docstring : corollaire global indépendant de ρ
  - `exact_metapattern_excludes_exponential_scale_growth` (OfflineZeroIncompatibility) : conditionnel : la non-annulation du reste n'est pas déchargée
  - `offline_zero_incompatible_with_exact_prime_gap_metapattern_conditional` (OfflineZeroIncompatibility) : le nom promet plus que le type : la version inconditionnelle est explicitement non prouvée (docstring)
  - `smoothedFormulaProjectedChannel_eq_inv_add_one_mul_P5_via_zeroMode` (OfflineZeroIncompatibility) : idem, preuve indépendante
  - `activeOfflineOrbitMobiusTerm.congr_simp` (OfflineZeroOrbitDecomposition) : lemme de congruence auto-généré
  - `offlineOrbitPrimitivePart.congr_simp` (OfflineZeroOrbitDecomposition) : lemme de congruence auto-généré
  - `offlineOrbitPsiRecovered.congr_simp` (OfflineZeroOrbitDecomposition) : lemme de congruence auto-généré
  - `offlineRestPsiRecovered.congr_simp` (OfflineZeroOrbitDecomposition) : lemme de congruence auto-généré
  - `offline_zero_channel_decomposition` (OfflineZeroOrbitDecomposition) : définitionnel
  - `offline_zero_channel_decomposition_instantiates_hdecomp` (OfflineZeroOrbitDecomposition) : idem, énoncé identique au précédent
  - `offline_zero_channel_incompatible_conditional` (OfflineZeroOrbitDecomposition) : conditionnel : sous-exponentialité et non-annulation non déchargées
  - `Int.fract_abs_le_one` (P4Port.Algebra.Order.Floor.Ring) : port Mathlib-like
  - `Polynomial.logDeriv_exp_eval` (P4Port.Analysis.Calculus.Deriv.Polynomial) : port Mathlib-like
  - `Polynomial.degree_derivative_le_zero_of_degree_le_one` (P4Port.Analysis.Calculus.Deriv.Polynomial) : port Mathlib-like
  - `Polynomial.eval_derivative_eq_eval_derivative_zero_of_degree_le_one` (P4Port.Analysis.Calculus.Deriv.Polynomial) : port Mathlib-like
  - `Complex.norm_le_of_mem_ball_of_forall_sphere_norm_le` (P4Port.Analysis.Complex.AbsMax) : port Mathlib-like
  - `Complex.div_sub_one_eq_one_add_one_div` (P4Port.Analysis.Complex.Basic) : port Mathlib-like
  - `Complex.exists_norm_bound_on_closedBall` (P4Port.Analysis.Complex.Basic) : port Mathlib-like
  - `Complex.exists_pos_radius_forall_mem_ball_re_ge` (P4Port.Analysis.Complex.Basic) : port Mathlib-like
  - `Complex.borelCaratheodory_zero_closedBall` (P4Port.Analysis.Complex.BorelCaratheodory) : port Mathlib-like
  - `Complex.canonicalProduct_def` (P4Port.Analysis.Complex.CanonicalProduct) : équation de définition
  - `Complex.hasProdLocallyUniformlyOn_canonicalProduct` (P4Port.Analysis.Complex.CanonicalProduct) : port Mathlib-like
  - `Complex.multipliableLocallyUniformlyOn_canonicalProduct` (P4Port.Analysis.Complex.CanonicalProduct) : port Mathlib-like
  - `Complex.hasProdUniformlyOn_canonicalProduct_compact` (P4Port.Analysis.Complex.CanonicalProduct) : port Mathlib-like
  - `Complex.canonicalProduct_converges_uniformOn_compact` (P4Port.Analysis.Complex.CanonicalProduct) : port Mathlib-like
  - `Complex.differentiable_canonicalProduct` (P4Port.Analysis.Complex.CanonicalProduct) : port Mathlib-like
  - `Complex.analyticOnNhd_canonicalProduct` (P4Port.Analysis.Complex.CanonicalProduct) : port Mathlib-like
  - `Complex.logDeriv_weierstrassFactor_one_div` (P4Port.Analysis.Complex.CanonicalProduct) : port Mathlib-like
  - `Complex.canonicalProduct_apply_eq_zero` (P4Port.Analysis.Complex.CanonicalProduct) : port Mathlib-like
  - `Complex.canonicalProduct_eq_zero_of_mem_range` (P4Port.Analysis.Complex.CanonicalProduct) : port Mathlib-like
  - `Complex.canonicalProduct_ne_zero` (P4Port.Analysis.Complex.CanonicalProduct) : port Mathlib-like
  - `Complex.differentiableOn_canonicalPartialProduct` (P4Port.Analysis.Complex.CanonicalProduct) : port Mathlib-like
  - `_private.RhGapCriterion.P4Port.Analysis.Complex.CanonicalProduct.0.Complex.tendsto_deriv_canonicalPartialProduct` (P4Port.Analysis.Complex.CanonicalProduct) : lemme privé
  - `Complex.canonicalProduct_eq_zero_iff` (P4Port.Analysis.Complex.CanonicalProduct) : port Mathlib-like
  - `Complex.canonicalProduct_ne_zero_iff` (P4Port.Analysis.Complex.CanonicalProduct) : port Mathlib-like
  - `Complex.logDeriv_canonicalProduct_one_eq_tsum` (P4Port.Analysis.Complex.CanonicalProduct) : port Mathlib-like
  - `Complex.Gamma.norm_bound_re_ge_one` (P4Port.Analysis.SpecialFunctions.Gamma.StripBounds) : docstring ≠ type (la docstring dit polynomiale en ‖s‖, l'exposant du type dépend de ‖s‖)
  - `Real.log_norm_le_log_one_add_norm` (P4Port.Analysis.SpecialFunctions.Log.ExpGrowth) : docstring ≠ type (la docstring restreint à une norme non nulle, le type n'a aucune hypothèse)
  - `Kadiri.neg_zeta_logDeriv_eq_of_genusOne_hadamard` (P4Port.IEANTN.HadamardLogDerivative) : la famille de zéros est un paramètre libre, non liée aux zéros non triviaux dans le type
  - `Kadiri.neg_zeta_logDeriv_eq_of_centered_orbit_hadamard` (P4Port.IEANTN.HadamardLogDerivative) : la famille d'orbites est un paramètre libre
  - `_private.RhGapCriterion.P4Port.IEANTN.HadamardLogDerivative.0.Kadiri.zetaGammaFactor_shift_avoid_of_not_zero` (P4Port.IEANTN.HadamardLogDerivative) : le type ne demande pas s ≠ 1 : lecture via l'ensemble zeroes
  - `Kadiri.riemannZetaConjZeroSource_of_riemannZeta_conj` (P4Port.IEANTN.KadiriZeroCounting) : le type est la définition dépliée d'une Source Prop ; RHV6Fresh donne la version avec ordre, non seulement l'annulation
  - `Kadiri.zeroes_rect_Ioo_critical_positive_height_finite` (P4Port.IEANTN.KadiriZeroCounting) : correspondance de même vérité (finitude d'une fenêtre de hauteur) mais fenêtres et prédicat de zéro non triviaux différents
  - `Kadiri.zeroes_rect_univ_positive_height_finite` (P4Port.IEANTN.KadiriZeroCounting) : même vérité de finitude ; RHV6Fresh est énoncé pour les zéros non triviaux sur ]T1,T2]
  - `Kadiri.zeroImagDyadicNOrderSummableSource_of_positive_height_zero_free` (P4Port.IEANTN.KadiriZeroCounting) : le type affiché est la définition dépliée de la Source ; le nom promet une condition, le type est inconditionnel
  - `Kadiri.zeroHeightNontrivialZeros_finite` (P4Port.IEANTN.KadiriZeroCounting) : finitude seulement, non vacuité ; hors énoncé du maître (V7 exige Im>0)
  - `Kadiri.zeroImagDyadicAbsToPositiveCountWithZeroHeightSource_of_riemannZeta_conj` (P4Port.IEANTN.KadiriZeroCounting) : le type est la Source dépliée ; usage de la conjugaison rapproche de V64 seulement par l'énumération des hauteurs positives
  - `Kadiri.zeroImagSquareTailSummable_of_crude_majorant` (P4Port.IEANTN.KadiriZeroCounting) : le type est la Source dépliée
  - `_private.RhGapCriterion.P4Port.IEANTN.KadiriZeroCounting.0.Kadiri.analyticOrderAt_conj_conj` (P4Port.IEANTN.KadiriZeroCounting) : RHV6Fresh énonce sans l'hypothèse d'analyticité
  - `zero_density_bound.bound` (P4Port.IEANTN.ZetaDefinitions) : champ de structure, non un théorème sur zêta ; le nom promet plus que le type
  - `MeasureTheory.IntegrableOn.mono'` (P4Port.MeasureTheory.Integral.IntegrableOn) : port d'un lemme Mathlib
  - `intervalIntegral.integral_congr_Ioc_of_le` (P4Port.MeasureTheory.Integral.IntervalIntegral.Basic) : port d'un lemme Mathlib
  - `Nat.Primes.norm_cpow_neg_eq_rpow_neg_re` (P4Port.NumberTheory.LSeries.RiemannZeta) : cette identité de norme est l'analogue côté Euler de zeroTerm_norm (‖q^ρ/ρ‖ = q^β/‖ρ‖), non le même énoncé
  - `one_lt_zetaAbelContinuationReLower` (P4Port.NumberTheory.LSeries.RiemannZetaAbelContinuation) : le nom (one_lt) suggère 1 < seuil, le type dit seuil < 1
  - `norm_zeta_product_ge_one` (PerronPort.ZetaBounds) : docstring ≠ type : la docstring dit « y non nul » ; le type quantifie sur tout y réel
  - `zeroMemberTransition_exactly_four` (PrimeDeterminedZeroCompleteGrammar) : le nom « exactly four » promet plus que le type : l'unicité ∃! est triviale (la fonction est déterministe), et rien ne dit que les quatre valeurs sont toutes atteintes
  - `prime_determined_zero_grammar_bridge` (PrimeDeterminedZeroCompleteGrammar) : type tronqué à 700 car. : conjonction complète non relue dans la source
  - `prime_determined_first_five_is_an_instance` (PrimeDeterminedZeroRecovery) : type affiché tronqué (⋯ = ⋯), lu dans la docstring
  - `prime_determined_first_hundred_is_an_instance` (PrimeDeterminedZeroRecovery) : type affiché tronqué (⋯ = ⋯), lu dans la docstring
  - `no_zero_reconstructed_completeGrammar_memberwise_common_contact_for_true_offline` (PrimeGrammarMemberContactDecoderNoGo) : type tronqué à 700 caractères, formulation lue dans la docstring
  - `windowed_identity_exact` (PrimeZeroIntertwining) : identité définitionnelle sans contenu analytique (la docstring le déclare)
  - `zeroMode_norm` (PrimeZeroIntertwining) : norme mode explicite du repère centré en 1/2, distincte de zeroTerm_norm (q^β/‖ρ‖) de RHV6Fresh
  - `RH_from_windowed_identity_and_remainder_bound` (PrimeZeroIntertwining) : conclusion sur l'ensemble Z (RH pour Z) ; chaîne conditionnelle, toutes hypothèses en paramètres
  - `round23_zero_prime_gap_reconstruction` (Round23TerminalClosure) : conjonction de résultats (la dernière partie est conditionnelle en interne à F déterminée par les premiers)
  - `weightedP5OrbitProjectionEnergy_eq_exp_growth` (Round25G2CEnergyBridge) : croissance exponentielle en (Re ρ − 1/2), lecture dans le repère du corpus historique
  - `zero_reconstructed_transformation_conditioned_increment_decomposition` (Round25G2CGrammarBridge) : décomposition mod 6, indexée sur la couche de grammaire, transportée aux zéros
  - `normalizedRChebyshevCorrectionEnergy_le` (Round25G2CNormalizedWindowEnergy) : version moins générale du théorème précédent (même borne, hypothèse U ≥ log 2 superflue)
  - `terminal_theta_mellin_energy_identified` (Round25M50TerminalMellinEnergy) : le nom promet plus que le type (identification de l'énergie de Mellin θ à l'énergie terminale M.49) ; la docstring le déclare
  - `theta_energy_subexponential_implies_psi_energy_subexponential` (Round25M50TerminalMellinEnergy) : implication sur la sous-exponentialité (non RH)
  - `psi_mellin_subexponential_excludes_right_nontrivial_zeros` (Round25M53MellinZetaIdentity) : conclusion Re ρ ≤ 1/2 et non Re ρ = 1/2 ; la prémisse n'est pas établie inconditionnellement
  - `theta_mellin_subexponential_excludes_right_nontrivial_zeros` (Round25M53MellinZetaIdentity) : conclusion Re ρ ≤ 1/2 et non Re ρ = 1/2
  - `R_and_aT_window_subexponential_implies_theta_mellin` (Round26ACorrectedBridge) : implication de sous-exponentialité, non RH
  - `thetaErrorReal_measurable'` (Round26ADiscreteMellinBridge) : doublon d'un théorème du même module de Mellin (thetaErrorReal_measurable)
  - `zero_reconstructed_signed_correlation_eq` (Round26AGSignedCrossDecomposition) : le transport vers la réalisation zéro s'appuie sur M^Z = M ; la Vi n'est instanciée que par cette liaison zéros/premiers
  - `zero_reconstructed_diagonal_increment_mass_eq` (Round26AGSignedCrossDecomposition) : idem
  - `gram_weighted_R_sq_eq_zero_reconstructed_diagonal_add_signed_correlation` (Round26AGSignedCrossDecomposition) : idem
  - `reflectedPairRatio_scale_rpow` (Round26AKPrimeForcedRatioRecurrence) : l'exposant 1 - 2β est la différence des exposants d'amplitude q^(1-β) et q^β ; correspondance approximative seulement
  - `rpow_eq_rpow_of_ne_forces_exponent_zero` (Round26AKPrimeForcedRatioRecurrence) : lemme réel générique
  - `reflectedPairRatio_eq_at_distinct_positive_scales_iff_critical_line` (Round26AKPrimeForcedRatioRecurrence) : équivalence locale à un zéro (pas RH) ; RH n'en découle qu'après quantification sur les zéros
  - `primeScaleForcedRatioRecurrence_iff_primeForcedTwoScaleRatioRecurrence` (Round26AKPrimeForcedRatioRecurrence) : équivalence entre deux prémisses chacune établie ↔ RH par primeForcedTwoScaleRatioRecurrence_iff_riemannHypothesis et primeScaleForcedRatioRecurrence_iff_riemannHypothesis
  - `primeForcedTwoScaleRatioRecurrence_of_scale_four_subexponential` (Round26AKPrimeForcedRatioRecurrence) : le verrou est équivalent à RH ; la conclusion est donc RH sous la prémisse quantitative
  - `primeScaleForcedRatioRecurrence_of_scale_four_subexponential` (Round26AKPrimeForcedRatioRecurrence) : idem
  - `norm_left_mode` (Round26ALSpineRestGrowthReduction) : vocabulaire différent (mode réétalonné exp((β-1/2)U) contre terme q^β/‖ρ‖) ; même mécanisme d'amplitude en exposant β
  - `no_offline_zero_of_channel_and_rest_subexponential` (Round26ALSpineRestGrowthReduction) : la prémisse ZeroSideChannelSubexponential est dite de force RH par la docstring du fichier
  - `generic_two_scales_do_not_separate_scale_characters` (Round26AMPrimeScaleCharacterFaithfulness) : contre-modèle (le nom énonce une existence, pas une négation universelle en syntaxe)
  - `zero_completeGrammarBlock_rigid` (Round26ANGrammarRigidityRestoration) : transport par M^Z = M
  - `GZ_transition_does_not_determine_internal_gap` (Round26ANGrammarRigidityRestoration) : contre-exemple existentiel
  - `GZ_internal_gap_does_not_determine_transition` (Round26ANGrammarRigidityRestoration) : contre-exemple existentiel
  - `RigidPrimeGrammarBlock.mk.congr_simp` (Round26AORigidCoupledGrammar) : lemme auto-généré de structure
  - `RigidPrimeGrammarBlock.canonical` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidPrimeGrammarBlock.rigid` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidCoupledZeroPrimeGrammar.prime_start_ge_two` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidCoupledZeroPrimeGrammar.source_encodes_prime` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidCoupledZeroPrimeGrammar.zeroRows_eq_canonical` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidCoupledZeroPrimeGrammar.zeroHeights_from_rows` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidCoupledZeroPrimeGrammar.zeroGaps_from_heights` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidCoupledZeroPrimeGrammar.zeroRows_ordered` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidCoupledZeroPrimeGrammar.internalGapWithNext_exact` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidCoupledZeroPrimeGrammar.primeGap_exact` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidCoupledZeroPrimeGrammar.primeTransition_exact` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidCoupledZeroPrimeGrammar.primePattern_exact` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidCoupledZeroPrimeGrammar.primeFamily_exact` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidCoupledZeroPrimeGrammar.tableEntry_exact` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidCoupledZeroPrimeGrammar.weightedEntry_exact` (Round26AORigidCoupledGrammar) : projection de structure
  - `RigidCoupledZeroPrimeGrammar.totalColumnBridge` (Round26AORigidCoupledGrammar) : projection de structure ; la somme porte sur tous les zéros, pas sur un terme isolé
  - `FullRigidCoupledZeroPrimeGrammar.transition_partition` (Round26APFullRigidCoupledGrammar) : projection de structure
  - `FullRigidCoupledZeroPrimeGrammar.family_change_skeleton_alternates` (Round26APFullRigidCoupledGrammar) : même alternance forcée, forme squelette avec intermédiaires nuls ; le type RHV6Fresh porte trois premiers consécutifs sans intermédiaires
  - `FullRigidCoupledZeroPrimeGrammar.block_occurrences_prime` (Round26APFullRigidCoupledGrammar) : projection de structure
  - `FullRigidCoupledZeroPrimeGrammar.rank_density_exact` (Round26APFullRigidCoupledGrammar) : projection de structure
  - `FullRigidCoupledZeroPrimeGrammar.theta_density_exact` (Round26APFullRigidCoupledGrammar) : projection de structure
  - `FullRigidCoupledZeroPrimeGrammar.transition_succession_exact` (Round26APFullRigidCoupledGrammar) : projection de structure
  - `FullRigidCoupledZeroPrimeGrammar.family_succession_exact` (Round26APFullRigidCoupledGrammar) : projection de structure
  - `FullRigidCoupledZeroPrimeGrammar.pattern_succession_exact` (Round26APFullRigidCoupledGrammar) : projection de structure ; pas de docstring
  - `FullRigidCoupledZeroPrimeGrammar.universal_position_gap_transport` (Round26APFullRigidCoupledGrammar) : aveuglement de la grammaire première à la source reconstruite
  - `FullRigidCoupledZeroPrimeGrammar.only_four_transitions` (Round26APFullRigidCoupledGrammar) : doublon de transition_partition (partie existence)
  - `FullRigidCoupledZeroPrimeGrammar.change_skeleton_alternates` (Round26APFullRigidCoupledGrammar) : doublon de family_change_skeleton_alternates ; même remarque de forme
  - `FullRigidCoupledZeroPrimeGrammar.has_finite_metapattern` (Round26APFullRigidCoupledGrammar) : doublon de meta_pattern_finite
  - `full_coupled_rigidity_exclusion_iff_offline_exclusion` (Round26AQTerminalRigidityClosure) : équivalence à une exclusion hors ligne quantifiée ; l'égalité formelle avec RiemannHypothesis n'est pas dans ce type
  - `relational_bundle_exclusion_iff_offline_exclusion` (Round26ARRelationalRigidityRecovery) : équivalence à l'exclusion hors ligne quantifiée sur T, ρ ; le type ne cite pas RiemannHypothesis
  - `auditedAlignedOfflineExclusion_iff_truncated_critical_line` (Round26ASTerminalJunctionBoundary) : équivalence locale à une hauteur T ; RH en quantifiant sur T
  - `ConstellationPrimePatternCrosswalkCell.mk.congr_simp` (Round26ASTerminalJunctionExhaustion) : lemme auto-généré de structure
  - `_private.RhGapCriterion.Round26ASTerminalJunctionExhaustion.0.reflectConjZero_mem_positiveRepresentatives` (Round26ASTerminalJunctionExhaustion) : lemme privé
  - `_private.RhGapCriterion.Round26ASTerminalJunctionExhaustion.0.mem_orderedPositiveRepresentatives_of_mem_positive` (Round26ASTerminalJunctionExhaustion) : lemme privé
  - `AlignedOfflinePrimeJunction.member` (Round26ASTerminalJunctionExhaustion) : projection de structure
  - `AlignedOfflinePrimeJunction.offline` (Round26ASTerminalJunctionExhaustion) : projection de structure
  - `AlignedOfflinePrimeJunction.primeIndex_ge_two` (Round26ASTerminalJunctionExhaustion) : projection de structure
  - `AlignedOfflinePrimeJunction.row_member` (Round26ASTerminalJunctionExhaustion) : projection de structure
  - `AlignedOfflinePrimeJunction.reflected_row_member` (Round26ASTerminalJunctionExhaustion) : projection de structure
  - `AlignedOfflinePrimeJunction.rows_distinct` (Round26ASTerminalJunctionExhaustion) : projection de structure
  - `AlignedOfflinePrimeJunction.defect` (Round26ASTerminalJunctionExhaustion) : projection de structure
  - `AlignedOfflinePrimeJunction.leftCell_member` (Round26ASTerminalJunctionExhaustion) : projection de structure
  - `AlignedOfflinePrimeJunction.rightCell_member` (Round26ASTerminalJunctionExhaustion) : projection de structure
  - `AlignedOfflinePrimeJunction.same_column_same_prime_labels_different_entries` (Round26ASTerminalJunctionExhaustion) : énoncé tronqué à 700 car. dans le lot, conjonction lue jusqu'à l'unicité de famille ; la fin suit la docstring (entrées différentes)
  - `AlignedOfflinePrimeJunction.active_MZ_eq_M` (Round26ASTerminalJunctionExhaustion) : M^Z = M
  - `AlignedOfflinePrimeJunction.active_zero_height_gap_and_prime_gap_coexist` (Round26ASTerminalJunctionExhaustion) : aucune égalité entre les deux champs n'est introduite
  - `AlignedOfflinePrimeJunction.zero_gap_position_and_prime_defect_column_coexist` (Round26ASTerminalJunctionExhaustion) : aucun théorème n'identifie i et la colonne
  - `AlignedOfflinePrimeJunction.active_total_column_bridge` (Round26ASTerminalJunctionExhaustion) : somme sur tous les zéros, jamais un terme isolé
  - `AlignedOfflinePrimeJunction.window_finite_metapattern` (Round26ASTerminalJunctionExhaustion) : type tronqué dans le lot ; méta-pattern fini comme dans FullRigidCoupledZeroPrimeGrammar.meta_pattern_finite
  - `AlignedOfflinePrimeJunction.window_ordered_successions_transport` (Round26ASTerminalJunctionExhaustion) : M^Z = M
  - `AlignedOfflinePrimeJunction.JunctionExhaustionCertificate.mz_eq_m` (Round26ASTerminalJunctionExhaustion) : M^Z = M
  - `_private.RhGapCriterion.Round26ATCompiledTerminalJunctionAudit.0.exists_prime_index_gt_with_residue` (Round26ATCompiledTerminalJunctionAudit) : Lemme privé, sans zéro
  - `defectColumnMeetsChangeFamily_is_not_the_exclusion` (Round26ATCompiledTerminalJunctionAudit) : le nom promet plus que le type : le type ne mentionne pas DefectColumnMeetsChangeFamily, il énonce seulement exclusion alignée ⟹ pas de zéro hors ligne à T
  - `critical_line_of_defectColumnMeetsChangeFamily_and_compatibility` (Round26AUReflectedDefectEventuality) : Prémisse compatibilité ⟺ RH (RhGap.reflectedChangeFamilyCompatibility_iff_RH, même lot) : implication circulaire
  - `riemannHypothesis_of_defectColumnMeetsChangeFamily_and_compatibility` (Round26AUReflectedDefectEventuality) : Circulaire : une des prémisses est ⟺ RH
  - `riemannHypothesis_of_reflectedDifferenceEventuallyStrict_and_compatibility` (Round26AUReflectedDefectEventuality) : Circulaire : la seconde prémisse est ⟺ RH
  - `nontrivialZeroResidueTerm_eq_coeff_mul_cpow` (Round26AVReflectedDifferenceClosedForm) : Proche du terme explicite du maître mais avec le noyau de Perron propre au corpus, pas identifié à zeroTerm
  - `_private.RhGapCriterion.Round26AVReflectedDifferenceClosedForm.0.rpow_sq` (Round26AVReflectedDifferenceClosedForm) : Lemme privé générique
  - `exists_strictMonoOn_rpow_pair_add_linear` (Round26AVReflectedDifferenceClosedForm) : Lemme d'analyse réelle sans zêta
  - `_private.RhGapCriterion.Round26AVReflectedDifferenceClosedForm.0.prime_scale_pos` (Round26AVReflectedDifferenceClosedForm) : Lemme privé
  - `reflectedDifferenceEventuallyStrictOnPrimes_proved` (Round26AVReflectedDifferenceClosedForm) : Docstring et nom : la définition du prédicat ne porte que sur les zéros hors ligne, donc vide sur la ligne
  - `EarlyMultiLevelDisturbance.primeIndex_ge_two` (Round26AWMultiLevelDisturbanceLadder) : Champ de structure
  - `EarlyMultiLevelDisturbance.changeFamily` (Round26AWMultiLevelDisturbanceLadder) : Champ de structure
  - `EarlyMultiLevelDisturbance.weight_ne_zero` (Round26AWMultiLevelDisturbanceLadder) : Champ de structure
  - `EarlyMultiLevelDisturbance.weightedStepDefect` (Round26AWMultiLevelDisturbanceLadder) : Champ de structure
  - `EarlyMultiLevelDisturbance.everyLabelledWindowDefect` (Round26AWMultiLevelDisturbanceLadder) : Champ de structure
  - `EarlyMultiLevelDisturbance.everyFamilyMaskedWindowDefect` (Round26AWMultiLevelDisturbanceLadder) : Champ de structure
  - `EarlyMultiLevelDisturbance.everyPatternMaskedWindowDefect` (Round26AWMultiLevelDisturbanceLadder) : Champ de structure
  - `EarlyMultiLevelDisturbance.familyOccursPrime` (Round26AWMultiLevelDisturbanceLadder) : Champ de structure
  - `EarlyMultiLevelDisturbance.familyOccursReconstructed` (Round26AWMultiLevelDisturbanceLadder) : Champ de structure
  - `EarlyMultiLevelDisturbance.patternOccursPrime` (Round26AWMultiLevelDisturbanceLadder) : Champ de structure
  - `EarlyMultiLevelDisturbance.patternOccursReconstructed` (Round26AWMultiLevelDisturbanceLadder) : Champ de structure
  - `ComplexPsiDisturbance.psiIndex_ge_two` (Round26AWMultiLevelDisturbanceLadder) : Champ de structure
  - `ComplexPsiDisturbance.leftRightSeparated` (Round26AWMultiLevelDisturbanceLadder) : Champ de structure
  - `ComplexPsiDisturbance.exactTotalDecomposition` (Round26AWMultiLevelDisturbanceLadder) : Champ de structure
  - `complexPsi_attack_survives_before_real_projection` (Round26AWMultiLevelDisturbanceLadder) : La seconde conjonction (non-injectivité de Re) est indépendante du zéro
  - `carrier_routes_require_row_specific_input` (Round26AXCarrierValueFreedom) : Le nom est une lecture interprétative ; le type ne dit que la liberté des valeurs
  - `zeroGapRigidity_iff_critical_line` (Round26AZZeroGapGrammarRigidity) : Équivalence locale à la hauteur T, pas RH
  - `all_zeroGapRigidity_iff_global_critical_line` (Round26AZZeroGapGrammarRigidity) : Le membre droit est RH sous forme explicite
  - `weighted_quadratic_energy_exponent_dictionary` (Round26B4AdjacentBlockKernelPrototype) : Ici β est un réel générique, pas la partie réelle d'un zéro
  - `exp_two_beta_sub_one_mul_eq_rpow` (Round26B4AdjacentBlockKernelPrototype) : Ici β est un réel générique
  - `R_eq_centered_add_boundary` (Round26B4AdjacentBlockKernelPrototype) : Trivial
  - `decoder_output_is_prime_side` (Round26B4CollectiveDecoderAbsorptionAudit) : Ré-export de psiRecoveredFromZeros_eq_psi (docstring)
  - `decoder_prime_gaps_are_canonical` (Round26B4CollectiveDecoderAbsorptionAudit) : Ré-export de zeros_prime_gaps_eq_prime_gaps (docstring)
  - `collective_block_projection_row_swap_invariant` (Round26B4ConstellationCollisionRigidity) : idem, instance bloc
  - `collective_grammarVoiceRow_row_swap_invariant` (Round26B4ConstellationCollisionRigidity) : idem, instance voix de grammaire
  - `_private.RhGapCriterion.Round26B4ConstellationCollisionRigidity.0.norm_nontrivialZeroResidueTerm_eq_amplitude_rpow` (Round26B4ConstellationCollisionRigidity) : l'amplitude est une définition privée opaque
  - `offline_member_leaves_reconstructed_pattern_block_unchanged` (Round26B4ConstellationGapElementLocalisation) : idem, instance bloc de pattern
  - `offline_member_leaves_reconstructed_prime_gap_unchanged` (Round26B4ConstellationGapElementLocalisation) : idem, instance écart premier
  - `constellationWindowHeights_length` (Round26B4ConstellationGapPattern) : idem, hauteurs
  - `constellationWindowGaps_length` (Round26B4ConstellationGapPattern) : idem, écarts
  - `constellation_gaps_pos_iff_critical_line` (Round26B4ConstellationGapPattern) : la conclusion est une équivalence sur T fixé, non ↔ RiemannHypothesis
  - `crosswalk_right_prime_is_prime` (Round26B4ConstellationPrimePatternCrosswalk) : idem, côté droit
  - `refinementColumn_right_prime` (Round26B4ConstellationRefinementTable) : idem, borne droite
  - `constellationRefinementEntry_indep` (Round26B4ConstellationRefinementTable) : le nom promet plus que le type : l'indépendance énoncée est une propriété de signature (preuve rfl)
  - `double_refinement_commutes` (Round26B4ConstellationRefinementTable) : fait de treillis sur les index seulement
  - `double_refinement_union_le` (Round26B4ConstellationRefinementTable) : fait de treillis sur les index seulement
  - `row_total_is_boundary_only` (Round26B4ConstellationRefinementTable) : portée dégénérée : les hypothèses ne sont satisfaites que par un même bloc (voir no_distinct_same_boundary_blocks)
  - `reflectConjZero_ne_self_iff` (Round26B4ConstellationReflectionInvolution) : contraposée du point fixe
  - `card_image_zeroHeight_eq_iff_critical_line` (Round26B4ConstellationReflectionInvolution) : équivalence à T fixé, distincte de ↔ RiemannHypothesis
  - `card_image_zeroHeight_lt_iff_offline_member` (Round26B4ConstellationReflectionInvolution) : équivalence à T fixé, distincte de ↔ RiemannHypothesis
  - `grammarVoiceRow_norm_le` (Round26B4DiscreteVariationIdentity) : majoration triangulaire, pas de lien à β
  - `normalized_delta4_cross_eq_critical_cross_shifted` (Round26B4ForwardRecurrenceAttempt) : idem, instance décalée
  - `chebyshev_error_two_sided_elementary` (Round26B4ForwardRecurrenceAttempt) : bornes en O(x), non o(x)
  - `offlineOrbitThetaPart.congr_simp` (Round26B4GrammarSpectralClosure) : lemme auto-généré sans contenu propre
  - `offlineRestThetaPart.congr_simp` (Round26B4GrammarSpectralClosure) : lemme auto-généré sans contenu propre
  - `explicitFormulaProjectedChannel_eq_perronResidueProjection` (Round26B4GrammarSpectralClosure) : restatement de nom (définition dépliée)
  - `residue_scaleFourThetaMellinContinuation` (Round26B4GrammarSpectralClosure) : porte sur Re ρ > 1/2 seulement
  - `residue_scaleFourThetaMellinContinuation_eq_factor_mul_P5` (Round26B4GrammarSpectralClosure) : porte sur Re ρ > 1/2 seulement
  - `card_Transform6` (Round26B4GrammarSpectralSectors) : type Transform6 : 4 transformations (états mod 6 pris deux à deux)
  - `four_transform_indicators_basis_decomposition` (Round26B4GrammarSpectralSectors) : type tronqué dans le lot, lu jusqu'à la troisième composante
  - `canonicalGrammarThetaDyadicMellinBlock_eq_sector_recomposition` (Round26B4GrammarSpectralSectors) : idem 120 à l'indice n+2
  - `_private.RhGapCriterion.Round26B4GrammarSpectralSectors.0.ae_on_Ioi_four_of_all` (Round26B4GrammarSpectralSectors) : lemme technique privé
  - `_private.RhGapCriterion.Round26B4GrammarSpectralSectors.0.dist_lt_of_mem_ball_half` (Round26B4GrammarSpectralSectors) : lemme technique privé
  - `psiScaleFourMellinAboveFour_eq_of_change_of_variables` (Round26B4GrammarSpectralSectors) : forme algébrique dépendant de hchange, pas de définition par le membre de droite
  - `explicitNonzeroScaleFourResidue_ne_zero` (Round26B4GrammarSpectralSectors) : le nom "Nonzero" est déjà dans la définition, l'énoncé est la non-nullité
  - `GrammarSectorMeromorphicContinuationAt.meromorphicAt` (Round26B4GrammarSpectralSectors) : projection d'une structure (champ), pas un théorème analytique autonome
  - `GrammarSectorMeromorphicFamilyAt.residue_sum_eq_global` (Round26B4GrammarSpectralSectors) : projection d'une structure (champ)
  - `grammarZeroModeEnergy_exact_growth` (Round26B4GrammarSpectralSectors) : ρ complexe quelconque (pas nécessairement zéro de zêta)
  - `grammarZeroModeEnergy_subexponential_forces_re_le_half` (Round26B4GrammarSpectralSectors) : ρ complexe quelconque (pas nécessairement zéro de zêta); n'établit que Re ρ au plus 1/2 sous l'hypothèse de croissance, ne donne pas RH
  - `scale4_eigenvalue_norm_le_one_implies_re_le_half` (Round26B4GrammarSpectralSectors) : ρ complexe quelconque; fait élémentaire, ne donne pas RH

## 6. Contrôle de complétude

- Modules du lot : 159 ; théorèmes du lot dans le jsonl : 2467 ; entrées des tables : 2467 ; noms distincts (nom, module) : 2467.
- Contrôle par script sur le fichier final : 2467 lignes de théorème dans les tables par module = 2467 lignes du lot dans `data/rh_gap_criterion.jsonl` : CONFORME.
