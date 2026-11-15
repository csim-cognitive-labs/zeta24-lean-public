# Rapport — raccordement théorèmes acquis × CAP × contacts (directive R11, 2026-11-01)

Livrables : `RHV6Fresh/RhGapPort/PrimesDetermineZeros.lean` (port, 22 théorèmes), `RHV6Fresh/Terminal/PrimeCapsContactsBridge.lean`
(raccordement, 27 théorèmes), `CollectiveContactRigidity.lean` (deux hypothèses de substitution supprimées), trois réexports dans
`RHV6Fresh/PNTPort/`, sonde hors build `ProbePrimeCapsContactsBridge.lean` + sortie brute `.out.txt`, journal `COMPILATION_20261101.md`.
Tous les modules sont isolés (non ajoutés à `RHV6Fresh.lean`) ; chaîne terminale non modifiée ; axiomes standard partout
(`[propext, Classical.choice, Quot.sound]`) ; aucun `sorry`, `admit`, axiome, aucune hypothèse posée.

## 1. Incident d'import R9 : reproduit, identifié, résolu (§3 de la directive)

| Étape | Constat |
|---|---|
| Reproduction | `import RHV6Fresh.PNTPort.Sobolev failed, environment already contains 'CS.deriv' from RHV6Fresh.Zeta23Port.FromPNTPlus.Sobolev` (journal R9, tentative 1). |
| Modules et symboles | `PNTPort/Sobolev.lean` et `Zeta23Port/FromPNTPlus/Sobolev.lean` : deux copies du MÊME fichier source (PrimeNumberTheoremAnd/Sobolev.lean), corps identiques (`diff` vide sur les corps), déclarant `CS`, `CS.deriv`, `W1`, `W1.deriv`, `W21`, `trunc` dans l'espace de noms racine. Même situation pour `Fourier.lean` (seule différence : un retour à la ligne) et `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` (`Real.tendsto_pow_log_div_pow_atTop`, seul l'en-tête différait). |
| Nature | **Définitionnel, non mathématique** : double déclaration d'objets identiques ; aucune divergence d'énoncé, de preuve ni de dépendance. |
| Raccord minimal | Les trois fichiers du port PNT deviennent des réexports (`import RHV6Fresh.Zeta23Port.FromPNTPlus.<même nom>`), en-tête de provenance conservé. Aucun théorème modifié. |
| Compilation commune | Reconstruction `PNTPort.Defs`, `Wiener` (38 s), `Consequences` (28 s), `LogGapsTheorem`, `SummitVertical` : `Build completed successfully`. Sonde de coexistence (`LogGapsTheorem` + `FrequencyCap` + `CollectiveContactRigidity` dans un même fichier) : EXIT=0. |
| Hypothèses de substitution supprimées | `every_zero_in_some_crowd_of_logGapsVanish (hL : Tendsto …)` → `every_zero_in_some_crowd (w)` (preuve par `logGapsVanish_holds`) ; `crowdRadialRigidity_iff_riemannHypothesis (hL)` → sans hypothèse. Recompilé : EXIT=0. |

## 2. CAP effectivement disponibles (§2) — tous compilés, inconditionnels, sans dépendance à RH

| Théorème | Source | Hypothèses (signature) | Conclusion | RH |
|---|---|---|---|---|
| `height_le_iff_card` | `Terminal/FrequencyCap.lean:78` | `k : ℕ`, `a : ℝ` | `T_{k+1} ≤ a ↔ k+1 ≤ #upperWindow a` | absente |
| `upperCount_eq_Ncount` | `FrequencyCap.lean:96` | `a` | comptage terminal = `N(0,a]` du port zeta23 | absente |
| `Ncount_nat_le` | `FrequencyCap.lean:113` | `A₀ ≥ 0`, borne locale `hA` | `N(0,n] ≤ n·A₀·log(n+3)` | absente |
| `lower_cap` | `FrequencyCap.lean:137` | — | `∃ A₀ ≥ 1, n·A₀·log(n+3) < k+1 → n < T_{k+1}` | absente (comptage local `zeta_local_zero_count`, `Zeta23Port/RvM/LocalCount.lean:266`) |
| `upper_cap` | `FrequencyCap.lean:186` | — | `∃ C T₀ A₀, … → T_{k+1} ≤ 2T` | absente (`riemannVonMangoldt gammaFacts`, `Zeta23Port/RvM/Statement.lean:20`) |
| `caps_count_off_pairs_twice` | `FrequencyCap.lean:219` | `a` | `N(0,a] = N₀(a) + 2·W(a)` | absente |
| `contact_interval_ge_of_height_le` | `FrequencyCap.lean:228` | `T_z ≤ a`, `k : ℤ` | `π/a ≤ log(C_{k+1}/C_k)` | absente |
| `contact_interval_lt_of_lt_height` | `FrequencyCap.lean:235` | `0 < n < T_z`, `k` | `log(C_{k+1}/C_k) < π/n` | absente |

Portée exacte (consignée dans le module) : les CAP portent sur le comptage total avec multiplicité, ON et OFF confondus ; ils
bornent la hauteur du membre de rang `k+1` par des fonctions de `k` seul.

## 3. Théorèmes universels de détermination (§4) — portés, raccordés

| Théorème | Source d'origine → port | Hypothèses | Conclusion | Transport | RH |
|---|---|---|---|---|---|
| `primes_determine_zeta_in_halfplane` | `rh_gap_criterion/…/ZeroPrimeReconstruction.lean:349` → `RhGapPort/PrimesDetermineZeros.lean` | `1 < Re s` | produit d'Euler = `ζ(s)` | Mathlib `riemannZeta_eulerProduct_tprod` | absente |
| `primes_determine_zeta_meromorphic_continuation` | `…/PrimeDeterminesZetaAndZeros.lean:25` → port | `IsPrimeDeterminedZetaContinuation F` | `F = ζ` sur `{1}ᶜ` | identique (unicité analytique, `isPreconnected_compl_one_complex` de `rhv3_lean`) | absente |
| `primes_determine_nontrivial_zero_multiset` | `…:61` → port | idem | mêmes zéros non triviaux, mêmes ordres | identique | absente |
| `primeDeterminedZeroSource_eq_canonical`, `prime_determined_any_zero_source_object_eq` | `…/PrimeDeterminedZeroCompleteGrammar.lean:151,167` → port | idem | source déterminée = source canonique ; tout objet transporté | identique | absente |
| `prime_determined_zero_window_eq_canonical_any_length` | `…/PrimeDeterminedZeroRecovery.lean:115` → port | idem, `T n k` | fenêtre ordonnée déterminée = canonique | identique (fenêtre générique portée §3 ; spécialisation canonique via `nontrivialZetaZerosByHeight_finite`, `rhv3_lean/…/ZetaZeroHeightTruncation.lean:159`) | absente |
| `riemannZeta_isPrimeDetermined`, `primeDetermined_unique` | nouveaux (raccord) | — / `hF hG` | `ζ` est admissible ; deux `F` admissibles coïncident hors de `1` | — | absente |
| `isNontrivialZetaZero_iff_strip` | nouveau (raccord) | `ρ` | prédicat Mathlib ⟺ prédicat de bande `PIsNonTrivialZetaZero` | `isNontrivialZetaZero_re_mem_Ioo` (`rhv3_lean/…/ZetaZeroHeightTruncation.lean:122`, port Kadiri) | absente |
| `zeroPositiveMembers_canonical_eq_upperWindowOpen`, `mem_zeroOrderedMembers_primeDetermined_iff` | nouveaux (raccord) | `hF`, `T` | la vue ordonnée déterminée par les premiers EST la fenêtre ouverte de RHV6Fresh | — | absente |

Hypothèse unique de tous ces énoncés : `IsPrimeDeterminedZetaContinuation F` (analytique hors de `1`, égale au produit
d'Euler sur `Re s > 1`). Elle est satisfaite par `ζ` et par elle seule hors du pôle.

## 4. Raccord aux objets de RHV6Fresh (`PrimeCapsContactsBridge.lean` §1)

| Objet RHV6Fresh | Théorème de raccord | Conclusion |
|---|---|---|
| vrais zéros (`TrueZero`, `PIsNonTrivialZetaZero`) | `primeDetermined_strip_iff` | `F ρ = 0 ∧ 0 < Re ρ < 1 ↔ PIsNonTrivialZetaZero ρ` |
| fenêtre fermée `upperWindow T` | `primeDetermined_upperWindow` | = zéros de bande de `F`, `0 < Im ≤ T` |
| foule `crowd I` | `primeDetermined_crowd` | = zéros de bande de `F`, `0 < Im ≤ π/ℓ` |
| membres canoniques, hauteurs, positions radiales | `primeDetermined_canonicalMember_zero`, `primeDetermined_coordinates` | `F(β_k + i T_k) = 0` |
| contacts | fonctions du membre (`contactMinusAt`), donc de `F` via les coordonnées ; lus par `coordinates_from_two_contacts` (`CollectiveContactRigidity.lean:115`) | — |
| comptage avec multiplicité (objet des CAP) | `primeDetermined_mult_of_mem`, `primeDetermined_upperCount` | `= Σ analyticOrderNatAt F` |
| occurrences, rencontres, contributions spectrales | définies sur `ExplicitIndex`/`TrueZero` (zéros de `ζ`), donc sur les zéros de `F` par les égalités ci-dessus ; la demande : `primeDetermined_demand_decomposition` | `D_I = foule + queue`, foule lue dans `F` |
| question radiale | `primeDetermined_lowZero_iff_not_riemannHypothesis`, `primeDetermined_lowZero_iff_offCarrier` | « `F` a un zéro bas » ⟺ ¬RH ⟺ un porteur OFF existe |
| toute propriété | `primeDetermined_property_iff` | `P F ↔ P ζ` pour `P` invariante hors du pôle |

Distinction demandée (§4) : la détermination globale est une identité (`F = ζ`), elle fixe la constellation entière y compris
les positions radiales ; la reconstruction constructive par les contacts (`coordinates_from_two_contacts`) lit `(T, β)` sur
deux contacts d'un membre donné. Les deux sont compilées ; ni l'une ni l'autre n'est niée.

## 5. Compositions compilées (§5, §7)

| Théorème (`PrimeCapsContactsBridge.lean`) | Compose | Conclusion |
|---|---|---|
| `lower_cap_contact_interval`, `lower_cap_pitch` | `lower_cap` × `contact_interval_lt_of_lt_height` | pas de contact du rang `k+1` strictement sous `π/n` dès que `n·A₀·log(n+3) < k+1` |
| `upper_cap_contact_interval` | `upper_cap` × `contact_interval_ge_of_height_le` | pas au moins `π/(2T)` sous la condition de Riemann–von Mangoldt |
| `OffCarrier.pair_blind_to_caps_and_steps` | `outgoing_same_height` × `pair_same_crowds` × `contactLog_step_blind_to_radial` | paire OFF/sortant : même hauteur, même pas, mêmes foules, mêmes pas de contact |
| `OffCarrier.pair_counted_twice` | `caps_count_off_pairs_twice` × `zetaZeroMultiplicity_pos` | `W(a) ≥ 1` et `N(0,a] = N₀ + 2W` dès que `T ≤ a` |
| `crowd_card_le_count`, `crowd_card_cap` | `upperWindow_card_le_count` × `upperCount_eq_Ncount` × `Ncount_mono` × `Ncount_nat_le` | `#foule ≤ ⌈π/ℓ⌉·A₀·log(⌈π/ℓ⌉+3)` |
| `crowd_contains_rank_of_upper_cap` | `upper_cap` × `mem_crowd_iff_height_le` × `height_le_iff_card` | rang `k+1` dans la foule si `2T ≤ π/ℓ` et condition RvM |
| `crowd_family_contacts_le`, `crowd_family_contacts_cap` | `contactsCrossed_le_one_of_mem_crowd` × `sum_le_card_nsmul` × `card_le_card_of_injOn` × `crowd_card_cap` | contacts traversés par toute famille de la foule ≤ #famille ≤ #foule ≤ cap |
| `window_sdiff_card_le_Ncount`, `crowd_transition_card_le`, `crowd_transition_cap` | `mem_upperWindow` × `zerosIn_finite` × `card_nsmul_le_sum` × `Ncount_mono` × comptage local | transition de foule entre deux écarts ≤ `N(π/ℓ_J, π/ℓ_I]` ≤ `A₀·log(|π/ℓ_J|+3)` si seuils à moins d'une unité |
| `tail_unit_window_cap` | idem | membres de queue par fenêtre unité ≤ `A₀·log(|t|+3)` |
| `primeDetermined_demand_decomposition` | `crowd_tail_decomposition` × `primeDetermined_crowd` | `D_I = foule + queue`, foule = zéros de bande de `F` sous le seuil |
| `crowdRadialRigidity_iff_riemannHypothesis'` | `crowdRadialRigidity_iff_riemannHypothesis` (sans hypothèse) | rigidité radiale de la foule ⟺ RH |

Toutes valent pour toute position radiale (aucune ne mentionne `β` sauf les deux dernières lignes, par identité).

## 6. Audit de dépendances des étapes de la composition vers une contradiction OFF (§6)

| Élément | Théorème | Source | Hypothèses | Statut | Transport | Conclusion | RH |
|---|---|---|---|---|---|---|---|
| OFF existe | `exists_offCarrier_of_not_riemannHypothesis` | `OffCarrier.lean:88` | `¬RH` | compilé | — | `Nonempty OffCarrier` | prémisse à contredire |
| OFF dans une foule | `every_zero_in_some_crowd` | `CollectiveContactRigidity.lean:414` | `w` | compilé (R11 : sans `hL`) | `logGapsVanish_holds` (`LogGapsTheorem.lean:25`, `chebyshev_asymptotic` `PNTPort/Consequences.lean:155`) | `∃ I, zeroPoint w ∈ crowd I` | absente |
| demande exacte | `crowd_tail_decomposition` | `CollectiveContactRigidity.lean:310` | `I` | compilé | — | `D_I = foule + queue` | absente |
| terme OFF isolé | `OffCarrier.crowdSum_split_zero` | `CollectiveContactRigidity.lean:350` | `hI` | compilé | — | foule = terme OFF + reste | absente |
| queue bornée | `collective_residual_bound` | `CollectiveContactRigidity.lean:327` | `I` | compilé | — | `‖D − foule‖ ≤ budget·(p_n + p_{n+1})` (exposant 1) | absente ; la version `√x` ⟺ suivants en ligne (`followingSum_sqrt_iff_following_le_half`) |
| CAP sur la foule | `crowd_card_cap`, `crowd_contains_rank_of_upper_cap` | bridge | — | compilé | — | taille/rang de la foule capés | absente |
| contacts de la foule | `crowd_family_contacts_cap` | bridge | famille ⊆ foule | compilé | — | contacts traversés capés | absente |
| paire et CAP | `OffCarrier.pair_blind_to_caps_and_steps`, `pair_counted_twice` | bridge | `C` | compilé | — | la paire est invisible aux CAP et aux pas | absente |
| lecture radiale | `contact_tangent_reads_radial`, `pair_contacts_shifted`, `mirror_density_dominates` | `GapContactRegimes.lean:226,237`, `CollectiveContactRigidity.lean:161` | `C`, `k` | compilé | — | contacts décalés, amplitude dominée par le miroir | absente |
| détermination | `primes_determine_nontrivial_zero_multiset` et raccords | port + bridge | `hF` | compilé | fait | zéros de `F` = zéros de `ζ` | absente |
| **conclusion `False`** | — | sonde | tout ce qui précède | **NON RÉSOLU** | — | `⊢ False` | — |

**Aucune propriété déjà démontrée n'est classée manquante.** Le seul but non résolu après application de tous les théorèmes
existants est `⊢ False` dans le contexte complet (sortie brute `ProbePrimeCapsContactsBridge.out.txt`, une seule erreur,
volontaire). Contrôle : le même contexte se ferme avec `β = 1/2` (`control_goal_closes`).

## 7. Buts encore ouverts et raisons mathématiques précises de chaque blocage (§7)

1. **La détermination universelle est un théorème d'identité.** Son hypothèse n'est satisfaite que par `ζ` hors du pôle
   (`primeDetermined_unique`, `riemannZeta_isPrimeDetermined`). Toute conséquence est donc un énoncé sur les zéros de `ζ`
   (`primeDetermined_property_iff`). Elle transporte la question « existe-t-il un zéro bas ? » exactement
   (`primeDetermined_lowZero_iff_not_riemannHypothesis`) et ne fournit aucune inégalité : pour contredire une position OFF, il
   faut une contrainte radialement sensible qui ne soit pas elle-même une reformulation de RH.
2. **Les CAP comptent avec multiplicité ON + 2·OFF.** Toute conséquence des CAP et des hauteurs est invariante quand on
   remplace, à une hauteur donnée, un zéro ON par une paire OFF/miroir (`caps_count_off_pairs_twice`, `pair_counted_twice`,
   `pair_blind_to_caps_and_steps`). Les CAP ne déterminent donc pas `β` directement (constaté, non supposé) ; ils bornent la
   taille des foules, les contacts admissibles, les transitions et le débit de la queue, pour toute `β`.
3. **Le pas de contact est `π/T`, aveugle à `β`.** Les seuls objets compilés sensibles à `β` sont les positions des contacts
   (décalage commun `pair_contacts_shifted`) et l'amplitude (`mirror_density_dominates`), qui entrent dans la demande par la
   somme de foule, identité exacte avec la queue. La borne de queue disponible est d'exposant 1 ; une borne d'exposant `< 1 − β`
   sur la queue ou sur la foule privée de la paire, à partir des seuls premiers, n'existe pas dans le corpus ; la version `√x`
   équivaut à « les suivants sont en ligne ».
4. **La reconstruction inverse directe par les rencontres** (lire `β` par la demande sans passer par les contacts d'un membre
   déjà connu) n'est pas compilée : la fenêtre ordonnée déterminée par les premiers (`prime_determined_zero_window_eq_canonical_any_length`)
   fixe l'existence et l'unicité de la constellation, pas une inégalité exploitable sur un écart donné.

But exact laissé par Lean : `⊢ False` sous `hF`, `C : OffCarrier`, `hI`, et les 29 faits listés dans la sonde. Aucune
hypothèse n'est proposée pour le fermer.

## 8. Incident indépendant constaté (hors directive, non corrigé)

`lake build` (cible par défaut `RHV6Fresh`) échoue AVANT toute modification de cette session :
`RHV6Fresh.lean:1:0: import RHV6Fresh.Terminal.SpectralWindowProjection failed, environment already contains
'RHV6Fresh.windowProjection' from RHV6Fresh.Terminal.GapTranslationInvariance` (deux modules non touchés, dernier commit
les concernant `7a9534c7`). `GapTranslationInvariance` est importé par `DemonstrationChain.lean` : toute correction touche la
chaîne ou son agrégateur, donc arrêt et question à l'auteur. La chaîne elle-même compile (`lake build
RHV6Fresh.Terminal.DemonstrationChain` : `Build completed successfully`).
