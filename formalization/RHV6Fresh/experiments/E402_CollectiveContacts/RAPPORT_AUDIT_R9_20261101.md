# Rapport d'audit — mission R9 « capturer la dérive collective des contacts » (2026-11-01)

Référence : commit `3dd0f638`, R8, §19.29 ; livraison §19.30. Chaîne terminale non modifiée.

## Correspondance point par point avec la mission
| § mission | Demandé | Fait | Où |
|---|---|---|---|
| 2 | géométrie complète des contacts, inversions, branches, les deux coordonnées | `contactLog_eq`, `contactLog_step`, `height_from_contactLog`, `contactLog_tangent`, `radial_from_contactLog`, `contactLog_branch_bounds` (`T u_k − kπ ∈ ]0, π/2[`), `coordinates_from_two_contacts`, `coordinates_eq_of_contacts_eq` | `CollectiveContactRigidity.lean` §1 |
| 3 | dérive : phase d'entrée/sortie, contacts traversés, décalage à la rencontre, contribution complexe, évolution ; séparer β et T | Lean : `contactPhase_*`, `contactsCrossed_*`, `mem_crossed_iff`, `contactLog_step_blind_to_radial`, `contactLog_shift_of_same_height`, `_ne_zero`, `mirror_density_dominates` ; numérique : E402 (`e402_members_chosen_gaps.txt`, `e402_drift.txt`, quarts, rencontres exactes = 0) | §2 ; E402 |
| 4 | `D_n = S_foule + S_queue + B_n`, queue jamais supprimée, sommes complexes | `crowd_tail_decomposition` (identité compilée, toute β), `gapCrowdSum_eq_finite_sum`, `crowd_alone_never_accomplishes_demand` ; E402 colonnes `D_n B_n Z_n 2Re(S_foule) Im(S_foule) 2Re(S_queue)` | §3 ; E402 |
| 5 | seuil `π/ℓ`, foule, fréquences, contacts, contributions, queue, bornes démontrées, transitions | `threshold`, `mem_crowd_iff_height_le`, `crowd_card_transition`, `mem_crowd_sdiff_iff`, `crowd_eq_filter_of_window` ; E402 `K_n`, `dK` | §3–4 ; E402 |
| 6 | résidu collectif, borne indépendante, déplacements des contacts | `collective_residual_eq_tail`, `collective_residual_bound` (exposant 1, sans RH) ; E402 résidu ≤ 1,4·10⁻⁷, bornes `eps_uncond`/`eps_online` ; dérive analytique | §3 ; E402 |
| 7 | E402 exécutée, provenances, empreintes | README E402, SHA-256 vérifié, 1229 écarts, 2 001 052 zéros, synthétique séparé | E402 |
| 8 | obligation collective indépendante ou but manquant exact | **non obtenue** ; `CrowdRadialRigidity` ⟺ RH (`crowdRadialRigidity_iff_riemannHypothesis`, sous `LogGapsVanish`) ; but exact affiché par la sonde | §5 ; sonde |
| 9 | module isolé réutilisant `GapContactRegimes` et l'existant | 47 théorèmes, 3 tentatives, axiomes standard | journal |
| 10 | diagnostic du compilateur : énoncé, contexte, théorèmes appliqués, hypothèses nécessaires, dépendances à RH, raisons | ci-dessous | — |

## Diagnostic du premier but non résolu (sonde, sortie brute `ProbeCollectiveContactRigidity.out.txt`)
* **Énoncé** : `probe_collective_contact_rigidity (C : OffCarrier) (I : PrimeGapInterval) (hI : zeroPoint C.zero ∈ crowd I) : False`.
* **Contexte complet** (tel qu'affiché) : `hDecomp : localArithmeticTarget I = gapCrowdSum I + gapTailSum I` ;
  `hSplit : gapCrowdSum I = (terme du zéro OFF à p_{n+1} − à p_n) + Σ_{erase} (…)` ;
  `hTail : ‖localArithmeticTarget I − gapCrowdSum I‖ ≤ followingBudget I.threshold * (I.lower + I.upper)` ;
  `hMirror : zeroPoint (mirrorMember C.zero) ∈ crowd I` ; `hShift : contactLog (mirror) 0 − contactLog C.zero 0 ≠ 0` ;
  `hCoord : T = π/(u_1 − u_0) ∧ β = (π/(u_1 − u_0))/tan((π/(u_1 − u_0))·u_0)` ;
  `hAmp : ‖p_{n+1}^{ρ−1}‖ < ‖p_{n+1}^{ρ*−1}‖` ; `hCross : contactsCrossed C.zero I ≤ 1` ; `hF8` ; `hLow : β < 1/2` ; `⊢ False`.
* **Théorèmes déjà appliqués** : C126 (`localSynchronization`, via `remainder_eq_preceding_add_following`), `precedingSum_split_member`,
  `localHeightResidual_bound`, `contactAt_tangent_minus`, `log_contact_eq`, `height_from_contacts`/`radial_from_contact` (T2/T3),
  `density_norm`, `mirrorMember_radial/ordinate`, `cells_read_eq_length_over_pitch`, F8.
* **Hypothèses encore nécessaires** : une borne de la queue (ou de la part de foule privée de la paire) d'exposant `< 1 − β`
  à partir des seuls premiers, ou une lecture des contacts de la foule par la demande qui ne passe pas par `β`. Aucune des
  deux n'existe dans le corpus. Toutes les hypothèses du contexte sont vraies pour toute position radiale (identités), sauf
  `hLow`, qui est l'hypothèse à contredire.
* **Dépendances à RH** : la borne à l'échelle `√x` de la queue ⟺ tous les zéros suivants en ligne
  (`followingSum_sqrt_iff_following_le_half`, `collectiveBudget_iff_following_onLine`) ; la rigidité radiale de la foule
  ⟺ RH (`crowdRadialRigidity_iff_riemannHypothesis`). Aucune n'est posée.
* **Raison précise de l'échec** : le contexte ne contient que des identités et une borne d'exposant 1 ; l'exposant 1 est
  satisfait par tout point de partie réelle `≤ 1` (`tail_bound_admits_offline_point`), et E402 confirme qu'une paire
  synthétique ne fait jamais dépasser ces bornes (0/468). Blocage mathématique, pas d'implémentation.

## Réponse à la question terminale (§12)
Démontré : les contacts rendent les deux coordonnées ; la demande de chaque écart se décompose exactement en foule et queue
pour toute position radiale ; les foules sont des fenêtres emboîtées d'un ensemble fixe ; un membre de foule traverse au plus
un contact ; la foule seule n'accomplit jamais la demande. Mesuré : la reconstruction est exacte au niveau des données ; la
part de phase de la foule est petite ; le défaut après perturbation synthétique reste sous toute borne démontrée. Ce que Lean
affiche comme manquant : `⊢ False` sous des identités seulement — la rigidité radiale des contacts ne découle pas des
contraintes disponibles ; le but manquant exact est la borne de queue d'exposant `< 1 − β` indépendante des zéros, ou la
lecture directe des contacts par la demande. **Il n'y a pas de réponse par hypothèse.**

## Addendum R11 (2026-11-01)
Le conflit d'import PNT/Zeta23 signalé ici est résolu (réexports, `audits_compilation/prime_caps_contacts_bridge/REPORT.md` §1) ;
`every_zero_in_some_crowd` et `crowdRadialRigidity_iff_riemannHypothesis` sont désormais sans hypothèse. Le diagnostic « il manque »
de ce rapport est corrigé par §19.31 : la détermination universelle des zéros par les premiers est acquise et raccordée
(`PrimeCapsContactsBridge.lean`) ; ce qui manque est qu'elle entraîne une contradiction OFF — but exact dans la sonde R11.
