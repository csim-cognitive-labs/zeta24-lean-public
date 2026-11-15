# Journal de compilation — TwoRaccordReadingTransport.lean (2026-11-01)

Module isolé `RHV6Fresh/Terminal/TwoRaccordReadingTransport.lean` (non ajouté à `RHV6Fresh.lean`, chaîne intacte).
Décision de l'auteur : composer deux raccords consécutifs (trois membres, deux écarts d'occurrence, contributions
complexes exactes, phases conservées). Correction de l'auteur en cours d'exécution : réintégrer les CAP
(`FrequencyCap`, `ThreeZeroWindow`, `OccurrenceHeightComposition`, importés explicitement) ; critère révisé :
incompatibilité démontrée entre les deux lectures successives et une hauteur commune, sans supposer que deux rangs
exigent deux hauteurs.

| Tentative | Durée | Résultat | Erreurs exactes |
|---|---|---|---|
| 1 | 2 min 10 s (rebuild des dépendances) | échec | (a) `transport_factor_polar` : `rw [hsplit]` motif absent — `cpow_def_of_ne_zero` donne `log u * ρ`, hsplit écrit `ρ * log u` ; (b) `two_gap_telescoping` : `R₁` inconnu (variable de section non incluse dans l'énoncé) ; (c) `frozen_reading_ratio` : `ring` après un `field_simp` qui fermait déjà le but ; (d)(e) `off_two_raccord_profile`, `previous_dominates_at_second_prime` : `rw [zeroTerm_norm]` échoue sur un terme `⟨C.outgoing.zEarlierMember, ⋯⟩` (motive non type-correct sous transparence implicite) ; (f) `composite_ratio_eq` : `rw [energyRatio_eq]` même cause. |
| 2 | 16 s | échec | `transport_factor_polar` seulement : deux buts résiduels `log u * β = β * log u`, `log u * T = T * log u` (commutativité) ; **tout le reste, y compris le §5 CAP, compile**. |
| 3 | 23 s | **succès** | aucune. Résidu de commutativité corrigé par `mul_comm` dans les deux `simp`. |

Corrections : (a) hsplit réécrit dans l'ordre `log u * ρ` ; (b) section remplacée par des lieurs explicites
`(R₁ : TowerRaccord e l) (R₂ : TowerRaccord l m)` ; (c) `ring` supprimé ; (d)(e) lemme `zeroTerm_norm_pos'` énoncé sur
une Tour variable puis instancié ; (f) `refine (energyRatio_eq _ _ _).trans ?_` + `show` au lieu de `rw`.

Résultat : 28 théorèmes, tous `[propext, Classical.choice, Quot.sound]`, 0 `sorry`, 0 `admit`, aucune hypothèse
nouvelle ; `RadialConservationAtAuthenticDeparture` non introduite. Avertissements : `longLine` seulement.
Les journaux bruts `attempt1.log`, `attempt2.log`, `attempt3.log` sont dans ce dossier (ignorés par git, `*.log`).

## Lecture (critère de l'auteur appliqué)
1. §1–2 : identités valables pour toute Tour (transport d'une lecture à travers un écart, décomposition polaire module
   radial / phase de fréquence, télescopage sur deux écarts, lecture gelée à fréquence égale, transport composé sur
   deux raccords = produit des deux transports et du facteur radial transmis).
2. §3 : profil de signes sur le porteur : transport d'arrivée ≤ 1, facteur transmis < 1, transport sortant > 1 ;
   le précédent ON domine encore strictement le zéro OFF au second premier partagé ; le rapport composé `z_n → z_{n+2}`
   est le seul objet radialement sensible reliant les deux, et aucun théorème ne fixe son signe.
3. §4 : orientation, transport ≤ 1, hiérarchie au second raccord sont chacun équivalents à `ContinuationForced` (⟺ RH).
4. §5 CAP : même phase sur le second écart, contribution gelée du sortant = celle du zéro OFF × facteur radial × phase
   constante, CAP inférieur au rang n+1 appliqué à la hauteur commune, deux places du comptage, même pas de contacts,
   membre suivant encadré par la hauteur commune : **toutes des instances satisfaites par la paire**.
5. Verdict `common_height_excluded_iff_riemannHypothesis` : « sur tout porteur, les rangs n et n+1 ont des hauteurs
   distinctes » ⟺ RH. L'incompatibilité cherchée n'est pas un lemme intermédiaire ; c'est la conclusion.
   **Composition déclarée insuffisante** selon le critère fixé : ni contrainte indépendante sur le second raccord, ni
   incompatibilité entre les deux lectures et une hauteur commune ; les CAP encadrent par le rang et n'exigent pas une
   fréquence nouvelle au second événement premier. L'arrête manquante est exactement cette exigence (= ContinuationForced).
