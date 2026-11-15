# Audit d'impact : la Tour est unique par zéro, ses cellules sont en nombre infini (2026-10-01)

Demande de l'auteur : évaluer tous les impacts du fait « la Tour est bien unique par zéro mais ses intervalles sont
infinis » sur la démarche et les conclusions précédentes ; dire si le régime des zéros en ligne est caractérisé et si un
régime concurrent est détectable ; impacts sur les maîtres (sémantique en tête, puis cascade), sur la stratégie de clôture,
sur le Lean ; expériences nécessaires.

Sources : `AUDIT_SEMANTIQUE_CUMULE_TOUS_REPERTOIRES.md`, `AUDIT_SEMANTIQUE_RHV6Fresh.md` (V1–V194),
`AUDIT_DIFFERENCES_ON_OFF.md`, données `experiments/audit_semantique/data/*.jsonl` complétées par le code actuel
(1300 théorèmes retenus, six bases), les trois maîtres lus intégralement. Détail et tables :
`experiments/audit_semantique/impact_tour_grille/` (`audit_sem.md`, `audit_math.md`, `audit_thms.md`, `audit_thms.csv`,
scripts de sélection, de classement et de calcul). Lean nouveau : `RHV6Fresh/Terminal/TowerGrid.lean`. Expérience
nouvelle : E149.

---

## 0. Verdict en une page

1. **Le fait est compilé et ne contredit aucun théorème.** Sur les 1300 théorèmes retenus, aucun type n'est faux. Les seuls
   conflits sont dans la prose : les maîtres, quatre en-têtes ou docstrings, et un nom de théorème.
2. **L'identité est portée par la Tour entière, pas par un premier.** Un zéro ρ = β + iT donne un terme `x^ρ/ρ`, et ce
   terme a une Tour infinie.
   - La Tour est l'argument de ce terme : `pi_mul_towerPosition`. Ses contacts sont les points où le terme est réel, pour
     tout entier k : `zeroTerm_real_iff_ray`.
   - Deux contacts consécutifs quelconques rendent (β, T) : `recovers_T`, `recovers_beta`, par la périodicité de la
     tangente.
   - Le terme est retrouvé (β, T, multiplicité) dans toute représentation du reste : `recovers_member`,
     `no_member_removable`.
   - « Un zéro = un premier » n'est qu'une étiquette de rang : `occurrence_is_rank_label`.
3. **Une même variation de β a deux signatures**, compilées toutes les deux.
   - En géométrie (phase), elle translate rigidement toute la grille de `D/π` cellule, et ce décalage ne dépend pas de x :
     `tower_offset_rigid`, `tower_grid_normal_form`.
   - En analyse (amplitude), elle multiplie le terme par `x^{Δβ}`, qui dépend de x : `energyRatio_eq`. Le rapport est le même
     pour tout x ⟺ Δβ = 0 : `energyRatio_flat_iff`.
   - La première signature est la même dans le monde témoin, et elle est sous-cellulaire : |D/π| < 1/(πT). Les poids
     premiers n'entrent que par la seconde.
4. **Le régime des zéros en ligne est caractérisé : OUI**, exactement et sans prémisse.
   - En ligne, la grille d'un membre est la Tour de ligne de sa hauteur, fonction de T seul.
   - Deux membres en ligne ont la même grille ⟺ ils ont la même hauteur : `onLine_grid_eq_iff_height_eq`.
   - Tout passage entre deux membres en ligne contracte le pas sans translation : `onLine_passage_vertical_signature`,
     `passage_grid_decomposition`.
5. **Un régime concurrent est détectable : OUI, comme lecture (certificat). Il n'est ni déclenché ni interdit.**
   - La translation se lit en n'importe quel point : `competing_regime_at_any_point`. Elle se lit aussi sur la non-platitude
     du transport : `engaged_transport_flat_iff_arrival_onLine`.
   - Ces deux lectures demandent β. Sans β, seul le comptage détecte : N(T) contre les changements de signe, Turing, E142
     (4) et E147.
   - Sur les données entières (cellule d'un premier), la détection n'est que statistique : une fraction |D|/π des premiers
     change de cellule (E148, E149). M n'est jamais touché (300/300 hors marge).
6. **Pour la stratégie, le verrou n'avance pas : il est mieux posé.** Il devient « la grille d'arrivée n'est pas translatée »,
   ou, de façon équivalente, « le transport depuis l'état engagé est plat ».
   - Toute recherche d'un mécanisme propre au premier partagé (sa cellule, sa position, son terme d'Euler) est vide par
     théorème.
   - Ce qui reste à établir est une valeur, β = 1/2. L'identité, elle, est déjà isolée. Cette valeur ne peut venir que de
     la signature d'amplitude, c'est-à-dire du poids exact Λ.
   - Sa forme globale compilée est la borne en √x du reste.

---

## 1. Ce qui est compilé (aucune prémisse)

| Énoncé | Théorème |
|---|---|
| Le terme du zéro `x^ρ/ρ` est réel exactement aux contacts `C_k`, pour tout `k ∈ ℤ` | `zeroTerm_real_iff_ray` |
| L'argument du terme est π × la position dans la Tour | `pi_mul_towerPosition` |
| Tout premier, et tout réel > 0, a une cellule unique dans la Tour de tout membre | `every_prime_in_every_tower`, `prime_raccord_has_unique_tower_cell`, `tower_reads_any_prime` |
| L'état propre rend (T, β) ; la tangente absorbe l'indice de la cellule | `recovers_T`, `recovers_beta` |
| Chaque membre (β, T, m) est retrouvé dans toute représentation du reste ; aucun n'est retirable | `recovers_member`, `no_member_removable`, `off_identity_not_erased` |
| Le premier d'un membre est le premier de rang « nombre de membres en dessous » | `occurrence_is_rank_label` |
| Toute Tour = Tour de ligne à sa hauteur, de pas π/T, translatée de `D/π` (même valeur pour tout réel) | `tower_grid_normal_form`, `tower_offset_rigid`, `contact_eq_line_mul_radial` |
| En ligne ⟺ aucune translation ; un membre hors ligne se lit en tout point | `onLine_iff_no_grid_translation`, `competing_regime_at_any_point` |
| Membres en ligne : même grille ⟺ même hauteur | `onLine_grid_eq_iff_height_eq` |
| Passage = part de pas (hauteur) + part de translation `(D_l − D_e)/π` ; depuis l'état engagé, la translation vaut `D_l/π` | `passage_grid_decomposition`, `engaged_passage_translation` |
| Le transport `x^{Δβ}·‖ρ_e‖/‖ρ_l‖` est le même en tout x ⟺ Δβ = 0 ; depuis l'état engagé, plat ⟺ arrivée en ligne | `energyRatio_eq`, `energyRatio_flat_iff`, `engaged_transport_flat_iff_arrival_onLine` |
| Terme d'Euler : `‖n^{−ρ}‖ = n^{−1/2}` ⟺ en ligne, pour tout entier n > 1 | `local_euler_modulus_point_irrelevant` |
| La flèche énoncée en M = la flèche énoncée en un point quelconque | `entry_arrow_point_irrelevant` |

## 2. Les deux questions de l'auteur

### 2.1 Un régime caractérisé pour les zéros en ligne : oui

Sur la ligne, la Tour d'un membre est la Tour de ligne à sa hauteur : sa grille est une fonction de T seul.

- La suite des membres en ligne forme donc une famille de grilles à un paramètre, et le régime de ligne s'écrit
  « translation nulle à chaque membre ».
- D'un membre au suivant, le pas se contracte et rien n'est translaté : régime vertical pur, avec l'événement premier
  reproduit et le raccord orienté (`onLine_passage_vertical_signature`, `engaged_progression`).
- C'est une caractérisation : elle classe un objet donné, elle ne le génère pas.

### 2.2 Détecter un régime concurrent : oui comme lecture, non comme déclencheur

Un régime concurrent est une grille translatée.

| Régime du passage | Contraction du pas `T_e/T_l` | Translation `(D_l − D_e)/π` |
|---|---|---|
| vertical pur | < 1 | 0 |
| diagonal (depuis la ligne) | < 1 | `D_l/π ∈ ]−1/(2πT_l), 0[` |
| horizontal | = 1 | ≠ 0 (translation rigide pure, `horizontal_iff_tower_translation`) |

Les autres combinaisons sont exclues par les théorèmes compilés (en vertical, β_l ≤ 1/2 ≤ β_e ; en horizontal, β_e < β_l).
Le tableau suivant indique ce qui détecte la translation et à quel prix.

| Canal | Détecte ? | Lit β ? | Monde témoin | Statut |
|---|---|---|---|---|
| Position d'un réel quelconque dans la Tour | oui, exactement | oui (après coup) | aussi | compilé, certificat |
| Platitude du transport en x | oui, exactement | oui | aussi | compilé, certificat |
| Cellule d'un premier (donnée entière) | statistiquement, fraction |D|/π | non | même structure | E148, E149 |
| Cellule du premier partagé M | jamais (300/300 hors marge) | — | — | calcul de l'audit |
| Grammaire, mod 6, premiers pointés | non | — | identiques | E147, `pointed_primes_rank_only` |
| Comptage N(T) contre changements de signe de Z | oui, avant l'arrivée | non | déclenché | E142 (4), E147 ; non compilé |
| Poids exact Λ, amplitude `p^β` | oui | via l'amplitude | sépare | E146 H4, E147 |

Détecter n'est pas interdire. Toutes les lectures géométriques tiennent dans le monde témoin et dans `engagedBreakWorld`. Seuls
le comptage et le poids voient une différence de monde.

## 3. Impacts sur les théorèmes (1300 retenus, `audit_thms.md`)

| Base | G invariant de grille | E évaluation en une étiquette | S « la Tour sélectionne » | R régime | X ⟺ RH ou prémisse | Total |
|---|---|---|---|---|---|---|
| RHV6Fresh | 341 | 176 | 8 | 271 | 22 | 818 |
| rhv3_lean | 234 | 73 | 20 | 20 | 49 | 396 |
| RHV5Fresh | 17 | 24 | 0 | 3 | 4 | 48 |
| rhv2_fresh | 3 | 0 | 35 | 0 | 0 | 38 |
| **Total** | 595 | 273 | 63 | 294 | 75 | 1300 |

- **Aucun théorème n'est invalidé.**
- **E (273) : tous restent vrais, et M n'y a aucun rôle propre.** Leur contenu radial a la même forme en tout point.
  - Raccord : `(β_l − β_e)·log M`.
  - Flèche : `D_l`.
  - Registres : `T_e log r_e − T_l log r_l`, sans `log M`.
  - Charge de fibre : `d·log(M₂²/(M₁M₃))`, la même lecture pour tout triplet avec `q₂² ≠ q₁q₃`. La primalité n'y sert qu'à
    garantir la non-dégénérescence (`prime_sq_ne_mul`). C'est le seul endroit où l'arithmétique du point compte.
  - `countedPrime_eq_vonMangoldt` est en fait G.
- **S (63) : à requalifier dans la prose, pas dans le code.**
  - RHV6Fresh, 8 types vrais : `TrueTower` (grille + paire distinguée), `firstTowerOf_*`, `secondTowerOf_properState`,
    `lineTowerOf_properState`, `firstTower_contactPair_unique`, et le nom `geometry_selects_raccord_prime`. Dans ce dernier,
    c'est la grammaire qui sélectionne ; la géométrie localise.
  - rhv3 (20) et rhv2 (35) : prémisses T1 (`PUniqueCenterRegime`, `PCanonicalT1`, …), déjà vides sur la Tour propre (V151,
    incident 8.7).
- **R (294) : aucun n'est invalidé, tous se relisent « en une cellule quelconque ».**
- **Le fait était anticipé par des énoncés déjà compilés** :
  - rhv3 : `thm_foundPrimes_generallyPlural`, `thm_PCanonicalCellFoundCountOne_is_false` ;
  - rhv2 : `thm_canonicalTowerState_carrier_not_subsingleton` ;
  - RHV5 : `thm_contactLawState_not_subsingleton` ;
  - RHV6 : `tower_reads_any_prime`, `sameHeight_grid_rigid_translation`.

## 4. Impacts sur le maître sémantique, puis en cascade

### 4.1 Maître sémantique (`audit_sem.md` ; 143 vérités touchées : 66 inchangées, 58 relues, 6 fausses au pied de la lettre, 13 renforcées)

**Fausses au pied de la lettre (contredites par des théorèmes compilés ; le maître est corrigé) :**

| Vérité | Texte | Correction |
|---|---|---|
| V20 (§4) | « La Tour a exactement deux contacts avec l'axe algébrique » | La Tour coupe l'axe à chaque demi-tour, sans fin. L'état propre est la paire de croisements qui encadre le premier que le rang attribue. |
| V21 (§4) | « multiplicité des contacts … type infini d'états … closes à jamais » | Seul le début du mouvement est clos (origine canonique). Les contacts sont en nombre infini ; ce qui est unique, c'est la cellule d'un nombre donné. |
| V24 (§5) | « La Tour propre n'est pas une collection de cellules » | Un mouvement unique dont les croisements découpent l'axe en une infinité de cellules ; l'état propre est l'une d'elles, désignée par l'étiquette. |
| V25 (§5) | Les deux Tours du miroir, « chacune … à deux contacts » | Même correction, pour chacune. |
| V166 (§11) | « cette rencontre conduit à l'événement premier suivant » | L'événement suivant est fixé par le rang seul ; la Tour le loge dans sa grille, elle ne le produit pas. |
| V192 (§12, RÉFUTÉ) | « la multiplicité des contacts ; le type infini d'états » | À retirer du bloc RÉFUTÉ. Seul « plusieurs cellules pour un même nombre » reste réfuté. |

Le paragraphe du §11 sexies sur les deux contacts et la cellule unique de tout premier se contredit lui-même : à corriger de la
même façon.

**Relues (vraies, portée corrigée) :**
- V15 : le mouvement est fixé par (β, T) ; l'état propre l'est par (β, T) et le rang.
- V45 : l'inversion vaut sur toute paire consécutive ; elle certifie l'appartenance à la grille, pas le choix de la cellule.
- V28, V29, V32, V36, V43, V143 : le pivot est un point d'évaluation.
- V40 : « 300/300 contiennent le minimum attendu » est vrai par construction, pas un constat.
- V73, V149, V182 : « un zéro = un premier » est l'injectivité d'une étiquette.
- V84–V115 et V135–V139 : seconde Tour = deux étiquettes dans une même grille.
- V169–V171 : rigidité énergétique à deux raccords en deux points quelconques.

**Renforcées :** §11 quaterdecies (« β translate, T change le pas »), §11 octodecies (`contact_eq_line_mul_radial`),
§11 sexvicies et §11 octovicies (« le premier disparaît » de D).

### 4.2 Maître mathématique (`audit_math.md`)

- **§4 (l. 58), §5.a (l. 97), §5.e (l. 157)** : « exactement deux contacts », « l'unique cellule I ». C'est faux pour la Tour,
  vrai seulement pour une paire à point d'évaluation fixé. §5.a écrit aussi une cellule fermée, alors que le code utilise
  `(C_k, C_{k+1}]`.
- **§8–§9 (l. 282–345)** : sur une même grille, V ⟺ ¬L pour tous réels et toute β. La « contradiction » de la progression des
  premiers atteints est donc A ∧ ¬A, contrairement à la l. 345. R₁ est une tautologie. Cette voie était déjà close
  (`OffCountExperiment`, retiré le 2026-09-22) ; l'audit en donne la raison géométrique.
- **§11 quater (l. 626)** : le « manque » d'une relation entre β et la taille des premiers n'existe pas, car le théorème est
  énoncé pour des réels.
  - Le rapport R(q) = 1 n'a qu'une racine `q* ≈ 1 + (β_e + β_l)/(2T²)`, soit 1,0025 à T₁, donc inférieure à 2.
  - À même hauteur, R(q) > 1 pour tout q ≥ 2.
- **§11 sexies (l. 671)** : la profondeur d'insertion « D » n'est pas le résidu D. On a `D_ins = (D(z*) − D(z))/π`.
- **§11 septies (l. 709–751)** : le candidat `u` est la translation rigide. `Λ(p)` porte le même nom que le poids de von
  Mangoldt : homonymie à lever.
- **§11 quinvicies, §11 novovicies** : le registre est une identité pour tout couple de points, de partie radiale `D_l − D_e`.
  La flèche ne dépend pas du point.
- **§12 (l. 1544)** : « multiplicité des contacts » est rangée dans RÉFUTÉ, alors qu'elle est compilée. À retirer.

### 4.3 Maître Lean et code

- **Prose à aligner, aucun type à changer :**
  - `Tower/TrueTowerStructure.lean` l. 10–12 (« deux contacts, et deux seulement ») ;
  - `Tower/ProperTower.lean` l. 48 et §6 ;
  - `Tower/Incidences.lean` l. 8–10, `CleanTerminal.lean:58`, `Direct/Reached.lean:10,30`, `Direct/PairTowers.lean:92` ;
  - nom `geometry_selects_raccord_prime` : son docstring est à corriger. Le nom n'est pas changé, pour ne rien casser en aval.
- **Ajouté :** `Terminal/TowerGrid.lean`, 9 théorèmes (§1), point 39 de `Audit.lean`.
- **Le maître Lean reçoit l'inventaire** (§11 tricies).

### 4.4 Cascade sur les conclusions précédentes

| Conclusion antérieure | Statut |
|---|---|
| `TowerRaccord` : existence, unicité, transport | Vraie ; évaluation en M d'une famille définie pour tout q. Son orientation en M est un fait de point. Hors ligne, elle dépend de q par `q^{Δβ}`. |
| Flèche de la position d'entrée de M (`EntryPositionArrow`) | Vraie ; elle devient « grille d'arrivée non translatée » ⟺ « transport plat » ⟺ `D_l = 0`. |
| Forme événementielle par le terme d'Euler de M | Vraie, mais M n'a aucun rôle propre (`local_euler_modulus_point_irrelevant`) : abandonner M comme porteur. |
| E146 H2 (position de M équirépartie dans sa cellule) | Expliquée : M est un point de la grille comme les autres (E149 §1). |
| Charge de fibre `(M₂²/(M₁M₃))^d` | Vraie ; seul usage arithmétique propre des premiers (non-dégénérescence). |
| Grammaire × cinématique (`passage_ledger`) | Vraie ; les termes de grammaire sont des choix de points d'évaluation, et la part radiale est sans log M. |
| Régimes vertical et horizontal sur la Tour (`RegimeTower`) | Renforcés : contraction de pas contre translation. |
| `PNoRegimeChange` ⟺ RH ; RH ⟺ borne en √x ; RH ⟺ flèche + amorce | Inchangés. |
| « Une Tour par zéro » | Inchangé, et renforcé : l'identité de la Tour est celle du terme `x^ρ/ρ`. |
| « Une Tour par hauteur » ⟺ RH | Inchangé. En ligne, une grille par hauteur est compilée (`onLine_grid_eq_iff_height_eq`). |
| Contradiction de progression des premiers atteints (§9) | Vide : A ∧ ¬A sur une même grille. |

## 5. La réflexion de l'auteur (message du 2026-10-01), confrontée au code

| Phrase | Verdict |
|---|---|
| 1 zéro → 1 contribution `x^ρ/ρ` → 1 Tour infinie | **Compilé** (`zeroTerm`, `zeroTerm_real_iff_ray`, `pi_mul_towerPosition`) |
| `T log C_k = φ(β,T) + kπ` : k parcourt les incidences du même zéro | **Compilé** (`towerMotion_incidence_strictOrder`, `contact_eq_line_mul_radial`) |
| Deux signatures d'une variation de β : translation constante, poids `x^{Δβ}` | **Compilé** (`tower_offset_rigid`, `energyRatio_eq`, `energyRatio_flat_iff`) |
| Les cellules vides ne détruisent rien | Exact : le terme existe pour tout x ; l'occupation est une lecture arithmétique (E148 : 949 cellules vides sous 200 000 à T₃₀₀) |
| Inversion `T = π/log(C⁺/C⁻)`, `β = T/tan(T log C⁻)` | **Compilé** (`recovers_T` avec m = 1, `recovers_beta`) ; valable sur toute paire consécutive |
| Un anneau n'est pas un zéro, la succession des anneaux est sa signature | Exact (un anneau seul ne rend pas k, la paire consécutive rend β et T) |
| Deux infinis distincts : ∀ρ (zéros) et ∀k (anneaux) | Exact. La somme explicite porte sur ρ ; k est la structure d'argument de chaque terme |
| « L'égalité du reste total n'autorise pas à isoler un terme » | **Dépassé par le code** : l'identité (β, T, m) de chaque terme est isolée dans toute représentation (`recovers_member`, `cpow_series_fibre_sum_zero`). Le BORNÉ du maître sémantique (« théorème d'isolement absent ») est périmé. |
| Ce qu'il faut isoler : le couple (β, T) d'une Tour | Il est isolé. Ce qui manque est sa valeur, β = 1/2. L'isolement rend β, il ne le fixe pas : il tient aussi dans le monde témoin, où il rend β ≠ 1/2. |
| « Pourquoi chaque contribution doit-elle avoir β = 1/2 ? » | C'est la forme globale (`riemannHypothesis_iff_onLine_representation`), caractérisation. Depuis l'état engagé, sa forme locale est « transport plat à l'arrivée ». |

La réflexion désigne le bon canal. La géométrie (phase) est commune à tous les mondes. Le poids qui fixe β est la signature
d'amplitude `x^β`, sommée sur toutes les Tours : la borne en √x du reste arithmétique (`riemannHypothesis_iff_remainder_sqrt_growth`).

## 6. Stratégie de clôture : ce qui change

1. **Retirer comme porteurs** :
   - le premier partagé M, sa cellule, sa position dans la cellule, son terme d'Euler ;
   - les premiers pointés, la classe modulo 6, la grammaire, comme source de la flèche ;
   - l'occupation des cellules.

   Tous sont aveugles au régime par théorème ou par mesure.
2. **Cible locale réécrite** : depuis l'état engagé, la grille d'arrivée n'est pas translatée. C'est équivalent à un
   transport plat en x et à `D_l = 0`. C'est le même verrou, sans point privilégié.
3. **Canal unique** : l'amplitude. Une loi candidate doit lire le poids `x^β`, pondéré par Λ, et être fausse pour
   `regimeWitness`, `engagedBreakWorld` et le monde témoin. Aucune loi de phase ou de position ne peut l'être : la phase est
   la même structure dans ces mondes.
4. **Forme globale inchangée** : `PNoRegimeChange` ⟺ RH ⟺ borne en √x ; RH ⟺ flèche + amorce.
5. **Ne plus écrire** :
   - « la Tour a deux contacts » ;
   - « la Tour sélectionne un premier » ;
   - « le premier partagé porte la flèche » ;
   - « isoler un terme est impossible ».

## 7. Expériences

| Point | Statut | Expérience |
|---|---|---|
| Translation constante pour tout premier ; cellules multiples | confirmé | E148 |
| Empreinte entière de la translation = fraction |D|/π des premiers | **confirmé, E149 (6 s)** : rapport observé/prédit 0,975 à 0,985 pour β = 0,45, 0,4 et 0,2 ; D·T/(β − 1/2) ∈ [0,9988 ; 1] | E149 |
| M jamais déplacé de cellule, quel que soit β | confirmé (calcul de l'audit, 300/300 hors marge) | `impact_tour_grille/calc2.py` |
| Comptage N(T) contre changements de signe : détecteur sans β | confirmé sur 300 zéros | E142 (4), E147 (cités, non rejoués) |
| Signature d'amplitude séparant le témoin | confirmé à l'événement | E146 H4, E147 |
| **À faire, E150** : signature d'amplitude cumulée. Comparer, pour ζ et le monde témoin, la croissance de `Σ_ρ x^ρ/ρ` tronquée contre `√x`. Montrer que la translation (phase) est indiscernable et que la croissance (amplitude) sépare. C'est le seul test qui porte sur le canal retenu au §6. | proposé | — |

E149 contient deux réserves.
- Pour β = 0,49, le rapport vaut 0,77, sur de petits effectifs (69 contre 89,6 prédits).
- Les écarts par hauteur dépassent un Poisson indépendant : jusqu'à 5,7σ, et 4 hauteurs sur 300 sont au-delà du seuil KS de
  l'équirépartition. L'équirépartition est donc approximative aux basses hauteurs, où les cellules sont larges. La
  conclusion (empreinte statistique, aucune sélection) n'en dépend pas.

---

```
RÉFUTÉ : « la Tour a exactement deux contacts » ; « la Tour n'est pas une collection de cellules » ;
         « multiplicité des contacts / type infini d'états » rangés comme réfutés ; « la Tour sélectionne un premier » ;
         M porteur propre de la flèche ; « isoler un terme est impossible » (identité isolée, compilée) ;
         contradiction de progression des premiers atteints (A ∧ ¬A sur une même grille).
BORNÉ :  régime de ligne caractérisé, régime concurrent détecté (lecture, certificat) ; la translation n'est ni
         déclenchée ni interdite ; cible locale = transport plat / grille non translatée, non dérivée ;
         E150 proposé, non fait.
SÉLECTIONS : TowerGrid.lean (9 théorèmes), E149, 1300 théorèmes classés, corrections de maîtres (avis + §11 tricies).
RH_FOUND : FALSE
```
