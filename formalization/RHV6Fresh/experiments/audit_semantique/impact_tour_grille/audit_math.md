# Audit du maître mathématique : rôle des premiers évalués dans une Tour (2026-10-01)

Lecture seule. Source : `RHV6Fresh/RHV6final_STRATEGIE_MATHEMATIQUE.md` (1587 lignes, lu intégralement).
Références compilées : `Terminal/OneZeroOnePrime.lean`, `PointedPrimeComparison.lean`, `EntryPositionArrow.lean`,
`CanonicalTransition.lean`, `ChangePredictor.lean`, plus les théorèmes cités ci-dessous (vérifiés par grep).
Calculs : `scratchpad/calc.py`, `scratchpad/calc2.py` (premiers ≤ 200 000, 300 zéros d'Odlyzko).

## 0. Cadre commun

Notation : `z = β + iT`, `φ = arctan(T/β)`, `φ₀(T) = arctan 2T`, `D = φ₀(T) − φ = −T log r`.
Position d'un réel `q > 0` : `θ_z(q) = (T log q − φ)/π = θ^ligne_T(q) + D/π` (`towerPosition_eq_line_add_residue`).
Cellule : `k_z(q) = ⌈θ_z(q)⌉ − 1` (`pivotCoordinate`), définie pour **tout** `q > 0` (`prime_raccord_has_unique_tower_cell`,
`GeometricEnergyRaccord.lean:40`, hypothèse `0 < q` réelle ; `every_prime_in_every_tower`).
Amplitude : `‖q^ρ/ρ‖ = q^β/‖ρ‖` (`zeroTerm_norm`, réel `q > 0`).

Deux familles de quantités, et seulement deux :

| famille | forme | dépendance radiale | dépendance en `q` de la partie radiale |
|---|---|---|---|
| **phase/position** (contacts, cellules, Π, raccord S, D, flèche) | `T log q − φ` | `D/π` (translation rigide) | **aucune** (`tower_offset_rigid`) |
| **amplitude** (énergie, transport R, pas s, charge, terme d'Euler) | `q^β` | `q^{β−1/2}` ou `q^{Δβ}` | **oui**, loi de puissance pure en `q` |

Conséquence générale : dans la famille phase, le premier est un point d'évaluation sans rôle (la radialité ne voit pas `q`) ;
dans la famille amplitude, la radialité voit `q` seulement par un caractère `q ↦ q^{Δβ}` (multiplicatif, continu) : n'importe
quel réel `q ≠ 1` lit `Δβ = 0` ou non, deux réels quelconques lisent `Δβ` exactement ; aucune propriété arithmétique du premier
n'intervient, sauf un endroit (charge de fibre, non-géométricité `M₂² ≠ M₁M₃`, `prime_sq_ne_mul`).

## 1. Section par section

### §4 (l. 56–91) et §5.a (l. 93–97) — « exactement deux contacts », « l'unique cellule I = [C⁻, C⁺] »

1. Remplacer le premier par `q` : la règle `C_k < q ≤ C_{k+1}` vaut pour tout réel `q > 0` ; le choix `q = p_min` ne fait que
   sélectionner l'indice `k`.
2. Radial : `C_k(z) = c₀(T,k)·r(z)` pour tout `k` (`contact_eq_line_mul_radial`) ; facteur commun, indépendant de `k` et de `q`.
3. **Faux au pied de la lettre.** La Tour a une infinité de contacts avec l'axe réel :
   - `zeroTerm_real_iff_ray` (`Terminal/ExplicitFormulaLink.lean:172`) : `Im(q^ρ/ρ) = 0 ⟺ ∃ k ∈ ℤ, q = C_k` ;
   - `towerMotion_incidence_strictOrder` (`Tower/TrueTower.lean:70`) : `k < l ⟹ C_k < C_l`, donc `k ↦ C_k` injective, image infinie ;
   - `every_prime_in_every_tower` (`OneZeroOnePrime.lean`) : chaque premier a sa cellule ; donc une cellule par réel, pas une seule.
   - « deux contacts » n'est vrai que pour la structure `firstTowerOf z` (une paire `(C_{k}, C_{k+1})` à `k = k_z(p_min z)`) :
     `firstTower_contactPair_unique` (`Direct/PairTowers.lean`) est une unicité **à point d'évaluation fixé**.
   - Les mêmes phrases figurent en commentaires (pas en théorèmes) dans `Tower/Incidences.lean` l. 8–10, `CleanTerminal.lean:58`,
     `Direct/Reached.lean:10,30`, `Direct/PairTowers.lean:92`.
   - Incohérence secondaire : §5.a écrit `I = [C⁻, C⁺]` (fermé), §5.c et le code `(C_k, C_{k+1}]`.
4. Reformulation :
   `Tour(z) = { C_k(z) = exp((φ₀(T) + kπ)/T) · r(z) : k ∈ ℤ }`, grille infinie, pas `π/T`, facteur radial `r(z) = e^{−D/T}` commun.
   « Contacts d'un point q » : `(C_{k_z(q)}, C_{k_z(q)+1})`, `k_z(q) = ⌈θ^ligne_T(q) + D/π⌉ − 1`. Le premier pivot est le point
   d'évaluation que la grammaire désigne ; la Tour ne le sélectionne pas.

### §5.b (l. 99–113) — lois tangentielle et de rotation
1. Vraies pour toute paire `(C_k, C_{k+1})`, tout `k` : `sin(T log C_k − φ) = 0`, `sin(T(log C_{k+1} − log C_k)) = 0`.
2. Aucun point. 3. Pas faux, mais elles ne singularisent aucune paire. 4. « Pour tout `k ∈ ℤ` ».

### §5.c (l. 115–142) — coordonnée d'entrée, `m = 1`, événement d'arrêt, cible constatée `q(w) = max{p ≤ C⁺}`
1. `k(q) = ⌈(T log q − φ)/π⌉ − 1` et `m = 1` pour tout réel `q > 0` (m = 1 par construction : paire consécutive). Événement
   d'arrêt depuis `C_0` : `C_0 < q ⟺ 0 ≤ k(q)` (`canonicalOrigin_lt_iff_zero_le_pivotCoordinate`, réel `q`).
2. Radial : `k(q)` lit `D` seulement si `{θ^ligne(q)}` est dans la marge `]0, 1/(2πT)] ∪ ]1 − 1/(πT), 1]`
   (`entry_cell_eq_line_cell_of_margin`). Cible constatée : `C⁺ = c₀·r`, `|log r| = |D|/T ∈ ]−1/T², 1/(2T²)[` ;
   `q(w)` change seulement si un premier tombe dans ce facteur multiplicatif `e^{±1/T²}` autour de `C⁺_ligne`.
   **Calcul (300 zéros, cellule de `p_min`)** : la cible constatée peut changer, pour un β quelconque dans `]0,1[`, sur **2/300**.
3. Pas faux ; « l'événement d'arrêt » est l'événement d'un point, pas de la Tour.
4. `k_w(q) = ⌈θ^ligne_{T}(q) + D_w/π⌉ − 1`, `q(w) = p_{π(⌊c₀(T,k+1)·e^{−D_w/T}⌋)−1}`.

### §5.d (l. 144–153) — inversion
Vraie pour toute paire consécutive (`tan(T log C_k) = tan φ` pour tout `k`) ; aucun point ; correcte. « Deux zéros distincts ne
partagent jamais les mêmes deux contacts » (§5.e) est vrai sous la forme : une paire consécutive quelconque détermine `(T, β)`.

### §5.e (l. 155–157) — « l'unique mouvement qui porte exactement deux contacts : z ↔ (C⁻, C⁺) »
3. Faux au pied de la lettre (mêmes théorèmes que §4). 4. Reformulation : `z ↔ grille (T, D)` ; `z ↔ (C_k, C_{k+1})` pour
n'importe quel `k`.

### §5.f (l. 159–182) — table, « cellule du pivot contient le minimum attendu 300/300 »
Automatique pour tout `q` (la cellule est définie par l'appartenance). Les `k_hist` et `C^±` sont fonctions du point choisi.
Le 300/300 n'est pas une vérification ; à requalifier en « contrôle de formule ».

### §6 (l. 184–203) — « atteint », `Occ(z) = p_{n(z)}`, « rigidifie la relation zéro → premier »
1. `p ≤ C⁺(cellule de q)` pour tout `p ≤ q` : tautologique au point d'évaluation.
2. `Occ` ne lit ni `β` ni `T` : `occurrence_is_rank_label`, `pointed_primes_rank_only` (deux membres de même rang pointent le même
   premier quelles que soient leurs hauteurs et positions radiales).
3. « la liaison zéro → premier est rigide » : vraie comme bijection rang ↔ premier, fausse si on la lit comme lien géométrique.
4. « Occ(z) := p_{n(z)} est une étiquette de rang (nombre de membres en dessous) ; la Tour de z contient tous les premiers. »

### §7 (l. 205–235) — `p_min`, « un premier à pointer dans chaque intervalle, sans choix »
Grammaire pure (rang). « pointer » est fait par la grammaire, pas par la Tour. Reformulation : « la grammaire désigne
`p_{n+1}` ; la Tour lui attribue une cellule comme à tout réel ».

### §8 (l. 237–299) et §9 (l. 301–381) — deux Tours, V, L, « contradiction de la progression des premiers atteints »
(appareil retiré du code le 2026-09-26 ; audit de la logique pour la trace)
1. Pour deux réels `q₁ ≤ q₂` et la grille du miroir : `L : q₁ ≤ C_{k(q₂)} ⟺ k(q₁) < k(q₂)` ; `V : C_{k(q₂)} < q₁ ⟺ k(q₁) = k(q₂)`.
   Au même point `q₁` (consécutivité stricte : `Occ(z*) = p_min(z)`), et comme `q₁ ≤ q₂ ≤ C_{k(q₂)+1}`,
   **V ⟺ ¬L pour tous réels, toute β** : l'hypothèse `hβ` ne sert qu'à ordonner `p_min(z) ≤ Occ(z*)`.
   `R₁ : p_min(z) ≤ C⁺(z)` est `q ≤ C⁺(cellule de q)`, tautologie.
2. Radial : V/L dépendent de β seulement par la translation `D*/π` de la grille du miroir :
   `V ⟺ {θ*(q₂)}' > s`, `s = T log(q₂/q₁)/π` (partie hauteur), `{·}' ∈ ]0,1]` ; `|D*/π| < 1/(πT)`.
   `ReadingArithmetic` (l. 387) : `V ⟹ s < 1`, `s ≥ 1 ⟹ L` : énoncés de hauteur seule, vrais pour tous réels.
3. l. 345 « Ce que la contradiction n'est pas : ni « même Tour, A ∧ ¬A » » : **faux** — V et L sont les deux membres d'une
   partition (même cellule / cellule inférieure) d'une même grille ; la « contradiction » est `A ∧ ¬A`.
4. Reformulation : `V(q₁,q₂) ⟺ ⌈θ*(q₁)⌉ = ⌈θ*(q₂)⌉`, `L ⟺ ¬V` ; dépendance radiale : translation `D*/π`, commune à tous les points.

### §10 (l. 387) — formule explicite, amplitude, `V ⟹ T log(p_min(z*)/p_min(z)) < π`
1. `zeroTerm_im_eq_sin_towerPosition`, `zeroTerm_real_iff_ray`, `zeroTerm_norm`, `mirror_amplitude_exponent_dominates` :
   tous énoncés pour `q` réel (`0 < q`, resp. `1 ≤ q`).
2. Amplitude : radial `q^β`, dépend de `q` ; position : radial `D/π`, ne dépend pas de `q`.
3. Rien de faux, sauf que `zeroTerm_real_iff_ray` contredit §4/§5 (infinité de contacts).

### §11 (l. 404) — « conditions d'anneau sur le terme du miroir aux deux premiers p_min(z), Occ(z*) »
Mêmes conditions pour deux réels quelconques ; la « remarque non compilée » (largeur π/T contre `log(p_{n+2}/p_{n+1})`) est
une comparaison de hauteur seule, aveugle à β. Reformulation : « conditions de cellule de deux points, partie radiale `D*/π` ».

### §11 quater (l. 560–632) — rigidité énergétique à deux raccords ; « ce qui manque : une relation entre position radiale et la grandeur des premiers q₁ = Occ(l), q₂ = p_min(l) »
1. `energy_balance_two_primes_false` (`HorizontalExclusion.lean:277`) est énoncé pour `q₁ < q₂` **réels** (`0 < q₁`).
   Calcul : `R(q) = q^{Δβ}·‖ρ_e‖/‖ρ_l‖ = 1` a une seule solution `q* = (‖ρ_l‖/‖ρ_e‖)^{1/Δβ}`.
   Même hauteur : `log q* = log(‖ρ_l‖/‖ρ_e‖)/Δβ = (β_e + β_l)/(2T²) + O(T⁻⁴)`, `q* ≈ 1 + (β_e+β_l)/(2T²)`
   (T₁, (0,4 ; 0,6) : `q* = 1,0025`). Pour tout `q ≥ 2` on a `R(q) > 1` (`sameHeight_amplitude_inverts_at_primes`, réel `q ≥ 2`).
2. Radial `q^{Δβ}` dépend de `q`, mais le signe de `log R(q)` est constant sur `q > q*`, et `q* < 2` : aucun premier n'est spécial.
3. **Diagnostic faux** (l. 626) : les deux égalités ne dépendent d'aucune « grandeur numérique des premiers » ; elles échouent
   en tout `q ≥ 2` dès que `β_e ≠ β_l` à hauteur égale.
4. `‖q^{ρ_e}/ρ_e‖ = ‖q^{ρ_l}/ρ_l‖` en deux réels distincts `⟺ β_e = β_l ∧ ‖ρ_e‖ = ‖ρ_l‖` ; à hauteur égale, `β_e < β_l ⟹ R(q) > 1 ∀ q ≥ 2`.
   `J(p) = ΔT·rPrimeGapLogRatio` : avec des réels, `ΔT·log(q''/q')`, identité de hauteur, aveugle à β.

### §11 quinquies (l. 643, 653) — catalogue
Reprendre §4/§5 (grille infinie) et la ligne RACCORD (`R(q) = q^{δ}‖ρ_e‖/‖ρ_l‖` pour tout réel `q`).

### §11 sexies (l. 660–683) — profondeur d'insertion
Aucun point. **Collision de nom** : `D_ins(z) = (φ − φ*)/π = (D(z*) − D(z))/π ≈ (1 − 2β)/(πT)` (cohérent avec R4) n'est pas le
`D` de §11 octovicies. R3 « uniforme en k » = translation rigide, conforme à `tower_offset_rigid`.

### §11 septies (l. 685–757) — raccord, transport, cahier des charges
1. `M` sert de point d'évaluation : cellules `k_e(M)`, `k_l(M)` (tout réel), encadrement `E(C⁻) < E(M) ≤ E(C⁺)`
   (`pivotCell_amplitude_brackets`, réel `q > 0`), `R(q)` (`energyRatio_eq`, réel `q > 0`).
2. Transport : radial `M^{Δβ}` dépend de `q` ; orientation : vertical `R(q) < 1 ∀ q > 0` (`amplitude_lt_of_height_lt`) ;
   horizontal `R(q) > 1 ∀ q ≥ 2`.
3. l. 751 « une relation Λ(p) portant sur (k_e, k_l, M) et la phase » : le candidat `u_l − u_e = (φ_e − φ_l)/π − Δk` est la
   translation rigide, indépendante de `M` sauf `Δk ∈ {0,1}` (fonction de la marge) ; `Λ(p)` homonyme du poids de von Mangoldt.
4. `R(q) = q^{β_l−β_e}‖ρ_e‖/‖ρ_l‖, q > 0` ; « Or(p) au point M » = « Or(p) en tout q ≥ 2 ».

### §11 octies / nonies (l. 759–841) — détecteur, cas diagonal, monde témoin, charge de fibre
1. Cas diagonal : `amplitude_le_of_radial_ge` (`RaccordDetector.lean:72`) pour tout réel `q ≥ 2`. Calcul `q*` diagonal parti de
   la ligne (T₁→T₂, β 0,5→0,4) : `q* = 0,019 < 1`, donc `R(q) < 1` pour tout `q > 1`.
   « Transport horizontal `M^{2δ}` = rapport des poids `M^δ/M^{−δ}` » (l. 818) : vrai pour tout `q`.
2. Charge `(M₂²/(M₁M₃))^δ` (`fibre_transport_product_off`, réels) : radial dépend des trois points ; neutralité ⟺ `δ = 0`
   dès que `M₂² ≠ M₁M₃` ; c'est le **seul** endroit où une propriété des premiers sert (`prime_sq_ne_mul`, factorialité :
   exclut les triplets géométriques). Le signe dépend des écarts (`sq_sub_mul_eq_gaps`) : propriété des points, pas de β.
3. Rien de faux ; E134 `‖χ_n‖ = p_n^{−(β−1/2)}` vaut pour tout `q`.
4. « Neutralité de la charge : `(q₂²/(q₁q₃))^δ = 1 ⟺ δ = 0` pour tout triplet non géométrique ; les premiers distincts en sont un. »

### §11 decies (l. 843–906) — pas `s(z) = (Occ/p_min)^{β−1/2}`, transport cumulé
1. `u^{β−1/2} = 1 ⟺ β = 1/2` pour tout réel `u ∈ ]0,1[` ; transport cumulé : identité pour tous réels `M_k`.
2. Radial `u^{β−1/2}` dépend du rapport, nullité non.
4. « `s_u(z) = u^{β−1/2}`, `u ≠ 1` quelconque ».
(ΔR(a,b), reste, Λ : rôle arithmétique réel des premiers — poids `Λ` — hors Tour ; non concerné.)

### §11 quaterdecies, quindecies, octodecies (l. 1036–1118, 1221–1274)
Déjà sans point (pas, translation `c`, `cellule_w(q) ∈ {cellule_z(q), +1}` pour tout `q`, `contact_k = c₀·r`). Conformes.
Charge de la cellule `a → e → l → b` : comme §11 nonies.

### §11 quinvicies (l. 1441–1469) — registre `Π(l) − Π(e) = ΔT log M − Δφ + T_e log(p_{n+1}/p_n)`
1. Avec `q` (point de sortie) et `q'` (point d'entrée) réels quelconques :
   `π(θ_l(q') − θ_e(q)) = (T_l − T_e) log q' − (φ_l − φ_e) + T_e log(q'/q)` — identité pour tous `q, q' > 0`.
2. Radial : `−(φ_l − φ_e) = −Δφ₀ + (D_l − D_e)`, indépendant de `q, q'` ; `ΔT log q'` (hauteur) et `T_e log(q'/q)`
   (« grammaire ») sont aveugles à β. Le choix `q = Occ(e)`, `q' = M` ne fait que nommer les deux termes aveugles.
3. Rien de faux ; « Π(l) n'est fixé par aucun énoncé » se lit « `D_l` n'est fixé par aucun énoncé ».
4. `X(e,l) − H(e,l) = D_l − D_e` (pour tout couple de points) ; alternance `p_{n+2} ≥ p_n + 6` : propriété de la grammaire,
   aucune part radiale.

### §11 sexvicies (l. 1479) — `(Occ(l)/p_min(l))^{β'−1/2} = 1`, `M^{β'−1/2} = 1`
Vrai pour tout réel `≠ 1` à la place ; reformuler `q^{β'−1/2} = 1, q ≠ 1`.

### §11 octovicies (l. 1501–1517) — résidu `D`
Déjà indépendant de `q` (`changeResidue_eq_position_sub`) : conforme. Ajouter le développement (a) ci-dessous.

### §11 novovicies (l. 1519–1535) — la flèche
1. `entry_arrow_point_irrelevant` : la flèche en `M` équivaut à la flèche en tout point `f(l)` choisi par membre.
2. `θ_l(q) − θ^ligne(q) = D_l/π` pour tout `q`.
3. l. 1535 « aucune relation compilée ne lie θ_l(M) à θ_e(M), T_e, n, Λ(M) » : la mention de `M` et `Λ(M)` est sans objet.
4. « Flèche : `D_l = 0` (la Tour d'arrivée n'est pas translatée) ; `θ_l(q) = θ^ligne_{T_l}(q) + D_l/π` pour tout q ».
   Forme Euler (absente du maître, `EntryPositionArrow.lean`) : `‖q^{−ρ_l}‖ = q^{−β_l}` pour tout réel `q > 0`
   (`local_euler_term_norm` est énoncé en ℕ mais la preuve est `Complex.norm_natCast_cpow_of_pos`, valable pour réels) ;
   flèche `⟺ q^{−β_l} = q^{−1/2}` pour un `q ≠ 1` quelconque. Le facteur `1 − q^{−s} ≠ 0` (Re s > 0) vaut pour tout réel `q > 1`.

### §12 (l. 1544) — bloc RÉFUTÉ : « multiplicité des contacts ; type infini d'états »
**Contredit par le code** : la multiplicité (infinie) des contacts est compilée (`zeroTerm_real_iff_ray`,
`towerMotion_incidence_strictOrder`, `every_prime_in_every_tower`). À reformuler : « réfuté : un état propre par contact ;
compilé : une grille infinie de contacts, un état (paire) par point d'évaluation ».

## 2. Calculs demandés

### (a) Développement de `D`
`arctan x = π/2 − 1/x + 1/(3x³) − …` (x > 0). Avec `x = 2T` et `x = T/β` :
`D = (−1/(2T) + 1/(24T³)) − (−β/T + β³/(3T³)) + O(T⁻⁵) = (β − 1/2)/T + (1/8 − β³)/(3T³) + O(T⁻⁵)`,
soit `D = ((β − 1/2)/T)·[1 − (1/4 + β/2 + β²)/(3T²)] + O(T⁻⁵)`.
Vérifié : erreur relative du premier ordre `1,0·10⁻³` (T₁, β 0,4), `6,9·10⁻⁷` (T₃₀₀) ; avec le terme `T⁻³` : `1,1·10⁻⁶` (T₁),
`10⁻¹²` (T₃₀₀). Valeurs : T₁ : D = −7,068·10⁻³ (β 0,4), −2,121·10⁻² (β 0,2) ; T₃₀₀ = 541,847 : −1,846·10⁻⁴, −5,537·10⁻⁴.
Fenêtre compilée `−1/(2T) < D < 1/T` = image de `β ∈ ]0,1[` au premier ordre. Translation en cellules : `D/π ≈ (β−1/2)/(πT)`.

### (b) Fraction de premiers qui changent de cellule
Si `{θ^ligne_T(p)}` est équirépartie mod 1, un décalage `D/π` (|D/π| < 1) change la cellule de `p` ssi sa partie
fractionnaire est à moins de `|D|/π` du bord (côté `−` si D < 0) : fraction attendue `|D|/π`, nombre attendu `N·|D|/π`.
Variante pondérée par la densité (bords `C_k` géométriques) : `Σ_k C_k·(|D|/T)/log C_k` ; mêmes valeurs à 2 % près.

| hauteur | β | D/π | prédit N|D|/π | prédit densité | σ (Poisson) | E148 (recalculé) |
|---|---|---|---|---|---|---|
| T₁ = 14,135 | 0,4 | −0,002250 | 40,5 | 41,1 | 6,4 | 35 |
| T₁ | 0,2 | −0,006752 | 121,4 | 123,3 | 11,0 | 115 |
| T₁₀ = 49,774 | 0,4 | −0,000639 | 11,5 | 11,3 | 3,4 | 15 |
| T₁₀ | 0,2 | −0,001918 | 34,5 | 33,8 | 5,9 | 35 |
| T₁₀₀ = 236,524 | 0,4 | −0,000135 | 2,4 | 2,4 | 1,6 | 2 |
| T₁₀₀ | 0,2 | −0,000404 | 7,3 | 7,3 | 2,7 | 10 |
| T₃₀₀ = 541,847 | 0,4 | −0,000059 | 1,1 | 1,1 | 1,0 | 3 |
| T₃₀₀ | 0,2 | −0,000176 | 3,2 | 3,2 | 1,8 | 7 |

N = 17 984. Chiffres E148 retrouvés exactement en recalculant. Écarts ≤ 1σ à T₁ et T₁₀₀, ≈ 1,2σ à T₁₀ (β 0,4), ≈ 2σ à T₃₀₀
(petits effectifs ; les ensembles β 0,4 ⊂ β 0,2 ne sont pas indépendants). Totaux sur les quatre hauteurs : prédit 55,5 / 166,4,
observé 55 / 167. Conclusion : la loi `fraction ≈ |D|/π ≈ |β − 1/2|/(πT)` décrit E148 ; rien n'y est propre aux premiers.

### (c) Un seul premier peut-il lire le paramètre de translation ?
- La cellule d'un point `q` ne change, pour **toute** β ∈ ]0,1[, que si `{θ^ligne(q)} ∈ ]0, 1/(2πT)] ∪ ]1 − 1/(πT), 1]`
  (`entry_cell_eq_line_cell_of_margin`) : probabilité `3/(2πT)` ≤ 3,4 % à T₁, 0,09 % à T₃₀₀, → 0.
- Même dans la marge, le numéro de cellule est un bit : il lit une inégalité de seuil `D/π ≶ −{θ^ligne(q)}`, jamais la valeur.
- **Premier partagé réel, 300 transitions** : `M = Occ(l) = p_{n(l)}` est hors marge sur **300/300** (plus petite marge = 3,19 fois
  la demi-largeur de fenêtre) ; pour β = 0,4 et 0,2, la cellule de `M` change sur 0/300 (attendu 0,05 et 0,15). Donc aucune
  entrée possible de la cellule de M ne peut lire une arrivée hors ligne sur ces 300 transitions, quelle que soit β.
- Compteur au dernier rayon (`⌊C⁺⌋`, cellule de `p_min`) : lisible pour une β quelconque sur **2/300** seulement.
- Échelle : partie de hauteur du déplacement de `M` d'une Tour à l'autre `(ΔT log M − Δφ₀)/π` contre la translation radiale
  maximale `1/(2πT_l)` : rapport médian **6 100**, minimum 318 (299 passages).
Réponse : oui, le paramètre est trop petit — `|D/π| < 1/(πT)` — pour qu'une donnée entière d'un seul premier le lise en général ;
il n'est lisible que collectivement (fraction `|D|/π` des premiers) ou par une quantité réelle (position, amplitude).

### (d) Régime : contraction + translation
Chaque Tour = Tour de ligne de sa hauteur translatée : `θ_z(q) = θ^ligne_{T_z}(q) + D_z/π`. Sur `e → l` :
- **contraction de pas** `π/T_e → π/T_l`, facteur `T_e/T_l` (positions dilatées de `λ = T_l/T_e`), part déterminée par la
  hauteur (`Tour de ligne → Tour de ligne`) ;
- **translation radiale** `(D_l − D_e)/π` cellules (= `−(D_l − D_e)/T` en échelle log ; facteur de contacts
  `r_l/r_e = e^{−(D_l−D_e)/T}` à hauteur égale).
(Écrite comme application affine `θ_l = λ θ_e + c`, la part radiale de `c` est `(D_l − λD_e)/π` ; elle coïncide avec
`D_l/π` depuis la ligne, et a le même signe dans tous les cas ci-dessous.)
Signe de `D` = signe de `β − 1/2` ; compilé : vertical `⟹ β_l ≤ 1/2 ≤ β_e`, donc `D_l ≤ 0 ≤ D_e` ; horizontal `⟹ β_e < β_l`.

| régime | contraction `T_e/T_l` | translation `(D_l − D_e)/π` |
|---|---|---|
| vertical pur | `< 1` | `= 0` (D_e = D_l = 0) |
| diagonal | `< 1` | `< 0` strictement ; depuis la ligne `= D_l/π ∈ ]−1/(2πT_l), 0[` |
| horizontal | `= 1` | `> 0` strictement (translation rigide pure, `0 < c < 1`) |
| impossible | `= 1` avec translation `≤ 0` ; `< 1` avec translation `> 0` | |

Changement de régime V→H en `m` : translation `≤ 0` (avec contraction) puis translation `> 0` (sans contraction), `D_m < 0`.
La flèche (conservation depuis la ligne) = « pas de translation à l'arrivée d'une contraction » : `D_l = 0`.

## 3. Sections du maître à corriger (synthèse)

| § | lignes | correction |
|---|---|---|
| §4 | 58 | « exactement deux contacts » → grille infinie (`zeroTerm_real_iff_ray`, `towerMotion_incidence_strictOrder`) |
| §5.a | 93–97 | « deux contacts », « unique cellule I = [C⁻,C⁺] » → une cellule par réel ; demi-ouvert |
| §5.c | 117–142 | pivot = point d'évaluation ; `k(q)` lit `D` hors marge jamais ; cible constatée 2/300 sensible |
| §5.e | 157 | « unique mouvement à exactement deux contacts » → `z ↔ (T, D)` |
| §5.f | 182 | 300/300 de contenance automatique |
| §6 | 196–203 | « rigidifie zéro → premier » → étiquette de rang (`occurrence_is_rank_label`) |
| §8–§9 | 282–285, 310, 338–345 | V ⟺ ¬L pour tous réels, toute β ; l. 345 faux (c'est A ∧ ¬A sur une grille) |
| §11 | 404 | conditions de cellule de deux points, radial `D*/π` |
| §11 quater | 596–626 | « grandeur numérique des premiers » sans objet : `q* ≈ 1 + (β_e+β_l)/(2T²) < 2` |
| §11 quinquies | 640–653 | catalogue : grille infinie, `R(q)` pour tout q |
| §11 sexies | 671 | collision de nom `D_ins` / `D` |
| §11 septies | 709–751 | M point d'évaluation ; candidat `u` = translation rigide ; `Λ(p)` homonyme |
| §11 nonies | 812–839 | détecteur ∀ q ≥ 2 ; charge : seule utilisation d'une propriété des premiers (non-géométricité) |
| §11 quinvicies | 1445–1469 | registre ∀ (q, q') ; radial = `D_l − D_e` |
| §11 novovicies | 1531–1535 | flèche ∀ q (`entry_arrow_point_irrelevant`) ; ajouter forme Euler en q réel |
| §12 | 1544 | RÉFUTÉ « multiplicité des contacts » contredit le code |
