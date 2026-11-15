# RHV6 — MAÎTRE MATHÉMATIQUE

Version purgée du 2026-10-02. Même numérotation que le maître sémantique ; chaque section donne les formules
exactes. Statuts : **[C]** compilé (avec les hypothèses que l'énoncé du théorème déclare, le cas échéant) ;
**[⟺RH]** équivalence compilée avec l'hypothèse de
Riemann (caractérisation, pas théorème) ; **[N]** numérique (zéros publiés d'Odlyzko, jamais une preuve) ;
**[ND]** non dérivé ; **[NC]** non compilé. Les noms Lean et l'inventaire des fichiers sont dans le maître
Lean. L'historique est dans le journal git. Aucun terme de type `RiemannHypothesis` ne compile à ce jour ;
la démonstration de l'auteur, son statut, l'erreur de référence du build principal et le verrou unique sont en
§12 ; la section §14 donne le bloc de livraison.

## 1. Autorité, périmètre et méthode

```text
Cible           : terme t : RiemannHypothesis, axiomes ⊆ {propext, Classical.choice, Quot.sound},
                  aucun sorry, aucun admit, aucun axiome ajouté, aucune hypothèse non déchargée.
Hiérarchie      : code compilé RHV6Fresh (et sa base rhv3_lean) > port zeta23 > maîtres.
Dépendances     : RHV6Fresh → rhv3_lean → Mathlib (rhv2_fresh/.lake/packages/mathlib, même révision).
                  Aucune autre base (RHV5, rhv5_lean, rhv2, rhv4, rh_gap_criterion) n'est importée ;
                  leurs théorèmes sont des précédents historiques sans autorité. .lake/ n'est jamais versionné.
Caractérisation : RH ⟺ aucun zéro non trivial de partie réelle β < 1/2                      [⟺RH]
Prémisse unique : PNoRegimeChange (§11)                                                     [⟺RH]
```

Vocabulaire et méthode : ceux du maître sémantique §1 (caractérise ≠ décide, certificat ≠ déclencheur,
détecteur par existence ≠ générateur ; paquet entier à chaque livraison ; partir de l'état engagé ; toute loi
candidate fausse dans les mondes témoins §10).

Règles de travail en vigueur : tout se fait dans le build principal (`lake build RHV6Fresh`, tous les théorèmes
dans le scope) ; aucune sonde, aucun essai à part, aucun fichier Lean hors `RHV6Fresh/` ; après chaque
compilation, commit et push sur `main` même si le build est rouge, l'erreur du build principal étant l'erreur de
référence ; aucun `sorry`, `admit`, nouvel axiome ; seule `def P…` : `PNoRegimeChange` ; le verrou est la
traduction du but unique du compilateur, ni choisi ni reformulé, aucun verrou n'est ajouté ; sujet fermé :
l'enroulement compilé des Tours à l'infini (§4), ni rouvert ni contesté ; vocabulaire : « caractérise »,
« certificat » ; jamais « anti-compensation » comme flèche manquante, jamais « moitié » pour la symétrie miroir
(un zéro hors ligne vient en carré, §8), jamais « sans hypothèse » ou « sans prémisse » pour un théorème qui a
des hypothèses, jamais une difficulté non vérifiée ; pistes réfutées à ne pas reproposer : croissance des écarts
de premiers contre la plage de phase, écarts de hauteur croissants (§13).

## 2. Domaine

```text
z = β + iT,   0 < β < 1,   ζ(z) = 0 ;   membre : T > 0.
Identité             : ρ(z) = ρ(w) ⇒ z = w.
Clé d'ordre          : κ(z) = (T(z), β(z)), ordre lexicographique ≺.
Ordre z ≺ w          : T(z) < T(w) ∨ (T(z) = T(w) ∧ β(z) < β(w)).
Consécutivité z ▷ w  : z ≺ w ∧ ¬ ∃ v, z ≺ v ≺ w      (passage e → l).
Fibre                : F(T₀) = { z : T(z) = T₀ },  finie.
Verrou de fibre      : T(z) = T(w) ∧ z ≺ v ≺ w ⇒ T(v) = T(z).
Index (rang)         : n(z) = #{ w membre : w ≺ z }.
Avance               : a ▷ b ⇒ n(b) = n(a) + 1                                              [C]
```

Hors ligne : `β ≠ 1/2`, miroir `z* = 1 − β + iT`, `z* ≠ z`, `T* = T`, `β* = 1 − β`. Aucun zéro hors ligne
n'est calculé ; les expériences qui placent `β ≠ 1/2` à une hauteur publiée sont des mondes de contrôle.

**Plan des zéros** (distinct du plan des Tours, §4 : un point de ce plan est un zéro, pas une courbe) :

```text
zéro ρ = β + iT ↔ point (β, T) ;  hauteur T = Im ρ, partie réelle β = Re ρ ;  ligne critique {β = 1/2}
miroir        z* = 1 − ρ̄ = (1 − β) + iT :  T* = T,  β* = 1 − β ;  réflexion β ↦ 1 − β,
              lieu fixe = la ligne critique                                    [C]  (mirrorMember_ordinate, mirrorMember_radial)
miroir annulé  z* = z ⟺ β = 1/2                                                [C]  (mirror_annulled_iff_onLine)
milieu de la paire  m(z) := (ρ + ρ*)/2 = 1/2 + iT, pour tout β                 [C]  (mirror_pair_center)
              z et z* de même hauteur ont le même milieu ; T ≠ T' ⟹ m ≠ m' (parties imaginaires T, T')
zéro au milieu de sa paire  ρ = m(z) ⟺ β = 1/2                                 [C]  (zero_at_center_iff_onLine)
```

## 3. Les trois objets

```text
Z  = zéros non triviaux, ordonnés par ≺
T_z = Tour propre de z, fonction de (β, T) seule
𝓟  = (p_n)_{n ≥ 0}, p_0 = 2 ;  π(x) = #{p ≤ x} ;  g_n = p_{n+1} − p_n ;  p_{π(x)−1} = dernier premier ≤ x
```

## 4. La Tour propre

**Terme et Tour.** `ρ = β + iT`, `zeroTerm z q = q^ρ/ρ` pour `q > 0`. La Tour est la courbe `q ↦ q^ρ/ρ`,
`q ∈ (0, ∞)`.

```text
‖ρ‖² = β² + T² ;   ‖q^ρ/ρ‖ = q^β/‖ρ‖                                                        [C]
φ(β,T) = arctan(T/β) ∈ (0, π/2) ;   cos φ = β/‖ρ‖                                          [C]
Im(q^ρ/ρ) = q^β (β sin θ − T cos θ)/‖ρ‖²,   θ = T log q                                    [C]
β sin θ − T cos θ = (β/cos φ)·sin(θ − φ)                                                   [C]
Re(q^ρ/ρ) = q^β cos(θ − φ)/‖ρ‖                                                              [C]
```

**Plan des Tours, Tour brute, Tour normalisée, pôle de rotation.**

```text
Tour brute : x ↦ x^ρ/ρ, x > 0 (trace du terme) ; le zéro la détermine, il n'en est ni le centre ni le point de départ
   x = 1 : 1^ρ/ρ = 1/ρ ;  x = 2 (premier premier) : 2^ρ/ρ                                   [C]  (zeroTerm)
Plan des Tours : ℂ ∋ x^ρ/ρ ; origine 0 = pôle de rotation de TOUTES les Tours, u = log x :
   x^ρ/ρ = e^{uρ}/ρ ;  ‖x^ρ/ρ‖ = e^{βu}/‖ρ‖ ;  arg(x^ρ/ρ) = T u − φ  (mod 2π), φ = arg ρ = arctan(T/β)
Tour normalisée (échelle √x) : Γ_ρ(u) = x^{−1/2}·x^ρ/ρ = e^{u(ρ − 1/2)}/ρ = a·e^{d u}·e^{i(T u − φ)},
   a = 1/‖ρ‖,  d = β − 1/2,  x = e^u                           [C]  (rescaledTower_eq, towerCurve, pointCurve_hasDerivAt)
   Γ_ρ(0) = 1/ρ ;  Γ' = (ρ − 1/2)·Γ :  vitesse angulaire T par unité de log x,  taux radial d = β − 1/2 par unité de log x
   β = 1/2 : ‖Γ‖ = 1/‖ρ‖ constante, cercle de centre 0 ;  β ≠ 1/2 : ‖Γ‖ = a·e^{du}, spirale
symétrie centrale de la Tour normalisée : ∀ u ∃ u', Γ(u') = −Γ(u)  ⟺ d = 0 ⟺ β = 1/2     [C]  (TowerSymmetric,
   towerSymmetric_iff_onLine, tower_central_invariant_iff) ;  plan brut (d = β > 0) : jamais     [C]  (raw_tower_not_centrally_invariant)
tangente : Γ'(u) = (ρ − 1/2)·Γ(u) ;  Re(conj Γ·Γ') = (β − 1/2)·‖Γ‖² ;  tangente ⟂ rayon ⟺ β = 1/2     [C]  (pointCurve_hasDerivAt,
   pointCurve_tangent_radial, pointCurve_tangent_perp_iff)
Tour brute F(u) = e^{ρu}/ρ : F(u + π/T) = −e^{βπ/T}·F(u) ; ON : dilatation e^{π/(2T)} > 1, la Tour ON BRUTE est une spirale     [C]  (zeroTerm_half_turn) ;
   normalisée ON : W(u + π/T) = −W(u), opposition exacte     [C]  (rescaledTower_half_turn_onLine)
demi-tour : Γ(u + π/T) = −e^{(β − 1/2)π/T}·Γ(u) ;  opposition exacte, même rayon ⟺ β = 1/2     [C]  (rescaledTower_half_turn,
   towerCurve_central) ;  les Tours ON sont symétriques : théorème, pas affirmation ;  pour le zéro suivant, l'opposition exacte
   (ou la perpendicularité) de SA Tour est le but ; enroulement autour de la même origine + demi-tour ne suppriment pas le facteur
conjugaison : conj(x^ρ/ρ) = x^ρ̄/ρ̄, la Tour du conjugué                           [C]  (tower_topBottom_symmetric)
   elle n'est pas une invariance de la Tour : conj Γ_{d,a}(u) = e^{d(2u − 2φ/T)}·Γ(2φ/T − u), échange de profondeur d ↦ −d (§12, E161)
```

**Contacts.**

```text
C_k = exp((φ + kπ)/T),  k ∈ ℤ ;   T log C_k = φ + kπ ;   tan(T log C_k) = T/β                [C]
Im(q^ρ/ρ) = 0  ⟺  ∃ k ∈ ℤ, q = C_k                                                         [C]
C_k^ρ/ρ = (−1)^k · C_k^β/‖ρ‖   (réel, signe alterné, |·| croissant comme exp(kπβ/T))       [C]
log C_{k+1} − log C_k = π/T    (pas, fonction de T seul)                                    [C]
abscisse de lecture du contact k : x = C_k (réel > 0 où la Tour coupe l'axe réel) ;
   point atteint : C_k^ρ/ρ = (−1)^k C_k^β/‖ρ‖ ∈ ℝ (distance à l'origine = amplitude au contact) : deux objets distincts  [C]
écart logarithmique entre deux contacts successifs : π/T, fixé par la hauteur, strictement décroissant en T         [C]
```

**Origine canonique.** `C_0 = exp(φ/T)` : `C_{−1} < 1 < C_0`, `1 < C_k ⟺ 0 ≤ k`,
`sin(T log C_k − φ) = 0`, `cos(T log C_k − φ) = (−1)^k`. [C]

**Position, cellule.**

```text
θ_z(q) = (T log q − φ)/π                 (position ; π·θ_z(q) = argument du terme moins kπ)  [C]
θ_z(q₂) − θ_z(q₁) = T log(q₂/q₁)/π                                                          [C]
   (différence de deux positions de lecture dans une même Tour : indépendante de β et de φ ; elle efface le
   décalage commun D/π de θ_z = θ₀_T + D/π sans démontrer qu'il est nul ; ce n'est pas un énoncé général
   « les écarts de premiers sont lus par la hauteur seule dans toute Tour »)                 [C]  (gap_reading_height_only)
k_z(q) = ⌈θ_z(q)⌉ − 1   unique k avec  C_k < q ≤ C_{k+1}                                    [C]
cellule de q : (C_{k_z(q)}, C_{k_z(q)+1}] ; une par réel q > 0, dans toute Tour                [C]
tout premier a sa cellule dans la Tour de tout zéro ; une cellule contient 0, 1 ou plusieurs premiers  [C]
E148 : jusqu'à 3006 premiers par cellule (premiers ≤ 200 000)                               [N]
C_k(β, T) = exp((arctan(T/β) + kπ)/T) ; k ≥ 1, 0 < T < T', β > 0 ⟹ C_k(β, T') < C_k(β, T)      [C]
   (enroulement : (1, C_k(T')] ⊂ (1, C_k(T)) ; à même hauteur C_k(β', T) = C_k(β, T)·e^{Δφ/T}, sans enroulement) [C]
C_k < q ≤ C_{k+1} ⟹ kπ < T log q < (k+1)π + π/2 ;  T log 2 ≥ (k+1)π + π/2 ⟹ cellule k sans réel ≥ 2  [C]
T log q ≥ kπ + π/2 ⟹ C_k < q (tout réel traverse tout indice fixé) ; θ_{(β,T)}(C_k(β',T')) = (T(φ'+kπ)/T' − φ)/π [C]
enroulement à l'infini (sujet fermé) : WindingNestedAtInfinity(e, l) :⟺ ∃ K ∈ ℤ, ∀ k ≥ K, C_k(l) < C_k(e) ;
   le seuil K est propre à chaque comparaison (e, l) ;  e ≺ l ⟹ WindingNestedAtInfinity(e, l), toutes positions
   radiales (windingNestedAtInfinity_of_precedes) ;  TowerRoomAtInfinity(z) : contacts de z encadrés entre ceux de toute
   Tour qui précède et de toute Tour qui suit (towerRoomAtInfinity) ;  vrai pour toute assignation radiale :
   il n'affirme pas à lui seul la conservation radiale                                                      [C]
E151, k = 4 : cellule non vide ⟹ T < 24,93 ; parmi tous les zéros, seuls T_1 ({3}) et T_2 ({2})  [C + N]
E151 : avance d'un réel q par passage ΔT·log q/π ; une cellule par passage en moyenne ⟺ q ≈ √(T/2π)
   (θ'(T) = ½ log(T/2π)) ; premiers séparés par la grille de T_n jusqu'à 17 (n = 1), 641 (n = 300)  [N]
E151, k = n : nπ ≈ θ(T_n) + 3π/2 ⟹ C_n ≈ √(T_n/2πe)·exp((φ + 11π/8)/T_n) (rapport 0,982–1,018)  [N]
   cellule non vide 9/300 ({2} n = 10–11, {3} n = 46–48, {5} n = 209–212), Occ 0/300, p_min 0/300 [N]
   listes identiques à β = 0,4 et 0,2 (A et B, 300/300) ; décalage relatif des contacts ≤ 1,5·10⁻³ [N]
```

**Tour de ligne et forme normale.**

```text
φ₀(T) = arctan(T/(1/2)) = arctan 2T ;   c₀(T,k) = exp((φ₀(T) + kπ)/T) ;   θ₀_T(q) = (T log q − φ₀(T))/π
r(z) = exp((φ − φ₀(T))/T)   (facteur radial)                                               [C]
C_k(z) = c₀(T,k) · r(z)   ∀ k                                                              [C]
r = 1 ⟺ β = 1/2 ;  r > 1 ⟺ β < 1/2 ;  r < 1 ⟺ β > 1/2                                     [C]
facteur radial commun : à hauteur T fixée, toutes les abscisses de contact de z sont celles de la grille de ligne
   multipliées par le même r(z) (indépendant de k) ;  r(z) = 1 ⟺ β = 1/2                   [C]  (radialFactor_eq_one_iff)
translation rigide (définition, terme du code) : ∃ c > 0, ∀ k, C_k(w) = c·C_k(z), soit log C_k(w) − log C_k(z) = log c
   indépendant de k : multiplication uniforme de toutes les abscisses de contact, décalage uniforme en
   coordonnée logarithmique ; ce n'est pas un déplacement de la courbe                          [déf.]
D(z) = arctan 2T − arctan(T/β) = φ₀ − φ = −T log r   (résidu de changement)                 [C]
θ_z(q) = θ₀_T(q) + D/π   ∀ q > 0                                                           [C]
−1/(2T) < D < 1/T  (0 < β < 1, T > 0) ;   donc |D/π| < 1/(πT)                               [C]
D = 0 ⟺ β = 1/2 ;  D < 0 ⟺ β < 1/2 ;  D > 0 ⟺ β > 1/2                                    [C]
D = (β − 1/2)/T + (1/8 − β³)/(3T³) + O(T⁻⁵) ;  E149 : D·T/(β − 1/2) ∈ [0,9988 ; 1]          [N]
```

**Deux signatures d'une variation de β à T fixé.**

```text
phase     : θ_{β₂}(q) − θ_{β₁}(q) = (φ(β₁,T) − φ(β₂,T))/π, indépendant de q                 [C]
amplitude : ‖q^{ρ₂}/ρ₂‖/‖q^{ρ₁}/ρ₁‖ = q^{β₂−β₁}·‖ρ₁‖/‖ρ₂‖ ;
            (∀ q > 0, rapport(q) = rapport(1)) ⟺ β₂ = β₁                                    [C]
Euler     : ‖n^{−ρ}‖ = n^{−β} ;  ‖n^{−ρ}‖ = n^{−1/2} ⟺ β = 1/2, pour tout entier n > 1          [C]
```

**Inversion.** Pour toute paire de contacts consécutifs :

```text
T = π / log(C_{k+1}/C_k) ;   β = T / tan(T log C_k)                                         [C]
```

Deux zéros distincts n'ont jamais deux contacts consécutifs communs.

## 5. L'état propre et la règle du pivot

```text
Occ(z)   = p_{n(z)}           (étiquette de rang, injective)                                 [C]
p_min(z) = p_{n(z)+1}         (minimum attendu, injectif sur les membres)                    [C]
pivot    = p_min(z) (orientation croissante ; §8 pour la seconde Tour)
k        = ⌈θ_z(p_min(z))⌉ − 1 ;  C_k < p_min(z) ≤ C_{k+1} ;  plus petit k qui l'atteint      [C]
état propre : (C⁻, C⁺) = (C_k, C_{k+1}) ;  nombre d'étages m = T(log C⁺ − log C⁻)/π = 1      [C]
cible constatée q(z) = max{p premier : p ≤ C⁺} ;  p_min(z) ≤ q(z)                           [C]
C_0 < p_min ⟺ 0 ≤ k                                                                        [C]
```

La coordonnée `k` et `m` sont des lectures, jamais des entrées. Aucune formule `k = F(β, T)` n'est cherchée.

**Les quinze zéros historiques** (β = 1/2) **[N]** :

```text
Zéro  T                 k   pivot  C⁻                 C⁺
Z1    14.134725141735    4     3     2.711958785357     3.386956682246
Z2    21.022039638772   10     5     4.797132274455     5.570367919385
Z3    25.010857580146   14     7     6.175152195952     7.001627926974
Z4    30.424876125860   22    11    10.203703046818    11.313628568043
Z5    32.935061587739   26    13    12.519750118410    13.772789780756
Z6    37.586178158826   33    17    16.439726768932    17.872880198571
Z7    40.918719012147   37    19    17.793212164201    19.213121613095
Z8    43.327073280915   42    23    21.787932306575    23.426433450072
Z9    48.005150881167   50    29    27.238888230768    29.081100356062
Z10   49.773832477672   53    31    29.270397379051    31.177417414409
Z11   52.970321477714   60    37    36.161272714734    38.370820037842
Z12   56.446247697063   66    41    40.487406789284    42.804675692522
Z13   59.347044002602   70    43    41.755998180273    44.025942761549
Z14   60.831778524610   74    47    46.868149741354    49.352196508088
Z15   65.112544048082   81    53    51.016414041189    53.538235430116
```

Sur les 300 premiers zéros publiés : cellule contenant `p_min` 300/300 ; 15/15 contacts historiques
(`k = k_hist`, `m = 1`) ; `Occ` et `p_min` atteints 300/300 ; `q(z) > p_min(z)` sur 95/300 ; au moins deux
premiers dans la cellule sur 168/300. **[N]**

## 6. Le comptage et la grammaire première reconstruite

```text
p atteint par la Tour w   :⟺  p ≤ C⁺(w) ;   Occ(w) atteint ⟺ n(w) < π(C⁺(w))
rang compté au contact C  :   π(⌊C⌋) = fonction de comptage de Tchebychev/Von Mangoldt en ⌊C⌋,
                              dans les deux orientations                                     [C]
reconstruction (M^Z = M)  :   ψ_Z canal issu des zéros ; w(m) = ψ_Z(m) − ψ_Z(m−1) ;
                              m premier ⟺ m ≥ 2 ∧ w(m) = log m ;  E_n^Z = E_n ;  H_n^Z = H_n ;
                              F(H_n^Z) = F(H_n) pour toute fonction F de l'histoire          [C]
```

**Noyau rigide** [C] : unicité de la cellule et de la paire de contacts pour tout β ; chaîne
`n(b) = n(a) + 1`, `Occ(b) = p_min(a)`, `p_min(a) < p_min(b)` ; identité du rang compté et de la fonction de
comptage. Ce noyau ne lit pas β.

## 7. La progression et la grammaire première

**Passage** `e → l` (consécutifs) :

```text
n_l = n_e + 1 ;  T_e ≤ T_l ;  Occ(e) < Occ(l) = p_min(e) =: M ;  p_min(l) = p_{n_e+2} ;  p_min(e) < p_min(l)   [C]
```

`M` est le premier partagé. La somme de la formule explicite est invariante par toute permutation des zéros et
fermée par conjugaison (`T` et `−T`) : le sens de progression vient de l'ordre `≺`. [C]

**Deux grammaires.** Par rang : `Occ(z) = p_{n(z)}` [C]. Par hauteurs : `h(z)` = nombre de hauteurs
distinctes au-dessous de `T(z)` ; hors ligne, `z` et `z*` ont le même premier par hauteurs et deux occurrences
par rang [C] ; `n ≡ h` ⟺ toute fibre est un singleton ⟺ RH [⟺RH]. Hors ligne, il existe un passage avec
`n + 1`, occurrence qui avance et `T_e = T_l` [C].

**Rigidité modulo six.**

```text
GoodMod6(n) :⟺ n mod 6 ∈ {1, 5} ;   état(n) = B si n ≡ 1, A si n ≡ 5
p premier, p > 3 ⟹ GoodMod6(p)                                                              [C]
gapClass6(m,n) = (n − m) mod 6 ∈ {0, 2, 4}   (GoodMod6(m), GoodMod6(n), m ≤ n)               [C]
  = 0 ⟺ état(m) = état(n) ;  = 2 ⟺ A → B ;  = 4 ⟺ B → A                                     [C]
m ≤ n ≤ r, gapClass6(m,n) ≠ 0 ≠ gapClass6(n,r) ⟹ gapClass6(m,n) ≠ gapClass6(n,r)           [C]
même énoncé pour trois premiers > 3, et pour les p_min de trois membres consécutifs           [C]
p < q < r premiers > 3 ⟹ r ≥ p + 6 ;  donc p_{n+2} ≥ p_n + 6  (p_n > 3)                       [C]
g = 6a + r, a = ⌊g/6⌋ (magnitude), r = g mod 6 (classe) ; transition τ ∈ {AA, AB, BA, BB}            [déf.]
p ≤ q ≤ r, gapClass6(p,q) ≠ 0 ≠ gapClass6(q,r) ⟹ r − p = 6(a_{pq} + a_{qr} + 1)                   [C]
GoodMod6(p), GoodMod6(r), p ≤ r ⟹ (état(r) = état(p) ⟺ (r − p) mod 6 = 0)                          [C]
s : ℕ → {A, B} :  Σ_{i<m} (1[A→B] − 1[B→A]) = 1[s_m = B] − 1[s_0 = B] ∈ {−1, 0, 1}                  [C]
mot q_0 < … < q_m :  Σ_i (2(½+d) − 2(½−d))·log(q_{i+1}/q_i) = 4d·log(q_m/q_0) ;  ≠ 0 ⟺ d ≠ 0          [C]
deux changements consécutifs :  4d·log(r/p) = 4d·log(1 + 6(a + a' + 1)/p)                             [C]
```

Motifs, familles, méta-pattern : hiérarchie descriptive ; compilé au-delà des états : l'avance exacte de deux
changements, le retour d'état, le verrou des canaux AB/BA et la dette miroir d'un mot (E157). E102–E105 :
alternance vérifiée jusqu'à 2 000 000 de premiers, aveugle à β **[N]** ; E157 : 0 violation sur 378 566 paires
(p ≤ 10⁷), égalité des deux changements exacte partout **[N]**.

**Progression continue.** `ΔΘ_n(z) = T·log(p_{n+1}/p_n) > 0` : accroissement de phase du terme entre deux
premiers consécutifs [C] ; strictement positif mais sans quantum (son minimum décroît, E112) **[N]**.
« Un événement franchit au moins une cellule » est faux sur la ligne : même cellule dans 88/300 cas (E111)
**[N]**.

## 8. Le miroir, les quatre zéros et la seconde Tour

```text
ρ      = (β, T)          le zéro
ρ̄      = (β, −T)         conjugué
1 − ρ̄  = (1 − β, T)      miroir z*
1 − ρ  = (1 − β, −T)     réfléchi fonctionnel = conj(z*)
même multiplicité pour les quatre ;  sur la ligne : ρ̄ = 1 − ρ, 1 − ρ̄ = ρ                     [C]
β < 1/2 ⟹ z ≺ z*,  n(z) < n(z*),  p_min(z) ≤ Occ(z*),  p_min(z) < p_min(z*)                 [C]
z ▷ z* ⟹ n(z*) = n(z) + 1,  Occ(z*) = p_min(z),  p_min(z*) = p_{n(z)+2}                      [C]
```

Carré : `T > 0`, `β ≠ 1/2` ⟹ les quatre points `(β, T)`, `(β, −T)`, `(1 − β, T)`, `(1 − β, −T)` sont deux à deux
distincts (coordonnées) ; la symétrie miroir n'est pas une « moitié » : un zéro hors ligne vient en carré, dont deux
membres de la moitié supérieure des zéros (`T > 0`) : `ρ` et `z*` ; `β = 1/2` : les quatre points se réduisent à deux.

**Les deux plans, sans identification des centres** [C] (`tower_two_symmetries`) :

```text
symétrie centrale de la Tour normalisée de z  ⟺  β = 1/2  ⟺  mirrorMember z = z  ⟺  ρ = m(z) = 1/2 + iT
origine 0 (pôle de rotation, plan des Tours, la même pour toutes les Tours)  ≠  milieu m(z) = 1/2 + iT (plan des zéros)
l'équivalence relie trois propriétés ; elle n'identifie pas l'origine de la courbe et le milieu de la paire ;
deux hauteurs T ≠ T' donnent deux milieux m ≠ m' et une seule origine 0 ; deux membres miroirs de même hauteur
partagent le même milieu ; la Tour normalisée ON est un cercle de centre 0, la spirale OFF n'a pas cette symétrie
```

**Contraintes du miroir** [C] :

```text
φ* = arctan(T/(1 − β)) ;   C_k(z*) = C_k(z)·exp((φ* − φ)/T)   (rapport indépendant de k)
force horizontale δ + δ* = 0 (δ = β − 1/2, δ* = −δ) ;  tension 2δ² = 0 ⟺ β = 1/2
un seul C_k(z*) = C_k(z), ou φ* = φ, ⟹ β = 1/2
profondeur d'insertion D_ins(z) = (φ − φ*)/π ;  |D_ins| < 1/2 ;  D_ins > 0 ⟺ β < 1/2
C_k(z*) = C_k(z)·exp(−π D_ins/T) ;  position relative du contact miroir dans la cellule = 1 − D_ins
(D_ins = 0) XOR (entrelacement strict), pour tout k, uniforme en k
β ≤ 1/2 ⟹ 0 ≤ D_ins ≤ (1 − 2β)/(πT)
‖q^{z*}/z*‖ = q^{1−β}/‖ρ*‖ ;  β < 1/2 ∧ q ≥ 1 ⟹ q^β ≤ q^{1−β} ;  égalité des exposants sur la ligne
```

`D_ins` (miroir contre zéro, même hauteur) est distinct du résidu de changement `D` (§4, zéro contre Tour de
ligne). E123 : entrelacement 2100/2100 **[N]**.

**La seconde Tour** = Tour du réfléchi `1 − ρ = (1 − β, −T)` [C] :

```text
phase φ' = arctan(−T/(1 − β)) = −φ* ;  pas −π/T ;  log-rayons (φ' + jπ)/(−T) = log C*_{−j}
orientation opposée ; β ↦ 1 − β seul ne renverse rien (pas du miroir supérieur +π/T)
pivot propre p_min(z*) ;  k₂ = ⌈(T log p_min(z*) − φ*)/π⌉ − 1
C⁻(z*) = C_{k₂+1}(1 − β, T)  (entrée, en haut) ;  C⁺(z*) = C_{k₂}(1 − β, T)  (dernier rayon, en bas)
anneau = celui de la Tour propre de z* ;  C⁺(z*) < p_min(z*) ≤ C⁻(z*) ;  Occ(z*) ≤ C⁻(z*)
le mouvement réfléchi n'a aucun événement d'arrêt depuis sa propre origine
```

**Lecture de la seconde Tour** [C] :

```text
L : Occ(z*) ≤ C⁺(z*)  ⟺  k₂(Occ(z*)) < k₂(p_min(z*))
π ≤ T·log(p_min(z*)/Occ(z*))  ⟹  L
anneaux du miroir = anneaux du membre décalés de moins d'un demi-anneau
```

Sur les substituts publiés, `L` tient sur 212/300 **[N]**. La vérification `V : C⁺(z*) < p_min(z)`, son
exclusion avec `L` et les deux lois de l'inversion sont retirées du code (§13).

## 9. La formule explicite, le reste et l'identité de chaque membre

```text
q^ρ̄/ρ̄ = conj(q^ρ/ρ) ;  q^ρ/ρ + q^ρ̄/ρ̄ = 2 Re(q^ρ/ρ)                                        [C]
tout membre est un zéro non trivial du canal compilé                                         [C]
ψ(x) reconstruite depuis les zéros pour x ≥ 2 (formule explicite lissée de la base)          [C]
d/dx [x·f(x,ρ)] = x^ρ/ρ,   f(x,s) = x^s/(s(s+1))                                             [C]
```

**Reste arithmétique, sans zéro.**

```text
A(x) = Σ_{n < x} Λ(n)(1 − n/x) − fond(x)
fond(x) = x/2 − ζ'/ζ(0) + (ζ'/ζ(−1))/x + Σ_{n ≥ 1} (termes des zéros triviaux)
Λ(p_n) = log p_n = poids de l'événement de rang n
A(x) = Σ_ρ −m(ρ)·x^ρ/(ρ(ρ+1))   (x > 1)                                                   [C]
R_arith(N) = ψ(N) − ΔB(N) = R_spectral(N) = ΔZ(N)   (N ≥ 2)                                  [C]
```

**Identité de chaque membre** [C] :

```text
∀ x > 0 : −m(ρ)·f(x,ρ) ≠ 0 ;  Z_{≠ρ}(x) ≠ Z(x)
S fini, ∀ x > 1 : Σ_{s∈S} c_s x^s = 0  ⟹  ∀ s, c_s = 0
famille (s_i, a_i), Re s_i ≤ 1, localement finie, Σ‖a_i‖ < ∞ :
  (∀ x > 1, Σ' a_i x^{s_i} = 0) ⟹ ∀ Re z > 1, Σ' a_i/(z − s_i) = 0
                                ⟹ ∀ z ∉ {s_i}, Σ' a_i/(z − s_i) = 0      (prolongement)
                                ⟹ ∀ p, Σ_{s_i = p} a_i = 0                 (lecture du pôle)
représentation (s_i, c_i) du canal (points distincts, Re ≤ 1, s_i ∉ {0, −1}, localement finie,
  Σ‖c_i/(s_i(s_i+1))‖ < ∞, ∀ x > 1 : Σ' c_i f(x, s_i) = Z(x)) :
  ∀ ρ : ∃ i, s_i = ρ ∧ c_i = −m(ρ) ;   s_i non zéro ⟹ c_i = 0 ;   β, T, m de chaque membre retrouvés
  z hors ligne ⟹ ∃ i, c_i ≠ 0 ∧ Re s_i ≠ 1/2
RH ⟺ ∃ représentation, ∀ i, c_i ≠ 0 ⟹ Re s_i = 1/2                                        [⟺RH]
```

**Paquet de hauteur et compensation** [C] (indices `I`, deux branches, `t_x(ρ) = −m(ρ)·f(x,ρ)`) :

```text
E_T = {ρ ∈ I : |Im ρ| = T} ;  Z_S(x) = Σ_{ρ∈S} t_x(ρ) ;  B(x) = x·fond(x) ;  P_S(x) = x·Z_S(x)
R(N) = ψ(N) − ΔB(N) ;  L_S(N) = ΔP_S(N) ;  K_S(N) := R(N) − L_S(N)
Σ_I t_x = Z_S + Z_{Sᶜ}   (x > 1) ;   R(N) = L_S(N) + L_{Sᶜ}(N) ;   K_S(N) = L_{Sᶜ}(N)   (N ≥ 2)
K_S(N) − K_{S'}(N) = L_{S'}(N) − L_S(N)
événement M = N + 1 : R(N+1) − R(N) = Λ(N+1) − (ΔB(N+1) − ΔB(N)) = ΔL_S + ΔL_{Sᶜ}
z hors ligne : z, z* ∈ E_T, z ≠ z*, Z_{E_T} = t(z) + t(z*) + Z_{E_T∖{z,z*}}
```

**Lecture inverse** [C] :

```text
ΔR(a,b) = Σ_{a<n≤b} Λ(n) − (ΔB(b) − ΔB(a)) = R_spectral(b) − R_spectral(a) = L_S(a,b) + L_{Sᶜ}(a,b)
ΔR(a,b) + ΔR(b,c) = ΔR(a,c)
d'un événement au suivant sans puissance intercalée : ΔR_n ≈ log p_{n+1} − g_n (à 0,045 près, E137)  [N]
```

**Marche, demande, réponse collective, diagonale, croisés, dette** [C sauf mention] (E137bis) :

```text
marche pure p < q consécutifs, Λ(n) = 0 sur ]p, q[ :  Σ_{p<n≤q} Λ(n) = log q
ΔR(p, q) = log q − (ΔB(q) − ΔB(p)) = log q − (6a + r) − ((ΔB(q) − ΔB(p)) − (q − p)),  a = ⌊g/6⌋, r = g mod 6
c_ρ(n) = −2 Re[(x_{n+1}^ρ − x_n^ρ)/ρ], x_n = p_n + ½ ;  Σ_ρ c_ρ(n) = ΔR_n  (formule explicite, troncature [N])
D(c) := Σ_i c_i² ;  X(c) := (Σ_i c_i)² − D(c) = Σ_i Σ_{j ≠ i} c_i c_j ;  (Σ c)² = D + X
Σ c = S ⟹ X = S² − D ;  X < 0 ⟺ S² < D ;  ∀ i, c_i ≥ 0 ⟹ X ≥ 0 ;  |ε_i| = 1 ⟹ D(ε c) = D(c)
κ(classe) := Σ S_n² / Σ D_n   (taux de survie ; E κ = 1 pour des signes aléatoires)                  [déf.]
dette d'une paire 1/2 ± δ à la hauteur T :  d_n = Σ c(monde δ) − Σ c(monde ζ) ; excès ∝ (x^δ + x^{−δ})/2 > 1   [N, 10⁻¹⁴]
z hors ligne : ∀ représentation Rep, ∃ i, w_i ≠ 0 ∧ Re s_i ≠ 1/2 ;  θ* ≥ max(β, 1 − β) > 1/2
```

**Budget global de zeta23** [dépôt zeta23, compilé là-bas, hors de ce build] :

```text
N(T,2T) avec multiplicité ; N₀ˢ(T,2T) simples sur la ligne ; N_d(T,2T) distincts
∀ ε > 0, ∃ T₀, ∀ T ≥ T₀ :  (2/3 − ε)·N(T,2T) ≤ N₀ˢ(T,2T) ;  (5/6 − ε)·N(T,2T) ≤ N_d(T,2T)
côté premier hors diagonale :  |Σ_{n≠m} u_n v_m trig(c(y_n − y_m))/(y_n − y_m)| ≤ C·√(Σ u²)·√(Σ v²),  ≪ Σ_{n≤X} Λ(n)²
côté zéros : atome en ligne (multiplicité m_j) ⊕ bloc hors ligne (paire ρ, 1 − ρ̄) ; rang–trace :
    2c·tr(P + Q) − ‖P + Q‖_F² ≥ Σ_j k_c(m_j) + c²·b  ;  c = 2 : k(1) = 3, k(2) = 4, bloc 4  (égalité atteinte : tendue)
densité : proportion sur [T, 2T] ; aveugle à tout ensemble de zéros de proportion nulle
```

**Tout en ligne et écart** [C] :

```text
W = {ρ ∈ I : Re ρ = 1/2} ≃ {T : L(T) = 0}   (L fonction réelle sur la ligne, §10)
R(x) = C_W(x) + E(x),  E(x) = Σ_{ρ ∈ I∖W} t_x(ρ)
v nulle hors de W, Σ|v(ρ)|/|ρ(ρ+1)| < ∞, ∀ x > 1, E(x) = Σ v(ρ) f(x,ρ)  ⟹  v ≡ 0 ∧ RH
∃ z, β_z ≠ 1/2  ⟹  ∃ x > 1, E(x) ≠ 0
RH ⟺ ∀ x > 1, E(x) = 0 ⟺ ∀ x > 1, A(x) = Σ_{T : L(T)=0} −m(1/2+iT) f(x, 1/2+iT)        [⟺RH]
```

**Lecture par la croissance** [C] :

```text
(∀ x > 1, |Σ a_i x^{s_i}| ≤ C x^θ)  ⟹  ∀ p, Re p > θ : Σ_{s_i = p} a_i = 0
(∀ x > 1, |A(x)| ≤ C x^θ)  ⟹  β(ρ) ≤ θ pour tout zéro
RH ⟺ ∃ C, ∀ x > 1, |A(x)| ≤ C x^{1/2}                                                       [⟺RH]
```

Preuve de la croissance : `f(t) = Σ a_i t^{−s_i}` sur `0 < t ≤ 1` ; transformée de Mellin analytique sur
`Re z > θ` ; égale à `Σ a_i/(z − s_i)` sur `Re z > 1` ; identité sur une bande convexe sans exposant ; borne
du résidu quand `τ → 0`. La borne `|A(x)| ≤ C√x` est **[ND]**.

**Hauteur et pente d'un membre** (E150) :

```text
θ_z(y) − θ_z(x) = T·log(y/x)/π ;  log‖y^ρ/ρ‖ − log‖x^ρ/ρ‖ = β·log(y/x)   (x, y > 0)              [C]
‖y^ρ/ρ‖ / ‖x^ρ/ρ‖ = (y/x)^β ;  x^{−1/2}·‖x^ρ/ρ‖ = x^{β−1/2}/‖ρ‖                                 [C]
(∀ x > 0, x^{−1/2}·‖x^ρ/ρ‖ = 1/‖ρ‖) ⟺ β = 1/2                                                   [C]
Im(ρ + d) = T ;  ‖x^{ρ+d}‖ = x^d·‖x^ρ‖   (d réel, membres du monde témoin ρ ± δ)                    [C]
d, T, c > 0 :  c·x^{1/2} ≤ x^{1/2+d}/T ⟺ x ≥ (cT)^{1/d}   (horizon)                              [C]
x ≤ 10⁸ : |π − Li|/Li de 1,7·10⁻¹ à 1,3·10⁻⁴ ; |π − Li| de 5 à 754 ; |π − Li|·log x / g jusqu'à 772  [N]
reconstruction à N membres : 1er couple Λ ≠ 0 non séparé, log(n₂/n₁) ∝ T_N^{−0,91} (≈ π/T_N) ;
   tamis de la Tour N (E151) de même ordre ; RMS ε_N/√x ∝ T_N^{−0,38}                              [N]
F(u) = e^{−u/2}(ψ(e^u) − fond), fenêtre L = 7 : pente d log A_n/du₀, membres isolés (n ≤ 50) :
   ζ +0,0003 ± 0,0004 ;  W_δ (δ = 0,1, mêmes T_n) +0,0790, prédit δ⟨tanh δu₀⟩ = 0,0787             [N]
max|R|/√x par décade, 10³–10⁸ : exposant ζ +0,004, W_δ +0,086 ;  membres de ζ déplacés en 1/2 ± δ :
   écart à ψ de 0,31 à 1,33 (× √x), contre 0,24 constant pour les vrais membres                      [N]
pente 1/2 de tous les membres à la fois ⟺ |A(x)| ≤ C√x                                           [⟺RH]
```

## 10. Régimes, raccords et mondes témoins

**Régimes** (`p : e → l`) : `V(p) :⟺ T_e < T_l` ; `H(p) :⟺ T_e = T_l` ; exclusifs, exhaustifs [C].
« Vertical » (`VerticalPassage`) est le nom d'un passage dont la hauteur augmente, rien de plus : `V(p)` ne contient
ni `β_e = β_l` ni aucune hypothèse sur `β_e`, `β_l` (conservation radiale non incluse) ; seul `V(p) ∧ β_e = β_l = 1/2`
est « pur ». État engagé : `z` est engagé ⟺ `β_z = 1/2 ∧ ∃ o, V(o) ∧ l(o) = z` (membre ON atteint par un passage vertical).

```text
T_e < T_l ⟹ β_l ≤ 1/2 ≤ β_e    (sinon un miroir s'intercale ; fait d'inventaire, sans rôle dans la
                                  démonstration de l'auteur, §12)                               [C]
V : Δβ = 0 ⟺ β_e = β_l = 1/2 (pur) ;  Δβ < 0 ⟺ diagonal                                    [C]
H : β_e < β_l, une extrémité hors ligne                                                     [C]
```

**Lecture sur la Tour** [C] :

```text
pas(z) = log C_{k+1} − log C_k = π/T (écart logarithmique entre contacts) ;  pas(l) < pas(e) ⟺ V ;  pas(l) = pas(e) ⟺ H
T_z = T_w, β_z < β_w ⟹ ∃ c ∈ (0,1), ∀ k, C_k(w) = c·C_k(z),  c = exp((φ_w − φ_z)/T)
T_z ≠ T_w ⟹ ¬ ∃ c, ∀ k, C_k(w) = c·C_k(z)
θ_l(q) − θ_e(q) = [(T_l − T_e) log q − (φ₀(T_l) − φ₀(T_e))]/π + (D_l − D_e)/π       (décomposition)
régime = (contraction T_e/T_l, translation (D_l − D_e)/π) :
  vertical pur (< 1, 0) ;  diagonal depuis la ligne (< 1, D_l/π ∈ ]−1/(2πT_l), 0[) ;  horizontal (= 1, ≠ 0)
deux membres en ligne : (∀ q, θ_z(q) = θ_w(q)) ⟺ T_z = T_w
diagonal parti de la ligne : C_k(l) = c₀(T_l,k)·r(l), r(l) > 1, r(l*) < 1, φ(l) > φ₀(T_l), x^{β_l} < x^{1/2} (x > 1)
```

**Jonctions** (`p = (a,m)`, `q = (m,b)`) [C] :

```text
V puis V ⟹ β_m = 1/2 ;  V puis H ⟹ β_m < 1/2 ;  H puis V ⟹ β_m > 1/2
β_m = 1/2 ⟹ (V(p) ⟺ V(q)) ;  sortie horizontale d'un membre en ligne ⟹ atteint horizontalement, fibre ≥ 3
p vertical : V(q) ⟺ β_l = 1/2 ;  H(q) ⟺ β_l < 1/2
entrée H précédée d'un passage diagonal ; après V, V : départ en ligne
β_z ≠ 1/2 ⟹ ∃ m, T_m = T_z, β_m < 1/2, passage horizontal sortant de m, m le plus bas ou atteint verticalement
|F(T)| ≥ 2 ⟺ ∃ z ∈ F(T), β_z ≠ 1/2 ;  deux membres en ligne de même hauteur sont égaux
p vertical : β_l = 1/2 ⟺ F(T_l) = {l} ;  β_e = 1/2 ⟺ F(T_e) = {e}
RH ⟺ tout passage vertical ⟺ ∀ z, w : T_z = T_w ⟹ z = w
   ⟺ (aucun passage diagonal) ∧ (le plus bas membre sans passage horizontal)
   ⟺ (aucune jonction V puis H) ∧ (le plus bas membre sans passage horizontal)              [⟺RH]
```

**Fonction réelle sur la ligne** [C] :

```text
Λ_ℝ(s) = ζ(s)·Γ_ℝ(s) (Re s > 0) ;  Λ_ℝ(s̄) = conj Λ_ℝ(s) ;  Λ_ℝ(1 − s) = Λ_ℝ(s) ;  Λ_ℝ(1 − s̄) = conj Λ_ℝ(s)
L(T) = Λ_ℝ(1/2 + iT) ∈ ℝ
ζ(1/2 + iT) = 0 ⟺ L(T) = 0 ⟺ ∃ z ∈ F(T), β_z = 1/2
L(t₁)·L(t₂) < 0 ⟹ ∃ z, β_z = 1/2, t₁ < T_z < t₂
T_e < t < T_l ⟹ L(t) ≠ 0 ;  T_e < t₁ < t₂ < T_l ⟹ L(t₁)·L(t₂) > 0
```

Dans le monde décalé, `F_δ(1 − s) = F_δ(s)` et `F_δ(s̄) = conj F_δ(s)` : réel sur la ligne aussi **[NC]**.

**Cellule `a → e → l → b`**, `T_a < T_e = T_l < T_b` [C] :

```text
β_e < 1/2 < β_l, 1/2 ≤ β_a, β_b ≤ 1/2, l = e* ;  d := 1/2 − β_e ∈ (0, 1/2)
pas(e) < pas(a), pas(l) = pas(e), pas(b) < pas(l) ;  C_k(l) = c·C_k(e), 0 < c < 1
M₁ = Occ(e) = p_{n+1}, M₂ = Occ(l) = p_{n+2}, M₃ = Occ(b) = p_{n+3}
T·(β_w − β_z) = ‖ρ_z‖·‖ρ_w‖·sin(φ_z − φ_w) ;  2Td = ‖ρ_e‖·‖ρ_l‖·sin(−T log c)
verrou de phase : q^{ρ_l}/ρ_l = (q^{ρ_e}/ρ_e)·R_E(q)·exp(−iT log c),  R_E(q) = q^{2d}‖ρ_e‖/‖ρ_l‖
cellule_l(q) ∈ {cellule_e(q), cellule_e(q) + 1}
R(a,e;M₁)·R(e,l;M₂)·R(l,b;M₃) = M₁^{1/2−β_a}·M₃^{β_b−1/2}·‖ρ_a‖/‖ρ_b‖·(M₂²/(M₁M₃))^d
(M₂²/(M₁M₃))^d ≠ 1 ;  M₂² − M₁M₃ = M₂(g − g') + g g',  g = M₂ − M₁, g' = M₃ − M₂
charge > 1 ⟺ M₁M₃ < M₂² ;  g ≥ g' amplifie ;  (g, g') = (2, 4), M₂ > 4 atténue
cellule ⟹ ¬RH ;  RH ⟹ aucune cellule
```

Existence d'une cellule depuis un hors-ligne **[NC]**. E135, 5000 triplets : `g > g'` 2363/2363 amplifient,
`g = g'` 243/243, `g < g'` 2394/2394 atténuent ; rapport mesuré `= (M₂²/(M₁M₃))^δ` à 9 décimales **[N]**.

**Deux horloges** [C] : `n` (membres), `h` (hauteurs). V : `Δn = Δh = 1` ; H : `Δn = 1, Δh = 0`.

**Énergie et transport** [C] :

```text
E_z(q) = q^{β_z}/‖ρ_z‖ ;  R(q) = E_l(q)/E_e(q) = q^{β_l−β_e}·‖ρ_e‖/‖ρ_l‖
log(E_l/E_e)(q) = H(q) − V,  H(q) = (β_l − β_e) log q,  V = log‖ρ_l‖ − log‖ρ_e‖
β_e = β_l, T_e < T_l ⟹ E_l(q) < E_e(q)  ∀ q > 0
β_e < β_l ⟹ ∃ q₀ ≥ 1, ∀ q > q₀ : E_l(q) > E_e(q)
E_e(q₁) = E_l(q₁) ∧ E_e(q₂) = E_l(q₂) ∧ q₁ < q₂ ⟹ β_e = β_l   (une seule égalité ne suffit jamais)
C⁻(e) = C⁻(l) ⟺ β_e = β_l (même hauteur) ;  hors ligne aucun contact du miroir n'égale un contact du zéro
```

À même hauteur, `β_e < β_l`, `T ≥ 2` : l'équation `R(q) = 1` a pour seule racine
`q* ≈ 1 + (β_e + β_l)/(2T²) < 2`, et `R(q) > 1` pour tout `q ≥ 2` : aucune relation de taille des premiers
ne manque à cet endroit.

**Raccord** [C] :

```text
M := p_min(e) = Occ(l) ;  k_e = k_e(M), k_l = k_l(M) ;  C_{k_z}(z) < M ≤ C_{k_z+1}(z)
E_z(C⁻) < E_z(M) ≤ E_z(C⁺),  z ∈ {e, l} ;  unicité du raccord
Or(p) :⟺ R(M) ≤ 1 ⟺ (β_l − β_e) log M ≤ log‖ρ_l‖ − log‖ρ_e‖
diagonal fermé (a = β_e − β_l ≥ 0, q ≥ 2, T_e ≤ T_l, T_l ≥ 2) :
  q^a ≥ 1 + a/2 ;  ‖ρ_e‖² ≤ β_l² + T_l² + 2a ≤ (1 + a)‖ρ_l‖² ≤ q^{2a}‖ρ_l‖²  ⟹  R(q) ≤ 1
horizontal (T_e = T_l = T ≥ 2, δ = β_l − β_e > 0) :
  ‖ρ_l‖² − ‖ρ_e‖² = δ(β_l + β_e) < 2δ ≤ (δ/2)T² ⟹ ‖ρ_l‖² ≤ (1 + δ/2)‖ρ_e‖² < 4^δ‖ρ_e‖² ≤ q^{2δ}‖ρ_e‖² ⟹ R(q) > 1
T_e < T_l ⟹ Or(p) ;  T_e ≥ 2 : Or(p) ⟺ T_e < T_l
même hauteur : |k_l(q) − k_e(q)| ≤ 1
```

**Raccord grammatical** [C] :

```text
E_n = (n, p_n, p_{n−1}, p_{n+1}, g_in, g_out, p_n mod 6, g_in mod 6, g_out mod 6, log p_n) ;  H_{n+1} = H_n ⧺ (E_{n+1})
sur e → l : événement E_{n_l}, prédécesseur Occ(e), successeur p_min(l), g_in > 0, g_out > 0 ;
  E = E^Z ;  H_{n_l} = H_{n_e} ⧺ (E) ;  M détermine (e, l)
pas d'un membre s(z) = (Occ(z)/p_min(z))^{β_z − 1/2} :  = 1 ⟺ β = 1/2 ;  > 1 ⟺ β < 1/2 ;  < 1 ⟺ β > 1/2
R_{e→m}(M₁)·R_{m→l}(M₂) = (M₂^{β_l}/M₁^{β_e})·(‖ρ_e‖/‖ρ_l‖)·(M₁/M₂)^{1/2}·s(m)
∏_{k≤n} M_k^{β_{k+1}−β_k} N_k/N_{k+1} = (N_0/N_{n+1})·(M_n^{β_{n+1}}/M_0^{β_0})·(M_0/M_n)^{1/2}·C_n,
  C_n = ∏_{k<n} (M_k/M_{k+1})^{β_{k+1}−1/2} ;  (∀ n, C_n = 1) ⟺ ∀ k, β_{k+1} = 1/2
paire 1/2 ∓ δ : somme des modules x^{−1/2}(x^δ + x^{−δ}) > 2x^{−1/2}  (x > 1, δ ≠ 0)
fenêtre W(C) = {ρ : |Im ρ| ≤ C} ;  (∃ C, e ∈ W(C) ∧ l ∉ W(C)) ⟺ T_e < T_l
```

Le certificat complet existe sur le passage horizontal hors ligne, transport renversé. E137 (5000 hauteurs) :
`max |R(x)|/√x = 0,60` ; paire de remplacement au rang 1 : 6,9 / 14,3 / 50,7 fois le plancher pour
δ = 0 / 0,25 / 0,45, au rang 4001 : 1,03 / 1,16 / 2,37 ; meilleur δ sous comptage gardé : 0 aux quatre rangs
**[N]**.

**Système rigide global 𝒮** [C] : conjonction sur le même ensemble de zéros des couches ordre, miroir,
horloges, contacts, énergie, branche supérieure, raccord grammatical, détecteur, pas, grammaire `H_n^Z = H_n`,
formule explicite `ψ_Z = ψ` (`x ≥ 2`), reste. `𝒮` est vrai sans hypothèse ; un hors-ligne conserve
`ψ_Z = ψ`, `H_n^Z = H_n` et `𝒮`.

**Capture** [C] : `D_ins = 0` sur la ligne ; hors ligne `0 < D_ins ≤ (1 − 2β)/(πT)` (β < 1/2).

**Mondes témoins.**

```text
Monde décalé  F_δ(s) = ζ(s − δ)ζ(s + δ), 0 < δ < 1/2 :
  zéros ρ ± δ, même hauteur ;  −F_δ'/F_δ(s) = Σ Λ(n)(n^δ + n^{−δ}) n^{−s}  (Re s > 1 + δ)
  ψ_δ(x) = x^{1+δ}/(1+δ) + x^{1−δ}/(1−δ) − Σ_ρ [x^{ρ+δ}/(ρ+δ) + x^{ρ−δ}/(ρ−δ)] + …
  mêmes premiers, mod 6, écarts, alternance ; poids Λ(n)(n^δ + n^{−δ}) ;  pôles 1 ± δ ;  2N(T) membres
  w_d(p) = log p (p^d + p^{−d}) ≥ 2 log p ≠ log p : aucun premier reconnu, d = 0 compris        [C]
Monde de rupture  W_{δ,τ}(s) = ζ(s)·ζ(s−δ−iτ)ζ(s+δ−iτ)ζ(s−δ+iτ)ζ(s+δ+iτ), 0 < |δ| < 1/2, τ > 0 :
  W(ρ) = 0 et W(ρ ∓ δ + iτ) = 0 pour ρ = 1/2 + iT ;  poids Λ(n)·n^c                         [C]
  consécutivité des trois zéros                                                             [NC]
Fonction fixe sans premiers  f(s) = (w² + 1)((w − 1/4)² + 4)((w + 1/4)² + 4),  w = s − 1/2 :
  f(1 − s) = f(s), f(s̄) = conj f(s), Im f(1/2 + it) = 0 ;  zéros 1/2 ± i, 3/4 ± 2i, 1/4 ± 2i     [C]
```

E135 : dans `F_δ`, 5000/5000 raccords horizontaux renversés, 4999/4999 diagonaux orientés ; `Σ_ρ 1/ρ` réel
`= 0,0230957`, dans `F_δ` `≈ 0,0462` **[N]**. Quartet unique (rang 101, δ = 0,25) : perturbation
`|Δψ| ~ 2x^{1/2+δ}/γ` ; un quartet inséré satisfait les rigidités d'indice et les identités de comptage, il ne
se heurte qu'à la taille de `ψ(x) − x` **[N]**.

## 11. L'état engagé et la prémisse unique

```text
E(z) ⟺ β = 1/2 ;  E(z) ⟹ z* = z, contact_k(z) = c₀(T,k), r(z) = 1, D(z) = 0, L(T) = 0         [C]
∃ z, w : T_z < T_w   (deux hauteurs)                                                         [C]
∃ p, 0 < T_e ∧ V(p)  (existence d'un passage vertical ; elle n'engage aucun membre et ne localise
                      pas ses extrémités sur la ligne)                                       [C]  (exists_verticalPassage)
```

`E(z)` désigne l'ensemble des propriétés d'un membre ON (nom du code : `EngagedState`, `engagedState_iff_onLine`) ;
l'état engagé au sens de la démonstration est un membre ON atteint par un passage vertical (§10).

Preuve des deux hauteurs : sinon l'ensemble des zéros est fini ;
`F(z) = z/2 − ζ'/ζ(0) + (ζ'/ζ(−1))z⁻¹ − Σ_{n≥1} z^{−2n}/((−2n)(−2n+1)) − Σ_ρ m_ρ z^ρ/(ρ(ρ+1))` est holomorphe
sur `Re z > 3/2`, égale à `Σ_{n<x} Λ(n)(1 − n/x)` pour `x > 1`, nulle sur `3/2 < x ≤ 2`, donc nulle ; or
`F(5/2) = (log 2)/5 ≠ 0`.

**Progression depuis l'état engagé** (`o` vertical arrive sur `e`, `β_e = 1/2`, `p : e → l`) [C] :

```text
e(p) = e(p') ⟹ l(p) = l(p') ;  β_e = β_{e'} = 1/2 ∧ T_e = T_{e'} ⟹ l = l'
T_l > T_e, ¬H(p) ;  n_l = n_e + 1 ;  pas(l) < pas(e) ;  contact_k(l) = c₀(T_l,k)·r(l)
L ≠ 0 sur ]T_e, T_l[ ;  événement du raccord = événement reconstruit ;  T_l ≥ 2 ⟹ Or(p)
β_l ≤ 1/2,  r(l) ≥ 1,  D_l ≤ 0     (fait d'inventaire, sans rôle dans la démonstration de l'auteur, §12)
β_l = 1/2 ⟺ r(l) = 1 ⟺ D_l = 0 ⟺ F(T_l) = {l} ⟺ tout passage partant de l est vertical
F(T_l) = {l} ⟹ E(l)
```

**Liaisons sur l'arrivée** (`l = β' + iT'`) [C] :

```text
toute représentation : ∃ i, Re s_i = β', Im s_i = T', w_i = −m(l) ≠ 0
β' = 1/2 ⟺ ∀ i, w_i ≠ 0 ∧ Im s_i = T' ⟹ Re s_i = 1/2
T(l*) = T',  β' = 1/2 ⟺ l* = l ;  β' = 1/2 ⟹ L(T') = 0
```

**Paramètres de zêta** [C] : `ζ(s) = Π_p (1 − p^{−s})^{−1}` (`Re s > 1`) ; aucun paramètre ne dépend de `T` ;
la fonction fixe sans premiers change de régime (hauteur 1 : un zéro en ligne ; `1 < T < 2` : aucun ;
hauteur 2 : `1/4 + 2i`, `3/4 + 2i`).

**Persistance** [C] :

```text
M1  β_m = 1/2 ⟹ ¬(V(p) ∧ H(q)) ∧ ¬(H(p) ∧ V(q))
M2  E(z) ⟺ β = 1/2 ; tous les champs de E(z) fonctions de T(z)
M3  o vertical sur e, β_e = 1/2, β_l = β_e ⟹ V(p), E(l), ∀ q partant de l : V(q)
M4  Loi : ∀ p, V(p) ∧ β_e = 1/2 ⟹ β_l = β_e   (hypothèse)  ⟹  ∀ w ≻ e : β_w = 1/2, atteint et quitté verticalement
    (récurrence forte sur n(w))
RH ⟹ Loi ;  (∃ C, ∀ x > 1, |A(x)| ≤ C√x) ⟹ Loi ⟹ persistance
β_l = F(T_e, β_e, E) sur tout passage vertical, F(T, 1/2, E) = 1/2 ⟹ persistance
```

**Prémisse unique.**

```text
PNoRegimeChange := ∀ p q, l_p = e_q → ¬((V(p) ∧ H(q)) ∨ (H(p) ∧ V(q)))
PNoRegimeChange ⟺ RH   (aucune condition annexe)                                            [⟺RH]
p vertical : r(l) ≥ 1 [C] ;  r(l) ≤ 1 ⟺ ∀ q, l_p = e_q → ¬H(q) [C] ;
             PNoRegimeChange ⟹ r(l) = 1, β_l = 1/2, (T, 1/2) → (T', 1/2) [C]
r(l) ≤ 1                                                                                     [ND]
```

Cette lecture caractérise la prémisse sur un pas ; `r(l) ≤ 1` n'est pas le verrou en vigueur (§12).

`⟹` : aucune entrée `V → H`, et le plus bas passage n'est pas horizontal (sinon tout passage le serait,
contre les deux hauteurs). `⟸` : sous RH aucun passage horizontal.

**Cible locale.** `Cons :⟺ ∀ p, β_e = 1/2 ⟹ β_l = 1/2` (moitié supérieure) ; amorce : tout membre sans
prédécesseur en ligne est en ligne. `RH ⟺ Cons ∧ amorce` [⟺RH] ; `Cons` seule n'est pas RH ;
`p vertical : β_l = 1/2 ⟺ aucun changement de régime à l'arrivée` [C] ; `Cons` est violée dans le monde de
rupture et la fonction fixe sans premiers [C]. L'amorce n'est pas acquise dans le dépôt : aucun théorème du dépôt ni
du port zeta23 n'a pour conclusion `β = 1/2` au membre le plus bas ; le fait est annoncé connu dans la littérature,
non compilé ici [NC]. Démonstration de l'auteur, statut, erreur de référence et verrou unique : §12 ; le seul
verrou en vigueur est celui de §12 et §14.

## 12. Ce que la démarche a établi sur la flèche, et ce qui manque

**Composition grammaire × cinématique** [C] (`Π(z) := π·θ_z(Occ z) = T log Occ(z) − φ`) :

```text
Π(z) = T log Occ(z) − φ₀(T) − T log r     (part de hauteur + part radiale, nulle ⟺ β = 1/2)
Π(l) − Π(e) = S(e,l) + ΔΘ_n(e),  S(e,l) = (T_l − T_e) log M − (φ_l − φ_e),  ΔΘ_n(e) = T_e log(p_{n+1}/p_n)
S(e,l) = H(e,l) + T_e log r_e − T_l log r_l,  H(e,l) = (T_l − T_e) log M − (φ₀(T_l) − φ₀(T_e))
(T_l − T_e) log M = (Π(l) − Π(e)) − T_e log(p_{n+1}/p_n) + (φ_l − φ_e)   (équation ; ΔT = 0 la satisfait)
chaîne z_0 → … → z_m : n(z_j) = n_0 + j, Occ(z_j) = p_{n_0+j}
Π(z_m) − Π(z_0) = Σ S(z_j, z_{j+1}) + Σ T_j log(p_{n_0+j+1}/p_{n_0+j})
Abel : Σ T_j log(p_{j+1}/p_j) + Σ (T_{j+1} − T_j) log p_{j+1} = T_m log p_m − T_0 log p_0
Σ S = Σ H + T_0 log r_0 − T_m log r_m
T_j ≤ T_{j+1}, p > 3 : ΔΘ_{n_j}(z_j) + ΔΘ_{n_j+1}(z_{j+1}) ≥ T_j log(1 + 6/p_{n_j})
β_e = 1/2 : β_l = 1/2 ⟺ Π(l) − Π(e) = H(e,l) + T_e log(p_{n+1}/p_n)
```

Identité pour tout `β_e, β_l` ; aucune borne inférieure sur `ΔT` ; `Π(l)` n'est fixé par rien ; vraie dans
`F_δ`.

**Excès** [C] :

```text
X(e,l) := Π(l) − Π(e) − T_e log(p_{n+1}/p_n) = H(e,l) + T_e log r_e − T_l log r_l
β_e = β_l = 1/2 ⟹ X = H ;  β_e = 1/2, β_l < 1/2 ⟹ X = H − T_l log r_l < H ;  T_e = T_l, β_e < β_l ⟹ H = 0, X = φ_e − φ_l > 0
z_0 → z_1 → z_2, β_0 = 1/2, β_1 < 1/2, T_1 = T_2 : X_01 + X_12 = H(0,1) − T_2 log r_2 (> H(0,1) si β_2 > 1/2)
p_n > 3, T_0 ≤ T_1 : Π(2) − Π(0) > H(0,1) + T_0 log(1 + 6/p_n)
chaîne : Σ X_j − Σ H_j = T_0 log r_0 − T_m log r_m = −T_m log r_m si β_0 = 1/2
```

**Inventaire au point engagé (E140)** [C] : au départ, `z* = z`, `log r = 0`, `C_k = c₀(T,k)`, `φ = φ₀`,
`s(z) = 1`, `L(T) = 0` ; grammaire : `n_l = n_e + 1`, événement `E(n_e + 1)`, aucun β ; à travers le passage :
`C_k(l) = c₀(T',k)·r'`, `X − H = −T' log r'`, `s(l) = 1 ⟺ β' = 1/2`, `M^{β'−1/2} = 1 ⟺ β' = 1/2`.
Générateur : `∃ G : ℝ → ℝ × ℝ`, `G(T_e) = (T_l, β_l)` pour tout passage parti de la ligne ;
`(∀ p vertical, β_e = 1/2 ⟹ β_l = β_e) ⟺ (∀ p vertical, β_e = 1/2 ⟹ G(T_e)₂ = 1/2)`.

**Réponse radiale aux poids (E141)** [C] :

```text
Z_ε(s) = ζ(s − εc) ;  −Z_ε'/Z_ε(s) = Σ Λ(n) n^{εc} n^{−s} ;  ‖Λ(n) n^{εc}‖ = Λ(n) n^{ε Re c}
ρ(ε) = ρ + εc :  dβ/dε = Re c,  dT/dε = Im c ;  Re c = 0 ⟺ ∀ ε, n : ‖Λ(n) n^{εc}‖ = Λ(n)
Ξ réelle sur la ligne, Ξ'(ρ) ≠ 0, Im Φ(ρ) = 0, Ξ(γ(ε)) + εΦ(γ(ε)) = 0, γ(0) = ρ = 1/2 + iT :
  Re Ξ'(ρ) = 0,  Re γ'(0) = 0,  Im γ'(0)·Im Ξ'(ρ) = Φ(ρ)
contrôle f : f'(1/2 + i) = (2465/128)·i,  même conclusion
```

Aucun `Λ(n)` dans `∂β/∂ε = 0` ; vrai pour `f`. Existence de `γ`, théorème de Hamburger **[NC]**.

**Résidu de changement et prédicteurs (E141–E145)** [C] :

```text
D_l − D_e = (Π(l) − Π(e)) − H(e,l) − T_e log(p_{n+1}/p_n) ;  β_e = 1/2 : D_l = ΔΠ − H − T_e log(p_{n+1}/p_n)
p vertical parti de la ligne : D_l ≤ 0 ;  D_l = 0 ⟺ aucun passage horizontal ne part de l
∃ F : (T, n) ↦ ℝ, F(T_e, n_e) = D_l sur tout passage parti de la ligne
‖A(x)‖ ≤ C x^θ (x > 1, θ < 1) ⟹ 1 − θ ≤ β ≤ θ,  arctan 2T − arctan(T/(1−θ)) ≤ D ≤ arctan 2T − arctan(T/θ)
θ = 1/2 ⟹ D = 0 ;  (∀ w, D(w) = 0) ⟺ ∃ C, ∀ x > 1, ‖A(x)‖ ≤ C√x
(F exact) ∧ (F = 0 sur l'état engagé) ⟹ Loi ⟹ persistance ;  ∃ F exact et nul ⟺ Loi
contrôles : D(1/2, T) = 0, D(1/2 ∓ δ, T + τ) ≠ 0 (rupture) ;  D(1/2, 1) = 0, D(1/4, 2), D(3/4, 2) ≠ 0 (f)
```

**E142, rétro-ingénierie de 300 zéros** **[N]** :

```text
(1) θ(T̂_n) = (n − 3/2)π : écart-type 0,24 espacement, max 0,65 ; |N_lisse(T_n) − (n − 1/2)| < 1/2 sur 293/300
(2) tan θ(T) = −C_N(T)/S_N(T),  C_N = Σ_{n≤N} n^{−1/2} cos(T log n),  S_N = Σ_{n≤N} n^{−1/2} sin(T log n),
    N = ⌊√(T/2π)⌋ ≤ 9 : 300/300 racines, successeur prédit sur 299/299 passages, erreur max 1,7·10⁻³ espacement
(3) moyenne_n cos(T_n log x) = −(T/(2πN))·Λ(x)/√x : corrélation 0,998, x = 2..40 (Landau 1911)
(4) D̂ = ΔN − (changements de signe) sur [g_m, g_{m+1}), θ(g_m) = mπ : 0 sur 300/300 ; f : D̂ = 2 aux jumeaux
```

**Bit de changement** [C] : `D_l = 0 ⟺ ¬∃ w, β_w ≠ 1/2 ∧ T_e < T_w ∧ ∀ t ∈ ]T_e, T_w[, L(t) ≠ 0` ;
`T_e ≤ t₁ < t₂, L(t₁)L(t₂) < 0 ⟹ T_l < t₂`. Piste non poursuivie (verdict de l'auteur).

**Flèche canonique** [C] (`β_e = 1/2`, `n_l = n_e + 1`, `M = p_{n+1}`) :

```text
θ_e(M) = θ₀_{T_e}(M)
θ_l(q) − θ_l(q') = T_l log(q/q')/π
k + 1/(2πT_l) ≤ θ₀_{T_l}(q) ∧ θ₀_{T_l}(q) + 1/(πT_l) ≤ k + 1 ⟹ ⌈θ_l(q)⌉ − 1 = k  (toute β_l)
θ_l(q) = θ₀_{T_l}(q) + D_l/π ;  −1/(2πT_l) < θ_l(q) − θ₀_{T_l}(q) < 1/(πT_l)
π(θ_l(M) − θ_e(M)) = ΔT log M − (arctan 2T_l − arctan 2T_e) + D_l
β_l = 1/2 ⟺ θ_l(M) = θ₀_{T_l}(M) ⟺ θ_l(q) = θ₀_{T_l}(q) pour un q > 0 quelconque
```

**Flèche d'entrée écrite sur le poids d'Euler** (caractérisation, non verrou en vigueur) [C] : `Flèche ⟺ Cons` ; `RH ⟺ Flèche ∧ amorce` ;
`Flèche ⟺ ∀ p, β_e = 1/2 ⟹ ‖M^{−ρ_l}‖ = M^{−1/2}` ; `(1 − p^{−ρ})^{−1}` est défini et non nul en tout
membre. E146 **[N]** : flèche et amorce sur 1000 membres (Turing : signe de `Z` et `N(T)`) ; position de `M`
dans sa cellule équirépartie (KS p = 0,90) ; produit d'Euler tronqué à `M` : AUC 0,90 sur la hauteur
d'arrivée, 0,84–0,88 sur les zéros hors ligne de `F_δ` ; le poids exact sépare `F_δ` à chaque événement.

**Premiers pointés (E147)** [C] : `Occ`, `p_min`, états et classes mod 6 fonctions du rang ;
`Π(β,T,q) = T log q − arctan(T/β)` : même Tour ⟹ hauteur seule, même hauteur ⟹ translation rigide, même
premier ⟹ hauteur + phase. **[N]** (β = 0,4 et 0,2, 300 ON contre 150 paires) : `Occ`, `p_min` identiques
300/300 ; classes identiques sur 299 passages ; premier du contact `C⁺` différent sur 42 rangs pairs, égal
300/300 à celui de la Tour de ligne (effet de hauteur) ; écart d'entrée de `M` `< 1/(πT)` ; séparation par
`p^β` (0/300 égal) et par comptage (`N_OFF − N_ζ = +1` sur chaque `[T_{2i−1}, T_{2i})`).

**Grille infinie (E148, E149)** : écart OFF − ON constant à `10⁻⁶` près et égal à `D/π` ; à `T_1` : 35
(β = 0,4) et 115 (β = 0,2) premiers changent de cellule ; fraction `|D|/π` de premiers qui changent de
cellule, observé/prédit 0,975 (β = 0,45), 0,978 (0,4), 0,985 (0,2), 0,77 à β = 0,49 sur petit effectif ;
`M` ne change jamais de cellule hors marge (300/300) **[N]**.

**La démonstration de l'auteur, son statut, l'erreur de référence et le verrou unique.** Énoncé de l'auteur, mot pour
mot, à employer partout où la démonstration est énoncée (régime ON = régime des membres en ligne) :

> Une fois le régime ON engagé, du fait de l'enroulement des Tours, la partie réelle du zéro suivant est forcément la
> même que celle du zéro qui a engagé le régime.

Écrit dans le build principal (`Terminal/OnLineBetaEqPrevious.lean`) :

```text
onLine_beta_eq_previous {o p : TZeroPassage}  (hJ : l(o) = e(p))  (hE : 0 < T_{l(o)})  (ho : V(o))  (hOn : β_{l(o)} = 1/2) :
    β_{l(p)} = β_{e(p)}                                  (hypothèses déclarées ; aucune def P…, aucun sorry)
```

Écarts de premiers dans la démonstration (auteur) : c'est uniquement dans le régime ON que les écarts de premiers sont
atteints par la hauteur seule ; la partie réelle étant fixée, la hauteur doit progresser suffisamment. La phrase générale
« dans une Tour, l'écart entre deux premiers est lu par la hauteur seule » n'est pas un énoncé de la démonstration et n'y
figure pas. Le fait compilé reste dans l'inventaire avec sa portée : pour deux positions de lecture dans une même Tour,
`Π_z(q') − Π_z(q) = T·(log q' − log q)/π` (`gap_reading_height_only`) ; la différence efface le décalage commun
`D/π` sans démontrer qu'il est nul. La phrase « la partie réelle du zéro atteint ne dépasse pas un demi » n'est pas la
démonstration de l'auteur : elle ne figure dans aucun énoncé de la démonstration ; le théorème compilé qui la porte
(`β_l ≤ 1/2`, §11) reste dans l'inventaire, sans rôle dans la démonstration.

Statut (« prouvé ou pas, nous verrons », auteur) :

| Étape | Portée exacte |
|---|---|
| Existence d'un passage vertical | Établie [C] (`exists_verticalPassage`) ; ne localise pas ses extrémités sur la ligne. |
| Propriétés d'un membre ON | Établies [C] sous l'hypothèse qu'il est ON (`engagedState_iff_onLine`) ; ne produisent pas ce membre. |
| Sortie d'un état engagé | Établie [C] : le passage suivant avance en hauteur (`engaged_regime_kept`). |
| Propriétés de l'arrivée | Établies [C] : pas réduit, encadrement des contacts à l'infini (`windingNestedAtInfinity_of_precedes`). |
| Écarts de premiers dans le régime ON | Énoncé de l'auteur : la partie réelle étant fixée, les écarts ne sont atteints que par la hauteur, qui doit progresser suffisamment. Compilé : seulement l'identité des différences de lecture dans une même Tour (`gap_reading_height_only`), qui efface le décalage commun sans démontrer qu'il est nul. |
| Énoncé de l'auteur (régime ON engagé + enroulement ⟹ même partie réelle au zéro suivant) | Écrit dans le build principal (`onLine_beta_eq_previous`) ; compile ; [C sous `Dom`] où `Dom := ∀ w, ∀ x > 0, A_w(x) ≤ A_{z₁}(x)` est la CONCLUSION du raccord ouvert de l'unique prémisse `G := ∀ n ≥ 1, D_n ≤ D_1` ; `G` et `G ⟹ Dom` [ND] (2026-10-06). |
| Budget collectif `B_H : ∃ C > 0, ∀ x > 1, ‖S_{>H}(x)‖ ≤ C√x`, `S_{>H}(x) = Σ_{|Im ρ|>H} −m_ρ x^ρ/(ρ(ρ+1))` (`CollectiveBudget`, `followingSum`) : propriété à démontrer, jamais un fait acquis | [C] sans condition : `T_w > H ∧ β_w ≠ 1/2 ⟹ ¬B_H` (somme signée ; `ρ_w` et `1 − ρ̄_w` lus par la lecture du pôle, `offLine_following_refutes_collectiveBudget`) ; pour `H ≥ 0`, `B_H ⟺ ∀ w, T_w > H → β_w = 1/2`, avec `C_H = Σ_{|Im ρ|>H} m_ρ/‖ρ(ρ+1)‖` (`collectiveBudget_iff_following_onLine`, `followingBudget_eq`, `followingWeight_conj`) ; `A(x) = L_H(x) + S_{>H}(x)` pour `x > 1`, `L_H` somme FINIE sur `|Im ρ| ≤ H`, aucun de ses membres supposé en ligne (`remainder_eq_preceding_add_following`, `precedingSum_eq_finite_sum`) : identité, aucune borne. [C] sous hypothèse : `B_{T_e}` ⟹ `β_l = β_e` sur le pas engagé (`onLine_beta_eq_previous_of_collectiveBudget`). [ND] : `B_H` lui-même ; aucune grille finie ne le certifie. |
| Réduction au cas bas (`β_l ≤ 1/2` [C] pour le successeur immédiat ; reste `β_l < 1/2 ⟹ False`) et impacts comparés d'une paire `β < 1/2`, `1 − β` | [C] : `D(β,T) + D(1−β,T) < 0` avec `D = arctan 2T − arctan(T/β)`, par `arctan(T/β) − arctan 2T = arctan(T(1−2β)/(β+2T²)) > arctan(T(1−2β)/(1−β+2T²)) = arctan 2T − arctan(T/(1−β))` ; `λ_z·λ_{z*} > 1`, `C_k(z)·C_k(z*) > C_k^{ligne}(T)²` ; facteurs de demi-tour `e^{(β−1/2)π/T}·e^{(1/2−β)π/T} = 1` ; composante radiale de la tangente du signe de `β − 1/2` ; `β_l < 1/2 ⟹ ¬B_{T_e}`. Fonctions de `(β, T)` seules. [ND] : la contradiction du cas bas. |
| Fenêtre `e → l → s` : `l` premier zéro bas (`β_l < 1/2`, `T_l > T_e`), `s` successeur consécutif de `l` à hauteur gardée (existence [C], `exists_fiberSuccessor`) | [C] : `T_s = T_l`, `β_l < β_s ≤ 1 − β_l` (borne, pas `s = l*`) ; `π/T_s = π/T_l` ; `C_k(s) < C_k(l)` pour tout `k` ; `∀ N, ∃ M` premier `≥ N`, `‖F_l(M)‖ < ‖F_s(M)‖` ; `¬ LocalCaptivity(l → ·)` dès `T_l ≥ 2` ; captivité de `e → l` tenue ; si le passage quittant `s` avance en hauteur : `β_s > 1/2`. [N] E172 (premier partagé `p_min(départ) = Occ(arrivée) = p_{n+1}`) : rapports `3 → 4` médians 1,7306 ; 2,9950 ; 26,8661 (`β = 0,45 ; 0,4 ; 0,2`). [ND] : contrainte acquise contredite par la fenêtre. |
| Audit E118 / E163b / E172 / E173 : `F_ρ(x) = x^ρ/ρ` (brut) ≠ `−m x^ρ/(ρ(ρ+1))` (lissé) | [C] : `Re F_ρ(C_k) = (−1)^k ‖F_ρ(C_k)‖` aux contacts propres (`zeroTerm_re_at_contact`) ; `F_ρ(x)·conj F_{ρ*}(x) = x/(ρ(1−ρ))`, `ρ* = 1 − ρ̄` ; `‖F_ρ + F_{ρ*}‖² = ‖F_ρ‖² + ‖F_{ρ*}‖² + 2 Re(x/(ρ(1−ρ)))`, `Re(ρ(1−ρ)) = β(1−β) + T² > 0` ; donc `‖F_ρ + F_{ρ*}‖ > max(‖F_ρ‖, ‖F_{ρ*}‖)` pour tout `x > 0` (`mirror_pair_normSq`, `mirror_cross_re_pos`, `mirror_pair_no_internal_compensation`). `(x^d + x^{−d})/2 = cosh(d log x)` n'est la demi-somme que sans `1/ρ` ; écart mesuré 1,5e−4 (T_1, `d = 0,1`). [C] déjà : `‖F_β‖/‖F_{1/2}‖ = ‖1/2+iT‖/‖β+iT‖·x^{β−1/2}`, égalité en `x* = (‖β+iT‖/‖1/2+iT‖)^{1/(β−1/2)}` (`amplitude_ratio_sameHeight`, `upper_member_exact_horizon`). [N] E173 : `max ‖S_{>T_10}(x)‖/√x = 0,00491` sur `x ≤ 10¹⁰`, 5000 zéros (somme des modules 0,01867) ; avec paire `d = 0,1` en `T_11` : 0,00573 ; 0,00632 ; 0,00917 (`X = 10⁴, 10⁷, 10¹⁰`) ; résidu du reste lissé exact aux raccords `≤ 4,3e−5·√M`. [ND] : `B_H` ; toute borne collective ; l'énoncé lissé de la paire. |
| Comptage certifié, Zeta 23, reste exact (E174, audit §11) | [C] lissé : `G_ρ(x) = x^ρ/(ρ(ρ+1))`, `G_ρ·conj G_{ρ*} = x/(w(w+2))`, `w = ρ(1−ρ)`, `Re(w(w+2)) = a(a+2) − b² > 0`, `a = β(1−β)+T²`, `b = T(1−2β)` ; `‖c(G_ρ + G_{ρ*})‖ > max(‖cG_ρ‖, ‖cG_{ρ*}‖)`, `c ≠ 0`, `x > 0` (`mirror_cross_term_smoothed`, `mirror_cross_re_pos_smoothed`, `mirror_pair_no_internal_compensation_smoothed`). Exclusion du côté haut : [C] seulement sous `T_e < T_l` (arrivée), `passage_entry_radial_le_half` ; formes universelles [⟺RH] ou [ND]. [N, certifié hors Lean, Arb] `N(T_cut) = #{changements de signe de Z sur ]0, T_cut]} = 300` (`T_cut = 543,0857`) et `= 5000` (`T_cut = 5448,3852`) : liste exhaustive, simple, en ligne sous `T_cut`. [N] reste lissé `A = −Σ m G_ρ` : `|A − R_N| ≤ x ε_N`, `ε_300 ≤ 3,22e−3`, `ε_5000 ≤ 4,54e−4` (Rosser 1941, `β < 1` seulement) ; détection garantie `|A − R_N − Q| > x ε_N` jusqu'à `T ≈ 53–79` (N = 5000), aucune au-delà de `T_cut` ; rapports à un résidu observé (E173 : 45 / 3 / 0,2) non certifiés. Zeta23 (`fbdc36bb`) : `∀ε, ∃T₀, ∀T ≥ T₀, (2/3−ε)N(T,2T) ≤ N₀^simple(T,2T)`, constantes `2 − 1/c₁*` (≈ 0,6725), `5/6`, `(3 − 1/c₁*)/2` : proportions asymptotiques ; `lemmaR_tight_two` : paire hors ligne ≡ zéro double en ligne pour le certificat rang–trace. [ND] : `B_H` ; unicité du membre de la fibre à toute hauteur [⟺RH] ; captivité au raccord sortant. |
| Fenêtres de 12, 24, 36 transitions (E175, E174b, audit §12) | [C] premiers `> 3` consécutifs : `g_j + g_{j+1} ≥ 6` ; `m` pair : `p_{n+m} − p_n ≥ 3m`, `L(n,m) = log(p_{n+m}/p_n) ≥ log(1 + 3m/p_n)` ; `m` impair : `≥ 3m − 1` ; classe d'écart mod 6 = transition de résidus (`2 : 5→1`, `4 : 1→5`, `0` : même résidu) ; `ΔΘ_j = T_j log(p_{j+1}/p_j) > 0` même si `ΔT_j = 0` ; `Σ ΔΘ ≥ c·log(1+3m/p_0)` pour toute hauteur minimale `c` ; `T_m − T_0 = Σ_{ΔT_j ≠ 0} ΔT_j` ; Abel vrai pour TOUTE suite de hauteurs, la constante comprise (`Terminal/WindowProgression.lean`). [N] (Rosser 1941, littérature) : `b − a ≥ 2π(m+1−E(a)−E(b))/log(b/2π)` pour `m+1` points, `b − a ≤ 2π(E(a)+E(b))/log(a/2π)` entre points consécutifs, fibre `≤ ⌊2E(T)⌋` points, d'où `H ≤ (m+1) − ⌈(m+1)/K⌉` : limitation de fréquence, `H = 1` permis. [N] E174b : `ε_N` analytique (Arb) `3,2219e−3`, `4,5393e−4` ; détections certifiées en intervalles (ensembles d'indices, pas un seuil). [ND] : progression de hauteur minimale exigée par les premiers (aucune), exclusion d'une paire isolée. |
| Inversion tangentielle autour de 2 et 3 ; amorce des trois premiers zéros (E176, audit §13) | [C] `T = π/log(C_{k+1}/C_k)`, `β = T·cot(T log C_k)` pour tout zéro et tout `k` ; même paire indexée ⟹ même `(β, T)` ; branche : `0 < T log a − kπ < π/2` ⟹ `β := T cot(T log a) > 0` et `a = C_k` ; `∀ (β, T)`, `T > 0`, `∀ q > 0`, `∃! k`, `C_k < q ≤ C_{k+1}` ; `C_k = q` ⟺ `arctan(T/β) = T log q − kπ`, alors `β = T cot(T log q)` ; `β < 1` ⟺ `arctan T < arctan(T/β)` ; `T(log q₂ − log q₁) = (k − j)π` (`Terminal/TangentialInversion.lean`). [N] certifié Arb, hors Lean : balayage `k = 0..50`, `β ∈ ]0,1[`, `T ≤ 240` : 2 et 3 toujours dans une cellule ; « 2 et 3 contacts » ⟹ `T = mπ/log 1,5` et `β > 1` sous `T = 240` ; cellule de 3 dans `]2, 5[` : région 2D et 51 zéros sur 102 ; coupures 14, 17, 23, 28 : `N = 0, 1, 2, 3` (Turing ET Backlund), changements de signe de `Z`, `T_1 ∈ [14,1347251417347 ± 1,2e−14]`, `T_2 ∈ [21,0220396387716 ± 4,8e−14]`, `T_3 ∈ [25,0108575801457 ± 1,8e−14]`, simples et en ligne. [ND] propriété conservée par la succession ; transmission au-delà de `T_3`. |
| Largeurs de cellule, prédicteur sans fuite, fenêtre OFF conjointe, raréfaction première (E177, audit §14) | [C] `ℓ_l/ℓ_e = T_e/T_l` ; `ΔT ≥ A ⟹ ℓ_l ≤ π/(T_e + A)` ; `C_{k+1} − C_k = C_k(e^{π/T} − 1)` ; `log C_k = kπ/T + φ/T` ; `ΔT ≥ A, 2kA ≥ T_e ⟹ C_k(l) < C_k(e)` ; `π/2 − arctan T < 1/T` ; `0<β<1 ⟹ arctan T < arctan(T/β) < π/2`, réciproque (région de phase) ; `0<β<1, β'>0, (T'−T)(π + arctan T) ≥ 1 ⟹ ∀ k ≥ 1, C_k(β',T') < C_k(β,T)` ; fenêtre `(1/2, T_e) → (1/2 − d, T) → (1/2 + d, T) → (β_b, T_b)` : emboîtements, pas, écart de phase miroir `∈ ]0, 1/T[` pour tout `d ∈ ]0, 1/2[` ; `(m+1)! + i` composé (`Terminal/WindowFeasibility.lean`). [N] Rosser cité : `T_n ∈ [L_n, U_n]` (100 % sur 5000), contraction garantie seulement par fenêtre de `m ≥ m*(T)` (4 à 14, 7 à 5448, 10 à 10⁸), aucune sur un passage ; prédicteurs R, RB couverture 100 %, ajustement 89 % / 98 % (sans valeur de preuve) ; fenêtre OFF : région conjointe non vide sauf ajout/intercalation aux 13 premières positions (Rosser + comptage ON) ; fenêtres 12/24/36 : aucune violation de la borne de comptage avec un passage de même hauteur ; premiers : `p_{n+m} − p_n ≥ 3m` vérifié jusqu'à 2·10⁷. [ND] contraction à chaque passage ; `β = 1/2` depuis la phase. |
| Régime ON seulement : anneau radial entre deux Tours successives (auteur, 2026-10-05) | [C] normalisation commune `R_ρ(x) = ‖x^ρ/ρ‖/√x` ; `β = 1/2 ⟹ R_ρ(x) = r(T) := 1/√(T² + 1/4)` pour tout `x > 0` ; `0 ≤ L < U ⟹ r(U) < r(L)`, et pour `S, T ≥ 0` : `r(T) ≤ r(S) ⟺ S ≤ T` ; deux zéros en ligne, `T_e < T_l` : `r(T_l) < r(T_e)`, épaisseur `r(T_e) − r(T_l) > 0`, et pour tout zéro en ligne `w` : `r(T_l) ≤ R_w ≤ r(T_e) ⟺ T_e ≤ T_w ≤ T_l` ; `0 ≤ L ≤ T ≤ U ⟹ 1/√(U² + 1/4) ≤ r(T) ≤ 1/√(L² + 1/4)` ; `T_e ≤ L ≤ T_l ≤ U`, `l` en ligne ⟹ `r(T_e) − r(L) ≤ r(T_e) − r(T_l) ≤ r(T_e) − r(U)` ; `ε > 0`, `T > 1/ε ⟹ 0 < r(T) < ε` ; [C] (2026-10-06) anneau exact, MEMBRES ON : `e, l, w` en ligne, `0 < T_e < T_l` ⟹ `R_e = r(T_e)`, `R_l = r(T_l)`, `r(T_l) < r(T_e)`, et `r(T_l) ≤ R_w(x) ≤ r(T_e) ⟺ T_e ≤ T_w ≤ T_l` (`onLine_ring_iff`) ; limite basse LOCALE : `w` en ligne, `T_w ≤ T_l ⟹ 0 < r(T_l) ≤ R_w(x)` (`onLine_ring_floor_pos`) (`Terminal/OnRadialRing.lean`). [NC] la borne `U` issue du comptage, son calcul et sa validation anneau par anneau ; [ND] « le zéro suivant est en ligne » (antécédent de la limite basse). Ne pas confondre avec l'ordre des contacts. |
| Croisement rayons / contacts / hauteurs / comptage / reste, événement supplémentaire (auteur, 2026-10-05) | [C] `R_l(x) = x^{β_l − 1/2}/‖ρ_l‖` ; `β_l ≤ 1/2, x ≥ 1 ⟹ R_l(x) ≤ 1/‖ρ_l‖ < 1/T_l` ; si `T_e² + 1/4 ≤ T_l²` : `R_l(x) ≤ r(T_e)` ; `β_l < 1/2 ⟹ ∀ε>0 ∃X ∀x≥X, R_l(x) < ε` et `R_{l*}(x) > R` ; passage : aucun membre de hauteur dans `]T_e, T_l[` ; `z(C_k) = (−1)^k‖z(C_k)‖`, en ligne `(−1)^k r(T)√C_k` ; `log C_k = (kπ + φ)/T` ; `π·Π_l(C_k(e)) = (T_l/T_e)(kπ + φ_e) − φ_l` ; `Π_l(C_{k+1}(e)) − Π_l(C_k(e)) = T_l/T_e` ; `R_l(C_{k+1}(e)) = e^{(β_l−1/2)π/T_e} R_l(C_k(e))`, facteur `= 1 ⟺ β_l = 1/2` ; terme lissé `= −m·(x^ρ/ρ)/(ρ+1)` ; `T_e < T_l, β_l ≤ 1/2 ⟹ π/T_l < π/T_e`, `arctan 2T_l ≤ φ_l < arctan 2T_l + 1/(2T_l)`, `C_k(l) = C_k^{ligne}(T_l)·λ`, `1 ≤ λ < e^{1/(2T_l²)}` ; `(∀ε ∃ ON, r < ε) ⟺ (∀H ∃ ON, T > H)` ; encadrements numériques de `r(T_1), r(T_2), r(T_3)` sous bornes de hauteur en hypothèse. [C] (2026-10-06) `R_l(1) = 1/‖ρ_l‖` ; `β_l ≤ 1/2, 1 ≤ x ≤ X ⟹ 0 < X^{β_l−1/2}/‖ρ_l‖ ≤ R_l(x)` (plancher sur domaine fini) ; `β_l ≤ 1/2 : (∀ x ≥ 1, R_l(x) ≤ r(T_e)) ⟺ T_e² + 1/4 ≤ ‖ρ_l‖² = β_l² + T_l²` (`radius_dominated_iff_norm`, `radius_dominated_iff_gap`) ; `e` en ligne : `(∀ x > 0, R_l(x) ≤ r(T_e)) ⟺ β_l = 1/2 ∧ ‖ρ_e‖ ≤ ‖ρ_l‖` (`radius_dominated_axis_iff`) ; `β_l < 1/2 ⟹ ∀ R ∃ x ∈ ]0,1[, R < R_l(x)` (`low_member_not_dominated_on_axis`). [C] fenêtre de paramètres `(1/2, T_e), (1/2 − d, T), (1/2 + d, T)`, `T_e < T`, tout `d ∈ ]0, 1/2[` : tous les contrats de paramètres tiennent à hauteur gardée ; `k ≥ T_e/(T − T_e) ⟹ C_k(β, T) < C_k^{ligne}(T_e)`. [NC] toute borne `U` par comptage ; hauteurs ON non bornées. [ND] renouvellement de la contraction `T_l < T_s` (⟺ `λ = 1`). (`Terminal/OnCrossReadings.lean`) |
| Passage sortant `q`, travaillé directement (auteur, 2026-10-06) | Trois passages consécutifs `o → e`, `p : e → l`, `q : l → s` ; `o` vertical, `β_e = 1/2`. [C] `T_e < T_l`, `β_l ≤ 1/2` ; `q` horizontal, `β_l < 1/2 ⟹ β_s ≤ 1/2 ∨ s = l*` (`second_zero_mirror_or_le_half` : si `1/2 < β_s < 1 − β_l`, `s*` s'intercale) ; `VerticalPassage q ⟹ β_l = 1/2` (`junction_vertical_vertical`) ; `¬ VerticalPassage q ⟹ T_l = T_s ⟹ β_l < 1/2`, `λ_l > 1`, `T_s = T_l`, pas inchangé, contacts de `s` en deçà, `φ_s < φ_l`, `C_k(s) = C_k(l)·e^{(φ_s−φ_l)/T}`, captivité et hiérarchie au raccord `l → s` fausses (`T ≥ 2`), fibre de `T_l` non réduite à `l`. [ND] `VerticalPassage q` (théorème `renewed_height_advance`, un but `False`). Dépendance manquante : un énoncé [C], dérivé de propriétés acquises de zêta, faux sur `(1/2, T_e) → (β_l < 1/2, T_l) → (β_s, T_l)` ; sa conclusion peut porter sur `(β, T)` (correction de l'auteur, 2026-10-06 : ce qui importe est la dérivation, non la forme des paramètres) ; établi seulement : les contrats de paramètres déjà compilés sont tous satisfaits (`renewal_not_forced_by_parameters`). |
| Obligation d'enroulement entier, hypothèse de suffisance `W` (TDD, auteur, 2026-10-06 ; ANCIENNE prémisse : depuis la directive du même jour, l'unique prémisse est `G`, ligne suivante) | Prémisse `W := ∀ p, ∀ x > 0, ‖x^{ρ_l}/ρ_l‖ ≤ ‖x^{ρ_e}/ρ_e‖` (hauteurs positives : données structurelles ; aucune autre condition). [C] `W ⟹ RH` (`riemannHypothesis_of_whole_winding_all_passages`, sans amorce) ; raccords : domination entière sur `p` ⟹ `β_l = β_e ∧ ‖ρ_e‖ ≤ ‖ρ_l‖` ; `β_z < 1/2 ⟹ ∃ p` quittant `z`, `T_e = T_l`, `β_e < β_l` (miroir à même hauteur et à droite, successeur de fibre) ; donc `∀ z, ¬ β_z < 1/2`, ⟺ RH. [⟺RH] `W ↔ RH`. [C] Bloquée par le haut et par le bas : `W ⟹` pour `p, q` joints, `‖x^{ρ_s}/ρ_s‖ ≤ ‖x^{ρ_l}/ρ_l‖ ≤ ‖x^{ρ_e}/ρ_e‖` en tout `x > 0` (`two_sided_blocking_of_whole_winding`, conséquence, pas condition). Obligation ARITHMÉTIQUE [C], jamais prémisse : `smoothedRemainder x = Σ'_ρ nontrivialZeroResidueTerm x ρ` (`x > 1`, termes `−m_ρ x^ρ/(ρ(ρ+1))`, convergence absolue ; `smoothedRemainder_eq_tsum_residueTerm`) ; `= precedingSum H x + followingSum H x` ; `ψ(N) − fond = pas du canal des zéros` (`N ≥ 2`) ; lissé `= −m ·` brut `/(ρ+1)` membre par membre (`residueTerm_eq_zeroTerm`). Aucun objet `li − π` dans le dépôt, aucun théorème de liaison : identification interdite. Deux enroulements : acquis `∃ K, ∀ k ≥ K, C_k(l) < C_k(e)` sur tout passage, toute position radiale [C], ne suffit pas à fixer `β` ; posé `W` (`x < 1` compris) ; [⟺RH] `(∀ p, acquis ⟹ posé) ↔ RH` (antécédent toujours vrai) : [ND]. Portées : `W_p ⟹ InsideField` (`x ≥ 1`) [C] ; sous `β_l ≤ β_e`, `InsideField ↔ ‖ρ_e‖ ≤ ‖ρ_l‖` (ne conserve pas `β`) [C] ; plancher local sur domaine fini [C] ; anneau entre membres ON conditionnel ; `(∀ p, InsideField) ↔ RH` et `W ↔ RH` [⟺RH]. Routes du reste à `W`, chacune sous une borne [ND] : `‖followingSum T_e x‖ ≤ C√x` (`x > 1`) ⟹ `W_p` pour tout `p` de départ `> T_e` [C] ; `‖smoothedRemainder x‖ ≤ C√x ⟹ W` (lecture du pôle sur chaque membre et son miroir) [C] ; `W ↔ ∃ C, ∀ x > 1, ‖smoothedRemainder x‖ ≤ C√x` [⟺RH]. Raccord résiduel [ND] : identité de représentation (théorème) ⟹ borne `√x` ; l'antécédent étant acquis, ⟺ sa conclusion ⟺ RH ; posé nulle part en hypothèse. Obligation ouverte (auteur) : pourquoi la représentation exacte des écarts arithmétiques par les contributions des vrais zéros impose-t-elle `W` à chaque passage ? Statuts : démontré [C] ; conditionnel [C sous `W` ou sous une borne] ; observation numérique [N] (E164, E170, E173) ; ouvert [ND] (`W`, la borne, la flèche de renouvellement). Pas RH démontrée ; pas un verrou ajouté. LECTURE CONJOINTE (auteur, 2026-10-06 ; `Terminal/JointParameterReading.lean`, 38 théorèmes, 3 objets ; paramètres indépendants `β`, `T` ; dérivés `φ = arctan(T/β)`, `C_k = e^{(φ+kπ)/T}`, `ℓ = π/T`, fréquence `T` en `u = log x`, `x^β/√(β²+T²)`, `A(x) = x^{β−1/2}/√(β²+T²)`) : [C] `log C_{k+1} − log C_k = ℓ` ; `C_{k+1}/C_k = e^ℓ` ; `C_{k+1} − C_k = C_k(e^ℓ − 1)`, strictement croissant en `k` (distance ordinaire ≠ pas logarithmique) ; `A(x) = x^{β−1/2}·ℓ/√(π² + β²ℓ²)` ; `A(y)/A(x) = (y/x)^{β−1/2}` ; `A(C_{k+1})/A(C_k) = e^{(β−1/2)ℓ}` ; croisé : `Π_l(C_{k+1}(e)) − Π_l(C_k(e)) = T_l/T_e`, `A_l(C_{k+1}(e)) = e^{(β_l−1/2)π/T_e} A_l(C_k(e))` ; ON seulement `A(x) = ℓ/√(π² + ℓ²/4)` (conséquence) ; caractérisation `A(C_{k+1}) = A(C_k) ↔ β = 1/2`. Inversion [C] : `tan(T log C_k) = T/β ≠ 0` ; `T = π/log(C_{k+1}/C_k)`, `β = T/tan(T log C_k)` (restitution depuis deux contacts authentiques consécutifs du même zéro) ; encadrement d'un contact inconnu depuis l'état engagé : `C_k(l) = C_k^{ligne}(T_l)·λ`, `1 ≤ λ`, `λ = 1 ↔ β_l = 1/2` ; prédiction du prochain membre [ND]. Facteur de lissage `F = −m/(ρ+1)` [C] : lissé `= F·brut` ; `‖F‖ = m/√((β+1)²+T²)` ; `Re F = −m(β+1)/((β+1)²+T²)` ; `Im F = mT/((β+1)²+T²) > 0` ; `‖lissé‖ = m x^β/(√(β²+T²)√((β+1)²+T²))` ; au contact brut : lissé `= F·(−1)^k‖brut‖`, `Re = (−1)^k‖brut‖·Re F`, `Im ≠ 0` (les contacts bruts ne sont pas des contacts du lissé) ; `smoothedRemainder x = F·zeroTerm z x + Σ_{σ ≤ H, σ ≠ z} lissé_σ + followingSum H x` (`x > 1`, `T_z ≤ H`). Dérivée de comptage [C] : pour toute `F` avec `F'(ρ log x) = e^{ρ log x}/(ρ log x)`, `d/dy F(ρ log y)|_x = ρ·zeroTerm_ρ(x)/(x log x)` (`x > 1` ; `Ei` absent de Mathlib). Canaux [C] : `π(p_n) = n+1`, `π(p_{n+1}) − π(p_n) = 1` ; `Λ(p) = log p` ; `Λ(p^{k+1}) = log p` ; `li₂(x) = ∫_2^x dt/log t`, `R(n) = π(n) − li₂(n)`, `R(p_{n+1}) − R(p_n) = 1 − ∫_{p_n}^{p_{n+1}} dt/log t` ; [NC] liaison `R ↔ smoothedRemainder` (manque, pas réfutation). Fenêtres [C] : `A(p_{n+m})/A(p_n) = (p_{n+m}/p_n)^{β−1/2}` ; `β < 1/2`, `m` pair `≠ 0`, `p_n > 3` : `≤ (1 + 3m/p_n)^{β−1/2} < 1` (borne sur une Tour entre deux premiers, jamais par passage). [C sous `W_p`] `β_l = 1/2 ∧ ∀ k, A_l(C_{k+1}(l)) = A_l(C_k(l)) ∧ ℓ_l < ℓ_e ∧ ∀ k, A_l(C_{k+1}(e)) = A_l(C_k(e))` (`joint_reading_of_whole_winding`) ; `W_p ⟹ VerticalPassage q` (`renewed_height_advance`) ; `W ⟹ β_l = β_e` (`onLine_beta_eq_previous`) : BUILD PRINCIPAL PASS sous `W`. [⟺RH] `(∀ z k, A(C_{k+1}) ≤ A(C_k)) ⟹ W` (caractérisation nommant le premier raccord non démontré : identité de représentation ⟹ `∀ z k, A(C_{k+1}) ≤ A(C_k)`, [ND]). Chaîne : reproduction exacte → restriction conjointe [ND] → conservation [C] → renouvellement [C] → enroulement [C]. |
| Unique prémisse MINIMALE : le premier zéro apporte le plus grand gain dans la reconstruction collective du reste (auteur, 2026-10-06 ; `Terminal/FirstGainPremise.lean`, 118 théorèmes, 25 objets ; `Terminal/CanonicalEnumeration.lean`, 31 théorèmes, 7 objets ; objets arithmétiques corrigés le même jour, points 1 à 6) | Formules [C] : `ρ_n = β_n + iT_n`, `φ_n = arctan(T_n/β_n)`, `C_{n,k} = e^{(φ_n+kπ)/T_n}` ; contribution brute regroupée avec le conjugué `c_n(x) = −2 Re(x^{ρ_n}/ρ_n) = −2x^{β_n} cos(T_n log x − φ_n)/√(β_n²+T_n²)` (`pairContribution_eq`) ; `c_n(C_{n,k}) = −2(−1)^k C_{n,k}^{β_n}/√(β_n²+T_n²)` (`pairContribution_at_contact`) ; `|c_n(x)| ≤ 2‖x^{ρ_n}/ρ_n‖`, égalité aux contacts (phases d'amplitude maximale) ; `A_n(x) = 2x^{β_n−1/2}/√(β_n²+T_n²)` (`pairAmplitude_eq`) ; ON : `A_n = 2/√(1/4+T_n²)` ; `W_n = log(C_{n,k+1}/C_{n,k}) = π/T_n` (`contact_interval_eq`) ; ON : `A_n = 2W_n/√(π² + W_n²/4)` (`pairAmplitude_onLine_contact_interval`) ; `T_z < T_w ⟹ W_w < W_z` (toute position radiale) et, ON, `A_w < A_z` (`pairAmplitude_onLine_lt_of_height`). Gains sur un support de mesure fixé (`V` préhilbertien réel ; instance `EuclideanSpace ℝ (Fin m)`, `c_n = (c_n(x_i))_i`) [C] : `r_{n−1} = R − Σ_{j<n} c_j` ; `D_n = ‖r_{n−1}‖² − ‖r_{n−1} − c_n‖² = ‖r_{n−1}‖² − ‖r_n‖² = 2⟨r_{n−1}, c_n⟩ − ‖c_n‖²` (`collectiveGain_eq`) ; sous `R = Σ_{j≥1} c_j` (`HasSum`) : `r_{n−1} = c_n + Σ_{j>n} c_j`, `D_n = ‖c_n‖² + 2⟨Σ_{j>n} c_j, c_n⟩` (`collectiveGain_collective`). PRÉMISSE `G := ∀ n ≥ 1, D_n ≤ D_1` (hypothèse explicite `hGain` ; aucune hauteur, aucune domination, aucune décroissance des gains). [C sous `G`] `‖c_n‖² + 2⟨Σ_{j>n} c_j, c_n⟩ ≤ ‖c_1‖² + 2⟨Σ_{j>1} c_j, c_1⟩` (`firstGain_collective_relation`) ; `‖c_n‖² ≤ D_1 − 2⟨Σ_{j>n} c_j, c_n⟩` (`firstGain_amplitude_bound`) ; `⟨Σ_{j>1} c_j, c_1⟩ ≤ ⟨Σ_{j>n} c_j, c_n⟩ ⟹ ‖c_n‖ ≤ ‖c_1‖` (`norm_le_first_of_interaction`, lecture) ; SANS convergence [C] : `D_n = ‖c_n‖² + 2⟨r_n, c_n⟩`, `r_n = R − Σ_{j≤n} c_j` (`collectiveGain_eq_own_add_interaction`), relation collective bornée par le rang 1 (`firstGain_relation`), `⟨r_1, c_1⟩ ≤ ⟨r_n, c_n⟩ ⟹ ‖c_n‖ ≤ ‖c_1‖` (`norm_le_first_of_interaction_ordered`, hypothèse d'interaction [ND]) ; représentation ORDONNÉE `Σ_{j≤N} c_j → R` [C] : `r_N → 0`, `r_n = lim_N Σ_{n<j≤N} c_j` (`partialRemainder_tendsto_zero`, `following_partial_sums_tendsto`), `HasSum ⟹` ordonnée. CORRECTIONS (points 1 à 3) [C] : contribution normalisée `c_n(x)/√x` (`normalizedPairContribution`), `|c_n/√x| ≤ A_n`, égalité aux contacts ; support `∀ i, 1 < x_i`, `c_n := m_n · (c_n(x_i)/√x_i)_i` (`canonicalContributions`, multiplicité `m_n = zetaZeroMultiplicity`, simplicité non supposée), `‖c_n‖² ≤ m_n² Σ_i A_n(x_i)²` (`firstGain_canonical`) ; énumération canonique par l'index zéro-source `N(z) = #{w : 0 < T_w, w ≺ z}` : zéros en nombre infini (`explicitIndex_infinite`, `trueZero_infinite`), `∀ n ∃! z, N(z) = n` (`exists_index_eq`, `thm_zeroSourceIndex_injective`), `z_n := canonicalZero n` d'index `n − 1`, rang 1 = index 0, `z_m ≺ z_n ⟺ m < n`, `z_n, z_{n+1}` consécutifs, tout membre supérieur = un `z_n`, `sUpperZerosBelow z_1 = ∅` = ancre `hFirst` (`canonicalZero_one_bottom`) ; reste exact du canal brut `R(x) := ψ₀(x) − (x − log 2π − ½ log(1 − x⁻²))`, `ψ₀(x) = (ψ(x) + ψ(x⁻))/2` (`rawRemainder`), `R := (R(x_i)/√x_i)_i` (`normalizedRawRemainderVector`). [ND] représentation du canal brut `R(x)/√x = Σ_n m_n c_n(x)/√x` (ordre canonique ; `PM9aMidpointIdentity` nommée dans la base, jamais prouvée ; posée nulle part). [C] canal LISSÉ normalisé : `Re(A(x))/√x = Σ_n 2·Re(−m_n x^{ρ_n}/(ρ_n(ρ_n+1)))/√x` (`HasSum`, ordre canonique, membre et conjugué regroupés par `ExplicitIndex ≃ ℕ × Bool`, `smoothedCanonical_hasSum`), relation collective sous `G` compilée (`firstGain_smoothed_collective`) ; passage lissé → brut membre par membre : facteur `−m/(ρ+1)`, `|·| = m/√((β+1)²+T²)`, phase tournée (`normalizedSmoothedPairContribution_eq`), convergence non transportée [ND]. Conclusion visée du raccord : `∀ w, InsideField z_1 w ⟺ ∀ w, ∀ x ≥ 1, A_w(x) ≤ A_{z_1}(x)` (`insideField_iff_pairAmplitude`) ; ancre ON `β(z_1) = 1/2` [ND] (aucun terme Lean). FERMETURE [C], hypothèse = conclusion du raccord, pas `G` : `Dom := ∀ w, ∀ x > 0, A_w(x) ≤ A_{z₁}(x) ⟹ RH` (`riemannHypothesis_of_individual_domination`, aucune hypothèse sur `z₁`) ; `β₁ = 1/2 ∧ (∀ w, ∀ x ≥ 1, A_w ≤ A_{z₁}) ⟹ RH` (`_onLine`) ; premier zéro : `Dom ↔ RH` [⟺RH] ; `Dom ⟹ W` (ancienne obligation d'enroulement, `whole_winding_all_passages_of_individual_domination`). [C sous `Dom`] `renewed_height_advance`, `onLine_beta_eq_previous`. RACCORD OUVERT [ND], posé nulle part : `G ⟹ Dom`. COMPLÉMENTS (auteur, 2026-10-06, dix points + grammaire ; 118 théorèmes, 25 objets) [C] : `E_n := ‖c_n‖²`, `I_n := ⟨r_n, c_n⟩`, `r_n = R − Σ_{j≤n} c_j` ; `D_n = E_n + 2I_n` ; `D_1 − D_n = (E_1 − E_n) − 2(I_n − I_1)` ; `E_n − E_1 = 2(I_1 − I_n) − (D_1 − D_n)` ; [C sous `G`] `E_n − E_1 ≤ 2(I_1 − I_n)` ; `E_n ≤ E_1 ⟺ 2(I_1 − I_n) ≤ D_1 − D_n` (identifie le contrôle requis ; `I_1 ≤ I_n` suffisant, non nécessaire) [C], la borne elle-même [ND]. Phases, toute position radiale [C] : `a_z(x) = 2x^β/√(β²+T²)`, `φ_z = arctan(T/β)`, `c_z = −a_z cos(T_z u − φ_z)`, `u = log x` ; `c_z c_w = (a_z a_w/2)[cos((T_z−T_w)u − (φ_z−φ_w)) + cos((T_z+T_w)u − (φ_z+φ_w))]` ; normalisé : `(A_z A_w/2)[…]` ; `⟨c_n, c_j⟩ = m_n m_j Σ_i (A_n A_j/2)(x_i)[…]` sur le support. Queues [C] : `Q_{n,N} = Σ_{j=n+1}^N c_j`, `⟨Q_{n,N}, c_n⟩ = Σ ⟨c_j, c_n⟩`, `I_n = ⟨Q_{n,N}, c_n⟩ + ⟨r_N, c_n⟩` (sans convergence) ; représentation ordonnée ⟹ `⟨Q_{n,N}, c_n⟩ → I_n` ; `HasSum` (canal lissé) ⟹ `I_n = Σ_{j>n} ⟨c_n, c_j⟩`. ON [C] : `m_z = m_w`, `T_z < T_w` ⟹ `m_w A_w < m_z A_z` ; `A(C_{k+1})/A(C_k) = e^{(β−1/2)π/T}`. Grammaire [C] (objets compilés réutilisés) : `g_r = 6m_r + a_r`, `m_r = ⌊g_r/6⌋`, `a_r ∈ {0,2,4}` (`p_r > 3`), classes ⟺ transitions `AA/BB` (0), `A→B` (2), `B→A` (4), alternance des changements, `L_r = log(1 + (6m_r + a_r)/p_r)`, `Δθ_{n,r} = T_n L_r`, `B_n(p_{r+1})/B_n(p_r) = e^{β_n L_r}`, `B²` : `e^{2β_n L_r}`, `A_n(p_{r+1})/A_n(p_r) = e^{(β_n−1/2)L_r}` (ON : `1`), `Σ_{r=a}^{a+m−1} Δθ_{n,r} = T_n log(p_{a+m}/p_a)`, sommes de fenêtre par classes `0/2/4` et maintiens par état, `|#AB − #BA| ≤ 1`, phases relatives `Δθ_{n,j,r} = (T_n − T_j) L_r`, fenêtre `(T_n − T_j) log(p_b/p_a)`, plancher `|T_n − T_j| log(1 + 3m/p_a) ≤ |Σ|` (`m` pair, `p_a > 3`), arguments du produit avançant de `(T_n ∓ T_j) L_r` ; tout support de premiers est admissible (`p > 1`), pour des premiers sélectionnés par une fonction arbitraire : le transport depuis le support fixé n'est pas démontré. Identité d'Abel à hauteur constante : une constante réelle satisfait l'identité télescopique de toute fenêtre [C] ; cela ne construit aucune suite de vrais zéros et ne justifie pas « les premiers n'exigent aucune progression de hauteur » (revue de l'auteur, 2026-10-06). Le plancher de phase relative contient `|T_n − T_j|` en facteur : il mesure l'effet de l'écart des hauteurs, il ne le produit pas. [ND] chaîne canaux → borne des interactions → contrainte de hauteur ; borne démontrée sur `Σ cos(…)` des interactions ; `E_n ≤ E_1` ; `∀ w, ∀ x ≥ 1, A_w ≤ A_{z_1}` ; ancre ; gain maximal ⟹ domination individuelle. Lock court, exactement et sans ajout : « Déduire du premier gain collectif maximal que chaque contribution reste dans le champ du premier zéro. » Dépendances, dans un tableau séparé du lock (bloc `DÉPENDANCES DU RACCORD` du statut) : contrôle de `2⟨Σ_{j>n} c_j, c_n⟩` à chaque rang depuis `G` ; passage du support fini à tout `x > 0` ; représentation (ordonnée) des contributions BRUTES regroupées (non dérivée de `smoothedRemainder_eq_tsum_residueTerm`, qui porte sur `−m x^ρ/(ρ(ρ+1))`) ; passage du support fixé (`‖c_n‖ ≤ ‖c_1‖`) à la domination ponctuelle sur `x ≥ 1` ; contrôle de l'interaction `⟨r_n, c_n⟩`. `W` n'est plus une prémisse : hypothèse [⟺RH] de `riemannHypothesis_of_whole_winding_all_passages`, `two_sided_blocking_of_whole_winding`, `joint_reading_of_whole_winding`, `renewed_height_advance_of_whole_winding`. |
| Prémisse RÉDUITE (auteur, 2026-10-06 : le premier zéro est le plus fort sur la ligne) | [C] `A_n = 2/√(1/4 + T_n²)` ON, `T_1 ≤ T_n ⟹ A_n ≤ A_1` (`pairAmplitude_onLine_le_of_height`, `canonical_onLine_amplitude_le_first`) ; [C] rang canonique en ligne ⟹ dans le champ du premier, premier en ligne (`canonical_onLine_insideField`) ; [C] `A_w(x)/A_1(x) = x^{β_w − 1/2}·‖ρ₁‖/‖ρ_w‖` toute position radiale (`pairAmplitude_ratio_onLine_first`) : la hauteur atténue le coefficient, seule `β_w ≠ 1/2` fait varier le facteur en `x` ; [C] enveloppe lissée `|a_n/√x| ≤ 2m x^{β−1/2}/(√(β²+T²)√((β+1)²+T²))`, ON `2m/(√(1/4+T²)√(9/4+T²))`, décroissante en `T` (`abs_normalizedSmoothedPairContribution_le`, `_onLine_le`, `smoothed_onLine_envelope_anti`). Prémisse réduite `G′ : ∀ n ≥ 1, ¬ InsideField(z₁, z_n) → D_n ≤ D_1` ; [C] `G ⟹ G′` (`gain_restricted_of_gain`) ; [C] aux rangs en ligne `G′` est vide (`gain_restricted_vacuous_onLine`) ; [C sous `G′`] aux rangs hors du champ `E_n − E_1 ≤ 2(I_1 − I_n)` et `I_1 ≤ I_n ⟹ ‖c_n‖ ≤ ‖c_1‖` ; [C] ancre ON + `∀ n ≥ 1, InsideField(z₁, z_n)` ⟹ RH (`riemannHypothesis_of_canonical_insideField`) ; composition `G′ ⟹ (∀ n, InsideField)` en hypothèse (`riemannHypothesis_of_restricted_gain_link`). [ND] `D_n ≤ D_1` même en ligne (interaction `I_n` à borner) ; [ND] domination d'un rang hors du champ ; [ND] ancre ON. Corrections de l'auteur (2026-10-07) : [C] `riemannHypothesis_of_restricted_gain_link` = composition (ancre ON ∧ `G′` ∧ (`G′ ⟹ ∀ n, InsideField`) ⟹ RH), pas « `G′ ⟹ RH` » ; [C] `G ⟹ G′` est un affaiblissement, `G′` n'est pas démontrée ; [C] tous les rangs ON ⟹ `G′` vide (`gain_restricted_of_all_onLine`), et ce cas est RH (`riemannHypothesis_of_all_canonical_onLine`) : les observations entièrement ON ne testent pas `G′` ; [C] `m_n ≤ m_1 ⟹ m_n A_n ≤ m_1 A_1` ON (`canonical_onLine_weighted_le_first`), `‖c_n‖² ≤ m_n² Σ_i A_n(x_i)²` (`canonical_normSq_le_envelope`), `‖c_n‖² ≤ m_1² Σ_i A_1(x_i)²` ON sous `m_n ≤ m_1` (`canonical_onLine_envelope_le_first`) ; sans hypothèse sur les multiplicités, rien sur la contribution pondérée ; [C] support vide : `‖v‖ = 0`, `D_n = 0`, `G` et `G′` automatiques (`collectiveGain_support_empty`, `gain_of_support_empty`, `gain_restricted_of_support_empty`) ; porteurs sous `0 < m`. Cible [ND] : `E_n > E_1 ⟹ 2(I_1 − I_n) < E_n − E_1` ; [C] avec `E_n − E_1 ≤ 2(I_1 − I_n)` elle donne `E_n ≤ E_1` (`compensation_bound_incompatible`) et lui équivaut (`compensation_target_iff_ownEnergy_le`) ; instance `canonical_ownEnergy_le_first_of_no_compensation` [C sous `G′` et la cible] ; hypothèse d'aucune fermeture. Cible de captivité (auteur, 2026-10-07) : `Cap := ∀ w, ∀ u ≥ 0, A_w(e^u) ≤ A_1` ; [C] `Cap ⟺ ∀ w, InsideField(z₁, w)` (`captivity_iff_insideField`) ; [C] ON : `A_1 = 2/√(1/4 + T_1²)` constante ; [C] `β₁ = 1/2 ∧ Cap ⟹ RH` (`riemannHypothesis_of_captivity_onLine`) ; [ND] `Cap`. [C] `|I_n| ≤ Σ_{n<j≤N}|⟨c_j, c_n⟩| + ‖r_N‖‖c_n‖` (seule borne, `interaction_abs_le_tail_add_residual`) ; [ND] toute borne des sommes oscillantes. [C] `D_1 < D_n ⟺ 0 < (E_n − E_1) − 2(I_1 − I_n)` ; [C] `G′ ∧ (∀ n ≥ 1, ¬ InsideField ⟹ D_1 < D_n) ⟹ ∀ n ≥ 1, InsideField` (`canonical_insideField_of_gain_excess`, obligation en hypothèse). [C] `T_n = T_j` : `c_n c_j = (A_n A_j/2)[cos(φ_n − φ_j) + cos(2T log x − (φ_n + φ_j))]`. [C] `¬ InsideField(z₁, w) ⟺ ∃ x ≥ 1, A_{z₁}(x) < A_w(x)` ; [C] `β₁ = 1/2, β_w ≥ 1/2, A_{z₁}(x) < A_w(x), x ≤ x' ⟹ A_{z₁}(x') < A_w(x')` (`exceedance_persists`, lu par toute abscisse du support au-delà, `exceedance_detected_on_support`). Couplage ON [C] : `W_{n+1}/W_n = T_n/T_{n+1}`, `f_{n+1}/f_n = T_{n+1}/T_n`, `A_{n+1}/A_n = √((1/4+T_n²)/(1/4+T_{n+1}²))` (`onLine_coupling_ratios`) ; `T_n/T_{n+1} < A_{n+1}/A_n < 1` (`onLine_amplitude_ratio_between`) ; cellules parcourues `(T_n/π) log(p_fin/p_début) = Σ_r Δθ_{n,r}/π` (`window_cells_eq`), rapport `T_n/T_1` (`window_cells_ratio`) ; [ND] toute accélération (variation de ces rapports) ; [N] E182 : variation du rapport de fréquence > 1 sur 149/298 passages, L_r croît sur 589/1228 événements, annulation médiane 1,000 des sommes oscillantes sur les fenêtres de battement < 1/2 demi-tour. Chaînes (auteur, 2026-10-08) : [C] `Σ_{a≤n<b} D_n = ‖r_a‖² − ‖r_b‖²` (`chain_gain_telescope`) ; [C] `I_n = Σ_{n<ℓ≤b}⟨c_ℓ,c_n⟩ + Σ_{b<ℓ≤N}⟨c_ℓ,c_n⟩ + ⟨r_N,c_n⟩` (`interaction_eq_chain_add_external_add_residual`) ; [C] deux troncatures donnent la même interaction complète (`interaction_tail_decomposition_truncation_invariant`) ; [C] coût d'un masquage `D_n ≤ D_1 ⟹ E_n − D_1 ≤ −2I_n` et `‖c_n‖² − D_1 ≤ 2‖r_n‖‖c_n‖` (`masked_gain_requires_interaction`, `masked_gain_requires_residual`), instance [C sous `G′`] aux rangs hors du champ (`canonical_masked_exceedance_requires_residual`) ; [C] `T(a+k) − T(a) = Σ_{i<k}(T(a+i+1) − T(a+i))`, pas tous `> 0 ⟹` cumul `> 0`, cumul `> 0 ⇏` pas tous `> 0` (témoin `0, 0, 1`) ; [C] `Σ_{i<k}(W_{a+i} − W_{a+i+1}) = W_a − W_{a+k}`. Variations obligatoires mod 6 : [C] plancher par classe `g_r ≥ 6` (a = 0), `≥ 2` (a = 2), `≥ 4` (a = 4) (`primeGap_ge_classFloor`) ; [C] `L_r ≥ log(1 + plancher(a_r)/p_r)` ; [C] `|ΔΘ_z − ΔΘ_w| ≥ |T_z − T_w| log(1 + plancher/p_r)`, `ΔΘ_z + ΔΘ_w ≥ (T_z + T_w) log(1 + plancher/p_r)` ; [ND] obligation d'excès `¬ InsideField ⟹ (E_j − E_1) − 2(I_1 − I_j) > 0`, borne uniforme des sommes oscillantes, toute séparation minimale des hauteurs ; [N] E183 : progression normalisée `Σ ΔT/s(T)` min 1,16 / 2,09 / 7,98 / 9,86 (L = 3/4/10/12), planchers par classe atteints, parts médianes interne/externe/résidu 0,41/0,31/0,21 pour L = 12, `X_j ≤ 0` partout (antécédent faux). Retrait exact du premier membre (2026-10-08, section 20, 21 théorèmes, 186 au total ; E184) : [C] `R = c_1 + S`, `|R| ≤ B ⟹ −B − c_1 ≤ S ≤ B − c_1` et forme tronquée `S = S_N + ε_N` (résidu conservé ; marges de somme `2B` ; l'intervalle n'est pas `[−(B − |c_1|), B − |c_1|]`) ; [C] `partialRemainder 2 = R − c_1 = tailSum 1 N + partialRemainder (N+1)` ; [C] `D_1 = 2⟨R, c_1⟩ − ‖c_1‖²`, invariant par toute perturbation des autres membres ; [C] canal lissé : `∃ C, ∀ x > 1, |R̃(x)| ≤ C√x` (depuis `‖A(x)‖ ≤ Cx`), `S̃ = Σ_{n≥2} c̃_n` (HasSum), sommabilité absolue, `|ε̃_N(x)| ≤ Σ_{j≥N}|c̃_j(x)|`, `|c̃_j(x)| ≤ 2m√x/(‖ρ‖‖ρ+1‖)` pour `x ≥ 1` (par `β ≤ 1`) ; [C] `Σ_{a≤n<b} 2I_n = ‖r_a‖² − ‖r_b‖² − Σ E_n` ; [C] `D_n ≤ D_1 ⟺ (E_n − D_1)/2 ≤ −I_n` et, sous `D_n ≤ D_1`, `(E_n − D_1)/2 ≤ Σ_{n<j≤N}|⟨c_j,c_n⟩| + ‖r_N‖‖c_n‖` ; [ND] l'inverse strict à un rang hors du champ (inégalité exacte encore nécessaire), représentation et toute borne du canal brut ; [N] E184 : borne lissée tenue avec un facteur ≥ 946, résidus par différence, part calculable de la queue `2,7·10⁻³√x` (zéros 301–5000), perturbations hypothétiques sans violation de `D'_j ≤ D_1` (gain négatif du membre perturbé, compensation fournie par le reste dégradé). Lock (auteur, 2026-10-08, directive) : « Prouver que les contraintes arithmétiques et les interactions complètes empêchent toute contribution de dépasser le champ du premier zéro tout en maintenant la reconstruction exacte sur tout l'horizon. ». Réduction par le miroir (auteur, 2026-10-08 ; section 21, 22 théorèmes, 208 au total) : [C] `β₁ = 1/2 ⟹ (¬ InsideField(z₁, w) ⟺ β_w > 1/2 ∨ ‖ρ_w‖ < ‖ρ₁‖)` (`not_insideField_iff_upper_or_small` ; `upper_not_insideField`, `small_support_not_insideField`) ; [C] bande fine : `T₁ ≤ T_w ∧ ‖ρ_w‖ < ‖ρ₁‖ ⟹ β_w < 1/2 ∧ T_w² < T₁² + 1/4 ∧ T_w < T₁ + 1/(8T₁)` (`small_support_band`, `small_support_height_lt`), rangs canoniques : `T₁ < T_n` strict (`canonical_small_support_band`) ; [C] `β_w ≤ 1/2 ∧ T₁² + 1/4 ≤ T_w² ⟹ InsideField(z₁, w)` (`lower_captive_of_height`, `lower_captive_of_height_margin`, `canonical_lower_captive_of_margin`) ; [C] paire miroir hors ligne, `‖ρ₁‖ ≤ T_w` : `InsideField(z₁, w) ⟺ β_w < 1/2`, exactement un captif (`mirror_pair_captive_iff_lower`, `mirror_pair_exactly_one_captive`) ; [C] le miroir d'un rang de la bande est un rang haut (`band_rank_mirror_upper`) ; [C] `(∀ n ≥ 1, β_n ≤ 1/2) ⟺ RH` (`no_upper_canonical_iff_riemannHypothesis`) ; [C] `(∀ n ≥ 1, β_n > 1/2 → InsideField(z₁, z_n)) ⟺ ∀ n ≥ 1, β_n ≤ 1/2` (`upper_insideField_iff_no_upper`) ; [C] ancre ON ∧ chaque rang haut dans le champ ⟹ RH (`riemannHypothesis_of_upper_canonical_insideField`). Prémisse au miroir `G″ : ∀ n ≥ 1, β_n > 1/2 → D_n ≤ D_1` : [C] `G′ ⟹ G″` sous l'ancre (`gain_upper_of_restricted`) ; [C] RH ⟹ `G″` (`gain_upper_of_riemannHypothesis`) ; [C] ancre ∧ `G″` ∧ (`G″ ⟹ ∀ n, β_n > 1/2 → InsideField`) ⟹ RH (`riemannHypothesis_of_upper_gain_link`, composition) ; [C] le raccord ⟺ (`G″ ⟹ ∀ n ≥ 1, ¬ β_n > 1/2`) (`upper_gain_link_iff_refutation`) ; [C sous `G″`] `(E_n − D_1)/2 ≤ −I_n` à tout rang haut (`upper_gain_requires_interaction`). [ND] ce raccord : `D_n ≤ D_1` contredit à un rang haut par la reconstruction exacte. Tentative SANS la prémisse (2026-10-08) : conservée comme résultat TDD dans la cible séparée `RHV6FreshTDD` (non importée ; build principal vert) ; [ND] `riemannHypothesis_without_premise` : `β₁ = 1/2` seule, rang haut `n` supposé, but `⊢ False` ; [ND] forme composée `riemannHypothesis_without_premise_composed` : contexte succession, dépassement persistant lu par tout support, horizon exact, pas des contacts `A_n(p_{r+1})/A_n(p_r) = e^{(β_n − 1/2)L_r}`, planchers mod 6, retrait du premier, reconstruction lissée, interaction complète en série, queue `|R̃ − Σ_{j<N} c̃_j| ≤ Σ_{j≥N}|c̃_j|`, `|R̃| ≤ C√x`, lecture du pôle `β_n ≤ θ*`, `1/2 ≤ θ* ≤ 1` ; après composition par `β ≤ θ` (`radial_le_of_remainder_growth`), premier but réellement restant : `∃ θ < β_n, ∃ C, ∀ x > 1, ‖A(x)‖ ≤ C x^θ` ; acquis le plus proche `θ = 1` ([C] `smoothedRemainder_linear_growth`) ; écart : abaisser l'exposant démontré sous `β_n ≤ 1`, depuis les poids premiers (le membre haut impose `β_n ≤ θ*`) ; `θ* < 1` non dérivé (E152/E153). **Transmission du défaut** [C] (section 22, 18 théorèmes) : `r'_k = r_k − Δ`, `I'_k = I_k − ⟨Δ, c_k⟩`, `D'_k = D_k − 2⟨Δ, c_k⟩` (défaut du reste) ; insertion de deux membres distincts `d₁, d₂` aux rangs `p, p+1`, `Δ = d₁ + d₂`, rangs `k ≥ p ↦ k + 2` : `r'_{k+2} = r_k − Δ`, `I'_{k+2} = I_k − ⟨Δ, c_k⟩`, `D'_{k+2} = D_k − 2⟨Δ, c_k⟩`, `D'_1 = D_1` (`p ≥ 2`), `D'_p = 2⟨r_{p−1}, d₁⟩ − ‖d₁‖²`, `D'_{p+1} = 2⟨r_{p−1} − d₁, d₂⟩ − ‖d₂‖²`, `D'_p + D'_{p+1} = ‖r_{p−1}‖² − ‖r_{p−1} − Δ‖²`, résidu `r'_{N+2} → −Δ` sous la représentation ordonnée, `D'_{k+2} ≤ D'_1 ⟺ D_k − D_1 ≤ 2⟨Δ, c_k⟩`. **Ancre** : [N, externe] certifiée hors Lean (E185 : `N(15) = 1` Turing + Backlund, `Z` change de signe sur `[14.1, 14.2]` ⟹ plus bas zéro simple et ON) ; [ND] aucun terme Lean ; dépendance réelle, qui ne ferme pas le but TDD où l'ancre est accordée. E184 corrigée : deux membres distincts insérés, rangs décalés, identités [C] vérifiées sur 200 cas. Lock inchangé : « Prouver que les contraintes arithmétiques et les interactions complètes empêchent toute contribution de dépasser le champ du premier zéro tout en maintenant la reconstruction exacte sur tout l'horizon. ». **Directive en six points (auteur, 2026-10-08) et relecture E181–E185.** Ancre structurellement déduite [C sous `hU`] : `hU := ∃! w, T_w ≤ 15` ⟹ `T_{w*} = T_w ≤ 15` ⟹ `w* = w` ⟹ `1 − β_w = β_w` ⟹ `β_w = 1/2` ; aucun `u` avec `u ≺ w` (sinon `T_u ≤ T_w ≤ 15`, `u = w`, irréflexivité) ⟹ `w = z₁` (`canonicalMember_zero_precedes`) ⟹ `β₁ = 1/2` (`anchor_of_unique_band`) ; comptage `N⁺(T) := Σ_{ρ ∈ W⁺(T)} m_ρ`, `W⁺(T) = {ρ : ζ(ρ) = 0, 0 < Re ρ < 1, 0 < Im ρ ≤ T}` ; [C] `N⁺(T) = 1 ⟹ ∃! w, T_w ≤ T` et `m_w = 1` ; [C] `N⁺(15) = 1 ⟹ β₁ = 1/2` (`anchor_of_count_one`) ; [C] `W⁺(T) ∋ ρ ⟺ ∃ w, ρ = ρ_w ∧ T_w ≤ T` ; [C] convention ouverte `≤` fermée, égales sans zéro à la hauteur `T`. [ND] `N⁺(15) = 1` dans Lean (principe de l'argument certifié absent ; [N externe] E185). Insertion [C] : famille complète `Σ c_j → R`, famille insérée `Σ c'_j → R + Δ`, `Δ = d₁ + d₂` ; famille initiale et famille insérée reconstruisent le même reste `⟹ Δ = 0` ; `Δ ≠ 0 ⟹` la famille insérée ne reconstruit pas ce reste ; canal lissé : en toute abscisse `x > 1` (`smoothed_insertion_excluded_at`), et sur un support par une coordonnée `i` avec `(d₁ + d₂)_i ≠ 0` ; [C] non-annulation : points distincts `ρ_i`, `Im ρ_i > 0`, `Re ρ_i ≤ 1`, `κ_i ≠ 0`, `w_{i₀} ≠ 0` ⟹ `∃ x > 1, Σ_i w_i · 2 Re(κ_i x^{ρ_i}) ≠ 0` (unicité spectrale sur la famille doublée par les conjugués ; même hauteur permise) ; [C] paire miroir hypothétique `m₁ c(ρ) + m₂ c(ρ*)`, `m₁ > 0`, non identiquement nulle (brut `κ = −1/ρ`, lissé `κ = −1/(ρ(ρ+1))`, cas `ρ* = ρ` par `m₁ + m₂`) ; [C] insérée dans la famille lissée complète, elle ne reconstruit pas le reste en une abscisse. Portée : interdit une insertion supplémentaire dans une famille complète aux autres contributions conservées ; AVEUGLE à `β` (deux contributions ON insérées : même défaut, `insertTwo_not_reconstruct_onLine_pair`) ; n'exclut pas un membre OFF de la famille authentique. Complément [C] : `Σ c' → R` et `Σ c_ins → R + Δ` ⟹ `Σ (c' − c_ins) → −Δ` (mêmes canal, normalisation, coordonnées ; sur tout l'horizon par `∀ x > 1`) ; rigidité [C] : toute représentation spectrale (points injectifs, `Re ≤ 1`, localement finie, `Σ ‖w_i/(ρ_i(ρ_i+1))‖ < ∞`, noyau de Perron, égalité `∀ x > 1`) donne poids `0` à un point qui n'est pas un zéro et exactement `−m_z` à chaque membre : aucun complément de cette classe ne fournit `−Δ` ; [ND] une modification hors de cette classe ; l'unicité ne fixe pas `β_n` (TDD `ComplementRigidity`, but `β_n = 1/2`). Borne racine-log signée [C] : `R = c₁ + S`, `|R| ≤ C√x log x ⟹ −C√x log x − c₁ ≤ S ≤ C√x log x − c₁` ; instance lissée [C sous l'hypothèse `|Re A(x)| ≤ C√x log x`, ND] : `−C log x − c̃₁ ≤ S̃ ≤ C log x − c̃₁`. But analytique [ND] (TDD `UniformTail`) : `∃ θ < β_n, ∃ C, ∀ x > 1, ‖P_N(x)‖ + ‖ε_N(x)‖ ≤ C x^θ` (contrôle conjoint uniforme ; la convergence de la queue à `x` fixé et la borne linéaire normalisée n'y suffisent pas). [N] E186 : défaut d'insertion commun à la paire et au contrôle ON (`‖Δ_pair‖/‖Δ_ON‖` médian 1,05 → 1,35 selon le support), déformation propre `‖Δ_pair − Δ_ON‖/‖Δ_ON‖` croissante en `d` (0,002 → 5,2), compensation interne des chaînes 0,43 / 0,39 / 0,23 / 0,21 (L = 3/4/10/12, conservée dans l'analyse), annulation des cosinus de différence ≈ 1 sur les fenêtres de 12 et 0,05–0,5 sur les fenêtres de battement ≥ 1 demi-tour (observations, aucune borne uniforme), ajustement réel du complément non transportable d'un support à l'autre (résidu relatif > 1), multiplicités admissibles : CORRIGÉ (auteur, 2026-10-08) — les ajustements entiers essayés modifient effectivement des multiplicités (jusqu'à 157 membres), résidu relatif 0,17 sur le support d'ajustement, ≥ 1,05 hors de lui ; deux essais ne sont pas une recherche exhaustive. Directive en sept points (2026-10-08) : [C] `ξ₁(s) := s(1−s)Λ₀(s) − 1 = s(1−s)Λ(s)` entière, `ξ₁(1−s) = ξ₁(s)`, `ξ₁(0) = ξ₁(1) = −1` ; [C] `Im s ≠ 0 ⟹ ξ₁(s) = ζ(s)·s(1−s)Γℝ(s)`, facteur analytique non nul, `ξ₁(s) = 0 ⟺ ζ(s) = 0`, `ord_ρ ξ₁ = m_ρ` ; [C] zéros de `ξ₁` dans `(−1,2)×(0,T)` = fenêtre supérieure ouverte ; tout zéro de hauteur `> 0` vérifie `0 < Re < 1` ; [C] `ξ₁(σ) ≠ 0` pour `σ ∈ ℝ ∖ (0,1)` et sur `Re ∈ {−1, 2}` ; [C] `∮_{∂R} ξ₁ = 0` ; [C] `ζ(σ) ≠ 0`, `0 < σ < 1` (`riemannZeta_real_ne_zero_of_mem_Ioo`, par `RHV3Lean.thm_noRealZetaZeroInOpenUnitSegment` : `‖Λ₀(σ)‖ < 4 ≤ 1/σ + 1/(1−σ)`) ; [C] principe de l'argument `(2πi)⁻¹∮_{∂([−1,2]×[0,T])} ξ₁'/ξ₁ = Σ_{0<γ<T} m_ρ` sous `ξ₁ ≠ 0` au bord (`argument_principle_rect`, `completedEntire_argument_principle` : `∮ dz/(z−a) = 2πi`, factorisation `f = Π(z−ρ)^{m_ρ} g`, Cauchy pour `g'/g`) ; [ND] valeur `= 1` en `T = 15` et absence de zéro à la hauteur 15 (lemmes numériques ; E185 : certificats externes) ; [NC] `N(15) = 1`, l'ancre `β₁ = 1/2`, le miroir annulé et la domination ON du premier, composés depuis ces deux énoncés (cible de travail, obligation 1). [C] `|R| ≤ C√x log x ⟹ |R/√x| ≤ C log x` ; `R = c₁ + S, |R| ≤ B ⟹ −B/√x − c₁/√x ≤ S/√x ≤ B/√x − c₁/√x` ; [N] aucune borne `|R| ≤ C√x log x` n'est un théorème dans aucun canal du dépôt (acquis : linéaire, normalisée `C√x`). Cible de queue : `∃ θ < β_n, ∃ C, ∀ x > 1, ‖P_H(x) + S_H(x)‖ ≤ C x^θ` (somme, compensations conservées ; `‖P_H‖ + ‖S_H‖ ≤ C x^θ` retiré comme passage obligé) : énoncé conservé, hors de la cible de travail depuis le 2026-10-09 (audit §23). [ND] captivité universelle `∀ w, ∀ x ≥ 1, A_w(x) ≤ A_1(x)` COMPOSÉE sous l'ancre : rangs ON, bas et bande fine fermés par théorèmes, reste `β_w > 1/2 ⟹ False` (cible de travail, obligation 2) ; [NC] chaîne unique ancre → captivité → `∀ w, β_w = 1/2` → RH → aucun changement de régime → tout passage vertical (`riemannHypothesis_terminal`, conditionnel aux deux obligations ; aucun terme terminal). E187 : identités ON exactes sur 299 passages, `|φ_s − φ|` médian 1,566 rad (contacts bruts ≠ contacts lissés), `I_n` invariant par troncature (écart max ~1e−13), grammaire entière vérifiée (transitions AA 233 / AB 377 / BA 378 / BB 238 sur `p ≤ 10⁴`), annulation médiane du terme de différence 1,000 sur fenêtres 12/24/36 et 0,71 / 0,15 / 0,13 sur plages de battement 1/2/4 demi-tours (chaînes de 12), hauteur commune : `cos Δφ ≥ 0,999996`, seul le battement de somme compense (0,11–0,22 par fenêtres 12/24/36). | | | | | | | | | | | | | | |
| Persistance | Théorème conditionnel à une loi de transmission universelle (`engaged_persists_to_infinity`, §11, [ND] pour la loi). |
| RH | Fermeture conditionnelle à la transmission et à une amorce couvrant le début de l'énumération (`riemannHypothesis_iff_conservation_and_base`, §11). |
| Déficit de comptage et saturation ON (auteur, 2026-10-09 ; `Terminal/CountingDeficit.lean`) | [C] fenêtre supérieure fermée `0 < Im ρ ≤ T` ; `N(T) = Σ m_ρ`, `N₀(T) = Σ_{Re ρ = 1/2} m_ρ`, `W(T) = Σ_{Re ρ < 1/2} m_ρ`, `W⁺(T) = Σ_{Re ρ > 1/2} m_ρ` ; `N = N₀ + W + W⁺` ; réflexion `ρ ↦ 1 − ρ̄` : zéro non trivial, `Im` conservé, `Re ↦ 1 − Re`, `m_{1−ρ̄} = m_{ρ̄} = m_ρ` ⟹ `W = W⁺` ; `N = N₀ + 2W`, `N₀ ≤ N`, `(N : ℤ) − N₀ = 2W ≥ 0` ; `T ≤ U ⟹ W(T) ≤ W(U)` ; `W(T) = 0 ⟺ ∀ z, T_z ≤ T → β_z ≥ 1/2` ; `N(T) = 1 ⟹ N(T) = N₀(T)`. [C] fermeture CONDITIONNELLE : `N(H) = N₀(H)` ∧ `∀ U > H, N₀(U) − N₀(H) ≥ N(U) − N(H)` ⟹ `0 ≤ 2(W(U) − W(H)) ≤ 0` ⟹ `W ≡ 0` ⟹ aucun membre bas ⟹ (miroir) aucun membre hors ligne ⟹ RH ; elle vérifie que l'obligation suffit, ne la démontre pas. [⟺RH] RH ⟹ prolongement. [C] `¬ prolongement ⟺ ∃ z, H < T_z, β_z < 1/2` ; `β_w > 1/2`, ancre ON ⟹ `∃ k ≥ 0, A_1 < A_w(C_k)`, `C_k = e^{(φ + kπ)/T} → ∞` ; sous l'ancre : prolongement ⟺ aucun membre haut. [ND] inégalité de prolongement (obligation 2 de la cible de travail, `counting_extension_fifteen`, depuis la saturation certifiée `N(15) = N₀(15)`, elle-même conditionnelle à `N(15) = 1`). `N₀` compte des zéros ON avec multiplicité, pas des changements de signe. |
| Pas de comptage et deux premières bandes (2026-10-09 ; `Terminal/CountingDeficit.lean` §6) | [C] `N₀` croissant ; `N ≡ N₀ (mod 2)` ; `W(T) = 0 ⟹ ∀ w, T_w ≤ T → β_w = 1/2 ∧ w* = w` (côté haut exclu par son miroir bas) ; `T ≤ U, W(T) = 0, N(U) < N(T) + 2 ⟹ W(U) = 0` ; `(∀ U > H, W(U) = 0) ⟹` prolongement depuis `H` ; `N(15) = 1 ∧ N(22) = 2 ⟹ W(22) = 0`, `β₁ = β₂ = 1/2`, miroirs annulés, `15 < T₂ ≤ 22`, tout membre de hauteur `≤ 22` ON. [ND] les valeurs `N(15) = 1`, `N(22) = 2` (numériques, E185 externe pour la première). Le pas de comptage certifie des bandes FINIES ; il ne dérive pas le prolongement (⟺ RH). |
| Réduction de la transmission à la borne du reste (2026-10-09, interdiction levée ; `Terminal/DemonstrationChain.lean`) | [C] sous `∀ w, T_w ≤ H → β_w = 1/2` : `‖P_H(x)‖ ≤ B_H·√x` (`precedingSum_le_budget_of_onLine`) ; `R = P_H + F_H` ; `‖R‖ ≤ C√x ⟹ ‖F_H‖ ≤ (C + B_H)√x` ; `‖F_{T_e}‖ ≤ C√x ⟹ β_l = 1/2` (lecture du pôle) ; coût de rupture `N(T_e) + 2 ≤ N(T_l)` sous `β_l < 1/2`. [⟺RH] but affiché de [3] : `∃ C, ∀ x > 1, ‖smoothedRemainder x‖ ≤ C√x` (`riemannHypothesis_iff_remainder_sqrt_growth`) ; forme en comptage `N(T_l) < N(T_e) + 2`. [C] exposant 1 seulement (`smoothedRemainder_linear_growth`). [ND] l'exposant 1/2 depuis `Λ`. |
| Progression du fond et modulation par cellule (auteur, 2026-10-09 ; `Terminal/BackgroundModulation.lean`, E188) | [C] `b_ρ(x) = −2Re Ei(ρ log x)`, `b_ρ' = −2x^{β−1}cos(T log x)/log x`, `b_ρ'/li' = −2x^{β−1}cos(T log x) = c'(x)`, `c = −2Re(x^ρ/ρ)` (canal brut) ; `|b_ρ'/li'| ≤ 2x^{β−1} → 0` pour tout `β < 1` (aveugle au régime) ; échelle ON `(b_ρ'/li')/x^{−1/2} = −2x^{β−1/2}cos`, enveloppe plate ⟺ `β = 1/2` [C, caractérisation] ; `D_k = e^{(π/2+kπ)/T}`, `log(D_k/C_k) = arctan(β/T)/T` ; `|Δb_{ρ,k}| ≤ 2C_k^{β−1}Δli_k`. [N] collectif : `dJ = dψ/log t` ⟹ par sommation partielle `J − li` et `ψ − x` ont le même exposant de croissance (au facteur `log` près) : l'hypothèse « variations rapportées au fond, à l'échelle ON, sans masquage durable » est la borne `θ* = 1/2` [⟺RH] du but [3], non une obligation plus faible. E188 : rapport de cellule max 0,636 (≈ 2/π), pentes ζ fond −0,5 / ON 0, `W_δ` fond `δ − 1/2` / ON `+δ` ; résidu aux événements premiers peu réduit par 300 zéros (troncature) ; `B − |b_1|` violée 14/4000. |
| Étages `k = n` et attendu de la fibre suivante (auteur, 2026-10-10 ; `Terminal/StageCell.lean`, E189) | [C] `u_n = (arctan(T_n/β_n) + nπ)/T_n`, `W_n = π/T_n`, `C_n^± = e^{u_n}, e^{u_n+W_n}` ; `L_n = ∫_{u_n}^{u_n+W_n} e^v/v dv = li(C_n^+) − li(C_n^-)` ; avant `1` : `W e^{u+W}/(u+W) ≤ L ≤ W e^u/u` ; après : `W e^u/u ≤ L ≤ W e^{u+W}/(u+W)` ; traversant : `eW ≤ L ≤ W max(·,·)` ; toujours `L ≥ eW` ; `D_k ∈ ]C_k, C_{k+1}[` ; `|Δb_{ρ,k}| ≤ 2e^{(β−1)u_k}L_k` ; `L/a = L√(T²+1/4)`, `L/a² = L(T²+1/4)` ; canal lissé : `F_{]H,H']} = R − P_H − Q_{H'}`, `‖Q_H‖ ≤ budget(H)·x`, `budget(H) → 0`, historique ON jusqu'à `H` ⟹ `‖F‖ ≤ Cx + B_H√x + budget(H')x` ; `‖F‖ ≤ Cx^θ ⟹ β ≤ θ` sur la fibre ; [ND] `‖R − Q_{T_l}‖ ≤ C√x` (but [3], ⟺ fibre de `T_l` ON sous l'historique) ; [NC] formule explicite de `J` (transport de l'attendu vers `J`) ; [N] E189 |
| Fenêtres communes, queue conjointe, portée de la coupure fixée, singularité de l'inversion (relecture de l'auteur, 2026-10-10 ; `Terminal/StageCell.lean` §6, `Terminal/TangentialInversion.lean`, E189 corrigée) | [C] `‖Q_H(b) − Q_H(a)‖ ≤ budget(H)(a + b)` ; `H ≤ H' ⟹ ‖Q_{H'}(x)‖ ≤ budget(H)·x` ; `(∀ σ, H < |Im σ| → ‖Σ_r λ_r x_r^σ‖ ≤ M) ⟹ ‖Σ_r λ_r Q_H(x_r)‖ ≤ budget(H)·M` (une seule série pour toutes les fenêtres) ; `Σ_r λ_r (R − P_H)(x_r) − Σ_r λ_r F_{]H,H']}(x_r) = Σ_r λ_r Q_{H'}(x_r)`, bornée par `budget(H')·M` ; historique ON jusqu'à `H` : `‖ΔF‖ ≤ ‖ΔR‖ + B_H(√a + √b) + budget(H')(a + b)` ; `budget(H) > 0 ⟹ ¬∃ C, ∀ x > 1, budget(H)·x ≤ C√x` (la limite `budget → 0` est en la coupure, pas en `x`) ; au contact `tan θ = T/β ≠ 0`, donc `sin θ ≠ 0`, `cos θ ≠ 0`, `β = T cos θ / sin θ` : singulière aux zéros de `tan`, nulle aux pôles (exclu) ; [ND] toute borne de `Q_{T_l}` d'exposant `< 1`, ou `M < Σ|λ_r| x_r` démontré (répartition des hauteurs de la queue) ; [N] E189 corrigée (26 PASS, 0 FAIL) : prédicteur lié `(β, T)` sur fenêtres de l'historique (cellule du membre engagé, 12/24/36 événements), seuil démontré `S_up(T)·x` avec `S_up(T) = 4∫_T^∞ N_up/t³` (Rosser, externe) : couverture 299/299, aucune réduction (19000/19000 paires, largeur `T` = toute la plage, `β ∈ [0,05 ; 0,5]`), `τ_cert/nécessaire` médian 431,6 (cellule) → 21,8 (36 événements) ; queue mesurée ≤ 0,10 de `τ_cert` ; budget mesuré 0,52–0,65 de `S_up` ; filtre conjoint : 0 exclusion de plus, `M_sup/M_triv = 1,0000` ; canal `J` (mesure seule) : `|ΔQ_après|/|ΔF|` médian 1,8–4,2 |
| Couche grammaticale finie sur un petit ensemble de Tours (auteur, 2026-10-10 ; `Terminal/FiniteGrammarLayer.lean`, E190) | [C] `F = fibre ]H, H']` (membres consécutifs, miroirs, multiplicités) ; par événement `Y_r := ΔR_r − ΔP_{H,r} = ΔF_r + ΔQ_{H',r}` ; par fenêtre `Σ_{r<m} Y_r = (F(x_m) − F(x_0)) + (Q(x_m) − Q(x_0))` ; `‖Σ ΔQ_r‖ ≤ budget(H')(x_0 + x_m)` ; discriminabilité `2τ < ‖F₁ − F₂‖ ⟹ ¬(‖Y − F₁‖ ≤ τ ∧ ‖Y − F₂‖ ≤ τ)` ; `‖Y − G‖ ≤ budget·x ⟹ ‖F_vraie − G‖ ≤ 2·budget·x` (et forme conjointe `budget·M`) ; `x^{−d} + x^{d} = 2 + κ(x,d) ≥ 2 + (d log x)²` ; `m` pair, `p_n > 3` : `κ(p_{n+m}/p_n, d) ≥ (d log(1 + 3m/p_n))²` ; [ND] l'admissibilité du profil ON de l'arrivée (⟺ but [3]) ; toute borne du complément d'exposant `< 1` ; [N] E190 |
| Ancre et trois premiers zéros aux coupures d'E176 (auteur, 2026-10-10 ; `Terminal/CountingDeficit.lean` §7, chaîne) | [C] `N(a) ≤ k ∧ N(a) < N(b) ⟹ T_{k+1} ∈ ]a, b]` ; `N(c₀..c₃) = 0, 1, 2, 3 ⟹ T₁, T₂, T₃` dans leurs tranches, `β = 1/2`, miroirs annulés, tout `T_w ≤ c₃` ON ; `N(a) = N(b) ⟹` aucun membre dans `]a, b]`. [N] E176 (commit 02bd2b09, Arb, externe) : `N(14, 15, 17, 23, 28) = 0, 1, 1, 2, 3`. [ND] vérificateur Lean : `Re ζ(σ + 15i) > 0` sur `[1/2, 2]` et `θ(15)/π + 1 ∈ ]1/2, 3/2[` avec réduction de l'intégrale de bord (buts [1], [2]) |
| Ancre, attaque par le début (auteur, 2026-10-10) | [C] `‖ζ(s) − main_N(s)‖ ≤ ‖s‖‖s+1‖/12·(N^{−σ−2} + N^{−σ−1}/(σ+1))`, `σ > 0` ; [C] `‖σ+15i‖‖σ+16i‖/12·(10^{−σ−2} + 10^{−σ−1}/(σ+1)) < ‖main_10(σ + 15i)‖` sur `[1/2, 1[` (marge 0,031) ⟹ aucun zéro à la hauteur 15 ; [C] rectangle de `Re > 0` : `∮ ξ₁′/ξ₁ = ∮ ((1−s)ζ)′/((1−s)ζ)` (Γ éliminé) ; [C] `∮_{B₁} = 2πi`, `∮_{B₂} = 0`, `ζ ≠ 0` sur les bords ⟹ `Σ_{0<Im ρ<15} m(ρ) = 1` ; [ND] ces quatre faits numériques sur ζ (marges observées 0,22 et 0,18) |
| Dominance du premier zéro (auteur, 2026-10-10) | [C] étage `D(z,w)` : Tour normalisée de `w` symétrique, `T_z ≤ T_w`, `π/T_w ≤ π/T_z`, `r_w(x) ≤ r_z(x)` pour tout `x > 0`, contacts `C_k(w) < C_k(z)` pour tout `k ≥ 1` si `T_z < T_w` ; [C] `β_z = β_w = 1/2`, `T_z ≤ T_w` ⟹ `D(z,w)`, strict si `T_z < T_w` ; [C] `D(z,w)` ⟹ `β_w = 1/2` ; [C] composition ; [C] ancre ⟹ `D(z₁, w)` pour tout `w` ON ; [C] pas qui monte : `T_e < T_l`, `π/T_l < π/T_e`, emboîtement à l'infini, toute position radiale ; [C] `β_l < 1/2` ⟹ `¬D(e,l)`, miroir hors du champ du premier ; [ND] `D(e,l)` ou `InsideField z₁ l*` pour l'arrivée (⟺ arrivée ON) |
| Captivités sans supposer l'arrivée ON (correction de l'auteur, 2026-10-10) | [C] pas `p : e → l` : `Occ(l) = p_min(e)`, `C⁻(l) < p_min(l) ≤ C⁺(l)` (43d5fbfd, restauré) ; [C] `T_e < T_l`, `T_l ≥ 2` ⟹ `‖Z_l(M)‖ ≤ ‖Z_e(M)‖` au premier partagé (e586d8dd) ; [C] `β₁ = 1/2`, `x ≥ 1`, `√x‖ρ₁‖ ≤ ‖ρ_l‖` ⟹ `‖Z_l(x)‖ ≤ ‖Z₁(x)‖`, toute `β_l` (9aecca85) ; [C] `‖ρ₁‖ ≤ T_l` ⟹ `l` ou `l*` dans le champ ; [C] pas qui monte, `‖ρ₁‖ ≤ ‖ρ_l‖` (en particulier `T₁² + 1/4 ≤ T_l²`) ⟹ `l` dans le champ sur `x ≥ 1` ; [C] emboîtement à l'infini (70c35dc0) ; [C] domination individuelle sous gain et interaction explicites (0cb8cd68) ; portée : valent pour un membre bas, n'excluent pas `β_l < 1/2` ; [ND] captivité du miroir `l*` |
| Réalignement sur les acquis (auteur, 2026-10-10 ; chaîne `Terminal/DemonstrationChain.lean`) | [C] `canonical_onLine_step` : deux membres canoniques consécutifs ON, passage qui monte, `T ≥ 2` ⟹ `π/T_{m+1} < π/T_m`, rang `+ 1`, `p_min(m) = Occ(m+1)`, `λ_{m+1} = 1`, contacts emboîtés à l'infini, `‖Z_{m+1}(x)‖ ≤ ‖Z_m(x)‖` pour tout `x > 0`. [C] `first_three_members_geometry` (comptages `N(15) = 1`, `N(22) = 2`, `N(28) = 3` démontrés, 2026-10-11) : pour `j < 3`, Tour normalisée symétrique, `z_j* = z_j`, `r_j(x) = r(T_j) = 1/√(T_j² + 1/4)` constant, `r(T_2) < r(T_1) < r(T_0)`, `A_{j+1}(x) < A_j(x)`, passages 0 et 1 qui montent, et le pas canonique ci-dessus aux deux passages. [ND] (V1) `‖σ + 15i‖·10000^{−σ}/σ < ‖main_10000(σ + 15i)‖` sur `[1/2, 1[` ; (V2) `(2πi)⁻¹∮ ξ₁'/ξ₁ = 1` sur `∂([−1, 2] × [0, 15])` : buts ouverts, aucun paramètre (signatures historiques rétablies). Transmission [ND] : `False` sous `β_l < 1/2` ; contexte complété par symétrie, quatre secteurs, enroulement symétrique, régime, événement, anneaux, champ du premier ; chacune vaut pour toute position radiale de l'arrivée |
| Retrait certifié et estimation du retrait (auteur, 2026-10-11 ; `Terminal/CertifiedRemoval.lean`) | [C] `P_28 = Σ_{|Im ρ| ≤ 28} −m x^ρ/(ρ(ρ+1))` (trois premiers membres et conjugués, exacts), `‖P_28(x)‖ ≤ budget(28)·√x` ; `Σλ_r (R − P_28 − fibre]28,H])(x_r) = Σλ_r (R − P_H)(x_r) = groupe d'arrivée + complément` ; [C] `β_z < 1/2`, `θ < 1 − β_z`, `∀ fenêtre, ‖Σλ_r (R − P_28)(x_r)‖ ≤ C Σ|λ_r| x_r^θ ⟹ False` (miroir lu par le reste, `max(θ, 1/2) < 1 − β_z`) ; [C] arrivée de hauteur `≤ 28` ⟹ ON (cas fermés). [ND] l'estimation elle-même ; elle contient les fenêtres à un point, donc `‖R − P_28‖ ≤ C x^θ` sur tout `x > 1` ; sous l'historique ON, ⟺ aucun zéro de hauteur `> 28` au-delà de `θ` (`prime_blocks_iff_future_zero_free`, même nature). |
| Comparaison de fenêtres (auteur, 2026-10-11 ; E197 ; `Terminal/WindowComparison.lean`) | [C] `P_{h_K} − P_{h_0} = Σ_{i<K} fibre]h_i,h_{i+1}]`, `R − P_{h_0} = Σ fibres + Q_{h_K}` ; `Σλ(R − P_H) = Σλ fibre]H,H'] + Σλ(R − P_{H'})` ; [C] membres de `]H,H']` ON ⟹ `‖fibre]H,H'](x)‖ ≤ fiberBudget·√x` ; [C] historique ON jusqu'à `H ≥ 28` : estimation de `R − P_H` d'exposant `θ` ⟹ estimation de `R − P_28` d'exposant `max(θ,1/2)`. [N] E197 (5000 zéros, début/suite/milieu/fin, 12/24/36) : identités à 1,6e−15, enveloppe du groupe ∝ `m/T²`, part du groupe 0,98 → 0,05–0,20, `max|R − P_28|/√x ≤ 0,0101`, complément de fin entièrement résiduel. [ND] estimation de `R − P_{H_w}` (groupe d'arrivée + complément) d'exposant `θ < 1 − β_l`. |
| Incréments d'une transmission (auteur, 2026-10-11 ; E198 ; `Terminal/TransmissionIncrements.lean`) | [C] `ΔR = ΔS − ΔB` ; `ΔR = ΔP_{T_e} + Δfibre]T_e,T_l] + ΔQ_{T_l}` (consommé + groupe suivant + complément) ; `Δ(R − P_H) = ΔQ_H`, `‖Δ(R − P_H)‖ ≤ budget(H)(a + b)` ; incrément consommé télescopé. [N] E198 (300 zéros, 299 transmissions, 831 fenêtres 12/24/36) : médiane `|ΔP_e|/|ΔR|` 0,994, `|ΔG + ΔK|/|ΔR|` 0,054 ; signe du groupe en `M` = phase du lissé (`cos(T log M + arg(−1/(ρ(ρ+1))))`), aucune famille grammaticale ne le décale ; contact brut ≠ extremum du lissé (`(β+1)/|ρ+1|`) ; canal de comptage séparé (`Δli` ≈ `Δπ` à ±1). [ND] `‖ΔQ_H‖ ≤ C(√a + √b)` (forme incrémentale du but à `θ = 1/2`). |
| Exposant du retrait (auteur, 2026-10-11 ; `Terminal/RemovalExponent.lean`) | [C] `Σλ_r(R − P_H)(x_r) = Σλ_r Q_H(x_r)` ; zéros au-dessus de `H` sous `θ` ⟹ `‖Σλ_r(R − P_H)(x_r)‖ ≤ budget(H)·Σ|λ_r|x_r^θ` ; réciproque par lecture du pôle ; exposants admissibles du retrait = majorants des parties réelles au-dessus de `H` ; `H < T_z` ⟹ `max(β_z, 1 − β_z) ≤ θ`. [⟺] bande sans zéro au-dessus de `H_w` avec `θ < 1 − β_l` (contient le miroir de l'arrivée) : VOIE SUFFISANTE conservée, plus le but de la transmission (correction de l'auteur, 2026-10-11). [ND] tout exposant `< 1` (seul `θ = 1` acquis). |
| Cible de la transmission rétablie et obligations collectives (auteur, 2026-10-11 ; E199) | Cible : depuis l'historique ON, `β_l = β_e` ; dans le cas bas, `False` sous `β_l < 1/2`, construit depuis les obligations du passage et de la reconstruction. [C] fenêtre canonique : `M^Z(n₀+k) = p_{n₀+k}`, succession, consécutivité, `Σ_{k<m}(p_{n₀+k+1} − p_{n₀+k}) = p_{n₀+m} − p_{n₀}`, fenêtres adjacentes réunies sans omission ni double compte ; fibres contiguës, finies, complétées aux bords, stables par le miroir ; `Σ_{n∉S} c̃_n = R̃ − Σ_{n∈S} c̃_n` pour tout groupe fini `S`. [C] `A_{i,r} = g_i(x_{r+1}) − g_i(x_r)` : `Σ_r A_{i,r} = Δ_K g_i`, `Σ_i A_{i,r} = ΔR_r`, total commun, `|ΔR_total| ≤ Σ_r|ΔR_r| ≤ Σ_rΣ_i|A_{i,r}|`. [C] `2Re(w e^{(β+iT)u}) = 2‖w‖e^{βu}cos(Tu + arg w)` ; `Δv = −A(a)(cos(Tb+α) − cos(Ta+α)) − (A(b) − A(a))cos(Tb+α)`, `|Δv| ≤ |A(a)|·min(2, |T||b−a|) + |ΔA|` ; `cos(Tb+α) − cos(Ta+α) = −2 sin(T(a+b)/2+α) sin(T(b−a)/2)` ; sous `β = 1/2` (hypothèse) incrément normalisé sans terme d'enveloppe ; `Δ(√x v) = √b Δv + (√b − √a)v(a)` ; `(q−p)/log q ≤ ∫_p^q dt/log t ≤ (q−p)/log p`. Toutes vraies pour toute position radiale. [N] E199 : télescopages à 5e−16, `χ_H` 0,10–0,999, `η` médian 0,23–0,75, 47/378 colonnes `η < 0,1`, η croît avec la magnitude de l'écart, sensibilité N = 300 → 5000 ≤ 0,1 sur η. [ND] énoncé lu sur ces objets qui soit faux sous une première rupture basse. |
| Compensation sur une fenêtre grammaticale authentique (auteur, 2026-10-11) | Fenêtre `x_r = p_{n₀+r}`, `g_r = p_{n₀+r+1} − p_{n₀+r}`, `λ_r = g_r x_r^{−iT_l}`, `L_λ(f) = Σ_r λ_r f(x_r)`, `Y = R − P_H`, `F` = fibre `]H, T_l]`, `Q = Q_{T_l}`. [C] `L(Y − F) = L(Q)` : `|L(Q)| ≤ B` et `|L(Y − F)| > B` sont contradictoires (vérification de composition ; elles portent sur le même nombre). [C] `L(Y) = Σ_{n<p_{n₀+m}} Λ(n)Φ_λ(n) − L(fond) − L(P_H)`, `Φ_λ(n) = Σ_{r : n<x_r} λ_r(1 − n/x_r)`. [C] `L(F) = Σ_σ w_σ Σ_r λ_r x_r^σ`, `w_σ = −m_σ/(σ(σ+1))`, fibre complète ; passage consécutif ⟹ `|Im σ| = T_l` sur la fibre ; `Im σ = T_l` : `λ_r x_r^σ = g_r x_r^{β_σ}` ; `Im σ = −T_l` : `g_r x_r^{β_σ} x_r^{−2iT_l}` ; `β(β+1) < T² ⟹ Re w_σ ≥ 0` ; `Re(moitié supérieure) ≥ Re w_l·Σ g_r x_r^{β_l}`. [C] `‖L(Y)‖ + budget(T_l)Σ g_r x_r + ‖moitié conjuguée‖ < Re w_l Σ g_r x_r^{β_l} ⟹ False` ; cette inégalité exige `budget(T_l) < ‖w_l‖`. [ND] majoration non triangulaire de `L(Q)` (somme oscillante complète) ; majoration de la moitié conjuguée et de `L(Y)` sous la minoration supérieure. |
| Fenêtre grammaticale, ordre correctif (auteur, 2026-10-11) | La séparation précédente est une condition SUFFISANTE [ND], pas une solution acquise. [C] `‖Σ_r λ_r Σ'_σ w_σ x_r^σ‖ ≤ Σ'_σ ‖w_σ‖·‖Σ_r λ_r x_r^σ‖ ≤ (Σ'‖w‖)·Σ_r |λ_r| x_r` (B_Q, B_P, phases gardées en `r`) ; trois objets : `Re(sup) ≥ U`, `Re F ≥ U − B_L`, `‖Y − F‖ = ‖L(Q)‖ ≤ B_Q` ; composition générale `B_Y + B_Q + B_L < U ⟹ False` (triangulaire : `B_Q =` marge) ; miroir `ρ*_l = 1 − ρ̄_l` dans la fibre, `Im = T_l`, `Re = 1 − β_l`, `m* = m`, `ρ*_l ≠ ρ_l` sous `β_l < 1/2` ; `Re(sup) ≥ Re w_l Σ g p^{β_l} + Re w_{l*} Σ g p^{1−β_l}` ; fenêtre `n₀ = index(l)`, `p_{n₀} = p_min(e) = Occ(l)`, `n₀ ≥ 3`, `g_r = 6a_r + c_r`, `g_r ≥ plancher(c_r)`, alternance, `Σ g = p_{n₀+m} − p_{n₀} ≥ 3m` (`m` pair) ; `Σ g p^β ≥ p_{n₀}^β (p_{n₀+m} − p_{n₀})` ; `L(Q_{T}) = Σ'_σ w_σ Σ_r g_r p_r^{σ − iT}`, `Q_{T} = fibre]T, H''] + Q_{H''}`. Réduction [C] : `∃ m, ‖Σ_{n<p_{n₀+m}} Λ(n)Φ_λ(n) − L(fond)‖ + B_P + B_Q + B_L < Re w_l Σ g p^{β_l} + Re w_{l*} Σ g p^{1−β_l} ⟹ False`. Antécédent [ND] : but résiduel du build (échec de cette tentative, aucune impossibilité générale). |
| Comparaison signée (auteur, 2026-10-11) | La réduction en normes perd les compensations. [C] `Re L(Y) = Σ_{n<N} Λ(n)·Re Φ_λ(n) − Re L(fond) − Re L(P_H)`, `Re Φ_λ(n) = Σ_{r: n<p_r} g_r cos(T_l log p_r)(1 − n/p_r)`, `L(P_H) = Σ'_σ w_σ^H Σ_r λ_r p_r^σ`, `Re Σ' lower = Σ' Re(w_σ Σ_r g_r p_r^{β_σ} p_r^{−2iT_l})` ; [C] `Re L(Y) − Re(lower) + B_Q < U ≤ Re(upper) ⟹ False` ; [C] séparation en normes ⟹ comparaison signée. [C] pour tout `m`, membre de gauche `= Re(upper) + Re L(Q) + B_Q ≥ U` : la comparaison est renversée, le but `:390` équivaut à `False` dans le contexte (de même pour la séparation en normes). |
| Réalignement (auteur, 2026-10-12) | Cible = conservation du régime engagé. Aucune séparation signal–compensation, comparaison de fenêtre ni estimation globale n'est imposée comme dernier pas [retiré] ; lemmes fermés conservés [C]. But : `False` sous la première rupture (historique ON, départ ON, passage consécutif qui monte, `β_l < 1/2`) [ND]. Conséquences [C] : miroir `1 − ρ̄_l` distinct à hauteur `T_l` (consécutivité immédiate [NC]), `λ > 1`, facteur de pas `e^{(β_l−1/2)π/T_e} ≠ 1`, passage sortant de même hauteur. Obligations [C] (toute arrivée `β_l ≤ 1/2`) : rang + 1, premier partagé, `1 ≤ λ < e^{1/(2T_l²)}`, contacts = ligne × λ, cinématique de l'étage, grammaire de la fenêtre, reconstruction exacte. Aucune confrontation ne ferme. |
| Contrôle TDD (auteur, 2026-10-12) | `λ_l = 1` ∧ `λ_l > 1` (rupture) ⟹ `False` [C, contrôle conditionnel] : l'égalité suffit. Obligation : `λ_l = 1` depuis le passage (départ ON, montée, historique ON) [ND] ; acquis `1 ≤ λ_l < e^{1/(2T_l²)}` [C] ; `λ = 1 ⟺ β = 1/2` [C, caractérisation]. |
| Composition de comptage (auteur, 2026-10-12) | [C] `W(T_e) = 0` (historique ON) ∧ `N(T_l) < N(T_e) + 2` ⟹ `W(T_l) = 0` ⟹ arrivée ON (réflexion) ⟹ `λ_l = 1` ; [C] `N(T_l) = N(T_e) + fibre(T_l)` sur tout passage qui monte (consécutivité) ; pas `< 2` ⟺ fibre d'arrivée = un point simple ; `β_l < 1/2` ⟹ `fibre(T_l) ≥ 2`. Obligation : `N(T_l) < N(T_e) + 2` depuis le passage [ND] ; la consécutivité ne borne pas la fibre. |
| Trois hypothèses de travail sur la fibre d'arrivée (auteur, 2026-10-12) | [C] `λ = e^{(arctan(T/β) − arctan 2T)/T}` ; [C] `∀ β ∈ ]0,1/2]` : fenêtre de phase, `1 ≤ λ < e^{1/(2T²)}`, contacts = ligne × λ (H1 : obligations satisfaites par toute grille décalée) ; [C] grille de ligne ⟺ `β_l = 1/2` ; [C] `β = T cot(arctan 2T + kπ + T log λ)` ; [C] rang + 1 et premier partagé sur le passage de même hauteur parti d'un membre bas (H2 : une unité par membre, pas par hauteur) ; [C] `card fibre ≥ 2` sous la rupture ; [C] pas < 2 ⟺ ON ∧ unique à sa hauteur ∧ simple ; [C] double ON : `λ = 1` ∧ pas ≥ 2 (H3 : simplicité exigée par le sous-but, non par RH). Pas `N(T_l) < N(T_e) + 2` [ND]. |
| Comparaison directe au premier zéro par les contacts (auteur, 2026-10-12) | [C] `log(C_{l,k}/C_{w,k}) = log λ_l − log λ_w + h(T_w, T_l, k)`, `h = (arctan(2T_l) + kπ)/T_l − (arctan(2T_w) + kπ)/T_w` ; vers un membre en ligne : `log λ_l + h` (déplacement radial `log λ_l ≥ 0`, nul ⟺ en ligne ; hauteur ; contacts fixes) ; [C] `h = kπ(1/T_l − 1/T_w) + (arctan(2T_l)/T_l − arctan(2T_w)/T_w)`, strictement décroissant en `k`, `< 0` pour `k ≥ 1` (et `k ≥ 0` si `T_w ≥ 1/2`) ; [C] `C_{l,k} < C_{w,k} ⟺ log λ_l < −h` ; [C] `C_{l,k} ≤ C_{w,k} ∧ h ≥ 0 ⟹ λ_l ≤ 1` (avec `λ_l ≥ 1` : `= 1`), et `h ≥ 0 ⟹ k ≤ 0` (`k < 0`, `C_{l,k} < 1` si `T_w ≥ 1/2`), où `λ_l = 1 ⟹ ¬ C_{l,k} < C_{w,k}` ; [C] `λ < e^{1/(2T²)} ∧ 1/(2T²) ≤ −h ⟹` ordre ; [C] `∀ T > T₁ ≥ 1/2, ∃ β ∈ ]0,1/2[, λ(β,T) > 1 ∧ ∀ k ≥ 0, C_k(β,T) < C_k^{ligne}(T₁)` (et `k ≥ 1` pour tout `0 < T₁ < T`). Borne supérieure `λ_l ≤ 1` par les contacts [ND] : aucune ; aucune marge n'intervient. |
| Restitution des cellules et des passages, E202 (auteur, 2026-10-12) | [C] charge `Σ_{a<n≤b} Λ(n)` additive ; `a ≤ a' ≤ b ≤ b' ⟹ ch(a',b') = ch(a,b) − ch(a,a') + ch(b,b')` ; `β ≤ 1/2 ⟹ k_β(q) ∈ {k_ON(q), k_ON(q) − 1}`, `k_β(q) = k_ON(q) ⟺ −D/π < pos_ON(q) − (⌈pos_ON(q)⌉ − 1)` ; famille finie : `∀ᶠ β → 1/2⁻`, indices inchangés ; `paire(d) → 2·q^{ρ₀}/ρ₀`, `paire(d) − q^{ρ₀}/ρ₀ → q^{ρ₀}/ρ₀ ≠ 0`. [N] E202 (21 PASS) : résidu lissé ≤ 7,9e−3 · TB(5000)·x (Rosser, indépendant) ; 9/11063 événements susceptibles de changer de cellule ; ordres 1 / 1 / 2 / 0 ; Hardy `Z` sans changement de signe intérieur. [ND] `λ_l = 1` ; pas de comptage retiré comme dernier sous-but (exige la simplicité). |
| Défaut de comptage sur la ligne (auteur, 2026-10-12) | [C] `δ(T,U) = (N(U) − N(T)) − (N₀(U) − N₀(T)) = 2(W(U) − W(T))`, `2 ∣ δ`, `T ≤ U ⟹ δ ≥ 0` ; `W(T) = 0`, membre bas de hauteur `≤ U` ⟹ `δ ≥ 2` ; `W(T) = 0 ∧ δ = 0 ⟹` tout membre de hauteur `≤ U` ON, `λ = 1` ; `ΔN < 2 ⟹ δ = 0` (parité, mécanisme des rectangles 15/22/28) ; `∮_{[σ,2]×[a,b]} ξ₁'/ξ₁ = 0` (bord sans zéro) ⟹ aucun zéro dans le rectangle ; rectangles de droite `σ' → 1/2⁺` ⟹ `δ = 0` ; `k` changements de signe de `Λ(1/2 + it)` dans `[T,U]` ⟹ `ΔN₀ ≥ k`, `ΔN ≤ k ⟹ δ = 0` ; passage : `δ = fibre(T_l) − m_ζ(1/2 + iT_l)·[Λ(1/2+iT_l) = 0]`, aucun changement de signe dans `[T_e, T_l]`. [ND] `δ(T_e, T_l) = 0` (premier raccord analytique ouvert) ; [NC] multiplicité ON = ordre d'annulation de `t ↦ Λ(1/2 + it)`. |
| Rigidité des transitions au raccord, E203 (auteur, 2026-10-12) | [C] états `1, 5` ; `t11` (0), `t15` (4), `t51` (2), `t55` (0) ; `dst(t(m,n)) = src(t(n,r))` ; successeurs `t11 → t11|t15`, `t15 → t55|t51`, `t51 → t11|t15`, `t55 → t55|t51` ; entre deux `t15`, un `t51` (et réciproquement) ; `g_r = 6m_r + cls(t_r)`, magnitude libre ; passage : `n_l = n_e + 1`, `p_min(e) = Occ(l) = M`, transitions composables, toute `β` ; `β ≤ 1/2` ⟹ extrémités lues dans la cellule de ligne ou la précédente, écart d'indices à un près. [N] E203 (15 PASS) : raccord 299/299, 4999/4999 ; alternance dans les groupes et fenêtres ; profils synthétiques : 4186 déplacements, 4 changements de cellule, 0 violation. [ND] transport vers `λ_l = 1` ; liaison « rupture ⟹ violation de la rigidité dans la lecture authentique » réfutée dans cette lecture. |
| Champ de comptage autour de `li`, E204 (auteur, 2026-10-12) | [C] `b_ρ'(x) = −2x^{β−1}cos(T log x)/log x` ; extrema `D_k = e^{(π/2+kπ)/T}`, `log D_{k+1} − log D_k = π/T`, `T = π/(log D_{k+1} − log D_k)`, mêmes `D_k` à même hauteur (aveugles à `β`) ; `C_k < D_k < C_{k+1}` ; `δ = log D_k − log C_k = arctan(β/T)/T`, `β = T tan(Tδ)` ; `log λ = arctan(1/(2T))/T − δ`, `λ = 1 ⟺ δ = arctan(1/(2T))/T`, `β < 1/2 ⟹ δ < arctan(1/(2T))/T` ; `|Δb_k| ≤ 2C_k^{β−1}(li(C_{k+1}) − li(C_k))`. [N] E204 : `R_J = J₀ − F` (`F = li − log 2 + ∫_x^∞`), `b_n = −2 Re Ei(ρ_n log x)` ; contacts `X_k` (`b_n(X_k) = 0`) 48/71/85 sur `[2, 10⁵]`, `X_k ∈ ]D_{k−1}, D_k[`, `β = 1/2` racine unique de `Re Ei((β+iT) log X_k) = 0` ; restes propagés `r_{n−1}(D_k)` : signe commun 38/48, 48/71, 63/85, part médiane 0,55/0,46/0,42 ; ajustement sur `r_{n−1}` : `T` à 2e−3 près, `β = 0,50`. [NC] formule explicite de `J` (Riemann) et `Ei` : absentes de Lean et de Mathlib. |
| Registre d'un écart de premiers, E206 (auteur, 2026-10-12) | [C] sur `[p_n, p_{n+1}]` : `|Δb_ρ| ≤ 2p_n^{β−1}Δli_n ≤ 2p_n^{β−1}g_n/log p_n`, `g_n = 6m_n + a_n`, `≥ 2p_n^{β−1}·plancher(a_n)/log p_n` (`p_n > 3`) ; `β ≤ 1/2 ⟹` enveloppe `≤` enveloppe de ligne ; canal `ψ` lissé : `ΔR = ΔP_{T_e} + Δfibre]T_e, T_l] + ΔQ_{T_l}`, `Δfibre = ΔR − ΔP_{T_e} − ΔQ_{T_l}`, `‖ΔQ_{T_l}‖ ≤ budget(T_l)(p_n + p_{n+1})` (exposant 1) ; télescopage sur `m` écarts ; `1 − g_n/log p_n ≤ Δ(π − li₂) ≤ 1 − g_n/log p_{n+1}`. [N] E206 (canal `J`, 9591 écarts, `x ≤ 10⁵`, 5000 zéros) : `|Δb_n|/env ≈ |cos(T_n log p_n)|` (corrélation 0,99), 0,99 sur les écarts qui contiennent un contact `X_k`, 0,02 sur ceux qui contiennent un extremum `D_k` ; reste non comblé `U = ΔR − ΔP` dominé par `1 − g/log p` ; intérieur : `|ΔQ|/|Δb_n| ≈ 0,71√p_n` ; signes communs `(U, Δb_n)` 0,48–0,51 par écart, 0,50–0,58 par fenêtre de 36 ; paire hypothétique `1/2 ± d` : défaut `> |ΔQ|` sur 1 % (`d = 0,1`), 9 % (`d = 0,25`) des écarts. [NC] formule explicite de `J`. |
| Géométrie des contacts dans le champ collectif, sensibilité radiale, identifiabilité, E207 (2026-10-13) | [C] `δ(β, T) = arctan(β/T)/T` ; `0 ≤ β ≤ β' ≤ B ⟹ (β' − β)/(T² + B²) ≤ δ(β') − δ(β) ≤ (β' − β)/T²` ; sous la ligne `(1/2 − β)/(T² + 1/4) ≤ log λ ≤ (1/2 − β)/T²`, au-dessus `(β − 1/2)/(T² + 1) ≤ −log λ ≤ (β − 1/2)/T²` ; lecture de `δ` à `ε` près séparante si `2ε < (1/2 − β)/(T² + 1/4)`, aveugle si `(1/2 − β)/T² ≤ 2ε` ; système réduit (phase `arctan 2T ≤ φ < arctan 2T + 1/(2T)`, `0 ≤ log λ < 1/(2T²)`, `δ ≤ δ_ligne`, `x^{β−1/2} ≤ 1`) vrai pour toute `β ∈ ]0, 1/2]`. [N] E207 (canaux `J` et `π` séparés, Möbius exact à 1,8e−12 ; 5000 zéros, `x ≤ 10⁵`) : `X_k ≠ C_k` (écart ≈ demi-pas) ; contact individuel retrouvé dans le reste propagé exact 40/49, 50/72, 66/86 contre témoin 29/49, 44/72, 56/86 ; `β = 0,3` ou `0,7` à `T₁` : `Δlog C_k = ∓1,0e−3` ; restitution aveugle `T̂` à ≤ 3,6e−3, `β̂ = 0,497/0,504/0,501` ; région compatible `β ∈ [0,45 ; 0,53]` si le complément peut dépasser de 1 % le complément observé ; 48 contacts du zéro 1 à `10⁻³` près : `β ∈ [0,275 ; 0,725]` ; paire `1/2 ± d` substituée à `ρ₁` reproduit `J₀` à `10⁻¹²` avec complément redéfini (RMS 0,243 / 0,728 contre 0,184). [ND] borne du complément d'exposant `< 1 − β_l` (bande sans zéro au-dessus de `T_l`). [NC] `Ei`, formule explicite de `J`. |
| Induction du régime ON : parité des fibres, premier niveau de défaut, sondes, E208–E211 (2026-10-13) | [C] à toute hauteur `T` : `fibre(T) = fibre_ON(T) + fibre_BASSE(T) + fibre_HAUTE(T)`, `fibre_BASSE = fibre_HAUTE` (bijection `ρ ↦ 1 − ρ̄` à hauteur fixée), `fibre − fibre_ON = 2·fibre_BASSE` ; `D(T) = 0 ⟺ ∀ z, T_z ≤ T → β_z = 1/2` ; `T ≤ U ⟹ (ΔD(T, U) = 0 ⟺ ∀ z, T < T_z ≤ U → β_z = 1/2)` ; premier rang hors ligne `n` (bas, historique ON) : `D(T) = 0` pour `T < T_n`, `D(T_n) ≥ 2`, miroir distinct de même hauteur et multiplicité, `fibre_BASSE(T_n) ≥ 1`, `fibre(T_n) ≥ 2` ; sur `p : e → l` qui monte, historique ON : `β_l = 1/2 ⟺ ΔD(T_e, T_l) = 0 ⟺ mirror(l) = l`, `ΔD = 0 ⟺ fibre_BASSE(T_l) = 0` ; schéma : `P` suffisant ∧ `P` vrai sur tout passage d'historique ON ∧ ancre ⟹ RH ; instances suffisantes : `N(T_l) < N(T_e) + 2` (exige simplicité et unicité), `ΔD = 0`. [⟺RH] `ΔD = 0` sur tout passage d'historique ON (sous l'ancre). [N] E208 : `N(milieu_n) = n`, `D = 0` sur 300 rangs, `|S| < 1` observé, loi de Gram violée ; E209 : 299 passages, `ΔN = ΔN₀(signes) = 1`, `Δθ/π ∈ ]0, 2[`, corrélation classe mod 6 / `ΔS` ≈ 0, contacts emboîtés et pas contracté (théorèmes, toute `β`) ; E210 : premier défaut hypothétique = saut `+2` de `S` sans changement de signe, exclu par aucune borne démontrée ; rectangles de droite d'enroulement nul = l'obligation. [ND] toute loi `P` indépendante vraie sur les passages d'historique ON ; borne de `S(T)` ; lecture de `N₀` sans les zéros. |
| Audit du transport du régime ON, E212–E217 (2026-10-13) | [C] `p` qui monte : `∀ z, T_z = T_l → β_l ≤ β_z` (l'arrivée est le membre de partie réelle minimale de sa fibre) ; fibre mixte ⟹ arrivée basse ; SANS historique : `β_l = 1/2 ⟺ ∀ z, T_z = T_l → β_z = 1/2 ⟺ ∀ z, T_e < T_z ≤ T_l → β_z = 1/2 ⟺ ΔD(T_e, T_l) = 0 ⟺ fibre_BASSE(T_l) = 0` ; Tour ON `z` : `(∀ x ≥ 1, ‖u_w(x)‖ ≤ ‖u_z(x)‖) ⟺ β_w ≤ 1/2 ∧ ‖ρ_z‖ ≤ ‖ρ_w‖`, `(∀ x ∈ ]0, 1], …) ⟺ β_w ≥ 1/2 ∧ ‖ρ_z‖ ≤ ‖ρ_w‖` ; `β_w ≤ β_z` : inclusion sur les premiers ⟺ en `x = 2` ; `0 < M₁ < M₂` : `‖u_w‖/‖u_z‖ (M₁) = ‖u_w‖/‖u_z‖ (M₂) ⟺ β_w = β_z` ; `‖u_e(q_i)‖ = ‖u_l(q_i)‖` (`i = 1, 2`) `⟺ β_e = β_l ∧ ‖ρ_e‖ = ‖ρ_l‖`, faux sur tout passage qui monte. [N] E213 (modèle fini, 42 PASS), E214 (299 passages, rapports ON plats à 1e−9, `x* < 1`), E215 (297 fenêtres, identités exactes, ordre `d²`), E216 (égalités d'E116 fausses, ON compris). [ND] toute propriété indépendante ; inclusion sur `]0, 1[` depuis un historique ON. |
| Signature d'un zéro sur tous les écarts, hiérarchie, croisement, compatibilité collective, E218–E223 (2026-10-13) | [C] `Δ_s(a, b) = (b^s − a^s)/s = ∫_a^b t^{s−1} dt` (`Re s > 0`) ; `Δ_s ≠ 0` pour `0 < a < b` ; `‖Δ_s‖ ≤ (b^σ − a^σ)/σ` ; `Σ_{n<N} Δ_s(q_n, q_{n+1}) = Δ_s(q_0, q_N)` ; `t^{s+d−1} = t^d·t^{s−1}`, `‖Δ_{s+d}‖ ≤ b^d(b^σ − a^σ)/σ` ; ON `T_z < T_w` : `A_w/A_z = ‖ρ_z‖/‖ρ_w‖ < 1` en tout `x > 0` ; membre haut `1/2 + δ` : `A_w ≤ A_z ⟺ x ≤ (‖ρ_w‖/‖ρ_z‖)^{1/δ}` ; membre bas `1/2 − δ` : `A_{w'} ≤ A_z ⟺ ‖ρ_z‖/‖ρ_{w'}‖ ≤ x^δ` ; `A = x^{β−1/2}ℓ/√(π² + β²ℓ²)` pour toute `β` (`Terminal/GlobalGapSignature.lean`). [N] erreur relative de `Δ ≈ g p^{ρ−1}` `≤ |ρ−1|g/(2p)`, non uniforme en `T` (E219) ; canal `J` par écart : le reste d'un écart n'est porté par aucun zéro isolé, compléments par différence (E220) ; quartet hyp : défaut paire − double d'ordre `d²`, compensation libre sur fenêtre non transportée (E221) ; extraction de `(β, T)` en `log x` : identifie, ne borne pas (E222). [⟺RH] interdire le croisement pour tout membre (captivité universelle) ; borne du complément d'exposant `< β_w` (bande sans zéro). [ND] toute propriété globale des écarts contraignant `β` : les identités démontrées valent pour toute `β`. |
| Modèle harmonique des Tours, structure de ξ, fermeture du but `:399`, E224–E230 (2026-10-13) | [C] `t = log x`, `x^ρ/√x = e^{dt}e^{iTt}`, `d = β − 1/2` ; `y = e^{dt}cos(Tt − φ)` : `y'' − 2dy' + (T² + d²)y = 0` ; `E = ½((y' − dy)² + T²y²) = (T²/2)e^{2dt}`, `E' = 2dE`, `T ≠ 0` : `E'(t) = 0 ⟺ d = 0` ; `e^{(d+iT)t} + e^{(−d+iT)t} = 2cosh(dt)e^{iTt}`, différence `2sinh(dt)e^{iTt}`, `|somme| = 2cosh(dt) ≥ 2` ; `sup_t |e^{dt}| < ∞ ⟺ d = 0` ; vrai zéro : `E'_l = 0 ⟺ sup < ∞ ⟺ radialFactor = 1` (caractérisations) ; `F(s) = Λ(s − δ)Λ(s + δ)` : `F(1 − s) = F(s)`, `Λ(ρ) = 0 ⟹ F(ρ ± δ) = 0`. [C] but `:399` ⟺ `False` sous `hBelow` (`hLambda : 1 < radialFactor`) ; A ⟺ B ⟺ C (facteur, position, `fibre_BASSE(T_l) = 0`). [N] énergie de `(ψ − x)/√x` à `T_n` stationnaire (ζ, `|d| ≤ 2·10⁻⁴`), croissante à `δ⟨tanh δu⟩` (`W_δ`) ; noyau `Φ` (Titchmarsh §2.16) vérifié à `3·10⁻³¹`, `> 0`, pair ; `e^{−u²}(1 + ½cos 6u)` et `K_δ = (Φe^{δu}) ∗ (Φe^{−δu})` positifs à zéros non réels ; `Re ξ'/ξ = Σ (σ − β)/|s − ρ|² > 0` sur grille (ζ), `< 0` sous le zéro de `F_δ` ; réponse par écart de pente `d`. [⟺RH] `Re ξ'/ξ > 0` sur `Re s > 1/2` (Lagarias 1999) ; `|ξ|` croissante en `σ > 1/2` (Sondow–Dumitrescu 2010) ; hyperbolicité de tous les polynômes de Jensen de Ξ ; `Λ_dBN ≤ 0` ; énergie stationnaire de toute arrivée. [ND] une contrainte harmonique indépendante de RH tirée de la structure de ξ : FAUSSE pour toute structure partagée par `Λ(s − δ)Λ(s + δ)`. |
| Fenêtres finies, battements, grammaire des écarts, non-compensation, E231–E238 (2026-10-13) | [C] `ρ± = 1/2 ± d + iT`, `0 < a < b` : `−2Re(x^{ρ₊−1} + x^{ρ₋−1}) = −4x^{−1/2}cos(T log x)cosh(d log x)` ; `D_d(a,b) = G_d − G_0 = −4∫_a^b x^{−1/2}cos(T log x)(cosh(d log x) − 1)dx`, `D_{−d} = D_d`, `D_0 = 0`, `cos(T log x) ≥ 0` sur `[a,b]` ⟹ `D_d ≤ 0` (et `≥ 0` si `≤ 0`, `< 0` si `> 0` sur `]a,b[`, `d ≠ 0`, `a ≥ 1`) ; `p, q, r` premiers distincts : `log(q²/(pr)) ≠ 0`, `d·log(q²/(pr)) = 0 ⟺ d = 0` ; `det = Δ_s(p,q)Δ_t(q,r) − Δ_t(p,q)Δ_s(q,r)` : `det(s,s) = 0`, `det(t,s) = −det(s,t)`, sommes de colonnes symétriques ; `‖x^ρ‖‖x^{1−ρ̄}‖ = x` ; `‖x^{ρ₊}‖ + ‖x^{ρ₋}‖ = 2√x cosh(d log x)` ; `w ≥ 0 ⟹ Σw_n‖f_n‖² ≥ 0`. [N] signe par segment 53 712/53 712 ; même signe que le reste ψ requis 0,586 ; `L ≈ (c₂ − c₁)log q/q` (corr. 0,99995) ; six battements, `E(d) = E(−d)`, ordre `d²` ; complément requis ≤ 0,12 de la borne démontrée `budget(T_j)(a + b)` ; det non nul 240/240, ordre 1, observation de rang 1 ; transports ON `τ < 1` 299/299, renversement central ; compensation par zéros ultérieurs à poids libres sur `U = 2` (1e−6 à `T₁₀₀`), échec hors fenêtre ; `J` tronquée `≤ 0,25`, détection seulement contre troncature non certifiée ; Gram de `W_δ` PSD, matrice `−ζ'/ζ` non PSD à `σ = 0,75`. [⟺RH] interdire le renversement central sur tout passage ; borne du complément d'exposant `< 1/2 + d` (bande sans zéro). [ND] toute identité liant `d` aux données de la grammaire (aucune donnée de la fenêtre ne contient `d`) ; borne certifiée du reste dans le canal `J`. |
| Courant harmonique, courant croisé, premier zéro, couplage des Tours, E239–E241 (2026-10-13) | [C] `u = e^{(d+iT)t}`, `u' = (d + iT)u`, `J = Im(ū u') = T e^{2dt}`, `K = e^{2dt} = ‖u‖²`, `Q = K₂/K₁ = e^{2(d₂−d₁)t}` ; `Q(t) = 1` (`t ≠ 0`) ⟺ `Q(t₁) = Q(t₂)` (`t₁ ≠ t₂`) ⟺ `Q` constant ⟺ `d₁ = d₂` ; `β ∈ ]0, 1/2[` : grille admissible et `Q(C_k) = C_k^{2(β−1/2)} ≠ 1` ; vrai zéro, départ ON : `Q(log C_k) = Q(log C_k')` ⟺ `radialFactor l = 1` ; `W₁₂ = e^{(d₁+d₂)t}[T₂cos(ΔT t) + d₂sin(ΔT t)]`, `W₁₂ + W₂₁ = e^{(d₁+d₂)t}[(T₁+T₂)cos + (d₂−d₁)sin]`, `Im(conj(Σu)(Σu)') = ΣΣW` ; même hauteur : `W + W' = 2T e^{(d₁+d₂)t}`, paire `(d, −d)` : `2T`, total `4T cosh²(dt)` ; `Q(log x) = (‖Z_l(x)‖/‖Z_e(x)‖·‖ρ_l‖/‖ρ_e‖)²`, transport en deux abscisses ⟺ `‖Z_l‖/‖Z_e‖ (M₁) = (M₂)`. [N] Ξ réelle, `Ξ = 4∫_0^∞Φcos`, `Φ > 0` ; `θ(T₁)/π + 1 = 0,4497` ; `Z'(T₁) = 0,79316` ; part de `1/|ρ₁|²` 0,2186 (5000) ; canal `J` : zéro 1 > zéro 2 en absolu sur 6/9 fenêtres, retrait RMS +0,742/+0,497/+0,400 ; `Q` varie de `1 − e^{−2dπ/T_e}` entre deux contacts ; différence des fenêtres ON–OFF–OFF–ON et ON–double–ON paire en `d` ; même partie réelle, courants différents (CM12). [⟺RH] transport du courant sur tous les passages. [ND] toute obligation de courant ou de couplage fixant `d_l` ; part universelle du premier zéro. |
| Signal exact `x^ρ/ρ`, audit radial total, E242 (2026-10-13) | [C] `E = e^{ρt}/ρ = (e^{t/2}/ρ)U`, `R = U/ρ`, `U = e^{(d+iT)t}` ; `E = (e^{βt}/‖ρ‖)e^{i(Tt − θ)}`, `θ = arctan(T/β)` ; `J = Im(ĒE') = T e^{2βt}/(β²+T²) = (T/‖ρ‖²)e^{t}·e^{2dt}` ; `J₂/J₁ = (T₂‖ρ₁‖²)/(T₁‖ρ₂‖²)e^{2(d₂−d₁)t}`, égal en deux points ⟺ `β₁ = β₂` ; `‖E₁+E₂‖² = e^{2β₁t}/‖ρ₁‖² + e^{2β₂t}/‖ρ₂‖² + 2e^{(β₁+β₂)t}cos ΔΦ/(‖ρ₁‖‖ρ₂‖)`, `ΔΦ = (T₂−T₁)t + θ₁ − θ₂` ; `W₁₂ = e^{(β₁+β₂)t}[T₂cos ΔΦ + β₂ sin ΔΦ]/(‖ρ₁‖‖ρ₂‖)` ; `W^{exact} = Im(e^{t}Ū₁U₂/ρ̄₁)` ; `β₁+β₂ = 1`, même `T` : `W₁₂ = T e^{t}/‖ρ₁‖²`, `W₁₂+W₂₁ < 2T e^{t}/(1/4+T²)` (`d ≠ 0`, `T² > 3/4`) ; contacts `C_k, C_{k+1}` égaux ⟹ même `(β, T)` ; `Im U(kπ/T) = 0` ∀`d`. [N] inversion exacte des trois premiers zéros à 1e−9 ; constante de rapport ∈ [0,673 ; 0,995] ; annulations du croisé décalées de `arctan(β₁/T₁)/ΔT` ; écart miroir −5,0·10⁻⁵ (`d = 0,1`, `T₁`) ; 1 075 configurations 4.4 sans violation ; 172 scripts : 170 UNCHANGED, 2 CORRECTED. [ND] contrainte indépendante fixant `β_l`. |
| Synchronisation des Tours par écart premier, E243 (2026-10-13) | [C] `∫_a^b e^{ρt} dt = (e^{ρb} − e^{ρa})/ρ = 2h e^{ρm} sinh(ρh)/(ρh)` (`m`, `h` centre et demi-largeur logarithmiques), toute partie réelle ; unitaire `2h sinc(Th) e^{iTm}` ; `‖x^{ρ−1}‖ = x^{β−1}` : amplitude commune ⟺ même `β`, membre et miroir ⟺ `β = 1/2` ; [C] loi par écart `R(p_{n+1}) − R(p_n) = Σ_ρ (−m/(ρ+1))∫_{p_n}^{p_{n+1}} x^{ρ−1} dx` sur tous les vrais zéros ; linéarité ; déplacement radial = poids `e^{δt}` ; [N] E243 : loi par écart (canal ψ et J) à 3,1 % et 1,3 % avec 5000 zéros, superposition linéaire (R² 0,85) et non battements (R² 0,10), contacts non porteurs, peigne de Dirac `Λ(n)` en `log n` et biais de Landau retrouvés, même loi dans `W_δ` ; ajustement fini non transportable | identités et caractérisations ; la loi est la formule explicite intégrée sur l'écart, vraie pour toute partie réelle avec les poids correspondants ; l'amplitude commune des densités est le but (contrôle TDD) ; aucune contrainte indépendante |
| Synchronisation à amplitude stable, fréquences seules, E244 (2026-10-13) | [C] contrat `AmplitudeStableSync p` : `‖x^{ρ_l−1}‖ = ‖x^{ρ_e−1}‖` pour tout `x > 0`, `x ≠ 1` ⟺ `‖x^{ρ_l−1}/x^{ρ_e−1}‖ = 1` (fréquences seules) ⟺ `β_l = β_e` (une abscisse suffit) ; [C] départ ON + contrat ⟹ `radialFactor = 1` ; [⟺RH] le contrat sur tout passage qui monte depuis un membre ON (avec ou sans historique ON) ⟺ RH sous l'ancre ; [C] remplacement d'un point `ρ` par `ρ' ≠ ρ` (coefficient `−m/(ρ'(ρ'+1))`, autres contributions conservées) : défaut `c(ρ') − c(ρ)` non identiquement nul, la famille modifiée ne reconstruit pas ; instances `ρ' = ρ + δ` (amplitude) et `ρ' = ρ + iδ` (fréquence) ; [C] la représentation exacte du reste ne mentionne aucune position radiale ; [N] E244 : voir README | caractérisations et exclusions de remplacements ; la reconstruction exacte exclut TOUT remplacement sans distinguer amplitude et fréquence ; le contrat de l'auteur est le but `:399` écrit sur les densités, non dérivé ; aucune contrainte indépendante |
| Synchronisation locale des contributions sur chaque écart premier, C126, E264–E300 (2026-10-14) | [C] écart `I_n = [p_n, p_{n+1}]`, `a = log p_n < b = log p_{n+1}`, `0 < a` ; contribution locale d'un point `C_ρ(a,b) = ∫_a^b e^{ρt}/t dt` (canal de comptage ; `= li(e^{bρ}) − li(e^{aρ})`, `Ei` non formalisé), forme réelle `−2 Re C_ρ(a,b) = −2∫_a^b e^{βt}cos(Tt)/t dt` ; [C] `C[a,b] + C[b,c] = C[a,c]` ; `‖C[a,b]‖ ≤ (b−a)e^{βb}/a` (`β ≥ 0`) ; `∂_b C[a,b] = e^{ρb}/b`, `Re(e^{ρt}/t) = e^{βt}cos(Tt)/t` ; zéros de la densité `t = (π/2+kπ)/T`, indépendants de `β`, décalage au contact de phase `log C_k − log x_k = −arctan(β/T)/T` ; [C] paire miroir `e^{(ρ₀−d)t} + e^{(ρ₀+d)t} − 2e^{ρ₀t} = 2(cosh(dt)−1)e^{ρ₀t}` et son intégrale sur l'écart ; [C] canal lissé : `R(p_{n+1}) − R(p_n) = Σ_ρ (−m_ρ/(ρ+1))∫_a^b e^{ρt}dt` pour CHAQUE écart (toute `β`), résidu de troncature `= Σ_{ρ ∉ s}`, `c = Σ_s f + (c − Σ_s f)` (tautologie), télescopage de la cible sur une fenêtre ; [C] rigidité : `∀ b > a, C_ρ(a,b) = C_{ρ'}(a,b) ⟹ ρ = ρ'` (dérivée), de même pour `∫ e^{ρt}` ; identifie `1/4 + iT` comme `1/2 + iT` ; [C] sensibilité radiale `∂_β C_{β,T}(a,b) = ∫_a^b e^{(β+iT)t} dt = (e^{bρ} − e^{aρ})/ρ` (dérivation sous l'intégrale), `∂_b` de cette dérivée `= e^{βb}cos(Tb) ≠ 0` hors des zéros du cosinus ; [C] théorème A : `D_{β₁,T} = D_{β₂,T}` sur `]u, v[`, `u > 0` ⟹ `β₁ = β₂` ; inversion `β = log|(D(t₂)t₂/cos Tt₂)/(D(t₁)t₁/cos Tt₁)|/(t₂ − t₁)` ; seuls les zéros de la densité `(π/2+kπ)/T` sont indépendants de `β` ; [C] `LocalOnScale z : ‖e^{ρt}‖ = e^{t/2}` ⟺ `β = 1/2` ; départ ON + `LocalOnScale` de l'arrivée ⟹ `radialFactor = 1` ; [⟺RH] la loi quantifiée sur les passages d'historique ON ⟺ RH sous l'ancre ; [N] E264–E290 : voir README | C126 est la lecture locale de la formule explicite déjà compilée et de l'unicité spectrale ; ses trois maillons valent pour toute partie réelle (contre-modèle : tout point `β ≠ 1/2`, monde témoin `W_δ` avec ses poids) ; la forme fermante est le but `:399` écrit sur les contributions locales, non dérivée ; aucune contrainte indépendante |
| Audit contradictoire de la synchronisation locale et de la queue, E301 (2026-10-14) | [C] pour toute famille `F(x) = Σ c_i x^{r_i}` sommable aux deux bornes : `F(b) − F(a) = Σ c_i (b^{r_i} − a^{r_i})` ; synchronisation locale = formule explicite lissée aux deux bornes, seule entrée propre à ζ ; [C] `Σ f − Σ_s f = Σ_{sᶜ} f` pour toute famille sommable, d'où la queue ; [C] après retrait des zéros de hauteur `≤ H`, `‖ΔR(I_n) − ΔP_H(I_n)‖ = ‖ΔQ_H(I_n)‖ ≤ budget(H)(p_n + p_{n+1})`, `budget(H) = Σ_{|Im ρ|>H} m/|ρ(ρ+1)|` ; [C] même borne `‖Σ c_i x^{r_i}‖ ≤ (Σ‖c_i‖)x` pour toute famille `Re r_i ≤ 1`, satisfaite par `1/4 + iT` ; [N] F1 résidu médian 3,4e−5, 1000/1000 écarts sous la borne ; F2 détection 73–99,6 % (OFF), 63–98 % (double ON), 11–80 % (ON décalé) ; F3 compensation admissible, rapport ≤ 0,073 ; classement de 336 théorèmes porteurs : 217 identités, 19 identifiabilités, 19 caractérisations de `β = 1/2`, 15 [⟺RH], 19 conditionnels, 20 contraintes sans RH | identités et borne d'exposant 1, vraies pour toute `β` ; aucune des 20 contraintes sans RH n'exclut `β_l ∈ ]0, 1/2[` ; borne d'exposant `< 1 − β_l` = bande sans zéro [⟺RH quantifiée] |
| Trois Tours ON, contacts et synchronisation, E302 (2026-10-14) | [N] Tour `x^ρ/ρ` : hélice de fréquence `T`, rayon `√x/‖ρ‖`, départ `1/ρ` ; aucune intersection spatiale entre Tours (`‖q_a‖/‖q_b‖ = ‖ρ_b‖/‖ρ_a‖`) ; contacts de phase `exp((arctan(T/β)+kπ)/T)`, extrema `exp((π/2+kπ)/T)`, intersections avec li `Re Ei(ρ log x) = 0` ≈ contact + quart de tour ; synchronisation vérifiée = formule explicite, sélective en `T` ; résonance `Σ_{p≤x} p^{−iT_j} − ∫_2^x t^{−iT_j}/log t ≈ −li(√x)` ; correction écart par écart : `Δb_ρ(I_n) = −2∫_{I_n} t^{β−1}cos(T log t)/log t` lit `β` sur chaque écart ; famille ON : résidu par écart et par saut → 0 avec N ; ρ₁ remplacé par `1/2 ± d` : défaut `O(d²)` non nul sur chaque écart (remplacement, `replacement_not_reconstruct`) ; aucune relation ne fixe `β = 1/2` ; phase ON seulement |
| Synchronisation collective des trois premières Tours ON, E303 (2026-10-14) | Correction de l'auteur : synchronisation = superposition des trois contributions + interférences de phase, pas alignement de contacts. [C, module expérimental hors build] `E_ρ̄ = conj E_ρ`, `E_ρ + E_ρ̄ = 2 Re E_ρ` (le conjugué n'est pas une Tour supplémentaire) ; `(2Re E₁)(2Re E₂) = 2B₁₂ + 2B⁺₁₂`, `B₁₂ = e^{(β₁+β₂)t}/(‖ρ₁‖‖ρ₂‖)·cos((T₂ − T₁)t + θ₁ − θ₂)` (lent), `B⁺₁₂` même amplitude, `cos((T₁ + T₂)t − θ₁ − θ₂)` (rapide) ; `‖E₁+E₂+E₃‖² = Σ e^{2β_jt}/‖ρ_j‖² + 2ΣB_jk` ; `B₁₂(t + 2π/(T₂−T₁)) = e^{(β₁+β₂)2π/(T₂−T₁)}B₁₂(t)` ; extrema de `Re E` en `Tt = π/2 + kπ` (aveugles à `β`). [C] comptage par paire `−li(x^ρ) − li(x^ρ̄) = −2 Re Ei(ρ log x)` (branche `Ei(ρ log x)`). [démontré, Jensen] tout canal d'événements d'une somme finie de cosinus a `O(log X)` événements dans `[2, X]` : aucune correspondance exacte aux écarts premiers. [N] fenêtres de la première Tour (demi-périodes `π/T₁`) : superposition des trois paires de même signe que la demande `Δ(J₀ − li − C)` sur 73 %, corrélation 0,62 (témoins 50 %, −0,01) ; par écart individuel 52 % ; `|p̂_n − p_n|` 0,89 → 0,41 (x ≤ 100), 10,7 → 8,0 (≤ 10⁴), mieux que 200/200 témoins ; écart suivant inchangé au-delà de 100. Aucune conclusion sur `β` ni sur RH. |
| Théorèmes A et B de l'auteur, saut collectif et contacts partagés, E304 (2026-10-15) | [C] `ψ(N+1) − ψ(N) = Λ(N+1)` ; au premier `p = p_n`, `n ≥ 1` : `R_spec(p) − R_spec(p−1) = log p − (B(p+1) − 2B(p) + B(p−1))`, `B = x·fond`, `R_spec(N) = Z(N+1) − Z(N)`, `Z = x·Σ_ρ −m x^ρ/(ρ(ρ+1))` (théorème A : contribution collective de TOUS les zéros à la marche `p` = poids exact − seconde différence du fond ; identité sans hypothèse radiale) ; pour toute partie `S` : `ΔL_{Sᶜ} = (log p − Δ²B) − ΔL_S` (complément forcé). [C] contacts consécutifs partagés `C_k(z) = C_j(w)`, `C_{k+1}(z) = C_{j+1}(w)` ⟹ `T_z = T_w` (`T = π/log(C_{k+1}/C_k)`) puis `β_z = β_w` (`tan(T log C_k) = T/β`) ; hauteurs distinctes ⟹ aucun couple de contacts consécutifs commun. [⟺ but] `C_k(l) = C_k^{ligne}(T_l) ⟺ β_l = 1/2` (théorème B, forme exacte, caractérisation) ; [C] toute `β ∈ ]0, 1/2]` satisfait `C_k = C_k^{ligne}·λ`, `1 ≤ λ < e^{1/(2T²)}`. [N, vérification des scripts] hauteur de l'OFF : 70/109 à une hauteur de ζ, 23 témoins entiers, 16 nouvelles (milieu), 11 sans ; normalisation : 3/88 comparaisons aveugles par division par l'énergie propre, toutes annoncées ; `/√x` conserve `x^{β−1/2}`. [réduction, auteur] dernier pas de la chaîne : `ΔL_S(p) = J − ΔL_{Sᶜ}(p)` à `p = Occ(l)`, `S` = paquet de hauteur de l'arrivée ⟹ `‖ΔL_S‖ ≤ ‖J‖ + ‖ΔL_{Sᶜ}‖` ; but [ND, suffisant, non ⟺ RH] `‖J‖ + ‖ΔL_{Sᶜ}(p)‖ < ‖ΔL_S(p)‖` à ce seul événement ; signature 29bba26d88ce. |
| Raccords fixés par les deux bornes, E305 (2026-10-15) | [C] `∫_{log p_n}^{log p_{n+1}} e^{ρt} dt = F_ρ(log p_{n+1}) − F_ρ(log p_n)`, `F_ρ(u) = e^{ρu}/ρ` ; télescopage sur toute chaîne ; `Re ρ, Re ρ', Im ρ, Im ρ' > 0` et contributions égales sur tous les écarts premiers de rang `≥ n₀` ⟹ `ρ = ρ'` (seul `log p_n → ∞` : `F_ρ − F_{ρ'}` constante le long de la suite, croissance `e^{βu}` puis `‖ρ‖ = ‖ρ'‖`) ; vrai pour toute `β > 0` ; lecture de ligne sur une queue d'écarts ⟺ `β = 1/2` [⟺ but] ; `NoMixedHeight` [ND], impliquée par RH. [N] E305 : reconstruction aveugle de `(β, T)` depuis 600 écarts, ζ et zéros authentiques (ON et OFF) de Davenport–Heilbronn, `≤ 2e−13`. |
| Rigidité radiale depuis les seuls premiers, E308 (2026-10-15) | [C] `a + b = J ⟹ ¬(‖J‖ + ‖b‖ < ‖a‖)` : la séparation stricte d'E304 était fausse, retirée ; `1/2 + 14i` et `1/4 + 21i` ont tous deux leurs raccords fixés (identifier ≠ égaliser) ; `(∃ c, ∀ x > 0, x^{β₁} = c·x^{β₂}) ⟺ β₁ = β₂` ; enveloppe critique `2√x/√(1/4+T²)` ; sous l'ancre, loi de conservation radiale ⟺ RH. [N] E308/E308b : 13 fréquences détectées depuis `Λ` seul = 13 premières hauteurs à 0,01 ; `β₁` ajusté ∈ [0,488 ; 0,528], exposant commun ∈ [0,478 ; 0,522] selon pondération et horizon ; `β = 1/2` imposé ne dégrade pas la prédiction hors échantillon. [ND] conservation au premier changement de régime. |
| Amplitude de la courbe des premiers, réduction (2026-10-15) | [C] reproduction exacte, points fixes, `β_w ≤ θ` sous `‖R‖ ≤ Cx^θ` ; [C] `‖R‖ ≤ Cx` ; but `∃ C, ‖R(x)‖ ≤ C√x` [⟺RH], suffisant (miroir de l'arrivée basse) |
| Synchronisation par écart refaite, E309 (2026-10-15) | [C] synchronisation exacte de chaque écart par la famille authentique ; [C] insertion/remplacement exclus ; [N] 5000 zéros ON : 0 écart raté (x ≤ 10⁴) ; [N] toute configuration fabriquée, ON ou OFF, à hauteur distincte : défaut non nul sur chaque écart ; [C] aucun OFF de hauteur ≤ 28 ; « OFF ≠ hauteur d'un ON » : règle de protocole, [ND] |
| Audit externe du but `:378` vérifié, §95 (2026-10-15) | [C] enveloppes `A_β = 2x^{β−1/2}/√(β²+T²)`, `w` décroissante, miroir croissante, compatibles sous la borne d'exposant 1 ; [⟺RH] cible fenêtrée `∀ w ∈ 𝒲, limsup log(1+|∫F(U+v)w(v)dv|)/U ≤ 0`, `F(u) = e^{−u/2}R(e^u)`, classe détectant chaque fréquence (réponse `e^{(β−1/2)U}ŵ(T)` ⟹ `β ≤ 1/2` ∀ρ ; RH ⟹ von Koch ⟹ propriété) ; [C] synchronisation par écart vraie pour toute partie réelle (`gap_synchronization_any_family`) ; but inchangé |
| Courbe des écarts, amplitude du premier zéro, E310 (2026-10-15) | [N] premier zéro retrouvé depuis les seuls premiers, T̂₁ = 14,1348 ; [N] exposant d'amplitude lu par projection locale b = 0,5000 ± 0,0001, stable sur quatre décades ; [N] zéro sous un demi : facteur e^{−dΔu}, exclu numériquement dès d ≥ 0,0004 ; [N] monde témoin δ = 0,1 lu à 0,585 ; [C] β₁ = 1/2 (N(15) = 1) ; [C] unicité des sommes (`cpow_series_fibre_sum_zero`, `recovers_member`, `no_intruder`) = aucune compensation collective ; but ouvert inchangé |
| Second audit externe et extraction successive, E311, §96 (2026-10-15) | [C] rigidité collective : `cpow_series_fibre_sum_zero` (famille `s a : ι → ℂ` quelconque, `Re ≤ 1`, localement finie, `Σ‖a_i‖ < ∞`, `Σ' a_i x^{s_i} = 0 ∀x > 1 ⟹` chaque fibre nulle ; deux familles par `ι ⊕ κ`), `SpectralRepresentation` (côté droit = `smoothedRemainder`, poids des premiers), `contains_member`, `no_intruder`, `recovers_member`, `authentic_weight_rigid` ; elle ne fixe aucun exposant (`authentic_family_reconstructs_any_radial`) ; [C] résidu après retrait des modes de hauteur `≤ H` = `followingSum H`, `‖followingSum‖ ≤ C√x ⟺` suivants sur la ligne [⟺RH au-dessus de H], exposant 1 démontré ; [N] E311 : douze modes extraits successivement depuis les seuls premiers, `T̂_k` = douze premières hauteurs (|ΔT| ≤ 0,028), exposants libres `b_k` tous à 1/2 à 3σ (0,4645 ± 0,0309 au pire, mode 9), identiques à 1e−4 au signal synthétique à 1/2 exact ; témoin δ = 0,1 : 0,574–0,588 ; mesure finie |
| Correction collée pour E311, séparation des erreurs, E311b, §97 (2026-10-15) | [N] références `T_j` (mpmath, 30 chiffres, écart à Odlyzko 5e−10) ; décomposition exacte `β̂(T̂) − 1/2 = [β̂(T̂) − β̂(T_j)] + [β̂(T_j) − 1/2]` ; part de la hauteur ≤ 0,03 (j = 4, 9, 10), `dβ/dT ≤ 0,038`, prédiction linéaire vérifiée (j = 9 : +0,00105 / +0,00107) ; erreur d'inversion à hauteur exacte (j = 9 : −0,0365) reproduite à 1e−4 par le synthétique à exposant 1/2 exact (erreur de fenêtre) ; arrondi des références à `d` décimales à toutes les étapes : 1,1e−3 (1), 6,8e−4 (2), 2,1e−5 (3), 6,5e−6 (4), 1,5e−7 (5), 2,3e−8 (6) ; certification de `β_j = 1/2` : [C] rangs 1–3 (N(15), N(22), N(28)), externe rangs 4–12 ; aucun Lean, but `:378` inchangé. |
| §99 corrigé en §100 (2026-10-15) | `Terminal/JointSignatureHorizon.lean`, non composé : [C] identifiabilité CONDITIONNELLE `(∀ n ≥ n₀, G_{ρ'}(n) = G_w(n)) ⟹ Re ρ' = β_w ∧ Im ρ' = T_w` (hypothèse d'égalité ; aucune contrainte depuis les premiers) ; [C] OFF SUPPOSÉ ⟹ `∀ θ < 1 − β, ∀ C, ∃ x > 1, C x^θ < ‖R(x)‖`, `1 − β ≤ θ*` (direction OFF ⟹ reste) ; [⟺RH] exclusion ⟺ exposant `θ < 1 − β`, toutes exclues ⟺ `θ* = 1/2` ; [C] depuis les premiers SEULS : `0 ≤ β ≤ 1`, rien sur `T` (`prime_signal_alone_joint_constraint`). L'étude « signal ⟶ contraintes conjointes sur `(T, β)` » n'est PAS réalisée ; aucun mécanisme d'exclusion validé. |
| Généralisation : besoin constant aux points de rencontre (2026-10-15, §102) | Besoin `A_z(x) = 2x^{β−1/2}/‖ρ‖` ; `ConstantNeed z := ∀ x y ≥ 1, A_z(x) = A_z(y)` (aucune valeur présupposée). [C] `ConstantNeed z ⟺ β = 1/2` ; aux contacts `A(C_{k+1}) = A(C_k) ⟺ β = 1/2`, `A(C_{k+1})/A(C_k) = e^{(β−1/2)π/T}` ; deux besoins constants `T_z < T_w` : `π/T_w < π/T_z`, `A_w < A_z`, `A_w/A_z = √(1/4+T_z²)/√(1/4+T_w²)` (seule la fréquence change) ; `hDecr ⟹ ¬ ConstantNeed` ; `∃ 1 ≤ x < y, A_w(x) ≤ A_w(y)` + `hDecr ⟹ False`. [⟺RH] `(∀ z, ConstantNeed z) ⟺ RH` ; forme au passage avec historique, sous l'ancre, ⟺ RH. But `:383` (signature 8447175d18bf) : `∃ 1 ≤ x < y, A_w(x) ≤ A_w(y)` [ND]. Mesuré [N] (E313, premiers seuls, douze fréquences) : voir §102. |
| Verrou du couple sur la Tour normalisée (2026-10-16, §103) | Rencontres `C_k`, `log C_k = (arctan(T/β)+kπ)/T`, espacement `π/T`, position `C_k = C_k^{ligne}(T)·λ`, besoin `A(C_k)`. [C] même espacement ⟹ même `T` ; espacement aveugle à `β` ; à `T` égal, `C_k(w) = C_k(z) ⟹ β_w = β_z` (par `β = T·cot(T log C_k)`) ; à `T` égal, `A_w(C_{k+1})/A_w(C_k) = A_z(C_{k+1})/A_z(C_k) ⟹ β_w = β_z` ; `T·cot(T log C_k) = (T/π)·log(A(C_{k+1})/A(C_k)) + 1/2` ; `A(C_{k+1}) = A(C_k) ⟺ λ = 1` ; `A(C_{k+1}) ≠ A(C_k) ⟹ ∀ j, C_j ≠ C_j^{ligne}` ; `T_z < T_w ⟹ π/T_w < π/T_z ∧ ¬∃ c ∀ k, C_k(w) = C_k(z)·c` ; `T_z = T_w, β_z ≠ β_w ⟹ ∃ c ≠ 1 ∀ k, C_k(w) = C_k(z)·c ∧ ∀ k` rapports de besoins différents ; même espacement ∧ rencontre commune (ou même rapport de besoins) ⟹ `(T_w, β_w) = (T_z, β_z)` ; `hDecr ∧ ∃ k, A_w(C_{k+1}) = A_w(C_k) ⟹ False`. [⟺RH] `(∀ z, ∃ k, A_z(C_{k+1}) = A_z(C_k)) ⟺ RH`. But `:393` (signature 239cdd0a1bcb) : `∃ k, A_w(C_{k+1}) = A_w(C_k)` [ND]. Tout vrai pour toute `β` : aucune contrainte sur `β`. |
| La fréquence est déjà occupée (2026-10-16, §104) | `Occ(T) := ∃ z, T_z = T ∧ β_z = 1/2` ; `Un(·) := ∀ z w, T_z = T_w ⟹ C_0(w) = C_0(z)` ; `Pris(w) := ∃ z, T_z = T_w ∧ β_z = 1/2 ∧ C_0(w) = C_0(z)`. [C] `Occ(T) ⟹ ∃ z ON, ∀ k, C_k(z) = C_k^{ligne}(T)` ; `Un ∧ Occ(T_w) ⟹ β_w = 1/2` ; `Un ∧ Occ(T_w) ∧ β_w < 1/2 ⟹ False` ; `Un ∧ β_w < 1/2 ⟹ ¬Occ(T_w)` ; `1/2 < β_w ⟹ ∃ v, T_v = T_w ∧ β_v < 1/2` (miroir) ; `(∀ v, ¬ β_v < 1/2) ⟹ ∀ w, β_w = 1/2` ; `Pris(w) ⟺ β_w = 1/2` ; `hDecr ∧ Pris(w) ⟹ False`. [⟺RH] `Un ⟺ RH` ; `(∀ w, Pris(w)) ⟺ RH` ; [C] `Un ∧ (∀ w, Occ(T_w)) ⟹ RH`. But `:401` (signature 5fcfca4c2bd2) : `Pris(w)` [ND]. Les définitions écrivent le point de l'auteur ; rien n'est dérivé des écarts. |
| Des écarts exacts vers les fréquences engendrées et leurs points de rencontre (2026-10-16, §105, E321 ; réimplémenté §109) | Côté premiers, depuis `R(x) = Σ_{n<x} Λ(n)(1 − n/x) − fond` seul : `Rep(ι) := (p_i, w_i)` distincts, `Re ≤ 1`, localement finie, `Σ ‖w_i/(p_i(p_i+1))‖ < ∞`, `Σ_i w_i x^{p_i}/(p_i(p_i+1)) = R(x)` pour tout `x > 1` ; `FréqArith(T) := ∀ Rep, ∃ i, w_i ≠ 0 ∧ |Im p_i| = T` ; `Renc(p) := exp(arctan(Im p/Re p)/Im p)` (`Renc(p̄) = Renc(p)`) ; `RencArith(T, c) := ∀ Rep i, w_i ≠ 0 ∧ |Im p_i| = T ⟹ Renc(p_i) = c`. Forme spectrale : `Eng(T) := ∃ z, T_z = T` ; `RencLigne(T) := ∀ z, T_z = T ⟹ C_0(z) = C_0^{ligne}(T)` ; `UnSignal(T)` ; `AucuneDessous := ∀ T, Eng(T) ⟹ RencLigne(T)`. Correspondance [C] (unicité, `contains_member`, `no_intruder`, aucun exposant fixé) : `C_0(z) = Renc(ρ_z)` ; `C_0^{ligne}(T) = Renc(1/2 + iT)` ; `FréqArith(T) ⟺ Eng(T)` ; `RencArith(T, C_0^{ligne}(T)) ⟺ RencLigne(T)` ; `C_0^{ligne}(|Im σ|) < Renc(σ) ⟺ Re σ < 1/2`. Rigidités renversées [C] (toute `β`) : R2' `β = T·cot(T log C_0)` ; R3' `β = 1/2 + (T/π) log(A(C_1)/A(C_0))` ; R5' `C_0(z) = C_0^{ligne}(T_z) ⟺ β_z = 1/2` ; R6' `C_0^{ligne}(T_z) < C_0(z) ⟺ β_z < 1/2` ; R7' `UnSignal(T) ⟺ RencLigne(T) ⟺ ∀ z, T_z = T ⟹ β_z = 1/2` ; R8' détection / aveuglement d'une mesure finie ; R10' `C_0(w) = C_0^{ligne}(T_w) ⟹ Pris(w)`. [⟺RH] `AucuneDessous ⟺ RH` ; `(∀ T, Eng(T) ⟹ UnSignal(T)) ⟺ RH` ; `(∀ T, FréqArith(T) ⟹ RencArith(T, C_0^{ligne}(T))) ⟺ RH`. But `:419` (signature ceb3039e6ad7) : `RencArith(T_w, C_0^{ligne}(T_w))` [ND] (plus fort que `C_0(w) = C_0^{ligne}(T_w)` pris isolément ; équivalent à `False` dans le contexte). Trois objets distincts (§110) [C] : `RencArith` est la rencontre PROPRE `C_n` de chaque composante (`Iff.rfl`) ; rencontre collective `RencColl(x) := R(x) = 0 ⟺ Σ_i w_i x^{p_i}/(p_i(p_i+1)) = 0` dans toute `Rep`, et alors `w_i f_x(p_i) = −Σ_{j≠i} w_j f_x(p_j)` ; événement premier `P(n) := Λ(n) ≠ 0 ⟺ n` puissance de premier ; primitive `P(x) = x·S(x)` : `P(N+h) = P(N) + hψ(N)` (`0 < h ≤ 1`), saut de pente `Λ(N)` en `N ≥ 1`, non nul aux événements ; toute somme finie de composantes est dérivable sur `x > 0` : l'événement est porté par la somme infinie seule. Non écrit [ND] : la contrainte que les `P` imposent simultanément aux `C_n` et à leur résultante `R`. Trois ingrédients (§110, addendum) [C] : vertical depuis ON ⟹ `FréqArith(T_l)` ∧ `Occ(l) = p_min(e)` ∧ `Λ(Occ(l)) = log Occ(l)` ∧ `T_e < T_l` ∧ `β_l ≤ 1/2` (`movement_law_three_ingredients`), conclusion muette sur `β_l` ; « vertical depuis ON + fréquence authentique + `M^Z = M` ⟹ `β_l ≥ 1/2` » [ND] : aucun théorème compilé ne le conclut, et les trois ingrédients valent pour toute `β_l ∈ ]0, 1/2]`. Mesuré E321–E322 (premiers seuls, `X = 10⁸`, vingt fréquences, lecture calibrée sur un contrôle ON ; objet lu = zéros d'une contribution FILTRÉE du signal collectif, rencontre collective, non la rencontre propre `C_n` du but) [N] : fréquences = hauteurs de zêta ; translation `log λ̂` compatible avec 0 ; pente d'amplitude `1/2` ; un seul signal (`d̂ ≈ 0`, témoin `d̂ ≈ δ`) ; porteur = tailles exactes dans leur ordre. Les règles renversées et la correspondance identifient `β`, aucune ne le fixe. Loi de compensation (§111) [C], abscisses brutes : `V(T, T') := arctan(2T')/T' − arctan(2T)/T` (part verticale), `Rad(z) := log C_0(z) − log C_0^{ligne}(T_z) = log λ_z` (part radiale), `RadArith(p) := log Renc(p) − log C_0^{ligne}(|Im p|)` ; `arctan v / v` strictement décroissante sur `v > 0` (valeur moyenne) ⟹ `V(T, T') < 0` pour `0 < T < T'`, `C_0^{ligne}(T') < C_0^{ligne}(T)` ; `Rad(z) > 0 ⟺ β_z < 1/2`, `Rad(z) = 0 ⟺ β_z = 1/2` ; départ sur la ligne : `log C_0(w) − log C_0(e) = V(T_e, T_w) + Rad(w)` ; `C_0(w) = C_0(e) ⟺ Rad(w) = −V(T_e, T_w)`, et si `T_e < T_w` alors `β_w < 1/2` ; réalisable : `∀ T > 0, ∃ T' > T, ∃ β ∈ ]0, 1/2[, Renc(β + iT') = C_0^{ligne}(T)` (point du plan ; l'impossibilité « conserver la rencontre du départ » est fausse) ; `C_0(w) = C_0^{ligne}(T_w) ⟺ Rad(w) = 0` ; `RencArith(T, C_0^{ligne}(T)) ⟺ ∀ Rep i, w_i ≠ 0 ∧ |Im p_i| = T ⟹ RadArith(p_i) = 0`. [⟺RH] `(∀ z, Rad(z) = 0) ⟺ RH`. But `:419` (signature 4ae9f8496acf) : `RadArith(p_i) = 0` pour tout signal `p_i` de fréquence `T_w` [ND] (réduction sans perte). Non-compensation (§112, [C]) : `c_z(x) = R(x) − Σ_{j≠z} c_j(x)`, aucun remplacement ni changement d'amplitude ne reconstruit, dérive par écart `e^{(β−1/2)L_r}` (toute `β`) ; valeur de l'amplitude imposée [ND] ; E324 [N] exposant 0,4997–0,5003. |
| Vérification de E321, reprise sur le canal de comptage autour de li (2026-10-16, §106, E322, numérique seulement, aucun Lean) | `J(x) = Σ_{p^m ≤ x} 1/m = li(x) − Σ_ρ li(x^ρ) − log 2 + Σ_{k≥1} E1(2k log x)` (points de continuité) ; contribution d'une paire `−2 Re Ei(ρ log x) = −2 e^{βu} Re[e^{iTu} S(ρu)/ρ]/u`, `S(z) = 1 + 1/z + 2/z² + 6/z³ + …`, amplitude `x^β/(|ρ| log x)`, normalisée `x^{β−1/2}/|ρ|` [C, identités]. Mesuré [N] (`experiments/E322_CountingReconstructionAroundLi/`, `X = 10⁸`, vingt fréquences, contrôle = 5000 zéros publiés à `β = 1/2`) : rencontres avec le fond non déplacées (mode 1 : `Δu = 2·10⁻⁸`, exclusion `β ≤ 0,49996` par `meeting_shift_detects`) ; `b = 0 ± 10⁻⁵` ; résidu après `N` fréquences `0,2154 → 0,1189` (ζ) contre `0,2149 → 0,1181` ; profil du résidu en `β` d'une fréquence seule minimal en `1/2`, surcroît 26 %–10 % à `β = 0,4 / 0,6` ; limite `J − F` : `D′ = −1/log x + 1/(x(x²−1) log x)` hors des puissances de premiers, sauts `1/m` ; `S_N′(p) ≈ T_N/(πp)` (Landau, mesuré 1,622 contre 1,719). Loi quantifiée [⟺RH] ; but `:409` inchangé [ND]. |
| La matrice de synchronisation (2026-10-16, §107, E323, `Terminal/SynchronizationMatrix.lean`) | cellule `M(ρ; a, b) := term_b(ρ) − term_a(ρ) = (−m_ρ/(ρ+1))∫_a^b x^{ρ−1} dx` [C] ; identité de ligne `R(b) − R(a) = Σ_ρ M(ρ; a, b)` pour `1 < a, b` [C, `row_identity`] ; ligne tronquée = queue `Σ_{ρ∉s} M` [C] ; `b ↦ Σ_{ρ∈s} M(ρ; a, b)` continue sur `b > 0` [C] ; réajustement `log(A_z(y)/A_z(x)) = (β − 1/2)(log y − log x)` [C, `block_readjustment_log`], inversion `β = 1/2 + log(A(y)/A(x))/(log y − log x)` [C] ; `∀ x, y ≥ 1, log(A(y)/A(x)) = 0 ⟺ β = 1/2` [C, caractérisation] ; `∀ z, ∀ x, y ≥ 1, log(A_z(y)/A_z(x)) = 0 ⟺ RH` [⟺RH, `matrix_compatibility_law_iff_riemannHypothesis`]. Mesuré [N] (`experiments/E323_SynchronizationMatrix/`, premiers seuls, `X = 10⁸`, 9506 lignes exactes sur `[10³, 10⁵]`, vingt colonnes, 10 PASS) : résidu de ligne `0,999` (20 colonnes), `0,897` (5000 zéros) ; rencontres `Δu·T_n/π` des lignes ; saut nul des colonnes ; réajustement par bloc `≤ 3·10⁻⁴`, pente nulle ; témoin pente `0,083`. But `:409` inchangé [ND]. |
| Zéro suivant sous un demi : fréquence et amplitude (2026-10-16, §108, `Terminal/LowNextZeroSignatures.lean`) | `β_l < 1/2` sur un passage qui monte ⟹ `N(T_l) ≥ N(T_e) + 2` [C] ; `β_w < 1/2` ⟹ `N(T_w) − N₀(T_w) ≥ 2` [C] ; `N(c) = k ∧ W(c) = 0 ∧ β_w < 1/2` ⟹ `c < T_w ∧ N(T_w) ≥ k + 2` [C] ; instance `c = 28, k = 3` [C, `low_zero_after_certified_band`] ; `x, y ∈ [1, X] ⟹ |log(A_w(y)/A_w(x))| ≤ |β − 1/2| log X` [C] ; `∀ X ≥ 1, ε > 0, ∃ d₀ > 0, |β − 1/2| < d₀ ⟹` dérive propre `< ε` sur `[1, X]` [C] ; `r > 1 ⟹ ∀ H, ∃ d₀, 0 < d < d₀ ⟹ H < r^{1/d}` [C]. Signature de comptage discrète (`2`, tout `d`), signature d'amplitude continue, nulle en `d = 0` ; « `N = N₀` à toute hauteur » [⟺RH]. But `:409` inchangé [ND]. |
| Alignement sur le sens imposé (2026-10-15, §101) | Aucun énoncé modifié ; `off_signal_amplitude_incompatible` (`:382`, signature 8cc375a270c0, ligne déplacée par les docstrings) commenté dans le sens unique écarts ⟶ signaux ⟶ position. Démontré [C] : `‖R(x)‖ ≤ C·x` depuis `Λ ≥ 0` + Chebyshev (la courbe impose l'échelle entière) ; `R = Σ_ρ −m x^ρ/(ρ(ρ+1))` ; unicité des signaux. Mesuré [N] (E310, E311, E312 premiers seuls) : pour `k = 1..12`, `β̂_k = 1/2` à la précision de la méthode, résidu minimal à `β = 1/2` sur grille, pente d'amplitude `0`, témoin `≈ +δ`. Manque [ND] : la rigidité écrite des écarts exacts vers l'amplitude forcée ; toutes les rigidités R1–R136 sont du zéro vers ses effets. RÉFUTÉ [démarche] : expériences à zéros fabriqués et inférences depuis le monde témoin, comme énoncés sur zêta ; « ce qui manque est la borne `√x` » comme question. |
| Texte collé « fréquence attendue », §98 (2026-10-15) | [C] (1) identification pour toute `β` (`prime_gap_contributions_determine_point`, `recovers_member`) ; [C] (2) ancre ; [C] miroir `1 − ρ̄` à même hauteur (`zetaZeroMultiplicity_mirrorPoint`) ; [C] côté haut exclu à l'arrivée par l'ordre de la fibre (`passage_entry_radial_le_half`), côté bas = but ; [N]/[ND] (3a) aucun théorème ne produit une hauteur depuis la grammaire (`window_abel_all_sameHeight`, `grammar_step_regime_blind`) ; [⟺RH] (3b) unicité radiale à la hauteur du suivant, quantifiée (`local_on_law_iff_riemannHypothesis`, `amplitudeStable_law_iff_riemannHypothesis`) ; [C] (5) réfuté comme fait : `gap_synchronization_any_family`, `authentic_family_reconstructs_any_radial` ; seul un remplacement rompt (`replacement_not_reconstruct`). Aucun théorème `expected_frequency_forces_onLine` : but inchangé. |
| Réduction en trois points de l'auteur (2026-10-15) | [C] premier zéro ON, champ `2/√(1/4+T₁²)` ; [C] même point exclu ; [C] aucun OFF sous 28 ; [C] zeta23 : proportion ≥ 2/3 sur la ligne (asymptotique) ; [ND] (2) `T_z = T_w ∧ β_w = 1/2 ⟹ β_z = 1/2` ; [ND] (3) `∃ w ON, T_w = T_l` ; (2) ∧ (3) ⟹ contradiction [C] |
| Certificat (V2) de l'ancre (auteur, 2026-10-10 : « attaque le but 1 ») | [C] sur chaque morceau `[s_a, s_b]` d'un côté : `L·main(s) = (L − α)main(s_a) + α main(s_b) + R`, `‖R‖ ≤ Bα(L − α)` (la dérivée s'élimine), `Re(I^z ζ(s)) ≥ min(q_a, q_b) − BL²/4 − E > 0` ; `(1 − s)` dans `Re > 0` par `I^w` ; `∮ = Σ raccords · (π/2) i` ; B₁ = [1/4, 2] × [−1, 15] : `∮ = 2πi` ; B₂ = [3/4, 2] × [−1, 15] : `∮ = 0` ⟹ N(15) = 1, premier zéro simple et ON | [C] `ZB.Cert.zeta_box_certificate`, 193 morceaux générés (e192), axiomes standard ; l'ancre n'est plus un but |
| Lecture conjointe de la fibre d'arrivée (auteur, 2026-10-11) | [C] `Y = R − P_{T_e} = F + Q_{T_l}` ; `‖Σλ_r Y(x_r)‖ ≤ Σ|λ_r|(C x_r + B√x_r)` (indépendante de l'identité, exposant 1) ; `‖Σλ_r Q(x_r)‖ ≤ budget(T_l)·M` ; `‖Σλ_r F(x_r)‖ ≤ fiberBudget·Σ|λ_r|x_r` ; `Σ|λ|(Cx + B√x) + budget·M < ‖ΣλF‖ ⟹ False` ; cette inégalité exige `C < fiberBudget` ; [ND] minoration du signal signé de `F` ; [ND] majoration de `Σλ_r R(x_r)` meilleure que `C·Σ|λ|x` | [C] `Terminal/JointComparison.lean` ; but de la transmission = l'inégalité stricte |
| Miroir de la première rupture dans un groupe fini (auteur, 2026-10-11) | [C] `R − P_{T_e} = G_{T_e,H''} + Q_{H''}`, groupe fini ; `l` bas dans le groupe ⟹ `¬ ∃C, ‖G‖ ≤ C x^θ` pour `θ < 1 − β_l` (miroir, lecture du pôle) ; `‖R − Q_{H''}‖ ≤ C x^θ`, `θ < 1 − β_l` ⟹ contradiction ; démontré : `‖R − Q_{H''}‖ ≤ (C_lin + budget(H''))·x`. [C] `R − Q_{H''} = P_{H''}` (somme finie contenant le miroir : la borne précédente n'était pas indépendante) ; `‖R‖ ≤ C x^θ`, `θ < 1 − β_l` ⟹ contradiction. [ND] `‖R‖ ≤ C x^θ` avec `θ < 1` (seul `θ = 1` est démontré) ; minoration quantitative du signal signé du miroir. |
| Reste déroulé aux poids premiers (revue de l'auteur, 2026-10-11) | [C] `S(N) = Σ_{n<N} Λ(n)(N − n)/N` ; `‖R(N)‖ ≤ |primeMass N − N²/2|/N + B₀` ; `‖R(x) − R(⌈x⌉)‖ ≤ D` ; blocs `C N^{1+θ}` ⟹ `‖R(x)‖ ≤ C' x^{max θ 0}` ; `primeMass = primePart + powerPart`, `powerPart ≤ 2N^{3/2} log N` ; `primePart` = bord + quatre transitions `≥ 0` ; `primePart ≤ 2N log 3 + N log N (N/3 + 2)` (états mod 6, unilatéral) ; blocs `≤ (log 4 + 5) N²`. [C] pour `θ > 1/2` : blocs d'exposant `1 + θ` ⟺ tout zéro `β ≤ θ` ; sous historique ON sous `T` : ⟺ tout zéro de hauteur `≥ T` sous `θ` (caractérisation, deux sens). [ND] `|primePart N − N²/2| ≤ C N^{1+θ}`, `θ < 1 − β_l` ; aucune bande `Re s > θ`, `θ < 1` fixé, n'est connue inconditionnellement (littérature). |
| Conservation du régime ON au passage authentique (auteur, 2026-10-09 ; `Terminal/AuthenticPassageProfile.lean` ; chaîne unique `Terminal/DemonstrationChain.lean` du build principal, la cible séparée est supprimée) | Cible : `VerticalPassage(o) ∧ o.zLater = p.zEarlier ∧ β_{p.zEarlier} = 1/2 ⟹ β_{p.zLater} = β_{p.zEarlier}`, sans supposer le prochain membre ON. [C] `ρ = 1 − ρ̄ ⟺ β = 1/2` ; `β_z = 1/2 ⟹ z* = z`, `T_{z*} = T_z`, `m_{z*} = m_z`. [C] `C_k = exp((φ + kπ)/T)`, `φ = arctan(T/β)`, `log(C_{k+1}/C_k) = π/T`. [C] `A_ρ(x) = 2x^{β−1/2}/‖ρ‖` ; ON : `A = 2/√(1/4 + T²) = 2W/√(π² + W²/4)`, `W = π/T` ; `A_l/A_e = x^{β_l − 1/2}·‖ρ_e‖/‖ρ_l‖` (e ON). [C] `e` ON, `p : e → l` monte ⟹ `β_l ≤ 1/2`, rang `+ 1`, `Occ(l) = p_min(e)`, `π/T_l < π/T_e`, `φ_l ∈ [arctan 2T_l, arctan 2T_l + 1/(2T_l)[`, `λ_l ≥ 1`, `C_k(l) = C_k^{ligne}(T_l)·λ_l`, `Λ(M) = log M`, registre ; `λ_l = 1 ⟺ β_l = 1/2`. [C] `L_r = log(p_{r+1}/p_r)`, `Δθ_ρ = T_ρ L_r`, `A_ρ(p_{r+1})/A_ρ(p_r) = e^{(β_ρ − 1/2)L_r}`, `g_r ≥ plancher(a_r)`, `a_r ∈ {0, 2, 4}`, alternance. [C] canal lissé normalisé sur support `> 1` : `Σ_{j≥1} c_j = R`, `D_n = ‖c_n‖² + 2⟨r_n, c_n⟩`, `⟨r_n, c_n⟩ = Σ_{n<j≤N}⟨c_j, c_n⟩ + ⟨r_N, c_n⟩ = Σ_{j>n}⟨c_n, c_j⟩` (résidu conservé) ; [C] `x ≥ 2` : `ψ` reconstruite depuis les zéros, comptage pondéré `rPiWeighted` (rhv3_lean) ; [C] `Σ_ρ m_ρ/|Im ρ|² < ∞`. [C] membre le plus bas ON ⟹ son passage sortant monte (miroir du membre haut de même hauteur précéderait le plus bas). [C] ancre `β₁ = 1/2` ∧ loi `∀ p, 0 < T_e → T_e < T_l → β_e = 1/2 → β_l = β_e` ⟹ tout membre canonique ON, tout passage canonique monte ⟹ RH (`riemannHypothesis_of_anchor_and_conservation`) ; [⟺RH] la loi est impliquée par RH ; [C] forme de l'auteur par `engaged_regime_kept`. [ND] la loi elle-même (`radial_conservation_authentic`, but `False` sous `β_l < 1/2` avec `λ_l > 1`, passage sortant `q : l → s` de même hauteur, `C_k(s) < C_k(l)`, `β_s ≤ 1/2 ∨ s = l*`, `q` monte ⟺ `λ_l = 1`, reconstruction et interactions instanciées) : écart exact = une inégalité ou identité démontrée, lue sur les poids premiers et la reconstruction exacte, imposant `λ_l = 1`, fausse sur « `e` ON ; `l`, `s` consécutifs à la même hauteur, `β_l < 1/2` ». Premier membre canonique conservé dans chaque raccord (auteur, second message, 2026-10-09) [C sous l'ancre] : `sUpperZerosBelow z₁ = ∅`, `T₁ ≤ T_e ≤ T_l` ; `A_1(e^u) = 2/√(1/4 + T₁²)` ; `A_e(x) ≤ A_1(x)` (`e` ON, par unité de multiplicité) ; `A_l/A_1 = x^{β_l−1/2}‖ρ₁‖/‖ρ_l‖` ; retrait signé `Σ_{j≥2} c̃_j(x) = R̃(x) − c̃_1(x)` (`x > 1`) et `Σ_{j≥2} c_j = R − c_1` sur tout support, `r_1 = R − c_1`, `D_1 = 2⟨R, c_1⟩ − ‖c_1‖²`, `I_1 = Σ_{j≥2}⟨c_1, c_j⟩` (complément infini conservé) ; `C_k(z₁) = exp((arctan(T₁/β₁) + kπ)/T₁)` ; `c_{z₁}(x) c_w(x) = (A_1 A_w/2)[cos((T₁ − T_w) log x − (φ₁ − φ_w)) + cos((T₁ + T_w) log x − (φ₁ + φ_w))]` ; `|T_l − T₁| log(1 + plancher/p_r) ≤ |Δθ_l − Δθ_{z₁}|`. [C] tout membre ON ∧ ancre ⟹ captivité universelle `∀ w, ∀ u ≥ 0, A_w(e^u) ≤ A_1` (CONSÉQUENCE, jamais hypothèse) ; [C] ancre ∧ loi ⟹ tout ON ⟹ captivité ⟹ RH. Le déficit de comptage reste une fermeture disponible ([C] `riemannHypothesis_of_counting`) et un contrôle ; il ne remplace pas la cible. `thm_localZeroDensity_le_log` (rhv2_fresh, commit 51cf3728) : hors périmètre d'import. Premier changement de régime (troisième message, 2026-10-09) : [C] `1/2 < β_z ⟹ β_{z*} < 1/2 ∧ z* ≺ z` ; [C] sous l'ancre, `VerticalPassage (canonicalPassage 0) ∧ β(canonicalMember 1) ≤ 1/2` ; [C] `(∀ k ≤ m, β_k = 1/2) ⟹ VerticalPassage (canonicalPassage m)` ; [C] `¬RH ⟹ ∃ n, β_n < 1/2 ∧ ∀ k < n, β_k = 1/2` ; [⟺RH] aucun premier changement de régime ; [C] profil : `1 ≤ n`, départ ON, montée, `∀ w ≺ l, β_w = 1/2`, `∀ T < T_l, W(T) = 0 ∧ N(T) = N₀(T)`, `1 ≤ W(T_l)`, `l ≺ l*` ; [C] ancre ∧ loi renforcée (historique ON) ⟹ tout ON ⟹ RH ; [C] loi simple ⟹ loi renforcée. [ND] la loi renforcée elle-même. Lock (auteur, 2026-10-09) : « Depuis un zéro ON engagé, prouver que les obligations du passage authentique et de la reconstruction arithmétique exacte maintiennent l'annulation du miroir : le prochain membre conserve la même partie réelle et la progression se poursuit par la hauteur. »  Chaîne unique intégrée (auteur, 2026-10-09) : comptage initial `N(15) = 1` [ND, deux lemmes numériques : `(2πi)⁻¹ ∮_{∂([−1,2]×[0,15])} ξ₁'/ξ₁ = 1`, aucun zéro à `Im ρ = 15`] → ancre `β₁ = 1/2` [C sous le comptage] → loi `β_e = 1/2 ∧ T_e < T_l ∧ (∀ w ≺ l, β_w = 1/2) ⟹ β_l = β_e` [ND, but `False` sous `β_l < 1/2`] → `∀ n, β_n = 1/2` [C sous la loi] → RH [C sous la loi et l'ancre]. Aucune prémisse ajoutée ; trois buts ouverts, build principal rouge. Frontière supérieure (même jour) : [C] `‖ζ(σ+it) − (Σ_{n≤N} n^{−s} − N^{1−s}/(1−s) − N^{−s}/2)‖ ≤ ‖s‖N^{−σ}/σ` (`σ > 0`) ; [C] réflexion : un zéro de hauteur 15 donne un zéro de hauteur 15 avec `σ ≥ 1/2` ; [ND, numérique fini] `‖σ+15i‖·10⁴^{−σ}/σ < ‖main_{10⁴}(σ+15i)‖` sur `[1/2, 1[` (erreur ≤ 0,301, `|ζ| ≥ 0,669`, non certifié). Comptage : [C] principe de l'argument ⟹ le but (a) équivaut à `N(15) = 1` ; [ND] nombre d'enroulements certifié de `ξ₁`. |

Formulation correcte de l'état : plusieurs propriétés et compositions conditionnelles sont compilées ; la transmission
reste ouverte ; l'amorce annoncée comme connue (littérature) est distinguée d'une preuve présente dans le dépôt, dont il
n'existe aucune.

État de référence du build principal (`lake build RHV6Fresh`, EXIT=0, aucune erreur, aucun `sorry`, axiomes `propext`, `Classical.choice`,
`Quot.sound` ; signature 33d944cd61ba, 2026-10-07, après la cible de captivité et le couplage de l'auteur, et les quatre corrections sur la prémisse réduite ; sortie de `scripts/status.sh`) : compilation complète ; unique
prémisse MINIMALE `G := ∀ n ≥ 1, D_n ≤ D_1` (hypothèse explicite `hGain`, aucune `def P…` ; `D_n = ‖r_{n−1}‖² − ‖r_{n−1} − c_n‖²`,
`r_{n−1} = R − Σ_{j<n} c_j` ; instance corrigée : `c_n = m_n · (c_n(x_i)/√x_i)_i`, contribution brute `c_n(x) = −2 Re(x^{ρ_n}/ρ_n)` du membre
canonique de rang `n` (index zéro-source `n − 1`), support `∀ i, 1 < x_i`, `R = (R(x_i)/√x_i)_i`, `R(x) = ψ₀(x) − fond`). Théorèmes qui portent `G` :
`firstGain_collective_relation`, `firstGain_amplitude_bound`, `norm_le_first_of_interaction`, `firstGain_relation`, `norm_le_first_of_interaction_ordered`, `firstGain_canonical`, `canonical_norm_le_first_of_interaction`, `firstGain_smoothed_collective`. `G` n'est dérivée nulle part. [C] normalisation, énumération canonique, identités de gain avec et sans convergence, représentation
exacte du canal LISSÉ normalisé (`smoothedCanonical_hasSum`). [ND] représentation du canal BRUT ; raccord `G ⟹ ∀ w, InsideField z_1 w` (contrôle de
l'interaction, support fixé → `x ≥ 1`) ; ancre ON `β(z_1) = 1/2`. Fermeture compilée `Dom ⟹ RH` (`riemannHypothesis_of_individual_domination`),
`Dom := ∀ w, ∀ x > 0, A_w(x) ≤ A_{z₁}(x)` = CONCLUSION du raccord ouvert ; théorèmes conditionnels à `Dom` :
`riemannHypothesis_of_individual_domination(_onLine)`, `whole_winding_all_passages_of_individual_domination`,
`renewed_height_advance`, `onLine_beta_eq_previous`. Aucun théorème terminal ne prend `G` pour conclure RH ; `RH_FOUND=FALSE`.

Prémisse réduite (2026-10-06) : `G′ : ∀ n ≥ 1, ¬ InsideField(z₁, z_n) → D_n ≤ D_1` ; `G ⟹ G′` [C] ; aux rangs en ligne la conclusion `InsideField(z₁, z_n)` est [C] sous l'ancre ON (`canonical_onLine_insideField`), donc `G′` n'y demande rien ; le raccord ouvert devient `G′ ⟹ ∀ n ≥ 1, InsideField(z₁, z_n)` [ND], posé en hypothèse (`hLink`) de la seule composition `riemannHypothesis_of_restricted_gain_link` (qui l'applique : composition, pas « `G′ ⟹ RH` »). Corrections de l'auteur (2026-10-07) : `G ⟹ G′` affaiblit, ne démontre pas ; `G′` vide si tous les rangs sont ON (cas = RH) ; domination ON par unité de multiplicité, pondérée sous `m_n ≤ m_1` ; support non vide `0 < m` exigé (support vide : `G′` automatique). Cible d'interdiction de compensation `E_n > E_1 ⟹ 2(I_1 − I_n) < E_n − E_1` [ND], incompatible avec la borne sous `G′` dès que `E_n > E_1`, équivalente à `E_n ≤ E_1` sous cette borne ; cible de preuve, hypothèse d'aucune fermeture. Cible centrale (auteur, 2026-10-07) : `Cap := ∀ w, ∀ u ≥ 0, A_w(e^u) ≤ A_1` [ND], `Cap ⟺ ∀ w, InsideField(z₁, w)` [C], `Cap ⟹ RH` sous l'ancre ON [C] ; l'obligation exacte manquante vers `Cap` depuis `G′` est `∀ n ≥ 1, ¬ InsideField(z₁, z_n) ⟹ D_1 < D_n` [ND], c'est-à-dire une borne uniforme des sommes oscillantes `Σ_{p ∈ plage} cos((T_n − T_1) log p − Δφ)` sur des plages de fenêtres d'horizon logarithmique ≥ π/|T_n − T_1| [ND] (E182 : aucune annulation sur une fenêtre de battement < 1/2 demi-tour). Chaînes (2026-10-08) : le coût d'un masquage est [C] (`‖c_n‖² − D_1 ≤ 2‖r_n‖‖c_n‖` sous `G′` hors du champ), aucune borne acquise sur `‖r_n‖` ne l'interdit (condition NÉCESSAIRE au masquage, pas une interdiction ; E183 corrigée : marges min `D_1 − D_n` 0,049 / 0,445 / 2,460 sur 16/100/300 premiers, aucun membre ON ne satisfait `E_n > D_1`) ; les planchers mod 6 des deux arguments sont [C] et minorent la sollicitation sans borner les sommes. Lock (auteur, 2026-10-08) : « Démontrer que la compensation nécessaire pour sortir du champ du premier est incompatible avec la reconstruction arithmétique complète. »
Verrou sémantique : le premier raccord non démontré est `G ⟹ Dom` [ND] (premier gain collectif maximal à tout rang ⟹ chaque amplitude
individuelle sous celle du premier ON sur tout l'horizon) ; en aval, `Dom ⟹ RH` [C] par la réflexion ; en amont, `D_n = ‖c_n‖² + 2⟨Σ_{j>n} c_j, c_n⟩`
[C] et la relation collective bornée par le rang `1` [C sous `G`]. Manque exact (2026-10-06, après la décomposition) : la borne `2(I_1 − I_n) ≤ D_1 − D_n` depuis `G` et la grammaire (identifiée par
`E_n ≤ E_1 ⟺ 2(I_1 − I_n) ≤ D_1 − D_n` [C] ; `D_1 − D_n ≥ 0` est `G` elle-même) ; le passage de `E_n ≤ E_1` sur le support fixé à `∀ x ≥ 1, A_n ≤ A_1`
(les contacts propres lisent l'amplitude mais ne sont pas dans le support) ; la représentation ordonnée des contributions brutes. Lock court : « Déduire du premier gain collectif maximal que chaque contribution reste dans le champ du premier zéro. ».
Ce raccord n'est introduit comme seconde prémisse nulle part.

Formes équivalentes compilées, qui caractérisent la cible locale sans la dériver :

```text
cible locale :  β_e = 1/2 ⟹ D_l = 0
             ⟺  la grille d'arrivée n'est pas translatée
             ⟺  ∀ q > 0, R(q) = R(1)   (transport plat)
             ⟺  β_l = 1/2  ⟺  mirrorMember l = l                    [C] (équivalences), [ND] (la cible)
forme globale : PNoRegimeChange ⟺ RH ⟺ ∃ C, ∀ x > 1, |A(x)| ≤ C√x                          [⟺RH]
```

Canal unique : l'amplitude, donc `Λ(n)` exact ; aucune loi géométrique (translation présente dans `F_δ`). Une liaison
`Λ` exact → `D_l` à travers le produit d'Euler prolongé et la borne `|A(x)| ≤ C√x` caractérisent la cible, elles ne sont pas
dérivées et ne sont pas le verrou en vigueur. Les énoncés compilés rencontrés plus bas (plancher radial, prison à
l'infini, loi de fenêtre, passage de même hauteur, captivité, grille non translatée) décrivent des faits avec leur portée
exacte ; aucun n'est le verrou.

**Routes de fermeture réunies (E152, E153, E154)** — route compilée `Λ → A (reste lissé de ψ) → θ → β → D` ; `Li` n'y figure pas :

```text
W(e,l;q) = θ_l(q) − θ_e(q) = ((T_l − T_e)·log q − (φ_l − φ_e))/π                                  [C]
log R(y) − log R(x) = (β_l − β_e)·(log y − log x)   (R = energyRatio e l)                          [C]
β(z*) − β(z) = 1 − 2β(z)  (z* miroir, T* = T)                                                      [C]
RH ⟺ ∀ z, R_{z,z*} constant ⟺ ∀ e l, β_l = β_e                                                  [⟺RH]
(∀ x > 1, |A(x)| ≤ C x^θ) ⟹ ∀ z, 1 − θ ≤ β_z ≤ θ ;  θ ≥ 1/2 ;  ∀ e l, |β_l − β_e| ≤ 2θ − 1          [C]
(∀ x > 1, |A(x)| ≤ C √x) ⟹ ∀ e l, β_l = β_e                                                     [C]
RH ⟺ ∀ ε > 0, ∃ C, ∀ x > 1, |A(x)| ≤ C x^{1/2+ε}                                                 [⟺RH]
x > 0 : x^β + x^{1−β} ≥ 2√x ;  x ≠ 1 : égalité ⟺ β = 1/2   (paquet nu, sans m/(ρ(ρ+1)) ni phases)  [C]
anti-compensation : (∀ x > 1, |A(x)| ≤ C x^θ) ⟹ ∀ z, max(β, 1 − β) ≤ θ   (lecture du pôle, Mellin)   [C]
E152 : D_{n,n+1} lu sur ψ (n ≤ 30, passages isolés) : ζ +0,0001, W_δ +0,0002 ; pente absolue W_δ +0,079  [N]
Λ ≥ 0 : |Σ_{n<x} Λ(n)(1 − n/x)| ≤ ψ(x) ≤ (log 4 + 4)·x ;  |Σ_k triv_k(x)| ≤ Σ 1/(k+1)²            [C]
∃ C, ∀ x > 1, |A(x)| ≤ C·x   (premiers seuls)  ⟹  ∀ z, 0 ≤ β_z ≤ 1 ;  ∀ e l, |β_l − β_e| ≤ 1         [C]
θ* := inf{θ : ∃ C, ∀ x > 1, |A(x)| ≤ C x^θ} ;  1/2 ≤ θ* ≤ 1 ;  ∀ z, max(β, 1 − β) ≤ θ*              [C]
RH ⟺ θ* = 1/2                                                                                       [⟺RH]
θ* < 1 (bande fixe [1 − θ*, θ*]) : non dérivé                                                       [ND]
F_δ : poids Λ(n)(n^δ + n^{−δ}) ≥ 2Λ(n) ≥ 0 ; = 2Λ(n) (poids de ζ²) ⟺ δ = 0  (n ≥ 2, Λ(n) ≠ 0)         [C]
E153 : A (premiers seuls) − Σ_{300} −2a x^β cos(T log x − φ) ≤ 0,16 × queue (ζ), 0,13 (W_δ)          [N]
E153 : A change de signe (96 fois, x ≤ 10⁷) ; θ̂ : ζ 0,507 ; F_δ, δ = 0,05..0,4 : 0,532..0,907 ≈ 1/2 + δ [N]
Λ(n)² ≤ log n · Λ(n) ;  x ≥ 1 : Σ_{n≤x} Λ(n)² ≤ log x · ψ(x) ≤ (log 4 + 4)·x·log x   (diagonale critique)  [C]
F_δ : w_δ(n)² ≥ 4Λ(n)² ; = 4Λ(n)² ⟺ δ = 0  (n ≥ 2, Λ(n) ≠ 0)                                         [C]
C_{k+1} = C_k e^{π/T} ;  ΔR_k := Re(q^ρ/ρ)|_{C_k}^{C_{k+1}} = −(−1)^k (C_{k+1}^β + C_k^β)/|ρ| ;  |ΔR_k| ≥ 2C_k^β/|ρ| [C]
ε_k := ΔR_k²/(C_{k+1} − C_k) ;  ε_{k+1} = e^{(2β−1)π/T} ε_k ;  ε_{k+1} = ε_k ⟺ β = 1/2   (tout monde)   [C]
𝓔(U) = ∫_{log 10}^U A(e^u)² du : exposant ζ 0,999 ; W_δ, δ = 0,05..0,4 : 1,052..1,797 ≈ 1 + 2δ  (E154)  [N]
E154 : croisés de hauteurs distinctes ≈ −5 % de 𝓔 ; croisé miroir 4a₊a₋cos(φ₊ − φ₋)·e^U non éteint      [N]
cellule π/T : ⟨G²⟩/(⟨masse⟩ log x) = Tr × Dw ;  Tr = ⟨G²⟩/⟨Σw²⟩, Dw = ⟨Σw²⟩/(⟨masse⟩ log x)            [déf.]
E154 : Tr ζ ≈ Tr W_δ (invariance de degré 0 dans la cellule, ne teste rien) ; Tr ζ 0,14..0,34 < Cramér 0,55..0,99 ;
       Dw ζ ≈ 1,03 ; Dw W_0,1 3,4 → 5,0 ; W_0,3 28 → 109 par décade                                     [N]
borne quadratique critique depuis Λ ⟸ (Dw borné [C]) ∧ (Tr borné à toute résolution π/T [ND])              [ND]
p, p' premiers : Λ(p') − Λ(p) = log(p'/p) ;  Tour (β, T), 0 < p, q :  ΔΠ = T log(q/p)/π,                      [C]
    Δ log|q^ρ/ρ| = β log(q/p),  Δ log|q^ρ/ρ|² = 2β log(q/p)   (E155 ; Li hors de toute lecture locale)
Σ_{i<m} c·(log q_{i+1} − log q_i) = c·log(q_m/q_0) ; invariant par permutation des écarts ;
    Σ_{i<m} 2d·g_i = log (q_m/q_0)^{2d}   (télescopage : translation rigide déjà connue)                      [C]
(Re C_k^ρ/ρ)² = |C_k^ρ/ρ|²   (au contact cos Θ = ±1, sin Θ = 0)                                              [C]
|s(n)| = 1 ⟹ |Λ(n)s(n)| = Λ(n), (Λ(n)s(n))² = Λ(n)², Σ_{n≤x}(Λ s)² ≤ (log 4 + 4) x log x                       [C]
niveaux de taille exacte : |w| = Λ, w² = Λ², w = Λ (le dernier : −ζ'/ζ elle-même, aucun témoin)          [déf.]
E155 signes cohérents : P(s(n) = −1) = ½ n^{β₀−1}(1 − cos(T₁ log n)) ; pôles β₀, β₀ ± iT₁ ; même diagonale ;
    β₀ = 0,8 : exposant de 𝓔 1,58, Tr 92 (T_1) → 2,8 (T_300), +0,43 par décade (T_100)                       [N]
E155 Tr aux résolutions π/T_j, j = 1..300 : ζ 0,05..0,29 (plat par décade) ; signes aléatoires 0,85..1,31 ;
    Cramér 0,87..0,98 ; écarts permutés par blocs de 10 : = ζ ; de 1000 : 0,09..0,48 ; de 10⁵ : 15,4 → 1,17   [N]
(Σ w² critique) ⟹̸ (Tr borné) : contre-exemple de même support et même diagonale                          [N + C]
E137bis (p ≤ 5000, 668 marches, 5000 Tours) : ζ κ par magnitude a = 0 : 1,89 ; 1 : 0,14 ; 2 : 0,68 ; 3 : 2,04 ; ≥ 4 : 4,01 ;
    κ global ζ 0,99 ; signes aléatoires 1,01 ; phases aléatoires 1,00 ; écarts permutés 1,08                  [N]
E137bis écart quadratique moyen réponse − demande : ζ 0,47 (plancher) ; signes 7,2 ; phases 7,3 ; écarts permutés 7,6 ;
    paire hors ligne rang 1 δ = 0,1 : 1,16, δ = 0,25 : 2,22                                                 [N]
E137bis bandes T < 100 / 100..1000 / > 1000 : κ 0,97 / 1,11 / 0,83 ; ΣX internes +346, entre bandes −517    [N]
E137bis W_δ (sa propre demande) : κ par magnitude W_0,25 = ζ à 3 % ; W_0,1 dans un facteur 1,4 ;
    D_W/D_ζ / x^{2δ} : 1,24 → 1,05 par décade (δ = 0,25)                                                    [N]
E137bis dette (rang 1, 101, 1001 ; δ = 0,25) compensée par réorganisation libre (w_j ∈ ℂ) : résidu fenêtre ≤ 10⁻¹⁴
    dès 2m > marches ; résidu hors fenêtre 1,04..5,6 × la dette                                              [N]
fermeture « aucune compensation ne cache la dette » = (unicité spectrale ∧ θ* > 1/2 sous dette) [C] ∧ (θ*(ζ) = 1/2) [⟺RH]
E157 (p ≤ 10⁷) : AA 0,2153 (a moyen 2,76), AB 0,2848 (1,85), BA 0,2848 (1,78), BB 0,2150 (2,77) ;
    deux changements consécutifs 31,4 % ; p_{n+2} − p_n = 6(a_n + a_{n+1} + 1) exact ; dette de mot = 4d·log(q_m/q_0) à 10⁻¹⁵ [N]
E157 Tr (T_1, T_10, T_100, T_300) : ζ 0,058 / 0,147 / 0,210 / 0,286 ; blocs 10⁵ : G0 (permutés) 15,0 / 5,15 / 1,68 / 1,15 ;
    G1 (même classe r à chaque rang, grammaire exacte) 16,0 / 5,83 / 1,76 / 1,16 ; G2, G3 (+ voisinage de magnitude) 17,7 / 17,1 à T_1 ;
    M (magnitudes à leur rang, classes permutées) 0,071 / 0,178 / 0,235 / 0,321 ; blocs 10³ : G1 ≈ G0, M ≈ ζ     [N]
E157 canaux τ (décade 10⁶..10⁷) : ζ Tr_τ 0,21..0,53 (AB, BA les plus bas), Σ_τ⟨G_τ²⟩/⟨G²⟩ = 16,8 (T_1), 1,74 (T_100) :
    croisés entre canaux négatifs ; signes aléatoires Tr_τ ≈ 1, croisés −0,4 / −0,06 ; signes cohérents β₀ = 0,8 :
    Tr_τ 15..17 (T_1), croisés +0,74 / +0,69                                                                    [N]
profondeur d → 0 : prix rang–trace d'une paire 4 = double en ligne ; dette de deux pas 4d·log(1 + 18/p) ; excès d'exposant d
budget global (densité) ⟹̸ aucune paire : une paire isolée a une proportion nulle et force θ* ≥ 1/2 + d [C]
E158 fenêtre minimale (cellule a → e → l → b) : 4 membres, 3 passages, M₁ < M₂ < M₃ = p_{n+1}, p_{n+2}, p_{n+3},
    2 écarts ; rang(b) = rang(a) + 3, hauteurs T_a < T_e = T_l < T_b (4 membres, 3 hauteurs) ; avec un passage
    vertical engagé de chaque côté : 6 membres, 5 passages, 5 premiers, 4 écarts ; « 6 passages » non dérivé    [C]
lectures centrales sur p → q : ΔΘ_e = ΔΘ_l = T·log(q/p) ; ‖·‖ en (q/p)^{1/2 ∓ d} ; écart 2d·log(q/p)          [C]
log charge = d·(log(M₂/M₁) − log(M₃/M₂)), impair en d, |log charge| ≤ d·((M₂−M₁)/M₁ + (M₃−M₂)/M₂)          [C]
paire miroir côté premier : P(q,T,d) = q^{1/2+d+iT}/(1/2+d+iT) + q^{1/2−d+iT}/(1/2−d+iT), P(−d) = P(d),
    ∂_d P(0) = 0 ; z_e, z_l d'une cellule contribuent P(q, T, d)                                                [C]
E158 (p ≤ 10⁷, 664 576 triples) : base > 1 dans 51,6 % ; base > 1 ⟺ g'M₁ < gM₂ (100 %) ; g' ≤ g ⟹ base > 1 ;
    médiane |log base| 7,1e−3 (10²..10³), 1,4e−4 (10⁴..10⁵), 2,0e−6 (10⁶..10⁷)                              [N]
E158 cellule synthétique (e, l réels → paire 1/2 ∓ d à T_c), reste exact lu sur ψ : Δ_prof(2d)/Δ_prof(d) = 4,00..4,01 ;
    RMS Δ_prof(0,1)/RMS R_hors sur les 5 premiers du mot 2e−3..1,2e−2 ; Δ_fusion/R_hors 0..0,08 ; pente en d :
    côté premier orienté par le mot 2,00, charge 1,00 ; horizon (T_c ≈ 81, mot 71..89) : d = 0,4 → x ≈ 366,
    0,3 → 3,1e3, 0,2 → 8,3e4 ; d = 0,1 : > 10⁷ à toutes les hauteurs testées                                    [N]
E159 référence = double en ligne 2·q^{s₀}/s₀, s₀ = 1/2 + iT (configuration tendue de zeta23), pas « rien » :
    q^{s₀+d} + q^{s₀−d} − 2q^{s₀} = q^{s₀}·κ_q(d), κ_q(d) = 2(cosh(d log q) − 1), ‖·‖ = √q·κ_q(d)           [C]
    (d log q)² ≤ κ_q(d) ; κ_q(d) = 0 ⟺ d log q = 0 ; 1 ≤ q ≤ X ⟹ κ_q(d) ≤ κ_X(d)                              [C]
    toute lecture linéaire Σ_{1≤n≤X} a_n(·) : ‖paire − double‖ ≤ κ_X(d)·Σ‖a_n‖√n                              [C]
    Δ(q,T,d) = P(q,T,d) − 2q^{s₀}/s₀ : Δ(0) = 0, Δ(−d) = Δ(d), Δ = q^{s₀}κ_q(d)/s₀ + corrections,
    ‖Δ − q^{s₀}κ_q(d)/s₀‖ ≤ (q^{1/2+d} + q^{1/2−d})·|d|/T²                                                       [C]
    paire en ligne serrée 1/2 + i(T ± h) : q^{s₀+ih} + q^{s₀−ih} − 2q^{s₀} = q^{s₀}·2(cos(h log q) − 1),
    −(h log q)² ≤ 2(cos(h log q) − 1) ≤ 0 : contre le double, hors ligne ⟹ courbure ≥ 0, en ligne ⟹ ≤ 0        [C]
    facteur local (s − s₀)² − ε : ε = d² > 0 paire hors ligne, ε = 0 double, ε = −h² < 0 paire en ligne ; lecture
    = q^{s₀}·Σ_k 2ε^k (log q)^{2k}/(2k)! : la courbure dépend de ε au premier ordre ; sign ε classe une
    continuation donnée du double (certificat), aucune lecture des premiers ne le sélectionne                     [C, k = 1 ; série NC]
    le double est une configuration de référence (point de comparaison), pas un événement de l'ordre des membres ;
    une portion hors ligne a une cellule d'entrée et une cellule de sortie distinctes, aucune n'est l'inverse de l'autre
    comptage avec multiplicité et changements de signe de Z : identiques pour la paire et le double (+2, aucun
    changement de signe en T) ; E147 (+1) sépare la paire du simple, pas du double                               [analytique]
E159 (p ≤ 10⁷) : erreur relative ‖Δ − atome/s₀‖/‖Δ‖ ≤ 3,9e−2 à T₁, ≤ 5,7e−3 pour T ≥ 77 ; séparation normalisée requise 1 ⟺
    log X = 0,962/d (d = 0,1 : X ≈ 10^4,2 ; 0,01 : 10^41,8) ; lecture alignée Λ = 0,53..0,78 κ_X ; horizon contre le
    reste exact de ψ (RMS local de (ψ − x)/√x ≈ 0,21) : 4(cosh(d log x) − 1)/|s₀| = RMS, mesuré/prédit 0,46..1,9,
    d·log(horizon) ≈ log(|s₀|·RMS) + cste (1,1..1,4 à T₁, 2,25 à T₂₀, 3,2 à T₁₀₀, 4,8..4,9 à T₁₀₀₀) ;
    plus petites paires en ligne réelles (h = 0,022..0,053) : courbure −(h log X)² au signe près de la paire OFF    [N]
E160 interaction I(u, v) = Re(u·v̄) (terme croisé de ‖u + v‖²) ; continuations du double : radiale P_d − 2q^{s₀},
    verticale L_h − 2q^{s₀} ; pour toute Tour w, toute famille finie (w_i) :
    I(P_d − 2q^{s₀}, w) = κ_q(d)·I(q^{s₀}, w), I(L_h − 2q^{s₀}, w) = c_q(h)·I(q^{s₀}, w), c_q(h) = 2(cos(h log q) − 1)  [C]
    P_{−d} = P_d (ensemble symétrique) : toute lecture, propre ou croisée, paire en d                           [C]
    I(P_d − 2q^{s₀}, w)·I(L_h − 2q^{s₀}, w) ≤ 0                                                                  [C]
    Tour engagée 1/2 + d' + iT' : I(q^{s₀}, q^{ρ'}) = q^{1+d'}·cos((T − T') log q) ; T' ≠ T ⟹ ∀U, ∃u ≥ U de signe +
    et ∃u ≥ U de signe − (q = e^u)                                                                               [C]
    terme propre : ‖2q^{s₀} + (L_h − 2q^{s₀})‖ ≤ 2√q ≤ ‖2q^{s₀} + (P_d − 2q^{s₀})‖ (= √q·|2 + c|, √q·(2 + κ))         [C]
    raffinement : c_q(h) ∈ [−4, 0] pour tout q ; d ≠ 0 ⟹ ∀C ∃q > 1, κ_q(d) > C                                     [C]
    loi « seule la continuation verticale reste compatible sous raffinement » = rien ne compense indéfiniment
    κ_X(d) → ∞ dans le reste = croissance critique                                                               [⟺RH]
E160 (5000 zéros, p ≤ 10⁷, 190 000 points) : rapport exact / (courbure × interaction du double) 0,995..1,000 sur 200
    Tours engagées, radial × vertical < 0 partout ; part des Tours d'interaction > 0 avec le double 0,48..0,51 ;
    J(T) = ∫ (log x)²·canal(T)·R_monde d log x / x, changement radial ≈ +d²J, vertical ≈ −h²J, 300 hauteurs,
    part J > 0 : ζ 1,000 ; θ 0,99 ; W_0,1 1,000 ; ζ sans terme propre 0,46 ; écarts permutés 0,49..0,51 ;
    signes aléatoires 0,49..0,53 : le signe fixe vient du membre présent à la hauteur T (ζ ou paire de W_δ), pas de
    l'ordre ni de la structure multiplicative                                                                    [N]
Quatre secteurs : milieu de la paire m = 1/2 + iT (plan des zéros, distinct de l'origine des Tours), w = s − m ; symétrie exacte conservant la hauteur w ↦ −w̄ (axe critique) ;
    w ↦ w̄ (axe arithmétique) n'est pas une symétrie de ζ (conjugaison T ↦ −T) ;
    {w₁, w₂} avec w₂ = −w̄₁ ou Re w₁ = Re w₂ = 0 ⟹ Im((w₁ − w₂)/2)² = 0 ; paire miroir ⟹ ≥ 0, axe critique ⟹ ≤ 0   [C]
    u² réel ⟹ {±u} invariant par w ↦ w̄, w ↦ −w̄, w ↦ −w ; continuations du double : milieu m, u² = d², u² = −h²     [C]
    (classement d'un seul déplacement recentré ; ne porte ni sur les contacts, ni sur les rayons, ni sur l'ordre)
Tour entière (E161) : u = log x, x^{−1/2}·x^ρ/ρ = Γ(u) = a e^{d u} e^{i(T u − φ)}, a = 1/‖ρ‖, φ = arg ρ, d = β − 1/2     [C]
    contacts u_k = (φ + kπ)/T, Γ(u_k) = (−1)^k a e^{d u_k} (axe arithmétique = axe réel)                          [C]
    Γ(u + π/T) = −e^{dπ/T} Γ(u) ; conj Γ(u) = e^{d(2u − 2φ/T)} Γ(2φ/T − u) ; −conj Γ(u) = e^{d(2u − (2φ+π)/T)} Γ((2φ+π)/T − u)
    indices k ↦ k + 1, k ↦ −k, k ↦ 1 − k ; X(q) ↦ X + 1, −X, 1 − X                                             [C]
    invariance de l'ensemble Γ(ℝ) par w ↦ −w, w ↦ w̄, w ↦ −w̄ : chacune ⟺ d = 0 ; plan brut (d = β > 0) : jamais    [C]
    ordre : u ↦ u + π/T croissante, u ↦ c − u décroissante ; conj Γ_{T,φ} = Γ_{−T,−φ} (Tour du conjugué) ;
    conj Γ_{d,a} = Γ_{−d, a e^{2dφ/T}}(2φ/T − ·) (échange de profondeur)                                         [C]
    numérique : défaut ≤ 2·10⁻¹³ en ligne (T_1, T_10, T_100, 401 contacts), 0/401 points génériques hors ligne
    (W_0,1) et dans le plan brut ; positions des premiers mod 2 denses : images à 10⁻³ d'un premier = uniforme       [N]
Trajectoire et boucle miroir (E162) : Γ_ρ(u) = e^{u(ρ − 1/2)}/ρ ; Γ' = (ρ − 1/2)·Γ (vitesse angulaire T, taux radial d)  [C]
    u < v : ‖Γ(u)‖ < ‖Γ(v)‖ ⟺ β > 1/2 ; > ⟺ β < 1/2 ; = ⟺ β = 1/2 (une Tour seule lit sign d ; la paire miroir non)  [C]
    boucle : conj Γ_ρ(−u) = g(ρ)·Γ_{ρ*}(u), ρ* = 1 − ρ̄, g = (1 − ρ̄)/ρ̄ ; ‖g‖ = 1 ⟺ β = 1/2 ; ‖g‖ > 1 ⟺ β < 1/2       [C]
    β = 1/2 : ρ* = ρ, même Tour, rotation pure ; β ≠ 1/2 : ρ* ≠ ρ, membre véritable (zeta23), profondeur −d            [C]
    S finie, S* = S : conj Σ_{ρ∈S} Γ_ρ(−u) = Σ_{σ∈S} e^{u(σ − 1/2)}/(1 − σ) (mêmes exposants, permutation ρ ↔ ρ*)     [C]
    Im σ ≠ 0 ⟹ 1/(1 − σ) ≠ 1/σ ; ‖1/(1 − σ)‖ = ‖1/σ‖ ⟺ Re σ = 1/2                                               [C]
    côté premier, l'objet après boucle : √x (Σ_{n≤x} Λ(n)/n − log x + γ) + termes triviaux, pas (x − ψ(x) − …)/√x      [N]
    numérique : identité à 4·10⁻¹⁶ ; ‖g‖ = 1 (ζ), 0,9995 / 1,0005 (W_0,1) ; fermeture collective à 3·10⁻¹⁵ dans ζ et
    dans W_δ (800/800 membres hors ligne)                                                                        [N]
Canal antisymétrique (E163) : A_ρ(u) = Γ_ρ(u) − Γ_{ρ*}(u) ; β = 1/2 ⟹ A = 0 ; A_{ρ*} = −A_ρ ; β ≠ 1/2 ⟹ A_ρ(0) ≠ 0      [C]
    S finie, S* = S, H quelconque : Σ_S H(σ*) = Σ_S H(σ) ; Σ_S (H(σ) − H(σ*)) = 0                                  [C]
    H(1 − s̄) = −H(s) ∀s ⟹ H(1/2 + it) = 0 ; H entière ⟹ H ≡ 0 (aucun poids holomorphe impair par le miroir)       [C]
    originale − boucle : poids 1/σ − 1/(1 − σ) ≠ 0 sur la ligne (Im σ ≠ 0) : lit les membres en ligne              [C]
    toute paire β ≠ 1/2 : {ρ, ρ*} stable, Σ (H − H∘*) = 0 ∀H, A_ρ(0) ≠ 0 (absence d'observable ≠ annulation)       [C]
    numérique : Σ H(σ) − Σ H(σ*) = 0 (5 poids, ζ, W_0,1, W_0,4) ; canal orienté Σ sgn(β − 1/2) H(σ) = 0 dans ζ,
    ≠ 0 dans W_δ et reproduit côté premier par ψ_{−δ} − ψ_{+δ} (poids Λ(n) n^{±δ}, deux produits d'Euler) ;
    F − G = (x − ψ)/√x − √x(Σ Λ(n)/n − log x + γ) ≠ 0 dans ζ, reproduit par le poids 1/ρ − 1/(1 − ρ)            [N]
Variation quadratique locale (auteur, 2026-10-03) : fenêtre S ⊂ ]0, ∞[ finie, μ ≥ 0, E(f) = Σ_S μ(q)|f(q)|²,
    ⟨f, g⟩ = Σ_S μ(q) Re(f(q) ḡ(q)) ; paire P_d(q) = q^{1/2+d+iT} + q^{1/2−d+iT}, double P_0 = 2q^{1/2+iT}, atome K = P_d − P_0
    E(P_d + C) − E(P_0 + C) = (E(P_d) − E(P_0)) + 2⟨K, C⟩                                                     [C]
    |P_d(q)|² − |P_0(q)|² = q(4κ_q(d) + κ_q(d)²) ≥ 0, = 0 ⟺ d log q = 0                                          [C]
    R = P_d + C fixé : E(R) − E(R − K) = 2⟨K, R⟩ − E(K) ; ⟨K, C⟩ = ⟨K, R⟩ − ⟨K, P_d⟩                             [C]
    ⟨K, R⟩ = Σ_S μ(q) κ_q(d) Re(q^{1/2+iT} R̄(q)) (lecture de R à la fréquence T) ; pair en d ; K ≠ 0 ⟹ toute valeur
    réelle atteinte par un complément                                                                            [C]
    référence fusionnée à complément égal : aucune représentation à poids Λ (unicité spectrale) [C] ; borne uniforme
    sur ⟨K, R⟩ pour tout T, d : croissance critique du reste [⟺RH] ; « Λ d'énergie minimale » : diagonale égale dans
    tout monde ±Λ, qui porte des membres hors ligne (E155) [C, N]
Champ du premier zéro en ligne (auteur, 2026-10-03) : F₁(x) = ‖x^{ρ₁}/ρ₁‖ = x^{1/2}/|ρ₁| ; w dans le champ ⟺
    ∀ x ≥ 1, x^{β_w}/|ρ_w| ≤ F₁(x)
    β_w = 1/2, T_w ≥ T₁ ⟹ w dans le champ                                                                         [C]
    x^β/A ≤ x^γ/B ∀ x ≥ 1 ⟹ β ≤ γ ; w et w* dans le champ ⟹ β_w = 1/2                                             [C]
    z₁ premier et en ligne : (∀ w, w dans le champ) ⟺ RH                                                          [⟺RH]
    enroulement le long des premiers : T(π/2 + kπ) ≤ T'kπ ⟹ C_k(β', T') < C_k(β, T) ∀ β, β' > 0 (aveugle à β)      [C]
    plan des Tours (E163b) : Tours ON = un même cercle de centre l'origine 0, pôle de rotation de toutes les Tours
    (normalisation propre), cercles concentriques de rayon |ρ₁|/|ρ_n| (normalisation commune) ; paire OFF : même
    pôle de rotation 0, même rotation, demi-somme = cercle × cosh(du)  [N]
β fixé, Tour prisonnière (auteur, 2026-10-03) :
    ‖x^{ρ_w}/ρ_w‖ / F₁(x) = x^{β_w − β₁}·|ρ₁|/|ρ_w|, exposant fixé pour tout x                                       [C]
    β_w = β₁, T_w ≥ T₁ ⟹ w dans le champ ; ∀ w, β_w = β₁ = 1/2 ⟹ RH                                               [C]
    β_w > β₁ fixé ⟹ w hors du champ (aucun changement de β le long de la Tour)                                     [C]
    témoin sans paramètre (miroir, conjugaison, réel sur la ligne), premier zéro 1/2 + i en ligne :
    16^{3/4}/|3/4 + 2i| > 16^{1/2}/|1/2 + i|                                                                      [C]
    prisonnière (arrivée dans le champ du départ, sur un passage) ⟹ β_l ≤ β_e ⟹ T_e < T_l                          [C]
    T_e < T_l sur tout passage de la moitié supérieure ⟹ RH                                                       [C]
    toutes les Tours prisonnières de la précédente ⟺ RH                                                          [⟺RH]
    grammaire du passage (occurrence = minimum attendu, registre) ⟹ T_e < T_l : non dérivé, le passage de même hauteur
    la satisfait                                                                                                   [ND]
financement de l'évasion par le reste exact A(x) (auteur, 2026-10-03 ; E164) :
    β_w > β₁ ⟹ ∀ K > 0, ∃ x ≥ 1, ‖x^{ρ_w}/ρ_w‖ > K·F₁(x)                                                           [C]
    ‖A(x)‖ ≤ C x^θ (x > 1) ⟹ ‖x^{ρ_w}/ρ_w‖ ≤ x^θ/|ρ_w| (x ≥ 1), pour toute Tour                                    [C]
    θ < β_w ⟹ ∀ C, ∃ x > 1, ‖A(x)‖ > C x^θ   (l'évasion se paie dans le reste)                                     [C]
    Λ ≥ 0 + Chebyshev : ‖A(x)‖ ≤ C x, β_w ≤ 1 : le disponible démontré couvre le besoin                            [C]
    règle minimale R(z) : ∃ C, ∀ x > 1, ‖A(x)‖ ≤ C‖x^{ρ_z}/ρ_z‖ et ‖A(x)‖ ≤ C‖x^{ρ_z*}/ρ_z*‖   (définition)
    un seul côté ⟹ ∀ w, β_w ≤ β_z et β_z ≥ 1/2 ; R(z) ⟹ β_z = 1/2 ⟹ RH ⟹ toutes les Tours prisonnières              [C]
    (∃ z, R(z)) ⟺ RH                                                                                              [⟺RH]
    E164 (x ≤ 10⁷, z = premier zéro) : K(x) = |A(x)|·|ρ₁|/√x, max par décade 0,23…0,32 au-delà de 100 (1,55 sous
    100), médiane 0,09 ; témoin δ = 0,25 : 2,9 ; 3,7 ; 7,7 ; 12,9 par décade ; δ = 0,1 non concluant à cette portée   [N]
[les blocs qui suivent (hiérarchie, horizon, double rigidité, captivité, plancher, enroulement imposé) décrivent des
faits compilés avec leur portée ; aucun n'est le verrou en vigueur, qui est le verrou unique ci-dessus]
hiérarchie de Tour à Tour au raccord (correction de l'auteur, 2026-10-03 : l'objet est le couple de Tours successives,
pas A(x) contre la première Tour ; E165) :
    β_z = β_w = 1/2, T_z < T_w ⟹ ∀ x > 0 : ‖x^{ρ_w}/ρ_w‖ < ‖x^{ρ_z}/ρ_z‖, rapport = |ρ_z|/|ρ_w| < 1 (constant),
        π/T_w < π/T_z, T_z log(y/x) < T_w log(y/x) (la vitesse de rotation, T par unité de log x, augmente), arctan 2T_z < arctan 2T_w        [C]
    H(p) : ‖M^{ρ_l}/ρ_l‖ ≤ ‖M^{ρ_e}/ρ_e‖ au premier partagé M et π/T_l < π/T_e   (définition)
    T_e < T_l, T_l ≥ 2 ⟹ H(p), pour toutes positions radiales                                                      [C]
    H(p) ⟹ T_e < T_l ; T_e = T_l ⟹ pas conservé, (T ≥ 2) énergie en M strictement renversée, ¬H(p)                 [C]
    état engagé en e (β_e = 1/2, atteint verticalement), passage e → l, T_l ≥ 2 ⟹ T_e < T_l et H(e → l)            [C]
    état engagé en e, passage e → l, H au passage qui part de l ⟹ β_l = 1/2                                         [C]
    H(e → l) ⟹ H au passage qui part de l : non dérivé (faux dans le monde de rupture engagée)                      [ND]
    (∀ p, H(p)) ⟺ RH ; (∀ p, H(p)) ⟹ toute Tour au moins aussi haute que z₁ est dans le champ de z₁                [⟺RH]
    E165 (300 zéros publiés) : énergie au raccord 0,673…0,9992 (< 1 sur 299/299), pas idem, vitesse × 1,0008…1,487,
    écart de hauteur moyen 2,64 → 1,41 (les hauteurs se resserrent) ; part du premier zéro : 0,216 des amplitudes,
    0,672 des énergies, somme/première = 4,64 ; amplitude de A(x)/√x lue sur les premiers seuls (10² ≤ x ≤ 10⁷) à la
    fréquence T_n, n ≤ 12 : strictement décroissante, mesurée/prévue 0,93…1,12 ; paire de même hauteur d = 0,05…0,4
    aux mêmes raccords : énergie arrivée/départ > 1 sur 300/300 (1,12…436), pas et vitesse inchangés                 [N]
ce que les seuls paramètres (β, T, |ρ|) fixent : horizon de la première Tour (auteur, 2026-10-04 ; E166) :
    x > 0 : ‖x^{ρ_w}/ρ_w‖ ≤ ‖x^{ρ_z}/ρ_z‖ ⟺ x^{β_w − β_z}·|ρ_z| ≤ |ρ_w| ; dépassement ⟺ inégalité renversée          [C]
    β_w ≤ β_z, |ρ_z| ≤ |ρ_w| ⟹ w dans le champ de z pour tout x ≥ 1                                               [C]
    β_z = β_w = 1/2, x > 0 : ‖x^{ρ_w}/ρ_w‖ < ‖x^{ρ_z}/ρ_z‖ ⟺ T_z < T_w                                            [C]
    β₁ = 1/2, x ≥ 1, √x·|ρ₁| ≤ |ρ_w| (a fortiori √x·|ρ₁| ≤ T_w) ⟹ ‖x^{ρ_w}/ρ_w‖ ≤ ‖x^{ρ₁}/ρ₁‖, pour tout β_w < 1 :
        horizon garanti x_h(w) = (|ρ_w|/|ρ₁|)², croissant comme T_w² ; borne uniforme : β_w remplacée par le pire
        cas β_w < 1, ce n'est pas l'horizon de la Tour                                                              [C]
    β₁ = 1/2, β_w ≤ 1/2, |ρ₁| ≤ |ρ_w| ⟹ w dans le champ pour tout x ≥ 1 (membre bas) ; |ρ₁| ≤ T_w ⟹ w ou son
        miroir (celui du côté bas) dans le champ pour tout x ≥ 1                                                    [C]
    membre haut β_w = 1/2 + δ : ‖x^{ρ_w}/ρ_w‖ / ‖x^{ρ₁}/ρ₁‖ = x^δ·|ρ₁|/|ρ_w| ; évasion en x ⟺ x^δ > |ρ_w|/|ρ₁| ;
        δ > 0 : dans le champ en x ⟺ x ≤ (|ρ_w|/|ρ₁|)^{1/δ} (horizon exact) ≥ (|ρ_w|/|ρ₁|)² (horizon garanti)        [C]
    η < δ ⟹ ∀ C, ∃ x > 1, ‖A(x)‖ > C·x^{1/2+η} : lecture asymptotique globale du reste ; ne compare pas un coût
        de sortie au disponible d'un raccord, n'utilise ni raccord ni Tour précédente                              [C]
    portée : modules individuels seuls (ni Λ, ni phases, ni premiers du raccord, ni reste) ; une Tour T_w > T₁,
        β_w > 1/2 sort ; la géométrie emprisonne le membre bas, la difficulté est le gain x^δ du membre haut
        contre ce que poids exacts + phases + reste après le fond autorisent ; disponible démontré x¹             [ND]
    E166 : x_h(n)/p_n = 0,41…0,74 sur les 300 zéros publiés (raccord au-delà de l'horizon garanti, 0/299) ; hauteurs
    approchées par le comptage : raccord sous l'horizon à partir du rang ≈ 600, x_h/p_n = 1,27 ; 4,66 ; 21,6 en
    n = 10³, 10⁴, 10⁵ ; horizon exact d'une Tour de profondeur d à T_n : d = 0,1 : 53 ; 2,9·10⁵ ; 1,7·10¹² ; 6,8·10¹⁵
    (n = 2, 10, 100, 300) ; Σ 1/|ρ_n|² (ligne, moitié supérieure) = 1 + γ/2 − log(4π)/2 = 0,0230957, première Tour
    0,2164 du total, dix premières 0,586, suivantes/première = 3,62, décroissance stricte terme à terme             [N]

    Double rigidité sur un passage e → l, M = Occ(l) (Terminal/DoubleRigidity.lean) :
    liaison premiers–Tour : Occ(l) = p_min(e) (M^Z = M), M premier, Occ(e) < M, Λ(M) = log M,
        π·Π_l(M) = T_l·log M − arctan(T_l/β_l), Π(l) − Π(e) = raccord + T_e·log(p_{n+1}/p_n)                      [C]
    différence de deux positions de lecture dans une même Tour (elle efface le décalage commun sans démontrer qu'il
        est nul ; ce n'est pas « les écarts de premiers sont lus par la hauteur seule dans toute Tour », énoncé de
        l'auteur propre au régime ON, §12) : Π_z(q') − Π_z(q) = T_z·(log q' − log q)/π ; pour 0 < q < q' :
        Π_z(q') − Π_z(q) = Π_w(q') − Π_w(q) ⟺ T_z = T_w ; T_z = π·(Π_z(q') − Π_z(q))/(log q' − log q)            [C]
    β fixé, T < T' : π/T' < π/T ; arctan(T/β) < arctan(T'/β) ; β² + T² < β² + T'² ;
        x^β/√(β²+T'²) < x^β/√(β²+T²) ; T·log(q'/q) < T'·log(q'/q) ; C_k(T') < C_k(T), k ≥ 1                       [C]
    passage T_e < T_l, T_l ≥ 2 : hiérarchie au raccord, β_l ≤ 1/2 ≤ β_e, Π_e(q') − Π_e(q) < Π_l(q') − Π_l(q)       [C]
    passage T_e = T_l : M^Z = M, Λ(M) = log M, Π_l(q') − Π_l(q) = Π_e(q') − Π_e(q) pour tous q, q', pas conservé,
        Π(l) − Π(e) = T_e·log(p_{n+1}/p_n) + (φ_e − φ_l), φ_l < φ_e ; T ≥ 2 : ‖M^{ρ_e}/ρ_e‖ < ‖M^{ρ_l}/ρ_l‖ ;
        Tour d'arrivée non prisonnière                                                                             [C]
    modèle de paramètres (1/4, 2), (3/4, 2), q = 16 : mêmes formules, (16^{1/4})²·(9/16 + 4) < (16^{3/4})²·(1/16 + 4) [C]
    (∀ passage, T_e > 0 ⟹ T_e ≠ T_l) ⟺ RH                                                                         [⟺RH]
    tentative « sur tout passage, hiérarchie au raccord », sans hypothèse ajoutée : un but ouvert, False sur T_e = T_l  [ND]

    Captivité locale au raccord exact, passage e → l, premier du raccord M (Terminal/LocalRaccordCaptivity.lean) :
    ‖x^{ρ_l}/ρ_l‖ / ‖x^{ρ_e}/ρ_e‖ = x^{β_l − β_e}·|ρ_e|/|ρ_l| pour tout x > 0                                       [C]
    coût(q) = (β_l − β_e)·log q ; disponible = log|ρ_l| − log|ρ_e| ;
        ‖q^{ρ_l}/ρ_l‖ ≤ ‖q^{ρ_e}/ρ_e‖ ⟺ coût(q) ≤ disponible ; captivité locale ⟺ coût(M) ≤ disponible              [C]
    captivité locale := ‖M^{ρ_l}/ρ_l‖ ≤ ‖M^{ρ_e}/ρ_e‖, M = p_min(e) : définie par l'énergie seule, sans le raccord ;
        captivité locale ⟺ raccord orienté : théorème séparé (localCaptivity_iff_oriented)                         [C]
    T_e ≤ T_l, T_l ≥ 2, β_l ≤ β_e, q ≥ 2 : disponible ≥ −(β_e − β_l)/4 (peut être < 0), coût(q) ≤ −(β_e − β_l)·log 2,
        coût(q) + (β_e − β_l)·(log 2 − 1/4) ≤ disponible (deux supports seuls)                                     [C]
    T_e < T_l : coût(M) ≤ 0 (β_l ≤ 1/2 ≤ β_e) ; T_l ≥ 2 ⟹ budget tenu avec excédent ⟹ captivité locale,
        par le budget seul (théorème d'orientation non utilisé)                                                    [C]
    T_e = T_l = T ≥ 2, β_e < β_l, q ≥ 2 : disponible ≤ (β_l − β_e)/4,
        coût(q) − disponible ≥ (β_l − β_e)·(log 2 − 1/4) > 0 ; au raccord : captivité locale fausse                [C]
    T_e ≥ 2 : captivité locale ⟺ coût(M) ≤ disponible ⟺ T_e < T_l, les deux sens par le budget                     [C]
    ‖y^ρ/ρ‖ = ‖x^ρ/ρ‖·(y/x)^β ; chaîne : (∀ k, ‖M_k^{ρ_{k+1}}/ρ_{k+1}‖ ≤ ‖M_k^{ρ_k}/ρ_k‖) ⟹
        ‖M_n^{ρ_{n+1}}/ρ_{n+1}‖ ≤ ‖M_0^{ρ_0}/ρ_0‖·∏_{k<n} (M_{k+1}/M_k)^{β_{k+1}}                                   [C]
    M_k ≤ M_{k+1} ⟹ ∏_{k<n} (M_{k+1}/M_k)^{β_{k+1}} ≥ 1 : la chaîne ne donne pas ‖·‖ ≤ ‖M_0^{ρ_0}/ρ_0‖,
        ni décroissance cumulée ni prison globale                                                                  [C]
    captivité locale (avec pas contracté) à tous les raccords ⟺ RH (raccordHierarchy_iff_riemannHypothesis)        [⟺RH]
    transition première exacte X(p) : événement complet de M (rang, prédécesseur, successeur, écarts, classes),
        Occ(l) = M, Λ(M) = log M, événement reconstruit depuis les zéros, pas de l'histoire,
        R(M) − R(M−1) = log M − (fond(M) − fond(M−1)), π·Π_l(M) = T_l log M − arctan(T_l/β_l), registre,
        rapport d'énergie ; X(p) existe sur tout passage (chaque champ est un théorème)                            [C]
    T_e = T_l ≥ 2 : X(p) existe, Z_l(M) = Z_e(M)·rapport·e^{i(φ_e − φ_l)}, ‖Z_e(M)‖ < ‖Z_l(M)‖                      [C]
    (∀ p, T_e = T_l, T_e ≥ 2, X(p) ⟹ captivité locale) ⟺ (∀ p, T_e ≥ 2 ⟹ T_e ≠ T_l) : X faite de faits
        démontrés n'apporte rien comme hypothèse ; Λ(M) = log M seul ne peut interdire le passage                  [C]
    tentative « T_e = T_l ∧ X(p) ⟹ captivité locale » : un but ouvert, coût(M) ≤ disponible, avec
        disponible < coût(M) et tous les champs de X en contexte                                                   [ND]

    Plancher radial de l'arrivée depuis un départ engagé (Terminal/EngagedRadialFloor.lean) ; o → e → l,
    T_o < T_e, β_e = 1/2 :
        un membre n'a que deux coordonnées, β et T : aucune « diagonale » dans zêta ; arrivée hypothétique
        considérée dans ce bloc = (T, 1/2) → (T', β' < 1/2), T' > T (hauteur qui avance, grille d'arrivée translatée),
        avant (T', β') → (T', 1 − β') ; cible alignée = non-translation de la grille (bloc suivant)                [C]
    T_e < T_l, β_l ≤ 1/2 ; β_l = 1/2 ⟺ 1/2 ≤ β_l                                                                   [C]
    seul plancher compilé sur une arrivée : passage suivant l → b, 1/2 ≤ β_l ⟺ T_l < T_b ; il lit le passage
        d'après, aucun plancher ne vient du raccord du passage même                                               [C]
    arrivée translatée hypothétique (β_e = 1/2, T_e < T_l, β_l < 1/2, T_l ≥ 2) : X(p) existe,
        coût(M) = (β_l − 1/2)·log M < 0, coût(M) + (1/2 − β_l)·(log 2 − 1/4) ≤ disponible, captivité locale :
        l'énergie au raccord est du côté de la descente radiale, elle ne donne aucun plancher                      [C]
    (∀ départ engagé, X(p) ⟹ 1/2 ≤ β_l) ⟺ (∀ départ engagé, β_l = 1/2) : X faite de faits démontrés
        n'apporte rien comme hypothèse                                                                             [C]
    (∀ p, T_e < T_l, β_e = 1/2 ⟹ 1/2 ≤ β_l) ⟺ (∀ p, T_e < T_l, β_e = 1/2 ⟹ β_l = β_e) ; nécessaire sous RH        [C]
    plancher ⟹ tout membre au-dessus d'un membre engagé est en ligne, atteint et quitté avec T croissant           [C]
    plancher 1/2 ≤ β_l depuis un départ engagé                                                                     [ND]
    tentative « départ engagé + événement premier successeur ⟹ 1/2 ≤ β_l » : un but ouvert, 1/2 ≤ β_l, avec
                β_l ≤ 1/2, T_e < T_l, coût(M) ≤ 0 et tous les champs de X en contexte                                      [ND]

    Enroulement imposé + captivité au raccord + succession ⟹ λ = 1 (Terminal/EngagedNoTranslation.lean) ;
    pas e → l, β_e = 1/2, T_e < T_l ; λ := facteur radial de l, C_k(l) = C_k^{ligne}(T_l)·λ :
    λ = 1 ⟺ β_l = 1/2 ⟺ ∀ q, Π_l(q) = Π^{ligne}_{T_l}(q) ⟺ ∀ k, C_k(l) = C_k^{ligne}(T_l)                          [C]
    T < T', k ≥ 1 ⟹ C_k^{ligne}(T') < C_k^{ligne}(T)                                                               [C]
    Emboîtée(e, l) := ∀ k ≥ 1, C_k(l) < C_k(e)   (objet)
    β_e = β_l = 1/2, T_e < T_l ⟹ Emboîtée(e, l)                                                                    [C]
    β_e = 1/2 : Emboîtée(e, l) ⟺ ∀ k ≥ 1, C_k^{ligne}(T_l)·λ < C_k^{ligne}(T_e) : l'emboîtement borne λ            [C]
    β_e = 1/2, T_e < T_l, ¬Emboîtée(e, l) ⟹ β_l ≠ 1/2                                                              [C]
    T_e·(π/2 + kπ) ≤ T_l·kπ ⟹ C_k(l) < C_k(e) pour tous β_e, β_l                                                   [C]
    pas engagé, T_l ≥ 2, ensemble : EV_l = EV_e + 1, p_min(e) < p_min(l), T_e < T_l, β_l ≤ 1/2,
        π/T_l < π/T_e, captivité locale, λ ≥ 1, C_k(l) = C_k^{ligne}(T_l)·λ, Π_l = Π^{ligne} + D_l/π,
        Im(q^{ρ_l}/ρ_l) = 0 ⟺ q = C_k(l)                                                                           [C]
    pas engagé + Emboîtée ⟹ 1 ≤ λ et ∀ k ≥ 1, C_k^{ligne}(T_l)·λ < C_k^{ligne}(T_e) : fenêtre de λ                 [C]
    (∀ pas engagé, T_l ≥ 2 : β_l = 1/2) ⟺ (∀ pas engagé : Emboîtée) ∧ (∀ pas engagé : EV + 1 ∧ captivité ∧
        Emboîtée ⟹ ∀ q, Π_l(q) = Π^{ligne}_{T_l}(q))                                                               [C]
    Emboîtée(e, l) sur tout pas engagé, sans condition de profondeur                                               [ND]
    EV + 1 ∧ captivité ∧ Emboîtée ⟹ λ = 1                                                                          [ND]
        tentative : un but ouvert, λ = 1, avec 1 ≤ λ, C_1^{ligne}(T_l)·λ < C_1^{ligne}(T_e) et toute la composition
        en contexte                                                                                                [ND]
    Tour suivante (paramètre de l'auteur) ; e → l → b ; l'enroulement de b est une HYPOTHÈSE de ces énoncés, non dérivé :
    k ≥ 0 ⟹ 1 < C_k(z) : plancher commun, les Tours suivantes s'accumulent vers 1                                  [C]
    Emboîtée(e, l) ∧ Emboîtée(l, b) ⟹ Emboîtée(e, b) ; k ≥ 1 : 1 < C_k(b) < C_k(l) < C_k(e)                        [C]
    β_e = 1/2 : C_k^{ligne}(T_b)·λ_b < C_k^{ligne}(T_l)·λ_l < C_k^{ligne}(T_e) : fenêtre bornée des deux côtés     [C]
    T_e < T_l : (π/T_b < π/T_l) ⟺ λ_l = 1 : équivalence, aucun des deux côtés n'est dérivé                         [C]
    T_e < T_l ∧ T_l < T_b ⟹ λ_l = 1 et ∀ x, Π_l(x) = Π^{ligne}_{T_l}(x)                                            [C]
    T_l = T_b ⟹ π/T_b = π/T_l, ∀ k ∈ ℤ, C_k(b) < C_k(l), Emboîtée(l, b) : place prise par translation, sans
        enroulement ; l'emboîtement des contacts seul ne porte pas l'obligation                                    [C]
    (∀ pas de la moitié supérieure, π/T_l < π/T_e) ⟺ RH                                                            [⟺RH]
    transmission de la contraction, sans hypothèse ajoutée : EV + 1, p croissant (deux pas), π/T_l < π/T_e, capture au
        raccord, β_e = 1/2 ⟹ π/T_b < π/T_l ; tentative : cas T_l < T_b fermé, cas T_l = T_b : but ouvert
        π/T_b < π/T_l avec π/T_b = π/T_l en contexte (EXIT=1)                                                      [ND]
    place parmi TOUTES les Tours : Place(z) := (∀ w ≺ z, Emboîtée(w, z)) ∧ (∀ w ≻ z, Emboîtée(z, w))
    RH ⟹ ∀ z, Place(z)                                                                                              [C]
    β_z < 1/2 ⟹ z ≺ z*, ∀ k ∈ ℤ, C_k(z*) < C_k(z), π/T_{z*} = π/T_z : le miroir prend la place sous z            [C]
    paramètres (1/2,1) ≺ (1/4,4) ≺ (3/4,4) ≺ (1/2,8) : chaque Tour a sa place, k ≥ 1 réel, plancher 1            [C]
    T_e < T_l, T_l ≥ 2 : Captive(l → b) ⟺ λ_l = 1 (capture du raccord SUIVANT)                                     [C]
    ∀ z, ∃ K, ∀ k ≥ K, contacts emboîtés avec toute autre Tour (toutes positions radiales)                         [C]
    ∀ z, Place(z) (tout k ≥ 1) sans hypothèse ajoutée ; Place(l) ⟹ λ_l = 1 ; Captive(l → b) depuis le pas engagé :
        tentatives, EXIT=1 [ND] ; la forme k ≥ K (enroulement à l'infini, §4) est compilée, sujet fermé ; Place n'entre pas
        dans la fermeture
    loi de persistance : ‖Z_z(M₂)‖ = ‖Z_z(M₁)‖·(M₂/M₁)^{β_z}, ‖Z_z(M)‖ = M^{β_z}/‖ρ_z‖ (identité)                      [C]
    rapport transporté R(M) = R(M₁)·(M/M₁)^{β_l−β_e} ; horizontal(p) (β_l > β_e) ⟹ ∃ premier q ≥ N, ‖Z_e(q)‖ < ‖Z_l(q)‖ [C]
    inégalité PC(p) := ∀ M ≥ M_min(e), ‖Z_l(M)‖ ≤ ‖Z_e(M)‖ : de type RH, (∀ p, PC(p)) ⟺ RH, pas la loi de persistance   [⟺RH]
    depuis l'état engagé, le pas suivant n'est pas de même hauteur : tentative sans hypothèse ajoutée, but False (EXIT=1)    [ND]


```

## 13. Pistes closes

```text
V : C⁺(z*) < p_min(z), collision L ∧ V, clôture par l'inversion, collision à l'entrée, PInvertedLiaison,
    PInvertedVerification, RH ⟺ PInvertedLiaison ∧ PInvertedVerification, comparaison de deux Tours :
    retirés du code ; V comparait la seconde Tour à la référence d'un autre zéro ; sur une même grille,
    k₂(·) = k₂(p_min z*) et k₂(·) < k₂(p_min z*) partitionnent : « A ∧ ¬A »
pivot commun p_min(z) de la seconde Tour : retiré ; V obtenu par construction (299/299 automatique)
accord des grammaires comme criticité ; commutation S T_d = T_d S ⟺ d = 0 ⟺ β = 1/2
prémisses retirées : PNoNullPassage, PHeightProgression, PEnergyBalanceAtRaccords, PRaySuperposition,
    PNoStrictInterlacing, PZeroInsertionDepth (∀ z, D_ins = 0), PLocalReadingOrientation, PPastOnLine,
    PVerticalEnergyPush, PVerticalDominatesAtRaccord, PMirrorEventIdentity, PMirrorTransport, PGrammarByHeight,
    PTowerRaccordOrientation (∀ p, Or(p)), PNoLowOffZero (∀ z hors ligne, T_z ≥ 2)
excès inter-Tours J(p) = (T_l − T_e)·log(p_{n+2}/p_{n+1}) > 0 ⟺ T_e < T_l : c'est la progression de hauteur
quartet : ∏ R_i = ∏ f(s_{i+1})/f(s_i) = 1 (cobord) ; holonomie 1
grammaire signée (E133) : fonction de l'indice seul ; soudure de cobord d'état ‖χ_N(ρ)/χ_M(ρ)‖ = 1 ⟺ Re ρ = 1/2
Q = f ∘ T : tautologie fonctionnelle, n'exclut pas une loi couplée Q(T, β)
réponse radiale au premier ordre : vraie pour f
course L(t) / comptage de fenêtre : non poursuivie
numéro de cellule, place dans la cellule, grammaire, mod 6, occupation, produit d'Euler tronqué, M comme porteur
« exactement deux contacts », « l'unique cellule I = [C⁻, C⁺] », « la Tour sélectionne un premier »,
    « isoler un terme est impossible » : faux (§4, §5, §9)
ΔT_min : équation, satisfaite par ΔT = 0
voie Mellin de la somme des Tours : −ζ'/ζ(s) = s/(s−1) + s·M(s), M transformée de ψ(x) − x ; hors build
flèche dans l'enroulement, la fréquence ou la résolution π/T : coordonnée de hauteur, séparée de la pente β [C]
pente lue sur une plage finie x ≤ X comme loi : horizon x ≥ (cT)^{1/d} pour chaque membre [C + N]
platitude D_{n,n+1} entre hauteurs distinctes comme ancre : vraie aussi dans W_δ (E152) ; ancre = miroir ou θ* [C + N]
Λ ≥ 0 (+ Landau) ⟹ θ* = 1/2 : Λ ≥ 0 ne donne que θ = 1 ; vraie dans F_δ, θ*(F_δ) = 1/2 + δ ∈ [1/2, 1[ [C + N]
« Li + reste exact » comme nom de la route compilée : la route est Λ → reste lissé de ψ
« le carré élimine les compensations » : elles deviennent des croisés ; le croisé miroir ne s'éteint pas [N]
identité de cellule homogène de degré 0 en le poids (Tr, ⟨G²⟩/⟨Σw²⟩) comme loi séparant ζ de W_δ : invariante [N]
contenu d'une cellule (C_k, C_{k+1}] par Li(C_{k+1}) − Li(C_k) : moyenne de comptage, pas objet local (E155)
accumulation radiale Σ 2d·g_n sur les écarts exacts comme contrainte nouvelle : télescopage (E155) [C]
diagonale (|w| = Λ ou w² = Λ²) comme contrôle du transfert Tr : signes cohérents, même diagonale, Tr non borné (E155) [C + N]
témoin « w = Λ exactement avec membres hors ligne » : c'est ζ, ce serait un contre-exemple, pas un contrôle
loi de partage D/X par magnitude (κ par classe) comme séparatrice ζ / W_δ : W_δ a le même partage renormalisé (E137bis) [N]
κ global comme mesure d'organisation : ζ 0,99 ≈ hasard 1,01 (E137bis) [N]
rigidité de compensation testée sur une fenêtre finie à contributions libres : compensable si 2m > marches (E137bis) [N]
    — sous-détermination des équations de demande, pas « aucune fenêtre de ζ ne décide » ;
loi de fenêtre sur les seuls premiers partagés de la cellule, ou terme d'ordre 1 en d côté premier : P paire en d [C],
    défaut sous le reste jusqu'à l'horizon (E158) [N] ;
loi de fenêtre à horizon premier fixé X : sépare la paire du double d'au plus κ_X(d) → 0 quand d → 0 (E159) [C] ;
    comptage (N avec multiplicité, signes de Z) ou rang comme séparateur paire / double : identiques, le rang par membre
    distinct est une étiquette [analytique] ; extrapoler la proportion de zeta23 vers 1 [C, E157] ;
    « les premiers lisent sign ε » : certificat d'une continuation donnée [C, E159] ; interaction avec les Tours
    engagées comme sélecteur : factorisée par la courbure propre, signe fixé par la phase ou par le membre présent,
    même sens dans W_δ (E160) [C, N] ; stabilité sous raffinement comme loi nouvelle : croissance critique [⟺RH] ;
    double comme événement de l'histoire, portion hors ligne comme paire qui sort puis revient [analytique] ;
    symétrie d'une paire recentrée comme sélecteur : automatique pour toute paire invariante par w ↦ −w̄ [C] ;
    symétrie à quatre secteurs de la Tour entière comme loi : ⟺ d = 0 du membre donné, certificat (E161) [C]
    fermeture de jauge (boucle miroir remise dans l'ordre + unicité spectrale ⟹ chaque Tour invariante) : la boucle
    permute ρ ↔ ρ*, l'objet collectif a les mêmes exposants et les coefficients 1/(1 − σ), l'unicité ne donne que
    S* = S ; exacte dans W_δ (E162) [C, N] ; « ni orientation ni trajectoire » : faux, Γ' = (ρ − 1/2)Γ [C]
    canal antisymétrique (originale − miroir) comme contrainte : Σ_S H(σ) = Σ_S H(σ*) ∀H, aucun H holomorphe impair,
    absence ≠ annulation, W_δ porte le canal par deux produits d'Euler (E163) [C, N] ; objet fixé membre par membre
    par la boucle : ⟺ ρ* = ρ, la conclusion [C]
    variation quadratique locale (paire séparée − référence fusionnée) : terme croisé = ⟨K, R⟩, lecture du reste à la
    fréquence T, ni nul ni signé par l'algèbre ; borne uniforme [⟺RH] ; « Λ d'énergie minimale » : vide (unicité) ou
    faux au niveau diagonal (E155) [C, N]
    rigidité sur toute l'histoire comme pièce manquante : unicité spectrale + θ* > 1/2 sous dette, déjà [C]
orientation du demi-tour (C⁻ ↔ C⁺) comme marque OFF, ou Λ(p) orienté : seconde Tour = première Tour de z* lue à rebours
    (rfl, existe en ligne, z* = z) ; contacts miroirs jamais égaux [C] ; Λ(p) > 0 saut de la somme entière ;
    corr(G_k, F_k) T_1 : ζ +0,58, W_0,1 +0,77, grille translatée β = 0,4 +0,68 (E156) [C + N]
grammaire modulo 6 (états, transitions τ, mots, alternance) comme porteur de la régularité de ζ aux résolutions π/T :
    surrogat G1 de grammaire exacte, Tr = écarts permutés ; magnitudes à leur rang suffisent (E157) [N]
canaux de transition comme contrainte nouvelle sur la compensation : la compensation passe entre canaux ;
    grammaire identique dans W_δ et dans le monde de signes cohérents [C + N]
« dette miroir attachée à la progression grammaticale » comme contrainte nouvelle : 4d·log(q_m/q_0), télescopage [C]
budget global de zeta23 (proportion, même portée à 1) comme exclusion d'une paire : densité aveugle à une paire ;
    rang–trace tendue, paire proche = double en ligne [zeta23 + C]
croissance des écarts entre premiers contre la plage de phase d'une Tour : ΔΘ = T_n·log(1 + g_n/p_n) → 0 quand n → ∞ ;
    piste réfutée, non reproposée
écarts de hauteur croissants entre membres consécutifs : les écarts se resserrent en moyenne (E165 : 2,64 → 1,41) ;
    piste réfutée, non reproposée [N]
zéros fabriqués (remplacement, insertion, perturbation, grille décalée, paire/signal synthétique, OFF à hauteur d'un ON :
    E147, E159, E163b, E172, E173, E184, E186, E200, E221, E231–E238, E243, E244, E302, E304 OFF, E305, E309 fabriqués,
    E312 synthétique) et conclusions « X ne contraint pas β » ; inférences « vrai pour ζ(s−δ)ζ(s+δ) donc sans contrainte » :
    retirées comme énoncés sur zêta (§101) ; théorèmes compilés inchangés [démarche]
« besoin constant aux rencontres » présenté comme loi dérivée : réfuté avant d'être proposé ; sa forme quantifiée ⟺ RH ; le but
    `∃ 1 ≤ x < y, A_w(x) ≤ A_w(y)` reste [ND] (§102)
« verrou du couple (T, β) » présenté comme contrainte sur `β` : identités et caractérisations vraies pour toute `β` ; le but en
    forme de couple `∃ k, A_w(C_{k+1}) = A_w(C_k)` reste [ND] (§103) ; conclusions des expériences à OFF fabriqués non réutilisées
« fréquence occupée », « un seul signal par fréquence », « fréquence prise » présentés comme dérivés des écarts : définitions et
    caractérisations ; `Un ⟺ RH`, `(∀ w, Pris(w)) ⟺ RH` ; le but `Pris(w)` reste [ND] (§104), réduit à `C_0(w) = C_0^{ligne}(T_w)` [ND] (§105, R10') ; le sens imposé est écarts ⟶
    fréquences engendrées ⟶ point de rencontre à une demi, aucune en dessous
« ce qui manque = borne √x / lecture des poids / amplitude libre / couple libre » : réfutés (§101) ; manque = rigidité
    écarts exacts ⟶ amplitude forcée, sens unique [ND]
« centre » employé pour deux objets : origine (pôle de rotation de toutes les Tours, plan des Tours) ≠ milieu de la paire
    miroir m = 1/2 + iT (plan des zéros) ; « le centre du zéro précédent » comme objet commun à deux Tours ; deux hauteurs
    donnent deux milieux, une seule origine ; l'équivalence symétrie centrale ⟺ β = 1/2 ⟺ ρ = m relie des propriétés
    sans identifier 0 et m [C] ; « la Tour part de son zéro » ou « est centrée sur son zéro » : faux, la Tour brute vaut
    1/ρ en x = 1 et 2^ρ/ρ en x = 2 (§4)
```

## 14. Règle anti-régression et format de livraison

Réorganisation du 2026-10-15 (auteur) : unique énoncé ouvert de la chaîne, `off_signal_amplitude_incompatible` [ND] : sous l'ancre [C], départ ON, passage qui monte, historique ON, pour tout zéro `w` à la hauteur du zéro suivant tel que `x ↦ 2x^{β_w − 1/2}/‖ρ_w‖` soit strictement décroissante sur `x ≥ 1` (⟺ `β_w < 1/2` [C]) : `False`. Conservation `β_l = β_e` [C sous cet énoncé] : côté haut exclu [C], `β_l < 1/2 ⟹` amplitude décroissante [C]. En contexte [C] : `R(x) = Σ' −m x^ρ/(ρ(ρ+1))`, aucun remplacement ne reconstruit, `β(mirror w) = 1 − β_w` et amplitude croissante, `‖R‖ ≤ C x^θ ⟹ β ≤ θ` pour tout zéro, `‖R‖ ≤ C x` [C], `T_w > 28` [C]. Portée : quantifié sur tous les passages, ⟺ RH sous l'ancre [⟺RH] (`radial_conservation_law_iff_riemannHypothesis`). Lock de l'auteur : « l'amplitude d'un OFF situé à < 1/2 est incompatible avec le signal des écarts des premiers et ne peut pas être synchronisé » ; ni « la ligne » ni β dans le lock.

Toute modification déclare : formules changées, avec la section sémantique d'où elles descendent ; si la
représentation de l'état propre change ; si la définition d'une preuve change. Une
correction remplace la formule fausse à sa place ; aucun paragraphe correctif n'est ajouté en fin de document ;
aucune définition correcte n'est retirée. Toute livraison est en français et se réduit au bloc de build du maître Lean §14
(auteur, 2026-10-09 : « l'erreur de compilation, son analyse, et rien après ») : bloc ÉTAT (ce qui a été fait) en tête du statut, puis erreurs réelles de `lake build RHV6Fresh` (fichier, ligne,
signature du théorème, contexte complet, but), puis leur analyse ; rien d'autre. Retirés définitivement : toute évaluation de RH, RÉFUTÉ,
BORNÉ, SÉLECTIONS, le bloc du premier raccord (2026-10-06), la prémisse et ses porteurs, le bloc ROUTE UNIQUE, le tableau des dépendances,
le bloc CIBLE DE TRAVAIL et la zone SEMANTIC LOCK (2026-10-09). Le verrou (§12 : une fois le régime engagé, la partie réelle du zéro
suivant est la même que celle du zéro qui a engagé le régime) est la lecture du but ouvert de la chaîne unique ; il n'est plus affiché.

---

Version purgée et consolidée le 2026-10-02 par Claude Opus 5.5, sur ordre de l'auteur ; historique dans le
journal git.

**Note de renvoi du 2026-11-09 (cohérence).** Ce maître mathématique n'a pas été mis à jour depuis le 2026-10-25. Tout ce qui suit cette date
(réorientation §19, route des contacts, plan K0–K6, plan Φ, modules isolés jusqu'à `Terminal/CollectiveSlopeOnPieces.lean`, E465) est
consigné dans `RHV6final_STRATEGIE_SEMANTIQUE.md` §19 et dans `HANDOVER_20261107_LIGNE.md` ; en cas de conflit, le théorème compilé
puis le passage le plus récent l'emportent (`CLAUDE.md` §1bis).
