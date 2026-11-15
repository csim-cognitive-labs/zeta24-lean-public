> Version française conservée à titre de référence. Main language: English, see README.md.

# E406–E411 — le canal brut côté zéros, la décomposition fréquentielle, la cassure, la borne aux rencontres

Pré-enregistré AVANT exécution (2026-11-02). Suite logique demandée par l'auteur après E404, E405 et
`Terminal/RawMeetingRemainder.lean` : relier l'organisation des hautes fréquences (E404) au contrôle du reste brut aux
rencontres (condition terminale d'E405, `riemannHypothesis_of_psiRemainder_at_events`). Sens conservé : axe réel →
premiers → écarts → cassures → hautes fréquences → contacts et amplitudes → (β, T). Aucune hypothèse nouvelle. Le
compilateur tranche. Tous les théorèmes en ligne, aucun code dupliqué, aucune sonde.

## 0. Rectification préalable (audit du corpus, avant toute écriture)
§19.35.2 affirmait que « le canal brut n'avait aucun objet compilé côté zéros ». C'est inexact : `Terminal/InverseReading.lean`
(auteur, 2026-09-30) définit `spectralRemainder N = stepAt zeroChannelPrimitive N`, le pas sur la cellule `[N, N+1]` de la
primitive absolument convergente `x · Σ' ρ, −m(ρ) x^ρ/(ρ(ρ+1))`, et prouve `arithmetic_eq_spectral : exactRemainder N =
spectralRemainder N` (`N ≥ 2`), avec `exactRemainder N = ψ(N) − stepAt backgroundPrimitive N`. C'est EXACTEMENT la convention
de sommation demandée par E406 : la série brute ponctuelle `Σ x^ρ/ρ` n'est pas absolument convergente, mais son intégrale sur
la cellule unité l'est ; comme `ψ` est constante sur `[N, N+1[`, l'intégrale de cellule de `ψ` est `ψ(N)` et l'identité
exacte au saut est attribuée à une somme absolument convergente, sans ordre de sommation ni convention au point de saut.
Ce qui manquait réellement : le lien entre cet objet et `psiRemainder N = ψ(N) − N` d'E405 (une correction bornée de fond),
l'instanciation par seuil fréquentiel, et une BORNE de ce que les basses fréquences peuvent réaliser à une cassure.

## 1. Livrables et objets (module isolé `Terminal/RawSpectralChannel.lean`, non ajouté à `RHV6Fresh.lean`)
- **E406 (canal brut côté zéros, convention de cellule)** : `psiRemainder_eq_spectral_add_correction` : à tout entier
  `N ≥ 2`, `ψ(N) − N = spectralRemainder N + c(N)` avec `‖c(N)‖ ≤ cellBackgroundConstant` (constante explicite : un demi,
  la dérivée logarithmique de zêta en zéro, et deux fois la somme des zéros triviaux). Convergence : `channelOn_summable`
  (déjà compilé) ; la convention est le pas de cellule, consignée dans la docstring.
- **E407 (décomposition fréquentielle exacte)** : `lowFrequencies H` (indices de hauteur absolue au plus `H`, les deux
  branches), finitude (`lowFrequencies_finite`, par `explicitIndex_locallyFinite`), et l'instance
  `exactRemainder_split_frequency H N : exactRemainder N = localPacket (low H) N + localPacket (low H)ᶜ N`, même sens de
  convergence (sous-séries d'une série absolument convergente). Idem sur l'incrément à la rencontre
  (`remainderIncrement_split_frequency`).
- **E408 (raccord cassure / hautes fréquences)** : le théorème central nouveau,
  `norm_packetIncrement_finite_le : ‖packetIncrement (↑s) N‖ ≤ Σ_{ρ∈s} m(ρ)` pour toute famille FINIE `s` d'indices et
  tout `N ≥ 1` : la seconde différence du canal de cellule d'un zéro est bornée par sa multiplicité (deux inégalités des
  accroissements finis, dérivées `x^ρ/ρ` puis `x^{ρ−1}`, et `x^{β−1} ≤ 1` car `β ≤ 1`). Donc les basses fréquences ne
  peuvent réaliser à elles seules une cassure plus grande que leur nombre (compté avec multiplicité). Conséquence
  compilée `break_realized_by_high_frequencies` : à tout entier `N ≥ 2`,
  `‖packetIncrement (low H)ᶜ N‖ ≥ Λ(N+1) − 1 − 4τ − K(H)` où `τ` est la constante compilée des zéros triviaux et
  `K(H) = Σ_{ρ ∈ low H} m(ρ)`. À un premier `p` : la part de la cassure `log p` qui dépasse `1 + 4τ + K(H)` est portée
  NÉCESSAIREMENT par les fréquences au-dessus de `H`. C'est la lecture P-A4 d'E404 (« la cassure exige des fréquences
  bien au-delà de la foule ») transformée en théorème, avec un déficit explicite. Plancher de fréquence
  (`frequency_floor_of_low_realization`) : si les fréquences au plus `H` réalisent seules la cassure en `p` (complément
  d'incrément nul), alors `K(H) ≥ log p − 1 − 4τ`.
- **E409 (amplitudes et coordonnées)** : aucun théorème nouveau ; audit de ce qui est récupérable avec les théorèmes
  compilés : `radial_from_amplitude_step`, `inversion_radial`, `two_contacts_height_quantized` (par membre, à partir de SES
  contacts) ; `spectral_weights_unique` (la fonction totale sur tout `x > 1` détermine chaque poids). Ce qui n'est PAS
  compilé : la récupération des composantes à partir des seules valeurs aux rencontres (entiers). Consigné tel quel.
- **E410 (composition des rigidités)** : `off_member_forces_break_and_excess` : un membre à `β > θ` force (E405) une
  rencontre brute `E` avec dépassement du reste brut, ET à cette rencontre, pour tout seuil `H`, la cassure est réalisée
  au-dessus de `H` à hauteur d'au moins `Λ(E) − 1 − 4τ − K(H)` (E408). Chaîne nommée théorème par théorème dans §19.36 ;
  raccords ouverts identifiés.
- **E411 (recherche de la borne aux rencontres)** : deux tentatives au plus, journalisées avec le but exact du compilateur
  (`COMPILE_JOURNAL.md`). Tentative 1 : réduire `|ψ(E) − E| ≤ C E^{1/2+ε}` par la décomposition fréquentielle
  (correction bornée + paquet bas + complément haut) et lire les buts restants. Critère d'échec déclaré : si le but restant
  sur le paquet bas exige `β ≤ 1/2` pour les zéros bas (circulaire) ou si le but restant sur le complément est la borne de
  queue elle-même, la tentative est morte et le théorème est retiré. Tentative 2 : borner le complément par la seconde
  différence (E408) : critère d'échec déclaré : si la seconde différence ne contrôle pas la valeur (elle contrôle les
  variations, pas le niveau), la tentative est morte. Aucune hypothèse nommée ne sera posée.

## 2. Jumeaux numériques (script `e406_e411_raw_spectral_channel.py`, borné, réel, aucune sortie fabriquée)
Données : `experiments/data/odlyzko_zeros6_2001052.txt` (SHA-256 vérifié), crible de `Λ` jusqu'à `2·10^6`. Constantes
de fond par mpmath (dérivées logarithmiques de zêta en 0 et −1, somme des zéros triviaux). Temps attendu : < 3 minutes.
- Volet E406 : aux premiers `p ∈ {4547, 9587, 9931, 104729, 1000003}` et aux entiers voisins, comparer `ψ(N) − N` à
  `spectralRemainder N + c(N)` (convention de cellule, 2 001 052 zéros, deux branches par partie réelle doublée) ; lire le
  résidu de troncature (attendu petit : la série de cellule converge comme `1/γ²`) et vérifier `‖c(N)‖ ≤ cellBackgroundConstant`.
- Volet E407/E408 : à `p = 4547` et `p = 9587`, pour `H ∈ {30, 100, 300, 594, 1000, 3000, 10^4, 3·10^4, 10^5, tout}` :
  incrément du paquet bas `packetIncrement (low H) (p−1)` contre sa borne compilée `K(H)` (attendu : très au-dessous), part
  de la cassure `log p − 1` portée par le complément, et le `H` minimal tel que `K(H) ≥ log p − 1 − 4τ` (plancher compilé)
  contre le `H` observé en E404 (ordre `π p`). Prédiction écrite : le plancher compilé est très en dessous de l'observé
  (il ne lit que le comptage, pas les phases) ; l'écart entre les deux est la mesure de ce qu'E408 ne capture pas.
- Volet E411 : `‖localPacket (low H)ᶜ (p)‖ / √p` pour les mêmes `H` et `p` : lecture seulement, aucune conclusion sur
  l'exposant (jumeau, pas preuve).
R12 : tout est axe réel (vrais premiers, vraie fonction en escalier, vrais zéros) ; les constantes de fond sont
analytiques et non projectives ; le lien `K(H)` ↔ Riemann–von Mangoldt, s'il est invoqué, est PROJECTION (R12) et ne sera
pas compilé ici.

## 3. Critères
- Le module compile sans `sorry`, axiomes standard ; sinon : erreurs exactes journalisées, deux tentatives par pas.
- E411 : succès = la borne dérivée ; échec attendu = un but résiduel affiché par le compilateur, copié tel quel.
- Aucune fermeture déclarée tant que la borne n'est pas démontrée sans hypothèse équivalente à RH.

## Résultats (exécution du 2026-11-02, 4,5 s, sortie `e406_e411_results.txt` ; aucune sortie fabriquée)
Module `Terminal/RawSpectralChannel.lean` : 37 déclarations, compilé (`lake build`), aucun `sorry`, axiomes standard ;
trois passages journalisés (`COMPILE_JOURNAL.md`). Constantes lues : c₀ = −log 2π = −1,8379 ; c₁ = 1,9851 ; τ = π²/6 ;
`cellBackgroundConstant` = 5,628.

### Volet E406 (identité de cellule)
`ψ(N) − N = spectralRemainder N + c(N)` vérifiée au résidu de troncature de la liste : 2,4·10⁻² à N ≈ 9,6·10³ (résolution
π·N/γ_max = 0,027), 0,30 à N = 10⁵ (résolution 0,29), 4,3 à N = 10⁶ (résolution 2,8 > 1 : la liste ne résout plus la
cellule, comme prévu). La correction `c(N)` vaut 1,3379 (constante, à 10⁻¹¹ près : la part des zéros triviaux est
négligeable), sous la borne compilée 5,628. La seconde différence du fond vaut un à 10⁻¹¹ près (borne compilée 4τ = 6,58,
très lâche). Prédiction tenue.

### Volet E407/E408 (paquet bas à la rencontre contre sa borne compilée)
Pour p = 4547, 9587, 104729 et dix seuils : l'incrément du paquet bas est TOUJOURS sous la borne `K(H)` (théorème
`norm_packetIncrement_finset_le`), mais de trois à six ordres de grandeur : quotient 10⁻³ à H = 30, 10⁻⁴ à 10³,
10⁻⁵ à 10⁴, 2·10⁻⁶ avec toute la liste. Le plancher compilé (`frequency_floor_of_low_realization`) ne demande que
K(H) ≥ 0,8 à 4,0, c'est-à-dire H ≥ 14,1 ou 21,0 : il est trivialement satisfait, alors qu'E404 observe que la cassure
nette exige H de l'ordre de π·p (1,4·10⁴, 3,0·10⁴, 3,3·10⁵). Prédiction tenue : le théorème de comptage est vrai et
très faible ; l'écart (de quatre à cinq ordres de grandeur) est la mesure de ce qu'E408 ne capture pas, l'annulation
de phase entre les secondes différences des basses fréquences. Part de la cassure (log p − 1) portée au-dessus de H
(convention de cellule, identité exacte côté total) : p = 4547 : 100 % jusqu'à H = 10³, 57 % à 10⁴, 11 % à 3·10⁴, 3 % à
10⁵ ; p = 9587 : 100 % jusqu'à 3·10³, 72 % à 10⁴, 27 % à 3·10⁴, 6 % à 10⁵ ; p = 104729 : 96 % à 10⁴, 93 % à 3·10⁴, 83 %
à 10⁵, 32 % à 3·10⁵, 6 % avec toute la liste (γ_max = 1,13·10⁶ ≈ π·p/0,3 : la liste ne suffit plus). La lecture P-A4
d'E404 se reproduit dans la convention de cellule, avec des dépassements de 100 % à certains seuils (le paquet bas
s'oppose transitoirement à la cassure) : les phases s'organisent, elles ne s'additionnent pas.

### Volet E411 (lecture seule)
Niveau du complément divisé par √p, dix seuils : 0,0002 à 0,08 ; décroît avec H à liste fixée ; aucune lecture
d'exposant (jumeau).

### Ce que l'expérience ne dit pas
Elle ne dit rien sur β : les hauteurs réelles portent déjà un demi (hypothèse de données). Elle mesure l'écart entre un
théorème compilé (comptage) et un mécanisme observé (phases), sans le combler.
