# E405 — Le reste brut aux points de rencontre : jumeau numérique du module `RawMeetingRemainder.lean` (2026-11-02)

Pré-enregistrée AVANT exécution (engagée avant le lancement ; résultats ajoutés après). Exécution bornée (< 10 min),
réelle (crible), aucune sortie fabriquée. Trois volets SÉPARÉS : réel (premiers par crible, zéros Odlyzko sur la ligne),
jumeau OFF synthétique (hauteurs jamais égales à une hauteur ON existante), identités déterministes.

## Ce que le Lean compile (à vérifier numériquement, pas à découvrir)
1. Reste brut `r(N) = ψ(N) − N`. Entre deux rencontres (entiers de poids non nul), `r` descend d'exactement une unité par
   entier ; à une rencontre il saute du poids. Donc, entre deux rencontres, `|r|` est majoré par le maximum de ses valeurs
   aux deux bouts (`abs_rawRemainder_le_of_noEvent`).
2. Pont brut → lissé à l'entier : `M·A(M) = Σ_{k<M} ψ(k)` (`natMul_smoothedVonMangoldtSum_eq`,
   `rawCumulative_eq_sum_massA`).
3. Une borne `|r(E)| ≤ C·E^θ` et `|r(E−1)| ≤ C·E^θ` aux seules rencontres `E` donne la même borne à tout entier
   (facteur `C·2^θ + 1`, Bertrand), puis `‖reste lissé(x)‖ ≤ C'·x^θ` pour tout `x > 1`, puis `β ≤ θ` pour tout membre
   (`zero_re_le_of_rawRemainder_at_events`).

## Volet 1 — réel, identités (déterministe)
- Crible de Λ jusqu'à X = 2 000 000 ; `r(N)` pour tout N ≤ X.
- Vérification exacte de 1 (descente d'une unité entre rencontres, sur tous les N) et de 2 (pour M dans une liste fixée).
- Pour θ ∈ {0.50, 0.52, 0.55, 0.60} : maximum de `|r(E)|/E^θ` et `|r(E−1)|/E^θ` sur les rencontres E ≤ X, maximum de
  `|r(N)|/N^θ` sur tous les N ≤ X, et vérification de l'inégalité compilée `max_N ≤ (2^θ·max_E + 1)` (le +1 vient de N = 1).
- Par tranche dyadique [2^j, 2^{j+1}) : maximum de `|r(E)|/√E` aux rencontres (lecture : croît-il ? ne tranche pas θ).

## Volet 2 — tentative A (pré-enregistrée en §19.34.5), réel
- Aux points de rencontre p_{n+1} (premiers ≤ 100 000) : reste lissé exact `R(p) = A(p) − B(p)` (fond d'E401 par mpmath),
  = somme télescopée des demandes des écarts précédents + R(p_1). Signe de chaque demande, nombre de changements de signe,
  maximum de `|R(p)|/p^θ` pour θ ∈ {0.5, 0.6, 0.7}. Critère d'échec déclaré : si aucune loi d'annulation ne s'écrit
  autrement que « la somme partielle EST le reste », A est une tautologie (prédiction de l'exécutant).

## Volet 3 — tentative B (pré-enregistrée en §19.34.6), réel + jumeau synthétique, minimal
- Six écarts consécutifs n = 614..619 (ceux d'E404). Au point de rencontre p = p_{n+1} : canal brut, somme des termes
  `x^ρ/ρ` des zéros de hauteur < π·p (tête) contre le reste brut vrai moyenné des deux côtés (crible) ; queue = vrai − tête.
- Paire synthétique β = 0.6 à une hauteur T choisie au milieu de deux hauteurs ON consécutives (jamais une hauteur ON) :
  dépôt brut de la paire aux six rencontres, pas entre rencontres consécutives, comparé à la tête et à la queue.
- Critère d'échec déclaré : si l'absorption du pas de la paire par la tête n'est contrainte que par la constance par membre
  (⟺ RH, §19.21), B est morte (prédiction de l'exécutant).

## Règle
Aucune conclusion sur β ne sera tirée des maxima numériques : le manque est l'exposant aux rencontres, et seul le
compilateur le tranche. Les chiffres servent de jumeau des identités et de lecture, pas de preuve.

## Résultats (ajoutés après exécution ; `e405_results.txt`, 4,2 s ; un premier lancement s'est arrêté après le
volet 1 sur un cast numpy → mpmath, corrigé par `int(p)`, relancé au complet, volet 1 identique)
Volet 1 (réel, identités). Crible jusqu'à deux millions : 148 933 premiers, 149 235 rencontres brutes. La descente
d'une unité par entier entre rencontres est exacte sur les 1 850 765 entiers non-rencontre (écart zéro). L'identité
« M fois la somme lissée en M égale la somme des ψ(k) pour k < M » tient à l'arrondi machine près pour les sept M
testés. Les maxima de |ψ(N) − N|/N^θ à toutes les rencontres (deux côtés) et à tout entier respectent l'inégalité
compilée (facteur 2^θ plus un) pour les quatre exposants ; le maximum global est atteint en N = 1 (valeur un).
Tranches dyadiques jusqu'à deux millions : le maximum de |ψ(E) − E|/√E aux rencontres oscille entre 0,19 et 0,71
sans tendance lisible à cette échelle. Aucune conclusion sur θ : la croissance ultime n'est pas une mesure.
Volet 2 (tentative A). 9 592 rencontres (premiers ≤ 100 000) : 4 777 demandes positives, 4 814 négatives, 471
changements de signe ; la somme télescopée des demandes est, à l'identique, le reste lissé au dernier point moins
le reste au premier. Les quotients |R(p)|/p^θ sont tous petits (maximum atteint sur les tout premiers p) et
décroissent. Verdict par le critère déclaré : A est une tautologie. La « loi d'annulation » n'est que la valeur du
reste ; aucune identité sur les seuls premiers n'apparaît qui donnerait l'exposant autrement.
Volet 3 (tentative B, minimale). Six rencontres consécutives (4547 à 4591) : la tête (zéros de hauteur inférieure
à π fois le premier, quinze mille environ) porte presque toute la somme vraie ; la queue est de l'ordre du dixième.
La paire synthétique (β = 0,6, hauteur jamais ON) dépose entre −0,31 et +0,36 à chaque rencontre, du même ordre que
la queue. Son pas entre rencontres consécutives (−0,43 à +0,67) est dominé par la rotation de phase ; le facteur
radial entre deux rencontres consécutives est de 1,0003 à 1,0021 seulement. Lire β sur un pas exigerait de séparer
la phase de l'amplitude à cette échelle, ce que ni la tête ni la queue ne font. Verdict par le critère déclaré :
B est morte (seule la constance par membre contraindrait l'absorption, et elle équivaut à RH).
