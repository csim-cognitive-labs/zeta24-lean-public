# E404 — Somme des contacts sur l'axe réel le long de chaque écart : montée, cassure, redescente (2026-11-02)

Pré-enregistrée AVANT exécution (ce fichier est engagé avant le lancement du script ; les résultats sont ajoutés après).

## Demande de l'auteur (reprise en mots)
Étudier non plus l'amplitude d'un contact isolé mais la somme de tous les contacts sur l'axe réel, suivie le long de
l'axe à l'intérieur d'un écart jusqu'au point de rencontre, puis dans l'écart suivant. Deux cas comparés sur les mêmes
vrais écarts : l'enchaînement des zéros sur la ligne (fréquence qui avance à chaque zéro, amplitude stable) et
l'enchaînement dégénéré d'une chaîne OFF (deux membres sur une fréquence qui n'avance pas, amplitude scindée en une
croissance trop faible et une trop forte). Aucune projection, aucune statistique : chaque écart choisi est lu seul,
valeur par valeur. Comportement à isoler : la montée progressive de la somme jusqu'à un maximum très précis au point de
rencontre, qui doit être l'écart exact (la cassure), puis la redescente immédiate pour laisser l'écart suivant
recommencer. Lecture de l'auteur, mesurée et non posée : la montée vers la cassure est portée par la fréquence qui
augmente fortement d'un zéro ON au suivant. Les deux canaux sont faits, à la demande de l'auteur (le brut d'abord).

## Deux canaux, séparés
- **Canal brut** (jumeau NON compilé dans le corpus) : la fonction de Tchebychev en escalier contre son fond régulier.
  Sur l'axe, entre deux premiers consécutifs, la somme des zéros monte avec une pente régulière égale à un, et au
  premier suivant elle chute d'un coup d'une hauteur égale au logarithme de ce premier. Le cumul depuis le début de
  l'écart atteint donc, juste avant la rencontre, l'écart arithmétique exact (différence des deux premiers, à un
  terme de fond près), puis chute du logarithme du premier : c'est la cassure brute.
- **Canal lissé** (canal compilé, celui d'E402/E403) : la demande A(x) = Σ_{m<x} Λ(m)(1 − m/x) contre le fond B(x)
  d'E401. La somme des dépôts est continue ; la cassure y est un changement de pente au point de rencontre, et le
  cumul depuis le début de l'écart vaut au point de rencontre la demande exacte de l'écart (Z_n d'E402/E403).
Dans les deux canaux le même facteur de phase exp(iγ log x) sert à tous les zéros ; seul le poids change (1/ρ pour le
brut, −1/(ρ(ρ+1)) pour le lissé).

## Ce qui est calculé (déterministe, borné, aucune sortie fabriquée)
1. Vrais écarts : premiers ≤ 10 000 (1229 écarts), Λ par crible, ψ et A exacts ; fond brut et fond lissé.
2. Zéros : les 2 001 052 hauteurs du fichier Odlyzko (SHA-256 vérifié), posées sur la ligne (hypothèse de données).
3. Écarts choisis, un par un, sans moyenne : n = 4, 614, 1228 (ceux d'E403), le plus long écart arithmétique,
   le dernier écart de longueur 2, et n = 100, 300, 500, 800, 1000. Plus une fenêtre de six écarts consécutifs
   (n = 614 à 619) suivie en continu, sans remise à zéro.
4. Pour chaque écart, grille de 100 points de x entre p_n + 1/2 et p_{n+1} − 1/2 (jamais sur un premier : la formule
   brute y vaut la moyenne des deux côtés), puis le point p_{n+1} + 1/2 pour la redescente. En chaque point : somme
   signée de tous les zéros dans les deux canaux, valeur vraie par crible, résidu de troncature. Pour le brut, aussi
   la somme tronquée en fréquence aux seuils 30, 100, 300, 1 000, 3 000, 10 000, 30 000, 100 000, 300 000 et T_max,
   pour voir COMMENT la montée et la cassure se construisent quand la fréquence augmente (lecture de l'auteur).
5. Décomposition par fréquence croissante au point de rencontre : la montée (valeur en p_{n+1} − 1/2 moins valeur en
   p_n + 1/2) et la chute (valeur en p_{n+1} + 1/2 moins valeur en p_{n+1} − 1/2), toutes deux cumulées zéro par zéro
   par rang, lues aux mêmes seuils de fréquence et au seuil de foule π/ℓ. Les deux canaux.
6. Jumeau OFF dégénéré, SÉPARÉ : un bloc de zéros ON consécutifs retiré et remplacé par des paires de position radiale
   0,3 / 0,7 à la hauteur médiane entre le zéro retiré et le suivant (jamais la hauteur d'un zéro existant ; vérifié).
   Trois tailles de bloc : 1 (rang 2000, comme E403), 50 (rangs 2000–2049), 500 (rangs 2000–2499). Le premier zéro
   n'est jamais touché (fait : il est ON). Mêmes grilles, mêmes points, mêmes décompositions ; différence point par
   point avec le réel, dans les deux canaux.
7. Jumeaux mpmath (30 décimales) : sur trois écarts, au point p_{n+1} − 1/2, la somme brute et la somme lissée sur
   les 2 000 premiers zéros, comparées à la somme numpy tronquée au même rang ; A et ψ en mpmath.

## Prédictions écrites avant exécution
Prédictions de l'auteur : (P-A1) montée progressive et régulière ; (P-A2) sommet très précis égal à l'écart exact au
point de rencontre ; (P-A3) redescente immédiate ; (P-A4) le dernier élan vers la cassure est porté par les
fréquences qui montent fortement ; (P-A5) la chaîne OFF n'atteint pas le sommet exact et ne redescend pas de la même
manière.
Prédictions de l'exécutant : (P-E1) canal brut : à troncature totale, cumul avant rencontre = écart arithmétique
exact à un résidu de troncature près de l'ordre du dixième, et chute = logarithme du premier au même résidu près ;
la pente de montée vaut un partout ; (P-E2) canal brut : aux faibles seuils de fréquence, la montée est déjà
presque entière (pente un portée par les basses fréquences) mais la cassure est étalée ; la cassure se resserre
quand le seuil monte, sa largeur en x étant de l'ordre de π·p/T ; donc l'élan final est bien porté par les hautes
fréquences, pas la montée ; (P-E3) canal lissé : cumul au point de rencontre = Z_n à 10⁻⁷ près, profil continu
avec cassure de pente ; (P-E4) jumeau OFF : différence point par point non nulle, croissant en p^{0,4}, plus grande
avec le bloc ; au niveau du bloc 500, la différence dépasse le résidu brut de troncature ; (P-E5) rien n'est
conclu sur β des vrais zéros.

## Lancement
`cd formalization/RHV6Fresh/experiments/E404_ContactSumProfile`
`nohup timeout 900 python3 -I e404_contact_sum_profile.py ../data/odlyzko_zeros6_2001052.txt 10000 . > e404_run.log`
Borné (< 15 min). Sorties : `e404_profiles.txt`, `e404_window.txt`, `e404_freq_decomposition.txt`,
`e404_synthetic.txt`, `e404_summary.txt`, `e404_run_log.txt`.

## Résultats (exécution du 2026-11-02, 140,6 s, sortie `e404_summary.txt` ; aucune sortie fabriquée)

Provenance : fichier Odlyzko vérifié (SHA-256 identique), 2 001 052 zéros, hauteurs posées sur la ligne (hypothèse de
données). Écarts choisis : n = 4, 100, 300, 500, 614, 800, 1000, 1182 (le plus long, 9551 → 9587), 1223 (dernier de
longueur 2, 9929 → 9931), 1228. Fenêtre continue n = 614 à 619. Jumeaux mpmath : brut et lissé à 10⁻¹² ou mieux.

### Canal brut (jumeau non compilé) : la montée, le sommet exact, la chute
- **Montée** : sur chaque écart lu, la somme de tous les contacts monte avec une pente régulière égale à un et atteint,
  juste avant la rencontre, l'écart arithmétique exact (la vérité par crible est exactement « différence des deux premiers
  moins un » sur la grille de demi-entiers, sans puissance de premier intérieure dans les écarts choisis). Valeurs lues
  (calcul / vérité) : n = 614 : 22,970 / 23 ; n = 1182 : 35,081 / 35 ; n = 1228 : 32,889 / 33 ; n = 100 : 8,9993 / 9 ;
  n = 4 : 0,99940 / 0,99942. L'écart entre calcul et vérité est le résidu de troncature de la liste (max 0,06 à x ≈ 10⁴),
  il grandit avec l'abscisse, et il est de l'ordre de la pente mesurée point par point (min 0,92, max 1,04 pour n = 614).
  Sur les écarts de longueur deux (n = 500, 1223), la grille de cent points est plus fine que la largeur de résolution
  de la liste (environ π·p / T_max ≈ 0,03) : le profil y est dominé par l'ondulation de troncature aux deux bords
  (pente lue de −5,6 à +7,8), la montée vaut 0,97 / 1 et 0,91 / 1. P-A1 et P-A2 tenues au niveau du résidu de
  troncature ; P-E1 tenue.
- **Chute** : entre p_{n+1} − 1/2 et p_{n+1} + 1/2 la somme chute d'exactement un moins le logarithme du premier
  (vérité) : n = 614 : −7,393 calculé / −7,422 vérité (log p = 8,422) ; n = 1228 : −8,115 / −8,211 ; n = 4 :
  −1,56542 / −1,56541. La cassure brute est donc bien un saut d'une hauteur très précise, celle du logarithme du
  premier rencontré. P-A3 tenue.
- **Redescente « presque à zéro »** : NON tenue au sens littéral. Après la chute, la somme ne revient pas à sa valeur
  de départ : elle est plus haute de « écart arithmétique moins logarithme du premier » (n = 614 : 24 − 8,42 = 15,58,
  valeur lue 15,577). La fenêtre continue sans remise à zéro le montre : départ 0 à p_614, puis 23 → 15,58 → 16,3 →
  9,16 → 17,5 → 12,7 → 16,5 → 10,3 → 21,7 → 17,9 → 23,2 au fil de six écarts ; la somme dérive, elle ne revient pas
  à zéro écart par écart. Ce qui revient vers zéro est la dérive x − ψ(x) sur de longues plages, et cela est le
  contenu du théorème des nombres premiers, donc de la projection (R12). Dans le canal brut, le « up and down »
  de l'auteur est exact pour les deux hauteurs (montée = écart exact, chute = log p) mais le point de retour n'est pas
  zéro ; il est zéro seulement si l'on remet l'origine à chaque rencontre, ce que fait le module Lean
  (`contactSumProfile_continuation`) comme un changement d'origine, pas comme un retour de la somme.
- **Décomposition par fréquence croissante** (`e404_freq_decomposition.txt`), écart n = 614 (p = 4523 → 4547, seuil
  de foule π/ℓ = 594) : montée cumulée 0,29 avec les trois premiers zéros, −0,90 à T ≤ 100, 0,34 à T ≤ 300, 2,79 au
  seuil de foule (336 zéros), 13,9 à T ≤ 1 000, 16,5 à T ≤ 3 000, 20,1 à T ≤ 10 000, 24,5 à T ≤ 30 000 (dépassement),
  22,96 à T ≤ 100 000, 22,97 avec tous. La montée n'est donc PAS portée par les basses fréquences : elle se construit
  entre le seuil de foule et vingt fois ce seuil. Chute cumulée au même écart : 0,01 à T ≤ 30, 0,28 au seuil de foule,
  −0,25 à 1 000, −1,90 à 3 000, −3,24 à 10 000, −8,79 à 30 000 (dépassement), −7,46 à 100 000, −7,39 avec tous. La
  chute se construit encore plus haut : elle exige des fréquences de l'ordre de π·p_{n+1} ≈ 1,4·10⁴ et au-delà, c'est-à-
  dire vingt-cinq fois le seuil de foule. Même lecture sur les autres écarts (n = 1228 : montée 18,2 au seuil de foule
  587, 31,6 à 10⁴, 33,3 à 3·10⁴, 32,9 avec tous ; chute −0,05 au seuil de foule, −2,1 à 10⁴, −7,8 à 3·10⁴, −8,1 avec
  tous). **Lecture P-A4 (auteur) : tenue dans ce canal.** Le dernier élan vers le sommet exact et la cassure elle-même
  sont réalisés par les membres de fréquence la plus haute, bien au-delà de la foule de l'écart ; la fréquence doit
  monter fortement, jusqu'à l'ordre du premier rencontré fois π, pour que la cassure soit nette. **Lecture P-E2
  (exécutant) : FAUSSE pour la montée** (prédite déjà portée par les basses fréquences ; elle ne l'est pas), vraie pour
  la cassure.

### Canal lissé (compilé) : profil continu, sommet exact à la demande, cassure de pente
- Sommet : au point de rencontre la somme des contacts vaut la demande exacte de l'écart à 10⁻⁸ près sur tous les
  écarts choisis (n = 614 : 1,992073544·10⁻² contre Z_n = 1,992072673·10⁻² ; résidu max sur la grille 1,6·10⁻⁸).
  C'est le théorème `contactSumProfile_meetingPoint` lu numériquement.
- Forme : le profil est continu et courbe (n = 614 : 0 → 0,0073 → 0,0135 → 0,0184 → 0,0221 → 0,0247 → 0,0260 →
  0,0262 → 0,0251 → 0,0229 → 0,0199 à la rencontre → 0,0191 après) : il monte, plafonne au milieu de l'écart, puis
  redescend AVANT la rencontre ; la cassure n'est qu'un changement de pente, la montée n'est ni régulière ni
  monotone jusqu'au sommet. Le sommet exact (la demande) n'est pas un maximum du profil. P-A1 et P-A3 ne se lisent
  pas dans ce canal ; P-A2 se lit (sommet = demande exacte), P-E3 tenue.
- Fréquences : la montée lissée est presque entière dès T ≤ 1 000 (n = 614 : 0,0220 contre 0,0199 ; n = 1228 : à
  10⁻⁵ près dès 3 000) : le poids en un sur T² de ce canal éteint les hautes fréquences. Ce canal ne voit donc PAS
  l'élan de haute fréquence qui fait la cassure brute ; il la lisse.

### Jumeau OFF dégénéré, SÉPARÉ (bloc de rang 2000 remplacé par des paires 0,3 / 0,7, hauteurs médianes, aucune
hauteur d'un zéro existant, distance minimale au zéro le plus proche 1,5·10⁻³ ; blocs de 1, 50 et 500)
- Canal brut : la différence point par point avec le réel, au point p_{n+1} − 1/2, vaut pour le bloc 1 : 3,3·10⁻³
  (n = 4), 0,079 (n = 100), 0,18 (n = 614), 0,43 (n = 1228) ; bloc 50 : jusqu'à 4,2 (n = 1223) ; bloc 500 : 3,9 à
  11,9, c'est-à-dire de l'ordre de la cassure elle-même (log p ≈ 8 à 9). Le long de l'écart n = 614 la différence du
  bloc 500 oscille entre −5,7 et +5,1 à l'intérieur d'un seul écart : la chaîne dégénérée n'ajoute ni pente régulière
  ni saut, elle ajoute une ondulation de la taille de la cassure dont la position n'est pas celle du premier. Ces
  différences dépassent le résidu réel de troncature (max 0,06) pour les trois blocs sur tous les écarts choisis
  sauf le bloc 1 à n = 4 (3,3·10⁻³ contre 4,9·10⁻⁶ : dépasse aussi). Aucune borne compilée n'existe dans ce canal
  (le canal brut n'est pas dans le corpus) : il n'y a rien à « violer » ; le jumeau est seulement en désaccord avec la
  vérité par crible, que seule une liste de zéros complète reproduit (même situation qu'E403, R12 : comparaison faite
  sur l'axe réel, vrais écarts, vraie fonction en escalier ; aucune projection).
- Canal lissé : différences 10⁻⁷ à 3·10⁻³ (bloc 500, n = 1228 : 2,7·10⁻³ contre résidu 1,4·10⁻⁹), toutes au-dessus du
  résidu réel, comme en E403 ; les bornes de queue compilées d'E402/E403 (eps_online ≈ 10⁻⁵ à 7·10⁻⁴) ne sont pas
  recalculées ici ; le bloc 500 les dépasserait à n = 1228 (2,7·10⁻³ > 7,4·10⁻⁴ borne max d'E403), ce qui est noté
  sans être conclu : la borne d'E403 suppose la liste réelle, pas le jumeau. P-A5 tenue au sens « la chaîne OFF ne
  reproduit ni le sommet exact ni la chute exacte » ; P-E4 tenue (croissance avec le bloc et avec l'abscisse ; aucune
  loi de puissance lue, les phases s'y mêlent).
- P-E5 : rien n'est conclu sur β des vrais zéros ; les hauteurs réelles portent déjà un demi.

### Ce que l'expérience ne dit pas
Elle n'explique pas pourquoi la liste réelle fait monter la somme avec la pente un ni pourquoi la chute vaut log p :
ce sont les deux faces de l'identité brute (somme des zéros = fond moins fonction en escalier), qui est une vérité de
la liste complète. Le canal brut n'est pas compilé ; le canal lissé l'est (`Terminal/ContactSumProfile.lean`).
