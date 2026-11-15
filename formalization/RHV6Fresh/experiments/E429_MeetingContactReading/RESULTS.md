# E429 — Résultats (exécutée 2026-11-04, après le pré-enregistrement c6cdbc12)

Pièces : `logs/e429a.log`, `logs/e429b.log`, `logs/e429c.log` (post-hoc), `data/e429{a,b}_results.json`,
`data/e429c_posthoc.json`, `logs/lean_attempt{1,2,3}.log`, `logs/lake_build_full.log` (`lake build RHV6Fresh` vert).
Exécution : 2 s (a), 4 s (b), 2 s (c). Aucune sortie fabriquée ; tous les nombres ci-dessous sont lus des journaux.

## Identités (P1–P6) — niveau 1 : réussi, avec une localisation déclarée
* **P1, P5, pivot : 0 violation** sur 24 Tours × 2 000 rencontres (encadrement `C_k ≤ p < C_{k+1}`, nombre de contacts
  entre rencontres à moins d'une unité de `T·log(q/p)/π`, pivot ≤ dernier contact ; pivot = dernier contact sur
  100 % des rencontres : aucune rencontre n'est elle-même un contact).
* **P2 (valeur à la rencontre depuis le dernier contact)** : erreur relative ≤ 4·10⁻⁹ jusqu'au rang 10 000
  (T ≈ 10⁴) ; au-delà (rangs 10⁵, 10⁶, 2 001 052 ; T de 7·10⁴ à 1,1·10⁶), erreur relative double précision jusqu'à
  7·10⁻⁶ **sur les rencontres où `cos(πf)` est de l'ordre de 10⁻⁴ à 10⁻⁵**. Localisation post-hoc (e429c, 30 chiffres)
  aux pires points : **l'identité tient à 10⁻²¹** ; la valeur directe en double précision y est elle-même fausse de
  3·10⁻⁶ relatif (argument du cosinus ~ 10⁷). L'écart est le conditionnement du calcul, pas l'énoncé. Facteur de
  croissance `(p/C_k)^β = e^{βπf/T}` : 2,8·10⁻¹⁵ partout.
* **P3** : lecture radiale aux deux contacts encadrants : erreur max **5,8·10⁻¹⁰** (toutes Tours, toutes rencontres) ;
  lecture tangentielle au dernier contact : ≤ 4·10⁻⁹ jusqu'au rang 1 000, puis 10⁻⁷ à 3·10⁻³ aux grandes hauteurs
  (même conditionnement : `T/tan` avec `tan ~ 10⁶` ; à 30 chiffres 10⁻¹⁹) ; lecture sur la valeur à la rencontre : de
  2·10⁻¹² (rang 1) à 1,5·10⁻² (rang 2 001 052), même cause (division par `πf` et logarithme d'un cosinus petit).
* **P4** : Tour + miroir = 1 à 8,5·10⁻¹⁰ ; écart miroir − Tour = 0,4 = 1 − 2β exactement ; décalage des fractions de
  cellule Tour/miroir égal à `(φ_β − φ_{1−β})/π` modulo 1 à 6,7·10⁻¹⁰ (0,009 au rang 1, décroissant en 1/T).
* **P6** : `breakResidual_erase` et `breakResidual_erase_pair` vérifiées à 2,7·10⁻⁸ et 1,5·10⁻⁸ absolu sur des
  valeurs de l'ordre de 10⁸ (relatif 10⁻¹⁶ ; le README disait « 10⁻¹⁰ » sans préciser absolu/relatif : il s'agit du
  relatif). Lecture radiale aux rencontres sur le canal lissé (649 Tours × 1 999 écarts) : 3·10⁻¹¹.
* **Jumeaux mpmath** : (a) indices `k` identiques, fractions, valeurs et lectures à 10⁻¹⁵ (rang 1) et 10⁻¹⁰
  (rang 2 001 052) ; (b) dépôts des paires 6·10⁻¹⁴ relatif, `ψ₁` exact 10⁻¹³, résidu de troncature `ε` (H = 100) 2·10⁻¹³.

## Mesures sans attente (a)
* Fractions de cellule aux rencontres : histogrammes à 10 classes plats (de 172 à 237 par classe sur 2 000) pour
  toutes les Tours, en ligne et hors ligne ; moyenne 0,49–0,51.
* Contacts par écart : 0,02 (rang 1 ; 1 963 écarts sur 1 999 sans contact), 0,33 (rang 100), 1,96 (rang 1 000),
  13,6 (rang 10 000), 1 563 (rang 2 001 052).
* Information radiale du comptage (nombre de contacts entre rencontres différent entre β = 0,3 et β = ½) : 0,8 % au
  rang 1, 0,1 % au rang 10, 0,2 % au rang 100, 0 à partir du rang 10 000 (cohérent E428).

## Résidu, insertion, absorption (b)
* Résidu de troncature par écart (famille des 649 zéros de hauteur ≤ 1 000) : 12,5 en moyenne, 156 au maximum,
  pour une cassure exacte moyenne de 7,6·10⁴ (1,6·10⁻⁴ relatif).
* Paires insérées (hauteurs synthétiques 17,5 et 23,0) : part moyenne du dépôt de la paire dans la cassure exacte
  0,6 % (hors ligne) contre 0,2 % (témoin en ligne) ; part dans la somme des modules des dépôts de la famille 18 %
  et 14 % (hors ligne) contre 6,4 % et 4,8 % (en ligne) ; aucune paire ne dépasse jamais la cassure ; module du dépôt
  sur les 12 premiers / 12 derniers écarts : 1,54 → 793 (hors ligne, 17,5) contre 1,23 → 220 (en ligne, 17,5).
* **Coût d'absorption par pondération libre des 649 Tours authentiques** (solution de norme minimale) :

  | m écarts | hors ligne 17,5 | témoin en ligne 17,5 | rapport | hors ligne 23,0 | témoin 23,0 | rapport |
  |---|---|---|---|---|---|---|
  | 12 | 15,3 | 13,9 | 1,10 | 7,06 | 6,08 | 1,16 |
  | 120 | 669 | 389 | 1,72 | 315 | 193 | 1,63 |
  | 600 (rang 564) | 1,9·10⁶ | 7,8·10⁵ | 2,47 | 1,8·10⁵ | 6,5·10⁴ | 2,73 |
  | 1 200 (sur-déterminé) | résidu rel. 0,73 | 0,75 | — | 0,79 | 0,81 | — |
  | 2 000 | 0,71 | 0,73 | — | 0,43 | 0,49 | — |

  **Critère pré-enregistré de l'obligation Deux satisfait** (le rapport croît de m = 12 à m = 600 pour les deux
  paires). **Mais** : (i) le coût absolu est du même ordre pour la paire en ligne (étrangère elle aussi à la
  famille) ; (ii) post-hoc (e429c) : **retirer le zéro authentique de rang 1** et le faire absorber par les 648
  autres coûte 13,2 (m = 12), 364 (120), 1,1·10⁶ (600), résidu relatif 0,83–0,86 au-delà : **autant que la paire hors
  ligne** ; le zéro de rang 10 coûte 0,86 / 32 / 2 786, le rang 100 : 0,04 / 1,07 / 15. Le coût mesure la rareté
  des basses fréquences dans la famille, pas la position radiale. La croissance du rapport hors ligne/en ligne
  (1,1 → 2,5) est l'exposant `p^{½−β}` déjà compilé (`mirror_deposit_ratio`), rien de plus.
* **Obligation Trois** (deux paires hors ligne, 17,5 et 23,0) : annulation `c < 0,1` sur 4,3 % des rencontres ;
  **plus longue suite de rencontres consécutives annulées : 21** (seuil pré-enregistré 12 : une suite est trouvée,
  consignée sans interprétation comme prévu) ; `c` moyen 0,69 ; absorption de A par B avec un seul scalaire :
  résidu relatif 0,88 (aucun paiement mutuel global). Distance aux réseaux lent/rapide prédits (membres dominants,
  phases du canal lissé) : 0,16 cellule pour les rencontres annulées contre 0,27 pour toutes. Explication
  géométrique post-hoc, non prédite au pré-enregistrement : la période du réseau lent en abscisse logarithmique est
  `2π/(23 − 17,5) ≈ 1,14`, soit, autour de `p ≈ 17 000`, une largeur en `x` de plusieurs centaines où `A ≈ −B` ;
  les premiers y tombent par dizaines. L'attente « points isolés » était vraie en abscisse logarithmique, fausse en
  nombre de rencontres : le seuil de 12 était mal calibré, et le critère est consigné comme tel.

## Verdict
* **Identités** : réussi (0 violation ; identités à 10⁻⁹ dans le domaine conditionné, à 10⁻²¹ à 30 chiffres aux pires
  points) ; aucune contradiction entre un énoncé compilé et la mesure.
* **Obligation Deux (version locale, troncature)** : critère satisfait mais **non discriminant** : le coût d'absorber
  une paire hors ligne est celui d'absorber n'importe quelle Tour basse fréquence, légitime ou non ; la croissance
  du rapport est l'exposant déjà compilé. Négatif comme levier.
* **Obligation Trois** : suite de 21 annulations trouvée ; pas de paiement mutuel global (résidu 0,88) ; les
  annulations suivent les réseaux lent/rapide compilés. Le seuil de 12 était mal calibré ; aucune loi nouvelle.
* **Obligation Une** : non décidable ici, comme annoncé.
