# E477 — Résultats : poids alternés de la cassure, Tour moins miroir, sur les premiers à mot décalé (2026-11-14) ; pré-enregistrement `67feec44`

Jumeau `twin_e477.py` (`logs_twin_run.txt`, `twin_results.json`, 15 s) : premiers ≤ 3·10^7, paire fictive aux hauteurs `T_1`, `T_10`, `T_100`,
`β ∈ {0,45 ; 0,40 ; 0,30}`, témoin `β = 1/2` ; cellules complètes en nombre pair ; aucun module (mesure avant hypothèse). Post-hoc
`post_e477_corrected_p1.py` (`logs_post_corrected_p1.txt`) : loi P1 corrigée et échelle de fluctuation, calculées APRÈS lecture du jumeau.

| Tour | β | δ/π | cellules | premiers décalés | P1 fraction (prédite δ/π) | P2 résidu médian / |D| médian | P3 résidu | P4 R (second ordre) | non décalés R (premier ordre) | P5 borne / pente | S_pair/x^{3/2} |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 0,45 | 2,25e-3 | 44 | 3 062 | 2,50e-3 (+11 %) | 0,000 / 1,14 | 5e-12 | 1,31 | 0,999 | 2,83 / 1,60 | −1,8e-4 |
| 1 | 0,40 | 4,50e-3 | 44 | 6 177 | 5,05e-3 (+12 %) | 0,001 / 1,13 | 2e-12 | 1,21 | 0,999 | 11,5 / 1,72 | −1,0e-3 |
| 1 | 0,30 | 9,00e-3 | 44 | 12 272 | 1,00e-2 (+11 %) | 0,001 / 1,13 | 6e-13 | 1,16 | 0,998 | 3,17 / 1,88 | −2,9e-3 |
| 10 | 0,45 | 6,39e-4 | 162 | 1 139 | 6,23e-4 (−3 %) | 0,000 / 1,02 | 1e-10 | 0,60 | 1,000 | 87,6 / 1,53 | 5,0e-6 |
| 10 | 0,40 | 1,28e-3 | 162 | 2 366 | 1,29e-3 (+1 %) | 0,000 / 1,07 | 4e-11 | 1,32 | 1,000 | 66,5 / 1,51 | 8,3e-6 |
| 10 | 0,30 | 2,56e-3 | 162 | 4 722 | 2,58e-3 (+1 %) | 0,000 / 1,04 | 2e-11 | 1,17 | 1,000 | 123 / 1,45 | 6,1e-6 |
| 100 | 0,45 | 1,35e-4 | 774 | 238 | 1,29e-4 (−4 %) | 0,000 / 0,98 | 3e-9 | −0,14 | 1,000 | 1179 / 1,49 | 1,3e-8 |
| 100 | 0,40 | 2,69e-4 | 774 | 473 | 2,57e-4 (−5 %) | 0,000 / 0,99 | 7e-10 | 1,39 | 1,000 | 13199 / 1,49 | 2,7e-7 |
| 100 | 0,30 | 5,38e-4 | 774 | 973 | 5,29e-4 (−2 %) | 0,000 / 1,03 | 3e-10 | −2,81 | 1,000 | 3325 / 1,43 | 2,3e-7 |

Témoin `β = 1/2` : zéro premier décalé, `D = 0` exactement, sur les trois hauteurs.

## Verdict : **B** — P2, P4, témoin passés ; P1, P3, P5 échoués par la lettre ; P6 : second ordre (Tour 1), aucun théorème à écrire
- **P1** échoue sur la Tour 1 (+11 à +12 %) : MÊME défaut que H3b d'E476 — prédiction `|δ|/π` écrite en fraction logarithmique de cellule,
  alors que les premiers sont équirépartis en `x` et que la bande décalée est en haut de la cellule. Loi corrigée (post-hoc, calculée) :
  fraction `= (1 − e^{−δ/T})/(1 − e^{−π/T})` ; Tour 1 : écart 0,2 %, 0,6 %, 0,1 % ; Tours 10 et 100 : 2–6 % (bruit d'échantillonnage,
  quelques centaines à quelques milliers de premiers). La correction tend vers 1 quand `T` croît (1,115 ; 1,032 ; 1,007).
- **P2** passe : la loi du premier ordre `D = (−1)^j(2x/T)[e^{π/T}δ − (1+e^{π/T})πu]` est exacte à 1e-3 (médiane) ; `|D|` médian ≈ `x·δ/T`.
  Sur un premier à mot décalé, la différence des deux poids alternés est du PREMIER ordre en `δ`, de signe variable dans la bande
  (positif près du contact du miroir, négatif près du contact de la Tour).
- **P3** échoue par la lettre sur les Tours 10 et 100 (1e-10 à 3e-9 contre seuil 1e-10) : plancher flottant de `1 − e^{−δ/T}` pour
  `δ/T ≈ 1e-6` ; l'identité est algébrique (`saw_β − saw_{1−β} = 2C_{k+1}(e^{−δ/T} − 1)` sur un même mot) et vérifiée à 1e-12 sur la Tour 1.
- **P4** passe : la somme restreinte désalternée vaut la prédiction du SECOND ordre `Σ_k (δ²(e^{π/T}−1)/(πT))·ℓ_k·C_{k+1}` à un facteur
  1,16–1,31 (Tour 1 ; le facteur contient la correction de mesure 1,115) et 0,60–1,32 (Tour 10, bruité). Sur les premiers NON décalés, la
  somme désalternée vaut la prédiction du premier ordre `(2δ/T)(1 − δ/π)·ℓ_k·C_{k+1}` à 0,1 % près (identité P3 sommée).
- **P5** échoue, et la prédiction était fausse en nature, pas seulement en seuil : la somme cumulée sur un nombre pair de cellules n'est
  pas bornée par la moyenne du second ordre des deux dernières cellules ; elle est dominée par la FLUCTUATION des termes individuels, du
  premier ordre en `δ` et de signe variable (écart-type estimé `√((δ/π)(log X)/3)·(δ/T)·X^{3/2}`, du même ordre que la mesure sur les
  Tours 10 et 100 ; sur la Tour 1 la mesure dépasse l'écart-type et reste de l'ordre de la moyenne d'une cellule). Pentes log-log 1,43–1,88,
  rapport à `x^{3/2}` de 1e-8 à 3e-3 : rien ne croît de façon monotone, rien ne dépasse le fond.
- **P6** : sur la Tour 1 (statistique suffisante), `R` constant à 13 % entre les trois `β` (1,31 ; 1,21 ; 1,16) : second ordre confirmé ;
  `R·δ` varie d'un facteur 3,5 : premier ordre rejeté. Tour 10 : dispersion 70 % (bruit), `R·δ` varie d'un facteur 7,8 : premier ordre
  rejeté aussi. Règle pré-écrite : second ordre ⟹ **aucun théorème à écrire sur cette restriction**.

## Constats
1. Sur les premiers à mot décalé, les deux poids alternés de la cassure (Tour et miroir) sont égaux au premier ordre : la différence de
   parité compense la différence de signe des dents de scie (compilé en forme : `pair_same_sign_iff` + `alternating_break_weight`, lu ici
   par la mesure). L'effet moyen est du second ordre en `δ`, alterné en `k`, à l'échelle de fond `x²` avec constante `δ²(e^{π/T}−1)²/(πT)`.
2. Sur les premiers non décalés, la différence est du premier ordre, uniforme par cellule, alternée : `−(−1)^j·2C_{k+1}(1 − e^{−δ/T})`
   (identité). C'est là, et non sur la fraction décalée, que la paire écrit la plus grande différence de poids ; mais elle est alternée et
   d'échelle de fond elle aussi.
3. La « localisation » d'E476 (premiers à mot décalé) ne porte donc aucune obligation nouvelle : ni croissance au-dessus de `x^{3/2}`, ni
   premier ordre moyen. Aucun théorème à écrire ; rien d'admis ; RH non démontrée. Rectification de méthode consignée (R-Ψ octies) : toute
   prédiction de fraction de premiers dans une bande de cellule se calcule en mesure `x`, et toute somme restreinte à une sous-famille de
   premiers est dominée par ses fluctuations avant d'être lue comme budget.

## Stratégie (R-Ψ) — suite
Le fil « tente et cassure » (E474 → E476 → E477) est mesuré jusqu'au bout : l'obligation du poids est une forme compilée dont les deux
restrictions naturelles (premiers décalés, non décalés) sont alternées et d'échelle de fond. Aucune piste de fermeture n'en sort. Retour à
la question active de l'auteur (§19.108, Q475) : la contrainte doit venir des données arithmétiques du raccord à la rencontre (forme O7,
fréquence avant hauteur), pas d'une restriction du budget des aires. Décision de l'auteur attendue ; aucun pré-enregistrement sans elle.
