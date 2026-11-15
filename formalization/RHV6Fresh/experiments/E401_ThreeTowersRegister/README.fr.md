> Version française conservée à titre de référence. Main language: English, see README.md.

# E401 — Registre déterministe des trois Tours connues sur les 168 écarts premiers depuis 2 (p_n ≤ 1000)

Étape G du plan pré-enregistré (maître §19.24.8, feu vert de l'auteur le 2026-11-01). Aucun Lean modifié.

## Pré-enregistrement (écrit AVANT exécution)

Objets : les trois premiers zéros certifiés (T₁, T₂, T₃, partie réelle 1/2 : théorèmes), leurs Tours, les 168 écarts
`[p_n, p_{n+1}]` avec `p_n ≤ 1000` (de `[2, 3]` à `[997, 1009]`).

Pour chaque écart, le registre donne :
1. les contacts `C_k = exp((arctan(T/β) + kπ)/T)` de chaque Tour traversés par l'écart (indices `k`), c'est-à-dire les
   cellules `J_{k,n}` que l'écart découpe ;
2. la contribution brute `−2 Re (p_{n+1}^ρ − p_n^ρ)/ρ` de chaque Tour (= `Δ_{ρ,n}` du texte, F3 compilé) et leur somme ;
3. la contribution de comptage `−2 Re (Ei(ρ log p_{n+1}) − Ei(ρ log p_n))` et leur somme ;
4. la contribution lissée `−2 Re (p_{n+1}^ρ − p_n^ρ)/(ρ(ρ+1))` (F4 compilé) et leur somme ;
5. EN REGARD, la demande exacte de l'écart dans le canal compilé : `R(p_{n+1}) − R(p_n)` avec
   `R(x) = Σ_{m<⌈x⌉} Λ(m)(1 − m/x) − [x/2 − ζ'/ζ(0) + (ζ'/ζ)(−1)/x + Σ_{j≥0} (−x^{s_j}/(s_j(s_j+1))), s_j = −2(j+1)]`,
   formule prise telle quelle dans `ZetaPerronLineIdentity` / `ZetaSmoothedZeroFormulaP5` (aucune autre).

Jumeau : deux implémentations à 30 et 50 chiffres (mpmath) ; les zéros sont recalculés (`zetazero`) et comparés aux
valeurs certifiées à 30 chiffres. Aucun zéro synthétique, aucune fenêtre, aucune moyenne, aucune corrélation.

Résultats attendus, dits d'avance :
- télescopage exact : pour chaque canal, la somme des 168 contributions d'une Tour égale sa contribution sur `[2, 1009]`
  (identité `primeGapContribution_chain`, `gapTerm_add`) ;
- la somme des trois Tours lissées n'égale la demande exacte sur AUCUN écart (c'est F8 compilé,
  `no_finite_family_at_any_meeting`) ; l'écart résiduel est la queue des zéros omis (`localResidual_eq_tail`) ;
- contrôle d'implémentation (pas un résultat) : le résidu `demande − Σ_{k≤K} lissée` décroît quand `K` passe de 3 à
  30 puis 100 zéros, puisque la série lissée converge absolument ; aucune valeur n'est lue comme mesure de `β` ;
- aucune conclusion sur `β` ; aucun contact n'est un premier ; aucune comparaison à une moyenne.

Les huit points de la liste « erreurs de débutant » (CLAUDE.md, 2026-10-28) sont vérifiés : (1) rien n'est réfuté ;
(2) aucun « critère échoué » ; (3) lecture aux fins d'écarts (rencontre = `p_{n+1}`) ; (4) rien demandé à l'auteur ;
(5) aucun mot prêté ; (6) action = fichiers + commit ; (7) la demande est confrontée à la somme, pas à un membre ;
(8) aucune lecture de hauteur depuis les écarts.

## Résultats (exécution du 2026-11-01, après pré-enregistrement ; 11 s à 30 chiffres, 13 s à 50 chiffres)

Fichiers : `e401_register_dps30.txt`, `e401_register_dps50.txt` (168 lignes : contacts traversés par Tour, contributions
brute / comptage / lissée par Tour et sommes, demande exacte, résidus après 3, 30, 100 zéros), `e401_output_dps30.txt`,
`e401_output_dps50.txt` (bilans).

- Zéros 1..3 recalculés = valeurs certifiées à 1e−28, aux deux précisions.
- Jumeau : contacts traversés identiques sur les 168 écarts ; toutes les colonnes numériques identiques sur les 12 chiffres
  affichés (écart maximal 0).
- Télescopage : pour chaque Tour et chaque canal, somme des 168 contributions − contribution sur `[2, 1009]` ≤ 2e−30
  (identité, comme prévu).
- Demande exacte totale sur `[2, 1009]` : −0,332282131799033 (même valeur aux deux précisions).
- Nombre d'écarts où la somme lissée des trois Tours égale la demande à 1e−20 : **0 sur 168** (comme prévu : F8).
- Contrôle d'implémentation (pas un résultat) : résidu maximal `|demande − Σ_{k≤K} lissée|` sur les 168 écarts :
  0,149 (K = 3), 0,032 (K = 30), 0,013 (K = 100) : décroissant avec K, conforme à la convergence absolue de la série
  lissée ; c'est la queue des zéros omis (`localResidual_eq_tail`), rien d'autre.
- Les onze premières lignes reproduisent E400 (texte collé) à l'identique sur le canal brut.

Aucune conclusion sur β. Aucun contact n'est un premier. Aucune moyenne, fenêtre ni corrélation n'a été calculée.
