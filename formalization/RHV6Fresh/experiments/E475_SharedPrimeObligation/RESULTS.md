# E475 — Résultats des mesures M1–M3 (2026-11-14) ; pré-enregistrement `f7172ad5` ; `logs_twin_run.txt`, `twin_results.json` (0,1 s)

Hypothèse de calcul (jamais une prémisse Lean) : zéros d'Odlyzko sur la ligne, multiplicité 1. Raccords canoniques `n = 0 … 1999`.

## M1 — premier partagé : EXACT
Pour les 2000 raccords, `expectedMinimumPrime (canonicalMember n) = occurrence (canonicalMember (n+1)) = meetingPoint ⟨n⟩ = p_{n+1}`
(indexation `fnPrimeAtRank 0 = 2`). Exemples : zéro 1 → zéro 2 au premier 3 ; zéro 2 → zéro 3 au premier 5 ; … ; zéro 10 → zéro 11 au
premier 31. Conforme au théorème compilé `sharedPrime_eq_meeting`.

## M2 — parts imposées des deux membres à l'écart ⟨n⟩ contre le transport : ÉCHEC du test 1e-6, loi consignée
Identité de la forme close (`imposedShare_at_meeting`) : résidu relatif ≤ 5,8e-13. Rapport `r_n = |s_l|/|s_e|` sur transport
`E_n = ‖ρ_e‖/‖ρ_l‖` (ligne), dix premiers raccords : 2,10 ; 0,17 ; 0,86 ; 1,50 ; 0,096 ; 0,69 ; 0,83 ; 1,07 ; 0,72 ; 0,93.
Décomposition EXACTE (identité, toute β) : `r_n / E_n = (‖ρ_e+1‖/‖ρ_l+1‖) · (Φ_l/Φ_e)`, avec
`Φ_w² = p_{n+1} + p_n − 2√(p_n p_{n+1}) cos(T_w · log(p_{n+1}/p_n))` : le facteur de phase est l'écart lu par la fréquence du membre.
Dix premiers : facteur de norme 0,67 → 0,94 ; facteur de phase 3,11 ; 0,21 ; 1,05 ; 1,62 ; 0,11 ; 0,76 ; 0,88 ; 1,18 ; 0,75 ; 0,98.
Loi en `n` (tranches de 200) : médiane de `Φ_l/Φ_e` 1,0025 → 1,0003 ; quartiles [0,996 ; 1,006] → [1,000 ; 1,000] ; extrêmes [0,11 ; 6,26] sur
la première tranche, [0,97 ; 1,01] sur la dernière. `r/E` médiane globale 0,9999 ; 1,25 % des raccords au-dessus de 1.
LECTURE : la convergence vers 1 n'est pas une contrainte : deux zéros consécutifs ont des hauteurs relativement proches, donc lisent le même
écart presque à la même phase. Le rapport des parts est un produit de trois facteurs, chacun fonction de `(β, T)` du membre et des deux
bornes de l'écart seulement ; AUCUNE donnée du raccord autre que les deux bornes n'y entre.

## M3 — sensibilité radiale de la paire fictive : SENSIBLE
Variation relative de `|pairShare|/|s_e|` par rapport à `β = 1/2`, `β = 0,40` : 0,4 % (premier 3) → 5,8 % (premier 31) ; `β = 0,30` : 1,8 % → 24 % ;
contrôle `β = 1/2 ⟹ paire = 2 s_l` à 1e-16. La sensibilité suit `cosh((β − 1/2) log x)` : c'est le PRIX (O5, `pair_amplitude_eq_price`),
déjà compilé, pas une contrainte nouvelle.

## Verdict : B (M1 exact ; M2 échoue, loi consignée ; M3 sensible mais réductible à O5)

## Constats
1. Q475 posée sur les parts imposées des deux membres est VIDE : la relation mesurée est une identité (forme close compilée) ; les données
   arithmétiques du raccord n'y entrent que par les deux bornes de l'écart, lues par la fréquence de chaque membre.
2. La dépendance radiale de la part d'une paire est exactement le prix (O5) : rien que la reconstruction n'ait déjà compilé.
3. Le seul endroit où la paire OFF modifie l'ASSIGNATION arithmétique est l'énumération : deux membres à la même hauteur ont deux index
   consécutifs (`low_arrival_precedes_mirror`), donc deux occurrences consécutives `p_{n+1}`, `p_{n+2}` ; le raccord `l → miroir` au premier
   partagé `p_{n+2}` est le détour de `TransportAtSharedPrime` (§19.18–19.19 : détour ≠ chaîne ON, aucune loi de conservation compilée,
   recherche suspendue). Les deux membres lisent l'écart `⟨n+1⟩` à la même phase (même `T`) avec les amplitudes `p^β`, `p^{1−β}` : part de la
   paire sans compensation (O4), identité satisfaite par les autres (O1).
4. Aucune contradiction ; rien d'admis ; rien déclaré manquant qui ne manque pas.

## Stratégie (R-Ψ) — ce que la mesure dit de la suite
La contrainte cherchée ne peut pas se lire sur les parts d'un écart ; elle doit porter sur l'ÉNUMÉRATION (quel membre lit quel écart) :
c'est la fréquence avant la hauteur (ordre de l'auteur 2026-10-28) et la question P5 sous sa forme O7 (« la fréquence attendue monte à
chaque rencontre »). Sous R-RH, ce n'est pas une objection. Proposition à soumettre à l'auteur AVANT tout pré-enregistrement : formuler
l'obligation comme un énoncé sur deux écarts consécutifs `⟨n⟩`, `⟨n+1⟩` et trois membres `e → l → l'`, où `l'` est soit un zéro de
hauteur supérieure (ligne) soit le miroir de `l` (paire), et chercher dans `localSynchronization` appliquée aux deux écarts ce qui
distingue les deux cas SANS somme infinie prise pour objet (les deux écarts ont les mêmes autres zéros ; seule change la lecture par `l'`).
Interdits inchangés : contact ≠ premier ; aucune absorption par le complément ; aucune borne d'exposant ; R-E446.
