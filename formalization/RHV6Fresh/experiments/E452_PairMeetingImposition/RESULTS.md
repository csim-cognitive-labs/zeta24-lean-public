# E452 — Résultats (K2b, §19.74, 2026-11-08)

Pré-enregistrée au commit 9bc55404 avant compilation et exécution. **Verdict A.**

## Module `Terminal/PairMeetingImposition.lean` (isolé, import `PairBreakOfZero` seul)
* 23 déclarations (1 définition `mirrorWordShift`, 22 théorèmes), **tentative 1 verte** (`attempts/build_attempt1.txt`,
  9094 jobs, aucun avertissement dans le module), axiomes standards `[propext, Classical.choice, Quot.sound]` sur les neuf
  énoncés imprimés (`attempts/axioms_attempt1.txt`). Grep du ban (`smoothedRemainder|remainderExponent|OffCarrier|complement|
  familyRe|CollectiveCurvature`) : 0. `lake build RHV6Fresh` complet vert après (`logs/lake_build_full.txt`, 9064 jobs).
* Trois sondes avant le module (`attempts/probe1–3.txt`) : (1) deux erreurs de syntaxe sur la valeur absolue imbriquée
  `| |a| + b |` (écrite `abs (…)`) et un argument implicite `T` à nommer dans `pair_value_sum_ge` ; (2) dans le cas `s = 1`,
  `(−1)^1 = −1` : la branche était écrite comme le cas `s = 0` ; (3) verte. Une variable inutilisée retirée
  (`pair_value_mirror_eq` ne dépend que de `β < 1`).
* Énoncés compilés, par rapport au pré-enregistrement : tous (L1–L7), plus le lemme auxiliaire `abs_sign_sum` et
  `neg_one_zpow_neg_one'`.

## Ce que dit le compilé
1. **Mot exact du miroir** : `k_{1−β}(x) = k_β(x) + ⌊f_β(x) + δ/π⌋`, `δ = mirrorPhaseShift β T` ; le décalage vaut −1, 0 ou 1.
2. **Fenêtre de même mot fixée par `β`** : même mot ⟺ `−δ/π ≤ f_β(x) < 1 − δ/π` ; sur la ligne, décalage nul partout.
3. **Signes** : `v·v* = (−1)^s |v||v*|` ; même signe ⟺ même mot.
4. **Valeur de la paire au premier partagé** : `|v + v*| = | |v| + (−1)^s |v*| |` : somme des deux amplitudes si même mot,
   différence sinon ; dans tous les cas `|v| − |v*| ≤ |v + v*|`.
5. **Non-compensation** : pour `β > 1/2` (le miroir couvre `β < 1/2`), au-delà d'un rang `|v + v*| > |v|/2` en tout point,
   donc à toute rencontre `p_{n+1}` au-delà d'un rang (`pair_meeting_no_cancellation`). La séparation non bornée (E450 L6)
   interdit à la paire de se compenser elle-même au premier partagé.
6. **Ligne** : `v + v* = 2v`.
7. **Zéro vrai** : non-compensation au paramètre d'un zéro vrai hors ligne ; `|m v + m* v*| = m |v + v*| ≥ |v + v*|`.

## Expérience (a) — `scripts/e452a_pair_imposition.py` (numpy, 10⁵ premiers ≤ 10⁷, graine 452)
24 couples (six fréquences de K0 × `β ∈ {0,3 ; 0,4 ; 0,45 ; 0,5}`), `logs/e452a_log.txt`, `data/e452a_results.json`.
* H1 mot exact : 0 violation / 2 400 000 ; H2 : 0 ; H3 même signe ⟺ même mot : 0 ; H4 identité de la valeur de paire : écart
  maximal 0 (identique au bit) ; H5 : 0 violation ; H7 ligne `v* = v` : écart 0.
* H6 non-compensation `|v + v*| > |v_dominant|/2` : vraie sur TOUT l'échantillon pour les 24 couples (dès le premier premier
  échantillonné, 47) ; l'énoncé compilé ne garantit qu'« au-delà d'un rang ».
* Observation sans loi : la part des premiers à mots décalés suit `|δ|/π` (β = 0,3 : 1,00 % contre 0,90 % à T ≈ 14,13 ;
  0,27 % contre 0,26 % à T ≈ 49,8 ; 0,05 % contre 0,05 % à T ≈ 236,5 ; au-delà de T ≈ 10⁴, au plus un premier sur 10⁵).
  Le décalage observé est toujours +1 (jamais −1) : `δ > 0` pour `β < 1/2`. Aucune équidistribution n'est compilée ni posée.

## Expérience (b) — `scripts/e452b_twin_mpmath.py` (jumeau, 30 chiffres)
240 cas (10 premiers par couple) : 0 violation ; H1, H3 exacts ; H4 à 0 ; écart aux valeurs numpy ≤ 3·10⁻¹⁵.

## Ce que cela établit, et ce que cela n'établit pas
La rencontre exacte impose aux deux termes de même poids au même premier : un mot commun sauf sur une fenêtre de fraction
de cellule de largeur `|δ|/π` fixée par `β` (vide sur la ligne), un signe commun exactement quand le mot est commun, une
valeur de paire qui est la somme des deux amplitudes (mot commun) ou leur différence (mot décalé), jamais nulle au-delà d'un
rang, dominée par un seul membre hors ligne. Aucune hypothèse n'a été posée ; aucune contradiction n'est tirée (§19.74.2).
Suite : K3, inversion de la paire (les écarts portent un mot par fréquence, E449 ; la paire exige deux mots décalés sur la
fenêtre) ; toute prémisse que K3 exigerait sera vérifiée pour non-équivalence avec RH avant d'être posée.
