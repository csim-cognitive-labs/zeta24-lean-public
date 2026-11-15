# E431 — Résultats (2026-11-04)

Pré-enregistré au commit 4a1db82a avant toute compilation. Compilation seule ; aucune conclusion numérique.

## Sondes (fichier de sondage non versionné, supprimé après capture)
- `logs/probe_attempt1.txt` : 65 erreurs, une seule cause — les objets `stagePosition`, `cellFraction`,
  `densitySignChangeLog` vivent dans l'espace de noms `RHV6Fresh` (non ouvert) et le lemme de positivité du
  logarithme d'un premier s'appelle `Nat.Prime.log_pos`. Aucune erreur mathématique.
- `logs/probe_attempt2.txt` : tous les lemmes candidats passent ; seuls les deux `done` des sondes restent, avec les
  buts exacts suivants.
  - S1 (« surplus nul en tout rang » ⟹ `False`, sans la rigidité arithmétique) : le compilateur ne laisse que
    `log p_2 = (π/2 + kπ)/T`, `log p_3 = (π/2 + jπ)/T` ⊢ `False`. Il demande exactement « deux premiers distincts sur
    deux changements de signe de la même fréquence » — c'est `signChange_two_primes_false` (factorisation unique).
  - S2 (surplus non nul au rang `m` ⟹ accroissement du complément non nul) : après l'identité de cassure, il reste
    `remainderIncrement m = packetIncrement C.packet m` et `C.pairSurplus m ≠ 0` ⊢ `False`. Le compilateur demande un
    pont entre le surplus de densité réelle (dérivée de la contribution de comptage, en `1/log x`) et le pas du canal
    lissé des paquets (facteur `−m/(ρ+1)`, `residueTerm_eq_smoothingFactor_mul`). Aucun objet du corpus ne relie ces
    deux grandeurs ; la cassure, identité pour tout paquet, n'y contribue pas.

## Module `Terminal/RaccordPhaseRigidity.lean` (isolé, 18 déclarations, aucun `sorry`)
- Tentative 1/2 (`logs/lean_attempt1.txt`) : 0 erreur (la seule occurrence de « error » est un avertissement de
  linter préexistant dans `Zeta23Port/Analytic/Stirling.lean`). Avertissements de longueur de ligne seulement.
  Aucune seconde tentative nécessaire.
- `#print axioms` sur 7 énoncés : `[propext, Classical.choice, Quot.sound]`.
- `lake build RHV6Fresh` : « Build completed successfully (9064 jobs) », EXIT=0 (`logs/lake_build_full_trimmed.txt`).

## Compilé
1. `cellFraction_at_signChange` : la fraction de cellule d'une Tour `(β, T)` en tout changement de signe de la
   densité de fréquence `T` vaut `arctan(β/T)/π`, indépendante de l'indice ; elle lit `β`.
2. `pairDepositOnLine_cellFraction` : sous `PairDepositOnLine`, fractions de cellule de la Tour et du miroir au
   premier partagé : `arctan(β/T)/π` et `arctan((1−β)/T)/π`.
3. `signChange_two_primes_false` : deux premiers distincts ne tombent jamais tous deux sur un changement de signe
   d'une même fréquence (`p^(2j+1) = q^(2k+1)` contredit la factorisation).
4. `same_cellFraction_three_primes_false` : trois premiers ordonnés ne partagent jamais la même fraction de cellule
   d'une Tour — une Tour ne touche au plus que deux premiers (`q^n p^m = r^m p^n`).
5. `PairDepositOnLineAt m`, `pairSurplus m`, `pairSurplus_eq` (`2(cosh(δ log p_m) − 1)·D_ligne`),
   `pairDepositOnLineAt_iff_sign_change`, `pairDepositOnLineAt_unique` (pour tout porteur, le dépôt en ligne est vrai en
   au plus un rang de toute la série), `pairSurplus_ne_zero_of_ne`.

## Lecture
Attendu du pré-enregistrement confirmé : la plus faible hypothèse survivante de E430 ne peut être vraie qu'une fois
sur la série des premiers. Pour tout porteur, en tout premier sauf au plus un, la paire dépose un surplus non nul
par rapport à la paire en ligne, et ce surplus est absorbé par le complément (identité). Le chaînon manquant se
réduit à la question posée par S2 : relier le surplus (densité réelle) au pas du canal lissé des paquets, puis
montrer que le complément ne peut pas l'absorber sur la série — argument à famille infinie et fréquences distinctes,
non compilé (§19.13, §19.44, §19.45). Aucune contradiction obtenue ; frontière inchangée, étau resserré d'un cran.
