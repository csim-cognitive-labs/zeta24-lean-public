> Version française conservée à titre de référence. Main language: English, see README.md.

# E431 — Rigidité arithmétique de la phase aux cassures : la paire ne peut déposer comme la ligne qu'en un seul premier (2026-11-04)

Expérience de compilation seule (aucune mesure numérique ; aucun jumeau requis car aucune conclusion numérique).
Demande de l'auteur : « continue, améliore la démarche et resserre l'étau ». Suite directe de E430 (§19.45) : la plus
faible hypothèse compilée qui survivait, `PairDepositOnLine` (la paire dépose à la cassure comme la paire en ligne),
équivaut à « le premier partagé tombe sur un changement de signe de la densité de ligne ». E430 l'avait étudiée en UN
premier ; la directive impose de travailler sur une SÉRIE d'écarts.

## Question posée (avant toute compilation)
Si l'on demande l'hypothèse « dépôt en ligne » non plus au seul premier partagé mais à chaque cassure d'une série de
premiers, que reste-t-il ? Attendu (écrit avant exécution) : la factorisation unique interdit que deux premiers
distincts tombent tous deux sur un changement de signe de la densité d'une même fréquence ; l'hypothèse ne peut donc
être vraie qu'en un seul premier de toute la série. Ce qui resterait pour le chaînon manquant est alors l'absorption,
par le complément, d'un surplus non nul de la paire en tous les premiers sauf au plus un.

## Protocole
1. Pré-enregistrer ce fichier (commit) avant la première compilation.
2. Sondes TDD dans un fichier de sondage NON versionné (`RaccordPhaseProbe_SCRATCH.lean`, supprimé après capture), chaque
   sonde terminée par `done` pour que le compilateur imprime le but restant ; sorties exactes dans `logs/probe_attempt*.txt`.
3. Écrire le module isolé `Terminal/RaccordPhaseRigidity.lean` (non ajouté à `RHV6Fresh.lean`) :
   (a) la fraction de cellule d'une Tour en un changement de signe de la densité lit la position radiale :
       `arctan(β/T)/π` (identité) ; sous `PairDepositOnLine`, fractions de la Tour et du miroir à la cassure ;
   (b) l'hypothèse « dépôt en ligne » en tout premier de rang `m` (`PairDepositOnLineAt m`) et son équivalence avec
       le changement de signe (même preuve qu'en E430) ;
   (c) rigidité arithmétique : deux premiers distincts ne tombent jamais tous deux sur un changement de signe de la
       densité d'une même fréquence (factorisation unique) ; conséquence pour tout porteur : `PairDepositOnLineAt` est
       vraie en au plus un rang ;
   (d) tentative (une seule) : une Tour `(β, T)` ne touche au plus que deux premiers (trois contacts en des premiers
       distincts sont contradictoires) ; si le compilateur demande plus que la factorisation, consigner le but et
       ne pas insister ;
   (e) le surplus de la paire à une cassure (`pairSurplus m`), son expression `2(cosh(δ log p_m) − 1)·D_ligne(log p_m)`,
       et : sur deux rangs distincts, l'un au moins des surplus est non nul.
4. Deux tentatives de compilation au plus pour le module, journalisées (`logs/lean_attempt{1,2}.txt`).
5. Aucune hypothèse posée ; aucun `sorry` ; `lake build RHV6Fresh` vert après (`logs/lake_build_full_trimmed.txt`).

## Sondes prévues et but attendu
- S1 : de « surplus nul en tout rang » dériver `False` sans (c) — attendu : le compilateur demande deux rangs
  distincts et la factorisation ; rien d'autre.
- S2 : de « le complément absorbe le surplus en tout rang » dériver `False` — attendu : but ouvert sur le complément,
  aucune contrainte compilée ne le ferme (identité de cassure pour tout paquet, E430 sonde 4).

## Objets réutilisés (jamais reconstruits)
`stagePosition`, `cellFraction`, `lastContactBefore`, `mirror_stage_shift_ne_zero` (FirstExceedanceRaccord,
MeetingContactReading) ; `realCountingDensity`, `densitySignChangeLog`, `realCountingDensity_eq_zero_iff`
(LocalPrimeGapSynchronization) ; `PairDepositOnLine`, `breakLog`, `pairDepositOnLine_iff_sign_change`
(RaccordTransportObligation) ; `pair_real_density_eq_cosh_line`, `radialShift_pos`, `linePoint_im`, `zero_radial_eq`,
`mirror_radial_eq` (OffCarrier) ; `fnPrimeAtRank`, `thm_primeAtRank_isPrime`, `thm_primeAtRank_injective` (RHV3Lean) ;
`Real.arctan_inv_of_pos`, `Int.fract_eq_iff`, `Nat.Prime.dvd_of_dvd_pow`, `Nat.prime_dvd_prime_iff_eq` (Mathlib).

## Ce que l'expérience ne prétend pas
Aucune contradiction n'est attendue : l'absence de contrainte compilée sur le complément reste la frontière (§19.13,
§19.44, §19.45). L'étau se resserre d'un cran : l'hypothèse la plus faible ne peut être vraie qu'une fois sur la série.
