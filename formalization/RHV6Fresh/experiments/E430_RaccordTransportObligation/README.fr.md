> Version française conservée à titre de référence. Main language: English, see README.md.

# E430 — Le transport au premier partagé écrit avec les contacts, et l'obligation du raccord guidée par le compilateur (2026-11-04)

Expérience de compilation seule (aucune mesure numérique ; aucun jumeau requis car aucune conclusion numérique).
Demande de l'auteur : « procède avec ton plan ; il faut faire des tentatives pour que le compilateur Lean te guide et
qu'il demande précisément ce qu'il manque ; puis tu détailles les hypothèses pour produire le chaînon manquant ; on
travaille en TDD ».

Cible (critique du 2026-11-04) : « prouver que l'obligation arithmétique du raccord au premier partagé s'applique au
transport défini dans `TransportAtSharedPrime.lean` ».

## Protocole (fixé avant la première compilation)
1. Écrire le module isolé `Terminal/RaccordTransportObligation.lean` (non ajouté à `RHV6Fresh.lean`) :
   (a) identités : transport entre deux membres à une abscisse, écrit avec les deux derniers contacts et les deux
   fractions de cellule ; paire au premier partagé ; (b) définition `RaccordTransportObligation` (le détour transporte
   la valeur de la chaîne ON) et ce qu'elle équivaut ; (c) identité de la cassure pour tout paquet ; hypothèse nommée
   `PairDepositOnLine` (jamais posée) et ce qu'elle force.
2. Deux tentatives de compilation au plus, journalisées (`logs/lean_attempt{1,2}.txt`).
3. Sondes TDD dans un fichier de sondage NON versionné, chaque sonde terminée par `done` pour que le compilateur
   imprime le but restant (`logs/probe_attempt1.txt` conserve la sortie exacte) ; le fichier de sondage est supprimé
   après la capture.
4. Aucune hypothèse posée ; aucun `sorry` dans le module ; `lake build RHV6Fresh` vert après (`logs/lake_build_full_trimmed.txt`).

## Objets réutilisés (jamais reconstruits)
`energyRatio`, `energyRatio_eq`, `zeroTerm_norm`, `zeroPoint_eq_mk`, `zeroPoint_re_pos`, `mirrorMember_ordinate`
(SuccessionInvariants, ExplicitFormulaLink, SuccessiveContactConstraints, MirrorCount) ; `abs_contactRealValue`,
`growth_factor_eq`, `lastContactBefore`, `cellFraction` (ContactRealValue, MeetingContactReading) ;
`detour_transport_product_onLine`, `onLine_chain_transport`, `detour_arithmetic_factor_ne_one`, `detourPrimeContent`,
`detourPrimeContent_eq_exp_logGaps` (TransportAtSharedPrime) ; `remainderIncrement_eq_packet_add_complement`,
`break_compensated_by_other_frequencies`, `break_at_meeting`, `pair_real_density_eq_cosh_line`,
`realCountingDensity_eq_zero_iff`, `densitySignChangeLog` (HeightPacket, OffCarrier, LocalPrimeGapSynchronization).

## Résultat attendu de chaque sonde (écrit avant exécution)
* Sonde 1 (obligation depuis la cassure) : le but restant portera sur `δ` et le contenu premier seuls ; les hypothèses
  de cassure ne seront pas utilisables.
* Sonde 2 (`PairDepositOnLine` depuis la cassure) : le but restant sera l'annulation de la densité de ligne à la
  cassure.
* Sonde 3 (paquet de la paire au pas de la cassure) : identité explicite en Tours brutes, sans le complément.
* Sonde 4 (dépôt du complément) : identité, fermée par `rfl`.
