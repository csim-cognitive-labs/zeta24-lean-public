> Version française conservée à titre de référence. Main language: English, see README.md.

# E433 — Le bilan de la paire sur une série de pas consécutifs : ce que le complément doit absorber (2026-11-04)

Expérience de compilation seule (aucune mesure numérique ; aucun jumeau requis). Demande de l'auteur : « continues »,
après E432 dont le chaînon manquant est « le complément ne peut pas absorber, sur la série des pas, le surplus intégré
de la paire ». Directive : travailler sur une SÉRIE d'écarts, jamais un seul ; fréquence avant hauteur.

## Question posée (avant toute compilation)
Sur une fenêtre de `m` pas consécutifs à partir de `a ≥ 2`, que vaut exactement la somme des incréments du complément
de la paire, et par quels points la paire y entre-t-elle ?
Attendu (écrit avant exécution) :
1. la somme des incréments de tout paquet sur la fenêtre se télescope en deux pas locaux, celui de la fin moins celui
   du début (« effondrement aux bords » : les pas intérieurs de la paire s'annulent exactement sur la série) ;
2. la somme des incréments du reste exact sur la fenêtre vaut la somme des poids de von Mangoldt des points atteints
   moins la variation du pas du fond ;
3. donc la somme du complément sur la fenêtre = contenu arithmétique de la fenêtre − (pas local de la paire à la fin −
   pas local au début) ; la paire n'entre que par la primitive de ses quatre membres évaluée aux deux bords ;
4. pour la paire miroir (cas (a)), le pas local a une forme close : primitive `−m·x·Tour/(ρ+1)` des quatre membres ;
   la norme du membre miroir de cette primitive croît comme `x^{2−β}/(‖ρ'‖·‖ρ'+1‖)`.

## Protocole
1. Pré-enregistrer (commit) avant la première compilation.
2. Sondes TDD dans `SeriesBalanceProbe_SCRATCH.lean` (non versionné, supprimé après capture ; sorties exactes dans
   `logs/probe_attempt*.txt`).
3. Module isolé `Terminal/PacketSeriesBalance.lean` (non ajouté à `RHV6Fresh.lean`) : points 1–4.
   Si le compilateur demande davantage que les objets listés, consigner le but exact et ne pas insister.
4. Deux tentatives de compilation au plus pour le module (`logs/lean_attempt{1,2}.txt`) ; aucune hypothèse posée ;
   aucun `sorry` ; `lake build RHV6Fresh` vert après.

## Sondes prévues
- S1 : « le complément de la paire est nul sur tous les pas d'une fenêtre ⟹ False » — attendu : pas de contradiction ;
  le compilateur laisse « contenu arithmétique de la fenêtre = différence des pas locaux de la paire aux bords ».
- S2 : « le complément de la paire est borné en norme sur tous les pas à partir de `a` ⟹ False » — attendu : pas de
  contradiction ; but restant = croissance en `N^{1−β}` du pas local de la paire contre le contenu arithmétique, qui est
  l'exposant du reste (frontière connue, ⟺ RH).

## Objets réutilisés
`packetIncrement`, `remainderIncrement`, `localPacket`, `remainderIncrement_eq_packet_add_complement`,
`remainderIncrement_arithmetic`, `gap_demand_sum_increments`, `packet_channel_four_of_mirror`,
`residueTerm_eq_zeroTerm`, `residueTerm_conjIndex`, `norm_zeroTerm_eq`, `mirror_multiplicity_eq`,
`Finset.sum_range_succ`.
