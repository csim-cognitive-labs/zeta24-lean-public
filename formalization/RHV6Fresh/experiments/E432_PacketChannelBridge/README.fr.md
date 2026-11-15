> Version française conservée à titre de référence. Main language: English, see README.md.

# E432 — Le pont densité → canal des paquets : le surplus de la paire dans le canal des Tours (2026-11-04)

Expérience de compilation seule (aucune mesure numérique ; aucun jumeau requis). Demande de l'auteur : « ok continue »,
après E431 dont la sonde S2 a laissé le but « reste exact = paquet de la paire » face à « surplus non nul », sans pont
compilé entre la densité réelle et le pas du canal lissé des paquets.

## Question posée (avant toute compilation)
Le pas du canal des paquets de la paire sur le pas de la cassure, écrit comme intégrale de sa dérivée (termes de Tour),
porte-t-il le surplus de la paire avec le même facteur hyperbolique que la densité, ou ce surplus est-il déformé ?
Attendu (écrit avant exécution) : dans le canal des Tours, les deux membres sont pondérés par `1/ρ` (amplitude et phase
propres), de sorte que le surplus de la paire par rapport au jumeau en ligne vaut le facteur hyperbolique sur la ligne
PLUS un terme de déformation proportionnel au décalage radial, de la forme `(δ/ρ_L)·(Tour du zéro − Tour du miroir)`.
Conséquence attendue : un changement de signe de la densité n'annule pas le surplus dans le canal des paquets.

## Protocole
1. Pré-enregistrer (commit) avant la première compilation.
2. Sondes TDD dans `RaccordBridgeProbe_SCRATCH.lean` (non versionné, supprimé après capture ; sorties exactes dans
   `logs/probe_attempt*.txt`).
3. Module isolé `Terminal/PacketChannelBridge.lean` (non ajouté à `RHV6Fresh.lean`) :
   (a) `lineTerm` (terme de Tour du point de ligne) et l'identité ponctuelle du surplus de la paire dans le canal des
       Tours (facteur hyperbolique + déformation) ;
   (b) dérivée de la primitive du paquet à quatre membres (cas (a)) : `−m·(Tours des quatre membres)` ;
   (c) le pas local du paquet sur `[N, N+1]` (`N ≥ 2`) comme intégrale de cette dérivée (théorème fondamental) ;
   (d) si (a)–(c) passent : le surplus du pas du paquet par rapport au jumeau en ligne de mêmes multiplicités, comme
       intégrale du facteur hyperbolique plus la déformation.
   Si le compilateur demande davantage que les objets listés, consigner le but exact et ne pas insister.
4. Deux tentatives de compilation au plus pour le module (`logs/lean_attempt{1,2}.txt`) ; aucune hypothèse posée ;
   aucun `sorry` ; `lake build RHV6Fresh` vert après.

## Sonde prévue
- S1 : « le surplus du canal des Tours s'annule en un changement de signe de la densité » — attendu : faux ; le
  compilateur laisse un terme en sinus de la phase de ligne `arctan(2T)` et la déformation.

## Objets réutilisés
`zeroTerm`, `zeroTerm_hasDerivAt`, `explicit_term_derivative`, `residueTerm_conjIndex`, `packet_channel_four_of_mirror`,
`zeroPoint_eq_line_sub_shift`, `mirrorPoint_eq_line_add_shift`, `linePoint_im`, `channelPrimitive`, `stepAt`,
`localPacket`, `pair_gapTerm_signature` (pour comparaison), Mathlib `cpow_add/sub/def_of_ne_zero`, `ofReal_log`,
`integral_eq_sub_of_hasDerivAt`, `conjCLE`.
