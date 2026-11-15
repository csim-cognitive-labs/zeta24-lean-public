# E430 — Résultats (2026-11-04)

## Compilation du module `Terminal/RaccordTransportObligation.lean`
* Tentative 1 (`logs/lean_attempt1.txt`) : échec, une seule cause — l'espace de noms `RHV3Lean` non ouvert
  (`rZeroRadialPosition`, `rZeroHeight` inconnus) ; la première déclaration `amplitude_from_lastContact` compilait déjà.
* Tentative 2 (`logs/lean_attempt2.txt`) : `open Real RHV3Lean` ; **0 erreur, EXIT=0**, neuf `#print axioms`
  tous `[propext, Classical.choice, Quot.sound]`, aucun `sorry`. Limite de deux tentatives respectée.
* `lake build RHV6Fresh.Terminal.RaccordTransportObligation` : succès (`logs/lake_build_module_trimmed.txt`).
* `lake build RHV6Fresh` complet : voir `logs/lake_build_full_trimmed.txt` (dernière ligne `EXIT=`).

## Compilé (19 déclarations)
* `amplitude_from_lastContact` : `q^β/‖β+iT‖ = |v_k|·e^{βπf/T}` (dernier contact `k`, fraction `f`).
* `energyRatio_from_contacts` : le transport d'un membre à un autre à l'abscisse `q` est le rapport des valeurs
  absolues aux derniers contacts avant `q`, fois le rapport des croissances sur les fractions de cellule.
  **Le premier partagé n'entre dans le transport que par les deux derniers contacts avant lui et les deux fractions
  de cellule.**
* `pair_transport_from_contacts` : la paire au premier partagé, positions `½ ∓ δ`, même fréquence.
* `RaccordTransportObligation` (définition) ; `obligation_iff_factor_one` : ⟺ `(p_{n+1}²/(p_n p_{n+2}))^δ = 1` ;
  `not_raccordTransportObligation` : **fausse pour tout porteur** (reprise en ligne) ; `obligation_of_link` : la seule
  hypothèse qui la ferme est `δ·log(contenu) = 0` ; `link_false` : cette hypothèse est réfutée.
* `break_split_any_packet` : à la cassure, reste = paquet + complément pour tout paquet.
* `PairDepositOnLine` (hypothèse nommée, jamais posée) ; `pairDepositOnLine_iff_sign_change` : ⟺ la cassure tombe
  sur un changement de signe de la densité de ligne, `log p_{n+1} = (π/2 + kπ)/T` ;
  `not_obligation_of_pairDepositOnLine` : elle laisse l'obligation de transport fausse.

## Sondes TDD (`logs/probe_attempt1.txt`, sortie exacte du compilateur)
* **Sonde 1** — obligation de transport depuis les identités de cassure (`hbreak`, `hsplit` dans le contexte) :
  but restant `(rPrimeGapLogRatio C.n − rPrimeGapLogRatio (C.n + 1)) * C.radialShift = 0`.
  Les deux hypothèses de cassure sont présentes et inutilisables : le but ne contient ni paquet ni complément.
  Les deux facteurs sont non nuls (compilé : `detourPrimeContent_ne_one`, `radialShift_pos`).
* **Sonde 2** — `PairDepositOnLine` depuis la cassure : but restant
  `2·cosh(δ·log p_{n+1})·D_ligne = 2·D_ligne`, soit `D_ligne(log p_{n+1}) = 0` ; l'hypothèse de cassure inutilisable.
* **Sonde 3** — paquet de la paire au pas de la cassure : après trois réécritures, identité explicite en Tours
  brutes (`smoothingFactor × zeroTerm` aux abscisses `N`, `N+1`, `N+2`, plus conjugués) ; aucune occurrence du
  complément ; aucune demande du compilateur autre que la poursuite des réécritures.
* **Sonde 4** — dépôt du complément à la cassure = `log p_{n+1} − Δfond − paquet de la paire` : fermée par `rfl`.

## Lecture
Le compilateur, sur trois routes, ne demande jamais rien qui vienne de la cassure : la cassure est une identité
pour tout paquet (`break_split_any_packet`) et le complément absorbe ce que la paire ne dépose pas (sonde 4).
Ce qu'il demande est toujours une équation sur `δ` seul (sonde 1), déjà réfutée, ou une position de la cassure
dans la cellule de densité (sonde 2). Conséquence : « l'obligation arithmétique du raccord s'applique au transport »
ne peut pas être une égalité de transport (elle est fausse pour tout porteur) ; si un chaînon existe, c'est une
relation entre le dépôt de la paire à la cassure et la position de la cassure dans la cellule, dont
`PairDepositOnLine ⟺ changement de signe` est la forme compilée la plus faible. Rien de compilé ne place le point de
rencontre `p_{n+1}` sur la phase de la densité (`meetingPoint` est le premier supérieur de l'écart, sans phase).
