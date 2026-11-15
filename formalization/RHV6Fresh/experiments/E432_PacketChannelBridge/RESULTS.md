# E432 — Résultats (2026-11-04)

Pré-enregistré au commit 310e9a57 avant toute compilation. Compilation seule ; aucune conclusion numérique.

## Sondes (fichier non versionné, supprimé après capture)
- `logs/probe_attempt1.txt` : 6 erreurs — deux fermetures `linarith` (remplacées par `sub_zero`/`add_zero`), une
  application de fonctions sommées non dépliée (`Pi.add_apply`), une instance `const_smul` ambiguë (remplacée par
  `continuousAt_const.mul`), un `simp` déjà suffisant pour la dérivée conjuguée, et la sonde S1. L'identité ponctuelle
  du surplus (`pair_zeroTerm_surplus`) est passée dès cette première exécution.
  - S1 (« le surplus hyperbolique du canal des Tours s'annule au changement de signe de la densité ») : le compilateur
    laisse la partie réelle de `exp(t·ρ_L)/ρ_L` en `t = (π/2 + kπ)/T` — c'est-à-dire la phase propre du point de ligne
    `arctan(2T)`, absente de la densité. But faux, comme attendu : le lemme compilé `lineTerm_re_at_signChange` donne
    `(−1)^k · T · e^{t/2}/(1/4 + T²) ≠ 0`.
- `logs/probe_attempt2.txt` : 1 erreur (ordre des réécritures dans `lineTerm_exp_re`, corrigé) ; tout le reste passe.

## Module `Terminal/PacketChannelBridge.lean` (isolé, 17 déclarations, aucun `sorry`)
- Tentative 1/2 (`logs/lean_attempt1.txt`) : 0 erreur ; `#print axioms` sur 6 énoncés : `[propext, Classical.choice,
  Quot.sound]`. Aucune seconde tentative nécessaire.
- `lake build RHV6Fresh` : vert, EXIT=0 (`logs/lake_build_full_trimmed.txt`).

## Compilé
1. `pair_zeroTerm_surplus` : dans le canal des Tours, `Tour(z) + Tour(z*) − 2·ligne = 2(cosh(δ log x) − 1)·ligne +
   (δ/ρ_L)·(Tour(z) − Tour(z*))`. Le facteur hyperbolique de la densité survit ; s'y ajoute une déformation
   proportionnelle au décalage radial, portée par la différence des deux Tours (poids `1/ρ` propres).
2. `channelPrimitive_packet_hasDerivAt` (cas (a)) : la primitive du paquet à quatre membres a pour dérivée
   `−m·(Tour(z) + conj + Tour(z*) + conj)` ; `localPacket_eq_integral` : le pas local du paquet sur `[N, N+1]`
   (`N ≥ 2`) est l'intégrale de cette dérivée.
3. `packetTowerDerivative_surplus` : surplus de la dérivée du paquet par rapport au jumeau en ligne de mêmes
   multiplicités = `−m·(facteur hyperbolique + déformation + conjugués)`.
4. `lineTerm_exp_re`, `lineTerm_re_at_signChange`, `lineTerm_re_at_signChange_ne_zero`,
   `hyperbolic_surplus_re_at_signChange_ne_zero` : au changement de signe de la densité, le terme de ligne du canal
   des Tours et le surplus hyperbolique (partie réelle) ne s'annulent pas.

## Lecture
Le pont existe et il est compilé : le pas du paquet de la paire est l'intégrale, sur le pas de la cassure, d'une
dérivée de Tour dont le surplus par rapport au jumeau en ligne est le facteur hyperbolique de la densité PLUS une
déformation en `δ/ρ_L` fois la différence des Tours. Conséquence : la condition « dépôt en ligne » du canal des
paquets n'est pas le changement de signe de la densité (le terme de ligne y a sa propre phase `arctan(2T)`) ; les deux
lectures, densité et paquets, diffèrent exactement par le lissage. Le chaînon manquant se réduit donc à l'absorption
par le complément, sur la série des pas, d'un surplus intégré non nul — rien ici ne le ferme (identité de cassure).
