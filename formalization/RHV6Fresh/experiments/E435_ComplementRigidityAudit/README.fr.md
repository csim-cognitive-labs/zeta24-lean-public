> Version française conservée à titre de référence. Main language: English, see README.md.

# E435 — Audit exhaustif de la rigidité du complément au premier partagé (2026-11-04)

Expérience de compilation et d'audit seule (aucune mesure numérique ; aucun jumeau requis). Mission de l'auteur
(2026-11-04) : « déterminer si les théorèmes existants imposent au complément collectif une contrainte indépendante
incompatible avec la dérive de la paire OFF et de son miroir au point de rencontre arithmétique ». Ni nouvelle mesure,
ni nouveau modèle, ni prémisse équivalente à RH. Ne pas recommencer E429, ne pas réécrire E434, ne pas inventer une
conservation du transport.

## Question posée (avant toute compilation)
La reconstruction arithmétique exacte aux rencontres impose-t-elle au complément (`packetᶜ` du porteur `C`, cas
miroir) une rigidité déjà démontrée dans le corpus qui rende impossible la dérive de la Tour OFF et de son miroir ?

## Hypothèses admises
Uniquement un porteur `C : OffCarrier` (premier zéro bas authentique, prédécesseurs canoniques en ligne) et le cas
miroir `h : C.outgoing.zLaterMember = (mirrorMember C.zero).1`, comme dans E432–E434. Aucune autre hypothèse ; les
sondes qui en ajoutent une (borne, silence) doivent le déclarer et n'alimentent aucun théorème du module.

## Acquis réutilisés (vérifiés dans leur forme Lean exacte avant usage, voir RESULTS.md §1)
`pair_complement_series_balance`, `pair_window_re_balance`, `pairPrimitive_re_from_contacts`,
`integratedTower_re_from_lastContact`, `towerIm_from_lastContact`, `packetIncrement_series_telescopes`,
`localPacket_pair_eq`, `channelPrimitive_packet_eq`, `exactRemainder_eq_packet_add_complement`,
`smoothedRemainder_eq_tsum_residueTerm`, `channel_eq_packet_add_complement`, `break_realized_by_high_frequencies`,
`norm_packetIncrement_finset_le`, `mirror_pair_exponent_le(_remainderExponent)`, `off_signature_lifts_remainderExponent`,
`infinite_complement_closes`, `acquired_exponent_not_below_mirror`, `riemannHypothesis_iff_remainderExponent_eq_half`,
`exists_offCarrier_of_not_riemannHypothesis`, `no_offCarrier_of_riemannHypothesis`, `norm_mirror_primitive_term`,
`norm_zero_primitive_term`, `inversion_height`, `inversion_radial`, `mirror_contacts_coincide_iff`,
`radial_of_contact_value_ratio`, `mirror_amplitude_ratio_tendsto`, `detour_arithmetic_factor_ne_one`,
`detour_transport_product`, `detour_defect_eq_memberStep_product`. Aucune démonstration refaite.

## Protocole
1. Pré-enregistrer (ce fichier, commit) avant la première compilation.
2. Inventaire exhaustif (RESULTS.md §1) : tous les théorèmes du corpus portant sur le complément ou ses variations,
   avec nom, fichier, énoncé, hypothèses, domaine, conditionnel/inconditionnel, dépendance à RH, portée sur une
   famille infinie de rencontres ; nature (identité de décomposition / majoration / égalité de raccord / asymptotique).
3. Sondes TDD dans `ComplementRigidityProbe_SCRATCH.lean` (non versionné, supprimé après capture ; sorties exactes
   dans `logs/probe_attempt*.txt`).
4. Module isolé `Terminal/ComplementRigidityAudit.lean` (non ajouté à `RHV6Fresh.lean`), deux tentatives de compilation
   au plus (`logs/lean_attempt{1,2}.txt`), aucune hypothèse posée, aucun `sorry`, axiomes affichés ;
   `lake build RHV6Fresh` vert après.

## Sondes prévues et attendus (écrits avant exécution)
- **S1 — Bilan exact par contacts.** Partie réelle du complément sur une fenêtre `[a, a+m]` = somme des poids de von
  Mangoldt − variation réelle du pas du fond − effet de bords, l'effet de bords étant lu aux quatre points
  `a, a+1, a+m, a+m+1` par les contacts des deux membres (valeurs signées, fractions de cellule, retards d'angle
  conservés ; aucun module, aucun terme supprimé). Attendu : compile par réécriture de `pair_window_re_balance` et
  `pairPrimitive_re_from_contacts`.
- **S2 — Transport vers la série des rencontres.** Pour toute suite de fenêtres, la somme des sommes de fenêtre du
  complément est la somme des différences de ses pas locaux aux bords ; deux fenêtres consécutives se concatènent ;
  le pas local du complément en tout `N ≥ 2` est le reste exact moins le pas de la paire ; au niveau des primitives,
  complément = `x·reste lissé(x) − primitive de la paire(x)` pour tout `x > 1`. Attendu : compile sans borne ; la
  série de fenêtres ne porte aucune information au-delà de la suite ponctuelle du complément.
- **S3 — Contrainte indépendante.** Application des seuls théorèmes de rigidité retrouvés : (i) borne inférieure
  ponctuelle de la cassure portée par le complément de la paire (instance de `break_realized_by_high_frequencies`
  sur la famille finie des quatre membres) ; (ii) exposant du reste ≥ `1/2 + δ` ; (iii) aucune borne du reste sous
  `1/2 + δ` n'est compatible avec `C` ; (iv) une borne de croissance du complément seul à l'exposant `1 + θ` ne
  transfère au reste lissé que l'exposant `max(θ, 1/2 + δ)`. Attendu : (i)–(iii) instances directes ; (iv) une
  majoration par les quatre normes des membres de la primitive.
- **S4 — Contradiction OFF.** Depuis `C`, `h` et les résultats de S1–S3 seuls, tenter `False`. Attendu (écrit avant
  exécution) : aucune contradiction ; le but `False` reste avec, en contexte, l'exposant du reste ≥ `1/2 + δ` et
  l'exposant acquis `1` seulement. Variante : complément borné à l'exposant `1 + θ`, `θ < 1/2 + δ` ⟹ `False` :
  attendu, le but reste (le transfert donne le reste à l'exposant `1/2 + δ`, non strictement en dessous).

## Critères (une seule catégorie)
A fermeture compilée ; B réduction inconditionnelle nouvelle du chaînon ; C frontière équivalente à RH, équivalence
compilée ; D aucune rigidité indépendante, propriété absente nommée. Attendu : D, avec la forme C de la propriété
absente (`(OffCarrier → False) ↔ remainderExponent = 1/2`) compilée.
