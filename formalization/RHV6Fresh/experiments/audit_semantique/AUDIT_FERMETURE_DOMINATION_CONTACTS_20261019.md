# Audit de fermeture RHV6Fresh — 19 octobre 2026

Référence examinée : `fcbfb025`. Sources : `RHV6Fresh/Terminal/OffAmplificationAudit.lean`, `RHV6Fresh/Terminal/DemonstrationChain.lean`, `RHV6Fresh/Terminal/AstraSeparation.lean`, `RHV6Fresh/Terminal/GeometricEnergyRaccord.lean`. Audit de lecture des corps ; compilation locale non exécutée. Le journal utilisateur rapporte `lake build RHV6Fresh` PASS, axiomes standard, 0 sorry/admit.

## Verdict vérifiable
1. `mirror_exceeds_domination_at_prime` prouve qu'une arrivée de partie réelle strictement inférieure à un demi a un miroir dont le terme dépasse le champ du premier zéro **à au moins un nombre premier**.
2. `mirror_dominated_at_primes_of_onLine` prouve la domination au miroir d'un membre ON à chaque nombre premier.
3. `low_arrival_impossible_of_mirror_domination_at_primes` oppose exactement ces deux inégalités : contradiction valide **sous** la domination supposée au miroir OFF.
4. `arrival_low_contradiction` consomme explicitement `hDomPrime` pour fermer `False` ; aucune preuve de `hDomPrime` n'apparaît à cet endroit.
5. `riemannHypothesis_terminal` conserve `hDomPrime` dans sa signature ; la fermeture est conditionnelle.
6. `mirror_domination_premise_iff_riemannHypothesis` prouve que la prémisse universelle a exactement la force de RH. Cela interdit de la présenter comme un théorème indépendant déjà établi.
7. `AstraSeparation.interMemberLogSeparation_lt_half_pitch` réfute le plancher historique inter-Tours d'un pas complet ; `ringJump_logWidth` ne concerne que les contacts d'une même Tour.
8. `GeometricEnergyRaccord.pivotCell_amplitude_brackets` encadre l'amplitude au premier par les contacts propres de sa cellule, sans assimiler un premier à un contact.
9. La non-compensation par **groupe fini** ne fournit pas à elle seule un contrôle du complément infini. Les propriétés du reste lissé doivent être prouvées dans la même normalisation que `zeroTerm`.
10. Les résultats numériques E071, E112–E115, E310–E324 sont des guides de construction ; ils ne remplacent pas une implication universelle Lean.

## Réduction recherchée : garder la fermeture Astra, changer l'obligation
On conserve le schéma « progression première + contacts/frequences authentiques => incompatibilité de la première arrivée OFF », mais sans `π/T` comme distance inter-Tours. Il suffit de démontrer, **pour le premier passage engagé qui serait OFF**, une borne au miroir au **seul nombre premier témoin** `q` construit par `mirror_exceeds_domination_at_prime`. C'est une réduction locale de la consommation de `hDomPrime`, non une preuve autonome : la borne au témoin reste à dériver.

## Hypothèses intermédiaires à tester, sans les déclarer vraies
**H1 — Conservation au contact authentique.** Lors d'un passage ON engagé, les cellules propres de l'arrivée et les raccords premiers imposent une borne de contribution du miroir au premier témoin. Vérifier l'indépendance de cette borne par rapport à la conclusion `β_l = 1/2`.

**H2 — Fréquence et rencontre.** Les rencontres exactes de `zeroTerm` avec le canal de comptage, associées à la progression de rang, imposent une contrainte sur la cellule lue par le miroir ; démontrer une exclusion du décalage OFF, et non une simple différence de contacts.

**H3 — Contrôle collectif au premier témoin.** Isoler la fibre de hauteur `T_l` dans la formule explicite au premier `q` et borner rigoureusement la contribution du reste infini. Ne pas substituer la non-compensation finie à ce contrôle.

**H4 — Domination sous grammaire.** Formuler une loi vérifiable depuis les écarts premiers exacts et la représentation spectrale, donnant la borne au miroir sans la supposer. Si elle est équivalente à RH, l'identifier comme nouvelle formulation du but.

**H5 — Contrôle d'échelles.** Vérifier dans tous les lemmes les types `zeroTerm`, `pairAmplitude`, `firstField`, le lissage et les coefficients. Ne pas transporter une inégalité entre signaux renormalisés sans théorème de conversion.

## Plan de vérification Lean
A. Extraire le premier témoin premier `q` et sa borne de dépassement depuis `mirror_exceeds_domination_at_prime`.
B. Reconstituer les deux contacts authentiques de la cellule contenant `q`, leurs indices dérivés et la fréquence `T_l`.
C. Calculer la position de rencontre et la différence de cellule pour le membre bas et son miroir ; conserver les deux branches de la trichotomie.
D. Connecter le saut de grammaire au premier `q` au **canal de comptage**, pas au terme brut isolé.
E. Isoler le terme miroir et le complément infini, sans supposer la borne recherchée.
F. Tenter la contradiction locale au témoin ; examiner toute hypothèse nouvellement ajoutée pour circularité.
G. Vérifier `#print axioms` et la signature complète du théorème terminal après chaque tentative.

## Conclusion
La contradiction OFF + domination du miroir est bien codée ; l'obligation manquante est une loi indépendante « événements premiers + contacts authentiques + fréquences + rencontres => borne au miroir au premier témoin ». La géométrie seule démontre la déformation, pas l'interdiction de cette déformation. La fermeture conditionnelle compilée n'est pas une preuve inconditionnelle de RH.
