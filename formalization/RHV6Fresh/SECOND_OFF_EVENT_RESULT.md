# Tentative inversée sur le second événement OFF — 2026-09-21

L'analyse part des définitions Lean, sans invoquer les maîtres.
Aucun nouvel événement, lecteur, sélecteur, compteur ou axiome n'est défini.

## Calcul de l'événement effectivement transporté

`Terminal/SecondOffEvent.lean` compose les preuves sur les états authentiques :

`off_literal_mirror_occurrence_distinct` traite aussi le miroir fonctionnel
littéral : sous OFF, son occurrence propre diffère de celle du membre source,
par injectivité membre-sensible. Cela ne suppose pas la paire miroir consécutive.

1. `sameHeight_authentic_radial_progression` : à hauteur égale, la coordonnée
   radiale décodée du membre postérieur est strictement supérieure.
2. `transported_event_prime_progresses` : l'occurrence du même événement
   transporté progresse strictement pour chaque paire consécutive.
3. `transported_event_prime_not_stalled` : sur cette paire, Lean prouve
   la négation de la non-progression proposée.
4. `sameHeight_second_event_distinguished` : le nœud de hauteur des deux
   états est identique, mais son occurrence est strictement inférieure à
   l'occurrence du second événement membre-sensible.
5. `off_second_event_computation` : les faits précédents s'appliquent aux
   mêmes vrais membres consécutifs produits depuis un vrai zéro OFF.

La conservation de l'événement par un état conserve `(T, β)`, sa clé d'ordre
lexicographique, et donc son occurrence propre. Elle ne conserve pas seulement
la hauteur. La translation négative des contacts correspondants ne fait pas
disparaître la différence de β décodée par ces contacts.

## Tentative de non-progression

Le test a demandé, pour la paire produite par `off_sameHeight_pair`,

```lean
RHV5Fresh.occurrenceOfEvent (eventOf b) ≤
  RHV5Fresh.occurrenceOfEvent (eventOf a)
```

avec en contexte la géométrie complète, le transport des états, les identités
d'occurrences, le successeur et la progression stricte. Après réécriture des
identités, la tentative arithmétique `omega` échoue. Ce résultat de tactique
n'est pas un contre-modèle de RH et ne prouve pas l'impossibilité de toute
autre démonstration. Le fichier de test en échec n'est pas ajouté à la bibliothèque.

Le résultat positif compilé est plus précis qu'un échec de tactique :

```lean
theorem transported_event_prime_not_stalled {a b : TrueZero}
    (hab : PZeroMembersConsecutive a.1 b.1) :
    ¬ (RHV5Fresh.occurrenceOfEvent (eventOf b) ≤
      RHV5Fresh.occurrenceOfEvent (eventOf a))
```

Sous OFF, une preuve indépendante de la non-progression constituerait donc
effectivement une contradiction. Elle n'est pas produite par le transport
événementiel existant, qui donne la progression, ni par la seule immobilité
de son observable hauteur. Les deux sont distingués formellement dans le
module, sans modifier les définitions.

`RH_FOUND = FALSE` : aucun théorème inconditionnel RH n'est ajouté.

## Validation

`lake build` : PASS (4017 tâches, après intégration de `origin/main`).
Sources RHV6 : `sorry=0`, `admit=0`, aucune déclaration d'axiome.
Les cinq résultats contrôlés par `#print axioms` utilisent uniquement
`[propext, Classical.choice, Quot.sound]`.


Les changements concurrents de `main` sur le minimum attendu ont été conservés.
Leur raccord `universal_expectedMinimum_package` nécessitait une réécriture
explicite de `memberMZOccurrence b` en `fnPrimeSuccessor (nZeroSourceIndex a.1)`;
elle a été ajoutée sans changer l’énoncé. L’ancien module d’orientation supprimé
sur `main` n’a pas été réintroduit.
