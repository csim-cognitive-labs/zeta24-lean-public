# RHV6 — progression événementielle et premier von Mangoldt uniquement

La surface Lean active contient six modules locaux :

```text
RHV6Fresh
RHV6Fresh.Audit
RHV6Fresh.Core.Zero
RHV6Fresh.Grammar.Reconstruction
RHV6Fresh.Terminal.PrimeProgressionCollision
RHV6Fresh.Terminal.ContactVonMangoldtCount
```

La seule donnée de Tour ajoutée est le contact supérieur de l'état authentique
déjà produit depuis l'occurrence du membre. Il n'y a ni hauteur comparée,
géométrie miroir, orientation, étage libre, portée, lecture locale, minimum
attendu, ni nouvel événement.

Les résultats compilés sont :

```lean
eventOccurrence_vonMangoldt :
  Prime (occurrence z) ∧ Λ (occurrence z) = log (occurrence z)

sameEvent_sameVonMangoldtPrime :
  eventOf b = eventOf a → occurrence b = occurrence a

sameVonMangoldtWeight_samePrime :
  Λ (occurrence b) = Λ (occurrence a) → occurrence b = occurrence a

eventProgression_nextPrime :
  Consecutive a b →
    occurrence b = nextPrime (eventIndex a) ∧ occurrence a < occurrence b

samePrime_contradicts_eventProgression :
  Consecutive a b → occurrence b = occurrence a → False

sameVonMangoldtWeight_contradicts_eventProgression :
  Consecutive a b → Λ (occurrence b) = Λ (occurrence a) → False

advancedAuthenticContactCount_eq_vonMangoldtChebyshev :
  count(C⁺ z) = primeCountingFromJ(ψ, floor(C⁺ z))

previousOccurrenceCount_lt_secondAdvancedContactCount :
  Consecutive a b → count(occurrence a) < count(C⁺ b)

vonMangoldtCountAtSecondAdvancedContact_not_stuck :
  Consecutive a b → π_J(C⁺ b) > π_J(occurrence a)
```

La tentative demandée isole donc exactement la contradiction souhaitée :
`MÊME PREMIER + PROGRESSION → False`, sans autre notion.

Le test demandé au contact le plus avancé a désormais été effectué. La
localisation authentique donne `occurrence b < C⁺ b`. La dualité exacte entre
le comptage et l'énumération première montre alors que le compteur reconstruit
depuis von Mangoldt/Chebyshev à `C⁺ b` est strictement supérieur au compteur à
`occurrence a`. Il a donc progressé et n'est pas resté sur le premier
précédent.

La proposition nécessaire à la contradiction proposée serait exactement :

```lean
∀ {a b : TrueZero},
  PZeroMembersConsecutive a.1 b.1 →
    advancedAuthenticContactCount b =
      nEdgePrimeRank (occurrence a : ℝ)
```

Sa négation est compilée sous le nom
`secondAdvancedContactCount_ne_previousOccurrenceCount`, et la stricte
inégalité correspondante sous
`vonMangoldtCountAtSecondAdvancedContact_not_stuck`. La fermeture demandée ne
peut donc pas être obtenue de ce contact et de ces définitions sans contredire
un théorème maintenant vérifié par Lean.

`RH_FOUND = FALSE` : aucun théorème RH inconditionnel n'est déclaré.
