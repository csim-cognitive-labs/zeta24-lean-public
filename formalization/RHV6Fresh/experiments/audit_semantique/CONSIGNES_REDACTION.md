# Consignes de rédaction des fragments (Fable → Sonnet, 2026-09-29)

Plan : `../PLAN_AUDIT_SEMANTIQUE_20260929.md`. Vérités du maître : `VERITES_MAITRE.md` (V1…V194,
O1…O24, I1…I17, glossaire, tensions T1…T20). Données : `data/<projet>.jsonl` (un théorème par ligne :
name, module, file, line, type, docstring, deps_project, deps_base, axioms, uses_sorry, mentions_RH,
hyp_count). Lots : `lots/<LOT>.txt` (liste de modules). Sortie : `fragments/<LOT>.md`, EN FRANÇAIS.

## Règles absolues

1. Aucun fichier existant modifié, aucun `.lean` touché, aucun commit.
2. Rien d'inventé : chaque énoncé sémantique se lit dans le TYPE Lean (et la docstring, qui n'est
   qu'une aide : si docstring et type divergent, le TYPE fait foi et la divergence est notée
   « docstring ≠ type »). Ouvrir le fichier source si le type est illisible.
3. Les liens de conséquence viennent UNIQUEMENT du graphe `deps_project` (et `deps_base`) : « A
   entraîne B » signifie « la preuve de B utilise A ». Calculer les dépendances inverses par script.
4. Vocabulaire du glossaire de `VERITES_MAITRE.md` ; un terme absent y est signalé « (terme hors
   maître) » à sa première occurrence dans le fragment.
5. Non adversarial : on ne cherche pas à réfuter ; on qualifie honnêtement.
6. Chaque théorème du lot apparaît exactement une fois (contrôle final par script : nombre d'entrées
   = nombre de lignes du lot dans le jsonl ; écrire ce contrôle en fin de fragment).

## Statut (un seul, décidé d'abord mécaniquement puis vérifié à la lecture du type)

- `NON VALIDE (sorryAx)` si `uses_sorry`.
- `HORS STANDARD (<axiome>)` si axiome ∉ {propext, Classical.choice, Quot.sound} (ex. native_decide).
- `ÉQUIVALENTE À RH` si le type est une équivalence dont un côté est `RiemannHypothesis` (ou une
  prémisse dont un autre théorème compilé établit `↔ RiemannHypothesis` — citer lequel).
- `IMPLIQUE RH SOUS PRÉMISSE` si la conclusion est `RiemannHypothesis` avec hypothèse(s) Prop.
- `TERME RH FERMÉ` si le type est exactement `RiemannHypothesis` sans hypothèse (incident à signaler).
- `CONFIRMÉE SOUS CONDITION` si hypothèses Prop (hyp_count > 0) : nommer la condition en mots
  (« pour un zéro de côté bas », « sur un passage », « sous la prémisse P »…). Une hypothèse qui n'est
  qu'une donnée de l'objet (positivité de la hauteur d'un membre supérieur, `0 < q`) est une
  condition de domaine : statut `CONFIRMÉE`, la mentionner entre parenthèses.
- `CONFIRMÉE` sinon.
- `RÉFUTATION COMPILÉE` si la conclusion est `False` ou `¬ …` d'un énoncé que le maître ou une piste
  affirmait (dire lequel) — c'est une vérité négative établie.

## Format d'une entrée (audit RHV6Fresh, lots B1–B4 : format complet)

```
#### `NomCourt` — `Module` l.N — STATUT
- **Énoncé** : une ou deux phrases dans le vocabulaire du maître.
- **Vérités** : Vi, Vj (le théorème les établit ou les instancie) | `AJOUT` (aucune Vi) | Oi (touche un point ouvert, dire comment).
- **Repose sur** : noms (projet) ; base rhv3 : noms.
- **Entraîne** : noms des théorèmes du projet dont la preuve l'utilise (tous, ou les 12 premiers + « et N autres »).
```

## Format d'une entrée (audit cumulé, lots C : format tabulaire)

Tableau par module : `| théorème | énoncé sémantique (1 phrase) | statut | Vi / AJOUT | entraîne (nb) |`.
Une famille de théorèmes dont les types sont identiques à un paramètre numérique près peut partager
un énoncé (« idem, instance k ») mais chaque nom a sa ligne.

## Sections finales obligatoires de chaque fragment

1. **Table vérité → théorèmes** : pour chaque Vi touchée par le lot, la liste des théorèmes qui la
   confirment, avec le statut le plus fort atteint.
2. **Ajouts proposés** : vérités nouvelles, rédigées comme le maître les écrirait (une phrase), avec
   les théorèmes qui les établissent.
3. **Cascades** : pour les 5 à 15 théorèmes les plus utilisés du lot (dépendances inverses dans tout
   le projet), la chaîne « cette vérité est confirmée … et provoque la série de conséquences
   suivantes : … » (conséquences = théorèmes qui l'utilisent, avec leur énoncé en mots).
4. **Points ouverts touchés** (Oi) et **tensions** (Ti) éclairées par le lot, sans les résoudre.
5. **Incidents** (sorryAx, axiome hors standard, terme RH fermé, docstring ≠ type, théorème dont le
   nom promet plus que le type).
6. **Contrôle de complétude** (script).

Ne pas écrire de conclusion générale : les conclusions sont réservées à Fable.

## Correctif de contrôle n°1 (Fable, après contrôle de B1)

`CONFIRMÉE SOUS CONDITION` ne s'applique PAS quand l'hypothèse est l'antécédent de la relation
énoncée elle-même : injectivité (`f a = f b → a = b`), unicité (`P k → k = k₀`), implication entre
deux notions (`A → B` où A et B sont les deux termes de la vérité), caractérisation. Ces théorèmes
sont `CONFIRMÉE` (la vérité EST l'implication). Exemples corrigés : `expectedMinimumPrime_injective`
= CONFIRMÉE ; `firstTower_contactPair_unique` = CONFIRMÉE. `SOUS CONDITION` est réservé à une
restriction substantielle du domaine : côté bas `β < 1/2`, hors ligne, consécutivité stricte,
passage particulier, prémisse nommée (`PRegimeCapture`, `PLowestZeroOnLine`, `hReaches`…).
Le shared scratchpad est partagé : travailler dans un sous-répertoire propre au lot.
