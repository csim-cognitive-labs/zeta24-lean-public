# Journal de compilation — `Terminal/AuthenticRaccordLock.lean` (étape K′, direction corrigée de l'auteur, 2026-11-01)

Commande : `lake build RHV6Fresh.Terminal.AuthenticRaccordLock` (Lean v4.33.0-rc2, Mathlib de `rhv2_fresh`).
Feu vert de l'auteur : « continues avec la tentative envisagée » (2026-11-01), dix points de direction + hypothèse de
fermeture en cinq lignes (maître §19.27.1).

| Tentative | Résultat | Erreurs exactes |
|---|---|---|
| 1 (23 s) | échec | `lock_relation_reads_frequency_only` :178 `rewrite failed: did not find an occurrence of the pattern` : la cible écrit `rZeroRadialPosition p.zLaterMember` et le lemme `rZeroRadialPosition (⟨p.zLaterMember, hL⟩ : TrueZero).1` (égaux par définition, différents syntaxiquement) ; aucune autre erreur (l'identité de phase `towerInteraction_same_tower` passe du premier coup) |
| 2 (14 s) | succès | `Built RHV6Fresh.Terminal.AuthenticRaccordLock (7.4s)` ; 12 théorèmes, 1 définition `Prop` nommée (`RadialConservationAtAuthenticDeparture`), 1 définition d'objet (`occurrenceGap`) |

Correction : `exact (lock_relation_le_one_iff_oriented _).trans (towerRaccord_oriented_iff_height_lt p hE hL hT2)`
(unification par définition) au lieu de `rw`.

Axiomes (`#print axioms`, 12/12) : `[propext, Classical.choice, Quot.sound]`. Aucun `sorry`, `admit`, axiome ajouté
(`grep -c sorry` sur le journal : 0). Seuls avertissements : lignes de plus de 100 caractères (docstrings, comme dans
`SameGapsAudit.lean`). Module non ajouté à `RHV6Fresh.lean` ; aucun fichier de la chaîne modifié.
Extraits : `attempt1.errors.log`, `attempt2.summary.log` (journaux bruts dans le bac à sable de session, non versionnés).

## Ce que la composition établit (lecture, à confirmer par l'auteur ; maître §19.27)

1. La relation d'amplitudes de l'auteur (point 5) est le champ `transport` du raccord : déjà compilée.
2. Le premier partagé de tout raccord sortant de `e` est la rencontre de l'écart d'occurrence `⟨idx e⟩` (point 3).
3. La contribution exacte de toute Tour sur cet écart est `𝒯_z(M) − 𝒯_z(Occ e)` ; son énergie exacte est
   `A(M)² + A(Occ)² − 2·A(M)·A(Occ)·cos(T·(log M − log Occ))` (point 6, phases conservées).
4. L'hypothèse de fermeture de l'auteur (orientation du raccord sortant imposée par la lecture authentique du précédent)
   est un THÉORÈME sur les acquis : zéro authentique atteint verticalement ⟹ raccord sortant orienté et hiérarchique,
   quelle que soit la position radiale de l'arrivée ; de même au premier zéro (point 7).
5. Mais, dès `T_e ≥ 2`, la relation `≤ 1` équivaut à `T_e < T_l` seule : elle ne lit pas `β_l`. Une arrivée OFF laisse
   ce raccord orienté ; c'est le raccord SUIVANT qui casse (point 9 de l'auteur confirmé : la relation ne suffit pas).
6. Premier but non résolu (point 8) : « arrivée en ligne ⟺ hiérarchie au raccord qui la quitte » ; le verrou qui ferme
   est donc la conservation radiale au départ d'un membre ON (`RadialConservationAtAuthenticDeparture`, Prop nommée,
   jamais prouvée), qui avec le premier zéro ON donne RH par composition de théorèmes existants.
