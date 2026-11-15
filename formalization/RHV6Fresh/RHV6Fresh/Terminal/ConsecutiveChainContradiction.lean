/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Direct.PairTowers

/-!
# RHV6Fresh — la chaîne arithmétique intouchable (auteur, 2026-09-25 ; destruction de V/Xor, 2026-09-26)

Niveau LECTURE ARITHMÉTIQUE. Transcription littérale de la chaîne que l'auteur qualifie d'intouchable :
pour deux vrais zéros consécutifs `a → b` (ici le membre `z` et son miroir `z* = mirrorMember z`,
sous consécutivité stricte `hab : PZeroMembersConsecutive z (z*)`),

    z → z* ⟹ n* = n + 1 ⟹ Occ(z) = p_n ⟹ p_min(z) = Occ(z*) = p_{n+1} ⟹ p_min(z*) = p_{n+2}.

Chaque flèche est déjà un théorème compilé (`mirror_sourceIndex_of_consecutive`,
`occurrence_eq_primeAtRank`, `progression_occurrence`, `expectedMinimum_eq_mirror_occurrence_of_consecutive`,
`expectedMinimum_lt_mirror_expectedMinimum`) : `consecutivePairArithmeticChain` ne fait que les
regrouper, sans aucune hypothèse nouvelle.

**Destruction (auteur, 2026-09-26)** : tout ce qui, dans ce fichier et dans `Direct/PairTowers.lean`,
`Terminal/PairContradiction.lean`, `Terminal/EntryCollision.lean`, `Terminal/InversionClosure.lean`,
`Terminal/PairHeightGap.lean`, `Terminal/TwoTowersComparison.lean`, portait la notion « V » (dernier
rayon de la seconde Tour comparé à `p_min(z)`, une référence d'un AUTRE zéro, via l'inversion d'une
cellule fixe) et l'alternative `Xor` bâtie dessus (`pivotCoordinate_mono`,
`secondTower_verification_or_reads`, `secondTower_verification_xor_reads`,
`verification_is_pivot_coarseness_not_place_collapse`) est retiré : ces quatre derniers fichiers sont
supprimés, ce fichier est réduit à la seule chaîne arithmétique. Motif de l'auteur : la seconde Tour
comparée par « V » n'est pas la bonne quantité — la géométrie du recul du miroir doit s'étudier
directement sur `z*` lui-même, par `k(z*, p_min(z*)) → k(z*, Occ(z*))` (déjà compilé,
`secondTower_reads_occurrence_iff_coordinate_lt`, `Direct/PairTowers.lean`), jamais par l'inversion
d'une cellule fixe confrontée à `p_min(z)`.

`RiemannHypothesis` n'apparaît pas ici. Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## La chaîne arithmétique intouchable -/

/-- **La chaîne intouchable** (auteur, 2026-09-25), sous consécutivité stricte et `β < 1/2` :
l'événement avance d'un cran, l'occurrence du miroir est exactement le minimum attendu de `z`, et les
deux minima attendus sont strictement ordonnés. Regroupement de quatre théorèmes déjà compilés, aucune
hypothèse nouvelle. -/
theorem consecutivePairArithmeticChain {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (hab : PZeroMembersConsecutive z.1 (mirrorMember z).1) :
    nZeroSourceIndex (mirrorMember z).1 = nZeroSourceIndex z.1 + 1 ∧
      occurrence (mirrorMember z) = expectedMinimumPrime z ∧
      occurrence z < expectedMinimumPrime z ∧
      expectedMinimumPrime z < expectedMinimumPrime (mirrorMember z) :=
  ⟨mirror_sourceIndex_of_consecutive hab,
    (expectedMinimum_eq_mirror_occurrence_of_consecutive hab).symm,
    occurrence_lt_expectedMinimumPrime z,
    expectedMinimum_lt_mirror_expectedMinimum hβ⟩

/-! ## Tentative de composition terminale avec le mouvement réfléchi authentique (auteur, demande de
composition, 2026-09-26)

But : composer `consecutivePairArithmeticChain` (progression arithmétique intouchable) avec
`reflectedFromOrigin_never_reaches_expectedMinimum` (`Tower/ReflectedMotion.lean` : le mouvement
réfléchi authentique, suivi depuis SA PROPRE origine, n'atteint jamais `p_min(z*)`), SANS ajouter de
prémisse nouvelle, pour voir si `False` en sort. Résultat : ils se composent sans heurt, en une seule
proposition, PARCE QU'ILS PORTENT SUR DEUX OBJETS DIFFÉRENTS : la chaîne parle de `occurrence`/
`expectedMinimumPrime` (des entiers, la grammaire des rangs) ; le mouvement réfléchi parle de
`reflectedIncidence` (une trajectoire réelle continue). Aucun théorème compilé n'identifie l'un à
l'autre — `secondTowerOf`, l'objet qui EST identifié à sa propre coordonnée pivot, n'utilise justement
PAS ce domaine (`invertedPairAt_coordinate_le_zero`). Composer pour de vrai exigerait d'ajouter
l'hypothèse « le contact terminal de la seconde Tour EST une valeur de ce mouvement à coordonnée
`j + 1`, `j : ℕ` » — hypothèse absente du code, et l'ajouter serait une prémisse nouvelle interdite. -/

/-- **Composition explicite, sans contradiction** : la chaîne arithmétique et le fait que le mouvement
réfléchi authentique n'atteint jamais `p_min(z*)` tiennent SIMULTANÉMENT, pour tout zéro hors ligne
consécutif à son miroir. Ce n'est pas un théorème vide (les deux conjoints sont chacun non triviaux et
déjà compilés séparément) ; c'est la preuve, par construction d'un terme habité, qu'aucune incohérence
ne surgit de leur simple juxtaposition — la contradiction cherchée par l'auteur n'existe PAS à ce
niveau de composition. -/
theorem arithmeticChain_and_reflectedFromOrigin_coexist {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (hab : PZeroMembersConsecutive z.1 (mirrorMember z).1) (j : ℕ) :
    (occurrence z < expectedMinimumPrime z ∧
      expectedMinimumPrime z < expectedMinimumPrime (mirrorMember z)) ∧
      ¬ ((expectedMinimumPrime (mirrorMember z) : ℝ) ≤
          reflectedIncidence (mirrorMember z) ((j : ℤ) + 1)) :=
  ⟨(consecutivePairArithmeticChain hβ hab).2.2,
    reflectedFromOrigin_never_reaches_expectedMinimum z j⟩

/-- **La composition terminale EXACTE demandée par l'auteur** (2026-09-26) : SI l'obligation « la
seconde Tour doit atteindre `p_min(z*) = p_{n+2}` » est réalisée PAR le mouvement réfléchi authentique
(`∃ j, p_min(z*) ≤ C'_{j+1}`), ALORS `False`, sans hypothèse supplémentaire — schéma exact du bloc de
l'auteur : `∃j[...] ∧ ∀j¬[...] ⟹ ⊥`, ici avec le `∀j¬[...]` du côté prémisse (compilé,
`reflected_no_stop_event`) et le `∃j[...]` du côté hypothèse nommée `hReaches`. C'est un théorème
CONDITIONNEL : la clause `hReaches` n'est prouvée nulle part dans le code (elle affirmerait que le
contact terminal de `secondTowerOf` EST une valeur de ce mouvement précis, ce que
`invertedPairAt_coordinate_le_zero` réfute déjà pour l'objet compilé) ; en faire un axiome serait
interdit. Ce théorème ne clôt donc rien : il rend explicite, en Lean, exactement où se situerait la
collision SI l'identification `hReaches` était un jour établie sans hypothèse. -/
theorem terminalCollision_conditional_on_reflectedObligation (z : TrueZero)
    (hReaches : ∃ j : ℕ,
      (expectedMinimumPrime (mirrorMember z) : ℝ) ≤ reflectedIncidence (mirrorMember z) ((j : ℤ) + 1)) :
    False := by
  obtain ⟨j, hj⟩ := hReaches
  exact reflectedFromOrigin_never_reaches_expectedMinimum z j hj

/-! ## Les deux objets tenus séparés, sans `secondTowerOf` (auteur, correction du 2026-09-26 : « ta
conclusion sémantique ne suit pas »)

L'auteur objecte, preuves à l'appui (E44/E071, `firstTower_cell_contains_expected`,
`firstTower_contactPair_unique`, `secondTower_coordinate_eq_unique_mirrorContactPair`) : la
rigidification prouve que `secondTowerOf` EST la cellule unique de `firstTowerOf (mirrorMember z)`
relue à rebours — pas une trajectoire du mouvement réfléchi authentique parcouru depuis son origine.
Conclusion demandée : ne jamais mélanger les deux objets ; modéliser CHACUN séparément avec SON
contrat déjà figé, puis composer, sans `secondTowerOf`, sans nouvelle hypothèse. Les deux contrats
déjà compilés, cités ici tels quels : `firstTower_cell_contains_expected (mirrorMember z)` (la Tour
PROPRE de `z*`, contient son minimum attendu) et `reflectedFromOrigin_never_reaches_expectedMinimum`
(le mouvement réfléchi AUTHENTIQUE, suivi depuis sa PROPRE origine, n'atteint jamais ce même minimum).
Aucun des deux ne cite `secondTowerOf`. -/

/-- **Composition sans `secondTowerOf`, sans `∃j`, sans nouvelle hypothèse** : la Tour propre du membre
miroir contient son minimum attendu (théorème `firstTower_cell_contains_expected`, tout `β`) ET le
mouvement réfléchi authentique, suivi depuis sa propre origine, ne l'atteint jamais (théorème
`reflected_no_stop_event`). Ce fait est lui-même AVEUGLE À `β` (aucune des deux prémisses ne dépend de
`hβ` ni de `hab`) : il ne peut donc, seul, être LA contradiction OFF cherchée — la mesure honnête de sa
conséquence est qu'il tient identiquement des deux côtés, comme terme habité, sans heurt. -/
theorem properTowerOfMirror_and_reflectedMotion_coexist (z : TrueZero) (j : ℕ) :
    ((firstTowerOf (mirrorMember z)).entryContact < (expectedMinimumPrime (mirrorMember z) : ℝ) ∧
      (expectedMinimumPrime (mirrorMember z) : ℝ) ≤ (firstTowerOf (mirrorMember z)).lastRayContact) ∧
      ¬ ((expectedMinimumPrime (mirrorMember z) : ℝ) ≤
          reflectedIncidence (mirrorMember z) ((j : ℤ) + 1)) :=
  ⟨firstTower_cell_contains_expected (mirrorMember z),
    reflectedFromOrigin_never_reaches_expectedMinimum z j⟩

/-! **Verdict honnête** : les deux objets, tenus séparés exactement comme l'auteur l'exige (jamais
`secondTowerOf`, jamais l'inversion a posteriori d'une cellule fixe), coexistent sans heurt. Le pont
qui manquerait pour produire `False` serait une identification entre les deux — affirmer que le
contact terminal de la Tour PROPRE de `z*` (`firstTowerOf (mirrorMember z)`, coordonnée `pivotCoordinate`,
domaine empiriquement `≥ 0` sur Odlyzko mais non borné par théorème) EST une valeur du mouvement
réfléchi authentique (coordonnées `j + 1 ≥ 1`, `j : ℕ`) — identification qu'aucun théorème du code
n'établit (`canonicalOrigin_lt_iff_zero_le_pivotCoordinate` donne le signe de la première coordonnée
SI `canonicalOrigin (mirrorMember z) < p_min(z*)`, fait lui-même non prouvé sans condition ; les deux
mouvements sont d'ailleurs des fonctions différentes de `ℤ` — `towerMotionOf` et `reflectedIncidence`
— reliées seulement par `reflectedIncidence_eq`, qui identifie le mouvement réfléchi de `z*` à SA
PROPRE Tour propre en coordonnées négatives, jamais à un `∃j` positif). En fabriquer une serait une
prémisse nouvelle interdite. -/

/-! ## Reformalisation avec les DEUX CONTACTS déjà fixés de la seconde Tour authentique (auteur,
objection E44/E071, 2026-09-26)

Objection de l'auteur : la sémantique expérimentale (E44/E071) fixe d'abord un objet unique — UNE Tour,
DEUX contacts `(C⁻, C⁺)` par inversion round-trip — jamais une suite libre de contacts indépendants ;
chercher un `∃ j` libre sur le mouvement réfléchi (théorèmes ci-dessus) répond à la mauvaise question.
Le bon objet, DÉJÀ COMPILÉ, DÉJÀ FIXÉ, est `secondTowerOf z` lui-même : ses deux contacts sont
`(secondTowerOf z).lastRayContact` (`C⁻`) et `(secondTowerOf z).entryContact` (`C⁺`), obtenus par LA
MÊME règle du pivot que la première Tour, appliquée à `(1 − β, T)` (§3 ci-dessus, `secondTowerOf`,
`secondTower_entry_eq_reflected`/`secondTower_lastRay_eq_reflected` : l'inversion de ces deux contacts
précis EST un théorème, pas un choix). Composer ces deux contacts déjà fixés avec la progression déjà
figée (`consecutivePairArithmeticChain`), sans aucun `∃ j` nouveau. -/

/-- **La composition avec les deux contacts déjà fixés, sans `∃ j` libre** : sous consécutivité stricte,
l'entrée de la seconde Tour authentique (`C⁺ = C*_{k₂+1}`, déjà fixée par la règle du pivot sur
`p_min(z*)`) dépasse STRICTEMENT l'occurrence du membre miroir (`Occ(z*) = p_min(z)`, par la chaîne
arithmétique), et son dernier rayon (`C⁻`) reste strictement sous `p_min(z*)` (containment de cellule,
théorème). Composition explicite, sans aucune hypothèse nouvelle au-delà de `hβ`/`hab` déjà requis par
la chaîne. -/
theorem secondTowerOwnContacts_meets_arithmeticChain {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (hab : PZeroMembersConsecutive z.1 (mirrorMember z).1) :
    (occurrence (mirrorMember z) : ℝ) < (secondTowerOf z).properState.entryContact ∧
      (secondTowerOf z).properState.lastRayContact < (expectedMinimumPrime (mirrorMember z) : ℝ) := by
  have hchain := consecutivePairArithmeticChain hβ hab
  have hcell := secondTower_cell_contains_own_expected z
  refine ⟨?_, hcell.1⟩
  have heq : occurrence (mirrorMember z) = expectedMinimumPrime z := hchain.2.1
  have hlt : expectedMinimumPrime z < expectedMinimumPrime (mirrorMember z) := hchain.2.2.2
  calc (occurrence (mirrorMember z) : ℝ) = (expectedMinimumPrime z : ℝ) := by rw [heq]
    _ < (expectedMinimumPrime (mirrorMember z) : ℝ) := by exact_mod_cast hlt
    _ ≤ (secondTowerOf z).properState.entryContact := hcell.2

/-! **Verdict honnête de la reformalisation** : cette composition, avec les deux contacts authentiques
et déjà fixés (pas un `∃ j` libre), ne produit `False` sous aucune hypothèse — elle produit une
inégalité stricte cohérente (`Occ(z*) < C⁺`), déjà compatible avec tout ce qui est documenté
(`secondTower_reads_occurrence_iff_coordinate_lt`). La seule question qui reste ouverte — `Occ(z*)`
face au dernier rayon `C⁻`, c'est-à-dire C_lecture — n'est tranchée par aucun théorème : elle est
data-dépendante (script réel `experiments/e085_same_height_two_towers_published.py`, critère (A) :
212/300 lecture (`reads`), 88/300 V (même anneau) — étiquettes réalignées sur le code le 2026-09-27,
E085 nommant « V » l'événement qui est la lecture compilée ; le chiffre « 204/298 » cité dans une version antérieure
de ce commentaire est RETIRÉ, introuvable dans tout le dépôt, non backé par un script ; voir `CLAUDE.md`
§4, bullet de rétractation, 2026-09-26). Reformaliser
avec le bon objet (les deux contacts fixés de la seconde Tour authentique) ne fait donc PAS apparaître
la contradiction que l'auteur demande : elle rend seulement explicite, une fois de plus, que la
question ouverte est C_lecture, pas un `∃ j` sur le mouvement réfléchi ni la containment de cellule
(qui, elle, ne peut jamais être en défaut : c'est une tautologie de construction du pivot). -/

end RHV6Fresh
