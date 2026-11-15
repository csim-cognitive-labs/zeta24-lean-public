/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Direct.PivotCell
import RHV6Fresh.Direct.InvertedCount
import RHV6Fresh.Tower.ReflectedMotion

/-!
# RHV6Fresh — les deux Tours de la paire hors ligne par la règle du pivot (douzième correction, 2026-09-23 ;
événement propre de la seconde Tour, 2026-09-25 ; contacts inversés par théorème de la réflexion `1 − ρ`,
`Tower/ReflectedMotion.lean`)

Niveau LECTURE ARITHMÉTIQUE.  Transcription de l'énoncé de l'auteur (2026-09-23) : les zéros hors ligne
sont régis EXACTEMENT comme les zéros sur la droite ; la règle du pivot établit la cellule de toute Tour ;
les règles de sélection des cellules sont les mêmes pour les deux Tours de la paire ; seule l'orientation
change pour la seconde Tour.  Énoncé de l'auteur (2026-09-25) : la seconde Tour est la Tour d'un AUTRE
zéro, son `β` change ; elle ne peut pas avoir le même événement que la première : l'événement avance
(`n(z*) = n(z) + 1` sous consécutivité, `mirror_sourceIndex_of_consecutive`), son occurrence est
`Occ(z*) = p_{n(z*)}` et son minimum attendu `p_min(z*) = p_{n(z*)+1}`.  Le « pivot commun `p_min(z)` »
de la seconde Tour (2026-09-24) est retiré : il donnait à la seconde Tour l'événement de la première et
aucun événement d'arrêt propre (l'anneau était choisi sur `p_min(z)` puis seulement renommé).

* `firstTowerOf z`  : la Tour de tout zéro par la règle du pivot sur son minimum attendu (plus aucune
  restriction `β = 1/2`) ; R₁ et C_lecture y sont des théorèmes, comme sur la droite.
* `secondTowerOf z` : la seconde Tour du membre miroir `z*` depuis son seul couple `(1 − β, T)`, même
  règle, SON pivot `p_min(z*)` (OFF comme ON), dans la seconde orientation (`InvertedTower`, entrée en
  haut, dernier rayon en bas : le zéro réfléchi `1 − ρ` parcourt l'anneau à rebours).  Son anneau est
  celui de la première Tour du même membre (`secondTower_ring_eq_mirror_firstTower`) ; les deux Tours
  du membre lisent le même anneau en sens opposés.
* Sur la seconde Tour, C_lecture (`Occ(z*)` atteinte au dernier rayon) est une LECTURE, pas un théorème :
  elle équivaut à « `Occ(z*)` et `p_min(z*)` dans des anneaux différents »
  (`secondTower_reads_occurrence_iff_coordinate_lt`) — c'est la comparaison honnête `k(z*, Occ(z*))` vs
  `k(z*, p_min(z*))`, ENTIÈREMENT interne à `z*`, jamais confrontée à une référence d'un autre zéro.

**Destruction (auteur, 2026-09-26)** : la notion « V » (dernier rayon de la seconde Tour comparé à
`p_min(z)`, référence d'un AUTRE zéro, via l'inversion d'une cellule fixe — `secondTower_verification_iff_sameRing`,
`secondTower_verification_imp_not_reads`, `secondTower_reads_iff_not_verification_of_consecutive`) est
retirée : ce n'était pas la bonne quantité, le recul du miroir s'étudie uniquement sur `z*` lui-même.
`Terminal/PairContradiction.lean` et `Terminal/TwoTowersComparison.lean` (qui l'instanciaient) sont
supprimés.

Aucun zéro hors ligne calculé ; aucune hypothèse ; RH n'apparaît pas.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. La paire strictement consécutive -/

/-- Paire strictement consécutive (énoncé de l'auteur) : l'indice du miroir suit celui du zéro. -/
theorem mirror_sourceIndex_of_consecutive {z : TrueZero}
    (hab : PZeroMembersConsecutive z.1 (mirrorMember z).1) :
    nZeroSourceIndex (mirrorMember z).1 = nZeroSourceIndex z.1 + 1 := by
  have h := progression_occurrence hab
  rw [occurrence_eq_primeAtRank] at h
  unfold expectedMinimumPrime fnPrimeSuccessor at h
  exact thm_primeAtRank_strictMono.injective h

/-! ## 2. La première Tour de tout zéro : règle du pivot, OFF comme ON -/

/-- La Tour portée de tout zéro, par la règle du pivot sur son minimum attendu (douzième correction :
la restriction `β = 1/2` de `lineTowerOf` est levée, les zéros hors ligne sont régis comme les zéros
sur la droite). -/
noncomputable def firstTowerOf (z : TrueZero) : TrueTower z :=
  { towerMotionOf z, pivotCell z with }

theorem firstTowerOf_properState (z : TrueZero) :
    (firstTowerOf z).properState = pivotCell z := rfl

theorem firstTowerOf_eq_lineTowerOf (z : TrueZero) (hβ : rZeroRadialPosition z.1 = 1 / 2) :
    firstTowerOf z = lineTowerOf z hβ := rfl

/-- R₁ : la première Tour atteint le minimum attendu de son zéro (théorème, par la règle). -/
theorem firstTower_reaches_expected (z : TrueZero) :
    reaches (firstTowerOf z).properState (expectedMinimumPrime z) :=
  pivotPair_reaches z (expectedMinimumPrime_pos z)

/-- C_lecture sur la première Tour : son occurrence est atteinte (théorème). -/
theorem firstTower_reaches_occurrence (z : TrueZero) :
    reaches (firstTowerOf z).properState (occurrence z) :=
  reaches_of_le _ (le_of_lt (occurrence_lt_expectedMinimumPrime z))
    (firstTower_reaches_expected z)

theorem firstTower_readings (z : TrueZero) :
    (firstTowerOf z).properState.entryCoordinate = pivotCoordinate z (expectedMinimumPrime z) ∧
      (firstTowerOf z).properState.stageCount = 1 :=
  ⟨pivotPair_entryCoordinate z _, pivotPair_stageCount z _⟩

/-! ### Rigidification : un zéro, une Tour, deux contacts uniques (auteur, objection E44/E071,
2026-09-26)

Généralisation, sans restriction `β = 1/2`, de `lineTower_cell_contains_expected` et de
`pivotCoordinate_unique`/`pivotCoordinate_isLeast` (`Direct/PivotCell.lean`) : pour TOUT zéro, la Tour
`firstTowerOf z` a exactement deux contacts `(C⁻, C⁺)`, contenant son minimum attendu, et AUCUNE autre
coordonnée `k` ne peut jouer ce rôle — `k` est calculé (`pivotCoordinate`), jamais choisi. C'est
l'invariant `z ↔ (C⁻, C⁺)` du maître mathématique, comme objet universel, ON et OFF alike, sans
changer la définition. -/

/-- **Les deux contacts de la Tour portée contiennent le pivot** (généralisation de
`lineTower_cell_contains_expected` à tout `β`) : `C⁻ < p_min(z) ≤ C⁺`. -/
theorem firstTower_cell_contains_expected (z : TrueZero) :
    (firstTowerOf z).entryContact < (expectedMinimumPrime z : ℝ) ∧
      (expectedMinimumPrime z : ℝ) ≤ (firstTowerOf z).lastRayContact :=
  ⟨entry_lt_pivot z (by exact_mod_cast expectedMinimumPrime_pos z),
    pivot_le_lastRay z (by exact_mod_cast expectedMinimumPrime_pos z)⟩

/-- **La paire de contacts est unique** (généralisation de `pivotCoordinate_unique` à tout `β`) :
toute coordonnée `k` dont la cellule `(C_k, C_{k+1}]` contient le pivot `p_min(z)` EST la coordonnée
d'entrée de `firstTowerOf z` — aucune autre paire de contacts, aucune re-sélection de cellule, aucun
`k` libre ne peut satisfaire le même rôle. -/
theorem firstTower_contactPair_unique (z : TrueZero) {k : ℤ}
    (hLow : contactMinusAt z k < (expectedMinimumPrime z : ℝ))
    (hHigh : (expectedMinimumPrime z : ℝ) ≤ contactPlusAt z k) :
    k = (firstTowerOf z).properState.entryCoordinate := by
  rw [(firstTower_readings z).1]
  exact pivotCoordinate_unique z (by exact_mod_cast expectedMinimumPrime_pos z) hLow hHigh

/-! ## 3. La seconde Tour de la paire : la Tour du membre miroir sur SON pivot, orientation opposée,
contacts inversés par théorème

Énoncé de l'auteur (2026-09-25) : la seconde Tour est la Tour du zéro miroir `z*`, un autre membre,
d'événement `n(z*) > n(z)` ; elle est régie comme toute Tour : règle du pivot sur son propre minimum
attendu `p_min(z*) = p_{n(z*)+1}`.  Elle est la Tour du zéro que l'équation fonctionnelle produit,
`1 − ρ = (1 − β, −T)` (`zetaFunctionalReflect`, `zeta_functionalReflect_zero`), conjugué du miroir
supérieur : ses formules tangentielles ont la phase `−φ*` et le pas `−π/T`, elle parcourt le même
anneau dans l'orientation opposée et ses contacts sont ceux du miroir supérieur avec les rôles échangés
(`Tower/ReflectedMotion.lean` : `reflectedIncidence_eq`, `reflected_step`, `invertedPairAt_eq_reflected`).
Le mouvement réfléchi n'a aucun événement d'arrêt depuis sa propre origine (`reflected_no_stop_event`) :
l'événement d'arrêt est celui du membre `z*` sur son pivot, l'orientation ne décide que des rôles.
Anneau `(C*_{k₂}, C*_{k₂+1}]` avec `k₂ = ⌈(T log p_min(z*) − φ*)/π⌉ − 1` ; entrée `C*_{k₂+1}` (au-dessus
du pivot), dernier rayon `C*_{k₂}` (strictement sous le pivot), par théorème. -/

/-- La seconde Tour du membre miroir depuis son seul couple `(1 − β, T)` : même règle du pivot, SON
pivot `p_min(z*)`, seconde orientation (entrée en haut, dernier rayon en bas). -/
noncomputable def secondTowerOf (z : TrueZero) : InvertedTower (mirrorMember z) :=
  { towerMotionOf (mirrorMember z),
    invertedPivotPair (mirrorMember z) (expectedMinimumPrime (mirrorMember z)) with }

theorem secondTowerOf_properState (z : TrueZero) :
    (secondTowerOf z).properState =
      invertedPivotPair (mirrorMember z) (expectedMinimumPrime (mirrorMember z)) := rfl

/-- **Un membre, un anneau, deux orientations** : l'anneau de la seconde Tour est celui de la première
Tour du même membre `z*` (même pivot `p_min(z*)`, même règle), lu à rebours. -/
theorem secondTower_ring_eq_mirror_firstTower (z : TrueZero) :
    (secondTowerOf z).properState.upright = (firstTowerOf (mirrorMember z)).properState := rfl

/-- L'entrée de la seconde Tour est le rayon du haut de l'anneau de son pivot : `C*_{k₂+1}`. -/
theorem secondTower_entry_eq_incidence (z : TrueZero) :
    (secondTowerOf z).entryContact =
      (towerMotionOf (mirrorMember z)).incidence
        (pivotCoordinate (mirrorMember z) (expectedMinimumPrime (mirrorMember z)) + 1) := rfl

/-- Le dernier rayon de la seconde Tour est le rayon du bas de l'anneau de son pivot : `C*_{k₂}`. -/
theorem secondTower_lastRay_eq_incidence (z : TrueZero) :
    (secondTowerOf z).lastRayContact =
      (towerMotionOf (mirrorMember z)).incidence
        (pivotCoordinate (mirrorMember z) (expectedMinimumPrime (mirrorMember z))) := rfl

/-- **L'inversion est un théorème** : l'entrée de la seconde Tour est l'entrée du zéro réfléchi `1 − ρ`
à sa propre coordonnée `−(k₂ + 1)`. -/
theorem secondTower_entry_eq_reflected (z : TrueZero) :
    (secondTowerOf z).entryContact =
      reflectedIncidence (mirrorMember z)
        (-(pivotCoordinate (mirrorMember z) (expectedMinimumPrime (mirrorMember z)) + 1)) := by
  rw [secondTower_entry_eq_incidence, reflectedIncidence_eq, neg_neg]

/-- **L'inversion est un théorème** : le dernier rayon de la seconde Tour est le rayon suivant du zéro
réfléchi dans SON sens de parcours, coordonnée `−(k₂ + 1) + 1`. -/
theorem secondTower_lastRay_eq_reflected (z : TrueZero) :
    (secondTowerOf z).lastRayContact =
      reflectedIncidence (mirrorMember z)
        (-(pivotCoordinate (mirrorMember z) (expectedMinimumPrime (mirrorMember z)) + 1) + 1) := by
  rw [secondTower_lastRay_eq_incidence, reflectedIncidence_eq]
  congr 1
  ring

theorem secondTower_readings (z : TrueZero) :
    (secondTowerOf z).properState.entryCoordinate =
        pivotCoordinate (mirrorMember z) (expectedMinimumPrime (mirrorMember z)) + 1 ∧
      (secondTowerOf z).properState.stageCount = 1 :=
  ⟨invertedPivotPair_entryCoordinate _ _, invertedPivotPair_stageCount _ _⟩

/-- **`secondTowerOf` n'est pas une re-sélection** : sa coordonnée est EXACTEMENT la coordonnée unique
et rigide (`firstTower_contactPair_unique`, §2) de la Tour du membre miroir sur SON pivot `p_min(z*)` —
aucun `k` libre, aucune troisième paire de contacts ; seule l'étiquette d'orientation (entrée/dernier
rayon) est échangée. Réponse littérale à l'objection E44/E071 : la rigidification de la Tour unique,
appliquée à `mirrorMember z`, EST déjà `secondTowerOf z` — elle ne l'exclut pas, elle le fonde. -/
theorem secondTower_coordinate_eq_unique_mirrorContactPair (z : TrueZero) :
    (secondTowerOf z).properState.entryCoordinate - 1 =
      (firstTowerOf (mirrorMember z)).properState.entryCoordinate := by
  rw [(secondTower_readings z).1, (firstTower_readings (mirrorMember z)).1]
  ring

/-! ## 4. L'événement propre de la seconde Tour : théorèmes sur son pivot `p_min(z*)` -/

/-- La seconde Tour atteint l'anneau de SON pivot `p_min(z*)` : dernier rayon strictement sous lui,
entrée au moins lui. -/
theorem secondTower_cell_contains_own_expected (z : TrueZero) :
    (secondTowerOf z).lastRayContact < (expectedMinimumPrime (mirrorMember z) : ℝ) ∧
      (expectedMinimumPrime (mirrorMember z) : ℝ) ≤ (secondTowerOf z).entryContact :=
  invertedPivotPair_cell_contains _
    (by exact_mod_cast (expectedMinimumPrime_prime (mirrorMember z)).pos)

/-- Dans la seconde orientation, le contact qui atteint le pivot propre est l'entrée. -/
theorem secondTower_entry_reaches_own_expected (z : TrueZero) :
    (expectedMinimumPrime (mirrorMember z) : ℝ) ≤ (secondTowerOf z).properState.entryContact :=
  (secondTower_cell_contains_own_expected z).2

/-- Le pivot propre n'est jamais compté au dernier rayon (rayon du bas). -/
theorem secondTower_not_reaches_own_expected (z : TrueZero) :
    ¬ (secondTowerOf z).properState.reaches (expectedMinimumPrime (mirrorMember z)) :=
  invertedPivotPair_not_reaches _ (expectedMinimumPrime_prime (mirrorMember z)).pos

/-- Le premier compté au dernier rayon de la seconde Tour est strictement sous son pivot propre. -/
theorem secondTower_counted_lt_own_expected (z : TrueZero) :
    (secondTowerOf z).properState.countedPrime < expectedMinimumPrime (mirrorMember z) := by
  have h := secondTower_not_reaches_own_expected z
  unfold expectedMinimumPrime fnPrimeSuccessor at h ⊢
  exact (secondTowerOf z).properState.countedPrime_lt_of_not_reaches_succ h

/-- L'entrée de la seconde Tour atteint l'occurrence du membre miroir (`Occ(z*) < p_min(z*) ≤ C⁻`),
théorème sans hypothèse : à l'entrée, le membre lit son occurrence. -/
theorem secondTower_entry_reaches_mirror_occurrence (z : TrueZero) :
    (occurrence (mirrorMember z) : ℝ) ≤ (secondTowerOf z).properState.entryContact :=
  le_trans (by exact_mod_cast le_of_lt (occurrence_lt_expectedMinimumPrime (mirrorMember z)))
    (secondTower_entry_reaches_own_expected z)

/-! ## 5. Les deux constats de la collision sur la seconde Tour : lectures, chacune équivalente à
une position dans les anneaux du membre miroir

Le dernier rayon de la seconde Tour est `C*_{k₂}`, rayon du bas de l'anneau de `p_min(z*)`.
V (`C*_{k₂} < p_min(z)`) tient exactement quand `p_min(z)` est dans ce même anneau ; C_lecture
(`Occ(z*) ≤ C*_{k₂}`) exactement quand `Occ(z*)` est dans un anneau strictement inférieur.  Hors ligne
`p_min(z) ≤ Occ(z*)` : les deux constats s'excluent. -/

/-- Hors ligne le minimum attendu de `z` est strictement sous celui du miroir. -/
theorem expectedMinimum_lt_mirror_expectedMinimum {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    expectedMinimumPrime z < expectedMinimumPrime (mirrorMember z) :=
  lt_of_le_of_lt (expectedMinimum_le_mirror_occurrence hβ)
    (occurrence_lt_expectedMinimumPrime (mirrorMember z))

/-! ### Le premier impose le contact (raccord causal)

Le minimum attendu n'est pas choisi après la cellule.  Pour un membre inférieur
`z`, la progression ordonnée impose déjà `p_min(z) ≤ Occ(z*)`.  Dès qu'un
contact authentique du miroir lit `Occ(z*)`, cette inégalité arithmétique se
transporte au contact lui-même.  C'est le sens causal requis par la chaîne :
le premier imposé produit une obligation sur le contact, et non l'inverse.
-/

/-- Une lecture authentique de l'occurrence du miroir impose la lecture du
minimum attendu du membre inférieur sur le même contact. -/
theorem expectedMinimum_le_lastRay_of_mirror_occurrence {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (S : AnalyticContactPair (mirrorMember z))
    (hRead : reaches S (occurrence (mirrorMember z))) :
    (expectedMinimumPrime z : ℝ) ≤ S.lastRayContact := by
  have hArith : expectedMinimumPrime z ≤ occurrence (mirrorMember z) :=
    expectedMinimum_le_mirror_occurrence hβ
  have hArithReal : (expectedMinimumPrime z : ℝ) ≤
      (occurrence (mirrorMember z) : ℝ) := by
    exact_mod_cast hArith
  exact le_trans hArithReal hRead

/-- Le déficit devant le minimum attendu du membre inférieur est incompatible
avec la lecture authentique de l'occurrence du miroir sur le même contact. -/
theorem mirror_occurrence_reading_contradicts_expected_deficit {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (S : AnalyticContactPair (mirrorMember z))
    (hRead : reaches S (occurrence (mirrorMember z)))
    (hDeficit : S.lastRayContact < (expectedMinimumPrime z : ℝ)) :
    False := by
  exact (not_lt_of_ge (expectedMinimum_le_lastRay_of_mirror_occurrence hβ S hRead)
    hDeficit)

/-- **C_lecture est une lecture** : l'occurrence du membre miroir est atteinte au dernier rayon de la
seconde Tour si et seulement si `Occ(z*)` tombe dans un anneau strictement sous celui de `p_min(z*)`. -/
theorem secondTower_reads_occurrence_iff_coordinate_lt (z : TrueZero) :
    (secondTowerOf z).properState.reaches (occurrence (mirrorMember z)) ↔
      pivotCoordinate (mirrorMember z) (occurrence (mirrorMember z)) <
        pivotCoordinate (mirrorMember z) (expectedMinimumPrime (mirrorMember z)) := by
  have hq : (0 : ℝ) < (occurrence (mirrorMember z) : ℝ) := by
    exact_mod_cast (occurrence_prime (mirrorMember z)).pos
  show (occurrence (mirrorMember z) : ℝ) ≤
    contactMinusAt (mirrorMember z)
      (pivotCoordinate (mirrorMember z) (expectedMinimumPrime (mirrorMember z))) ↔ _
  constructor
  · intro h
    have h' : (occurrence (mirrorMember z) : ℝ) ≤ contactPlusAt (mirrorMember z)
        (pivotCoordinate (mirrorMember z) (expectedMinimumPrime (mirrorMember z)) - 1) := by
      unfold contactPlusAt
      unfold contactMinusAt at h
      simpa using h
    have := pivotCoordinate_le_of_le_contactPlus (mirrorMember z) hq h'
    omega
  · intro h
    have h1 := pivot_le_contactPlus_pivotCoordinate (mirrorMember z) hq
    unfold contactPlusAt at h1
    unfold contactMinusAt
    exact le_trans h1 (towerMotion_incidence_mono (mirrorMember z) (by omega))

/-! ### Le constat de vérification V, réinstauré littéralement (maître sémantique, texte remis par
l'auteur, 2026-09-26)

Le maître (§9, tel que remis) nomme deux constats distincts sur le dernier rayon de la seconde Tour :
« le constat de lecture » (`secondTower_reads_occurrence_iff_coordinate_lt`, ci-dessus) et « le constat
de vérification » — le dernier rayon `C⁻` est-il SOUS le minimum attendu `p_min(z)` du zéro ORIGINAL
(pas `p_min(z*)`) ? C'est exactement la quantité « V » retirée le 2026-09-26 pour ne jamais être
confrontée « à une référence d'un autre zéro » — mais le maître remis ici en fait explicitement le
second des deux constats de la collision de sa section 9. Elle est réinstaurée ici littéralement,
sous consécutivité stricte (seul cas où `p_min(z) = Occ(z*)` exactement, `progression_occurrence`),
et SEULEMENT comme ce qu'elle est : la négation exacte du constat de lecture — jamais comme fermeture. -/

/-- **Le constat de vérification** (maître §9) : le dernier rayon de la seconde Tour est sous le
minimum attendu du zéro ORIGINAL. Sous consécutivité stricte, `p_min(z) = Occ(z*)` exactement
(`expectedMinimum_eq_mirror_occurrence_of_consecutive`), donc ce constat est LA NÉGATION EXACTE du
constat de lecture — pas une information supplémentaire, une tautologie de l'ordre total sur `ℝ`. Le
maître le nomme lui-même « théorème, et c'est la collision » : c'est un théorème, mais c'est
l'exclusion de deux constats définis l'un comme négation de l'autre, jamais une preuve que l'un des
deux est réalisé sans condition. -/
theorem secondTower_verification_iff_not_reads_of_consecutive {z : TrueZero}
    (hab : PZeroMembersConsecutive z.1 (mirrorMember z).1) :
    (secondTowerOf z).properState.lastRayContact < (expectedMinimumPrime z : ℝ) ↔
      ¬ (secondTowerOf z).properState.reaches (occurrence (mirrorMember z)) := by
  rw [expectedMinimum_eq_mirror_occurrence_of_consecutive hab]
  exact ((secondTowerOf z).properState.not_reaches_iff (occurrence (mirrorMember z))).symm

/-! **RÉTRACTATION (auteur, 2026-09-26) : le chiffre « 204/298 / 94/298 » cité ci-dessus dans une
version antérieure de ce commentaire n'existe dans AUCUN script du dépôt** — `grep` sur tout le dépôt
ne trouve ce chiffre que dans ce commentaire et dans `CLAUDE.md`, jamais dans une sortie de script. Il
ne correspond pas non plus au script le plus proche réellement exécuté (`experiments/e085_same_height_two_towers_published.py`,
sortie `e085_same_height_two_towers_published_output.md`) : celui-ci mesure EXACTEMENT le même critère
((A), « V faux ⇔ précédent et minimum dans le même anneau », tautologie vérifiée 300/300) et donne
**212/300** pour ce qu'E085 nomme « V » (`VA = cpA < pmin` : `C⁺` de la cellule de `Occ` sur la grille
de `z*` sous `p_min`), qui est exactement la LECTURE compilée (`reads`, `coordinate_lt`, ci-dessous),
donc **88/300** pour la V compilée (`secondTower_verification_iff_not_reads_of_consecutive`, même
anneau) — étiquettes réalignées sur le code le 2026-09-27 (une version antérieure recopiait
l'étiquette d'E085 à l'envers). Identique aux trois β testés 0,4/0,6/0,8 et, recalculé directement,
pour tout β de 0,4 à 0,01 : le verdict de (A) ne dépend, sur ces 300 hauteurs, que de `T` et de la
position des deux premiers dans les anneaux (la condition suffisante `secondTower_reads_of_gap_ge_pi`
est aveugle à `β` par théorème ; la condition exacte ne l'est que par l'arrondi commun de phase). Le
chiffre « 204/298 » est donc RETIRÉ comme non vérifié : soit une erreur de calcul jamais journalisée,
soit une confusion — dans les deux cas une violation de la discipline numérique (`CLAUDE.md` §5) que
l'auteur a eu raison de suspecter. **Deuxième point, plus important, que l'auteur souligne** : E085
n'utilise PAS de vrais zéros hors ligne — aucun n'est connu, l'existence même d'un zéro hors ligne
étant justement ce que RH nie. E085 évalue les formules exactes du maître mathématique à un `β`
SYNTHÉTIQUE (0,4 / 0,6 / 0,8, choisi par l'auteur) À LA HAUTEUR `T` d'un vrai zéro publié d'Odlyzko —
jamais un couple `(β, T)` présenté comme un zéro réel. Aucune expérience numérique de ce dépôt ne peut
être un test sur « deux Tours OFF avec de vrais zéros » : la seule vérité numérique disponible est
celle des zéros SUR la droite (E075–E086) ; toute mesure côté `β ≠ 1/2` est nécessairement une formule
évaluée, jamais un zéro. Conclusion honnête, revue : ni V ni le constat de lecture n'est forcé sans
condition (ceci reste vrai, 212/300 ≠ 300/300 et ≠ 0/300 le confirme) — mais le chiffre exact cité
doit être 212/300 (E085, script réel, vérifiable), jamais 204/298. -/

/-- Forme comptée, sur tout état inversé : « le minimum est au moins le premier suivant celui compté »
équivaut à « le premier compté est strictement sous ce minimum ». -/
theorem authorForm_iff_counted_lt {z : TrueZero} (S' : InvertedContactPair (mirrorMember z)) :
    fnPrimeAtRank S'.countedRank ≤ expectedMinimumPrime z ↔
      S'.countedPrime < expectedMinimumPrime z := by
  unfold InvertedContactPair.countedPrime expectedMinimumPrime fnPrimeSuccessor
  rw [thm_primeAtRank_strictMono.le_iff_le, thm_primeAtRank_strictMono.lt_iff_lt]
  omega

/-! ## 6. Le membre miroir hors ligne : membre authentique, distinct, et ses deux Tours
(maîtres finaux §6, §7, §8, énoncés de l'auteur 2026-09-24 et 2026-09-25)

Le miroir d'un zéro hors ligne est un membre de la suite des zéros (`mirrorMember z : TrueZero`),
distinct du zéro original, placé strictement après lui, d'occurrence au moins le minimum attendu.
Il possède deux Tours sur le même anneau (pivot `p_min(z*)`) : sa première Tour (orientation croissante,
dernier rayon en haut) lit son occurrence par théorème ; sa seconde Tour (zéro réfléchi, dernier rayon
en bas) la lit exactement quand `Occ(z*)` est dans un anneau strictement inférieur. -/

/-- Le membre miroir d'un zéro hors ligne est distinct du zéro original. -/
theorem mirrorMember_ne {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    mirrorMember z ≠ z := by
  intro h
  have hr := mirrorMember_radial z
  rw [h] at hr
  linarith

/-- **Membre authentique et distinct** : le miroir hors ligne est un vrai zéro (par son type),
distinct de `z`, strictement postérieur dans l'ordre des zéros, d'index zéro-source strictement plus
grand, et son occurrence est au moins le minimum attendu de `z`. -/
theorem mirrorMember_distinct_member {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    mirrorMember z ≠ z ∧ PZeroMemberPrecedes z.1 (mirrorMember z).1 ∧
      nZeroSourceIndex z.1 < nZeroSourceIndex (mirrorMember z).1 ∧
      expectedMinimumPrime z ≤ occurrence (mirrorMember z) :=
  ⟨mirrorMember_ne hβ, mirror_precedes hβ, sourceIndex_lt_mirror hβ,
    expectedMinimum_le_mirror_occurrence hβ⟩

/-- **La liaison portée par la première Tour du membre miroir** : elle lit l'histoire première jusqu'à
son occurrence (instance de `firstTower_reaches_occurrence`). -/
theorem mirrorMember_firstTower_reaches_occurrence (z : TrueZero) :
    reaches (firstTowerOf (mirrorMember z)).properState (occurrence (mirrorMember z)) :=
  firstTower_reaches_occurrence _

/-- **Les deux Tours du membre miroir lisent le même anneau en sens opposés** : la première lit son
occurrence (théorème, rayon du haut) ; la seconde la lit au rayon du bas exactement quand `Occ(z*)`
est dans un anneau strictement sous celui de `p_min(z*)`. -/
theorem mirror_two_towers_same_ring (z : TrueZero) :
    reaches (firstTowerOf (mirrorMember z)).properState (occurrence (mirrorMember z)) ∧
      ((secondTowerOf z).properState.reaches (occurrence (mirrorMember z)) ↔
        pivotCoordinate (mirrorMember z) (occurrence (mirrorMember z)) <
          pivotCoordinate (mirrorMember z) (expectedMinimumPrime (mirrorMember z))) :=
  ⟨mirrorMember_firstTower_reaches_occurrence z, secondTower_reads_occurrence_iff_coordinate_lt z⟩

end RHV6Fresh
