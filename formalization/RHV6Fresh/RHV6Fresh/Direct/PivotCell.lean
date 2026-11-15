/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Direct.Reached
import RHV6Fresh.Direct.Raccords
import RHV6Fresh.Tower.CanonicalOrigin

/-!
# RHV6Fresh — la règle du pivot : définition de la cellule de toute Tour (maîtres finaux 2026-09-23, §5)

Niveau LECTURE ARITHMÉTIQUE.  Transcription du maître sémantique final §5, du maître mathématique
final §5.c et du maître Lean final §5 : la référence (le pivot, fixé par la progression première
avant toute Tour) entre dans l'**événement d'arrêt** de la Tour, jamais comme cellule choisie ni
comme formule arbitraire de la coordonnée.

**La règle.** Le parcours de la Tour part de l'origine canonique `C₀` (`Tower/CanonicalOrigin.lean`),
avance d'un demi-tour à chaque croisement, et s'arrête au **premier** croisement dont le croisement
suivant atteint le pivot `q` : `C_k < q ≤ C_{k+1}`, soit `k = ⌈(T log q − φ)/π⌉ − 1`
(`pivotCoordinate`, unicité `pivotCoordinate_unique`, minimalité `pivotCoordinate_isLeast`) ; la cellule
est `(C_k, C_{k+1}]` (`pivotPair`), `k` est lu (`pivotPair_entryCoordinate`), `m = 1`
(`pivotPair_stageCount`).

**Les deux informations.** La référence (pivot, avant la Tour) et la cible constatée `countedPrime`
(dernier premier `≤ C⁺`, lue après) : `pivot ≤ cible` (`pivot_le_counted`), bond en avant possible,
aucune circularité ; la règle est aveugle au premier de la cellule (`pivotCoordinate_eq_of_same_cell`).

**Périmètre de ce module.** `lineTowerOf z hβ : TrueTower z` est la Tour portée d'un zéro sur la
droite critique (pivot = minimum attendu `p_min(z)`).  Les deux Tours de la paire hors ligne sont
produites par la même règle dans `Direct/PairTowers.lean` (`firstTowerOf z`, toute `β`, pivot
`p_min(z)` ; `secondTowerOf z`, Tour du membre miroir sur SON pivot `p_min(z*)`, orientation opposée :
entrée au-dessus du pivot, dernier rayon strictement sous lui, par théorème de la réflexion `1 − ρ`).
Les énoncés de la section 6 sont des faits de l'orientation croissante (maître Lean final §5) : la
première Tour du miroir atteint `p_min(z)` au dernier rayon ; la seconde Tour lit le même anneau à
rebours, et V y est une lecture.  Rien ici ne dépend de l'hypothèse de Riemann.

Vérification sur zéros publiés d'Odlyzko (jamais une preuve) : k_hist 15/15, cellule contenant
`p_min` 300/300.  Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Le minimum attendu : établi sans la Tour (section 7) -/

theorem expectedMinimumPrime_pos (z : TrueZero) : 0 < expectedMinimumPrime z :=
  (expectedMinimumPrime_prime z).pos

/-! ## 2. La règle du pivot : `k` est calculé depuis la référence, jamais choisi -/

/-- Position d'un réel `q > 0` dans la Tour de `z` : `(T log q − φ)/π`, nombre réel de demi-tours
depuis l'origine canonique `C_0`. -/
noncomputable def towerPosition (z : TrueZero) (q : ℝ) : ℝ :=
  (rZeroHeight z.1 * Real.log q - (towerMotionOf z).phase) / Real.pi

/-- Règle du pivot : `k = ⌈(T log q − φ)/π⌉ − 1`, l'unique `k` tel que `C_k < q ≤ C_{k+1}`. -/
noncomputable def pivotCoordinate (z : TrueZero) (q : ℝ) : ℤ :=
  ⌈towerPosition z q⌉ - 1

/-- La paire de rayons `(C_k, C_{k+1})` à `k = pivotCoordinate z q`. -/
noncomputable def pivotPair (z : TrueZero) (q : ℝ) : AnalyticContactPair z :=
  analyticPairAt z (pivotCoordinate z q)

theorem pivotPair_entryContact (z : TrueZero) (q : ℝ) :
    (pivotPair z q).entryContact =
      Real.exp (((towerMotionOf z).phase + ((pivotCoordinate z q : ℤ) : ℝ) * Real.pi) /
        rZeroHeight z.1) := by
  unfold pivotPair
  rw [analyticPairAt_entryContact]
  unfold contactMinusAt
  rw [towerMotion_incidence]

theorem pivotPair_lastRayContact (z : TrueZero) (q : ℝ) :
    (pivotPair z q).lastRayContact =
      Real.exp (((towerMotionOf z).phase + ((pivotCoordinate z q + 1 : ℤ) : ℝ) * Real.pi) /
        rZeroHeight z.1) := by
  unfold pivotPair
  rw [analyticPairAt_lastRayContact]
  unfold contactPlusAt
  rw [towerMotion_incidence]

/-- **`k` n'est pas choisi** : si une coordonnée `k` vérifie `C_k < q ≤ C_{k+1}`, alors
`k = ⌈(T log q − φ)/π⌉ − 1`. -/
theorem pivotCoordinate_unique (z : TrueZero) {q : ℝ} (hq : 0 < q) {k : ℤ}
    (hLow : contactMinusAt z k < q) (hHigh : q ≤ contactPlusAt z k) :
    k = pivotCoordinate z q := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hπ : 0 < Real.pi := Real.pi_pos
  unfold contactMinusAt at hLow
  unfold contactPlusAt at hHigh
  rw [towerMotion_incidence] at hLow hHigh
  rw [← Real.exp_log hq] at hLow hHigh
  have h1 := Real.exp_lt_exp.mp hLow
  have h2 := Real.exp_le_exp.mp hHigh
  rw [div_lt_iff₀ hT] at h1
  rw [le_div_iff₀ hT] at h2
  have hc : (k : ℝ) < towerPosition z q ∧ towerPosition z q ≤ (k : ℝ) + 1 := by
    unfold towerPosition
    constructor
    · rw [lt_div_iff₀ hπ]; push_cast at h1 h2; nlinarith
    · rw [div_le_iff₀ hπ]; push_cast at h1 h2; nlinarith
  unfold pivotCoordinate
  have hceil : ⌈towerPosition z q⌉ = k + 1 := by
    rw [Int.ceil_eq_iff]
    push_cast
    exact ⟨by linarith [hc.1], hc.2⟩
  omega

/-- La lecture `k = (T log C⁻ − φ)/π` de la paire du pivot rend la coordonnée calculée :
règle et lecture coïncident. -/
theorem pivotPair_entryReading (z : TrueZero) (q : ℝ) :
    (pivotPair z q).entryReading = ((pivotCoordinate z q : ℤ) : ℝ) := by
  unfold AnalyticContactPair.entryReading
  rw [pivotPair_entryContact, Real.log_exp]
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hPhase : rTowerPhase z = (towerMotionOf z).phase := by
    rw [towerMotion_phase]; rfl
  rw [hPhase]
  field_simp
  ring

/-- La coordonnée lue sur la paire du pivot est la coordonnée calculée. -/
theorem pivotPair_entryCoordinate (z : TrueZero) (q : ℝ) :
    (pivotPair z q).entryCoordinate = pivotCoordinate z q := by
  have h := (pivotPair z q).entryCoordinate_cast
  rw [pivotPair_entryReading] at h
  exact_mod_cast h.symm

/-- Le nombre d'étages lu sur la paire du pivot vaut un : entrée et dernier rayon sont deux
croisements consécutifs. -/
theorem pivotPair_stageReading (z : TrueZero) (q : ℝ) :
    (pivotPair z q).stageReading = 1 := by
  unfold AnalyticContactPair.stageReading rTowerDensity rTowerHeight
    AnalyticContactPair.logDiameter
  unfold pivotPair
  rw [analyticPairAt_lastRayContact, analyticPairAt_entryContact, contactAt_consecutive_logWidth]
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

theorem pivotPair_stageCount (z : TrueZero) (q : ℝ) :
    (pivotPair z q).stageCount = 1 := by
  have h := (pivotPair z q).stageCount_cast
  rw [pivotPair_stageReading] at h
  exact_mod_cast h.symm

/-! ## 3. La règle place la référence dans la cellule : `C_k < q ≤ C_{k+1}` -/

theorem entry_lt_pivot (z : TrueZero) {q : ℝ} (hq : 0 < q) :
    (pivotPair z q).entryContact < q := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hπ : 0 < Real.pi := Real.pi_pos
  rw [pivotPair_entryContact]
  have hceil : (⌈towerPosition z q⌉ : ℝ) < towerPosition z q + 1 := Int.ceil_lt_add_one _
  have hk : ((pivotCoordinate z q : ℤ) : ℝ) < towerPosition z q := by
    unfold pivotCoordinate; push_cast; linarith
  unfold towerPosition at hk
  rw [lt_div_iff₀ hπ] at hk
  calc Real.exp (((towerMotionOf z).phase + ((pivotCoordinate z q : ℤ) : ℝ) * Real.pi) /
          rZeroHeight z.1)
      < Real.exp (Real.log q) := by
        apply Real.exp_lt_exp.mpr
        rw [div_lt_iff₀ hT]
        nlinarith
    _ = q := Real.exp_log hq

theorem pivot_le_lastRay (z : TrueZero) {q : ℝ} (hq : 0 < q) :
    q ≤ (pivotPair z q).lastRayContact := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hπ : 0 < Real.pi := Real.pi_pos
  rw [pivotPair_lastRayContact]
  have hceil : towerPosition z q ≤ (⌈towerPosition z q⌉ : ℝ) := Int.le_ceil _
  have hk : towerPosition z q ≤ ((pivotCoordinate z q + 1 : ℤ) : ℝ) := by
    unfold pivotCoordinate; push_cast; linarith
  unfold towerPosition at hk
  rw [div_le_iff₀ hπ] at hk
  calc q = Real.exp (Real.log q) := (Real.exp_log hq).symm
    _ ≤ Real.exp (((towerMotionOf z).phase + ((pivotCoordinate z q + 1 : ℤ) : ℝ) * Real.pi) /
          rZeroHeight z.1) := by
        apply Real.exp_le_exp.mpr
        rw [le_div_iff₀ hT]
        nlinarith

/-- La référence est **atteinte** par la cellule qu'elle arrête (lecture « atteint » = `p ≤ C⁺`). -/
theorem pivotPair_reaches (z : TrueZero) {p : ℕ} (hp : 0 < p) :
    reaches (pivotPair z p) p :=
  pivot_le_lastRay z (by exact_mod_cast hp)

/-- Tout premier au plus égal à la référence est atteint par la cellule de la référence. -/
theorem pivotPair_reaches_of_le (z : TrueZero) {p q : ℕ} (hpq : p ≤ q) (hq : 0 < q) :
    reaches (pivotPair z q) p :=
  reaches_of_le _ hpq (pivotPair_reaches z hq)

/-- La règle est aveugle au premier choisi dans la cellule : deux références de la même cellule
`(C_k, C_{k+1}]` donnent la même coordonnée. -/
theorem pivotCoordinate_eq_of_same_cell (z : TrueZero) {q q' : ℝ} (hq : 0 < q) (hq' : 0 < q')
    {k : ℤ} (h1 : contactMinusAt z k < q) (h2 : q ≤ contactPlusAt z k)
    (h1' : contactMinusAt z k < q') (h2' : q' ≤ contactPlusAt z k) :
    pivotCoordinate z q = pivotCoordinate z q' :=
  (pivotCoordinate_unique z hq h1 h2).symm.trans (pivotCoordinate_unique z hq' h1' h2')

/-! ## 3 bis. L'événement d'arrêt : le PREMIER croisement dont le suivant atteint la référence -/

/-- Toute coordonnée dont le croisement suivant atteint `q` est au moins la coordonnée du pivot : la
règle s'arrête au premier anneau qui atteint la référence, jamais plus loin. -/
theorem pivotCoordinate_le_of_le_contactPlus (z : TrueZero) {q : ℝ} (hq : 0 < q) {k : ℤ}
    (h : q ≤ contactPlusAt z k) : pivotCoordinate z q ≤ k := by
  by_contra hlt
  have hle : k + 1 ≤ pivotCoordinate z q := by omega
  have h1 : contactPlusAt z k ≤ (pivotPair z q).entryContact := by
    unfold pivotPair
    rw [analyticPairAt_entryContact]
    unfold contactPlusAt contactMinusAt
    exact towerMotion_incidence_mono z hle
  linarith [entry_lt_pivot z hq]

/-- La référence est atteinte au croisement suivant la coordonnée du pivot. -/
theorem pivot_le_contactPlus_pivotCoordinate (z : TrueZero) {q : ℝ} (hq : 0 < q) :
    q ≤ contactPlusAt z (pivotCoordinate z q) := by
  have h := pivot_le_lastRay z hq
  unfold pivotPair at h
  rwa [analyticPairAt_lastRayContact] at h

/-- **Événement d'arrêt** : `pivotCoordinate z q` est le plus petit `k` tel que `q ≤ C_{k+1}`. -/
theorem pivotCoordinate_isLeast (z : TrueZero) {q : ℝ} (hq : 0 < q) :
    IsLeast {k : ℤ | q ≤ contactPlusAt z k} (pivotCoordinate z q) :=
  ⟨pivot_le_contactPlus_pivotCoordinate z hq,
    fun _ hk => pivotCoordinate_le_of_le_contactPlus z hq hk⟩

/-- Le parcours part de l'origine canonique : la référence est devant l'origine exactement quand la
coordonnée d'arrêt est au moins `0` (le parcours s'arrête à `C₀` ou après). -/
theorem canonicalOrigin_lt_iff_zero_le_pivotCoordinate (z : TrueZero) {q : ℝ} (hq : 0 < q) :
    canonicalOrigin z < q ↔ 0 ≤ pivotCoordinate z q := by
  constructor
  · intro h
    have h2 : canonicalOrigin z < contactPlusAt z (pivotCoordinate z q) :=
      lt_of_lt_of_le h (pivot_le_contactPlus_pivotCoordinate z hq)
    unfold canonicalOrigin contactPlusAt at h2
    have h3 := (towerMotion_incidence_lt_iff z _ _).mp h2
    omega
  · intro h
    have h1 : canonicalOrigin z ≤ (pivotPair z q).entryContact := by
      unfold canonicalOrigin pivotPair
      rw [analyticPairAt_entryContact]
      unfold contactMinusAt
      exact towerMotion_incidence_mono z h
    linarith [entry_lt_pivot z hq]

/-! ## 4. Les deux informations : la référence et la cible constatée au dernier rayon -/

/-- Le compte au dernier rayon de la cellule d'une référence première est positif. -/
theorem pivot_countedRank_pos (z : TrueZero) {q : ℕ} (hq : Nat.Prime q) :
    0 < countedRank (pivotPair z q) := by
  have h := (reaches_primeAtRank_iff (pivotPair z q) (Nat.count Nat.Prime q)).mp
    (by rw [thm_primeAtRank_surjective_onPrimes hq]; exact pivotPair_reaches z hq.pos)
  omega

/-- **Deux informations** : la cible constatée (dernier premier `≤ C⁺`) est au moins la référence ;
elle peut la dépasser (bond en avant), jamais régresser sous elle. -/
theorem pivot_le_counted (z : TrueZero) {q : ℕ} (hq : Nat.Prime q) :
    q ≤ countedPrime (pivotPair z q) :=
  (reaches_iff_le_countedPrime _ hq (pivot_countedRank_pos z hq)).mp (pivotPair_reaches z hq.pos)

/-- R₁ en forme comptée sur toute paire : le minimum est atteint ssi il ne dépasse pas la cible. -/
theorem R1_iff_expected_le_counted (z : TrueZero) (S : AnalyticContactPair z)
    (hPos : 0 < countedRank S) :
    reaches S (expectedMinimumPrime z) ↔ expectedMinimumPrime z ≤ countedPrime S :=
  reaches_iff_le_countedPrime S (expectedMinimumPrime_prime z) hPos

/-! ## 5. La Tour portée d'un zéro sur la droite critique (pivot = minimum attendu) -/

/-- La cellule d'un zéro par la règle du pivot, référence = son minimum attendu `p_{n(z)+1}`. -/
noncomputable def pivotCell (z : TrueZero) : AnalyticContactPair z :=
  pivotPair z (expectedMinimumPrime z)

/-- **La Tour portée d'un zéro sur la droite critique** : mouvement de `z`, entrée et dernier rayon
donnés par la règle du pivot.  Pour tout zéro, sur ou hors ligne, la même règle donne `firstTowerOf z`
(`Direct/PairTowers.lean`, `firstTowerOf_eq_lineTowerOf`). -/
noncomputable def lineTowerOf (z : TrueZero) (_hβ : rZeroRadialPosition z.1 = 1 / 2) :
    TrueTower z :=
  { towerMotionOf z, pivotCell z with }

theorem lineTowerOf_properState (z : TrueZero) (hβ : rZeroRadialPosition z.1 = 1 / 2) :
    (lineTowerOf z hβ).properState = pivotCell z := rfl

/-- R₁ sur la droite : le minimum attendu est atteint à l'état porté (par construction de la règle). -/
theorem lineTower_reaches_expected (z : TrueZero) (hβ : rZeroRadialPosition z.1 = 1 / 2) :
    reaches (lineTowerOf z hβ).properState (expectedMinimumPrime z) :=
  pivotPair_reaches z (expectedMinimumPrime_pos z)

/-- C_lecture sur la droite : l'occurrence est atteinte (`Occ(z) < p_min(z)`). -/
theorem lineTower_reaches_occurrence (z : TrueZero) (hβ : rZeroRadialPosition z.1 = 1 / 2) :
    reaches (lineTowerOf z hβ).properState (occurrence z) :=
  reaches_of_le _ (le_of_lt (occurrence_lt_expectedMinimumPrime z))
    (lineTower_reaches_expected z hβ)

/-- Le minimum attendu est dans la cellule : `C⁻ < p_min(z) ≤ C⁺`. -/
theorem lineTower_cell_contains_expected (z : TrueZero) (hβ : rZeroRadialPosition z.1 = 1 / 2) :
    (lineTowerOf z hβ).entryContact < (expectedMinimumPrime z : ℝ) ∧
      (expectedMinimumPrime z : ℝ) ≤ (lineTowerOf z hβ).lastRayContact :=
  ⟨entry_lt_pivot z (by exact_mod_cast expectedMinimumPrime_pos z),
    pivot_le_lastRay z (by exact_mod_cast expectedMinimumPrime_pos z)⟩

/-- Les lectures sur la Tour de la droite : `k = ⌈(T log p_min − φ)/π⌉ − 1` (demi-tours depuis
l'origine), `m = 1`. -/
theorem lineTower_readings (z : TrueZero) (hβ : rZeroRadialPosition z.1 = 1 / 2) :
    (lineTowerOf z hβ).properState.entryCoordinate = pivotCoordinate z (expectedMinimumPrime z) ∧
      (lineTowerOf z hβ).properState.stageCount = 1 :=
  ⟨pivotPair_entryCoordinate z _, pivotPair_stageCount z _⟩

/-- La cible constatée sur la droite est au moins le minimum attendu (les deux informations). -/
theorem lineTower_expected_le_counted (z : TrueZero) (hβ : rZeroRadialPosition z.1 = 1 / 2) :
    expectedMinimumPrime z ≤ countedPrime (lineTowerOf z hβ).properState :=
  pivot_le_counted z (expectedMinimumPrime_prime z)

/-! ## 6. Contrôles d'implémentation (maître Lean final §5) : jamais un fait sur la seconde Tour

Appliquée au miroir `z*` dans l'orientation **croissante** avec toute référence `q ≥ p_min(z)` (en
particulier `p_min(z*)` ou `p_min(z)`), la règle donne `p_min(z)` atteint au dernier rayon (rayon du
haut).  La seconde Tour est la Tour du zéro réfléchi `1 − ρ` sur le même anneau (pivot `p_min(z*)`),
orientation opposée, dernier rayon = rayon du bas (`Direct/PairTowers.lean`) : V y est une lecture,
équivalente à « `p_min(z)` dans l'anneau de `p_min(z*)` ».  V exige `cible(z*) < p_min(z) ≤ Occ(z*)`.
Ces faits ne supposent rien d'autre que `β < 1/2` et un compte positif. -/

/-- Toute référence `q ≥ p_min(z)` à la Tour du miroir donne `p_min(z)` atteint. -/
theorem pivotPair_mirror_reaches_of_ge (z : TrueZero) {q : ℕ}
    (hq : expectedMinimumPrime z ≤ q) :
    reaches (pivotPair (mirrorMember z) q) (expectedMinimumPrime z) :=
  pivotPair_reaches_of_le _ hq (lt_of_lt_of_le (expectedMinimumPrime_pos z) hq)

/-- La règle avec la propre référence du miroir nie V : `p_min(z) ≤ Occ(z*) < p_min(z*) ≤ C⁺`. -/
theorem pivotCell_mirror_reaches_expected {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    reaches (pivotCell (mirrorMember z)) (expectedMinimumPrime z) :=
  pivotPair_mirror_reaches_of_ge z
    (le_trans (expectedMinimum_le_mirror_occurrence hβ)
      (le_of_lt (occurrence_lt_expectedMinimumPrime (mirrorMember z))))

/-- V force la référence du miroir strictement sous `p_min(z)`. -/
theorem lock_imp_pivot_lt_expected (z : TrueZero) {q : ℕ}
    (hV : ¬ reaches (pivotPair (mirrorMember z) q) (expectedMinimumPrime z)) :
    q < expectedMinimumPrime z := by
  by_contra h
  exact hV (pivotPair_mirror_reaches_of_ge z (not_lt.mp h))

/-- V force la cible constatée du miroir strictement sous l'occurrence du miroir. -/
theorem lock_imp_counted_lt_occurrence {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (S : AnalyticContactPair (mirrorMember z)) (hPos : 0 < countedRank S)
    (hV : ¬ reaches S (expectedMinimumPrime z)) :
    countedPrime S < occurrence (mirrorMember z) := by
  have h1 : ¬ expectedMinimumPrime z ≤ countedPrime S := by
    rwa [← reaches_iff_le_countedPrime S (expectedMinimumPrime_prime z) hPos]
  have h2 := expectedMinimum_le_mirror_occurrence hβ
  omega

/-! ## 5. Grilles alignées à même hauteur (auteur, 2026-09-27, « qu'est-ce qui oblige à quitter la
trajectoire de `z_n` au dernier rayon et à passer à la Tour de `z_{n+1}` ? »)

Réponse testée ici, sans restructuration de grammaire : deux Tours de MÊME hauteur `T` ont le MÊME
pas `π/T` (`contactAt_consecutive_logWidth`), donc la même grille en échelle log, décalée seulement
par la différence de phase `φ(z) − φ(w)`.  Comme la phase de toute Tour est dans `(0, π/2)`
(`towerMotion_phase_pos`, `towerMotion_phase_lt_pi_div_two`), ce décalage, DIVISÉ par `π`, est
toujours strictement dans `(−1/2, 1/2)` — donc la coordonnée de pivot d'un MÊME réel `q` dans les
deux grilles ne peut jamais différer de plus de UN cran.  Autrement dit : à hauteur égale, il n'y a
JAMAIS de raison géométrique de s'écarter de plus d'un anneau en passant d'une Tour à l'autre — le
saut « n → n+1 » de la grammaire arithmétique n'a, à `T` constant, presque aucune justification
géométrique. Ceci ne produit PAS de contradiction avec les faits déjà établis (l'écart ≤ 1 reste
cohérent avec tout ce qui est prouvé) ; ceci quantifie précisément, pour la première fois, à quel
point une paire hors ligne (même `T`) est géométriquement presque interchangeable. -/

/-- Le décalage de phase entre deux Tours, divisé par `π`, est strictement borné par `1/2`. -/
theorem towerPosition_shift_abs_lt_half (z w : TrueZero) :
    |((towerMotionOf z).phase - (towerMotionOf w).phase) / Real.pi| < 1 / 2 := by
  have hz1 := towerMotion_phase_pos z
  have hz2 := towerMotion_phase_lt_pi_div_two z
  have hw1 := towerMotion_phase_pos w
  have hw2 := towerMotion_phase_lt_pi_div_two w
  rw [abs_lt]
  constructor
  · rw [lt_div_iff₀ Real.pi_pos]; nlinarith
  · rw [div_lt_iff₀ Real.pi_pos]; nlinarith

/-- **La grille de deux Tours à même hauteur est alignée à un anneau près.**  Pour tout réel positif
`q`, la coordonnée de pivot que lui donnent deux Tours de même hauteur `T` ne peut jamais différer de
plus de un. -/
theorem pivotCoordinate_sameHeight_shift_le_one (z w : TrueZero)
    (hT : rZeroHeight z.1 = rZeroHeight w.1) (q : ℝ) :
    |pivotCoordinate w q - pivotCoordinate z q| ≤ 1 := by
  set a : ℝ := ((towerMotionOf z).phase - (towerMotionOf w).phase) / Real.pi with ha
  have haBound := towerPosition_shift_abs_lt_half z w
  rw [← ha] at haBound
  rw [abs_lt] at haBound
  have hshift : towerPosition w q = towerPosition z q + a := by
    unfold towerPosition
    rw [← hT, ha]
    ring
  unfold pivotCoordinate
  rw [hshift]
  set x : ℝ := towerPosition z q with hx
  have hUpper : ⌈x + a⌉ ≤ ⌈x⌉ + 1 := by
    apply Int.ceil_le.mpr
    push_cast
    linarith [Int.le_ceil x]
  have hLower : ⌈x⌉ - 1 ≤ ⌈x + a⌉ := by
    have h : (x : ℝ) ≤ ((⌈x + a⌉ + 1 : ℤ) : ℝ) := by
      push_cast
      linarith [Int.le_ceil (x + a)]
    have := Int.ceil_le.mpr h
    omega
  rw [abs_le]
  omega

end RHV6Fresh
