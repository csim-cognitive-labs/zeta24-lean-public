/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TowerHierarchy
import RHV6Fresh.Terminal.FirstZeroField

/-!
# Régime ON seulement : l'anneau radial entre deux Tours successives (auteur, 2026-10-05)

Normalisation commune par `√x` : le rayon d'une Tour en `x` est `‖x^ρ/ρ‖/√x` (`normalizedRadius`).

1. **Rayon ON.** Pour un zéro en ligne de hauteur `T`, ce rayon ne dépend pas de `x` et vaut
   `r(T) = 1/√(T² + 1/4)` (`onRadius`, `normalizedRadius_onLine`).
2. **Ordre des rayons.** `r` est strictement décroissant sur les hauteurs positives
   (`onRadius_strictAnti`, `onRadius_le_iff`).
3. **L'anneau.** Entre deux Tours ON de hauteurs `T_e < T_l` : limite haute `r(T_e)` (Tour actuelle),
   limite basse `r(T_l)` (Tour suivante), épaisseur `r(T_e) − r(T_l) > 0` ; une Tour ON est dans
   l'anneau ⟺ sa hauteur est entre les deux (`onLine_ring`, caractérisation exacte `onLine_ring_iff` :
   `r(T_l) ≤ r(T_w) ≤ r(T_e) ⟺ T_e ≤ T_w ≤ T_l`, MEMBRES ON). Limite basse LOCALE strictement positive
   entre deux hauteurs ON finies (`onLine_ring_floor_pos`) : la limite globale nulle (point 5) ne la
   supprime pas. La limite basse de l'anneau est une FONCTION qui attend « `l` en ligne » : elle est
   conditionnelle et ne peut pas servir à prouver que `l` est en ligne.
4. **Encadrement par des bornes de hauteur.** `L ≤ T_l ≤ U` ⟹ `r(U) ≤ r(T_l) ≤ r(L)`, et
   l'épaisseur est encadrée de même (`onRadius_bracket`, `onLine_ring_bracket`). La borne `U` est
   une HYPOTHÈSE : aucun comptage ne la fournit ici.
5. **Limite basse globale.** Les rayons ON sont strictement positifs et passent sous tout `ε > 0`
   au-delà de la hauteur `1/ε` (`onRadius_pos`, `onRadius_lt_of_height`, `onLine_radius_lt_of_height`) :
   zéro est la limite basse de l'ensemble, pas la frontière basse d'un anneau.

Portée : `onLine_ring` est l'anneau entre deux Tours ON DONNÉES ; il ne suppose aucune consécutivité
et n'est pas une enveloppe prédictive du prochain membre (voir `Terminal/OnCrossReadings.lean`). La
limite basse globale est CONDITIONNELLE à l'existence de zéros en ligne de hauteur arbitrairement
grande, non dérivée ici. Le rayon est celui du terme BRUT `x^ρ/ρ`, pas d'un terme du reste lissé.
Tout énoncé suppose les zéros concernés EN LIGNE ; rien n'est dit d'une Tour hors ligne, et
rien ne démontre qu'un zéro suivant est en ligne. Cette frontière RADIALE n'est pas l'ordre des
CONTACTS (`WindingNested`, `towerRoomAtInfinity`). Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Rayon ON -/

/-- Rayon d'une Tour en `x`, normalisation commune par `√x`. -/
noncomputable def normalizedRadius (z : TrueZero) (x : ℝ) : ℝ := ‖zeroTerm z x‖ / Real.sqrt x

/-- Rayon ON à la hauteur `T` : `1/√(T² + 1/4)`. -/
noncomputable def onRadius (T : ℝ) : ℝ := 1 / Real.sqrt (T ^ 2 + 1 / 4)

theorem onRadius_pos (T : ℝ) : 0 < onRadius T :=
  one_div_pos.mpr (Real.sqrt_pos.mpr (by positivity))

/-- Support d'un zéro en ligne : `‖ρ‖ = √(T² + 1/4)`. -/
theorem zeroPoint_norm_onLine (z : TrueZero) (hz : rZeroRadialPosition z.1 = 1 / 2) :
    ‖zeroPoint z‖ = Real.sqrt (rZeroHeight z.1 ^ 2 + 1 / 4) := by
  rw [← Real.sqrt_sq (norm_nonneg (zeroPoint z)), zeroPoint_norm_sq, hz]
  congr 1
  ring

/-- **Rayon d'une Tour ON** : constant le long de l'axe, égal à `1/√(T² + 1/4)`. -/
theorem normalizedRadius_onLine (z : TrueZero) (hz : rZeroRadialPosition z.1 = 1 / 2) {x : ℝ}
    (hx : 0 < x) : normalizedRadius z x = onRadius (rZeroHeight z.1) := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  unfold normalizedRadius onRadius
  rw [norm_zeroTerm_eq z hx, hz, ← Real.sqrt_eq_rpow, zeroPoint_norm_onLine z hz, div_right_comm,
    div_self hs]

/-! ## 2. Ordre des rayons -/

/-- Les rayons ON décroissent quand la hauteur monte. -/
theorem onRadius_anti {L U : ℝ} (hL : 0 ≤ L) (h : L ≤ U) : onRadius U ≤ onRadius L := by
  unfold onRadius
  apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity))
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg hL (sub_nonneg.mpr h), mul_nonneg (hL.trans h) (sub_nonneg.mpr h)]

/-- Décroissance stricte. -/
theorem onRadius_strictAnti {L U : ℝ} (hL : 0 ≤ L) (h : L < U) : onRadius U < onRadius L := by
  unfold onRadius
  apply one_div_lt_one_div_of_lt (Real.sqrt_pos.mpr (by positivity))
  apply Real.sqrt_lt_sqrt (by positivity)
  nlinarith [mul_nonneg hL (sub_nonneg.mpr h.le), mul_pos (lt_of_le_of_lt hL h) (sub_pos.mpr h)]

/-- L'ordre des rayons ON est exactement l'ordre inverse des hauteurs. -/
theorem onRadius_le_iff {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) : onRadius T ≤ onRadius S ↔ S ≤ T :=
  ⟨fun h => by
      by_contra hlt
      exact absurd h (not_le.mpr (onRadius_strictAnti hT (not_le.mp hlt))),
    onRadius_anti hS⟩

/-! ## 3. L'anneau entre deux Tours ON successives -/

/-- **L'anneau ON.** Deux zéros en ligne, `T_e < T_l` : le rayon de la Tour suivante est
strictement sous celui de la Tour actuelle ; chacune est un cercle de son rayon ; l'épaisseur est strictement
positive ; une Tour ON est dans l'anneau `r(T_l) ≤ r ≤ r(T_e)` ⟺ sa hauteur est entre `T_e` et `T_l`. -/
theorem onLine_ring {e l : TrueZero} (he : rZeroRadialPosition e.1 = 1 / 2)
    (hl : rZeroRadialPosition l.1 = 1 / 2) (hT : rZeroHeight e.1 < rZeroHeight l.1) :
    onRadius (rZeroHeight l.1) < onRadius (rZeroHeight e.1) ∧
    (∀ x : ℝ, 0 < x → normalizedRadius e x = onRadius (rZeroHeight e.1)) ∧
    (∀ x : ℝ, 0 < x → normalizedRadius l x = onRadius (rZeroHeight l.1)) ∧
    0 < onRadius (rZeroHeight e.1) - onRadius (rZeroHeight l.1) ∧
    (∀ w : TrueZero, rZeroRadialPosition w.1 = 1 / 2 → ∀ x : ℝ, 0 < x →
      (normalizedRadius w x ∈ Set.Icc (onRadius (rZeroHeight l.1)) (onRadius (rZeroHeight e.1)) ↔
        rZeroHeight e.1 ≤ rZeroHeight w.1 ∧ rZeroHeight w.1 ≤ rZeroHeight l.1)) := by
  have hlt := onRadius_strictAnti e.2.le hT
  refine ⟨hlt, fun x hx => normalizedRadius_onLine e he hx,
    fun x hx => normalizedRadius_onLine l hl hx, sub_pos.mpr hlt, fun w hw x hx => ?_⟩
  rw [normalizedRadius_onLine w hw hx, Set.mem_Icc]
  exact ⟨fun h => ⟨(onRadius_le_iff e.2.le w.2.le).mp h.2, (onRadius_le_iff w.2.le l.2.le).mp h.1⟩,
    fun h => ⟨(onRadius_le_iff w.2.le l.2.le).mpr h.2, (onRadius_le_iff e.2.le w.2.le).mpr h.1⟩⟩

/-- **Caractérisation exacte de l'anneau, MEMBRES ON SEULEMENT.** Deux zéros en ligne `e`, `l` de hauteurs
`0 < T_e < T_l` : chacune est le cercle de son rayon, `r(T_l) < r(T_e)`, et pour tout zéro EN LIGNE `w`,
`r(T_l) ≤ r_w(x) ≤ r(T_e)` ⟺ `T_e ≤ T_w ≤ T_l`. Elle classe un membre ON donné ; elle ne choisit pas à elle
seule le prochain zéro et ne dit rien d'un membre qui n'est pas supposé en ligne. -/
theorem onLine_ring_iff {e l : TrueZero} (he : rZeroRadialPosition e.1 = 1 / 2)
    (hl : rZeroRadialPosition l.1 = 1 / 2) (hT : rZeroHeight e.1 < rZeroHeight l.1)
    (w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2) {x : ℝ} (hx : 0 < x) :
    normalizedRadius e x = onRadius (rZeroHeight e.1) ∧
    normalizedRadius l x = onRadius (rZeroHeight l.1) ∧
    onRadius (rZeroHeight l.1) < onRadius (rZeroHeight e.1) ∧
    ((onRadius (rZeroHeight l.1) ≤ normalizedRadius w x ∧
        normalizedRadius w x ≤ onRadius (rZeroHeight e.1)) ↔
      (rZeroHeight e.1 ≤ rZeroHeight w.1 ∧ rZeroHeight w.1 ≤ rZeroHeight l.1)) := by
  refine ⟨normalizedRadius_onLine e he hx, normalizedRadius_onLine l hl hx,
    onRadius_strictAnti e.2.le hT, ?_⟩
  rw [normalizedRadius_onLine w hw hx]
  exact ⟨fun h => ⟨(onRadius_le_iff e.2.le w.2.le).mp h.2, (onRadius_le_iff w.2.le l.2.le).mp h.1⟩,
    fun h => ⟨(onRadius_le_iff w.2.le l.2.le).mpr h.2, (onRadius_le_iff e.2.le w.2.le).mpr h.1⟩⟩

/-- **Limite basse LOCALE, strictement positive.** Entre deux hauteurs ON finies, toute Tour ON `w` de hauteur
`T_w ≤ T_l` a un rayon `≥ r(T_l) > 0`, en tout point de l'axe. La limite basse GLOBALE nulle
(`onRadius_lt_of_height`) porte sur des hauteurs arbitrairement grandes ; elle ne supprime pas cette borne
locale. L'énoncé porte sur `w` EN LIGNE ; il n'est pas une borne sur un membre non supposé en ligne. -/
theorem onLine_ring_floor_pos {l w : TrueZero} (hw : rZeroRadialPosition w.1 = 1 / 2)
    (hwl : rZeroHeight w.1 ≤ rZeroHeight l.1) {x : ℝ} (hx : 0 < x) :
    0 < onRadius (rZeroHeight l.1) ∧ onRadius (rZeroHeight l.1) ≤ normalizedRadius w x := by
  rw [normalizedRadius_onLine w hw hx]
  exact ⟨onRadius_pos _, onRadius_anti w.2.le hwl⟩

/-! ## 4. Encadrement par des bornes de hauteur -/

/-- `L ≤ T ≤ U` ⟹ `1/√(U² + 1/4) ≤ r(T) ≤ 1/√(L² + 1/4)`. -/
theorem onRadius_bracket {L T U : ℝ} (hL : 0 ≤ L) (hLT : L ≤ T) (hTU : T ≤ U) :
    1 / Real.sqrt (U ^ 2 + 1 / 4) ≤ onRadius T ∧ onRadius T ≤ 1 / Real.sqrt (L ^ 2 + 1 / 4) :=
  ⟨onRadius_anti (hL.trans hLT) hTU, onRadius_anti hL hLT⟩

/-- **Encadrement de la limite basse de l'anneau.** Zéro suivant en ligne, `T_e ≤ L ≤ T_l ≤ U`
(bornes de hauteur en hypothèse) : le rayon de la Tour suivante est entre `r(U)` et `r(L)`, sous le
rayon de la Tour actuelle, et l'épaisseur de l'anneau est entre `r(T_e) − r(L)` et `r(T_e) − r(U)`. -/
theorem onLine_ring_bracket (e l : TrueZero) (hl : rZeroRadialPosition l.1 = 1 / 2) {L U : ℝ}
    (hEL : rZeroHeight e.1 ≤ L) (hL : L ≤ rZeroHeight l.1) (hU : rZeroHeight l.1 ≤ U) :
    (∀ x : ℝ, 0 < x → 1 / Real.sqrt (U ^ 2 + 1 / 4) ≤ normalizedRadius l x ∧
      normalizedRadius l x ≤ 1 / Real.sqrt (L ^ 2 + 1 / 4)) ∧
    onRadius L ≤ onRadius (rZeroHeight e.1) ∧
    onRadius (rZeroHeight e.1) - onRadius L ≤
      onRadius (rZeroHeight e.1) - onRadius (rZeroHeight l.1) ∧
    onRadius (rZeroHeight e.1) - onRadius (rZeroHeight l.1) ≤
      onRadius (rZeroHeight e.1) - onRadius U := by
  have hL0 : 0 ≤ L := e.2.le.trans hEL
  have hb := onRadius_bracket hL0 hL hU
  refine ⟨fun x hx => ?_, onRadius_anti e.2.le hEL, sub_le_sub_left hb.2 _, sub_le_sub_left hb.1 _⟩
  rw [normalizedRadius_onLine l hl hx]
  exact hb

/-! ## 5. Limite basse globale -/

/-- Au-delà de la hauteur `1/ε`, le rayon ON est sous `ε`. -/
theorem onRadius_lt_of_height {ε T : ℝ} (hε : 0 < ε) (hT : 1 / ε < T) : onRadius T < ε := by
  have hT0 : 0 < T := (one_div_pos.mpr hε).trans hT
  have hs : T < Real.sqrt (T ^ 2 + 1 / 4) := Real.lt_sqrt_of_sq_lt (by linarith)
  unfold onRadius
  rw [div_lt_iff₀ (hT0.trans hs)]
  calc (1 : ℝ) = ε * (1 / ε) := (mul_one_div_cancel hε.ne').symm
    _ < ε * Real.sqrt (T ^ 2 + 1 / 4) := mul_lt_mul_of_pos_left (hT.trans hs) hε

/-- **Limite basse globale des Tours ON** : toute Tour ON de hauteur au-delà de `1/ε` a un rayon
strictement positif et strictement sous `ε`, en tout point de l'axe : zéro n'est le rayon
d'aucune Tour. -/
theorem onLine_radius_lt_of_height {ε : ℝ} (hε : 0 < ε) (w : TrueZero)
    (hw : rZeroRadialPosition w.1 = 1 / 2) (hT : 1 / ε < rZeroHeight w.1) {x : ℝ} (hx : 0 < x) :
    0 < normalizedRadius w x ∧ normalizedRadius w x < ε := by
  rw [normalizedRadius_onLine w hw hx]
  exact ⟨onRadius_pos _, onRadius_lt_of_height hε hT⟩

#print axioms normalizedRadius_onLine
#print axioms onRadius_strictAnti
#print axioms onRadius_le_iff
#print axioms onLine_ring
#print axioms onLine_ring_iff
#print axioms onLine_ring_floor_pos
#print axioms onRadius_bracket
#print axioms onLine_ring_bracket
#print axioms onRadius_lt_of_height
#print axioms onLine_radius_lt_of_height

end RHV6Fresh
