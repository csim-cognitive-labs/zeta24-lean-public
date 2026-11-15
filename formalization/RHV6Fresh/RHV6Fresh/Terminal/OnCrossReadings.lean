/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.OnRadialRing
import RHV6Fresh.Terminal.SymmetricWinding
import RHV6Fresh.Terminal.MirrorPairExactSum
import RHV6Fresh.Terminal.WindowFeasibility
import RHV6Fresh.Terminal.HeightPacket
import RHV6Fresh.Terminal.VerticalEnergyPush
import RHV6Fresh.Terminal.DiagonalPassage
import RHV6Fresh.Tower.CanonicalOrigin
import RHV6Fresh.Grammar.ExpectedMinimum

/-!
# Croisement, sur les mêmes membres : rayons, contacts tangents, hauteurs, comptage, reste exact

(auteur, 2026-10-05). Les mêmes membres et les mêmes hauteurs dans toutes les lectures.

Statut de chaque énoncé : **identité déterministe** (vraie pour toute partie réelle, sauf mention
« en ligne »), **borne démontrée**, ou **équivalence dont aucun côté n'est dérivé**. Aucune
corrélation mesurée n'est un énoncé de ce fichier.

1. **Portée de l'anneau.** `onLine_ring` ne suppose aucune consécutivité : c'est l'anneau entre deux
   Tours ON DONNÉES. Entre deux membres consécutifs, aucun membre n'a de hauteur strictement entre
   les deux (`consecutive_no_height_between`) : l'anneau consécutif ne contient strictement aucune
   Tour ON (`consecutive_ring_interior_empty`).
2. **Enveloppe prédictive (ce que les données précédentes imposent, sans supposer le suivant ON).**
   `β_l ≤ 1/2` et `x ≥ 1` : rayon `≤ 1/‖ρ_l‖ < 1/T_l` (`radius_envelope_of_le_half`) ; si de plus
   `T_e² + 1/4 ≤ T_l²` : rayon `≤ r(T_e)`, limite haute de l'anneau (`radius_le_ring_top_of_gap`) ;
   caractérisation EXACTE de cette domination sur `x ≥ 1` : ⟺ `T_e² + 1/4 ≤ ‖ρ_l‖² = β_l² + T_l²`
   (`radius_dominated_iff_norm`, `radius_dominated_iff_gap`), condition d'écart explicite, non dérivée
   pour un membre bas ; sur TOUT l'axe positif, domination ⟺ `β_l = 1/2 ∧ ‖ρ_e‖ ≤ ‖ρ_l‖`
   (`radius_dominated_axis_iff`), et un membre bas dépasse tout seuil près de zéro
   (`low_member_not_dominated_on_axis`). Limite basse : plancher strictement positif sur tout domaine
   fini `1 ≤ x ≤ X` (`radius_floor_on_finite_domain`) ; aucun plancher UNIFORME jusqu'à l'infini
   pour un membre bas (`low_member_radius_below`).
3. **Limite globale.** « Les rayons ON passent sous tout `ε` » ⟺ « les hauteurs ON sont non
   bornées » (`onRadii_small_iff_onHeights_unbounded`) : aucun des deux côtés n'est dérivé dans le dépôt.
4. **Encadrements numériques** sous des bornes de hauteur en HYPOTHÈSE (certificat externe pour les
   trois premiers zéros, non compilé) : `certified_three_onRadii`.
5. **Contacts ↔ hauteurs.** Au contact propre le terme brut est réel de signe `(−1)^k`
   (`zeroTerm_at_own_contact`), en ligne `(−1)^k·r(T)·√C_k` (`onLine_zeroTerm_at_own_contact`) ;
   la position de TOUT autre membre aux contacts d'un membre est fixée par les hauteurs et les deux
   phases (`cross_position_at_contact`), l'avance entre deux contacts successifs vaut `T_l/T_e`
   (`cross_advance_between_contacts`) : aucune partie réelle n'y figure.
6. **Rayon aux contacts du zéro engagé.** `r_l(C_{k+1}) = e^{(β_l − 1/2)π/T_e}·r_l(C_k)`
   (`radius_step_between_contacts`), facteur `= 1` ⟺ `β_l = 1/2` (`radius_step_eq_one_iff`) : certificat.
7. **Reste exact.** Le terme d'un membre dans le reste LISSÉ est son terme BRUT divisé par `ρ + 1`,
   fois `−m` (`residueTerm_eq_zeroTerm`, `residueTerm_norm`) : transfert membre par membre SEULEMENT ;
   aucune enveloppe de la somme n'en découle.
8. **Cas bas (conséquence, pas contradiction).** Au-delà d'une abscisse, la Tour d'un zéro bas est
   sous toute limite basse ON et celle de son miroir au-dessus de toute limite haute
   (`low_case_pair_leaves_ring`) ; aucun énoncé compilé n'oblige une Tour à rester dans l'anneau.

Rang : `nZeroSourceIndex` compte des POINTS (cardinal d'un ensemble de membres) ; la multiplicité
n'apparaît que dans le coefficient `m` du reste. Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Portée de l'anneau : deux ON donnés, ou deux membres consécutifs -/

/-- Entre deux membres consécutifs, aucun membre n'a de hauteur strictement entre les deux. -/
theorem consecutive_no_height_between (p : TZeroPassage) (w : TNonTrivialZetaZero) :
    ¬ (rZeroHeight p.zEarlierMember < rZeroHeight w ∧ rZeroHeight w < rZeroHeight p.zLaterMember) := by
  rintro ⟨h1, h2⟩
  exact p.hConsecutive.2 ⟨w, (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mpr (Or.inl h1),
    (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mpr (Or.inl h2)⟩

/-- **Anneau consécutif** : entre les rayons ON des deux extrémités d'un passage, strictement, il
n'y a le rayon d'aucune Tour ON. (Les extrémités ne sont pas supposées en ligne : l'énoncé porte
sur les rayons ON de leurs hauteurs.) -/
theorem consecutive_ring_interior_empty (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2) {x : ℝ} (hx : 0 < x) :
    ¬ (onRadius (rZeroHeight p.zLaterMember) < normalizedRadius w x ∧
      normalizedRadius w x < onRadius (rZeroHeight p.zEarlierMember)) := by
  rw [normalizedRadius_onLine w hw hx]
  rintro ⟨h1, h2⟩
  apply consecutive_no_height_between p w.1
  constructor
  · by_contra h
    exact absurd h2 (not_lt.mpr (onRadius_anti w.2.le (not_lt.mp h)))
  · by_contra h
    exact absurd h1 (not_lt.mpr (onRadius_anti (hE.le.trans (passage_height_le p)) (not_lt.mp h)))

/-! ## 2. Rayon de toute Tour, enveloppe sans supposer le suivant en ligne -/

/-- Rayon normalisé de toute Tour : `x^{β − 1/2}/‖ρ‖`. -/
theorem normalizedRadius_eq (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    normalizedRadius z x = x ^ (rZeroRadialPosition z.1 - 1 / 2) / ‖zeroPoint z‖ := by
  unfold normalizedRadius
  rw [norm_zeroTerm_eq z hx, Real.sqrt_eq_rpow, div_right_comm, ← Real.rpow_sub hx]

theorem normalizedRadius_pos (z : TrueZero) {x : ℝ} (hx : 0 < x) : 0 < normalizedRadius z x := by
  rw [normalizedRadius_eq z hx]
  exact div_pos (Real.rpow_pos_of_pos hx _) (norm_zeroPoint_pos z)

/-- Amplitude du terme brut = rayon normalisé × `√x`. -/
theorem norm_zeroTerm_eq_radius (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm z x‖ = normalizedRadius z x * Real.sqrt x := by
  unfold normalizedRadius
  rw [div_mul_cancel₀ _ (Real.sqrt_pos.mpr hx).ne']

/-- La hauteur est strictement sous le support. -/
theorem height_lt_norm_zeroPoint (z : TrueZero) : rZeroHeight z.1 < ‖zeroPoint z‖ := by
  have hβ := thm_zeroRadialPosition_positive z.1
  apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
  rw [zeroPoint_norm_sq]
  nlinarith

/-- **Enveloppe prédictive haute, sans supposer le zéro en ligne** : partie réelle au plus un demi
et `x ≥ 1` ⟹ rayon `≤ 1/‖ρ‖ < 1/T`. -/
theorem radius_envelope_of_le_half (l : TrueZero) (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) {x : ℝ}
    (hx : 1 ≤ x) :
    normalizedRadius l x ≤ 1 / ‖zeroPoint l‖ ∧ 1 / ‖zeroPoint l‖ < 1 / rZeroHeight l.1 := by
  refine ⟨?_, one_div_lt_one_div_of_lt l.2 (height_lt_norm_zeroPoint l)⟩
  rw [normalizedRadius_eq l (by linarith)]
  exact div_le_div_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith))
    (norm_zeroPoint_pos l).le

/-- **Limite haute de l'anneau, sans supposer le suivant en ligne**, sous un écart de hauteur
suffisant `T_e² + 1/4 ≤ T_l²` (hypothèse) : le rayon du suivant ne dépasse pas `r(T_e)` sur `x ≥ 1`. -/
theorem radius_le_ring_top_of_gap (l : TrueZero) (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) {Te : ℝ}
    (hgap : Te ^ 2 + 1 / 4 ≤ rZeroHeight l.1 ^ 2) {x : ℝ} (hx : 1 ≤ x) :
    normalizedRadius l x ≤ onRadius Te := by
  refine (radius_envelope_of_le_half l hβ hx).1.trans ?_
  unfold onRadius
  apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity))
  rw [Real.sqrt_le_iff]
  refine ⟨norm_nonneg _, ?_⟩
  rw [zeroPoint_norm_sq]
  nlinarith [sq_nonneg (rZeroRadialPosition l.1)]

theorem rpow_eventually_gt {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    ∃ X : ℝ, 0 < X ∧ ∀ x : ℝ, X ≤ x → c < x ^ δ := by
  have hc : 0 < |c| + 1 := by positivity
  refine ⟨(|c| + 1) ^ (1 / δ), Real.rpow_pos_of_pos hc _, fun x hx => ?_⟩
  have hX : ((|c| + 1) ^ (1 / δ)) ^ δ = |c| + 1 := by
    rw [← Real.rpow_mul hc.le, one_div_mul_cancel hδ.ne', Real.rpow_one]
  calc c ≤ |c| := le_abs_self c
    _ < |c| + 1 := lt_add_one _
    _ = ((|c| + 1) ^ (1 / δ)) ^ δ := hX.symm
    _ ≤ x ^ δ := Real.rpow_le_rpow (Real.rpow_pos_of_pos hc _).le hx hδ.le

/-- Rayon en `x = 1` : `1/‖ρ‖`. -/
theorem normalizedRadius_one (z : TrueZero) : normalizedRadius z 1 = 1 / ‖zeroPoint z‖ := by
  rw [normalizedRadius_eq z one_pos, Real.one_rpow]

/-- **Plancher sur tout domaine fini, sans supposer le membre en ligne** (`β_l ≤ 1/2`) : pour
`1 ≤ x ≤ X`, rayon `≥ X^{β_l − 1/2}/‖ρ_l‖ > 0`. Borne LOCALE acquise ; aucun plancher uniforme jusqu'à
l'infini n'en découle pour un membre bas (`low_member_radius_below`). -/
theorem radius_floor_on_finite_domain (l : TrueZero) (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) {X x : ℝ}
    (hx : 1 ≤ x) (hX : x ≤ X) :
    0 < X ^ (rZeroRadialPosition l.1 - 1 / 2) / ‖zeroPoint l‖ ∧
      X ^ (rZeroRadialPosition l.1 - 1 / 2) / ‖zeroPoint l‖ ≤ normalizedRadius l x := by
  have hx0 : 0 < x := by linarith
  refine ⟨div_pos (Real.rpow_pos_of_pos (by linarith) _) (norm_zeroPoint_pos l), ?_⟩
  rw [normalizedRadius_eq l hx0]
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx0 hX (by linarith))
    (norm_zeroPoint_pos l).le

/-- **Limite haute de l'anneau, caractérisée EXACTEMENT** (`β_l ≤ 1/2`) : le rayon du membre atteint reste
sous `r(T_e)` sur tout `x ≥ 1` ⟺ `T_e² + 1/4 ≤ ‖ρ_l‖²`. La condition d'écart de hauteur est explicite ;
pour un membre en ligne elle découle de `T_e < T_l` ; pour un membre bas, aucun énoncé du dépôt ne la fournit. -/
theorem radius_dominated_iff_norm (l : TrueZero) (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) (Te : ℝ) :
    (∀ x : ℝ, 1 ≤ x → normalizedRadius l x ≤ onRadius Te) ↔ Te ^ 2 + 1 / 4 ≤ ‖zeroPoint l‖ ^ 2 := by
  have hs : 0 < Real.sqrt (Te ^ 2 + 1 / 4) := Real.sqrt_pos.mpr (by positivity)
  constructor
  · intro h
    have h1 := h 1 le_rfl
    rw [normalizedRadius_one] at h1
    unfold onRadius at h1
    have hle : Real.sqrt (Te ^ 2 + 1 / 4) ≤ ‖zeroPoint l‖ :=
      le_of_one_div_le_one_div (norm_zeroPoint_pos l) h1
    calc Te ^ 2 + 1 / 4 = Real.sqrt (Te ^ 2 + 1 / 4) ^ 2 := (Real.sq_sqrt (by positivity)).symm
      _ ≤ ‖zeroPoint l‖ ^ 2 := pow_le_pow_left₀ hs.le hle 2
  · intro h x hx
    refine (radius_envelope_of_le_half l hβ hx).1.trans ?_
    unfold onRadius
    apply one_div_le_one_div_of_le hs
    rw [Real.sqrt_le_iff]
    exact ⟨norm_nonneg _, h⟩

/-- La même caractérisation sur les paramètres : `T_e² + 1/4 ≤ β_l² + T_l²`. -/
theorem radius_dominated_iff_gap (l : TrueZero) (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) (Te : ℝ) :
    (∀ x : ℝ, 1 ≤ x → normalizedRadius l x ≤ onRadius Te) ↔
      Te ^ 2 + 1 / 4 ≤ rZeroRadialPosition l.1 ^ 2 + rZeroHeight l.1 ^ 2 := by
  rw [radius_dominated_iff_norm l hβ Te, zeroPoint_norm_sq]

/-- **Domination sur TOUT l'axe positif ⟺ même partie réelle et supports ordonnés** (en rayons ; `e` en
ligne) : `r_l(x) ≤ r(T_e)` pour tout `x > 0` ⟺ `β_l = 1/2 ∧ ‖ρ_e‖ ≤ ‖ρ_l‖`. Une domination valable sur
`x ≥ 1` ne s'étend donc jamais à l'axe entier pour un membre qui n'est pas en ligne. -/
theorem radius_dominated_axis_iff (e l : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2) :
    (∀ x : ℝ, 0 < x → normalizedRadius l x ≤ onRadius (rZeroHeight e.1)) ↔
      rZeroRadialPosition l.1 = 1 / 2 ∧ ‖zeroPoint e‖ ≤ ‖zeroPoint l‖ := by
  have hw := whole_tower_inside_iff e l
  rw [he] at hw
  rw [← hw]
  constructor
  · intro h x hx
    have h1 := h x hx
    rw [← normalizedRadius_onLine e he hx] at h1
    unfold normalizedRadius at h1
    exact (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr hx)).mp h1
  · intro h x hx
    rw [← normalizedRadius_onLine e he hx]
    unfold normalizedRadius
    exact div_le_div_of_nonneg_right (h x hx) (Real.sqrt_pos.mpr hx).le

/-- **Un membre bas n'est dominé sur aucun voisinage de zéro** : pour `β_l < 1/2`, le rayon dépasse tout
seuil `R` en des abscisses `0 < x < 1`. -/
theorem low_member_not_dominated_on_axis (l : TrueZero) (hl : rZeroRadialPosition l.1 < 1 / 2) (R : ℝ) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ R < normalizedRadius l x := by
  obtain ⟨X, _, h⟩ := rpow_eventually_gt (sub_pos.mpr hl) (R * ‖zeroPoint l‖)
  have hy2 : (2 : ℝ) ≤ max X 2 := le_max_right _ _
  have hy0 : 0 < max X 2 := by linarith
  refine ⟨1 / max X 2, one_div_pos.mpr hy0, ?_, ?_⟩
  · rw [div_lt_one hy0]; linarith
  · rw [normalizedRadius_eq l (one_div_pos.mpr hy0), lt_div_iff₀ (norm_zeroPoint_pos l)]
    have e : (1 / max X 2) ^ (rZeroRadialPosition l.1 - 1 / 2) =
        (max X 2) ^ (1 / 2 - rZeroRadialPosition l.1) := by
      rw [one_div, Real.inv_rpow hy0.le, ← Real.rpow_neg hy0.le]
      congr 1; ring
    rw [e]
    exact h _ (le_max_left _ _)

/-! ## 3. Limite globale : conditionnelle à des hauteurs ON non bornées -/

/-- **Les rayons ON passent sous tout `ε` ⟺ les hauteurs ON sont non bornées.** Équivalence :
aucun des deux côtés n'est dérivé ici. -/
theorem onRadii_small_iff_onHeights_unbounded :
    (∀ ε : ℝ, 0 < ε → ∃ w : TrueZero, rZeroRadialPosition w.1 = 1 / 2 ∧
        onRadius (rZeroHeight w.1) < ε) ↔
      (∀ H : ℝ, ∃ w : TrueZero, rZeroRadialPosition w.1 = 1 / 2 ∧ H < rZeroHeight w.1) := by
  constructor
  · intro h H
    by_cases hH : 0 < H
    · obtain ⟨w, hw, hr⟩ := h (onRadius H) (onRadius_pos H)
      refine ⟨w, hw, ?_⟩
      by_contra hle
      exact absurd hr (not_lt.mpr (onRadius_anti w.2.le (not_lt.mp hle)))
    · obtain ⟨w, hw, _⟩ := h 1 one_pos
      exact ⟨w, hw, lt_of_le_of_lt (not_lt.mp hH) w.2⟩
  · intro h ε hε
    obtain ⟨w, hw, hH⟩ := h (1 / ε)
    exact ⟨w, hw, onRadius_lt_of_height hε hH⟩

/-! ## 4. Encadrements numériques sous des bornes de hauteur en hypothèse -/

theorem onRadius_lt_of_sq {T a : ℝ} (ha : 0 < a) (h : 1 < a ^ 2 * (T ^ 2 + 1 / 4)) :
    onRadius T < a := by
  have h1 : (1 : ℝ) < Real.sqrt (a ^ 2 * (T ^ 2 + 1 / 4)) :=
    (Real.lt_sqrt zero_le_one).mpr (by simpa using h)
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le] at h1
  unfold onRadius
  rw [div_lt_iff₀ (Real.sqrt_pos.mpr (by positivity))]
  exact h1

theorem lt_onRadius_of_sq {T a : ℝ} (ha : 0 ≤ a) (h : a ^ 2 * (T ^ 2 + 1 / 4) < 1) :
    a < onRadius T := by
  have h1 : Real.sqrt (a ^ 2 * (T ^ 2 + 1 / 4)) < 1 :=
    (Real.sqrt_lt' one_pos).mpr (by simpa using h)
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha] at h1
  unfold onRadius
  rw [lt_div_iff₀ (Real.sqrt_pos.mpr (by positivity))]
  exact h1

/-- **Les trois premiers anneaux, sous bornes de hauteur en hypothèse.** Si trois hauteurs sont dans
les intervalles indiqués (certificat EXTERNE pour les trois premiers zéros, non compilé), leurs
rayons ON et les épaisseurs des deux anneaux sont encadrés numériquement. Fonction de la hauteur
seule : l'énoncé ne dit pas que ces hauteurs sont celles de zéros en ligne. -/
theorem certified_three_onRadii {T₁ T₂ T₃ : ℝ} (h₁ : 14.134 ≤ T₁ ∧ T₁ ≤ 14.135)
    (h₂ : 21.022 ≤ T₂ ∧ T₂ ≤ 21.023) (h₃ : 25.010 ≤ T₃ ∧ T₃ ≤ 25.011) :
    (0.0707 < onRadius T₁ ∧ onRadius T₁ < 0.0708) ∧
    (0.04755 < onRadius T₂ ∧ onRadius T₂ < 0.04756) ∧
    (0.03997 < onRadius T₃ ∧ onRadius T₃ < 0.03998) ∧
    (0.0231 < onRadius T₁ - onRadius T₂ ∧ onRadius T₁ - onRadius T₂ < 0.0233) ∧
    (0.0075 < onRadius T₂ - onRadius T₃ ∧ onRadius T₂ - onRadius T₃ < 0.0076) := by
  have a1 : (0.0707 : ℝ) < onRadius T₁ :=
    lt_of_lt_of_le (lt_onRadius_of_sq (by norm_num) (by norm_num))
      (onRadius_anti (by linarith [h₁.1]) h₁.2)
  have b1 : onRadius T₁ < 0.0708 :=
    lt_of_le_of_lt (onRadius_anti (by norm_num) h₁.1) (onRadius_lt_of_sq (by norm_num) (by norm_num))
  have a2 : (0.04755 : ℝ) < onRadius T₂ :=
    lt_of_lt_of_le (lt_onRadius_of_sq (by norm_num) (by norm_num))
      (onRadius_anti (by linarith [h₂.1]) h₂.2)
  have b2 : onRadius T₂ < 0.04756 :=
    lt_of_le_of_lt (onRadius_anti (by norm_num) h₂.1) (onRadius_lt_of_sq (by norm_num) (by norm_num))
  have a3 : (0.03997 : ℝ) < onRadius T₃ :=
    lt_of_lt_of_le (lt_onRadius_of_sq (by norm_num) (by norm_num))
      (onRadius_anti (by linarith [h₃.1]) h₃.2)
  have b3 : onRadius T₃ < 0.03998 :=
    lt_of_le_of_lt (onRadius_anti (by norm_num) h₃.1) (onRadius_lt_of_sq (by norm_num) (by norm_num))
  refine ⟨⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-! ## 5. Contacts tangents ↔ hauteurs -/

/-- **Au contact propre, le terme brut est réel** : `(−1)^k` fois son amplitude. -/
theorem zeroTerm_at_own_contact (z : TrueZero) (k : ℤ) :
    zeroTerm z (contactMinusAt z k) =
      (((-1 : ℝ) ^ k * ‖zeroTerm z (contactMinusAt z k)‖ : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
    exact zeroTerm_re_at_contact z k
  · rw [Complex.ofReal_im]
    exact ray_zeroTerm_real z k

/-- **En ligne** : au contact propre le terme brut vaut `(−1)^k · r(T) · √C_k`, hauteur seule. -/
theorem onLine_zeroTerm_at_own_contact (z : TrueZero) (hz : rZeroRadialPosition z.1 = 1 / 2)
    (k : ℤ) :
    zeroTerm z (contactMinusAt z k) =
      (((-1 : ℝ) ^ k * (onRadius (rZeroHeight z.1) * Real.sqrt (contactMinusAt z k)) : ℝ) : ℂ) := by
  have hq := contactMinusAt_positive z k
  rw [zeroTerm_at_own_contact, norm_zeroTerm_eq_radius z hq, normalizedRadius_onLine z hz hq]

/-- Logarithme du contact : `T · log C_k = k·π + φ`. -/
theorem height_mul_log_contact (z : TrueZero) (k : ℤ) :
    rZeroHeight z.1 * Real.log (contactMinusAt z k) = (k : ℝ) * Real.pi + (towerMotionOf z).phase := by
  have h := pi_mul_towerPosition z (contactMinusAt z k)
  rw [towerPosition_contactMinusAt] at h
  linarith

/-- Logarithme du contact : `log C_k = (k·π + φ)/T`. -/
theorem log_contact_eq (z : TrueZero) (k : ℤ) :
    Real.log (contactMinusAt z k) =
      ((k : ℝ) * Real.pi + (towerMotionOf z).phase) / rZeroHeight z.1 :=
  eq_div_of_mul_eq z.2.ne' ((mul_comm _ _).trans (height_mul_log_contact z k))

/-- **Position d'un membre aux contacts d'un autre** : fixée par les deux hauteurs et les deux
phases, `π·Π_l(C_k(e)) = (T_l/T_e)·(k·π + φ_e) − φ_l`. Toute partie réelle. -/
theorem cross_position_at_contact (e l : TrueZero) (k : ℤ) :
    Real.pi * towerPosition l (contactMinusAt e k) =
      rZeroHeight l.1 / rZeroHeight e.1 * ((k : ℝ) * Real.pi + (towerMotionOf e).phase) -
        (towerMotionOf l).phase := by
  rw [pi_mul_towerPosition, log_contact_eq]
  ring

/-- **Avance entre deux contacts successifs d'un autre membre** : exactement le rapport des
hauteurs, `T_l/T_e` demi-tours. Aucune partie réelle n'y figure. -/
theorem cross_advance_between_contacts (e l : TrueZero) (k : ℤ) :
    towerPosition l (contactMinusAt e (k + 1)) - towerPosition l (contactMinusAt e k) =
      rZeroHeight l.1 / rZeroHeight e.1 := by
  apply mul_left_cancel₀ Real.pi_pos.ne'
  rw [mul_sub, cross_position_at_contact, cross_position_at_contact]
  push_cast
  ring

/-! ## 6. Rayon d'un membre lu aux contacts d'un autre -/

/-- **Pas du rayon entre deux contacts successifs du zéro `e`** : facteur `e^{(β_l − 1/2)·π/T_e}`. -/
theorem radius_step_between_contacts (e l : TrueZero) (k : ℤ) :
    normalizedRadius l (contactMinusAt e (k + 1)) =
      Real.exp ((rZeroRadialPosition l.1 - 1 / 2) * Real.pi / rZeroHeight e.1) *
        normalizedRadius l (contactMinusAt e k) := by
  have h0 := contactMinusAt_positive e k
  have h1 := contactMinusAt_positive e (k + 1)
  have hlog : Real.log (contactMinusAt e (k + 1)) =
      Real.log (contactMinusAt e k) + Real.pi / rZeroHeight e.1 := by
    rw [log_contact_eq, log_contact_eq]
    push_cast
    ring
  rw [normalizedRadius_eq l h1, normalizedRadius_eq l h0, Real.rpow_def_of_pos h1,
    Real.rpow_def_of_pos h0, hlog, ← mul_div_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Le facteur vaut un ⟺ le membre lu est en ligne : certificat, il lit la partie réelle. -/
theorem radius_step_eq_one_iff (e l : TrueZero) :
    Real.exp ((rZeroRadialPosition l.1 - 1 / 2) * Real.pi / rZeroHeight e.1) = 1 ↔
      rZeroRadialPosition l.1 = 1 / 2 := by
  rw [Real.exp_eq_one_iff, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rcases mul_eq_zero.mp h with h | h
      · linarith
      · exact absurd h Real.pi_pos.ne'
    · exact absurd h e.2.ne'
  · intro h
    left
    rw [h]
    ring

/-- Sous la ligne, le rayon décroît strictement d'un contact du zéro `e` au suivant. -/
theorem low_radius_decreases_between_contacts (e l : TrueZero)
    (hl : rZeroRadialPosition l.1 < 1 / 2) (k : ℤ) :
    normalizedRadius l (contactMinusAt e (k + 1)) < normalizedRadius l (contactMinusAt e k) := by
  have hpos := normalizedRadius_pos l (contactMinusAt_positive e k)
  have hneg : (rZeroRadialPosition l.1 - 1 / 2) * Real.pi / rZeroHeight e.1 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) Real.pi_pos) e.2
  have hexp : Real.exp ((rZeroRadialPosition l.1 - 1 / 2) * Real.pi / rZeroHeight e.1) < 1 :=
    calc _ < Real.exp 0 := Real.exp_lt_exp.mpr hneg
      _ = 1 := Real.exp_zero
  rw [radius_step_between_contacts]
  calc _ < 1 * normalizedRadius l (contactMinusAt e k) := mul_lt_mul_of_pos_right hexp hpos
    _ = _ := one_mul _

/-! ## 7. Reste exact : terme lissé d'un membre = terme brut divisé par `ρ + 1` -/

/-- **Transfert membre par membre** : le terme d'un membre dans le reste lissé est `−m` fois son
terme brut divisé par `ρ + 1`. -/
theorem residueTerm_eq_zeroTerm (z : TrueZero) (x : ℝ) :
    nontrivialZeroResidueTerm x (memberIndex z) =
      -(zetaZeroMultiplicity (zeroPoint z) : ℂ) * (zeroTerm z x / (zeroPoint z + 1)) := by
  unfold zeroTerm
  rw [div_div]
  rfl

/-- Module du terme lissé d'un membre : `m·‖terme brut‖/‖ρ + 1‖`. -/
theorem residueTerm_norm (z : TrueZero) (x : ℝ) :
    ‖nontrivialZeroResidueTerm x (memberIndex z)‖ =
      (zetaZeroMultiplicity (zeroPoint z) : ℝ) * (‖zeroTerm z x‖ / ‖zeroPoint z + 1‖) := by
  rw [residueTerm_eq_zeroTerm, norm_mul, norm_neg, Complex.norm_natCast, norm_div]

/-- **En ligne, au contact propre** : le terme lissé vaut `−m·(−1)^k·r(T)·√C_k/(ρ + 1)`. -/
theorem onLine_residueTerm_at_own_contact (z : TrueZero) (hz : rZeroRadialPosition z.1 = 1 / 2)
    (k : ℤ) :
    nontrivialZeroResidueTerm (contactMinusAt z k) (memberIndex z) =
      -(zetaZeroMultiplicity (zeroPoint z) : ℂ) *
        ((((-1 : ℝ) ^ k * (onRadius (rZeroHeight z.1) * Real.sqrt (contactMinusAt z k)) : ℝ) : ℂ) /
          (zeroPoint z + 1)) := by
  rw [residueTerm_eq_zeroTerm, onLine_zeroTerm_at_own_contact z hz k]

/-! ## 8. Cas bas : la paire quitte tout anneau ON (conséquence, pas contradiction) -/

/-- Au-dessus de la ligne, le rayon dépasse tout seuil au-delà d'une abscisse. -/
theorem high_member_radius_exceeds (w : TrueZero) (hw : 1 / 2 < rZeroRadialPosition w.1) (R : ℝ) :
    ∃ X : ℝ, 0 < X ∧ ∀ x : ℝ, X ≤ x → R < normalizedRadius w x := by
  obtain ⟨X, hX, h⟩ := rpow_eventually_gt (sub_pos.mpr hw) (R * ‖zeroPoint w‖)
  refine ⟨X, hX, fun x hx => ?_⟩
  rw [normalizedRadius_eq w (hX.trans_le hx), lt_div_iff₀ (norm_zeroPoint_pos w)]
  exact h x hx

/-- Sous la ligne, le rayon passe sous tout seuil positif au-delà d'une abscisse : aucune limite
basse d'anneau ne tient pour une Tour qui n'est pas supposée en ligne. -/
theorem low_member_radius_below (w : TrueZero) (hw : rZeroRadialPosition w.1 < 1 / 2) {ε : ℝ}
    (hε : 0 < ε) : ∃ X : ℝ, 0 < X ∧ ∀ x : ℝ, X ≤ x → normalizedRadius w x < ε := by
  have hρ := norm_zeroPoint_pos w
  obtain ⟨X, hX, h⟩ := rpow_eventually_gt (sub_pos.mpr hw) (1 / (ε * ‖zeroPoint w‖))
  refine ⟨X, hX, fun x hx => ?_⟩
  have hx0 : 0 < x := hX.trans_le hx
  have hpow : 0 < x ^ (1 / 2 - rZeroRadialPosition w.1) := Real.rpow_pos_of_pos hx0 _
  have hinv : 1 / x ^ (1 / 2 - rZeroRadialPosition w.1) < ε * ‖zeroPoint w‖ :=
    (one_div_lt (mul_pos hε hρ) hpow).mp (h x hx)
  have e : x ^ (rZeroRadialPosition w.1 - 1 / 2) = 1 / x ^ (1 / 2 - rZeroRadialPosition w.1) := by
    rw [show rZeroRadialPosition w.1 - 1 / 2 = -(1 / 2 - rZeroRadialPosition w.1) by ring,
      Real.rpow_neg hx0.le]
    exact (one_div _).symm
  rw [normalizedRadius_eq w hx0, div_lt_iff₀ hρ, e]
  exact hinv

/-- **Cas bas** : au-delà d'une abscisse, la Tour d'un zéro sous la ligne est sous le rayon ON de
toute hauteur `U`, et celle de son miroir au-dessus du rayon ON de toute hauteur `Te`. Aucun des deux
n'est dans l'anneau ; aucun énoncé compilé n'impose qu'ils y soient. -/
theorem low_case_pair_leaves_ring (l : TrueZero) (hl : rZeroRadialPosition l.1 < 1 / 2) (Te U : ℝ) :
    ∃ X : ℝ, 0 < X ∧ ∀ x : ℝ, X ≤ x →
      normalizedRadius l x < onRadius U ∧ onRadius Te < normalizedRadius (mirrorMember l) x := by
  obtain ⟨X₁, hX₁, h₁⟩ := low_member_radius_below l hl (onRadius_pos U)
  obtain ⟨X₂, _, h₂⟩ := high_member_radius_exceeds (mirrorMember l)
    (by rw [mirrorMember_radial]; linarith) (onRadius Te)
  exact ⟨max X₁ X₂, lt_max_of_lt_left hX₁, fun x hx =>
    ⟨h₁ x ((le_max_left _ _).trans hx), h₂ x ((le_max_right _ _).trans hx)⟩⟩

/-! ## 9. Événement supplémentaire depuis un départ engagé : la restriction géométrique démontrée -/

/-- Partie réelle au plus un demi ⟹ la phase est au moins la phase de ligne. -/
theorem linePhase_le_phase_of_le_half (z : TrueZero) (h : rZeroRadialPosition z.1 ≤ 1 / 2) :
    linePhase (rZeroHeight z.1) ≤ (towerMotionOf z).phase := by
  rcases h.lt_or_eq with h | h
  · exact ((linePhase_lt_phase_iff z).mpr h).le
  · exact le_of_eq (by unfold linePhase; rw [towerMotion_phase, h])

/-- **Ce que l'événement supplémentaire impose à la Tour suivante**, sur un passage où la hauteur
avance vers un zéro de partie réelle au plus un demi (les deux sont acquis depuis un départ engagé) :
rang `+ 1` ; premier partagé ; intervalle logarithmique strictement réduit ; phase dans la fenêtre
`[phase de ligne, phase de ligne + 1/(2T_l)[` ; tous les contacts = contacts de ligne à la nouvelle
hauteur, multipliés par UN facteur `λ` avec `1 ≤ λ < e^{1/(2T_l²)}`. La restriction est démontrée ;
il reste un seul paramètre, `λ`, et `λ = 1` ⟺ zéro suivant en ligne (`radialFactor_eq_one_iff`) :
ce dernier point n'est pas dérivé. -/
theorem engaged_event_restriction (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember)
    (hT : rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember)
    (hLe : rZeroRadialPosition p.zLaterMember ≤ 1 / 2) :
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
    expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ = occurrence ⟨p.zLaterMember, hL⟩ ∧
    towerPitch ⟨p.zLaterMember, hL⟩ < towerPitch ⟨p.zEarlierMember, hE⟩ ∧
    linePhase (rZeroHeight p.zLaterMember) ≤ (towerMotionOf ⟨p.zLaterMember, hL⟩).phase ∧
    (towerMotionOf ⟨p.zLaterMember, hL⟩).phase - linePhase (rZeroHeight p.zLaterMember) <
      1 / (2 * rZeroHeight p.zLaterMember) ∧
    1 ≤ radialFactor ⟨p.zLaterMember, hL⟩ ∧
    radialFactor ⟨p.zLaterMember, hL⟩ <
      Real.exp (1 / (2 * rZeroHeight p.zLaterMember) / rZeroHeight p.zLaterMember) ∧
    ∀ k : ℤ, contactMinusAt ⟨p.zLaterMember, hL⟩ k =
      lineContact (rZeroHeight p.zLaterMember) k * radialFactor ⟨p.zLaterMember, hL⟩ := by
  have hle := linePhase_le_phase_of_le_half ⟨p.zLaterMember, hL⟩ hLe
  have hline : linePhase (rZeroHeight p.zLaterMember) =
      Real.arctan (2 * rZeroHeight p.zLaterMember) := by
    unfold linePhase
    congr 1
    ring
  have hwin := phase_window_width_lt (T := 2 * rZeroHeight p.zLaterMember) (by linarith)
  have hlt : (towerMotionOf ⟨p.zLaterMember, hL⟩).phase - linePhase (rZeroHeight p.zLaterMember) <
      1 / (2 * rZeroHeight p.zLaterMember) := by
    have := towerMotion_phase_lt_pi_div_two ⟨p.zLaterMember, hL⟩
    rw [hline]
    linarith
  refine ⟨eventIndex_succ_of_passage p hE, expectedMinimumPrime_eq_laterOccurrence p hE hL,
    (vertical_iff_pitch_contracts p hE hL).mp hT, hle, hlt, ?_, ?_,
    fun k => contact_eq_line_mul_radial _ k⟩
  · exact Real.one_le_exp (div_nonneg (sub_nonneg.mpr hle) hL.le)
  · exact Real.exp_lt_exp.mpr (div_lt_div_of_pos_right hlt hL)

/-! ## 10. Le renouvellement de la contraction n'est pas porté par les contrats de paramètres

Fenêtre de paramètres `e = (1/2, T_e)`, `l = (1/2 − d, T)`, `s = (1/2 + d, T)`, `T_e < T`, pour TOUT
`d ∈ ]0, 1/2[` : la première contraction tient, la seconde hauteur est gardée, et tous les contrats qui
ne lisent que les parties réelles et les hauteurs des trois membres sont satisfaits. Énoncé sur des
paramètres : il ne dit pas qu'une telle fenêtre existe parmi les zéros. -/

/-- Emboîtement à l'infini des contacts : toute Tour de phase sous un quart de tour, plus haute,
a ses contacts d'indice `≥ T_e/(T − T_e)` en deçà de ceux de la Tour de ligne à `T_e`. -/
theorem windingContact_nested_at_infinity {β Te T k : ℝ} (hTe : 0 < Te) (h1 : Te < T)
    (hk : Te / (T - Te) ≤ k) : windingContact β T k < windingContact (1 / 2) Te k := by
  have hT : 0 < T := hTe.trans h1
  have hgap : 0 < T - Te := sub_pos.mpr h1
  have hk' : Te ≤ k * (T - Te) := (div_le_iff₀ hgap).mp hk
  have hφ := Real.arctan_lt_pi_div_two (T / β)
  have hφe : 0 < Real.arctan (Te / (1 / 2)) := Real.arctan_pos.mpr (by positivity)
  have h3 : Real.arctan (T / β) * Te < Real.pi * Te :=
    mul_lt_mul_of_pos_right (by linarith [Real.pi_pos]) hTe
  have h4 : Real.pi * Te ≤ Real.pi * (k * (T - Te)) := mul_le_mul_of_nonneg_left hk' Real.pi_pos.le
  have h5 : 0 < Real.arctan (Te / (1 / 2)) * T := mul_pos hφe hT
  unfold windingContact
  apply Real.exp_lt_exp.mpr
  rw [div_lt_div_iff₀ hT hTe]
  nlinarith

/-- **La fenêtre `ON → bas → même hauteur` satisfait tous les contrats de paramètres, pour tout `d`.**
Première contraction ; phase du membre bas dans la fenêtre au-dessus de la phase de ligne ; contacts
= contacts de ligne × un facteur ; second membre miroir, à la même hauteur, contacts strictement en
deçà ; emboîtement à l'infini des deux dans la Tour engagée ; enveloppe haute du rayon. Aucun de ces
contrats n'exige que le passage quittant le membre atteint monte. -/
theorem renewal_not_forced_by_parameters {Te T d : ℝ} (hTe : 0 < Te) (h1 : Te < T) (hd : 0 < d)
    (hd1 : d < 1 / 2) :
    Real.pi / T < Real.pi / Te ∧
    Real.arctan (2 * T) < Real.arctan (T / (1 / 2 - d)) ∧
    Real.arctan (T / (1 / 2 - d)) - Real.arctan (2 * T) < 1 / (2 * T) ∧
    (∀ k : ℝ, windingContact (1 / 2 - d) T k = windingContact (1 / 2) T k *
      Real.exp ((Real.arctan (T / (1 / 2 - d)) - Real.arctan (T / (1 / 2))) / T)) ∧
    (1 / 2 - d) + (1 / 2 + d) = 1 ∧
    (∀ k : ℝ, windingContact (1 / 2 + d) T k < windingContact (1 / 2 - d) T k) ∧
    (∀ k : ℝ, Te / (T - Te) ≤ k → windingContact (1 / 2 - d) T k < windingContact (1 / 2) Te k ∧
      windingContact (1 / 2 + d) T k < windingContact (1 / 2) Te k) ∧
    (∀ x : ℝ, 1 ≤ x → x ^ ((1 / 2 - d) - 1 / 2) / Real.sqrt ((1 / 2 - d) ^ 2 + T ^ 2) < 1 / T) := by
  have hT : 0 < T := hTe.trans h1
  have hlo : 0 < 1 / 2 - d := by linarith
  have e2 : 2 * T = T / (1 / 2) := by ring
  have hmono : T / (1 / 2) < T / (1 / 2 - d) := div_lt_div_of_pos_left hT hlo (by linarith)
  have hwin := phase_window_width_lt (T := 2 * T) (by linarith)
  have hhalf := Real.arctan_lt_pi_div_two (T / (1 / 2 - d))
  refine ⟨div_lt_div_of_pos_left Real.pi_pos hTe h1, ?_, by linarith, fun k => ?_, by ring,
    fun k => windingContact_lt_of_radial_lt hlo (by linarith) hT,
    fun k hk => ⟨windingContact_nested_at_infinity hTe h1 hk,
      windingContact_nested_at_infinity hTe h1 hk⟩, fun x hx => ?_⟩
  · rw [e2]
    exact Real.arctan_strictMono hmono
  · unfold windingContact
    rw [← Real.exp_add]
    congr 1
    ring
  · have hs : T < Real.sqrt ((1 / 2 - d) ^ 2 + T ^ 2) :=
      (Real.lt_sqrt hT.le).mpr (by nlinarith [sq_pos_of_pos hlo])
    calc x ^ ((1 / 2 - d) - 1 / 2) / Real.sqrt ((1 / 2 - d) ^ 2 + T ^ 2)
        ≤ 1 / Real.sqrt ((1 / 2 - d) ^ 2 + T ^ 2) :=
          div_le_div_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith))
            (Real.sqrt_nonneg _)
      _ < 1 / T := one_div_lt_one_div_of_lt hT hs

#print axioms renewal_not_forced_by_parameters
#print axioms engaged_event_restriction
#print axioms consecutive_ring_interior_empty
#print axioms radius_envelope_of_le_half
#print axioms radius_le_ring_top_of_gap
#print axioms radius_floor_on_finite_domain
#print axioms radius_dominated_iff_gap
#print axioms radius_dominated_axis_iff
#print axioms low_member_not_dominated_on_axis
#print axioms onRadii_small_iff_onHeights_unbounded
#print axioms certified_three_onRadii
#print axioms onLine_zeroTerm_at_own_contact
#print axioms cross_position_at_contact
#print axioms cross_advance_between_contacts
#print axioms radius_step_between_contacts
#print axioms radius_step_eq_one_iff
#print axioms onLine_residueTerm_at_own_contact
#print axioms low_case_pair_leaves_ring

end RHV6Fresh
