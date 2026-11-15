/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CanonicalEnumeration
import RHV6Fresh.Terminal.MirrorPairExactSum

/-!
# Déduction structurelle de l'ancre ON (auteur, 2026-10-08, directive en six points, point 1)

Ce module sépare la **déduction structurelle** (compilée ici, sous une hypothèse d'unicité explicitement
nommée) de la **certification analytique** de cette hypothèse (E185, Arb, hors Lean ; obligation 1 de la chaîne
unique `Terminal/DemonstrationChain.lean`).

Hypothèse nommée : `hU : ∃! w : TrueZero, rZeroHeight w.1 ≤ 15` (un seul membre de la moitié supérieure dans la
bande de hauteur au plus quinze). Déduction :
1. le miroir de ce membre est dans la même bande (il conserve sa hauteur, `mirrorMember_ordinate`) ;
2. l'unicité impose `mirrorMember w = w` ;
3. `mirrorMember_radial` impose `β_w = 1/2` ;
4. aucun membre supérieur ne le précède (un prédécesseur aurait une hauteur au plus quinze) ;
5. l'ordre canonique (`canonicalMember_zero_precedes`) identifie ce membre à `canonicalZero 1`.

Conclusion : `rZeroRadialPosition (canonicalZero 1).1 = 1/2` (`anchor_of_unique_band`).

Raccord au comptage avec multiplicité : `upperCountWithMultiplicity T` (somme des multiplicités analytiques des
zéros non triviaux de hauteur `0 < T_ρ ≤ T`) ; un comptage égal à un donne l'existence et l'unicité
(`unique_band_of_count_one`), donc l'ancre (`anchor_of_count_one`). Les conventions aux frontières sont
explicitées (`upperCount_open_le_closed`, `upperCount_closed_eq_open_of_no_boundary`) ; l'équivalence entre les
points comptés et `TrueZero` est `mem_upperWindow_iff`.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau ; la valeur `upperCountWithMultiplicity 15 = 1` n'est PAS
démontrée ici (certification externe seulement).
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Déduction structurelle sous l'unicité dans la bande -/

/-- **(1) Le miroir reste dans la bande** : il conserve la hauteur. -/
theorem mirror_mem_band {T : ℝ} {w : TrueZero} (hw : rZeroHeight w.1 ≤ T) :
    rZeroHeight (mirrorMember w).1 ≤ T := by
  rw [mirrorMember_ordinate]; exact hw

/-- **(2) L'unicité impose que le membre soit son propre miroir.** -/
theorem mirror_eq_self_of_unique_band {T : ℝ} (hU : ∃! w : TrueZero, rZeroHeight w.1 ≤ T)
    {w : TrueZero} (hw : rZeroHeight w.1 ≤ T) : mirrorMember w = w := by
  obtain ⟨u, _, huniq⟩ := hU
  exact (huniq _ (mirror_mem_band hw)).trans (huniq _ hw).symm

/-- **(3) Son propre miroir ⟹ position radiale un demi** (`mirrorMember_radial`). -/
theorem onLine_of_mirror_eq_self {w : TrueZero} (h : mirrorMember w = w) :
    rZeroRadialPosition w.1 = 1 / 2 := by
  have := mirrorMember_radial w
  rw [h] at this
  linarith

/-- **(2)+(3) : le membre unique de la bande est en ligne.** -/
theorem onLine_of_unique_band {T : ℝ} (hU : ∃! w : TrueZero, rZeroHeight w.1 ≤ T)
    {w : TrueZero} (hw : rZeroHeight w.1 ≤ T) : rZeroRadialPosition w.1 = 1 / 2 :=
  onLine_of_mirror_eq_self (mirror_eq_self_of_unique_band hU hw)

/-- Un membre qui en précède un autre a une hauteur au plus égale. -/
theorem height_le_of_precedes {u w : TrueZero} (h : PZeroMemberPrecedes u.1 w.1) :
    rZeroHeight u.1 ≤ rZeroHeight w.1 := by
  rw [thm_zeroMemberPrecedes_iff_height_radial_lex] at h
  rcases h with h | h
  · exact h.le
  · exact h.1.le

/-- **(4) Aucun membre supérieur ne précède le membre unique de la bande** : un prédécesseur aurait une
hauteur au plus `T`, il serait lui-même dans la bande, donc égal à ce membre, et se précéderait. -/
theorem no_predecessor_of_unique_band {T : ℝ} (hU : ∃! w : TrueZero, rZeroHeight w.1 ≤ T)
    {w : TrueZero} (hw : rZeroHeight w.1 ≤ T) (u : TrueZero) : ¬ PZeroMemberPrecedes u.1 w.1 := by
  intro hprec
  obtain ⟨v, _, huniq⟩ := hU
  have hu : rZeroHeight u.1 ≤ T := (height_le_of_precedes hprec).trans hw
  have : u = w := (huniq _ hu).trans (huniq _ hw).symm
  subst this
  exact thm_zeroMemberPrecedes_irreflexive _ hprec

/-- **(5) Le membre unique de la bande est le premier membre canonique** : sinon `canonicalZero 1` le
précéderait (`canonicalMember_zero_precedes`), ce que (4) interdit. -/
theorem unique_band_eq_canonical_one {T : ℝ} (hU : ∃! w : TrueZero, rZeroHeight w.1 ≤ T)
    {w : TrueZero} (hw : rZeroHeight w.1 ≤ T) : canonicalZero 1 = w := by
  by_contra hne
  have hprec := canonicalMember_zero_precedes w (fun h => hne (by rw [canonicalZero_one, h]))
  exact no_predecessor_of_unique_band hU hw _ hprec

/-- **Ancre structurellement déduite** : sous l'unicité d'un membre supérieur de hauteur au plus quinze, le
premier membre canonique est sur la ligne. L'hypothèse `hU` est nommée ; elle n'est pas démontrée ici. -/
theorem anchor_of_unique_band (hU : ∃! w : TrueZero, rZeroHeight w.1 ≤ 15) :
    rZeroRadialPosition (canonicalZero 1).1 = 1 / 2 := by
  obtain ⟨w, hw, -⟩ := id hU
  rw [unique_band_eq_canonical_one hU hw]
  exact onLine_of_unique_band hU hw

/-- Même déduction pour toute hauteur de bande `T` (le seuil quinze n'y joue aucun rôle). -/
theorem anchor_of_unique_band_any {T : ℝ} (hU : ∃! w : TrueZero, rZeroHeight w.1 ≤ T) :
    rZeroRadialPosition (canonicalZero 1).1 = 1 / 2 := by
  obtain ⟨w, hw, -⟩ := id hU
  rw [unique_band_eq_canonical_one hU hw]
  exact onLine_of_unique_band hU hw

/-- Sous la même hypothèse, le premier membre canonique est de hauteur au plus quinze et est son propre
miroir. -/
theorem canonical_one_of_unique_band (hU : ∃! w : TrueZero, rZeroHeight w.1 ≤ 15) :
    rZeroHeight (canonicalZero 1).1 ≤ 15 ∧ mirrorMember (canonicalZero 1) = canonicalZero 1 := by
  obtain ⟨w, hw, -⟩ := id hU
  rw [unique_band_eq_canonical_one hU hw]
  exact ⟨hw, mirror_eq_self_of_unique_band hU hw⟩

/-! ## 2. Comptage avec multiplicité et raccord à l'unicité -/

/-- Les points-zéros de la moitié supérieure de hauteur au plus `T` (convention fermée `T_ρ ≤ T`), comme
`Finset` : la fenêtre symétrique de `rhv3_lean` filtrée par `0 < Im`. -/
noncomputable def upperWindow (T : ℝ) : Finset ℂ :=
  (finsetSymmetricZeroWindow T).filter fun ρ => 0 < ρ.im

theorem mem_upperWindow {T : ℝ} {ρ : ℂ} :
    ρ ∈ upperWindow T ↔ PIsNonTrivialZetaZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
  unfold upperWindow
  rw [Finset.mem_filter, thm_mem_finsetSymmetricZeroWindow]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h3, (le_abs_self _).trans h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, by rw [abs_of_pos h2]; exact h3⟩, h2⟩

/-- **Équivalence entre les points comptés et `TrueZero`** : un point est dans la fenêtre supérieure ⟺ c'est le
support d'un membre supérieur de hauteur au plus `T`. -/
theorem mem_upperWindow_iff {T : ℝ} {ρ : ℂ} :
    ρ ∈ upperWindow T ↔ ∃ w : TrueZero, zeroPoint w = ρ ∧ rZeroHeight w.1 ≤ T := by
  rw [mem_upperWindow]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨⟨ρ, h1⟩, h2⟩, rfl, h3⟩
  · rintro ⟨w, rfl, hw⟩
    exact ⟨w.1.2, w.2, hw⟩

/-- **Comptage avec multiplicité** : somme des multiplicités analytiques sur la fenêtre supérieure fermée. -/
noncomputable def upperCountWithMultiplicity (T : ℝ) : ℕ :=
  ∑ ρ ∈ upperWindow T, zetaZeroMultiplicity ρ

/-- Chaque point compté a une multiplicité au moins un. -/
theorem one_le_multiplicity_of_mem_upperWindow {T : ℝ} {ρ : ℂ} (h : ρ ∈ upperWindow T) :
    1 ≤ zetaZeroMultiplicity ρ :=
  zetaZeroMultiplicity_pos (mem_upperWindow.mp h).1.1

/-- Le nombre de points comptés est au plus le comptage avec multiplicité. -/
theorem upperWindow_card_le_count (T : ℝ) : (upperWindow T).card ≤ upperCountWithMultiplicity T := by
  unfold upperCountWithMultiplicity
  have := Finset.card_nsmul_le_sum (upperWindow T) zetaZeroMultiplicity 1
    fun ρ hρ => one_le_multiplicity_of_mem_upperWindow hρ
  simpa using this

/-- **Un comptage égal à un donne l'existence et l'unicité du membre dans la bande** (et sa simplicité). -/
theorem unique_band_of_count_one {T : ℝ} (h : upperCountWithMultiplicity T = 1) :
    ∃! w : TrueZero, rZeroHeight w.1 ≤ T := by
  have hcard : (upperWindow T).card ≤ 1 := by
    have := upperWindow_card_le_count T; omega
  have hne : (upperWindow T).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    unfold upperCountWithMultiplicity at h
    rw [he, Finset.sum_empty] at h
    exact one_ne_zero h.symm
  have hone : (upperWindow T).card = 1 := le_antisymm hcard (Finset.one_le_card.mpr hne)
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
  have hmem : a ∈ upperWindow T := by rw [ha]; exact Finset.mem_singleton_self a
  obtain ⟨w, hwa, hwT⟩ := mem_upperWindow_iff.mp hmem
  refine ⟨w, hwT, fun v hv => ?_⟩
  have hv' : zeroPoint v ∈ upperWindow T := mem_upperWindow_iff.mpr ⟨v, rfl, hv⟩
  rw [ha, Finset.mem_singleton] at hv'
  apply Subtype.ext; apply Subtype.ext
  show zeroPoint v = zeroPoint w
  rw [hv', hwa]

/-- Sous un comptage égal à un, le membre unique est simple. -/
theorem simple_of_count_one {T : ℝ} (h : upperCountWithMultiplicity T = 1) {w : TrueZero}
    (hw : rZeroHeight w.1 ≤ T) : zetaZeroMultiplicity (zeroPoint w) = 1 := by
  have hmem : zeroPoint w ∈ upperWindow T := mem_upperWindow_iff.mpr ⟨w, rfl, hw⟩
  unfold upperCountWithMultiplicity at h
  have hle : zetaZeroMultiplicity (zeroPoint w) ≤ 1 := by
    rw [← h]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  exact le_antisymm hle (one_le_multiplicity_of_mem_upperWindow hmem)

/-- **Ancre depuis le comptage** : `upperCountWithMultiplicity 15 = 1 ⟹ β(canonicalZero 1) = 1/2`. La valeur
du comptage est l'objet de la certification (E185, hors Lean) ; elle n'est pas démontrée ici. -/
theorem anchor_of_count_one (h : upperCountWithMultiplicity 15 = 1) :
    rZeroRadialPosition (canonicalZero 1).1 = 1 / 2 :=
  anchor_of_unique_band (unique_band_of_count_one h)

/-! ## 3. Conventions aux frontières -/

/-- Fenêtre supérieure OUVERTE (`T_ρ < T`), convention de `nontrivialZetaZerosByHeightFinset` et de
`riemannZeta.N'`. -/
noncomputable def upperWindowOpen (T : ℝ) : Finset ℂ :=
  (finsetSymmetricZeroWindow T).filter fun ρ => 0 < ρ.im ∧ ρ.im < T

theorem mem_upperWindowOpen {T : ℝ} {ρ : ℂ} :
    ρ ∈ upperWindowOpen T ↔ PIsNonTrivialZetaZero ρ ∧ 0 < ρ.im ∧ ρ.im < T := by
  unfold upperWindowOpen
  rw [Finset.mem_filter, thm_mem_finsetSymmetricZeroWindow]
  constructor
  · rintro ⟨⟨h1, _⟩, h3, h4⟩
    exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, by rw [abs_of_pos h2]; exact h3.le⟩, h2, h3⟩

theorem upperWindowOpen_subset (T : ℝ) : upperWindowOpen T ⊆ upperWindow T := by
  intro ρ h
  rw [mem_upperWindowOpen] at h
  exact mem_upperWindow.mpr ⟨h.1, h.2.1, h.2.2.le⟩

/-- Comptage ouvert `≤` comptage fermé. -/
theorem upperCount_open_le_closed (T : ℝ) :
    ∑ ρ ∈ upperWindowOpen T, zetaZeroMultiplicity ρ ≤ upperCountWithMultiplicity T :=
  Finset.sum_le_sum_of_subset_of_nonneg (upperWindowOpen_subset T) fun _ _ _ => Nat.zero_le _

/-- **Sans zéro exactement à la hauteur `T`**, les deux conventions coïncident. -/
theorem upperCount_closed_eq_open_of_no_boundary {T : ℝ}
    (hB : ∀ ρ : ℂ, PIsNonTrivialZetaZero ρ → ρ.im ≠ T) :
    upperCountWithMultiplicity T = ∑ ρ ∈ upperWindowOpen T, zetaZeroMultiplicity ρ := by
  unfold upperCountWithMultiplicity
  congr 1
  ext ρ
  rw [mem_upperWindow, mem_upperWindowOpen]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, lt_of_le_of_ne h3 (hB ρ h1)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3.le⟩

/-- Le comptage est croissant en la hauteur de coupure. -/
theorem upperCount_mono {T U : ℝ} (h : T ≤ U) :
    upperCountWithMultiplicity T ≤ upperCountWithMultiplicity U := by
  unfold upperCountWithMultiplicity
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
  intro ρ hρ
  rw [mem_upperWindow] at hρ ⊢
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.trans h⟩

end RHV6Fresh

#print axioms RHV6Fresh.anchor_of_unique_band
#print axioms RHV6Fresh.anchor_of_count_one
#print axioms RHV6Fresh.unique_band_of_count_one
#print axioms RHV6Fresh.mem_upperWindow_iff
#print axioms RHV6Fresh.upperCount_closed_eq_open_of_no_boundary
#print axioms RHV6Fresh.simple_of_count_one
#print axioms RHV6Fresh.mirror_eq_self_of_unique_band
#print axioms RHV6Fresh.no_predecessor_of_unique_band
#print axioms RHV6Fresh.unique_band_eq_canonical_one
#print axioms RHV6Fresh.upperCount_open_le_closed
