/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.RhGapPort.PrimesDetermineZeros
import RHV6Fresh.Terminal.FrequencyCap
import RHV6Fresh.Terminal.CollectiveContactRigidity

/-!
# Raccordement : détermination universelle × CAP de fréquence × contacts × foules (directive R11, 2026-11-01)

Module isolé (non ajouté à `RHV6Fresh.lean`, chaîne intacte). Il ne pose aucune hypothèse : il compose des théorèmes
acquis, chacun cité par son nom Lean, et consigne ce que la composition donne et ce qu'elle ne donne pas.

Théorèmes composés (voir `audits_compilation/prime_caps_contacts_bridge/REPORT.md` pour la table de dépendances) :
* détermination universelle (port `RhGapPort/PrimesDetermineZeros.lean`) :
  `primes_determine_zeta_meromorphic_continuation`, `primes_determine_nontrivial_zero_multiset`,
  `prime_determined_zero_window_eq_canonical_any_length`, `riemannZeta_isPrimeDetermined`, `primeDetermined_unique` ;
* CAP (`FrequencyCap.lean`) : `height_le_iff_card`, `lower_cap`, `upper_cap`, `caps_count_off_pairs_twice`,
  `contact_interval_ge_of_height_le`, `contact_interval_lt_of_lt_height`, `upperCount_eq_Ncount`, `Ncount_nat_le` ;
* contacts (`CollectiveContactRigidity.lean`, `GapContactRegimes.lean`) : `contactLog_step`, `coordinates_from_two_contacts`,
  `mem_crowd_iff_height_le`, `crowd_rank_iff`, `contactsCrossed_le_one_of_mem_crowd`, `crowd_tail_decomposition`,
  `collective_residual_bound`, `every_zero_in_some_crowd` (désormais sans hypothèse) ;
* comptage (`CountingDeficit.lean`, `AnchorStructure.lean`) : `upperWindow_card_le_count`, `upperCount_eq_on_add_two_low`.

## 1. Ce que la détermination universelle rend aux objets de RHV6Fresh
Toute continuation `F` déterminée par les premiers a pour zéros de bande exactement les vrais zéros (`TrueZero`) ; la
fenêtre fermée `upperWindow T`, la foule de chaque écart, le comptage avec multiplicité, les coordonnées `(β, T)` de
chaque membre canonique et ses contacts sont des fonctions de `F` seule (§1). La classe des `F` admissibles est réduite
à `ζ` hors du pôle (`primeDetermined_unique`) : **toute propriété des zéros de `F` est une propriété des zéros de `ζ`,
et réciproquement** (`primeDetermined_property_iff`). En particulier « `F` a un zéro bas » ⟺ « RH est fausse »
(`primeDetermined_lowZero_iff_not_riemannHypothesis`). La détermination transporte la question radiale exactement ;
elle ne la tranche pas : aucun énoncé de ce module ne déduit `β` de `F` autrement que par identité.

## 2. CAP × contacts (membre canonique de rang `k+1`)
Le pas de contact `log(C_{k,j+1}/C_{k,j}) = π/T_k` est encadré par les deux CAP : `lower_cap_contact_interval` (pas
strictement sous `π/n` dès que `n·A₀·log(n+3) < k+1`), `upper_cap_contact_interval` (pas au moins `π/(2T)` sous la
condition de Riemann–von Mangoldt). Les deux CAP et le pas sont aveugles à `β` : une paire OFF/miroir a même hauteur,
même pas, mêmes foules, et entre deux fois dans le comptage plafonné (`OffCarrier.pair_blind_to_caps_and_steps`,
`OffCarrier.pair_counted_twice`).

## 3. CAP × foules
Taille de la foule capée par la longueur de l'écart (`crowd_card_cap`) ; rang garanti dans la foule sous le plafond
(`crowd_contains_rank_of_upper_cap`) ; nombre total de contacts traversés par toute famille de membres de la foule
borné par la taille de la foule (`crowd_family_contacts_le`), donc capé (`crowd_family_contacts_cap`) ; transitions de
foule entre deux écarts bornées par le comptage local (`window_sdiff_card_le_Ncount`, `crowd_transition_cap`) ; membres
de queue par fenêtre unité bornés de même (`tail_unit_window_cap`). Tout cela vaut pour toute position radiale.

## 4. Ce qui n'est pas obtenu
Aucune de ces compositions ne lit `β` : voir §5 (« ce que la composition ne contraint pas ») et la sonde hors build
`ProbePrimeCapsContactsBridge.lean`. Le but exact laissé par Lean est consigné dans `REPORT.md`.
-/

namespace RHV6Fresh

open RHV3Lean Finset RhGap

/-! ## 1. Détermination universelle → objets de RHV6Fresh -/

section Determination

variable {F : ℂ → ℂ} (hF : IsPrimeDeterminedZetaContinuation F)
include hF

/-- Hors du pôle, `F` et `ζ` s'annulent aux mêmes points. -/
theorem primeDetermined_zero_iff {ρ : ℂ} (hρ : ρ ≠ 1) : F ρ = 0 ↔ riemannZeta ρ = 0 := by
  rw [primes_determine_zeta_meromorphic_continuation F hF (by simpa using hρ)]

/-- **Les zéros de bande de `F` sont exactement les vrais zéros** (`PIsNonTrivialZetaZero`, objet-source de
`rhv3_lean`). -/
theorem primeDetermined_strip_iff (ρ : ℂ) : (F ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) ↔ PIsNonTrivialZetaZero ρ := by
  have hne : ρ.re < 1 → ρ ≠ 1 := fun h1 h => by rw [h, Complex.one_re] at h1; exact lt_irrefl _ h1
  constructor
  · rintro ⟨hz, h0, h1⟩
    exact ⟨(primeDetermined_zero_iff hF (hne h1)).mp hz, h0, h1⟩
  · rintro ⟨hz, h0, h1⟩
    exact ⟨(primeDetermined_zero_iff hF (hne h1)).mpr hz, h0, h1⟩

/-- **La fenêtre fermée de RHV6Fresh est l'ensemble des zéros de bande de `F` de hauteur dans `]0, T]`.** -/
theorem primeDetermined_upperWindow (T : ℝ) :
    ((upperWindow T : Finset ℂ) : Set ℂ) = {ρ | F ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T} := by
  ext ρ
  rw [Finset.mem_coe, mem_upperWindow, Set.mem_ofPred_eq, ← primeDetermined_strip_iff hF]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨h1, h2, h3⟩, h4, h5⟩

/-- **La foule de chaque écart est lue dans `F`** : zéros de bande de `F` de hauteur au plus `π/ℓ`. -/
theorem primeDetermined_crowd (I : PrimeGapInterval) :
    ((crowd I : Finset ℂ) : Set ℂ) =
      {ρ | F ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ I.threshold} := by
  rw [crowd_eq_upperWindow_threshold]
  exact primeDetermined_upperWindow hF I.threshold

/-- Chaque membre canonique est un zéro de `F`. -/
theorem primeDetermined_canonicalMember_zero (k : ℕ) : F (zeroPoint (canonicalMember k)) = 0 :=
  ((primeDetermined_strip_iff hF _).mpr (canonicalMember k).1.2).1

/-- **Les deux coordonnées `(β_k, T_k)` du membre canonique sont un zéro de `F`** : la constellation complète
(positions radiales comprises) est déterminée par `F`, donc par les premiers. -/
theorem primeDetermined_coordinates (k : ℕ) :
    F (↑(rZeroRadialPosition (canonicalMember k).1) + ↑(rZeroHeight (canonicalMember k).1) * Complex.I) = 0 := by
  have h : (↑(rZeroRadialPosition (canonicalMember k).1) + ↑(rZeroHeight (canonicalMember k).1) * Complex.I : ℂ)
      = zeroPoint (canonicalMember k) := Complex.re_add_im _
  rw [h]
  exact primeDetermined_canonicalMember_zero hF k

/-- Sur la fenêtre, l'ordre analytique de `F` est la multiplicité du corpus. -/
theorem primeDetermined_mult_of_mem {T : ℝ} {ρ : ℂ} (h : ρ ∈ upperWindow T) :
    analyticOrderNatAt F ρ = zetaZeroMultiplicity ρ :=
  (primes_determine_nontrivial_zero_multiset F hF).2 ρ
    ((isNontrivialZetaZero_iff_strip ρ).mpr (mem_upperWindow.mp h).1)

/-- **Le comptage avec multiplicité, objet des CAP, est le comptage des ordres de `F`.** -/
theorem primeDetermined_upperCount (T : ℝ) :
    upperCountWithMultiplicity T = ∑ ρ ∈ upperWindow T, analyticOrderNatAt F ρ :=
  Finset.sum_congr rfl (fun ρ h => (primeDetermined_mult_of_mem hF h).symm)

/-- **Toute propriété de `F` invariante hors du pôle est une propriété de `ζ`** : la détermination transporte, elle
ne discrimine pas. -/
theorem primeDetermined_property_iff (P : (ℂ → ℂ) → Prop)
    (hP : ∀ G₁ G₂ : ℂ → ℂ, Set.EqOn G₁ G₂ (({1} : Set ℂ)ᶜ) → (P G₁ ↔ P G₂)) : P F ↔ P riemannZeta :=
  hP F riemannZeta (primes_determine_zeta_meromorphic_continuation F hF)

/-- **« `F` a un zéro bas » ⟺ « RH est fausse ».** La question radiale est transportée exactement. -/
theorem primeDetermined_lowZero_iff_not_riemannHypothesis :
    (∃ ρ : ℂ, F ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.re < 1 / 2) ↔ ¬ RiemannHypothesis := by
  rw [riemannHypothesis_iff_noLowerSide]
  push Not
  constructor
  · rintro ⟨ρ, hz, h0, h1, him, hlow⟩
    exact ⟨⟨⟨ρ, (primeDetermined_strip_iff hF ρ).mp ⟨hz, h0, h1⟩⟩, him⟩, hlow⟩
  · rintro ⟨z, hz⟩
    obtain ⟨h1, h2, h3⟩ := (primeDetermined_strip_iff hF _).mpr z.1.2
    exact ⟨zeroPoint z, h1, h2, h3, z.2, hz⟩

/-- Même énoncé en termes de porteur OFF (`OffCarrier`). -/
theorem primeDetermined_lowZero_iff_offCarrier :
    (∃ ρ : ℂ, F ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.re < 1 / 2) ↔ Nonempty OffCarrier := by
  rw [primeDetermined_lowZero_iff_not_riemannHypothesis hF]
  constructor
  · exact exists_offCarrier_of_not_riemannHypothesis
  · rintro ⟨C⟩ hRH
    exact no_offCarrier_of_riemannHypothesis hRH C

end Determination

/-! ## 2. CAP × contacts -/

/-- **Plancher × contacts** : si `n·A₀·log(n+3) < k+1`, chaque pas de contact du membre de rang `k+1` est strictement
sous `π/n`. -/
theorem lower_cap_contact_interval : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (k n : ℕ) (j : ℤ), 0 < n →
    (n : ℝ) * (A₀ * Real.log (n + 3)) < k + 1 →
    Real.log (contactMinusAt (canonicalMember k) (j + 1) / contactMinusAt (canonicalMember k) j) < Real.pi / n := by
  obtain ⟨A₀, hA1, hA⟩ := lower_cap
  refine ⟨A₀, hA1, fun k n j hn hlt => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact contact_interval_lt_of_lt_height hn' (hA k n hlt) j

/-- Même plancher lu sur le pas de la Tour. -/
theorem lower_cap_pitch : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (k n : ℕ), 0 < n →
    (n : ℝ) * (A₀ * Real.log (n + 3)) < k + 1 → towerPitch (canonicalMember k) < Real.pi / n := by
  obtain ⟨A₀, hA1, hA⟩ := lower_cap
  refine ⟨A₀, hA1, fun k n hn hlt => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold towerPitch
  exact div_lt_div_of_pos_left Real.pi_pos hn' (hA k n hlt)

/-- **Plafond × contacts** : sous la condition de Riemann–von Mangoldt, chaque pas de contact du membre de rang `k+1`
est au moins `π/(2T)`. -/
theorem upper_cap_contact_interval : ∃ C T₀ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ (k : ℕ) (T : ℝ) (j : ℤ), T₀ ≤ T → 1 ≤ T →
    ((k : ℝ) + 1) * (A₀ * Real.log (2 * T + 3)) < T / (2 * Real.pi) * Zeta23.ell1 T - C * Real.log T →
    Real.pi / (2 * T) ≤
      Real.log (contactMinusAt (canonicalMember k) (j + 1) / contactMinusAt (canonicalMember k) j) := by
  obtain ⟨C, T₀, A₀, hA0, h⟩ := upper_cap
  exact ⟨C, T₀, A₀, hA0, fun k T j hT0 hT1 hlt => contact_interval_ge_of_height_le (h k T hT0 hT1 hlt) j⟩

namespace OffCarrier

variable (C : OffCarrier)

/-- **La paire OFF/membre sortant est indiscernable par les CAP et par les pas** : même hauteur, même pas, mêmes
foules, mêmes pas de contact. Seuls les contacts eux-mêmes (décalés, `pair_contacts_shifted`) et l'amplitude
lisent `β`. -/
theorem pair_blind_to_caps_and_steps :
    rZeroHeight C.outgoingMember.1 = rZeroHeight C.zero.1 ∧
    towerPitch C.outgoingMember = towerPitch C.zero ∧
    (∀ I : PrimeGapInterval, zeroPoint C.zero ∈ crowd I ↔ zeroPoint C.outgoingMember ∈ crowd I) ∧
    (∀ k : ℤ, contactLog C.outgoingMember (k + 1) - contactLog C.outgoingMember k
      = contactLog C.zero (k + 1) - contactLog C.zero k) := by
  have hT : rZeroHeight C.outgoingMember.1 = rZeroHeight C.zero.1 := C.outgoing_same_height
  refine ⟨hT, ?_, C.pair_same_crowds, fun k => contactLog_step_blind_to_radial hT k⟩
  unfold towerPitch
  rw [hT]

/-- **Le zéro OFF entre dans le comptage plafonné, et son miroir y entre une seconde fois** : sous tout plafond `a`
atteignant sa hauteur, `N(0,a] = N₀(a) + 2·W(a)` avec `W(a) ≥ 1`. -/
theorem pair_counted_twice {a : ℝ} (ha : rZeroHeight C.zero.1 ≤ a) :
    1 ≤ lowCount a ∧ Zeta23.Ncount 0 a = onCount a + 2 * lowCount a := by
  refine ⟨?_, caps_count_off_pairs_twice a⟩
  unfold lowCount
  have hmem : zeroPoint C.zero ∈ (upperWindow a).filter (fun ρ => ρ.re < 1 / 2) := by
    rw [Finset.mem_filter]
    exact ⟨mem_upperWindow_iff.mpr ⟨C.zero, rfl, ha⟩, C.zero_low⟩
  calc 1 ≤ zetaZeroMultiplicity (zeroPoint C.zero) := zetaZeroMultiplicity_pos C.zero.1.2.1
    _ ≤ _ := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem

end OffCarrier

/-! ## 3. CAP × foules -/

/-- La taille de la foule est au plus le comptage avec multiplicité au seuil. -/
theorem crowd_card_le_count (I : PrimeGapInterval) : (crowd I).card ≤ upperCountWithMultiplicity I.threshold := by
  rw [crowd_eq_upperWindow_threshold]
  exact upperWindow_card_le_count _

/-- **La taille de la foule est capée par la longueur de l'écart** : `|foule| ≤ ⌈π/ℓ⌉·A₀·log(⌈π/ℓ⌉+3)`,
inconditionnel (comptage local). -/
theorem crowd_card_cap : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ I : PrimeGapInterval,
    ((crowd I).card : ℝ) ≤ (⌈I.threshold⌉₊ : ℝ) * (A₀ * Real.log (⌈I.threshold⌉₊ + 3)) := by
  obtain ⟨A₀, hA1, hA⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨A₀, hA1, fun I => ?_⟩
  have h1 : (crowd I).card ≤ upperCountWithMultiplicity I.threshold := crowd_card_le_count I
  have h2 : upperCountWithMultiplicity I.threshold = Zeta23.Ncount 0 I.threshold := upperCount_eq_Ncount _
  have h3 : Zeta23.Ncount 0 I.threshold ≤ Zeta23.Ncount 0 (⌈I.threshold⌉₊ : ℝ) :=
    Zeta23.Ncount_mono le_rfl (Nat.le_ceil _)
  have h4 := Ncount_nat_le A₀ (by linarith) hA ⌈I.threshold⌉₊
  have h5 : ((crowd I).card : ℝ) ≤ (Zeta23.Ncount 0 (⌈I.threshold⌉₊ : ℝ) : ℝ) := by
    exact_mod_cast h1.trans (h2 ▸ h3)
  linarith

/-- **Rang garanti dans la foule sous le plafond** : si `2T ≤ π/ℓ` et la condition de Riemann–von Mangoldt tient au
rang `k`, le membre de rang `k+1` est dans la foule, qui compte donc au moins `k+1` points. -/
theorem crowd_contains_rank_of_upper_cap : ∃ C T₀ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ (I : PrimeGapInterval) (k : ℕ) (T : ℝ),
    T₀ ≤ T → 1 ≤ T → 2 * T ≤ I.threshold →
    ((k : ℝ) + 1) * (A₀ * Real.log (2 * T + 3)) < T / (2 * Real.pi) * Zeta23.ell1 T - C * Real.log T →
    zeroPoint (canonicalMember k) ∈ crowd I ∧ k + 1 ≤ (crowd I).card := by
  obtain ⟨C, T₀, A₀, hA0, h⟩ := upper_cap
  refine ⟨C, T₀, A₀, hA0, fun I k T hT0 hT1 hthr hlt => ?_⟩
  have hk : rZeroHeight (canonicalMember k).1 ≤ I.threshold := (h k T hT0 hT1 hlt).trans hthr
  refine ⟨(mem_crowd_iff_height_le I _).mpr hk, ?_⟩
  rw [crowd_eq_upperWindow_threshold]
  exact (height_le_iff_card k _).mp hk

/-- **Nombre de contacts admissibles** : toute famille de membres de la foule traverse en tout au plus autant de
contacts qu'elle a de membres, et elle n'a pas plus de membres que la foule. -/
theorem crowd_family_contacts_le (I : PrimeGapInterval) (S : Finset TrueZero)
    (hS : ∀ w ∈ S, zeroPoint w ∈ crowd I) :
    ∑ w ∈ S, contactsCrossed w I ≤ S.card ∧ S.card ≤ (crowd I).card := by
  constructor
  · have h := Finset.sum_le_card_nsmul S (fun w => contactsCrossed w I) 1
      (fun w hw => contactsCrossed_le_one_of_mem_crowd w I (hS w hw))
    simpa using h
  · refine Finset.card_le_card_of_injOn zeroPoint (fun w hw => hS w hw) ?_
    intro a _ b _ hab
    apply Subtype.ext; apply Subtype.ext; exact hab

/-- **Les contacts traversés par la foule sont capés par la longueur de l'écart.** -/
theorem crowd_family_contacts_cap : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (I : PrimeGapInterval) (S : Finset TrueZero),
    (∀ w ∈ S, zeroPoint w ∈ crowd I) →
    ((∑ w ∈ S, contactsCrossed w I : ℤ) : ℝ) ≤ (⌈I.threshold⌉₊ : ℝ) * (A₀ * Real.log (⌈I.threshold⌉₊ + 3)) := by
  obtain ⟨A₀, hA1, hA⟩ := crowd_card_cap
  refine ⟨A₀, hA1, fun I S hS => ?_⟩
  obtain ⟨h1, h2⟩ := crowd_family_contacts_le I S hS
  have h3 : ((∑ w ∈ S, contactsCrossed w I : ℤ) : ℝ) ≤ ((crowd I).card : ℝ) := by
    have : (∑ w ∈ S, contactsCrossed w I : ℤ) ≤ ((crowd I).card : ℤ) := h1.trans (by exact_mod_cast h2)
    exact_mod_cast this
  exact h3.trans (hA I)

/-- Les points de la fenêtre fermée entre deux seuils sont comptés par `N(a, b]`. -/
theorem window_sdiff_card_le_Ncount (a b : ℝ) :
    (upperWindow b \ upperWindow a).card ≤ Zeta23.Ncount a b := by
  have hfin := Zeta23.zerosIn_finite a b
  have hsub : upperWindow b \ upperWindow a ⊆ hfin.toFinset := by
    intro ρ hρ
    rw [Finset.mem_sdiff, mem_upperWindow, mem_upperWindow] at hρ
    rw [Set.Finite.mem_toFinset]
    obtain ⟨⟨hz, hpos, hle⟩, hnot⟩ := hρ
    refine ⟨hz, ?_, hle⟩
    by_contra hcon
    exact hnot ⟨hz, hpos, not_lt.mp hcon⟩
  calc (upperWindow b \ upperWindow a).card ≤ hfin.toFinset.card := Finset.card_le_card hsub
    _ ≤ ∑ ρ ∈ hfin.toFinset, Zeta23.zeroMult ρ := by
        have h := Finset.card_nsmul_le_sum hfin.toFinset Zeta23.zeroMult 1 (fun ρ hρ => ?_)
        · simpa using h
        · rw [Set.Finite.mem_toFinset] at hρ
          exact zetaZeroMultiplicity_pos hρ.1.1
    _ = Zeta23.Ncount a b := by
        unfold Zeta23.Ncount
        rw [finsum_mem_eq_finite_toFinset_sum _ hfin]

/-- **Transition de foule entre deux écarts** : les membres qui entrent en passant d'un écart à un écart plus court
sont au plus `N(π/ℓ_J, π/ℓ_I]`. -/
theorem crowd_transition_card_le {I J : PrimeGapInterval} :
    (crowd I \ crowd J).card ≤ Zeta23.Ncount J.threshold I.threshold := by
  rw [crowd_eq_upperWindow_threshold I, crowd_eq_upperWindow_threshold J]
  exact window_sdiff_card_le_Ncount _ _

/-- **Transition capée** : si les deux seuils sont à moins d'une unité, la transition est bornée par le comptage local
`A₀·log(|π/ℓ_J|+3)`. -/
theorem crowd_transition_cap : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ I J : PrimeGapInterval,
    J.threshold ≤ I.threshold → I.threshold ≤ J.threshold + 1 →
    ((crowd I \ crowd J).card : ℝ) ≤ A₀ * Real.log (|J.threshold| + 3) := by
  obtain ⟨A₀, hA1, hA⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨A₀, hA1, fun I J _ h2 => ?_⟩
  have hle : Zeta23.Ncount J.threshold I.threshold ≤ Zeta23.Ncount J.threshold (J.threshold + 1) :=
    Zeta23.Ncount_mono le_rfl h2
  have h := (crowd_transition_card_le (I := I) (J := J)).trans hle
  have h' : ((crowd I \ crowd J).card : ℝ) ≤ (Zeta23.Ncount J.threshold (J.threshold + 1) : ℝ) := by
    exact_mod_cast h
  exact h'.trans (hA J.threshold)

/-- **Membres de queue par fenêtre unité** : au-delà du seuil, chaque fenêtre `]t, t+1]` contient au plus
`A₀·log(|t|+3)` points. La queue reste infinie ; seul son débit par unité de hauteur est capé. -/
theorem tail_unit_window_cap : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (I : PrimeGapInterval) (t : ℝ), I.threshold ≤ t →
    ((upperWindow (t + 1) \ upperWindow t).card : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
  obtain ⟨A₀, hA1, hA⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨A₀, hA1, fun _ t _ => ?_⟩
  have h : ((upperWindow (t + 1) \ upperWindow t).card : ℝ) ≤ (Zeta23.Ncount t (t + 1) : ℝ) := by
    exact_mod_cast window_sdiff_card_le_Ncount t (t + 1)
  exact h.trans (hA t)

/-! ## 4. Composition avec la demande : la décomposition exacte et la borne de queue valent pour `F` -/

/-- La demande de chaque écart vaut foule plus queue (`crowd_tail_decomposition`), et la foule est lue dans `F`
(`primeDetermined_crowd`) : composition explicite. -/
theorem primeDetermined_demand_decomposition {F : ℂ → ℂ} (hF : IsPrimeDeterminedZetaContinuation F)
    (I : PrimeGapInterval) :
    localArithmeticTarget I = gapCrowdSum I + gapTailSum I ∧
    ((crowd I : Finset ℂ) : Set ℂ) =
      {ρ | F ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ I.threshold} :=
  ⟨crowd_tail_decomposition I, primeDetermined_crowd hF I⟩

/-! ## 5. Ce que la composition ne contraint pas (consigné, jamais posé)

Chaque énoncé des sections 2–4 est vrai pour toute position radiale : les CAP, les pas, les foules, les transitions et
le comptage local ne mentionnent que les hauteurs ; la détermination universelle ne mentionne que `F = ζ`. La seule
sortie radiale compilée reste `crowdRadialRigidity_iff_riemannHypothesis` (désormais sans hypothèse) : « tout membre de
toute foule est en ligne » EST RH. Le but exact laissé par Lean est affiché par la sonde hors build. -/

/-- Rappel composé : la rigidité radiale de la foule est RH, sans aucune hypothèse (R11 : `LogGapsVanish` théorème). -/
theorem crowdRadialRigidity_iff_riemannHypothesis' : CrowdRadialRigidity ↔ RiemannHypothesis :=
  crowdRadialRigidity_iff_riemannHypothesis

end RHV6Fresh

#print axioms RHV6Fresh.primeDetermined_strip_iff
#print axioms RHV6Fresh.primeDetermined_crowd
#print axioms RHV6Fresh.primeDetermined_coordinates
#print axioms RHV6Fresh.primeDetermined_upperCount
#print axioms RHV6Fresh.primeDetermined_lowZero_iff_not_riemannHypothesis
#print axioms RHV6Fresh.primeDetermined_lowZero_iff_offCarrier
#print axioms RHV6Fresh.lower_cap_contact_interval
#print axioms RHV6Fresh.upper_cap_contact_interval
#print axioms RHV6Fresh.OffCarrier.pair_blind_to_caps_and_steps
#print axioms RHV6Fresh.OffCarrier.pair_counted_twice
#print axioms RHV6Fresh.crowd_card_cap
#print axioms RHV6Fresh.crowd_contains_rank_of_upper_cap
#print axioms RHV6Fresh.crowd_family_contacts_cap
#print axioms RHV6Fresh.crowd_transition_cap
#print axioms RHV6Fresh.tail_unit_window_cap
#print axioms RHV6Fresh.primeDetermined_demand_decomposition
#print axioms RHV6Fresh.crowdRadialRigidity_iff_riemannHypothesis'
