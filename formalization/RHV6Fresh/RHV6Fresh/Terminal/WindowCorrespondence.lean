/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FirstGainPremise
import RHV6Fresh.Terminal.CanonicalEnumeration
import RHV6Fresh.Direct.MirrorCount
import RHV3Lean.Objects.MemberSensitiveMZCorrespondence
import RHV3Lean.Objects.OffFibreAndPassage

/-!
# Correspondance collective par fenêtres canoniques (auteur, 2026-10-11)

Portage dans RHV6Fresh du contenu démontré de la correspondance à deux côtés (historique `rhv4_lean`,
`Prime/TwoSidedCorrespondence.lean`, non importé), réécrit sur les objets actuels et prouvé depuis `rhv3_lean` seul
(`nMemberMZOccurrence`, `thm_memberMZOccurrence_eq_canonicalAnchor_unconditional`, `thm_zeroSourceIndex_*`), puis étendu
aux fenêtres de membres canoniques consécutifs. Aucune prémisse.

* §1 occurrence reconstruite `M^Z` d'un membre canonique = premier de même rang ; sur une fenêtre `n₀, …, n₀ + m − 1` :
  mêmes membres, `M^Z = M = p_index`, succession première, injectivité, ordre strict, consécutivité, télescopage des écarts.
* §2 raccord exact de deux fenêtres adjacentes : réunion = fenêtre concaténée, disjointes (ni omission, ni double compte).
* §3 fibres de hauteur dans l'ordre canonique : contiguïté, finitude, complétion aux bords, stabilité par le miroir.
  Appartenance à une fibre ≠ localisation entre contacts : rien ici ne lit une cellule de Tour.
* §4 contributions signées : toute sélection finie de rangs (groupe) laisse un complément qui converge vers le reste moins
  la somme signée du groupe ; multiplicités conservées dans chaque contribution (`normalizedSmoothedPairContribution`).
-/

namespace RHV6Fresh

open RHV3Lean
open scoped Classical

/-! ## 1. Occurrences canoniques sur une fenêtre -/

/-- **`M^Z = M` sur un membre canonique** : l'occurrence reconstruite du membre d'index `n` est le premier de rang `n`. -/
theorem canonical_MZ_eq_primeAtRank (n : ℕ) :
    nMemberMZOccurrence (canonicalMember n) = fnPrimeAtRank n := by
  rw [thm_memberMZOccurrence_eq_canonicalAnchor_unconditional]
  unfold nMemberCanonicalAnchor
  rw [canonicalMember_index]

/-- **Fenêtre canonique** : les membres `n₀ + k`, `k < m`, sont consécutifs deux à deux et leurs occurrences sont les
premiers `p_{n₀+k}` ; l'occurrence suivante est le successeur premier (`M^Z = M`, succession, consécutivité). -/
theorem window_correspondence (n₀ m : ℕ) :
    (∀ k < m, nMemberMZOccurrence (canonicalMember (n₀ + k)) = fnPrimeAtRank (n₀ + k)) ∧
    (∀ k, k + 1 < m → nMemberMZOccurrence (canonicalMember (n₀ + k + 1)) = fnPrimeSuccessor (n₀ + k)) ∧
    (∀ k, k + 1 < m → PZeroMembersConsecutive (canonicalMember (n₀ + k)).1 (canonicalMember (n₀ + k + 1)).1) :=
  ⟨fun k _ => canonical_MZ_eq_primeAtRank _,
   fun k _ => by rw [canonical_MZ_eq_primeAtRank]; rfl,
   fun k _ => canonicalMember_consecutive _⟩

/-- **Injectivité et ordre strict** des occurrences canoniques : deux membres distincts ont des occurrences distinctes,
dans le même ordre que les membres. -/
theorem canonical_occurrence_strictMono :
    StrictMono (fun n => nMemberMZOccurrence (canonicalMember n)) := by
  intro a b h
  simp only [canonical_MZ_eq_primeAtRank]
  exact thm_primeAtRank_strictMono h

theorem canonical_occurrence_injective {z w : TrueZero}
    (h : nMemberMZOccurrence z = nMemberMZOccurrence w) : z = w := by
  obtain ⟨a, rfl⟩ := canonicalMember_surjective z
  obtain ⟨b, rfl⟩ := canonicalMember_surjective w
  rw [canonicalMember_injective.eq_iff]
  exact canonical_occurrence_strictMono.injective h

/-- **Télescopage des écarts** sur une fenêtre : `Σ_{k<m} (p_{n₀+k+1} − p_{n₀+k}) = p_{n₀+m} − p_{n₀}`. -/
theorem window_gap_telescope (n₀ m : ℕ) :
    ∑ k ∈ Finset.range m, ((fnPrimeAtRank (n₀ + k + 1) : ℤ) - fnPrimeAtRank (n₀ + k)) =
      (fnPrimeAtRank (n₀ + m) : ℤ) - fnPrimeAtRank n₀ := by
  have := Finset.sum_range_sub (fun k => (fnPrimeAtRank (n₀ + k) : ℤ)) m
  simpa [add_assoc] using this

/-! ## 2. Raccord exact de deux fenêtres adjacentes -/

/-- Membres d'une fenêtre canonique. -/
noncomputable def windowMembers (n₀ m : ℕ) : Finset TrueZero :=
  (Finset.range m).image fun k => canonicalMember (n₀ + k)

theorem windowMembers_card (n₀ m : ℕ) : (windowMembers n₀ m).card = m := by
  unfold windowMembers
  rw [Finset.card_image_of_injective _ (fun a b h => by
    have := canonicalMember_injective h; omega)]
  simp

/-- **Raccord** : la fenêtre `[n₀, n₀ + m + m')` est la réunion DISJOINTE de `[n₀, n₀ + m)` et `[n₀ + m, n₀ + m + m')`. -/
theorem window_raccord (n₀ m m' : ℕ) :
    windowMembers n₀ (m + m') = windowMembers n₀ m ∪ windowMembers (n₀ + m) m' ∧
      Disjoint (windowMembers n₀ m) (windowMembers (n₀ + m) m') := by
  constructor
  · ext z
    simp only [windowMembers, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      by_cases h : k < m
      · exact Or.inl ⟨k, h, rfl⟩
      · exact Or.inr ⟨k - m, by omega, by congr 1; omega⟩
    · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
      · exact ⟨k, by omega, rfl⟩
      · exact ⟨m + k, by omega, by congr 1; omega⟩
  · rw [Finset.disjoint_left]
    simp only [windowMembers, Finset.mem_image, Finset.mem_range]
    rintro z ⟨k, hk, rfl⟩ ⟨k', hk', h⟩
    have := canonicalMember_injective h
    omega

/-! ## 3. Fibres de hauteur dans l'ordre canonique -/

/-- **Contiguïté d'une fibre** : entre deux membres canoniques de même hauteur, tout membre canonique a cette hauteur. -/
theorem fiber_contiguous {a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (h : rZeroHeight (canonicalMember a).1 = rZeroHeight (canonicalMember b).1) :
    rZeroHeight (canonicalMember c).1 = rZeroHeight (canonicalMember a).1 :=
  le_antisymm (h ▸ canonicalMember_height_mono hcb) (canonicalMember_height_mono hac)

/-- **Finitude** : une fibre de hauteur ne contient qu'un nombre fini de rangs canoniques. -/
theorem canonical_fiber_finite (T : ℝ) : {n : ℕ | rZeroHeight (canonicalMember n).1 = T}.Finite := by
  have hF := thm_zeroHeightFiber_finite T
  have hinj : Set.InjOn (fun n => (canonicalMember n).1) {n : ℕ | rZeroHeight (canonicalMember n).1 = T} :=
    fun a _ b _ h => canonicalMember_injective (Subtype.ext h)
  exact Set.Finite.of_finite_image (hF.subset (by rintro _ ⟨n, hn, rfl⟩; exact hn)) hinj

/-- **Complétion aux bords** : toute fenêtre `[n₀, n₀ + m)`, `m ≥ 1`, est contenue dans une fenêtre `[a, b)` de fibres
complètes : aucun rang hors de `[a, b)` n'a la hauteur du premier ou du dernier membre de la fenêtre. -/
theorem window_fiber_completion (n₀ m : ℕ) (hm : 1 ≤ m) :
    ∃ a b : ℕ, a ≤ n₀ ∧ n₀ + m ≤ b ∧
      (∀ k < a, rZeroHeight (canonicalMember k).1 < rZeroHeight (canonicalMember n₀).1) ∧
      (∀ k, b ≤ k → rZeroHeight (canonicalMember (n₀ + m - 1)).1 < rZeroHeight (canonicalMember k).1) := by
  classical
  have hex : ∃ j, rZeroHeight (canonicalMember j).1 = rZeroHeight (canonicalMember n₀).1 := ⟨n₀, rfl⟩
  set a := Nat.find hex with ha
  have haLe : a ≤ n₀ := Nat.find_min' hex rfl
  obtain ⟨S, hS⟩ := (canonical_fiber_finite (rZeroHeight (canonicalMember (n₀ + m - 1)).1)).bddAbove
  refine ⟨a, max (S + 1) (n₀ + m), haLe, le_max_right _ _, ?_, ?_⟩
  · intro k hk
    have hle := canonicalMember_height_mono (le_trans hk.le haLe)
    have hne : rZeroHeight (canonicalMember k).1 ≠ rZeroHeight (canonicalMember n₀).1 := Nat.find_min hex hk
    exact lt_of_le_of_ne hle hne
  · intro k hk
    have hk' : n₀ + m - 1 ≤ k := by have := le_max_right (S + 1) (n₀ + m); omega
    have hle := canonicalMember_height_mono hk'
    refine lt_of_le_of_ne hle fun heq => ?_
    have := hS (show k ∈ {n : ℕ | _} from heq.symm)
    have := le_max_left (S + 1) (n₀ + m)
    omega

/-- **Stabilité par le miroir** : le miroir d'un membre canonique est un membre canonique de la même fibre (même
hauteur), donc dans toute fenêtre de fibres complètes qui contient le membre. -/
theorem fiber_mirror_stable (n : ℕ) :
    ∃ n', canonicalMember n' = mirrorMember (canonicalMember n) ∧
      rZeroHeight (canonicalMember n').1 = rZeroHeight (canonicalMember n).1 := by
  obtain ⟨n', h⟩ := canonicalMember_surjective (mirrorMember (canonicalMember n))
  exact ⟨n', h, by rw [h, mirrorMember_ordinate]⟩

/-- **Fenêtre de fibres complètes stable par le miroir** : dans `[a, b)` donné par la complétion, le miroir de tout membre
de `[n₀, n₀ + m)` est encore dans `[a, b)`. -/
theorem window_completion_mirror (n₀ m : ℕ) (hm : 1 ≤ m) :
    ∃ a b : ℕ, a ≤ n₀ ∧ n₀ + m ≤ b ∧ ∀ k, n₀ ≤ k → k < n₀ + m →
      ∃ k', a ≤ k' ∧ k' < b ∧ canonicalMember k' = mirrorMember (canonicalMember k) := by
  obtain ⟨a, b, ha, hb, hlo, hhi⟩ := window_fiber_completion n₀ m hm
  refine ⟨a, b, ha, hb, fun k hk1 hk2 => ?_⟩
  obtain ⟨k', hk', hh⟩ := fiber_mirror_stable k
  refine ⟨k', ?_, ?_, hk'⟩
  · by_contra h
    have h1 := hlo k' (lt_of_not_ge h)
    have h2 := canonicalMember_height_mono hk1
    linarith
  · by_contra h
    have h1 := hhi k' (le_of_not_gt h)
    have h2 := canonicalMember_height_mono (show k ≤ n₀ + m - 1 by omega)
    linarith

/-! ## 4. Contributions signées : groupe fini et complément conservé -/

/-- **Sélection finie, complément conservé** : pour tout ensemble fini `S` de rangs canoniques (groupe), les
contributions lissées normalisées des AUTRES rangs ont pour somme le reste lissé normalisé moins la somme SIGNÉE du
groupe ; aucune contribution n'est perdue, aucun signe n'est retiré. -/
theorem group_complement_hasSum (S : Finset ℕ) {x : ℝ} (hx : 1 < x) :
    HasSum (fun n : {n : ℕ // n ∉ S} => normalizedSmoothedPairContribution (canonicalMember n) x)
      (normalizedSmoothedRemainder x - ∑ n ∈ S, normalizedSmoothedPairContribution (canonicalMember n) x) := by
  have h := normalizedSmoothedPairContribution_hasSum hx
  have h' : HasSum (fun n => normalizedSmoothedPairContribution (canonicalMember n) x)
      ((normalizedSmoothedRemainder x - ∑ n ∈ S, normalizedSmoothedPairContribution (canonicalMember n) x) +
        ∑ n ∈ S, normalizedSmoothedPairContribution (canonicalMember n) x) := by
    rwa [sub_add_cancel]
  exact (Finset.hasSum_compl_iff S).mpr h'

/-- **Fenêtre en groupe** : reste = historique (rangs `< n₀`) + fenêtre (`n₀ ≤ n < n₀ + m`) + complément (rangs
`≥ n₀ + m`), tous signés ; le complément est la somme d'une série convergente. -/
theorem window_group_split (n₀ m : ℕ) {x : ℝ} (hx : 1 < x) :
    HasSum (fun j : ℕ => normalizedSmoothedPairContribution (canonicalMember (n₀ + m + j)) x)
      (normalizedSmoothedRemainder x -
        (∑ n ∈ Finset.range n₀, normalizedSmoothedPairContribution (canonicalMember n) x) -
        ∑ k ∈ Finset.range m, normalizedSmoothedPairContribution (canonicalMember (n₀ + k)) x) := by
  have h := (hasSum_nat_add_iff' (n₀ + m)).mpr (normalizedSmoothedPairContribution_hasSum hx)
  have hsplit : ∑ n ∈ Finset.range (n₀ + m), normalizedSmoothedPairContribution (canonicalMember n) x =
      (∑ n ∈ Finset.range n₀, normalizedSmoothedPairContribution (canonicalMember n) x) +
        ∑ k ∈ Finset.range m, normalizedSmoothedPairContribution (canonicalMember (n₀ + k)) x :=
    Finset.sum_range_add _ _ _
  rw [hsplit, ← sub_sub] at h
  simpa [add_comm, add_left_comm, add_assoc] using h

end RHV6Fresh
