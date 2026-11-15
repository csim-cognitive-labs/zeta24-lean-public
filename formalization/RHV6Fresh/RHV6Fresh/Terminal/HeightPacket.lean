/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GlobalRigidSystem

/-!
# RHV6Fresh — paquet de hauteur et compensation forcée (auteur, 2026-09-30)

L'unité spectrale n'est plus le membre mais **le paquet de hauteur** : tous les indices de la
formule explicite compilée dont la hauteur absolue est `T`. La formule explicite compilée (canal
lissé, somme absolument convergente sur tous les zéros non triviaux) se découpe exactement, sans
troncature ni fenêtre :

  reste exact = contribution du paquet + contribution du complément.

* `channel_eq_packet_add_complement` : le découpage, pour toute partie `S` des indices.
* `psi_eq_background_add_packet_add_complement` : `ψ(N) = fond + paquet + complément` (`N ≥ 2`).
* `compensation` (nom conservé) : `K := reste exact − paquet`, l'identité du complément. Ce n'est ni une
  hypothèse ni une obligation des autres zéros : c'est, par définition, leur somme.
  `compensation_eq_complement` : identité du complément (§19.21).
* `compensation_realized_for_all_x` : la même identité pour tout `x > 1`, au niveau des primitives.
* `eventCompensation_eq_complement` : la même identité sur l'incrément d'un événement premier.
* `compensation_difference` : pour deux paquets, `K_S − K_{S'} = L_{S'} − L_S`.
* `packet_two_members` : deux membres distincts d'un paquet y sont isolés, terme par terme.
* `off_forced_compensation` : la chaîne complète sur un zéro hors ligne — passage, raccord
  grammatical, événement premier, paquet de hauteur contenant les deux membres du passage, le zéro
  et son miroir, incrément résiduel de l'événement, compensation exacte du complément.

Tout est inconditionnel. Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean ArithmeticFunction

/-! ## 1. Le canal découpé sur une partie quelconque des indices -/

/-- Les indices de la formule explicite compilée : tous les zéros non triviaux, deux branches. -/
abbrev ExplicitIndex := {ρ : ℂ // IsNontrivialZetaZero ρ}

/-- La contribution au canal des zéros d'une partie `S` des indices. -/
noncomputable def channelOn (S : Set ExplicitIndex) (x : ℝ) : ℂ :=
  ∑' ρ : S, nontrivialZeroResidueTerm x ρ

/-- **Le paquet de hauteur `T`** : tous les indices de hauteur absolue `T` (la branche supérieure
à hauteur `T` et sa branche conjuguée). -/
def heightPacket (T : ℝ) : Set ExplicitIndex := {ρ | |(ρ : ℂ).im| = T}

theorem channelOn_summable (S : Set ExplicitIndex) {x : ℝ} (hx : 1 < x) :
    Summable ((fun ρ : ExplicitIndex => nontrivialZeroResidueTerm x ρ) ∘ (↑) : S → ℂ) :=
  (nontrivial_zero_residue_series_summable hx).subtype S

/-- **Le découpage exact** : le canal entier est la contribution de `S` plus celle du complément. -/
theorem channel_eq_packet_add_complement (S : Set ExplicitIndex) {x : ℝ} (hx : 1 < x) :
    ∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm x ρ = channelOn S x + channelOn Sᶜ x :=
  (Summable.tsum_add_tsum_compl (f := fun ρ : ExplicitIndex => nontrivialZeroResidueTerm x ρ)
    (s := S) (channelOn_summable S hx) (channelOn_summable Sᶜ hx)).symm

/-- Additivité sur deux parties disjointes. -/
theorem channelOn_union {A B : Set ExplicitIndex} (hd : Disjoint A B) {x : ℝ} (hx : 1 < x) :
    channelOn (A ∪ B) x = channelOn A x + channelOn B x :=
  Summable.tsum_union_disjoint (f := fun ρ : ExplicitIndex => nontrivialZeroResidueTerm x ρ) hd
    (channelOn_summable A hx) (channelOn_summable B hx)

/-- Le canal d'un seul indice est son terme. -/
theorem channelOn_singleton (a : ExplicitIndex) (x : ℝ) :
    channelOn {a} x = nontrivialZeroResidueTerm x a :=
  tsum_singleton a (fun ρ => nontrivialZeroResidueTerm x ρ)

/-- **Deux membres distincts d'un paquet y sont isolés** : le paquet est leurs deux termes plus le
reste du paquet. -/
theorem packet_two_members {S : Set ExplicitIndex} {a b : ExplicitIndex} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) {x : ℝ} (hx : 1 < x) :
    channelOn S x = nontrivialZeroResidueTerm x a + nontrivialZeroResidueTerm x b +
      channelOn (S \ {a, b}) x := by
  have hS : S = {a} ∪ ({b} ∪ (S \ {a, b})) := by
    ext ρ
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_insert_iff]
    constructor
    · intro h
      by_cases h1 : ρ = a
      · exact Or.inl h1
      · by_cases h2 : ρ = b
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨h, fun h' => h'.elim h1 h2⟩)
    · rintro (rfl | rfl | ⟨h, _⟩)
      · exact ha
      · exact hb
      · exact h
  have hd2 : Disjoint ({b} : Set ExplicitIndex) (S \ {a, b}) := by
    rw [Set.disjoint_left]
    intro ρ h1 h2
    exact h2.2 (Or.inr h1)
  have hd1 : Disjoint ({a} : Set ExplicitIndex) ({b} ∪ (S \ {a, b})) := by
    rw [Set.disjoint_left]
    intro ρ h1 h2
    rcases h2 with h2 | h2
    · exact hab (h1.symm.trans h2)
    · exact h2.2 (Or.inl h1)
  calc channelOn S x = channelOn ({a} ∪ ({b} ∪ (S \ {a, b}))) x := by rw [← hS]
    _ = _ := by
      rw [channelOn_union hd1 hx, channelOn_union hd2 hx, channelOn_singleton, channelOn_singleton]
      ring

/-! ## 2. Le fond, le paquet et le complément au niveau de l'escalier -/

/-- La primitive du fond lisse compilé (tout sauf le canal des zéros non triviaux). -/
noncomputable def backgroundPrimitive (x : ℝ) : ℂ := (x : ℂ) * smoothedZeroBackground x

/-- La primitive de la contribution d'une partie `S` des indices. -/
noncomputable def channelPrimitive (S : Set ExplicitIndex) (x : ℝ) : ℂ := (x : ℂ) * channelOn S x

/-- Le pas d'une primitive entre `N` et `N + 1` : c'est lui qui rend l'escalier. -/
noncomputable def stepAt (F : ℝ → ℂ) (N : ℕ) : ℂ := F ((N : ℝ) + 1) - F N

/-- La primitive compilée se découpe : fond + paquet + complément, pour tout `x > 1`. -/
theorem smoothedZeroPrimitive_split (S : Set ExplicitIndex) {x : ℝ} (hx : 1 < x) :
    smoothedZeroPrimitive x =
      backgroundPrimitive x + channelPrimitive S x + channelPrimitive Sᶜ x := by
  have h := smoothedZeroFormula_sub_background hx
  rw [channel_eq_packet_add_complement S hx] at h
  unfold smoothedZeroPrimitive backgroundPrimitive channelPrimitive
  linear_combination (x : ℂ) * h

/-- **L'escalier découpé** : `ψ(N) = fond + paquet + complément`, exactement, pour `N ≥ 2`. -/
theorem psi_eq_background_add_packet_add_complement (S : Set ExplicitIndex) {N : ℕ}
    (hN : 2 ≤ N) :
    (Chebyshev.psi (N : ℝ) : ℂ) =
      stepAt backgroundPrimitive N + stepAt (channelPrimitive S) N +
        stepAt (channelPrimitive Sᶜ) N := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN2 : (1 : ℝ) < (N : ℝ) + 1 := by linarith
  have h := smoothedZeroPrimitive_nat_difference hN
  rw [smoothedZeroPrimitive_split S hN1, smoothedZeroPrimitive_split S hN2] at h
  unfold stepAt
  linear_combination -h

/-! ## 3. Le reste exact, le paquet local et la compensation forcée -/

/-- **Le reste exact** : l'escalier moins le fond lisse compilé. -/
noncomputable def exactRemainder (N : ℕ) : ℂ :=
  (Chebyshev.psi (N : ℝ) : ℂ) - stepAt backgroundPrimitive N

/-- **La contribution du paquet local** `L`. -/
noncomputable def localPacket (S : Set ExplicitIndex) (N : ℕ) : ℂ := stepAt (channelPrimitive S) N

/-- **L'identité du complément** (nom `compensation` conservé) `K := reste exact − paquet local`. Définie du
seul côté arithmétique et du paquet : ce n'est pas une hypothèse, et rien n'y est « forcé » (§19.21). -/
noncomputable def compensation (S : Set ExplicitIndex) (N : ℕ) : ℂ :=
  exactRemainder N - localPacket S N

/-- Le reste exact est le paquet plus le complément. -/
theorem exactRemainder_eq_packet_add_complement (S : Set ExplicitIndex) {N : ℕ} (hN : 2 ≤ N) :
    exactRemainder N = localPacket S N + localPacket Sᶜ N := by
  unfold exactRemainder localPacket
  rw [psi_eq_background_add_packet_add_complement S hN]
  ring

/-- **La compensation est fournie exactement par le complément**, quel que soit le paquet. -/
theorem compensation_eq_complement (S : Set ExplicitIndex) {N : ℕ} (hN : 2 ≤ N) :
    compensation S N = localPacket Sᶜ N := by
  unfold compensation
  rw [exactRemainder_eq_packet_add_complement S hN]
  ring

/-- **La compensation est réalisée pour tout `x > 1`**, au niveau des primitives : ce qui reste
de la primitive compilée une fois retirés le fond et le paquet est la primitive du complément. -/
theorem compensation_realized_for_all_x (S : Set ExplicitIndex) {x : ℝ} (hx : 1 < x) :
    smoothedZeroPrimitive x - backgroundPrimitive x - channelPrimitive S x =
      channelPrimitive Sᶜ x := by
  rw [smoothedZeroPrimitive_split S hx]
  ring

/-- **Deux paquets, une même arithmétique** : la différence des compensations est la différence
opposée des paquets. -/
theorem compensation_difference (S S' : Set ExplicitIndex) (N : ℕ) :
    compensation S N - compensation S' N = localPacket S' N - localPacket S N := by
  unfold compensation
  ring

/-! ## 4. L'incrément résiduel d'un événement premier -/

/-- L'incrément du reste exact entre `N` et `N + 1`. -/
noncomputable def remainderIncrement (N : ℕ) : ℂ := exactRemainder (N + 1) - exactRemainder N

/-- L'incrément du paquet local entre `N` et `N + 1`. -/
noncomputable def packetIncrement (S : Set ExplicitIndex) (N : ℕ) : ℂ :=
  localPacket S (N + 1) - localPacket S N

/-- La compensation forcée sur l'incrément. -/
noncomputable def eventCompensation (S : Set ExplicitIndex) (N : ℕ) : ℂ :=
  remainderIncrement N - packetIncrement S N

/-- **Côté arithmétique** : l'incrément du reste exact est le poids de von Mangoldt de l'événement
moins l'incrément du fond. -/
theorem remainderIncrement_arithmetic (N : ℕ) :
    remainderIncrement N = ((Λ (N + 1) : ℝ) : ℂ) -
      (stepAt backgroundPrimitive (N + 1) - stepAt backgroundPrimitive N) := by
  have hw := thm_weightFromPsi_chebyshev (n := N + 1) (by omega)
  unfold fnWeightFromPsi at hw
  have hcast : ((N + 1 : ℕ) : ℝ) - 1 = (N : ℝ) := by push_cast; ring
  rw [hcast] at hw
  unfold remainderIncrement exactRemainder
  rw [← hw]
  push_cast
  ring

/-- **Côté spectral** : l'incrément du reste exact est l'incrément du paquet plus celui du
complément. -/
theorem remainderIncrement_eq_packet_add_complement (S : Set ExplicitIndex) {N : ℕ}
    (hN : 2 ≤ N) :
    remainderIncrement N = packetIncrement S N + packetIncrement Sᶜ N := by
  unfold remainderIncrement packetIncrement
  rw [exactRemainder_eq_packet_add_complement S hN,
    exactRemainder_eq_packet_add_complement S (N := N + 1) (by omega)]
  ring

/-- **La compensation de l'événement est fournie exactement par le complément.** -/
theorem eventCompensation_eq_complement (S : Set ExplicitIndex) {N : ℕ} (hN : 2 ≤ N) :
    eventCompensation S N = packetIncrement Sᶜ N := by
  unfold eventCompensation
  rw [remainderIncrement_eq_packet_add_complement S hN]
  ring

/-! ## 5. Les membres typés dans leur paquet -/

/-- L'indice de formule explicite d'un membre typé. -/
noncomputable def memberIndex (z : TrueZero) : ExplicitIndex :=
  ⟨zeroPoint z, zeroPoint_isNontrivial z⟩

/-- Un membre appartient au paquet de sa propre hauteur. -/
theorem memberIndex_mem_heightPacket (z : TrueZero) :
    memberIndex z ∈ heightPacket (rZeroHeight z.1) := by
  show |(zeroPoint z).im| = rZeroHeight z.1
  rw [zeroPoint_im]
  exact abs_of_pos z.2

theorem memberIndex_injective {z w : TrueZero} (h : memberIndex z = memberIndex w) : z = w := by
  have h1 : zeroPoint z = zeroPoint w := congrArg (fun i : ExplicitIndex => (i : ℂ)) h
  exact Subtype.ext (Subtype.ext h1)

/-- Le miroir est dans le même paquet de hauteur. -/
theorem mirrorMember_mem_heightPacket (z : TrueZero) :
    memberIndex (mirrorMember z) ∈ heightPacket (rZeroHeight z.1) := by
  have h := memberIndex_mem_heightPacket (mirrorMember z)
  rwa [mirrorMember_ordinate] at h

/-- En ligne, le miroir est le membre lui-même : il n'ajoute rien au paquet. -/
theorem on_packet_mirror_collapses {z : TrueZero} (hOn : rZeroRadialPosition z.1 = 1 / 2) :
    memberIndex (mirrorMember z) = memberIndex z := by
  rw [mirrorMember_eq_self_of_onLine hOn]

/-- Hors ligne, le miroir est un second indice du même paquet. -/
theorem off_packet_mirror_distinct {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    memberIndex (mirrorMember z) ≠ memberIndex z := by
  intro h
  have hr := mirrorMember_radial z
  rw [memberIndex_injective h] at hr
  exact hOff (by linarith)

/-- **Le paquet d'un zéro hors ligne, explicité** : le terme du zéro, le terme de son miroir, et
le reste du paquet (branche conjuguée et autres membres éventuels de même hauteur). -/
theorem off_packet_explicit {z : TrueZero} (hOff : PIsOffCriticalLine z.1) {x : ℝ} (hx : 1 < x) :
    channelOn (heightPacket (rZeroHeight z.1)) x =
      -(zetaZeroMultiplicity (zeroPoint z) : ℂ) * Perron.f x (zeroPoint z) +
        -(zetaZeroMultiplicity (zeroPoint (mirrorMember z)) : ℂ) *
          Perron.f x (zeroPoint (mirrorMember z)) +
        channelOn (heightPacket (rZeroHeight z.1) \ {memberIndex z, memberIndex (mirrorMember z)})
          x :=
  packet_two_members (memberIndex_mem_heightPacket z) (mirrorMember_mem_heightPacket z)
    (off_packet_mirror_distinct hOff).symm hx

/-! ## 6. La chaîne complète sur un zéro hors ligne -/

/-- **Compensation forcée par un zéro hors ligne.** Une seule chaîne, sur les mêmes objets :
le zéro `z` hors ligne ; un passage `p` à la hauteur de `z` ; son raccord grammatical `G` et son
événement premier `M = N + 1` ; le paquet de hauteur, qui contient les deux membres distincts du
passage, `z` et son miroir distinct ; l'incrément résiduel de l'événement, égal à `log M` moins
l'incrément du fond ; et la compensation de cet incrément, fournie exactement par le complément
du paquet. -/
theorem off_forced_compensation {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    ∃ p : TZeroPassage, ∃ hE : 0 < rZeroHeight p.zEarlierMember,
      ∃ hL : 0 < rZeroHeight p.zLaterMember,
      ∃ G : GrammaticalRaccord ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩, ∃ N : ℕ,
        N + 1 = G.M ∧ 2 ≤ N ∧
        rZeroHeight p.zEarlierMember = rZeroHeight z.1 ∧
        rZeroHeight p.zLaterMember = rZeroHeight z.1 ∧
        memberIndex ⟨p.zEarlierMember, hE⟩ ∈ heightPacket (rZeroHeight z.1) ∧
        memberIndex ⟨p.zLaterMember, hL⟩ ∈ heightPacket (rZeroHeight z.1) ∧
        memberIndex ⟨p.zEarlierMember, hE⟩ ≠ memberIndex ⟨p.zLaterMember, hL⟩ ∧
        memberIndex z ∈ heightPacket (rZeroHeight z.1) ∧
        memberIndex (mirrorMember z) ∈ heightPacket (rZeroHeight z.1) ∧
        memberIndex (mirrorMember z) ≠ memberIndex z ∧
        remainderIncrement N = ((Real.log (G.M : ℝ) : ℝ) : ℂ) -
          (stepAt backgroundPrimitive (N + 1) - stepAt backgroundPrimitive N) ∧
        eventCompensation (heightPacket (rZeroHeight z.1)) N =
          packetIncrement (heightPacket (rZeroHeight z.1))ᶜ N := by
  obtain ⟨p, hE, hL, hHz, hSame, _, hOcc, hOccLt⟩ := off_event_increment_without_height hOff
  let G := grammaticalRaccordOf p hE hL
  have hM : G.M = occurrence ⟨p.zLaterMember, hL⟩ := G.entry_eq
  have hMprime : (G.M).Prime := hM ▸ occurrence_prime _
  have hE2 : 2 ≤ occurrence ⟨p.zEarlierMember, hE⟩ := (occurrence_prime _).two_le
  have hM3 : 3 ≤ G.M := by rw [hM]; omega
  refine ⟨p, hE, hL, G, G.M - 1, by omega, by omega, hHz, hSame ▸ hHz, ?_, ?_, ?_,
    memberIndex_mem_heightPacket z, mirrorMember_mem_heightPacket z,
    off_packet_mirror_distinct hOff, ?_,
    eventCompensation_eq_complement _ (by omega)⟩
  · have h := memberIndex_mem_heightPacket ⟨p.zEarlierMember, hE⟩
    rwa [show rZeroHeight p.zEarlierMember = rZeroHeight z.1 from hHz] at h
  · have h := memberIndex_mem_heightPacket ⟨p.zLaterMember, hL⟩
    rwa [show rZeroHeight p.zLaterMember = rZeroHeight z.1 from hSame ▸ hHz] at h
  · intro h
    have h' := congrArg Subtype.val (memberIndex_injective h)
    exact thm_consecutive_members_distinct p.hConsecutive h'
  · rw [remainderIncrement_arithmetic]
    have hN1 : G.M - 1 + 1 = G.M := by omega
    rw [hN1, vonMangoldt_apply_prime hMprime]

#print axioms channel_eq_packet_add_complement
#print axioms packet_two_members
#print axioms psi_eq_background_add_packet_add_complement
#print axioms compensation_eq_complement
#print axioms compensation_realized_for_all_x
#print axioms compensation_difference
#print axioms remainderIncrement_arithmetic
#print axioms eventCompensation_eq_complement
#print axioms on_packet_mirror_collapses
#print axioms off_packet_mirror_distinct
#print axioms off_packet_explicit
#print axioms off_forced_compensation

end RHV6Fresh
