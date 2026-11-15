/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.HeightPacket

/-!
# RHV6Fresh — la lecture inverse : le résidu arithmétique comme objet autonome (auteur, 2026-09-30)

Jusqu'ici la formule explicite était lue dans un seul sens : zéros → formule → `ψ`, puis
`psiRecoveredFromZeros = ψ`. Cette égalité terminale écrase la décomposition. Ici la lecture
inverse est construite comme objet de travail, en quatre constructions, sans `False` et sans RH :

1. **`R_arith`** : `exactRemainder N = ψ(N) − fond(N)` (`Terminal/HeightPacket.lean`). Il ne contient
   que l'escalier des premiers et le fond compilé (`x/2`, `ζ'/ζ(0)`, `ζ'/ζ(−1)`, zéros triviaux) :
   aucun zéro non trivial, aucune position radiale (`exactRemainder_arithmetic_only`).
2. **`R_spectral`** : `spectralRemainder N`, défini du seul canal des zéros non triviaux.
   **Le pont** : `arithmetic_eq_spectral` (`R_arith = R_spectral`, `N ≥ 2`).
3. **`ΔR(a, b)`** entre deux événements arithmétiques quelconques `a ≤ b` : `remainderBetween`.
   Côté arithmétique, `ΔR(a, b) = Σ_{a<n≤b} Λ(n) − ΔB(a, b)` (`remainderBetween_arithmetic`) ;
   côté spectral, `ΔR(a, b) = Z(b) − Z(a)` (`remainderBetween_eq_spectral`).
4. **Paquet et complément** : `ΔR(a, b) = L_P(a, b) + C_{¬P}(a, b)` pour toute partie `P` des
   indices (`remainderBetween_eq_packet_add_complement`), donc `C_{¬P} = ΔR − L_P`
   (`complementBetween_forced`).

`off_inverse_reading` : la chaîne sur un zéro hors ligne, entre les deux premiers consécutifs du
raccord (l'occurrence de la Tour de sortie et le premier partagé).

Tout est inconditionnel. Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean ArithmeticFunction

/-! ## 1. `R_arith` : ce qu'il contient -/

/-- **`R_arith` ne lit que l'arithmétique et le fond** : l'escalier `ψ` et la primitive du fond
compilé, évaluée en `N + 1` et en `N`. Aucun zéro non trivial n'y figure. -/
theorem exactRemainder_arithmetic_only (N : ℕ) :
    exactRemainder N = (Chebyshev.psi (N : ℝ) : ℂ) -
      ((((N : ℝ) + 1 : ℝ) : ℂ) * smoothedZeroBackground ((N : ℝ) + 1) -
        ((N : ℝ) : ℂ) * smoothedZeroBackground (N : ℝ)) :=
  rfl

/-- L'escalier ne lit que la partie entière. -/
theorem psi_floor (x : ℝ) : Chebyshev.psi (⌊x⌋₊ : ℝ) = Chebyshev.psi x := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc]
  simp [Nat.floor_natCast]

/-- `R_arith` en un réel `x` : l'escalier en `x` moins le pas du fond à la marche `⌊x⌋`. -/
theorem exactRemainder_floor (x : ℝ) :
    exactRemainder ⌊x⌋₊ = (Chebyshev.psi x : ℂ) - stepAt backgroundPrimitive ⌊x⌋₊ := by
  unfold exactRemainder
  rw [psi_floor]

/-! ## 2. `R_spectral` et le pont -/

/-- La primitive du canal entier des zéros non triviaux. -/
noncomputable def zeroChannelPrimitive (x : ℝ) : ℂ :=
  (x : ℂ) * ∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm x ρ

/-- **`R_spectral`** : la contribution collective des zéros non triviaux à la marche `N`. Défini
du seul côté spectral. -/
noncomputable def spectralRemainder (N : ℕ) : ℂ := stepAt zeroChannelPrimitive N

/-- La primitive compilée est le fond plus le canal des zéros, pour tout `x > 1`. -/
theorem smoothedZeroPrimitive_eq_background_add_zeros {x : ℝ} (hx : 1 < x) :
    smoothedZeroPrimitive x = backgroundPrimitive x + zeroChannelPrimitive x := by
  have h := smoothedZeroFormula_sub_background hx
  unfold smoothedZeroPrimitive backgroundPrimitive zeroChannelPrimitive
  linear_combination (x : ℂ) * h

/-- **Le pont** : `R_arith = R_spectral`. Le résidu obtenu par soustraction du côté arithmétique
est la contribution collective des zéros. -/
theorem arithmetic_eq_spectral {N : ℕ} (hN : 2 ≤ N) : exactRemainder N = spectralRemainder N := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN2 : (1 : ℝ) < (N : ℝ) + 1 := by linarith
  have h := smoothedZeroPrimitive_nat_difference hN
  rw [smoothedZeroPrimitive_eq_background_add_zeros hN1,
    smoothedZeroPrimitive_eq_background_add_zeros hN2] at h
  unfold exactRemainder spectralRemainder stepAt
  linear_combination -h

/-- Le pont en un réel `x ≥ 2`. -/
theorem arithmetic_eq_spectral_real {x : ℝ} (hx : 2 ≤ x) :
    (Chebyshev.psi x : ℂ) - stepAt backgroundPrimitive ⌊x⌋₊ = spectralRemainder ⌊x⌋₊ := by
  rw [← exactRemainder_floor]
  exact arithmetic_eq_spectral (Nat.le_floor (by exact_mod_cast hx))

/-- Le canal entier se découpe : paquet plus complément. -/
theorem zeroChannelPrimitive_split (S : Set ExplicitIndex) {x : ℝ} (hx : 1 < x) :
    zeroChannelPrimitive x = channelPrimitive S x + channelPrimitive Sᶜ x := by
  unfold zeroChannelPrimitive channelPrimitive
  rw [channel_eq_packet_add_complement S hx]
  ring

/-- `R_spectral` se découpe : paquet plus complément. -/
theorem spectralRemainder_eq_packet_add_complement (S : Set ExplicitIndex) {N : ℕ} (hN : 2 ≤ N) :
    spectralRemainder N = localPacket S N + localPacket Sᶜ N := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN2 : (1 : ℝ) < (N : ℝ) + 1 := by linarith
  unfold spectralRemainder localPacket stepAt
  rw [zeroChannelPrimitive_split S hN1, zeroChannelPrimitive_split S hN2]
  ring

/-! ## 3. `ΔR` entre deux événements arithmétiques -/

/-- **`ΔR(a, b)`** : la différence du résidu arithmétique entre deux marches. -/
noncomputable def remainderBetween (a b : ℕ) : ℂ := exactRemainder b - exactRemainder a

/-- La différence de `R_spectral` entre deux marches. -/
noncomputable def spectralBetween (a b : ℕ) : ℂ := spectralRemainder b - spectralRemainder a

/-- La différence de la contribution d'une partie `S` des indices entre deux marches. -/
noncomputable def packetBetween (S : Set ExplicitIndex) (a b : ℕ) : ℂ :=
  localPacket S b - localPacket S a

/-- L'escalier entre deux marches est la somme des poids de von Mangoldt de l'intervalle. -/
theorem psi_sub_eq_sum_vonMangoldt {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.psi (b : ℝ) - Chebyshev.psi (a : ℝ) = ∑ n ∈ Finset.Ioc a b, Λ n := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hw := thm_weightFromPsi_chebyshev (n := b + 1) (by omega)
    unfold fnWeightFromPsi at hw
    have hcast : ((b + 1 : ℕ) : ℝ) - 1 = (b : ℝ) := by push_cast; ring
    rw [hcast] at hw
    rw [Finset.sum_Ioc_succ_top hab, ← ih]
    linarith

/-- **Côté arithmétique** : `ΔR(a, b)` est la somme des poids des événements de `]a, b]` moins
l'avance du fond. Aucune position radiale n'y figure. -/
theorem remainderBetween_arithmetic {a b : ℕ} (hab : a ≤ b) :
    remainderBetween a b = ((∑ n ∈ Finset.Ioc a b, Λ n : ℝ) : ℂ) -
      (stepAt backgroundPrimitive b - stepAt backgroundPrimitive a) := by
  unfold remainderBetween exactRemainder
  rw [← psi_sub_eq_sum_vonMangoldt hab]
  push_cast
  ring

/-- **Côté spectral** : `ΔR(a, b) = Z(b) − Z(a)`. -/
theorem remainderBetween_eq_spectral {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    remainderBetween a b = spectralBetween a b := by
  unfold remainderBetween spectralBetween
  rw [arithmetic_eq_spectral ha, arithmetic_eq_spectral hb]

/-- Les différences s'enchaînent. -/
theorem remainderBetween_chain (a b c : ℕ) :
    remainderBetween a b + remainderBetween b c = remainderBetween a c := by
  unfold remainderBetween
  ring

/-! ## 4. Paquet et complément entre deux événements -/

/-- **`ΔR(a, b) = L_P(a, b) + C_{¬P}(a, b)`**, pour toute partie `P` des indices. -/
theorem remainderBetween_eq_packet_add_complement (S : Set ExplicitIndex) {a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    remainderBetween a b = packetBetween S a b + packetBetween Sᶜ a b := by
  unfold remainderBetween packetBetween
  rw [exactRemainder_eq_packet_add_complement S ha, exactRemainder_eq_packet_add_complement S hb]
  ring

/-- **La contribution forcée du complément** : `C_{¬P}(a, b) = ΔR(a, b) − L_P(a, b)`. -/
theorem complementBetween_forced (S : Set ExplicitIndex) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    packetBetween Sᶜ a b = remainderBetween a b - packetBetween S a b := by
  rw [remainderBetween_eq_packet_add_complement S ha hb]
  ring

/-! ## 5. La chaîne sur un zéro hors ligne -/

/-- **Lecture inverse sur un zéro hors ligne.** Le zéro `z` hors ligne ; un passage `p` à sa
hauteur ; son raccord grammatical `G` ; les deux premiers consécutifs du raccord, `a` l'occurrence
de la Tour de sortie et `b = M` le premier partagé ; `ΔR(a, b)` lu du côté arithmétique, du côté
spectral, puis découpé en paquet de hauteur (qui contient `z` et son miroir distinct) et
complément. -/
theorem off_inverse_reading {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    ∃ p : TZeroPassage, ∃ hE : 0 < rZeroHeight p.zEarlierMember,
      ∃ hL : 0 < rZeroHeight p.zLaterMember,
      ∃ G : GrammaticalRaccord ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩,
        rZeroHeight p.zEarlierMember = rZeroHeight z.1 ∧
        rZeroHeight p.zLaterMember = rZeroHeight z.1 ∧
        occurrence ⟨p.zEarlierMember, hE⟩ < G.M ∧
        remainderBetween (occurrence ⟨p.zEarlierMember, hE⟩) G.M =
          ((∑ n ∈ Finset.Ioc (occurrence ⟨p.zEarlierMember, hE⟩) G.M, Λ n : ℝ) : ℂ) -
            (stepAt backgroundPrimitive G.M -
              stepAt backgroundPrimitive (occurrence ⟨p.zEarlierMember, hE⟩)) ∧
        remainderBetween (occurrence ⟨p.zEarlierMember, hE⟩) G.M =
          spectralBetween (occurrence ⟨p.zEarlierMember, hE⟩) G.M ∧
        remainderBetween (occurrence ⟨p.zEarlierMember, hE⟩) G.M =
          packetBetween (heightPacket (rZeroHeight z.1)) (occurrence ⟨p.zEarlierMember, hE⟩) G.M +
            packetBetween (heightPacket (rZeroHeight z.1))ᶜ
              (occurrence ⟨p.zEarlierMember, hE⟩) G.M ∧
        memberIndex z ∈ heightPacket (rZeroHeight z.1) ∧
        memberIndex (mirrorMember z) ∈ heightPacket (rZeroHeight z.1) ∧
        memberIndex (mirrorMember z) ≠ memberIndex z := by
  obtain ⟨p, hE, hL, hHz, hSame, _, _, hOccLt⟩ := off_event_increment_without_height hOff
  let G := grammaticalRaccordOf p hE hL
  have hM : G.M = occurrence ⟨p.zLaterMember, hL⟩ := G.entry_eq
  have ha : 2 ≤ occurrence ⟨p.zEarlierMember, hE⟩ := (occurrence_prime _).two_le
  have hlt : occurrence ⟨p.zEarlierMember, hE⟩ < G.M := by rw [hM]; exact hOccLt
  have hb : 2 ≤ G.M := by omega
  exact ⟨p, hE, hL, G, hHz, hSame ▸ hHz, hlt, remainderBetween_arithmetic hlt.le,
    remainderBetween_eq_spectral ha hb, remainderBetween_eq_packet_add_complement _ ha hb,
    memberIndex_mem_heightPacket z, mirrorMember_mem_heightPacket z,
    off_packet_mirror_distinct hOff⟩

#print axioms exactRemainder_arithmetic_only
#print axioms arithmetic_eq_spectral
#print axioms arithmetic_eq_spectral_real
#print axioms spectralRemainder_eq_packet_add_complement
#print axioms psi_sub_eq_sum_vonMangoldt
#print axioms remainderBetween_arithmetic
#print axioms remainderBetween_eq_spectral
#print axioms remainderBetween_eq_packet_add_complement
#print axioms complementBetween_forced
#print axioms off_inverse_reading

end RHV6Fresh
