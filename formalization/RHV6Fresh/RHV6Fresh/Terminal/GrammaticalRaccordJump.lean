/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.InverseReading
import RHV6Fresh.Terminal.TangentialInversion
import RHV6Fresh.Terminal.DiagonalPassage
import RHV6Fresh.Terminal.ArrivalFiberHypotheses
import RHV6Fresh.Voyage.Progression

/-!
# Raccord grammatical au saut d'un événement premier, contacts partagés (théorèmes A et B, 2026-10-15)

Programme de l'auteur (texte collé, 2026-10-15) : **théorème A**, un raccord grammatical contraignant, condition de
contact ou de phase dérivée des poids premiers exacts et de la reconstruction collective ; **théorème B**, cette
condition ne peut pas être satisfaite par une arrivée authentique à `β' < 1/2`, `T'` libre, tous les autres zéros présents.

## Ce que ce module établit (axiomes standard)

* **Saut collectif à chaque événement premier** (`collective_jump_at_prime_event`) : au premier `p = p_n` (`n ≥ 1`),
  la contribution collective de TOUS les zéros non triviaux, lue comme différence du résidu spectral entre `p − 1` et `p`,
  vaut exactement `Λ(p) = log p` moins la seconde différence du fond lisse. C'est la seule entrée des poids exacts dans la
  famille des zéros : la lecture du saut de `ψ` à travers la formule explicite compilée (`arithmetic_eq_spectral`).
* **Complément forcé à l'événement** (`complement_forced_at_prime_event`) : pour toute partie `S` d'indices (par exemple
  le paquet de hauteur de l'arrivée), la contribution du complément au saut est fixée par le saut exact, le fond et la
  contribution de `S`. Identité, aucune borne.
* **Contacts consécutifs partagés** (`shared_consecutive_contacts_same_height`, `shared_consecutive_contacts_same_member`) :
  deux Tours qui partagent deux contacts consécutifs ont la même hauteur, puis la même partie réelle (par l'inversion
  tangentielle, sans aucune hypothèse de branche de phase). Corollaire : deux Tours de hauteurs distinctes, ON comprises,
  ne partagent jamais deux contacts consécutifs (`distinct_heights_no_shared_consecutive_contacts`).
* **Condition de ligne sur un contact** (`contact_eq_line_iff_onLine`) : un contact de l'arrivée coïncide avec le contact
  de ligne de sa hauteur si et seulement si l'arrivée est ON. C'est la forme exacte du « théorème B » du texte collé.

## Portée (à lire avant tout usage)

* Le saut collectif est une IDENTITÉ vraie pour la famille authentique telle qu'elle est, sans hypothèse sur la position
  radiale d'aucun membre. Il ne contraint donc pas `β` : c'est l'obligation que toute famille de vrais zéros de ζ
  satisfait par la formule explicite. Il nomme où les poids exacts entrent ; il ne les transforme pas en borne.
* La condition de ligne sur un contact est une CARACTÉRISATION du but `:399` (`radialFactor = 1`), pas une loi ; la
  grammaire ne l'impose pas : toute `β ∈ ]0, 1/2]` satisfait les obligations de contact connues (`parameter_grid_admissible`,
  rappelé ici par `grammar_contacts_admit_any_radial`).
* Rien dans ce module n'est une prémisse, un `sorry`, un `admit` ni un axiome.
-/

namespace RHV6Fresh

open RHV3Lean ArithmeticFunction

/-! ## 1. Le saut de `ψ` entre deux entiers consécutifs est le poids exact -/

/-- `ψ(N + 1) − ψ(N) = Λ(N + 1)`. -/
theorem psi_step (N : ℕ) :
    Chebyshev.psi ((N : ℝ) + 1) - Chebyshev.psi (N : ℝ) = Λ (N + 1) := by
  have h1 : ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [h1]
  unfold Chebyshev.psi
  rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_Ioc_succ_top (Nat.zero_le N)]
  ring

/-- Le premier de rang `n ≥ 1` vaut au moins `3`. -/
theorem primeAtRank_ge_three {n : ℕ} (hn : 1 ≤ n) : 3 ≤ fnPrimeAtRank n := by
  have h0 : 2 ≤ fnPrimeAtRank 0 := (thm_primeAtRank_isPrime 0).two_le
  have h1 : fnPrimeAtRank 0 < fnPrimeAtRank n := thm_primeAtRank_strictMono (by omega)
  omega

/-- **Saut de `ψ` à l'événement premier** `p = p_n` : `ψ(p) − ψ(p − 1) = log p`. -/
theorem psi_step_at_prime_event {n : ℕ} (hn : 1 ≤ n) :
    Chebyshev.psi (fnPrimeAtRank n : ℝ) - Chebyshev.psi ((fnPrimeAtRank n - 1 : ℕ) : ℝ) =
      Real.log (fnPrimeAtRank n) := by
  have h3 := primeAtRank_ge_three hn
  have hp : ((fnPrimeAtRank n - 1 : ℕ) : ℝ) + 1 = (fnPrimeAtRank n : ℝ) := by
    have : (fnPrimeAtRank n - 1 : ℕ) + 1 = fnPrimeAtRank n := by omega
    exact_mod_cast this
  have hΛ : (fnPrimeAtRank n - 1 : ℕ) + 1 = fnPrimeAtRank n := by omega
  have h := psi_step (fnPrimeAtRank n - 1)
  rw [hp, hΛ] at h
  rw [h]
  exact ArithmeticFunction.vonMangoldt_apply_prime (thm_primeAtRank_isPrime n)

/-! ## 2. Théorème A : le saut collectif des zéros à chaque événement premier -/

/-- Le résidu exact entre deux marches consécutives `N ≥ 2` : différence de `ψ` moins seconde différence du fond. -/
theorem exactRemainder_step (N : ℕ) :
    exactRemainder (N + 1) - exactRemainder N =
      ((Chebyshev.psi ((N : ℝ) + 1) - Chebyshev.psi (N : ℝ) : ℝ) : ℂ) -
        (stepAt backgroundPrimitive (N + 1) - stepAt backgroundPrimitive N) := by
  unfold exactRemainder
  push_cast
  ring

/-- **Théorème A — saut collectif à l'événement premier** `p = p_n`, `n ≥ 1` : la contribution collective de TOUS les
zéros non triviaux à la marche `p` (différence du résidu spectral entre `p − 1` et `p`) vaut exactement le poids exact
`Λ(p) = log p` moins la seconde différence du fond lisse. Dérivé des poids premiers (`Λ(p) = log p`) et de la
reconstruction collective (`arithmetic_eq_spectral`). Identité sur la famille authentique, aucune hypothèse radiale. -/
theorem collective_jump_at_prime_event {n : ℕ} (hn : 1 ≤ n) :
    spectralRemainder (fnPrimeAtRank n) - spectralRemainder (fnPrimeAtRank n - 1) =
      ((Real.log (fnPrimeAtRank n) : ℝ) : ℂ) -
        (stepAt backgroundPrimitive (fnPrimeAtRank n) - stepAt backgroundPrimitive (fnPrimeAtRank n - 1)) := by
  have h3 := primeAtRank_ge_three hn
  set N := fnPrimeAtRank n - 1 with hNdef
  have hN2 : 2 ≤ N := by omega
  have hN1 : N + 1 = fnPrimeAtRank n := by omega
  have hA := arithmetic_eq_spectral hN2
  have hB := arithmetic_eq_spectral (show 2 ≤ N + 1 by omega)
  have hstep := exactRemainder_step N
  have hψ : Chebyshev.psi ((N : ℝ) + 1) - Chebyshev.psi (N : ℝ) = Real.log (fnPrimeAtRank n) := by
    have hp : ((N : ℕ) : ℝ) + 1 = (fnPrimeAtRank n : ℝ) := by exact_mod_cast hN1
    rw [hp]
    exact psi_step_at_prime_event hn
  rw [hψ] at hstep
  rw [← hN1, ← hA, ← hB, hstep]
  rw [show ((N + 1 : ℕ) : ℝ) = (fnPrimeAtRank n : ℝ) by exact_mod_cast hN1]

/-- **Complément forcé à l'événement** : pour toute partie `S` des indices, la contribution du complément au saut est
fixée par le saut exact, le fond et la contribution de `S`. Identité (compensation au niveau de l'événement), aucune
borne : elle vaut pour toute partie `S` et toute position radiale de ses membres. -/
theorem complement_forced_at_prime_event (S : Set ExplicitIndex) {n : ℕ} (hn : 1 ≤ n) :
    localPacket Sᶜ (fnPrimeAtRank n) - localPacket Sᶜ (fnPrimeAtRank n - 1) =
      (((Real.log (fnPrimeAtRank n) : ℝ) : ℂ) -
        (stepAt backgroundPrimitive (fnPrimeAtRank n) - stepAt backgroundPrimitive (fnPrimeAtRank n - 1))) -
        (localPacket S (fnPrimeAtRank n) - localPacket S (fnPrimeAtRank n - 1)) := by
  have h3 := primeAtRank_ge_three hn
  have hJ := collective_jump_at_prime_event hn
  have hS1 := spectralRemainder_eq_packet_add_complement S (N := fnPrimeAtRank n) (by omega)
  have hS0 := spectralRemainder_eq_packet_add_complement S (N := fnPrimeAtRank n - 1) (by omega)
  rw [← hJ, hS1, hS0]
  ring

/-- Le saut collectif à l'occurrence du membre atteint par un passage (son premier de rang) : instance de A sur
l'événement de l'arrivée, `Occ(l) = p_{n_l}`. -/
theorem collective_jump_at_arrival_occurrence (z : TrueZero) (hn : 1 ≤ nZeroSourceIndex z.1) :
    spectralRemainder (occurrence z) - spectralRemainder (occurrence z - 1) =
      ((Real.log (occurrence z) : ℝ) : ℂ) -
        (stepAt backgroundPrimitive (occurrence z) - stepAt backgroundPrimitive (occurrence z - 1)) := by
  rw [occurrence_eq_primeAtRank]
  exact collective_jump_at_prime_event hn

/-! ## 3. Contacts consécutifs partagés : hauteur puis partie réelle -/

theorem contactPlusAt_eq_succ (z : TrueZero) (k : ℤ) : contactPlusAt z k = contactMinusAt z (k + 1) := rfl

/-- **Deux Tours qui partagent deux contacts consécutifs ont la même hauteur** : `T = π / log(C_{k+1}/C_k)`. -/
theorem shared_consecutive_contacts_same_height (z w : TrueZero) (k j : ℤ)
    (ha : contactMinusAt z k = contactMinusAt w j)
    (hb : contactMinusAt z (k + 1) = contactMinusAt w (j + 1)) :
    rZeroHeight z.1 = rZeroHeight w.1 := by
  rw [← inversion_height z k, ← inversion_height w j, contactPlusAt_eq_succ, contactPlusAt_eq_succ, ha, hb]

/-- **… et la même partie réelle** : `tan(T log C_k) = T/β` sur chacune, même `T`, même `C_k`. Aucune hypothèse de branche
de phase n'est nécessaire : la tangente est lue directement. -/
theorem shared_consecutive_contacts_same_member (z w : TrueZero) (k j : ℤ)
    (ha : contactMinusAt z k = contactMinusAt w j)
    (hb : contactMinusAt z (k + 1) = contactMinusAt w (j + 1)) :
    rZeroHeight z.1 = rZeroHeight w.1 ∧ rZeroRadialPosition z.1 = rZeroRadialPosition w.1 := by
  have hT := shared_consecutive_contacts_same_height z w k j ha hb
  refine ⟨hT, ?_⟩
  have h1 := contactAt_tangent_minus z k
  have h2 := contactAt_tangent_minus w j
  rw [ha, hT] at h1
  rw [h1] at h2
  have hTw : rZeroHeight w.1 ≠ 0 := w.2.ne'
  have hβz := (thm_zeroRadialPosition_positive z.1).ne'
  have hβw := (thm_zeroRadialPosition_positive w.1).ne'
  field_simp at h2
  linarith [mul_comm (rZeroHeight w.1) (rZeroRadialPosition w.1)]

/-- Corollaire : deux Tours de hauteurs distinctes ne partagent jamais deux contacts consécutifs. En particulier les Tours
ON de zéros différents (toutes de hauteurs distinctes sous leur ordre) n'ont pas de suite de contacts commune. -/
theorem distinct_heights_no_shared_consecutive_contacts (z w : TrueZero) (hT : rZeroHeight z.1 ≠ rZeroHeight w.1)
    (k j : ℤ) :
    ¬ (contactMinusAt z k = contactMinusAt w j ∧ contactMinusAt z (k + 1) = contactMinusAt w (j + 1)) :=
  fun h => hT (shared_consecutive_contacts_same_height z w k j h.1 h.2)

/-! ## 4. Théorème B, forme exacte : la condition de ligne sur un contact caractérise l'arrivée ON -/

/-- **Condition de ligne sur un contact** : un contact d'un membre coïncide avec le contact de la Tour de ligne à sa
hauteur si et seulement si le membre est ON. Si la grammaire imposait à la Tour d'arrivée la géométrie de contacts d'une
Tour ON (même un seul contact), `β_l = 1/2` suivrait. C'est une caractérisation du but `radialFactor = 1`. -/
theorem contact_eq_line_iff_onLine (z : TrueZero) (k : ℤ) :
    contactMinusAt z k = lineContact (rZeroHeight z.1) k ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  rw [contact_eq_line_mul_radial, ← radialFactor_eq_one_iff]
  have hpos := lineContact_pos (rZeroHeight z.1) k
  constructor
  · intro h
    have : lineContact (rZeroHeight z.1) k * radialFactor z = lineContact (rZeroHeight z.1) k * 1 := by
      rw [mul_one]; exact h
    exact mul_left_cancel₀ hpos.ne' this
  · intro h; rw [h, mul_one]

/-- **Ce que la grammaire n'impose pas** : pour toute `β ∈ ]0, 1/2]`, les contacts `lineContact T k · λ(β, T)` avec
`1 ≤ λ < e^{1/(2T²)}` satisfont toutes les obligations de contact connues. La condition de ligne (`λ = 1`) n'est donc
dérivée d'aucune obligation de contact ; elle est le but. Rappel de `parameter_grid_admissible`. -/
theorem grammar_contacts_admit_any_radial {β T : ℝ} (hT : 0 < T) (hβ : 0 < β) (hβ2 : β ≤ 1 / 2) :
    1 ≤ paramFactor β T ∧ paramFactor β T < Real.exp (1 / (2 * T) / T) ∧
      ∀ k : ℤ, windingContact β T k = lineContact T k * paramFactor β T :=
  parameter_grid_admissible hT hβ hβ2

end RHV6Fresh
