/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RegimeTower

/-!
# RHV6Fresh — l'identité spectrale de chaque membre dans la somme (auteur, 2026-09-30)

Énoncé de l'auteur : les ensembles de zéros doivent rester cohérents ; c'est leur infinité qui est
additionnée ; on ne peut retirer aucun membre ; l'insertion d'un membre est réfutée par la somme et
par la contribution individuelle de chacun ; l'identité de chaque membre est préservée dans la
somme ; pas d'intrus.

Ce qui est compilé ici, sans prémisse :

* **Les profils `x ↦ x^s` sont linéairement indépendants** sur `x > 1`, pour des exposants
  complexes distincts (`cpow_finite_independent`, par le lemme de Dedekind). Même énoncé pour le
  noyau de la formule explicite compilée (`perron_finite_independent`) et pour les indices de la
  somme (`member_weights_zero_of_contribution_zero`).
* **Un profil porte son identité** : `x^s = x^{s'}` sur `x > 1` force `s = s'`
  (`cpow_profile_injective`) ; deux membres de même terme sont le même membre
  (`zeroTerm_profile_injective`) ; l'exposant `β` se lit sur le seul module du terme
  (`member_radial_read_on_profile`) et la fréquence `T` sur le seul pas de ses contacts
  (`member_height_read_on_profile`).
* **Aucun membre n'est retirable** : son terme ne s'annule en aucun `x > 0`
  (`member_term_ne_zero`) et la somme privée de ce membre diffère de la somme en tout `x > 1`
  (`no_member_removable`).
* **Pas d'intrus, pas de compensation finie** : ajouter à la somme un nombre fini de termes en des
  points quelconques (zéros ou non), avec des poids non tous nuls, change la somme en au moins un
  `x > 1` (`no_finite_intruder`). Un profil hors ligne n'est combinaison finie d'aucuns autres
  profils, en ligne ou non (`profile_not_finite_combination`,
  `off_profile_not_combination_of_onLine`).
* **Deux paquets finis de même contribution sont le même paquet**
  (`finite_packets_eq_of_contribution_eq`).

Borne : ces énoncés ne lisent pas la position radiale ; ils valent pour tout ensemble d'exposants.
Ils disent que la décomposition retrouve les zéros tels qu'ils sont, en ligne ou non.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Les profils `x^s` comme caractères, et leur indépendance -/

/-- Le profil `t ↦ exp(t·s)` (`x = e^t`, `t ≥ 0`) comme caractère du monoïde additif `ℝ≥0`. -/
noncomputable def expCharacter (s : ℂ) : Multiplicative NNReal →* ℂ where
  toFun t := Complex.exp ((((Multiplicative.toAdd t : NNReal) : ℝ) : ℂ) * s)
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, NNReal.coe_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem expCharacter_apply (s : ℂ) (t : NNReal) :
    expCharacter s (Multiplicative.ofAdd t) = Complex.exp (((t : ℝ) : ℂ) * s) := rfl

/-- Deux exposants distincts donnent deux caractères distincts. -/
theorem expCharacter_injective : Function.Injective expCharacter := by
  intro s s' h
  by_contra hne
  have hpos : 0 < ‖s - s'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set t : NNReal := ⟨Real.pi / ‖s - s'‖, (div_pos Real.pi_pos hpos).le⟩ with ht
  have htv : (t : ℝ) = Real.pi / ‖s - s'‖ := rfl
  have h1 : Complex.exp (((t : ℝ) : ℂ) * s) = Complex.exp (((t : ℝ) : ℂ) * s') := by
    rw [← expCharacter_apply, ← expCharacter_apply, h]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  have h3 : ((t : ℝ) : ℂ) * (s - s') = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [mul_sub, hn]; ring
  have h4 := congrArg norm h3
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg t), htv,
    div_mul_cancel₀ _ hpos.ne', norm_mul, Complex.norm_intCast, norm_mul, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_ofNat] at h4
  have h5 : (2 : ℝ) * |(n : ℝ)| = 1 := by
    have := Real.pi_pos
    have h6 : Real.pi * (2 * |(n : ℝ)|) = Real.pi * 1 := by linarith
    exact mul_left_cancel₀ this.ne' h6
  have h7 : (2 : ℤ) * |n| = 1 := by exact_mod_cast h5
  rcases abs_cases n with ⟨h8, _⟩ | ⟨h8, _⟩ <;> omega

/-- **Indépendance des profils** : une combinaison finie de profils `x^s`, d'exposants complexes
distincts, qui s'annule pour tout `x > 1`, a tous ses coefficients nuls. -/
theorem cpow_finite_independent (S : Finset ℂ) (c : ℂ → ℂ)
    (h : ∀ x : ℝ, 1 < x → ∑ s ∈ S, c s * (x : ℂ) ^ s = 0) : ∀ s ∈ S, c s = 0 := by
  have hli : LinearIndependent ℂ (fun s : ℂ => (expCharacter s : Multiplicative NNReal → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative NNReal) ℂ).comp expCharacter
      expCharacter_injective
  have key := linearIndependent_iff'.mp hli S (fun s => c s * Complex.exp s) (by
    funext t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hx : 1 < Real.exp (((Multiplicative.toAdd t : NNReal) : ℝ) + 1) :=
      Real.one_lt_exp_iff.mpr (by positivity)
    rw [← h _ hx]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, mul_assoc]
    congr 1
    change Complex.exp s * Complex.exp ((((Multiplicative.toAdd t : NNReal) : ℝ) : ℂ) * s) = _
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring)
  intro s hs
  exact (mul_eq_zero.mp (key s hs)).resolve_right (Complex.exp_ne_zero s)

/-- **Un profil porte son exposant** : `x^s = x^{s'}` pour tout `x > 1` force `s = s'`. -/
theorem cpow_profile_injective {s s' : ℂ}
    (h : ∀ x : ℝ, 1 < x → (x : ℂ) ^ s = (x : ℂ) ^ s') : s = s' := by
  by_contra hne
  have key := cpow_finite_independent {s, s'} (fun u => if u = s then 1 else -1) (by
    intro x hx
    rw [Finset.sum_pair hne, if_pos rfl, if_neg (Ne.symm hne), h x hx]
    ring)
  have := key s (Finset.mem_insert_self _ _)
  simp at this

/-- **Un profil n'est combinaison finie d'aucuns autres** : si `s ∉ S`, aucune famille de
coefficients ne donne `x^s = Σ_{u ∈ S} c_u · x^u` pour tout `x > 1`. -/
theorem profile_not_finite_combination {s : ℂ} {S : Finset ℂ} (hs : s ∉ S) (c : ℂ → ℂ) :
    ¬ ∀ x : ℝ, 1 < x → (x : ℂ) ^ s = ∑ u ∈ S, c u * (x : ℂ) ^ u := by
  intro h
  have key := cpow_finite_independent (insert s S) (fun u => if u = s then 1 else -c u) (by
    intro x hx
    rw [Finset.sum_insert hs, if_pos rfl, one_mul, h x hx, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun u hu => ?_
    rw [if_neg (fun hus : u = s => hs (hus ▸ hu))]
    ring)
  have := key s (Finset.mem_insert_self _ _)
  simp at this

/-! ## 2. Le noyau de la formule explicite compilée -/

/-- **Indépendance pour le noyau compilé** `Perron.f x s = x^s / (s (s + 1))`. -/
theorem perron_finite_independent (S : Finset ℂ) (c : ℂ → ℂ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s + 1 ≠ 0)
    (h : ∀ x : ℝ, 1 < x → ∑ s ∈ S, c s * Perron.f x s = 0) : ∀ s ∈ S, c s = 0 := by
  have key := cpow_finite_independent S (fun s => c s / (s * (s + 1))) (by
    intro x hx
    rw [← h x hx]
    refine Finset.sum_congr rfl fun s _ => ?_
    change c s / (s * (s + 1)) * (x : ℂ) ^ s = c s * ((x : ℂ) ^ s / (s * (s + 1)))
    ring)
  intro s hs
  have h1 := key s hs
  obtain ⟨h0, h1'⟩ := hS s hs
  exact (div_eq_zero_iff.mp h1).resolve_right (mul_ne_zero h0 h1')

theorem explicitIndex_ne_zero (ρ : ExplicitIndex) : (ρ : ℂ) ≠ 0 ∧ (ρ : ℂ) + 1 ≠ 0 := by
  have hstrip := isNontrivialZetaZero_re_mem_Ioo ρ.property
  constructor
  · intro h0
    have := hstrip.1
    rw [h0] at this
    simp at this
  · intro h0
    have h' := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h'
    linarith [hstrip.1]

/-- **Aucun membre n'est retirable, terme à terme** : le terme d'un indice dans le canal compilé
ne s'annule en aucun `x > 0`. -/
theorem member_term_ne_zero (ρ : ExplicitIndex) {x : ℝ} (hx : 0 < x) :
    nontrivialZeroResidueTerm x ρ ≠ 0 := by
  unfold nontrivialZeroResidueTerm
  obtain ⟨h0, h1⟩ := explicitIndex_ne_zero ρ
  have hm : (zetaZeroMultiplicity (ρ : ℂ) : ℂ) ≠ 0 := by
    exact_mod_cast (zetaZeroMultiplicity_pos ρ.property.1).ne'
  have hpow : (x : ℂ) ^ (ρ : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
    exact Complex.exp_ne_zero _
  exact mul_ne_zero (neg_ne_zero.mpr hm) (div_ne_zero hpow (mul_ne_zero h0 h1))

/-- **Aucun membre n'est retirable dans la somme** : pour tout `x > 1`, la somme sur tous les
indices sauf `ρ` diffère de la somme complète, exactement du terme de `ρ`. -/
theorem no_member_removable (ρ : ExplicitIndex) {x : ℝ} (hx : 1 < x) :
    (∑' σ : ExplicitIndex, nontrivialZeroResidueTerm x σ) =
        nontrivialZeroResidueTerm x ρ + channelOn {ρ}ᶜ x ∧
      channelOn {ρ}ᶜ x ≠ ∑' σ : ExplicitIndex, nontrivialZeroResidueTerm x σ := by
  have hsplit := channel_eq_packet_add_complement {ρ} hx
  rw [channelOn_singleton] at hsplit
  refine ⟨hsplit, fun h => ?_⟩
  rw [hsplit] at h
  exact member_term_ne_zero ρ (by linarith) (by linear_combination -h)

/-- **Pas d'intrus, pas de compensation finie** : si l'on ajoute au canal un nombre fini de termes
en des points quelconques (zéros ou non, hors `0` et `−1`) avec des poids non tous nuls, la somme
change en au moins un `x > 1`. -/
theorem no_finite_intruder (S : Finset ℂ) (c : ℂ → ℂ) (hS : ∀ s ∈ S, s ≠ 0 ∧ s + 1 ≠ 0)
    (hc : ∃ s ∈ S, c s ≠ 0) :
    ∃ x : ℝ, 1 < x ∧
      (∑' σ : ExplicitIndex, nontrivialZeroResidueTerm x σ) + ∑ s ∈ S, c s * Perron.f x s ≠
        ∑' σ : ExplicitIndex, nontrivialZeroResidueTerm x σ := by
  by_contra hno
  push Not at hno
  obtain ⟨s, hs, hcs⟩ := hc
  exact hcs (perron_finite_independent S c hS (fun x hx => by
    have := hno x hx
    linear_combination this) s hs)

/-- **Des poids sur un ensemble fini d'indices, de contribution nulle pour tout `x > 1`, sont
nuls** : aucune modification finie des multiplicités ne conserve la somme. -/
theorem member_weights_zero_of_contribution_zero (F : Finset ExplicitIndex)
    (w : ExplicitIndex → ℂ)
    (h : ∀ x : ℝ, 1 < x → ∑ ρ ∈ F, w ρ * Perron.f x (ρ : ℂ) = 0) : ∀ ρ ∈ F, w ρ = 0 := by
  classical
  have hinj : Set.InjOn (fun ρ : ExplicitIndex => (ρ : ℂ)) (F : Set ExplicitIndex) :=
    fun _ _ _ _ hab => Subtype.ext hab
  have key := perron_finite_independent (F.image (fun ρ : ExplicitIndex => (ρ : ℂ)))
    (fun s => if hs : IsNontrivialZetaZero s then w ⟨s, hs⟩ else 0)
    (by
      intro s hs
      obtain ⟨ρ, _, rfl⟩ := Finset.mem_image.mp hs
      exact explicitIndex_ne_zero ρ)
    (by
      intro x hx
      rw [Finset.sum_image hinj, ← h x hx]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [dif_pos ρ.property])
  intro ρ hρ
  have := key (ρ : ℂ) (Finset.mem_image_of_mem _ hρ)
  rwa [dif_pos ρ.property] at this

/-- **Deux paquets finis de même contribution sont le même paquet** : sur un ensemble fini
d'indices, la contribution (pour tout `x > 1`) détermine le poids de chaque indice. -/
theorem finite_packets_eq_of_contribution_eq (F : Finset ExplicitIndex)
    (w w' : ExplicitIndex → ℂ)
    (h : ∀ x : ℝ, 1 < x → ∑ ρ ∈ F, w ρ * Perron.f x (ρ : ℂ) =
      ∑ ρ ∈ F, w' ρ * Perron.f x (ρ : ℂ)) : ∀ ρ ∈ F, w ρ = w' ρ := by
  intro ρ hρ
  have key := member_weights_zero_of_contribution_zero F (fun σ => w σ - w' σ) (by
    intro x hx
    simp only [sub_mul, Finset.sum_sub_distrib, h x hx, sub_self]) ρ hρ
  exact sub_eq_zero.mp key

/-! ## 3. L'identité d'un membre, lue sur son seul profil -/

/-- **Deux membres de même terme sont le même membre.** -/
theorem zeroTerm_profile_injective {z w : TrueZero}
    (h : ∀ x : ℝ, 1 < x → zeroTerm z x = zeroTerm w x) : z = w := by
  by_contra hne
  have hρ : zeroPoint z ≠ zeroPoint w := fun h' => hne (Subtype.ext (Subtype.ext h'))
  have key := cpow_finite_independent {zeroPoint z, zeroPoint w}
    (fun u => if u = zeroPoint z then (zeroPoint z)⁻¹ else -(zeroPoint w)⁻¹) (by
      intro x hx
      rw [Finset.sum_pair hρ, if_pos rfl, if_neg (Ne.symm hρ)]
      have := h x hx
      unfold zeroTerm at this
      rw [div_eq_mul_inv, div_eq_mul_inv] at this
      linear_combination this)
  have h1 := key (zeroPoint z) (Finset.mem_insert_self _ _)
  rw [if_pos rfl] at h1
  exact zeroPoint_ne_zero z (inv_eq_zero.mp h1)

/-- **L'exposant `β` se lit sur le seul module du terme** : entre deux abscisses, le module du
terme d'un membre est multiplié par `(x₂/x₁)^β`. -/
theorem member_radial_read_on_profile (z : TrueZero) {x₁ x₂ : ℝ} (h₁ : 0 < x₁) (h₂ : 0 < x₂) :
    ‖zeroTerm z x₂‖ / ‖zeroTerm z x₁‖ = (x₂ / x₁) ^ rZeroRadialPosition z.1 := by
  rw [zeroTerm_norm h₁, zeroTerm_norm h₂, Real.div_rpow h₂.le h₁.le]
  have hN := (zeroPoint_norm_pos z).ne'
  have hp := (Real.rpow_pos_of_pos h₁ (rZeroRadialPosition z.1)).ne'
  field_simp

/-- **La fréquence `T` se lit sur le seul pas des contacts du terme** : `T = π / pas`, et les
contacts sont exactement les abscisses où le terme est réel. -/
theorem member_height_read_on_profile (z : TrueZero) (k : ℤ) :
    rZeroHeight z.1 =
        Real.pi / (Real.log (contactPlusAt z k) - Real.log (contactMinusAt z k)) ∧
      ∀ {x : ℝ}, 0 < x → ((zeroTerm z x).im = 0 ↔ ∃ j : ℤ, x = contactMinusAt z j) := by
  refine ⟨?_, fun hx => zeroTerm_real_iff_ray hx⟩
  rw [contactAt_consecutive_logWidth]
  have hT : rZeroHeight z.1 ≠ 0 := z.2.ne'
  field_simp

/-- **Un profil hors ligne n'est combinaison finie d'aucuns profils en ligne** : si tous les
exposants de `S` ont partie réelle `1/2` et si `z` est hors ligne, aucune famille de coefficients
ne donne `x^{ρ_z} = Σ_{u ∈ S} c_u · x^u` pour tout `x > 1`. -/
theorem off_profile_not_combination_of_onLine {z : TrueZero} (hOff : PIsOffCriticalLine z.1)
    (S : Finset ℂ) (hS : ∀ u ∈ S, u.re = 1 / 2) (c : ℂ → ℂ) :
    ¬ ∀ x : ℝ, 1 < x → (x : ℂ) ^ zeroPoint z = ∑ u ∈ S, c u * (x : ℂ) ^ u :=
  profile_not_finite_combination (fun hmem => hOff (hS _ hmem)) c

#print axioms expCharacter_injective
#print axioms cpow_finite_independent
#print axioms cpow_profile_injective
#print axioms profile_not_finite_combination
#print axioms perron_finite_independent
#print axioms member_term_ne_zero
#print axioms no_member_removable
#print axioms no_finite_intruder
#print axioms member_weights_zero_of_contribution_zero
#print axioms finite_packets_eq_of_contribution_eq
#print axioms zeroTerm_profile_injective
#print axioms member_radial_read_on_profile
#print axioms member_height_read_on_profile
#print axioms off_profile_not_combination_of_onLine

end RHV6Fresh
