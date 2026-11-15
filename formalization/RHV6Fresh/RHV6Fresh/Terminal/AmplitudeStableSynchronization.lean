/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GapSynchronization
import RHV6Fresh.Terminal.InsertionExclusion
import RHV6Fresh.Terminal.AuthenticPassageProfile
import RHV6Fresh.Terminal.DiagonalPassage

/-!
# RHV6Fresh — synchronisation à amplitude stable, fréquences seules (E244, 2026-10-13)

Énoncé de l'auteur (2026-10-13) : « les zéros sont reliés entre eux par une synchronisation nécessaire, impossible à obtenir
par des changements d'amplitude avec les écarts des premiers ; la synchronisation avec le zéro initial n'est possible qu'avec
une amplitude stable et seulement des changements de fréquences ». Audit externe collé le même jour : garder le but `:399`
inchangé, ne jamais supposer l'amplitude commune de l'arrivée, tester le contre-modèle `β = 1/4`, utiliser les vrais
coefficients de ζ.

Ce module écrit l'énoncé de l'auteur comme CONTRAT Lean et établit exactement ce qu'il vaut.

1. **Contrat** `AmplitudeStableSync p` : la densité exacte `x^{ρ_l − 1}` du membre atteint a, en toute abscisse `x > 0`,
   `x ≠ 1`, l'amplitude de celle du départ `x^{ρ_e − 1}`. Forme « fréquences seules » : le rapport des deux densités est de
   module `1` (`frequency_only_iff`), c'est-à-dire que seule la phase `e^{i(T_l − T_e) log x}` distingue les deux Tours.
2. **Ce qu'il vaut** : `AmplitudeStableSync p ⟺ β_l = β_e` (`amplitudeStableSync_iff`, une seule abscisse suffit) ; depuis un
   départ ON il ferme le but `radialFactor = 1` (`amplitudeStableSync_closes`) ; quantifié sur tous les passages qui montent
   depuis un membre ON, il ÉQUIVAUT à RH sous l'ancre (`amplitudeStable_law_iff_riemannHypothesis`, forme avec historique
   `amplitudeStable_history_law_iff_riemannHypothesis`). C'est une CARACTÉRISATION du but, pas une loi plus faible.
3. **Remplacement d'un point** : dans la famille lissée canonique, remplacer la contribution d'un point `ρ` par celle d'un
   autre point `ρ' ≠ ρ` (coefficient `−m/(ρ'(ρ'+1))` recalculé, toutes les autres contributions conservées) ne reconstruit
   pas le reste lissé (`replacement_not_reconstruct`). Instances : changement d'amplitude à fréquence fixée
   (`amplitude_change_not_reconstruct`, `ρ' = ρ + δ`, `δ` réel) et changement de fréquence à amplitude fixée
   (`frequency_change_not_reconstruct`, `ρ' = ρ + iδ`). La reconstruction exacte exclut TOUT remplacement, elle ne distingue
   pas les changements d'amplitude des changements de fréquence.
4. **Portée** : le vrai zéro atteint, quelle que soit sa partie réelle, reconstruit le reste par théorème
   (`smoothedRemainder_eq_tsum_residueTerm`, énoncé sans aucune hypothèse de position) ; un point remplacé n'est pas un zéro
   de ζ. Aucun théorème de ce module ne dérive `AmplitudeStableSync p` du champ arithmétique : c'est le but `:399`
   (sonde `experiments/e244_amplitude_stable_sync/ProbeE244_AmplitudeStable.lean`, même but ; contrôle TDD : le contrat
   en hypothèse ferme le corps).
-/

namespace RHV6Fresh

open RHV3Lean Complex Filter Topology

/-! ## 1. Le contrat : amplitude stable, fréquences seules -/

/-- Densité exacte du canal `ψ` portée par le membre `z` : `x^{ρ − 1}` (rien n'est normalisé). -/
noncomputable def memberDensity (z : TNonTrivialZetaZero) (x : ℝ) : ℂ := (x : ℂ) ^ ((z.1 : ℂ) - 1)

theorem rZeroRadialPosition_eq_re (z : TNonTrivialZetaZero) : rZeroRadialPosition z = (z.1 : ℂ).re := rfl

/-- Module de la densité exacte : `x^{β − 1}`. -/
theorem memberDensity_norm (z : TNonTrivialZetaZero) {x : ℝ} (hx : 0 < x) :
    ‖memberDensity z x‖ = x ^ (rZeroRadialPosition z - 1) :=
  density_norm _ hx

/-- **Contrat de synchronisation à amplitude stable** sur un passage `p : e → l` : en toute abscisse `x > 0`, `x ≠ 1`, la
densité du membre atteint a l'amplitude de celle du départ. -/
def AmplitudeStableSync (p : TZeroPassage) : Prop :=
  ∀ x : ℝ, 0 < x → x ≠ 1 → ‖memberDensity p.zLaterMember x‖ = ‖memberDensity p.zEarlierMember x‖

/-- **Le contrat est la même partie réelle** : une seule abscisse (`x = 2`) suffit dans un sens, toutes suivent dans l'autre. -/
theorem amplitudeStableSync_iff (p : TZeroPassage) :
    AmplitudeStableSync p ↔ rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember := by
  constructor
  · intro h
    exact (common_amplitude_iff _ _ (by norm_num : (0 : ℝ) < 2) (by norm_num)).mp (h 2 (by norm_num) (by norm_num))
  · intro h x hx hx1
    exact (common_amplitude_iff _ _ hx hx1).mpr h

/-- Rapport des deux densités : module `x^{β_l − β_e}`. -/
theorem density_ratio_norm (p : TZeroPassage) {x : ℝ} (hx : 0 < x) :
    ‖memberDensity p.zLaterMember x / memberDensity p.zEarlierMember x‖ =
      x ^ (rZeroRadialPosition p.zLaterMember - rZeroRadialPosition p.zEarlierMember) := by
  rw [norm_div, memberDensity_norm _ hx, memberDensity_norm _ hx, ← Real.rpow_sub hx]
  congr 1; ring

/-- **« Seules les fréquences changent »** : le rapport des densités est de module `1` en toute abscisse ⟺ amplitude
stable. Le contenu est alors la seule phase `e^{i(T_l − T_e) log x}`. -/
theorem frequency_only_iff (p : TZeroPassage) :
    (∀ x : ℝ, 0 < x → x ≠ 1 → ‖memberDensity p.zLaterMember x / memberDensity p.zEarlierMember x‖ = 1) ↔
      AmplitudeStableSync p := by
  constructor
  · intro h x hx hx1
    have hne : ‖memberDensity p.zEarlierMember x‖ ≠ 0 := by
      rw [memberDensity_norm _ hx]; exact (Real.rpow_pos_of_pos hx _).ne'
    have := h x hx hx1
    rw [norm_div, div_eq_one_iff_eq hne] at this
    exact this
  · intro h x hx hx1
    have hne : ‖memberDensity p.zEarlierMember x‖ ≠ 0 := by
      rw [memberDensity_norm _ hx]; exact (Real.rpow_pos_of_pos hx _).ne'
    rw [norm_div, div_eq_one_iff_eq hne]
    exact h x hx hx1

/-- Un membre et son miroir : le contrat entre eux ⟺ `β = 1/2`. -/
theorem amplitudeStable_mirror_iff (z : TNonTrivialZetaZero) {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    ‖memberDensity z x‖ = ‖(x : ℂ) ^ ((1 - starRingEnd ℂ (z.1 : ℂ)) - 1)‖ ↔ rZeroRadialPosition z = 1 / 2 :=
  common_amplitude_mirror_iff _ hx hx1

/-! ## 2. Ce que le contrat ferme, et ce qu'il vaut globalement -/

/-- **Fermeture du but `:399` sous le contrat** : depuis un départ ON, l'amplitude stable donne `radialFactor = 1` au membre
atteint. Le contrat n'est dérivé d'aucun théorème : c'est le but écrit sur les densités. -/
theorem amplitudeStableSync_closes (p : TZeroPassage) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) (h : AmplitudeStableSync p) :
    radialFactor ⟨p.zLaterMember, hL⟩ = 1 := by
  refine (radialFactor_eq_one_iff ⟨p.zLaterMember, hL⟩).mpr ?_
  have hβ : rZeroRadialPosition p.zLaterMember = 1 / 2 := by
    rw [(amplitudeStableSync_iff p).mp h, hOn]
  exact hβ

/-- **La loi « amplitude stable sur tout passage qui monte depuis un membre ON » équivaut à RH** sous l'ancre. -/
theorem amplitudeStable_law_iff_riemannHypothesis (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    (∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 → AmplitudeStableSync p) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_anchor_and_conservation h₁
      (fun p hE hV hOn => (amplitudeStableSync_iff p).mp (h p hE hV hOn))
  · intro hRH p hE hV hOn
    exact (amplitudeStableSync_iff p).mpr (conservation_of_riemannHypothesis hRH p hE hV hOn)

/-- Forme avec historique ON (celle du but `:399`) : même équivalence. -/
theorem amplitudeStable_history_law_iff_riemannHypothesis
    (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    (∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      AmplitudeStableSync p) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_anchor_and_history_conservation h₁
      (fun p hE hV hOn hHist => (amplitudeStableSync_iff p).mp (h p hE hV hOn hHist))
  · intro hRH p hE hV hOn hHist
    exact (amplitudeStableSync_iff p).mpr
      (history_conservation_of_conservation (conservation_of_riemannHypothesis hRH) p hE hV hOn hHist)

/-! ## 3. Remplacement d'un point : aucun changement, d'amplitude ou de fréquence, ne reconstruit -/

/-- Deux points distincts de hauteur `> 0` : la différence de leurs contributions lissées (même multiplicité `m > 0`)
n'est pas identiquement nulle sur `x > 1`. -/
theorem replacement_defect_not_identically_zero {ρ ρ' : ℂ} (hne : ρ' ≠ ρ) (hre : ρ.re ≤ 1) (hre' : ρ'.re ≤ 1)
    (him : 0 < ρ.im) (him' : 0 < ρ'.im) {m : ℕ} (hm : 0 < m) :
    ∃ x : ℝ, 1 < x ∧ -pointSmoothedPairContribution m ρ x + pointSmoothedPairContribution m ρ' x ≠ 0 := by
  have hρ' : ρ * (ρ + 1) ≠ 0 :=
    mul_ne_zero (point_ne_zero_of_im_pos him) (point_add_one_ne_zero_of_im_pos him)
  have hρ'' : ρ' * (ρ' + 1) ≠ 0 :=
    mul_ne_zero (point_ne_zero_of_im_pos him') (point_add_one_ne_zero_of_im_pos him')
  have hinj : Function.Injective (fun b : Bool => if b then ρ else ρ') := by
    intro b₁ b₂ h
    cases b₁ <;> cases b₂
    · rfl
    · exact absurd (by simpa using h) hne
    · exact absurd (by simpa using h.symm) hne
    · rfl
  obtain ⟨x, hx, h⟩ := grouped_profiles_not_identically_zero (ι := Bool)
    (fun b => if b then ρ else ρ') hinj
    (fun b => by cases b <;> simp [hre, hre'])
    (fun b => by cases b <;> simp [him, him'])
    (fun b => if b then -1 / (ρ * (ρ + 1)) else -1 / (ρ' * (ρ' + 1)))
    (fun b => by
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact div_ne_zero (by norm_num) hρ''
      · simp only [↓reduceIte]
        exact div_ne_zero (by norm_num) hρ')
    (fun b => if b then -(m : ℝ) else m) true (by simp; exact_mod_cast hm.ne')
  refine ⟨x, hx, ?_⟩
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  rw [pointSmoothedPairContribution_eq, pointSmoothedPairContribution_eq, ← neg_div, ← add_div,
    div_ne_zero_iff]
  refine ⟨?_, hs.ne'⟩
  rw [Fintype.sum_bool] at h
  simp only [↓reduceIte, Bool.false_eq_true] at h
  intro h0; apply h; linear_combination h0

/-- **Aucun remplacement ne reconstruit** : retirer la contribution d'un point `ρ` et ajouter celle d'un point `ρ' ≠ ρ`
(coefficient recalculé, mêmes multiplicité et canal, toutes les autres contributions conservées) ne reconstruit pas le
reste lissé normalisé en une abscisse `x > 1`. -/
theorem replacement_not_reconstruct {ρ ρ' : ℂ} (hne : ρ' ≠ ρ) (hre : ρ.re ≤ 1) (hre' : ρ'.re ≤ 1)
    (him : 0 < ρ.im) (him' : 0 < ρ'.im) {m : ℕ} (hm : 0 < m) {p : ℕ} (hp : 1 ≤ p) :
    ∃ x : ℝ, 1 < x ∧
      ¬ Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo (smoothedCanonicalAt x) p
        (-pointSmoothedPairContribution m ρ x) (pointSmoothedPairContribution m ρ' x) (j + 1))
        atTop (𝓝 (normalizedSmoothedRemainder x)) :=
  smoothed_insertion_excluded_fun hp _ _ (replacement_defect_not_identically_zero hne hre hre' him him' hm)

/-- **Changement d'amplitude à fréquence fixée** (`ρ' = ρ + δ`, `δ` réel non nul) : ne reconstruit pas. C'est l'énoncé
de l'auteur « impossible à obtenir par des changements d'amplitude », pour un point REMPLACÉ. -/
theorem amplitude_change_not_reconstruct {ρ : ℂ} {δ : ℝ} (hδ : δ ≠ 0) (hre : ρ.re ≤ 1) (hre' : ρ.re + δ ≤ 1)
    (him : 0 < ρ.im) {m : ℕ} (hm : 0 < m) {p : ℕ} (hp : 1 ≤ p) :
    ∃ x : ℝ, 1 < x ∧
      ¬ Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo (smoothedCanonicalAt x) p
        (-pointSmoothedPairContribution m ρ x) (pointSmoothedPairContribution m (ρ + δ) x) (j + 1))
        atTop (𝓝 (normalizedSmoothedRemainder x)) := by
  refine replacement_not_reconstruct ?_ hre (by simpa using hre') him (by simpa using him) hm hp
  intro h
  have := congrArg Complex.re h
  simp at this
  exact hδ this

/-- **Changement de fréquence à amplitude fixée** (`ρ' = ρ + iδ`, `δ` réel non nul, hauteur restant `> 0`) : ne
reconstruit pas non plus. La reconstruction exacte ne distingue pas les deux directions. -/
theorem frequency_change_not_reconstruct {ρ : ℂ} {δ : ℝ} (hδ : δ ≠ 0) (hre : ρ.re ≤ 1)
    (him : 0 < ρ.im) (him' : 0 < ρ.im + δ) {m : ℕ} (hm : 0 < m) {p : ℕ} (hp : 1 ≤ p) :
    ∃ x : ℝ, 1 < x ∧
      ¬ Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo (smoothedCanonicalAt x) p
        (-pointSmoothedPairContribution m ρ x) (pointSmoothedPairContribution m (ρ + δ * I) x) (j + 1))
        atTop (𝓝 (normalizedSmoothedRemainder x)) := by
  refine replacement_not_reconstruct ?_ hre (by simpa using hre) him (by simpa using him') hm hp
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hδ this

/-! ## 4. Portée : le vrai zéro reconstruit, quelle que soit sa partie réelle -/

/-- La représentation exacte du reste lissé ne mentionne aucune position radiale : le vrai membre atteint y figure avec
sa partie réelle, quelle qu'elle soit (réécriture de `smoothedRemainder_eq_tsum_residueTerm`, aucun contenu nouveau,
affichée pour la portée). -/
theorem authentic_family_reconstructs_any_radial (p : TZeroPassage) {x : ℝ} (hx : 1 < x) :
    smoothedRemainder x = ∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm x ρ ∧
      (rZeroRadialPosition p.zLaterMember < 1 / 2 ∨ rZeroRadialPosition p.zLaterMember = 1 / 2 ∨
        1 / 2 < rZeroRadialPosition p.zLaterMember) :=
  ⟨smoothedRemainder_eq_tsum_residueTerm hx, lt_trichotomy _ _⟩

#print axioms amplitudeStableSync_iff
#print axioms amplitudeStableSync_closes
#print axioms amplitudeStable_law_iff_riemannHypothesis
#print axioms replacement_not_reconstruct
#print axioms amplitude_change_not_reconstruct
#print axioms frequency_change_not_reconstruct

end RHV6Fresh
