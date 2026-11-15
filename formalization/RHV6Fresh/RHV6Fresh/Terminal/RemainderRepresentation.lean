/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.WholeWindingObligation
import RHV6Fresh.Terminal.ArithmeticReading
import RHV6Fresh.Terminal.InverseReading
import RHV6Fresh.Terminal.OnCrossReadings
import RHV6Fresh.Terminal.RegimeTrigger

/-!
# RHV6Fresh — représentation exacte du reste par les vrais zéros, et somme des suivants

Module INDÉPENDANT du fichier `Terminal/OnLineBetaEqPrevious.lean` (qui n'a pas de `.olean` tant
que son but est ouvert) : tout ce qui concerne le reste, la somme des suivants et le budget
collectif est ici, avec ses dépendances, dans des modules dont toutes les preuves sont fermées.

## Les deux obligations et leur statut (auteur, 2026-10-06)

* **Obligation géométrique, ancienne prémisse du TDD, désormais hypothèse ⟺ RH**
  (`Terminal/WholeWindingObligation.lean`,
  `riemannHypothesis_of_whole_winding_all_passages`) : pour chaque passage canonique consécutif,
  la norme de la contribution brute `zeroTerm` de la Tour atteinte reste inférieure ou égale à celle
  de la Tour précédente, au même réel `x > 0`. Rien d'autre.
* **Obligation arithmétique, RÉSULTAT DÉMONTRÉ, jamais seconde prémisse** : les contributions des
  vrais zéros représentent exactement le reste arithmétique considéré. Elle est COMPILÉE ici sous ses
  formes exactes (`smoothedRemainder_eq_tsum_residueTerm`, `remainder_eq_preceding_add_following`,
  et dans les bases `arithmetic_eq_spectral`, `liaison_analytic`).

## Identification exacte des objets (aucun n'est `li(x) − π(x)`)

* `zeroTerm z x` : `x^ρ / ρ`, terme BRUT de la Tour d'un membre `z` ; domaine `x > 0`.
* `nontrivialZeroResidueTerm x ρ` : `−m_ρ · x^ρ / (ρ(ρ+1))`, terme LISSÉ d'un indice, avec sa
  multiplicité `m_ρ`, son signe et le facteur supplémentaire `ρ + 1` ; défini pour tout `x`.
* `smoothedVonMangoldtSum x` : `Σ_{n<x} Λ(n)(1 − n/x)`, côté premiers ; tout `x`.
* `smoothedZeroBackground x` : `x/2 − ζ'/ζ(0) + ζ'/ζ(−1)/x +` somme des termes des zéros
  triviaux ; `x ≠ 0`.
* `smoothedRemainder x` : `smoothedVonMangoldtSum x − smoothedZeroBackground x`, premiers seuls ;
  l'identité de représentation vaut pour `x > 1`.
* `exactRemainder N` : `ψ(N) −` pas du fond, escalier NON lissé à l'entier `N` ; `N ≥ 2`.
* `precedingSum H x` : somme FINIE des termes lissés des indices de hauteur absolue `≤ H`.
* `followingSum H x` : somme à l'infini des termes lissés des indices de hauteur absolue `> H` ;
  sommable pour `x > 1`.

Transports compilés : `residueTerm_eq_zeroTerm` (lissé `= −m ·` brut `/(ρ + 1)`, membre par
membre) ; `smoothedRemainder_eq_tsum_residueTerm` (reste lissé `=` somme de TOUS les termes lissés,
`x > 1`, convergence : `tsum`, absolument sommable par `nontrivial_zero_residue_series_summable`) ;
`remainder_eq_preceding_add_following` (découpage à une hauteur) ; `arithmetic_eq_spectral`
(escalier `ψ` : reste exact `=` pas du canal des zéros, `N ≥ 2`) ; `liaison_analytic` (`ψ`
reconstruite depuis les zéros, `x ≥ 2`). Aucun objet du dépôt ne représente `li(x) − π(x)` ; aucun
théorème ne lie `smoothedRemainder` à `li − π` ; il est interdit de les identifier.

## Ce qui passe et ce qui ne passe pas

* Une BORNE DE CROISSANCE de la somme (en `C·x^θ`, `x > 1`) borne la partie réelle de chaque indice
  (`followingSum_growth_bounds_each`, `radial_le_of_remainder_growth`) : c'est la lecture du pôle.
* L'IDENTITÉ de représentation seule ne borne rien : elle est vraie quelle que soit la position
  radiale des zéros (`remainder_eq_preceding_add_following` ne suppose rien sur eux).
* Portées : tout ce qui est lu sur le reste est formulé pour `x > 1` ; la domination entière de la
  prémisse porte aussi sur `0 < x < 1` ; elle est obtenue ici par `β = 1/2` des deux membres
  (`whole_winding_iff_onLine`), jamais par transfert d'une inégalité formulée pour `x > 1`.

## Raccord analytique résiduel (OUVERT, énoncé exact)

Antécédent ACQUIS (théorème) : `∀ x > 1, smoothedRemainder x = ∑' ρ, nontrivialZeroResidueTerm x ρ`.
Conclusion NON DÉRIVÉE : `∃ C, ∀ x > 1, ‖smoothedRemainder x‖ ≤ C · x^(1/2)`.
L'antécédent étant un théorème, l'implication équivaut à sa conclusion, elle-même équivalente à la
prémisse d'enroulement et à RH (`whole_winding_all_passages_iff_remainder_sqrt_growth`). Aucun
théorème du dépôt ne la fournit ; elle n'est posée nulle part en hypothèse d'un théorème de
fermeture.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. L'identité de représentation, compilée -/

/-- **Obligation arithmétique, démontrée** : le reste lissé des premiers est la somme de tous les
termes lissés des vrais zéros (`x > 1`, somme absolument convergente). -/
theorem smoothedRemainder_eq_tsum_residueTerm {x : ℝ} (hx : 1 < x) :
    smoothedRemainder x = ∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm x ρ := by
  unfold smoothedRemainder
  exact (channel_eq_arithmetic hx).symm

/-! ## Tous les zéros suivants, ensemble : la somme à l'infini au-dessus d'une hauteur -/

/-- Coefficient d'un zéro dans la somme des contributions situées strictement au-dessus de la
hauteur `H` (en valeur absolue) : son coefficient dans le reste, ou zéro s'il n'est pas
au-dessus. -/
noncomputable def followingWeight (H : ℝ) (σ : ExplicitIndex) : ℂ :=
  if H < |(σ : ℂ).im| then -(zetaZeroMultiplicity (σ : ℂ) : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1)) else 0

/-- **La somme à l'infini de toutes les contributions au-dessus de la hauteur `H`.** -/
noncomputable def followingSum (H x : ℝ) : ℂ :=
  ∑' σ : ExplicitIndex, followingWeight H σ * (x : ℂ) ^ (σ : ℂ)

/-- **La somme de tous les suivants lit chacun d'eux.** Si la somme à l'infini des contributions
au-dessus de `H` est bornée par `C · x^θ`, aucun zéro au-dessus de `H` n'a de partie réelle
`> θ`. -/
theorem followingSum_growth_bounds_each {H θ C : ℝ}
    (h : ∀ x : ℝ, 1 < x → ‖followingSum H x‖ ≤ C * x ^ θ) (ρ : ExplicitIndex)
    (hρ : H < |(ρ : ℂ).im|) : (ρ : ℂ).re ≤ θ := by
  classical
  by_contra hlt
  push Not at hlt
  have hsum0 : Summable fun σ : ExplicitIndex =>
      ‖-(zetaZeroMultiplicity (σ : ℂ) : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1))‖ :=
    multiplicity_weight_summable.congr fun σ => by rw [neg_div, norm_neg]
  have hsum : Summable fun σ : ExplicitIndex => ‖followingWeight H σ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun σ => by
      unfold followingWeight
      split_ifs
      · exact le_rfl
      · rw [norm_zero]; exact norm_nonneg _) hsum0
  have key := cpow_series_growth_fibre_zero (fun σ : ExplicitIndex => (σ : ℂ))
    (followingWeight H) explicitIndex_re_le_one explicitIndex_locallyFinite hsum (θ := θ) (C := C)
    (fun x hx => h x hx) (ρ : ℂ) hlt
  rw [tsum_eq_single ρ (fun σ hσ => if_neg (fun h => hσ (Subtype.ext h))), if_pos rfl] at key
  unfold followingWeight at key
  rw [if_pos hρ] at key
  obtain ⟨h0, h1⟩ := explicitIndex_ne_zero ρ
  have hm : (zetaZeroMultiplicity (ρ : ℂ) : ℂ) = 0 := by
    have := (div_eq_zero_iff.mp key).resolve_right (mul_ne_zero h0 h1)
    exact neg_eq_zero.mp this
  exact (zetaZeroMultiplicity_pos ρ.property.1).ne' (by exact_mod_cast hm)

/-- **Si la somme de tous les suivants reste sous l'échelle de la ligne, chaque suivant est en
ligne.** Hypothèse : la somme à l'infini des contributions au-dessus de la hauteur du zéro `e` est
bornée par un multiple de `√x`. Conclusion : tout zéro plus haut que `e` a la partie réelle un demi
(le zéro et son miroir, de même hauteur, sont tous deux lus par la somme). -/
theorem following_onLine_of_followingSum_sqrt (e : TrueZero)
    (h : ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖followingSum (rZeroHeight e.1) x‖ ≤ C * x ^ (1 / 2 : ℝ))
    (w : TrueZero) (hw : rZeroHeight e.1 < rZeroHeight w.1) :
    rZeroRadialPosition w.1 = 1 / 2 := by
  obtain ⟨C, hC⟩ := h
  have h1 := followingSum_growth_bounds_each hC (memberIndex w) (by
    change rZeroHeight e.1 < |rZeroHeight w.1|
    exact lt_of_lt_of_le hw (le_abs_self _))
  have h2 := followingSum_growth_bounds_each hC (memberIndex (mirrorMember w)) (by
    change rZeroHeight e.1 < |rZeroHeight (mirrorMember w).1|
    exact lt_of_lt_of_le (by rw [mirrorMember_ordinate]; exact hw) (le_abs_self _))
  rw [show ((memberIndex w : ExplicitIndex) : ℂ) = zeroPoint w from rfl, zeroPoint_re] at h1
  rw [show ((memberIndex (mirrorMember w) : ExplicitIndex) : ℂ) = zeroPoint (mirrorMember w) from rfl,
    zeroPoint_re, mirrorMember_radial] at h2
  linarith

/-- Les coefficients de la somme des suivants sont sommables en norme. -/
theorem followingWeight_norm_summable (H : ℝ) :
    Summable fun σ : ExplicitIndex => ‖followingWeight H σ‖ := by
  have hsum0 : Summable fun σ : ExplicitIndex =>
      ‖-(zetaZeroMultiplicity (σ : ℂ) : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1))‖ :=
    multiplicity_weight_summable.congr fun σ => by rw [neg_div, norm_neg]
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun σ => by
    unfold followingWeight
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _) hsum0

/-- **Budget d'amplitude de tous les suivants** : la somme des modules des coefficients des zéros
au-dessus de la hauteur `H`. -/
noncomputable def followingBudget (H : ℝ) : ℝ := ∑' σ : ExplicitIndex, ‖followingWeight H σ‖

/-- **Le budget des suivants s'affaiblit quand la hauteur monte** : plus le zéro engagé est haut,
plus le budget de tous ceux qui le suivent est petit (au sens large). -/
theorem followingBudget_antitone : Antitone followingBudget := by
  intro H H' h
  unfold followingBudget
  refine Summable.tsum_le_tsum (fun σ => ?_) (followingWeight_norm_summable H')
    (followingWeight_norm_summable H)
  unfold followingWeight
  by_cases h' : H' < |(σ : ℂ).im|
  · rw [if_pos h', if_pos (lt_of_le_of_lt h h')]
  · rw [if_neg h', norm_zero]; exact norm_nonneg _

/-- **Réciproque : si aucun suivant ne dépasse la ligne, la somme de tous les suivants reste sous
leur budget fois `√x`.** Hypothèse : tout zéro au-dessus de `H` a une partie réelle `≤ 1/2`. -/
theorem followingSum_le_budget_of_le_half {H : ℝ}
    (hOn : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → (σ : ℂ).re ≤ 1 / 2) {x : ℝ} (hx : 1 < x) :
    ‖followingSum H x‖ ≤ followingBudget H * x ^ (1 / 2 : ℝ) := by
  have hx0 : 0 < x := lt_trans one_pos hx
  have hterm : ∀ σ : ExplicitIndex, ‖followingWeight H σ * (x : ℂ) ^ (σ : ℂ)‖ ≤
      ‖followingWeight H σ‖ * x ^ (1 / 2 : ℝ) := by
    intro σ
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    by_cases h : H < |(σ : ℂ).im|
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx.le (hOn σ h)) (norm_nonneg _)
    · have h0 : followingWeight H σ = 0 := by unfold followingWeight; rw [if_neg h]
      rw [h0, norm_zero, zero_mul, zero_mul]
  have hdom : Summable fun σ : ExplicitIndex => ‖followingWeight H σ‖ * x ^ (1 / 2 : ℝ) :=
    (followingWeight_norm_summable H).mul_right _
  have hs : Summable fun σ : ExplicitIndex => ‖followingWeight H σ * (x : ℂ) ^ (σ : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hdom
  unfold followingSum followingBudget
  calc ‖∑' σ : ExplicitIndex, followingWeight H σ * (x : ℂ) ^ (σ : ℂ)‖
      ≤ ∑' σ : ExplicitIndex, ‖followingWeight H σ * (x : ℂ) ^ (σ : ℂ)‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' σ : ExplicitIndex, ‖followingWeight H σ‖ * x ^ (1 / 2 : ℝ) :=
        Summable.tsum_le_tsum hterm hs hdom
    _ = (∑' σ : ExplicitIndex, ‖followingWeight H σ‖) * x ^ (1 / 2 : ℝ) := tsum_mul_right

/-- **Caractérisation : la somme de tous les suivants reste sous l'échelle de la ligne ⟺ aucun zéro
au-dessus de `H` ne dépasse la ligne.** C'est une équivalence : aucun de ses deux côtés n'est
dérivé ici. -/
theorem followingSum_sqrt_iff_following_le_half (H : ℝ) :
    (∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖followingSum H x‖ ≤ C * x ^ (1 / 2 : ℝ)) ↔
      ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → (σ : ℂ).re ≤ 1 / 2 :=
  ⟨fun ⟨_, hC⟩ σ hσ => followingSum_growth_bounds_each hC σ hσ,
    fun h => ⟨followingBudget H, fun _ hx => followingSum_le_budget_of_le_half h hx⟩⟩

/-- La somme, en nombre fini de hauteurs, des contributions des zéros qui ne sont pas au-dessus de
la hauteur `H`. -/
noncomputable def precedingSum (H x : ℝ) : ℂ :=
  ∑' σ : ExplicitIndex, (if H < |(σ : ℂ).im| then 0 else nontrivialZeroResidueTerm x σ)

/-- **Identité : le reste exact des premiers = contributions jusqu'à la hauteur `H` + somme de tous
les suivants.** Identité entre objets, vraie quelle que soit la position radiale des zéros ; elle ne
donne aucune borne. -/
theorem remainder_eq_preceding_add_following (H : ℝ) {x : ℝ} (hx : 1 < x) :
    smoothedRemainder x = precedingSum H x + followingSum H x := by
  have hsn := (nontrivial_zero_residue_series_summable hx).norm
  have h1 : Summable fun σ : ExplicitIndex =>
      (if H < |(σ : ℂ).im| then (0 : ℂ) else nontrivialZeroResidueTerm x σ) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun σ => by split_ifs <;> simp) hsn)
  have h2 : Summable fun σ : ExplicitIndex =>
      (if H < |(σ : ℂ).im| then nontrivialZeroResidueTerm x σ else (0 : ℂ)) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun σ => by split_ifs <;> simp) hsn)
  have hF : followingSum H x = ∑' σ : ExplicitIndex,
      (if H < |(σ : ℂ).im| then nontrivialZeroResidueTerm x σ else (0 : ℂ)) := by
    unfold followingSum
    refine tsum_congr fun σ => ?_
    unfold followingWeight
    split_ifs
    · change _ = -(zetaZeroMultiplicity (σ : ℂ) : ℂ) *
        ((x : ℂ) ^ (σ : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1)))
      ring
    · rw [zero_mul]
  rw [hF]
  unfold precedingSum
  rw [← h1.tsum_add h2]
  unfold smoothedRemainder
  rw [← channel_eq_arithmetic hx]
  refine tsum_congr fun σ => ?_
  split_ifs <;> simp

/-! ## Budget collectif de la somme des suivants : propriété à démontrer, jamais un fait acquis -/

/-- **Budget collectif `B_H`** : la somme à l'infini de toutes les contributions au-dessus de la
hauteur `H` reste sous un multiple strictement positif de `√x`. C'est une PROPRIÉTÉ À DÉMONTRER :
aucun théorème de ce fichier ne l'établit ; elle n'apparaît que comme hypothèse ou comme membre
d'une équivalence. -/
def CollectiveBudget (H : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ‖followingSum H x‖ ≤ C * x ^ (1 / 2 : ℝ)

/-- La constante du budget collectif peut toujours être prise strictement positive. -/
theorem collectiveBudget_iff_exists_bound (H : ℝ) :
    CollectiveBudget H ↔
      ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖followingSum H x‖ ≤ C * x ^ (1 / 2 : ℝ) := by
  constructor
  · rintro ⟨C, _, h⟩
    exact ⟨C, h⟩
  · rintro ⟨C, h⟩
    refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => (h x hx).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)

/-- **Un suivant hors ligne réfute le budget collectif.** Pour tout zéro `w` strictement au-dessus
de `H` : `β_w ≠ 1/2 ⟹ ¬ B_H`. La somme reste SIGNÉE (aucune somme de modules) : le zéro et son
miroir, de même hauteur, sont lus chacun par la lecture du pôle
(`followingSum_growth_bounds_each`), ce qui interdit toute compensation durable par les autres. -/
theorem offLine_following_refutes_collectiveBudget {H : ℝ} (w : TrueZero)
    (hw : H < rZeroHeight w.1) (hOff : rZeroRadialPosition w.1 ≠ 1 / 2) :
    ¬ CollectiveBudget H := by
  rintro ⟨C, _, hC⟩
  have h1 := followingSum_growth_bounds_each hC (memberIndex w) (by
    change H < |rZeroHeight w.1|
    exact lt_of_lt_of_le hw (le_abs_self _))
  have h2 := followingSum_growth_bounds_each hC (memberIndex (mirrorMember w)) (by
    change H < |rZeroHeight (mirrorMember w).1|
    exact lt_of_lt_of_le (by rw [mirrorMember_ordinate]; exact hw) (le_abs_self _))
  rw [show ((memberIndex w : ExplicitIndex) : ℂ) = zeroPoint w from rfl, zeroPoint_re] at h1
  rw [show ((memberIndex (mirrorMember w) : ExplicitIndex) : ℂ) = zeroPoint (mirrorMember w) from rfl,
    zeroPoint_re, mirrorMember_radial] at h2
  exact hOff (by linarith)

/-- **Conjugués et multiplicités, explicitement.** Le coefficient du conjugué d'un zéro dans la
somme des suivants est le conjugué du coefficient : même hauteur absolue, même multiplicité. -/
theorem followingWeight_conj (H : ℝ) (σ : ExplicitIndex) :
    followingWeight H ⟨starRingEnd ℂ (σ : ℂ), (isNontrivialZetaZero_conj_iff _).mpr σ.property⟩ =
      starRingEnd ℂ (followingWeight H σ) := by
  unfold followingWeight
  simp only [Complex.conj_im, abs_neg]
  split_ifs
  · rw [zetaZeroMultiplicity_conj σ.property.1]
    simp [map_div₀]
  · simp

/-- **Tout indice au-dessus de `H` est en ligne dès que tous les membres supérieurs à `H` le
sont** (`H ≥ 0`) : un indice de hauteur positive est un membre ; un indice de hauteur négative est
le conjugué d'un membre, de même partie réelle. -/
theorem index_re_eq_half_of_upper_onLine {H : ℝ} (hH : 0 ≤ H)
    (hOn : ∀ w : TrueZero, H < rZeroHeight w.1 → rZeroRadialPosition w.1 = 1 / 2)
    (σ : ExplicitIndex) (hσ : H < |(σ : ℂ).im|) : (σ : ℂ).re = 1 / 2 := by
  have hstrip := isNontrivialZetaZero_re_mem_Ioo σ.property
  rcases le_or_gt 0 (σ : ℂ).im with hpos | hneg
  · rw [abs_of_nonneg hpos] at hσ
    have him : 0 < (σ : ℂ).im := lt_of_le_of_lt hH hσ
    exact hOn ⟨⟨(σ : ℂ), σ.property.1, hstrip.1, hstrip.2⟩, him⟩ hσ
  · rw [abs_of_neg hneg] at hσ
    have hc := (isNontrivialZetaZero_conj_iff (σ : ℂ)).mpr σ.property
    have hstripc := isNontrivialZetaZero_re_mem_Ioo hc
    have him : 0 < (starRingEnd ℂ (σ : ℂ)).im := by rw [Complex.conj_im]; linarith
    have h := hOn ⟨⟨starRingEnd ℂ (σ : ℂ), hc.1, hstripc.1, hstripc.2⟩, him⟩ (by
      change H < (starRingEnd ℂ (σ : ℂ)).im
      rw [Complex.conj_im]; exact hσ)
    change (starRingEnd ℂ (σ : ℂ)).re = 1 / 2 at h
    rwa [Complex.conj_re] at h

/-- **La constante du budget** : `C_H = Σ_{|Im ρ| > H} m_ρ / |ρ(ρ+1)|`, multiplicités comprises,
les deux signes de hauteur comptés. -/
theorem followingBudget_eq (H : ℝ) :
    followingBudget H = ∑' σ : ExplicitIndex,
      (if H < |(σ : ℂ).im| then
        (zetaZeroMultiplicity (σ : ℂ) : ℝ) / ‖(σ : ℂ) * ((σ : ℂ) + 1)‖ else 0) := by
  unfold followingBudget
  refine tsum_congr fun σ => ?_
  unfold followingWeight
  split_ifs
  · rw [norm_div, norm_neg, Complex.norm_natCast]
  · rw [norm_zero]

/-- **Réciproque : si tous les membres supérieurs à `H` sont en ligne, le budget collectif tient**,
avec la constante `C_H` (sommabilité des coefficients). -/
theorem collectiveBudget_of_following_onLine {H : ℝ} (hH : 0 ≤ H)
    (hOn : ∀ w : TrueZero, H < rZeroHeight w.1 → rZeroRadialPosition w.1 = 1 / 2) :
    CollectiveBudget H :=
  (collectiveBudget_iff_exists_bound H).mpr ⟨followingBudget H, fun _ hx =>
    followingSum_le_budget_of_le_half
      (fun σ hσ => (index_re_eq_half_of_upper_onLine hH hOn σ hσ).le) hx⟩

/-- **Caractérisation : budget collectif `B_H` ⟺ tous les membres supérieurs à `H` sont en
ligne** (`H ≥ 0`). Équivalence : aucun de ses deux côtés n'est dérivé ici. -/
theorem collectiveBudget_iff_following_onLine {H : ℝ} (hH : 0 ≤ H) :
    CollectiveBudget H ↔
      ∀ w : TrueZero, H < rZeroHeight w.1 → rZeroRadialPosition w.1 = 1 / 2 :=
  ⟨fun hB w hw => by
      by_contra hOff
      exact offLine_following_refutes_collectiveBudget w hw hOff hB,
    collectiveBudget_of_following_onLine hH⟩

/-- Les indices qui ne sont pas au-dessus de la hauteur `H` sont en nombre fini. -/
theorem precedingIndices_finite (H : ℝ) : {σ : ExplicitIndex | ¬ H < |(σ : ℂ).im|}.Finite := by
  have hfin := nontrivialZetaZerosByHeight_finite (H + 1)
  refine Set.Finite.of_finite_image (hfin.subset ?_)
    (Set.injOn_of_injective Subtype.coe_injective)
  rintro _ ⟨ρ, hρ, rfl⟩
  have hle : |(ρ : ℂ).im| ≤ H := not_lt.mp hρ
  exact ⟨ρ.property, by linarith⟩

/-- **La part basse du reste est une somme FINIE** : les contributions des zéros de hauteur
absolue `≤ H`, avec le signe et la multiplicité de chaque terme du reste. Aucun de ces zéros n'est
supposé en ligne. -/
theorem precedingSum_eq_finite_sum (H x : ℝ) :
    precedingSum H x =
      ∑ σ ∈ (precedingIndices_finite H).toFinset, nontrivialZeroResidueTerm x σ := by
  unfold precedingSum
  rw [tsum_eq_sum (s := (precedingIndices_finite H).toFinset) (fun σ hσ => by
    rw [Set.Finite.mem_toFinset] at hσ
    by_contra h
    exact hσ (fun hlt => h (if_pos hlt)))]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [Set.Finite.mem_toFinset] at hσ
  exact if_neg hσ

/-- **Le terme lissé d'un membre est isolé dans la part basse du reste** : pour un membre de
hauteur `≤ H`, part basse = son terme + la somme finie des autres. Identité, aucune borne. -/
theorem precedingSum_split_member (H x : ℝ) (z : TrueZero) (hz : rZeroHeight z.1 ≤ H) :
    precedingSum H x = nontrivialZeroResidueTerm x (memberIndex z) +
      ∑ σ ∈ (precedingIndices_finite H).toFinset.erase (memberIndex z),
        nontrivialZeroResidueTerm x σ := by
  rw [precedingSum_eq_finite_sum]
  refine (Finset.add_sum_erase _ _ ?_).symm
  rw [Set.Finite.mem_toFinset]
  change ¬ H < |rZeroHeight z.1|
  exact not_lt.mpr ((abs_of_pos z.2).le.trans hz)

/-- **Fermeture conditionnelle.** Sous les hypothèses de l'énoncé de l'auteur ET sous le budget
collectif à la hauteur du zéro engagé (hypothèse `hB`, non dérivée), la partie réelle du zéro
suivant est celle du zéro qui a engagé le régime. -/
theorem onLine_beta_eq_previous_of_collectiveBudget {o p : TZeroPassage}
    (hJ : o.zLaterMember = p.zEarlierMember)
    (hE : 0 < rZeroHeight o.zLaterMember) (ho : VerticalPassage o)
    (hOn : rZeroRadialPosition o.zLaterMember = 1 / 2)
    (hB : CollectiveBudget (rZeroHeight p.zEarlierMember)) :
    rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember := by
  have hHeightAdvances : rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember :=
    (engaged_regime_kept hJ ho hOn).1
  have hOnE : rZeroRadialPosition p.zEarlierMember = 1 / 2 := by rw [← hJ]; exact hOn
  have hPE : 0 < rZeroHeight p.zEarlierMember := by rw [← hJ]; exact hE
  have hPL : 0 < rZeroHeight p.zLaterMember := lt_of_lt_of_le hPE (passage_height_le p)
  rw [hOnE]
  exact following_onLine_of_followingSum_sqrt ⟨p.zEarlierMember, hPE⟩
    ((collectiveBudget_iff_exists_bound _).mp hB) ⟨p.zLaterMember, hPL⟩ hHeightAdvances

/-! ## Borne collective ⟹ enroulement entier sur tout passage au-dessus (TDD d'enroulement, 2026-10-06)

La seule implication du dépôt qui aille du reste collectif à une domination TERME PAR TERME passe par
une BORNE sur la somme des suivants, jamais par l'identité `remainder_eq_preceding_add_following`
seule. -/

/-- **Si la somme de tous les suivants d'un zéro `e` reste sous un multiple de `√x`, tout passage dont
le départ est strictement plus haut que `e` est à enroulement entier** : ses deux membres sont en
ligne (`following_onLine_of_followingSum_sqrt`), et deux membres en ligne consécutifs s'enroulent
entièrement (`whole_winding_iff_onLine`). L'hypothèse est la borne collective, non dérivée ;
l'identité de décomposition ne la fournit pas. -/
theorem whole_winding_above_of_followingSum_sqrt (e : TrueZero)
    (h : ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖followingSum (rZeroHeight e.1) x‖ ≤ C * x ^ (1 / 2 : ℝ))
    (p : TZeroPassage) (hAbove : rZeroHeight e.1 < rZeroHeight p.zEarlierMember)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    ∀ x : ℝ, 0 < x →
      ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖ := by
  have hOnE : rZeroRadialPosition p.zEarlierMember = 1 / 2 :=
    following_onLine_of_followingSum_sqrt e h ⟨p.zEarlierMember, hE⟩ hAbove
  have hOnL : rZeroRadialPosition p.zLaterMember = 1 / 2 :=
    following_onLine_of_followingSum_sqrt e h ⟨p.zLaterMember, hL⟩
      (lt_of_lt_of_le hAbove (passage_height_le p))
  exact (whole_winding_iff_onLine p hE hL hOnE).mpr hOnL

#print axioms whole_winding_above_of_followingSum_sqrt

/-! ## 4. Du reste exactement représenté à l'enroulement entier : les routes compilées -/

/-- **Borne en `√x` du reste lissé ⟹ enroulement entier sur tout passage**, route directe membre par
membre : la lecture du pôle donne `β ≤ 1/2` pour chaque membre et pour son miroir, donc `β = 1/2`
partout, donc deux membres consécutifs s'enroulent entièrement (`whole_winding_iff_onLine`). La borne
est l'HYPOTHÈSE, non dérivée ; l'identité de représentation ne la donne pas. -/
theorem whole_winding_all_passages_of_remainder_sqrt_growth
    (h : ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 : ℝ)) :
    ∀ p : TZeroPassage, ∀ (hE : 0 < rZeroHeight p.zEarlierMember)
      (hL : 0 < rZeroHeight p.zLaterMember), ∀ x : ℝ, 0 < x →
      ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖ := by
  obtain ⟨C, hC⟩ := h
  have hOn : ∀ z : TrueZero, rZeroRadialPosition z.1 = 1 / 2 := fun z => by
    have h1 := radial_le_of_remainder_growth hC z
    have h2 := radial_le_of_remainder_growth hC (mirrorMember z)
    rw [mirrorMember_radial] at h2
    linarith
  intro p hE hL
  exact (whole_winding_iff_onLine p hE hL (hOn ⟨p.zEarlierMember, hE⟩)).mpr
    (hOn ⟨p.zLaterMember, hL⟩)

/-- **La prémisse d'enroulement équivaut à la borne en `√x` du reste lissé exactement représenté.**
Les deux côtés sont chacun équivalents à RH ; aucun n'est dérivé. -/
theorem whole_winding_all_passages_iff_remainder_sqrt_growth :
    (∀ p : TZeroPassage, ∀ (hE : 0 < rZeroHeight p.zEarlierMember)
        (hL : 0 < rZeroHeight p.zLaterMember), ∀ x : ℝ, 0 < x →
        ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖) ↔
      ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 : ℝ) :=
  whole_winding_all_passages_iff_riemannHypothesis.trans riemannHypothesis_iff_remainder_sqrt_growth

/-! ## 5. Bloquée par le haut par le zéro précédent, par le bas par le zéro suivant -/

/-- **Le blocage des deux côtés est une CONSÉQUENCE de l'obligation d'enroulement entier (ancienne
prémisse)**, instanciée sur le passage
qui atteint un membre et sur celui qui le quitte : la Tour du membre est sous celle du précédent et
au-dessus de celle du suivant, en tout `x > 0`. Aucune condition supplémentaire. -/
theorem two_sided_blocking_of_whole_winding
    (hWind : ∀ p : TZeroPassage, ∀ (hE : 0 < rZeroHeight p.zEarlierMember)
        (hL : 0 < rZeroHeight p.zLaterMember), ∀ x : ℝ, 0 < x →
        ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖)
    {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hS : 0 < rZeroHeight q.zLaterMember) :
    ∀ x : ℝ, 0 < x →
      ‖zeroTerm ⟨q.zLaterMember, hS⟩ x‖ ≤ ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ∧
        ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖ := by
  intro x hx
  refine ⟨?_, hWind p hE hL x hx⟩
  have hQ : 0 < rZeroHeight q.zEarlierMember := by rw [← hJ]; exact hL
  have h := hWind q hQ hS x hx
  have e : (⟨q.zEarlierMember, hQ⟩ : TrueZero) = ⟨p.zLaterMember, hL⟩ := Subtype.ext hJ.symm
  rwa [e] at h

#print axioms smoothedRemainder_eq_tsum_residueTerm
#print axioms remainder_eq_preceding_add_following
#print axioms following_onLine_of_followingSum_sqrt
#print axioms collectiveBudget_iff_following_onLine
#print axioms onLine_beta_eq_previous_of_collectiveBudget
#print axioms whole_winding_all_passages_of_remainder_sqrt_growth
#print axioms whole_winding_all_passages_iff_remainder_sqrt_growth
#print axioms two_sided_blocking_of_whole_winding

end RHV6Fresh
