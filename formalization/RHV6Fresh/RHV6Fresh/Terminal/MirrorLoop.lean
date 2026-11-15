/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TowerFourSectors

/-!
# RHV6Fresh — trajectoire d'une Tour et boucle miroir remise dans l'ordre arithmétique (E162, auteur, 2026-10-03)

Deux vérifications demandées par l'auteur.

* **Une Tour est une trajectoire** (§1). Le long de l'axe arithmétique `u = log x`, le terme ramené à l'échelle
  critique, `Γ_ρ(u) = e^{u(ρ − 1/2)}/ρ` (`pointCurve_eq`), a une phase, un rayon, une vitesse et un sens de rotation :
  `Γ' = (ρ − 1/2)·Γ` (`pointCurve_hasDerivAt`), vitesse angulaire = hauteur, taux radial = profondeur. Le rayon lu
  dans l'ordre des premiers croît ⟺ `β > 1/2`, décroît ⟺ `β < 1/2`, est constant ⟺ `β = 1/2`
  (`pointCurve_norm_lt_iff`, `pointCurve_norm_gt_iff`, `pointCurve_norm_eq_iff`) : une Tour seule lit le signe de la
  profondeur au premier ordre. Ce qui est pair en la profondeur est la somme d'une paire miroir, pas une Tour ; ce
  qui n'est pas une trajectoire est la succession d'un membre au suivant, pas la Tour.
* **La boucle miroir–réorientation** (§2) : réflexion par l'axe arithmétique (conjugaison), puis remise dans le sens
  de rotation d'origine (lecture à rebours). Exactement : `conj Γ_ρ(−u) = g(ρ)·Γ_{ρ*}(u)`, `ρ* = 1 − ρ̄` le membre
  miroir, `g(ρ) = (1 − ρ̄)/ρ̄` l'étalon de boucle (`mirrorLoop_eq`). `‖g‖ = 1 ⟺ β = 1/2`, `> 1 ⟺ β < 1/2`
  (`norm_loopGauge_eq_one_iff`, `one_lt_norm_loopGauge_iff`) ; en ligne `ρ* = ρ` : la boucle rend la même Tour,
  tournée d'un angle constant, sans dilatation (`mirrorLoop_onLine`) ; hors ligne elle rend la Tour d'un autre
  point, de profondeur opposée, dilatée (`mirrorLoop_offLine`), et ce point est un membre véritable
  (`mirrorLoop_target_isZero`).
* **Niveau collectif** (§3) : pour toute famille finie stable par la réflexion, en ligne ou non, l'image de la somme
  par la boucle est la somme sur la **même** famille avec les coefficients `1/(1 − σ)` au lieu de `1/σ`
  (`mirrorLoop_family`). Les exposants sont les mêmes ; la boucle permute les membres dans chaque paire miroir.
  Les deux coefficients diffèrent en tout point de hauteur non nulle, en ligne compris (`loop_coefficient_ne`) ;
  leurs modules sont égaux ⟺ en ligne (`loop_coefficient_norm_eq_iff`).

Borne (verdict sur la « fermeture de jauge par unicité spectrale ») : l'objet collectif après boucle n'est pas le
même objet arithmétique (normalisation miroir des poids, coefficients `1/(1 − σ)`), et ses exposants sont ceux de la
famille de départ : l'unicité spectrale y lit la stabilité de l'ensemble des membres par la réflexion (les quatre
zéros de zeta23), pas l'invariance de chaque membre. Tous les énoncés de ce fichier valent pour tout point et toute
famille stable, donc mot pour mot dans le monde décalé, dont tous les membres sont hors ligne. L'étalon de boucle
est un certificat de la position radiale d'un membre donné. Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Complex RHV3Lean

/-- **Terme d'un point ramené à l'échelle critique**, en coordonnée arithmétique `u = log x`. -/
noncomputable def pointCurve (ρ : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (-(u / 2)) : ℝ) : ℂ) * (Complex.exp (u * ρ) / ρ)

theorem pointCurve_eq (ρ : ℂ) (u : ℝ) : pointCurve ρ u = Complex.exp (u * (ρ - 1 / 2)) / ρ := by
  unfold pointCurve
  rw [Complex.ofReal_exp, ← mul_div_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- La courbe d'un point est la Tour de `TowerFourSectors`. -/
theorem pointCurve_eq_towerCurve (ρ : ℂ) (hρ0 : ρ ≠ 0) (u : ℝ) :
    pointCurve ρ u = towerCurve (ρ.re - 1 / 2) ρ.im (Complex.arg ρ) (1 / ‖ρ‖) u :=
  curve_of_point ρ hρ0 u

/-! ## 1. La Tour est une trajectoire -/

/-- **Vitesse** : `Γ' = (ρ − 1/2)·Γ` ; partie imaginaire du facteur = vitesse angulaire (hauteur), partie réelle =
taux radial (profondeur). -/
theorem pointCurve_hasDerivAt (ρ : ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => pointCurve ρ v) ((ρ - 1 / 2) * pointCurve ρ u) u := by
  have h1 : HasDerivAt (fun v : ℝ => ((v : ℂ)) * (ρ - 1 / 2)) (ρ - 1 / 2) u := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).mul_const (ρ - 1 / 2)
  have h2 := (h1.cexp).div_const ρ
  have hfun : (fun v : ℝ => pointCurve ρ v) = fun v : ℝ => Complex.exp ((v : ℂ) * (ρ - 1 / 2)) / ρ := by
    funext v; exact pointCurve_eq ρ v
  rw [hfun, pointCurve_eq]
  refine h2.congr_deriv ?_
  field_simp

theorem pointCurve_norm (ρ : ℂ) (u : ℝ) : ‖pointCurve ρ u‖ = Real.exp ((ρ.re - 1 / 2) * u) / ‖ρ‖ := by
  rw [pointCurve_eq, norm_div, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]
  ring

/-- Lu dans l'ordre des premiers, le rayon croît ⟺ le point est au-dessus de la ligne. -/
theorem pointCurve_norm_lt_iff (ρ : ℂ) (hρ0 : ρ ≠ 0) {u v : ℝ} (h : u < v) :
    ‖pointCurve ρ u‖ < ‖pointCurve ρ v‖ ↔ 1 / 2 < ρ.re := by
  have hn : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  rw [pointCurve_norm, pointCurve_norm, div_lt_div_iff_of_pos_right hn, Real.exp_lt_exp]
  constructor
  · intro h'
    by_contra hc
    nlinarith [sub_pos.2 h]
  · intro h'
    nlinarith [sub_pos.2 h]

/-- Le rayon décroît ⟺ le point est sous la ligne. -/
theorem pointCurve_norm_gt_iff (ρ : ℂ) (hρ0 : ρ ≠ 0) {u v : ℝ} (h : u < v) :
    ‖pointCurve ρ v‖ < ‖pointCurve ρ u‖ ↔ ρ.re < 1 / 2 := by
  have hn : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  rw [pointCurve_norm, pointCurve_norm, div_lt_div_iff_of_pos_right hn, Real.exp_lt_exp]
  constructor
  · intro h'
    by_contra hc
    nlinarith [sub_pos.2 h]
  · intro h'
    nlinarith [sub_pos.2 h]

/-- Le rayon est conservé ⟺ le point est en ligne : rotation sans dilatation. -/
theorem pointCurve_norm_eq_iff (ρ : ℂ) (hρ0 : ρ ≠ 0) {u v : ℝ} (h : u < v) :
    ‖pointCurve ρ u‖ = ‖pointCurve ρ v‖ ↔ ρ.re = 1 / 2 := by
  have h1 := pointCurve_norm_lt_iff ρ hρ0 h
  have h2 := pointCurve_norm_gt_iff ρ hρ0 h
  constructor
  · intro he
    have a : ¬ (1 / 2 < ρ.re) := fun hc => (ne_of_lt (h1.2 hc)) he
    have b : ¬ (ρ.re < 1 / 2) := fun hc => (ne_of_gt (h2.2 hc)) he
    linarith [not_lt.1 a, not_lt.1 b]
  · intro he
    have a : ¬ (‖pointCurve ρ u‖ < ‖pointCurve ρ v‖) := fun hc => by linarith [h1.1 hc]
    have b : ¬ (‖pointCurve ρ v‖ < ‖pointCurve ρ u‖) := fun hc => by linarith [h2.1 hc]
    linarith [not_lt.1 a, not_lt.1 b]

/-! ## 2. La boucle miroir remise dans l'ordre arithmétique -/

/-- **Étalon de boucle** d'un point. -/
noncomputable def loopGauge (ρ : ℂ) : ℂ := zetaReflect ρ / (starRingEnd ℂ) ρ

theorem zetaReflect_involutive (ρ : ℂ) : zetaReflect (zetaReflect ρ) = ρ := by
  unfold zetaReflect; simp

/-- **La boucle, exactement** : réflexion par l'axe arithmétique puis lecture à rebours = Tour du point miroir,
multipliée par l'étalon de boucle. -/
theorem mirrorLoop_eq (ρ : ℂ) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (u : ℝ) :
    (starRingEnd ℂ) (pointCurve ρ (-u)) = loopGauge ρ * pointCurve (zetaReflect ρ) u := by
  have hc : (starRingEnd ℂ) ρ ≠ 0 := by simpa using hρ0
  have hz : zetaReflect ρ ≠ 0 := by
    unfold zetaReflect
    intro h
    apply hρ1
    have : (starRingEnd ℂ) ρ = 1 := by linear_combination -h
    simpa using congrArg (starRingEnd ℂ) this
  rw [pointCurve_eq, pointCurve_eq, map_div₀, ← Complex.exp_conj]
  unfold loopGauge
  rw [div_mul_div_comm, mul_comm (zetaReflect ρ) _, mul_div_mul_right _ _ hz]
  congr 2
  unfold zetaReflect
  simp only [map_mul, map_sub, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
  push_cast; ring

/-- Le coefficient après boucle : `1/(1 − σ)` sur l'exposant `σ = ρ*`, au lieu de `1/σ`. -/
theorem mirrorLoop_coefficient (ρ : ℂ) (u : ℝ) :
    (starRingEnd ℂ) (pointCurve ρ (-u)) =
      Complex.exp (u * (zetaReflect ρ - 1 / 2)) / (1 - zetaReflect ρ) := by
  rw [pointCurve_eq, map_div₀, ← Complex.exp_conj]
  unfold zetaReflect
  simp only [map_mul, map_sub, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
  congr 2
  · push_cast; ring
  · ring

theorem norm_loopGauge (ρ : ℂ) : ‖loopGauge ρ‖ = ‖zetaReflect ρ‖ / ‖ρ‖ := by
  unfold loopGauge; rw [norm_div, Complex.norm_conj]

private theorem normSq_reflect_sub (ρ : ℂ) :
    ‖zetaReflect ρ‖ ^ 2 - ‖ρ‖ ^ 2 = 1 - 2 * ρ.re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply,
    zetaReflect_re, zetaReflect_im]
  ring

/-- **Étalon conservé ⟺ en ligne** : la boucle est une rotation sans dilatation exactement sur la ligne. -/
theorem norm_loopGauge_eq_one_iff (ρ : ℂ) (hρ0 : ρ ≠ 0) : ‖loopGauge ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  have hn : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  have key := normSq_reflect_sub ρ
  rw [norm_loopGauge, div_eq_one_iff_eq hn.ne']
  constructor
  · intro h; rw [h] at key; linarith
  · intro h
    have h2 : ‖zetaReflect ρ‖ ^ 2 = ‖ρ‖ ^ 2 := by linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- Étalon dilaté ⟺ le point est sous la ligne. -/
theorem one_lt_norm_loopGauge_iff (ρ : ℂ) (hρ0 : ρ ≠ 0) : 1 < ‖loopGauge ρ‖ ↔ ρ.re < 1 / 2 := by
  have hn : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  have key := normSq_reflect_sub ρ
  rw [norm_loopGauge, one_lt_div hn]
  constructor
  · intro h
    have : ‖ρ‖ ^ 2 < ‖zetaReflect ρ‖ ^ 2 := by nlinarith [norm_nonneg ρ]
    linarith
  · intro h
    have h2 : ‖ρ‖ ^ 2 < ‖zetaReflect ρ‖ ^ 2 := by linarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2

theorem zetaReflect_eq_self_iff (ρ : ℂ) : zetaReflect ρ = ρ ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    rw [zetaReflect_re] at this
    linarith
  · intro h
    apply Complex.ext
    · rw [zetaReflect_re]; linarith
    · rw [zetaReflect_im]

/-- **En ligne** : la boucle rend la même Tour, multipliée par un facteur de module un. -/
theorem mirrorLoop_onLine (ρ : ℂ) (hρ0 : ρ ≠ 0) (h : ρ.re = 1 / 2) (u : ℝ) :
    (starRingEnd ℂ) (pointCurve ρ (-u)) = loopGauge ρ * pointCurve ρ u ∧ ‖loopGauge ρ‖ = 1 := by
  have hρ1 : ρ ≠ 1 := by
    intro h1; rw [h1] at h; norm_num at h
  refine ⟨?_, (norm_loopGauge_eq_one_iff ρ hρ0).2 h⟩
  have := mirrorLoop_eq ρ hρ0 hρ1 u
  rwa [(zetaReflect_eq_self_iff ρ).2 h] at this

/-- **Hors ligne** : la boucle rend la Tour d'un autre point, de profondeur opposée, avec un étalon dilaté ou
contracté. -/
theorem mirrorLoop_offLine (ρ : ℂ) (hρ0 : ρ ≠ 0) (h : ρ.re ≠ 1 / 2) :
    zetaReflect ρ ≠ ρ ∧ (zetaReflect ρ).re - 1 / 2 = -(ρ.re - 1 / 2) ∧ ‖loopGauge ρ‖ ≠ 1 := by
  refine ⟨fun hc => h ((zetaReflect_eq_self_iff ρ).1 hc), by rw [zetaReflect_re]; ring,
    fun hc => h ((norm_loopGauge_eq_one_iff ρ hρ0).1 hc)⟩

/-- Le point d'arrivée de la boucle est un membre véritable (zeta23). -/
theorem mirrorLoop_target_isZero (ρ : ℂ) (h : PIsNonTrivialZetaZero ρ) :
    PIsNonTrivialZetaZero (zetaReflect ρ) :=
  zeta_reflect_zero ρ h

/-! ## 3. Niveau collectif -/

/-- **Fermeture collective, en ligne ou non** : sur toute famille finie stable par la réflexion, la somme après
boucle est la somme sur la même famille, coefficients `1/(1 − σ)`. -/
theorem mirrorLoop_family (S : Finset ℂ) (hS : ∀ ρ ∈ S, zetaReflect ρ ∈ S) (u : ℝ) :
    (starRingEnd ℂ) (∑ ρ ∈ S, pointCurve ρ (-u)) =
      ∑ σ ∈ S, Complex.exp (u * (σ - 1 / 2)) / (1 - σ) := by
  rw [map_sum]
  refine Finset.sum_nbij' zetaReflect zetaReflect hS hS
    (fun ρ _ => zetaReflect_involutive ρ) (fun ρ _ => zetaReflect_involutive ρ) ?_
  intro ρ _
  exact mirrorLoop_coefficient ρ u

/-- Les deux coefficients d'un même exposant diffèrent à toute hauteur non nulle, en ligne compris. -/
theorem loop_coefficient_ne (σ : ℂ) (hT : σ.im ≠ 0) : (1 : ℂ) / (1 - σ) ≠ 1 / σ := by
  intro h
  have h0 : σ ≠ 0 := fun hc => hT (by rw [hc]; simp)
  have h1 : (1 : ℂ) - σ ≠ 0 := fun hc => hT (by
    have : σ = 1 := by linear_combination -hc
    rw [this]; simp)
  rw [div_eq_div_iff h1 h0] at h
  have := congrArg Complex.im h
  simp at this
  exact hT (by linarith)

/-- Modules des deux coefficients égaux ⟺ en ligne. -/
theorem loop_coefficient_norm_eq_iff (σ : ℂ) (h0 : σ ≠ 0) (h1 : σ ≠ 1) :
    ‖(1 : ℂ) / (1 - σ)‖ = ‖1 / σ‖ ↔ σ.re = 1 / 2 := by
  have hn : 0 < ‖σ‖ := norm_pos_iff.2 h0
  have hm : 0 < ‖(1 : ℂ) - σ‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h1))
  have key : ‖(1 : ℂ) - σ‖ ^ 2 - ‖σ‖ ^ 2 = 1 - 2 * σ.re := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp; ring
  rw [norm_div, norm_div, norm_one, div_eq_div_iff hm.ne' hn.ne', one_mul, one_mul]
  constructor
  · intro h; rw [h] at key; linarith
  · intro h
    have h2 : ‖σ‖ ^ 2 = ‖(1 : ℂ) - σ‖ ^ 2 := by linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

#print axioms pointCurve_eq
#print axioms pointCurve_eq_towerCurve
#print axioms pointCurve_hasDerivAt
#print axioms pointCurve_norm
#print axioms pointCurve_norm_lt_iff
#print axioms pointCurve_norm_gt_iff
#print axioms pointCurve_norm_eq_iff
#print axioms zetaReflect_involutive
#print axioms mirrorLoop_eq
#print axioms mirrorLoop_coefficient
#print axioms norm_loopGauge
#print axioms norm_loopGauge_eq_one_iff
#print axioms one_lt_norm_loopGauge_iff
#print axioms zetaReflect_eq_self_iff
#print axioms mirrorLoop_onLine
#print axioms mirrorLoop_offLine
#print axioms mirrorLoop_target_isZero
#print axioms mirrorLoop_family
#print axioms loop_coefficient_ne
#print axioms loop_coefficient_norm_eq_iff

end RHV6Fresh
