/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TowerWinding

/-!
# RHV6Fresh — géométrie des contacts et accumulation des VALEURS d'une Tour (mission, 2026-11-03)

Module A de la mission « reconstruction des écarts premiers par accumulation spectrale exacte des
Tours ». Objets : la Tour géométrique `x^ρ/ρ`, sa phase, ses contacts (réutilisés de
`Terminal/TowerWinding.lean` : `windingContact β T k = exp((arctan(T/β) + kπ)/T)`), l'intervalle
entre deux contacts, la variation complexe d'une contribution sur cet intervalle, les portions de
bord, et l'accumulation signée depuis une origine.

Résultats (tous inconditionnels, aucune prémisse, aucun `sorry`) :

* `contactAt_ratio`, `contactAt_log_step`, `contact_interval_positive` : rapport `e^{π/T}`, pas
  logarithmique `π/T`, intervalle de longueur strictement positive (`T > 0`).
* `contact_is_axis_passage` : aux contacts, la partie imaginaire de `x^ρ/ρ` est nulle : le contact
  est le passage de la Tour sur l'axe réel (phase `arctan(T/β)` de la contribution `1/ρ`).
* `contact_interval_chain`, `contact_partition_exact`,
  `contact_accumulation_eq_endpoint_difference` : l'accumulation des VALEURS complexes sur les
  intervalles complets, plus les deux portions de bord, est exactement `F(x) − F(a)`, pour TOUTE
  fonction `F` — identité télescopique, indépendante de RH et indépendante du choix des contacts
  (`contact_accumulation_partition_independent`).
* `integratedTower_eq_geometric_div` : le canal intégré `x^ρ/(ρ(ρ+1))` est la Tour géométrique
  divisée par `ρ + 1` ; c'est la transformation de phase exacte entre les deux canaux.

Portée : ce module ne contient aucune arithmétique ; il établit que le découpage par contacts
conserve intégralement valeurs, phases et signes, et ne crée pas d'information nouvelle.
-/

namespace RHV6Fresh

open Real Complex

/-! ## 1. La Tour géométrique et ses canaux -/

/-- **La Tour géométrique** `x^ρ/ρ`. -/
noncomputable def towerValue (ρ : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ ρ / ρ

/-- Le canal intégré (poids de la formule explicite lissée compilée) `x^ρ/(ρ(ρ+1))`. -/
noncomputable def integratedTower (ρ : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ ρ / (ρ * (ρ + 1))

/-- **Transformation de phase entre canaux** : le canal intégré est la Tour divisée par `ρ + 1`.
La phase est décalée de `−arg(ρ + 1)`, le module divisé par `|ρ + 1|`. -/
theorem integratedTower_eq_geometric_div (ρ : ℂ) (x : ℝ) :
    integratedTower ρ x = towerValue ρ x / (ρ + 1) := by
  unfold integratedTower towerValue
  rw [div_div]

/-- La phase de la Tour `(β, T)` : `arctan(T/β)`. -/
noncomputable def towerPhase (β T : ℝ) : ℝ := Real.arctan (T / β)

/-! ## 2. Contacts, intervalles, pas -/

/-- Le contact d'indice entier `k`, réutilisé de `TowerWinding` (`exp((φ + kπ)/T)`). -/
noncomputable def contactAt (β T : ℝ) (k : ℤ) : ℝ := windingContact β T k

theorem contactAt_pos (β T : ℝ) (k : ℤ) : 0 < contactAt β T k := Real.exp_pos _

theorem contactAt_eq (β T : ℝ) (k : ℤ) :
    contactAt β T k = Real.exp ((towerPhase β T + k * Real.pi) / T) := rfl

/-- **Rapport de deux contacts consécutifs** : `e^{π/T}`. -/
theorem contactAt_ratio {β T : ℝ} (hT : T ≠ 0) (k : ℤ) :
    contactAt β T (k + 1) / contactAt β T k = Real.exp (Real.pi / T) := by
  unfold contactAt windingContact
  rw [← Real.exp_sub]
  congr 1
  push_cast
  field_simp
  ring

/-- **Pas logarithmique** : `log C_{k+1} − log C_k = π/T`. -/
theorem contactAt_log_step {β T : ℝ} (hT : T ≠ 0) (k : ℤ) :
    Real.log (contactAt β T (k + 1)) - Real.log (contactAt β T k) = Real.pi / T := by
  unfold contactAt windingContact
  rw [Real.log_exp, Real.log_exp]
  push_cast
  field_simp
  ring

/-- La largeur de l'intervalle `k` : `C_{k+1} − C_k`. -/
noncomputable def contactInterval (β T : ℝ) (k : ℤ) : ℝ :=
  contactAt β T (k + 1) - contactAt β T k

/-- **Intervalle de longueur strictement positive** (`T > 0`). -/
theorem contact_interval_positive {β T : ℝ} (hT : 0 < T) (k : ℤ) :
    0 < contactInterval β T k := by
  unfold contactInterval contactAt windingContact
  rw [sub_pos]
  apply Real.exp_lt_exp.mpr
  push_cast
  rw [div_lt_div_iff_of_pos_right hT]
  linarith [Real.pi_pos]

/-- La position des contacts dépend de `β` par la phase seule ; le pas ne dépend que de `T`
(`contactAt_log_step`). Explicitement : `C_k(β, T) = C_k(1/2, T) · exp((φ(β) − φ(1/2))/T)`. -/
theorem contact_radial_factor (β T : ℝ) (k : ℤ) :
    contactAt β T k = contactAt (1 / 2) T k *
      Real.exp ((towerPhase β T - towerPhase (1 / 2) T) / T) := by
  unfold contactAt windingContact towerPhase
  rw [← Real.exp_add]
  congr 1
  by_cases hT : T = 0
  · subst hT; simp
  · field_simp
    ring

/-! ## 3. Le contact est le passage sur l'axe réel -/

/-- Pour `x > 0` : `x^ρ = x^β · exp(i T log x)` (décomposition module–phase). -/
theorem ofReal_cpow_eq_rpow_mul_exp {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    (x : ℂ) ^ ρ = ((x ^ ρ.re : ℝ) : ℂ) * Complex.exp (Complex.I * (ρ.im * Real.log x)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hx.le]
  rw [Real.rpow_def_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
  · simp [Complex.mul_re, Complex.mul_im]; ring

/-- **Le contact est le passage sur l'axe** : à `x = C_k(β, T)`, `Im(x^ρ/ρ) = 0` pour
`ρ = β + iT`, `β > 0`, `T > 0`. -/
theorem contact_is_axis_passage {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (k : ℤ) :
    (towerValue (⟨β, T⟩ : ℂ) (contactAt β T k)).im = 0 := by
  unfold towerValue
  have hx : 0 < contactAt β T k := contactAt_pos β T k
  rw [ofReal_cpow_eq_rpow_mul_exp hx]
  -- la phase au contact : `T log C_k = arctan(T/β) + kπ`
  have hlog : (T : ℝ) * Real.log (contactAt β T k) = Real.arctan (T / β) + k * Real.pi := by
    unfold contactAt windingContact
    rw [Real.log_exp]
    field_simp
  have hρ : ((⟨β, T⟩ : ℂ).im : ℂ) * (Real.log (contactAt β T k) : ℂ) =
      ((Real.arctan (T / β) + k * Real.pi : ℝ) : ℂ) := by
    rw [← hlog]; push_cast; ring
  rw [hρ]
  -- `exp(iθ) = cos θ + i sin θ`, avec `θ = arctan(T/β) + kπ`
  set θ : ℝ := Real.arctan (T / β) + k * Real.pi with hθ
  have hexp : Complex.exp (Complex.I * (θ : ℂ)) =
      ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I]
    push_cast; ring
  rw [hexp]
  -- partie imaginaire de `A·(cos θ + i sin θ)/(β + iT)` : `A·(T cos θ... )`, on calcule
  have hden : (⟨β, T⟩ : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [Complex.div_im]
  have hcs : T * Real.cos θ - β * Real.sin θ = 0 := by
    have hc : Real.cos θ = Real.cos (Real.arctan (T / β)) * (-1 : ℝ) ^ k := by
      rw [hθ, Real.cos_add_int_mul_pi]; ring
    have hs : Real.sin θ = Real.sin (Real.arctan (T / β)) * (-1 : ℝ) ^ k := by
      rw [hθ, Real.sin_add_int_mul_pi]; ring
    rw [hc, hs, Real.cos_arctan, Real.sin_arctan]
    have hβ' : β ≠ 0 := hβ.ne'
    field_simp
    ring
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.normSq_mk]
  rw [div_sub_div_same]
  apply div_eq_zero_iff.mpr
  left
  linear_combination (-(contactAt β T k ^ β)) * hcs

/-! ## 4. Variation sur un intervalle et accumulation exacte -/

/-- **La variation complexe** d'une contribution `F` sur l'intervalle `k` : `F(C_{k+1}) − F(C_k)`.
La valeur complexe complète est conservée (ni module, ni comptage). -/
noncomputable def contactVariation (F : ℝ → ℂ) (β T : ℝ) (k : ℤ) : ℂ :=
  F (contactAt β T (k + 1)) - F (contactAt β T k)

/-- L'accumulation des variations sur `n` intervalles consécutifs à partir de l'indice `k₀`. -/
noncomputable def contactAccumulation (F : ℝ → ℂ) (β T : ℝ) (k₀ : ℤ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n, contactVariation F β T (k₀ + j)

/-- **Enchaînement** : deux intervalles consécutifs se composent exactement. -/
theorem contact_interval_chain (F : ℝ → ℂ) (β T : ℝ) (k : ℤ) :
    contactVariation F β T k + contactVariation F β T (k + 1) =
      F (contactAt β T (k + 1 + 1)) - F (contactAt β T k) := by
  unfold contactVariation
  ring

/-- **Télescopage exact** : l'accumulation sur `n` intervalles complets est la différence des
valeurs aux deux contacts extrêmes. Aucune hypothèse sur `F`. -/
theorem contact_partition_exact (F : ℝ → ℂ) (β T : ℝ) (k₀ : ℤ) (n : ℕ) :
    contactAccumulation F β T k₀ n = F (contactAt β T (k₀ + n)) - F (contactAt β T k₀) := by
  unfold contactAccumulation contactVariation
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have : k₀ + (n : ℤ) + 1 = k₀ + ((n : ℤ) + 1) := by ring
    rw [this]
    ring

/-- **L'accumulation depuis une origine `a` jusqu'à une position `x`** : portion de bord initiale
(`a` → premier contact), intervalles complets, portion de bord finale (dernier contact → `x`).
Les deux portions de bord sont obligatoires. -/
noncomputable def accumulationFrom (F : ℝ → ℂ) (β T : ℝ) (k₀ : ℤ) (n : ℕ) (a x : ℝ) : ℂ :=
  (F (contactAt β T k₀) - F a) + contactAccumulation F β T k₀ n +
    (F x - F (contactAt β T (k₀ + n)))

/-- **L'identité attendue** : `A_ρ(a, x) = F(x) − F(a)`, pour toute `F`, tout choix des contacts,
tout nombre d'intervalles. Son caractère télescopique ne dépend pas de RH. -/
theorem contact_accumulation_eq_endpoint_difference (F : ℝ → ℂ) (β T : ℝ) (k₀ : ℤ) (n : ℕ)
    (a x : ℝ) : accumulationFrom F β T k₀ n a x = F x - F a := by
  unfold accumulationFrom
  rw [contact_partition_exact]
  ring

/-- **Indépendance du découpage** : deux découpages quelconques (indices, nombre d'intervalles,
et même paramètres `(β', T')` d'une autre Tour) donnent la même accumulation. Le découpage par
contacts est une représentation géométrique exacte de la variation, non une information nouvelle. -/
theorem contact_accumulation_partition_independent (F : ℝ → ℂ) (β T β' T' : ℝ)
    (k₀ k₀' : ℤ) (n n' : ℕ) (a x : ℝ) :
    accumulationFrom F β T k₀ n a x = accumulationFrom F β' T' k₀' n' a x := by
  rw [contact_accumulation_eq_endpoint_difference, contact_accumulation_eq_endpoint_difference]

/-- Les contacts du canal intégré ne sont pas ceux de la Tour géométrique : la variation du canal
intégré sur un intervalle de contacts de la Tour est la variation de la Tour divisée par `ρ + 1`. -/
theorem integrated_variation_eq_geometric_div (ρ : ℂ) (β T : ℝ) (k : ℤ) :
    contactVariation (integratedTower ρ) β T k =
      contactVariation (towerValue ρ) β T k / (ρ + 1) := by
  unfold contactVariation
  rw [integratedTower_eq_geometric_div, integratedTower_eq_geometric_div, sub_div]

#print axioms contact_is_axis_passage
#print axioms contact_accumulation_eq_endpoint_difference
#print axioms contact_accumulation_partition_independent

end RHV6Fresh
