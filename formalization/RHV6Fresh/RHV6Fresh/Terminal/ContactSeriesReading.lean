/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FirstExceedanceRaccord
import RHV6Fresh.Terminal.ContactRealValue
import RHV6Fresh.Terminal.HarmonicRestoringLaw
import RHV6Fresh.Terminal.PrimeGapReconstruction
import RHV6Fresh.Terminal.GrammarContactStability

/-!
# RHV6Fresh — Terminal/ContactSeriesReading : lecture des transitions par la progression complète
des contacts sur une série d'écarts, raccord individuel–collectif, information radiale du miroir
(E428, §19.42.5–19.42.6, 2026-11-04)

Module isolé (non ajouté à `RHV6Fresh.lean`). Aucune hypothèse, aucun axiome, aucune prémisse
équivalente à RH, aucun zéro OFF, aucune contradiction cherchée. Les quatre corrections de l'auteur
(§19.42.6) sont compilées ici ; tout est identité ou encadrement sur des objets déjà définis.

## A0 — raccord individuel–collectif (obligation A)
* `individualStepContribution` : contribution d'une Tour au pas `N → N + 1` du canal intégré ;
* `truncatedStep_eq_sum_individual` : pas collectif tronqué = fond + **somme finie** des contributions
  individuelles (même troncature `lowFrequencies H`, même lissage) ;
* `individual_contribution_eq_own_contact_accumulation` : chaque contribution est l'accumulation de sa
  propre Tour sur ses propres contacts, pour tout découpage `(β, T, k₀, n)` ;
* `collective_eq_individual_add_rest` : collectif = une Tour + le reste (garde-fou) ;
* `reconstructedVonMangoldt_eq_limit_of_individual_sums` : la limite en `H` de ces sommes finies est
  `Λ̂(N)` — c'est exactement le passage à la limite du théorème compilé, aucune somme réordonnée.

## A1–A2 — progression des indices sur une série
* `seriesShift_telescopes` : les décalages consécutifs se somment en le décalage total ;
* `cellIndex_difference_bounds` : `|Δk − T·log(q'/q)/π| < 1`, toute position radiale (la phase
  `arctan(T/β)` s'élimine dans la différence) ; `log_ratio_bracket` : `|log(q'/q) − hΔk| < h`.

## A3 corrigé — arrondi certifié depuis `(p, T, Δk)` seuls
* `estimate_brackets` : `q̂e^{−h} < q < q̂e^{h}` (encadrement non centré) ;
* `certified_rounding` : `q̂(e^h − 1) < ½ ⟹ |q − q̂| < ½` ; `certified_unique_integer` : un seul entier ;
* `true_threshold_also_certifies` : l'ancien seuil `q(e^h − 1) < ½` du plan 19.42.3 certifie aussi
  (le compilateur le dit) ; son défaut n'est pas mathématique mais pratique : il lit le `q` inconnu.

## A4 — amplitude sur série, Tour contre miroir
* `mirror_series_amplitude_difference(_eq_zero_iff)` : `(1 − β)L − βL = (1 − 2β)L`, nul ⟺ ligne.

## C corrigé — indices du miroir, et portée exacte de la minoration miroir
* `mirror_contact_log_ratio` : `log(C_k(β)/C_k(1 − β)) = (φ_β − φ_{1−β})/T` ;
* `mirrorPhaseShift_eq_zero_iff` : décalage nul ⟺ `β = ½` ; `mirror_stagePosition_difference` ;
* `mirror_series_shift_difference_le_one` : sur une même série, les différences d'indices de la Tour
  et du miroir diffèrent d'au plus une unité — **jamais présumées égales** ;
* `mirrorMode_sub_norm` : `‖v₊ − v₋‖ = 2|sinh(dt)|`, nul en ligne : la minoration `≥ 2` de
  `mirrorMode_add_norm_ge` ne porte que sur la somme des modes normalisés (`mirror_floor_not_transported`).
-/

namespace RHV6Fresh

open RHV3Lean Filter Topology

/-! ## A0. Raccord individuel–collectif -/

/-- Contribution d'une Tour `ρ` au pas `N → N + 1` du canal intégré (convention `x · Σ`). -/
noncomputable def individualStepContribution (ρ : ExplicitIndex) (N : ℕ) : ℂ :=
  (((N : ℝ) + 1 : ℝ) : ℂ) * integratedTowerTerm ρ ((N : ℝ) + 1) -
    ((N : ℝ) : ℂ) * integratedTowerTerm ρ (N : ℝ)

/-- **Décomposition finie** : le pas collectif tronqué est le fond plus la somme des contributions
individuelles sur la même troncature. -/
theorem truncatedStep_eq_sum_individual (H : ℝ) (k₀ : ExplicitIndex → ℤ) (n : ExplicitIndex → ℕ)
    (N : ℕ) :
    truncatedStep H k₀ n N =
      stepAt backgroundPrimitive N + ∑ ρ ∈ lowFrequencies H, individualStepContribution ρ N := by
  rw [truncatedStep_eq]
  unfold individualStepContribution
  rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Chaque contribution individuelle est l'accumulation de **sa propre** Tour sur **ses propres**
contacts, quel que soit le découpage. -/
theorem individual_contribution_eq_own_contact_accumulation (ρ : ExplicitIndex) (N : ℕ)
    (β T : ℝ) (k₀ : ℤ) (n : ℕ) :
    individualStepContribution ρ N =
      (((N : ℝ) + 1 : ℝ) : ℂ) *
          (accumulationFrom (integratedTowerTerm ρ) β T k₀ n 1 ((N : ℝ) + 1) +
            integratedTowerTerm ρ 1) -
        ((N : ℝ) : ℂ) *
          (accumulationFrom (integratedTowerTerm ρ) β T k₀ n 1 (N : ℝ) + integratedTowerTerm ρ 1) := by
  rw [contact_accumulation_eq_endpoint_difference, contact_accumulation_eq_endpoint_difference]
  unfold individualStepContribution
  ring

/-- **Garde-fou** : le collectif est une Tour plus le reste ; une Tour isolée n'est jamais le collectif. -/
theorem collective_eq_individual_add_rest (H : ℝ) (N : ℕ) {ρ : ExplicitIndex}
    (hρ : ρ ∈ lowFrequencies H) :
    ∑ ρ' ∈ lowFrequencies H, individualStepContribution ρ' N =
      individualStepContribution ρ N +
        ∑ ρ' ∈ (lowFrequencies H).erase ρ, individualStepContribution ρ' N :=
  (Finset.add_sum_erase _ _ hρ).symm

/-- **Même limite** : les sommes finies de contributions individuelles tendent vers `Λ̂(N)` exactement
comme le théorème compilé (même troncature, même lissage, même passage à la limite). -/
theorem reconstructedVonMangoldt_eq_limit_of_individual_sums (k₀ : ExplicitIndex → ℤ)
    (n : ExplicitIndex → ℕ) {N : ℕ} (hN : 3 ≤ N) :
    Tendsto (fun H : ℝ =>
        (stepAt backgroundPrimitive N + ∑ ρ ∈ lowFrequencies H, individualStepContribution ρ N) -
          (stepAt backgroundPrimitive (N - 1) +
            ∑ ρ ∈ lowFrequencies H, individualStepContribution ρ (N - 1)))
      atTop (𝓝 (reconstructedVonMangoldt N)) := by
  refine (reconstructedVonMangoldt_eq_limit_contact_accumulation k₀ n hN).congr (fun H => ?_)
  rw [truncatedStep_eq_sum_individual, truncatedStep_eq_sum_individual]

/-! ## A1–A2. Progression des indices sur une série -/

/-- Décalage d'indice de cellule entre l'ancrage `p r` et le membre `p (r + j)` de la série. -/
noncomputable def seriesShift (β T : ℝ) (p : ℕ → ℝ) (r j : ℕ) : ℤ :=
  cellIndexAt β T (p (r + j)) - cellIndexAt β T (p r)

/-- **Télescopage** des décalages consécutifs. -/
theorem seriesShift_telescopes (β T : ℝ) (p : ℕ → ℝ) (r m : ℕ) :
    ∑ j ∈ Finset.range m,
        (cellIndexAt β T (p (r + (j + 1))) - cellIndexAt β T (p (r + j))) =
      seriesShift β T p r m := by
  unfold seriesShift
  rw [Finset.sum_range_sub (fun j => cellIndexAt β T (p (r + j)))]
  simp

theorem ceil_sub_ceil_bounds (s s' : ℝ) :
    (s' - s) - 1 < ((⌈s'⌉ - ⌈s⌉ : ℤ) : ℝ) ∧ ((⌈s'⌉ - ⌈s⌉ : ℤ) : ℝ) < (s' - s) + 1 := by
  have h1 := Int.le_ceil s
  have h2 := Int.ceil_lt_add_one s
  have h3 := Int.le_ceil s'
  have h4 := Int.ceil_lt_add_one s'
  push_cast
  constructor <;> linarith

/-- La phase s'élimine dans la différence de positions : il ne reste que `T·log(q'/q)/π`. -/
theorem stagePosition_sub (β T q q' : ℝ) (hq : 0 < q) (hq' : 0 < q') :
    stagePosition β T q' - stagePosition β T q = T * Real.log (q' / q) / Real.pi := by
  unfold stagePosition
  rw [Real.log_div hq'.ne' hq.ne']
  ring

/-- **Encadrement des différences d'indices**, toute position radiale. -/
theorem cellIndex_difference_bounds (β T q q' : ℝ) (hq : 0 < q) (hq' : 0 < q') :
    |((cellIndexAt β T q' - cellIndexAt β T q : ℤ) : ℝ) - T * Real.log (q' / q) / Real.pi| < 1 := by
  rw [cellIndexAt_eq_ceil, cellIndexAt_eq_ceil, ← stagePosition_sub β T q q' hq hq']
  have h := ceil_sub_ceil_bounds (stagePosition β T q) (stagePosition β T q')
  rw [abs_lt]
  push_cast at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- Forme de l'auteur : `|log(q'/q) − hΔk| < h` avec `h = π/T`. -/
theorem log_ratio_bracket (β T q q' : ℝ) (hT : 0 < T) (hq : 0 < q) (hq' : 0 < q') :
    |Real.log (q' / q) - Real.pi / T * ((cellIndexAt β T q' - cellIndexAt β T q : ℤ) : ℝ)| <
      Real.pi / T := by
  have h := cellIndex_difference_bounds β T q q' hq hq'
  have hπ := Real.pi_pos
  have hpT : 0 < Real.pi / T := div_pos hπ hT
  set D : ℝ := ((cellIndexAt β T q' - cellIndexAt β T q : ℤ) : ℝ)
  have hid : Real.log (q' / q) - Real.pi / T * D =
      -(Real.pi / T) * (D - T * Real.log (q' / q) / Real.pi) := by
    have hT' : T ≠ 0 := hT.ne'
    have hπ' : Real.pi ≠ 0 := hπ.ne'
    field_simp
    ring
  rw [hid, abs_mul, abs_neg, abs_of_pos hpT]
  calc Real.pi / T * |D - T * Real.log (q' / q) / Real.pi| < Real.pi / T * 1 :=
        mul_lt_mul_of_pos_left h hpT
    _ = Real.pi / T := mul_one _

/-! ## A3 corrigé. Arrondi certifié depuis `(p, T, Δk)` seuls -/

/-- `q̂ = p · exp(πΔk/T)` : ne lit que l'ancrage, la fréquence et le décalage d'indices. -/
noncomputable def seriesEstimate (p T : ℝ) (Δk : ℤ) : ℝ := p * Real.exp (Real.pi / T * Δk)

/-- **Encadrement non centré** : `q̂e^{−h} < q < q̂e^{h}`. -/
theorem estimate_brackets (β T p q : ℝ) (hT : 0 < T) (hp : 0 < p) (hq : 0 < q) :
    seriesEstimate p T (cellIndexAt β T q - cellIndexAt β T p) * Real.exp (-(Real.pi / T)) < q ∧
      q < seriesEstimate p T (cellIndexAt β T q - cellIndexAt β T p) * Real.exp (Real.pi / T) := by
  have h := log_ratio_bracket β T p q hT hp hq
  rw [abs_lt] at h
  have hL : Real.log (q / p) = Real.log q - Real.log p := Real.log_div hq.ne' hp.ne'
  unfold seriesEstimate
  constructor
  · rw [← Real.log_lt_log_iff (by positivity) hq, Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    linarith [h.1]
  · rw [← Real.log_lt_log_iff hq (by positivity), Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    linarith [h.2]

theorem one_sub_exp_neg_lt_exp_sub_one {h : ℝ} (hh : 0 < h) : 1 - Real.exp (-h) < Real.exp h - 1 := by
  have h1 : h + 1 < Real.exp h := Real.add_one_lt_exp hh.ne'
  have h2 : -h + 1 < Real.exp (-h) := Real.add_one_lt_exp (neg_ne_zero.mpr hh.ne')
  linarith

/-- **Arrondi certifié** : si `q̂(e^h − 1) < ½` — condition lue sur les données disponibles — alors
`|q − q̂| < ½`. -/
theorem certified_rounding {q qhat h : ℝ} (hh : 0 < h) (hq : 0 < qhat)
    (hlo : qhat * Real.exp (-h) < q) (hhi : q < qhat * Real.exp h)
    (hcert : qhat * (Real.exp h - 1) < 1 / 2) : |q - qhat| < 1 / 2 := by
  have hm := mul_lt_mul_of_pos_left (one_sub_exp_neg_lt_exp_sub_one hh) hq
  rw [abs_lt]
  constructor <;> linarith

/-- Un seul entier à moins de `½` de `q̂` : l'entier lu est unique. -/
theorem certified_unique_integer {x : ℝ} {n m : ℤ} (hn : |x - n| < 1 / 2) (hm : |x - m| < 1 / 2) :
    n = m := by
  have h1 : |((n : ℝ) - m)| < 1 := by
    calc |((n : ℝ) - m)| = |(x - m) - (x - n)| := by congr 1; ring
      _ ≤ |x - m| + |x - n| := abs_sub _ _
      _ < 1 := by linarith
  have h2 : |n - m| < 1 := by exact_mod_cast h1
  rcases abs_lt.mp h2 with ⟨a, b⟩
  omega

/-- L'ancien seuil du plan (`q(e^h − 1) < ½`, lu sur le `q` **inconnu**) certifie aussi : le défaut
signalé par l'auteur est pratique (non lisible), pas mathématique. Consigné tel que le compilateur
le dit. -/
theorem true_threshold_also_certifies {q qhat h : ℝ} (hh : 0 < h) (hq : 0 < q)
    (hlo : qhat * Real.exp (-h) < q) (hhi : q < qhat * Real.exp h)
    (hcert : q * (Real.exp h - 1) < 1 / 2) : |q - qhat| < 1 / 2 := by
  have hm := mul_lt_mul_of_pos_left (one_sub_exp_neg_lt_exp_sub_one hh) hq
  have hpos := Real.exp_pos h
  have hneg := Real.exp_pos (-h)
  have hprod : Real.exp h * Real.exp (-h) = 1 := by rw [← Real.exp_add]; simp
  rw [abs_lt]
  constructor
  · -- q − q̂ > −q(1 − e^{−h})  car q̂ < q·e^{h}
    have h5 := mul_lt_mul_of_pos_right hlo hpos
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h5
    nlinarith
  · -- q̂ − q < q(e^{h} − 1)
    nlinarith

/-! ## A4. Amplitude sur série, Tour contre miroir -/

theorem mirror_series_amplitude_difference (β p q : ℝ) :
    (1 - β) * Real.log (q / p) - β * Real.log (q / p) = (1 - 2 * β) * Real.log (q / p) := by ring

theorem mirror_series_amplitude_difference_eq_zero_iff (β p q : ℝ) (hL : Real.log (q / p) ≠ 0) :
    (1 - β) * Real.log (q / p) - β * Real.log (q / p) = 0 ↔ β = 1 / 2 := by
  rw [mirror_series_amplitude_difference, mul_eq_zero]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hL
  · intro h
    left
    linarith

/-! ## C corrigé. Indices du miroir -/

/-- Décalage de phase entre la Tour `(β, T)` et son miroir `(1 − β, T)`. -/
noncomputable def mirrorPhaseShift (β T : ℝ) : ℝ := Real.arctan (T / β) - Real.arctan (T / (1 - β))

/-- Formule de l'auteur : `log(C_k(β)/C_k(1 − β)) = (φ_β − φ_{1−β})/T`. -/
theorem mirror_contact_log_ratio (β T : ℝ) (k : ℤ) :
    Real.log (contactAt β T k / contactAt (1 - β) T k) = mirrorPhaseShift β T / T := by
  unfold contactAt windingContact mirrorPhaseShift
  rw [← Real.exp_sub, Real.log_exp, ← sub_div]
  ring

theorem mirrorPhaseShift_eq_zero_iff {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) :
    mirrorPhaseShift β T = 0 ↔ β = 1 / 2 := by
  unfold mirrorPhaseShift
  rw [sub_eq_zero]
  constructor
  · intro h
    have h1β : 0 < 1 - β := by linarith
    have h2 : T / β = T / (1 - β) := Real.arctan_strictMono.injective h
    rw [div_eq_div_iff hβ.ne' h1β.ne'] at h2
    have := mul_left_cancel₀ hT.ne' h2
    linarith
  · intro h
    subst h
    norm_num

/-- La différence de positions Tour − miroir est constante en `q` : `−(φ_β − φ_{1−β})/π`. -/
theorem mirror_stagePosition_difference (β T q : ℝ) :
    stagePosition β T q - stagePosition (1 - β) T q = -(mirrorPhaseShift β T) / Real.pi := by
  unfold stagePosition mirrorPhaseShift
  ring

/-- **Sur une même série, les différences d'indices de la Tour et du miroir diffèrent d'au plus une
unité** : elles encadrent toutes deux `T·log(q/p)/π` à moins d'une unité. L'égalité n'est pas
présumée ; l'écart est à mesurer. -/
theorem mirror_series_shift_difference_le_one (β T p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    |(cellIndexAt (1 - β) T q - cellIndexAt (1 - β) T p) -
        (cellIndexAt β T q - cellIndexAt β T p)| ≤ 1 := by
  have h1 := cellIndex_difference_bounds β T p q hp hq
  have h2 := cellIndex_difference_bounds (1 - β) T p q hp hq
  rw [abs_lt] at h1 h2
  push_cast at h1 h2
  have h3 : |(((cellIndexAt (1 - β) T q - cellIndexAt (1 - β) T p) -
      (cellIndexAt β T q - cellIndexAt β T p) : ℤ) : ℝ)| < 2 := by
    rw [abs_lt]
    push_cast
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have h4 : |(cellIndexAt (1 - β) T q - cellIndexAt (1 - β) T p) -
      (cellIndexAt β T q - cellIndexAt β T p)| < 2 := by exact_mod_cast h3
  rcases abs_lt.mp h4 with ⟨a, b⟩
  rw [abs_le]
  constructor <;> omega

/-! ## C. Portée exacte de la minoration miroir -/

/-- Module de la **différence** miroir : `2|sinh(dt)|`, nul en ligne — aucun plancher. -/
theorem mirrorMode_sub_norm (d T t : ℝ) :
    ‖complexMode d T t - complexMode (-d) T t‖ = 2 * |Real.sinh (d * t)| := by
  rw [mirrorMode_sub, norm_mul, norm_mul, complexMode_norm, zero_mul, Real.exp_zero, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num

theorem mirrorMode_sub_norm_on_line (T t : ℝ) :
    ‖complexMode 0 T t - complexMode (-0) T t‖ = 0 := by
  rw [mirrorMode_sub_norm]
  simp

/-- La minoration `≥ 2` porte sur la somme des modes normalisés ; pour toute autre combinaison, seule
l'inégalité triangulaire est disponible. -/
theorem mirror_floor_not_transported (A B : ℂ) : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le A B

#print axioms truncatedStep_eq_sum_individual
#print axioms reconstructedVonMangoldt_eq_limit_of_individual_sums
#print axioms cellIndex_difference_bounds
#print axioms certified_rounding
#print axioms certified_unique_integer
#print axioms true_threshold_also_certifies
#print axioms mirror_series_shift_difference_le_one
#print axioms mirrorMode_sub_norm

end RHV6Fresh
