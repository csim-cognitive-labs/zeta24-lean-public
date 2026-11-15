/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.SuccessiveContactConstraints
import RHV6Fresh.Terminal.MeetingPoint

/-!
# RHV6Fresh — Terminal/TowerMeetings : rencontres entre Tours sur l'axe réel
(§19.40, 2026-11-03, correction de la démarche : les rencontres avant toute contrainte radiale)

Module isolé (non ajouté à `RHV6Fresh.lean`). Il ne pose aucune hypothèse, n'introduit aucun
axiome, et ne parle ni de zéros OFF ni de contradiction. Il décrit la **géométrie réelle des
rencontres** entre deux Tours `x^ρ/ρ` lues le long de l'axe des abscisses `x > 0`, et la lecture
de l'écart des hauteurs dans la succession de ces rencontres.

Lexique (§19) : « point de rencontre » (`meetingPoint`) reste réservé à la fin d'un écart
premier ; les objets de ce module s'appellent **rencontres entre Tours** (`towerMeeting`),
**coïncidences de contacts** (`contactsCoincide`) et **rencontres lentes / rapides**
(`slowMeetingLog`, `fastMeetingLog`).

## 1. Trajectoire réelle d'une Tour
* `towerRe`, `towerRe_eq_re` : partie réelle de la Tour `(β, T)` en `x > 0` :
  `x^β/‖ρ‖ · cos(T log x − φ)` ; `towerRe_at_contact` : aux contacts, c'est la valeur réelle signée.
* `unitTowerRe` : trajectoire unitaire `cos(T log x − φ)` ; `towerRe_eq_amp_mul_unit`.

## 2. Coïncidence de contacts (A)
* `contactsCoincide_iff` : deux contacts coïncident ⟺ égalité exacte des abscisses logarithmiques
  `(φ₁ + kπ)/T₁ = (φ₂ + jπ)/T₂`.
* `norm_mk_inj` : à même position radiale, même module ⟹ même hauteur.
* `contactsCoincide_not_meeting` : **à même position radiale et hauteurs distinctes, une coïncidence
  de contacts n'est jamais une rencontre de valeurs** (les deux valeurs réelles ont des modules
  différents).

## 3. Rencontre de valeurs (B)
* `towerMeeting` : égalité des parties réelles à la même abscisse.
* `unit_difference`, `unitMeeting_iff` : la différence des trajectoires unitaires se factorise en
  produit de deux sinus ; rencontre unitaire ⟺ famille **rapide** (fréquence `T₁ + T₂`) ou famille
  **lente** (fréquence `T₁ − T₂`).
* `slowMeetingLog`, `fastMeetingLog`, `slow_sin_eq_zero_iff`, `fast_sin_eq_zero_iff` : les deux
  réseaux de rencontres unitaires, indexés par un entier.
* `slowMeetingLog_succ_sub`, `gap_of_slowMeetings` : **l'écart des hauteurs est lu exactement dans
  deux rencontres lentes consécutives** (`T₁ − T₂ = 2π/(u_{m+1} − u_m)`) ; `sum_of_fastMeetings` :
  la somme des hauteurs est lue dans deux rencontres rapides consécutives.
* `slowMeetingLog_zero_pos`, `slowMeetingLog_zero_lt` : la rencontre lente d'indice zéro de deux
  Tours de même position radiale est collée à l'abscisse 1 (entre `1` et `exp(1/(2T))`).
* `towerMeeting_iff_same_radial` : à même position radiale, rencontre brute ⟺ égalité des
  trajectoires unitaires pondérées par les modules inverses.
* `towerMeeting_of_unitMeeting_iff` : en un point de rencontre unitaire, la rencontre brute n'a lieu
  que si les deux Tours traversent l'axe imaginaire (valeur réelle nulle) : **les rencontres brutes
  sont déplacées par rapport aux réseaux unitaires**, sauf aux passages par zéro.

## 4. Succession des rencontres et cassure (C)
* `slowMeetings_coincide_iff` : une rencontre lente de la paire `(1, 2)` coïncide avec une rencontre
  lente de la paire `(2, 3)` ⟺ relation exacte entre les deux écarts consécutifs et les phases.
* `gap_of_slowMeetings_at_primeGap` : si deux rencontres lentes consécutives tombent aux deux
  bouts logarithmiques d'un écart premier (la seconde au point de rencontre `meetingPoint I`),
  alors l'écart des hauteurs vaut `2π` sur la longueur logarithmique de l'écart premier. Énoncé
  conditionnel : l'hypothèse de coïncidence est explicite, jamais posée.
-/

namespace RHV6Fresh

open Real

/-! ## 1. Trajectoire réelle d'une Tour -/

/-- Partie réelle de la Tour `(β, T)` à l'abscisse `x` : `x^β/‖ρ‖ · cos(T log x − φ)`. -/
noncomputable def towerRe (β T x : ℝ) : ℝ :=
  x ^ β / ‖(⟨β, T⟩ : ℂ)‖ * Real.cos (T * Real.log x - towerPhase β T)

theorem towerRe_eq_re {β T : ℝ} (hβ : 0 < β) {x : ℝ} (hx : 0 < x) :
    (towerValue (⟨β, T⟩ : ℂ) x).re = towerRe β T x := by
  rw [towerValue_polar hβ hx, mul_comm Complex.I, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re]
  rfl

/-- Aux contacts, la trajectoire réelle prend la valeur réelle signée du contact. -/
theorem towerRe_at_contact {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (k : ℤ) :
    towerRe β T (contactAt β T k) = contactRealValue β T k := by
  rw [← towerRe_eq_re hβ (contactAt_pos β T k), towerValue_at_contact hβ hT k, Complex.ofReal_re]

/-- Trajectoire unitaire : `cos(T log x − φ)`. -/
noncomputable def unitTowerRe (β T x : ℝ) : ℝ := Real.cos (T * Real.log x - towerPhase β T)

theorem towerRe_eq_amp_mul_unit (β T x : ℝ) :
    towerRe β T x = x ^ β / ‖(⟨β, T⟩ : ℂ)‖ * unitTowerRe β T x := rfl

/-! ## 2. Coïncidence de contacts (A) -/

/-- Coïncidence de contacts : les deux Tours touchent l'axe réel à la même abscisse. -/
def contactsCoincide (β₁ T₁ β₂ T₂ : ℝ) (k j : ℤ) : Prop :=
  contactAt β₁ T₁ k = contactAt β₂ T₂ j

theorem contactsCoincide_iff (β₁ T₁ β₂ T₂ : ℝ) (k j : ℤ) :
    contactsCoincide β₁ T₁ β₂ T₂ k j ↔
      (towerPhase β₁ T₁ + k * Real.pi) / T₁ = (towerPhase β₂ T₂ + j * Real.pi) / T₂ := by
  unfold contactsCoincide contactAt windingContact towerPhase
  exact Real.exp_eq_exp

/-- À même position radiale, même module ⟹ même hauteur. -/
theorem norm_mk_inj {β T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (h : ‖(⟨β, T₁⟩ : ℂ)‖ = ‖(⟨β, T₂⟩ : ℂ)‖) : T₁ = T₂ := by
  have h2 : Complex.normSq (⟨β, T₁⟩ : ℂ) = Complex.normSq (⟨β, T₂⟩ : ℂ) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h]
  rw [Complex.normSq_mk, Complex.normSq_mk] at h2
  have h3 : (T₁ - T₂) * (T₁ + T₂) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp h3 with h4 | h4
  · linarith
  · linarith

/-- **Une coïncidence de contacts n'est jamais une rencontre de valeurs** (même position radiale,
hauteurs distinctes). -/
theorem contactsCoincide_not_meeting {β T₁ T₂ : ℝ} (hβ : 0 < β) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hne : T₁ ≠ T₂) (k j : ℤ) (h : contactsCoincide β T₁ β T₂ k j) :
    ¬ (towerRe β T₁ (contactAt β T₁ k) = towerRe β T₂ (contactAt β T₁ k)) := by
  intro hm
  rw [towerRe_at_contact hβ hT₁ k, h, towerRe_at_contact hβ hT₂ j] at hm
  have ha := congrArg (fun v : ℝ => |v|) hm
  rw [abs_contactRealValue hβ k, abs_contactRealValue hβ j, ← h] at ha
  have hp : contactAt β T₁ k ^ β ≠ 0 := (Real.rpow_pos_of_pos (contactAt_pos β T₁ k) β).ne'
  have hn₁ : ‖(⟨β, T₁⟩ : ℂ)‖ ≠ 0 := (norm_mk_pos (T := T₁) hβ).ne'
  have hn₂ : ‖(⟨β, T₂⟩ : ℂ)‖ ≠ 0 := (norm_mk_pos (T := T₂) hβ).ne'
  have hnorm : ‖(⟨β, T₁⟩ : ℂ)‖ = ‖(⟨β, T₂⟩ : ℂ)‖ := by
    field_simp at ha
    linarith
  exact hne (norm_mk_inj hT₁ hT₂ hnorm)

/-! ## 3. Rencontre de valeurs (B) -/

/-- Rencontre de valeurs : mêmes parties réelles à la même abscisse. -/
def towerMeeting (β₁ T₁ β₂ T₂ x : ℝ) : Prop := towerRe β₁ T₁ x = towerRe β₂ T₂ x

/-- Factorisation de la différence des trajectoires unitaires. -/
theorem unit_difference (β₁ T₁ β₂ T₂ x : ℝ) :
    unitTowerRe β₁ T₁ x - unitTowerRe β₂ T₂ x =
      -2 * Real.sin (((T₁ + T₂) * Real.log x - (towerPhase β₁ T₁ + towerPhase β₂ T₂)) / 2) *
        Real.sin (((T₁ - T₂) * Real.log x - (towerPhase β₁ T₁ - towerPhase β₂ T₂)) / 2) := by
  unfold unitTowerRe
  rw [Real.cos_sub_cos]
  have e1 : ((T₁ * Real.log x - towerPhase β₁ T₁) + (T₂ * Real.log x - towerPhase β₂ T₂)) / 2 =
      ((T₁ + T₂) * Real.log x - (towerPhase β₁ T₁ + towerPhase β₂ T₂)) / 2 := by ring
  have e2 : ((T₁ * Real.log x - towerPhase β₁ T₁) - (T₂ * Real.log x - towerPhase β₂ T₂)) / 2 =
      ((T₁ - T₂) * Real.log x - (towerPhase β₁ T₁ - towerPhase β₂ T₂)) / 2 := by ring
  rw [e1, e2]

/-- Rencontre unitaire ⟺ famille rapide ou famille lente. -/
theorem unitMeeting_iff (β₁ T₁ β₂ T₂ x : ℝ) :
    unitTowerRe β₁ T₁ x = unitTowerRe β₂ T₂ x ↔
      Real.sin (((T₁ + T₂) * Real.log x - (towerPhase β₁ T₁ + towerPhase β₂ T₂)) / 2) = 0 ∨
      Real.sin (((T₁ - T₂) * Real.log x - (towerPhase β₁ T₁ - towerPhase β₂ T₂)) / 2) = 0 := by
  rw [← sub_eq_zero, unit_difference]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · rw [h]; ring
    · rw [h]; ring

/-- Abscisse logarithmique de la `m`-ième rencontre lente. -/
noncomputable def slowMeetingLog (β₁ T₁ β₂ T₂ : ℝ) (m : ℤ) : ℝ :=
  (towerPhase β₁ T₁ - towerPhase β₂ T₂ + 2 * m * Real.pi) / (T₁ - T₂)

/-- Abscisse logarithmique de la `m`-ième rencontre rapide. -/
noncomputable def fastMeetingLog (β₁ T₁ β₂ T₂ : ℝ) (m : ℤ) : ℝ :=
  (towerPhase β₁ T₁ + towerPhase β₂ T₂ + 2 * m * Real.pi) / (T₁ + T₂)

theorem slow_sin_eq_zero_iff {β₁ T₁ β₂ T₂ : ℝ} (hT : T₁ ≠ T₂) (u : ℝ) :
    Real.sin (((T₁ - T₂) * u - (towerPhase β₁ T₁ - towerPhase β₂ T₂)) / 2) = 0 ↔
      ∃ m : ℤ, u = slowMeetingLog β₁ T₁ β₂ T₂ m := by
  have hd : T₁ - T₂ ≠ 0 := sub_ne_zero.mpr hT
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    unfold slowMeetingLog
    rw [eq_div_iff hd]
    linarith
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm]
    unfold slowMeetingLog
    field_simp
    ring

theorem fast_sin_eq_zero_iff {β₁ T₁ β₂ T₂ : ℝ} (hT : T₁ + T₂ ≠ 0) (u : ℝ) :
    Real.sin (((T₁ + T₂) * u - (towerPhase β₁ T₁ + towerPhase β₂ T₂)) / 2) = 0 ↔
      ∃ m : ℤ, u = fastMeetingLog β₁ T₁ β₂ T₂ m := by
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    unfold fastMeetingLog
    rw [eq_div_iff hT]
    linarith
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm]
    unfold fastMeetingLog
    field_simp
    ring

/-- Deux rencontres lentes consécutives sont séparées de `2π/(T₁ − T₂)`. -/
theorem slowMeetingLog_succ_sub {β₁ T₁ β₂ T₂ : ℝ} (hT : T₁ ≠ T₂) (m : ℤ) :
    slowMeetingLog β₁ T₁ β₂ T₂ (m + 1) - slowMeetingLog β₁ T₁ β₂ T₂ m =
      2 * Real.pi / (T₁ - T₂) := by
  have hd : T₁ - T₂ ≠ 0 := sub_ne_zero.mpr hT
  unfold slowMeetingLog
  rw [div_sub_div_same]
  congr 1
  push_cast
  ring

/-- **L'écart des hauteurs est lu exactement dans deux rencontres lentes consécutives.** -/
theorem gap_of_slowMeetings {β₁ T₁ β₂ T₂ : ℝ} (hT : T₁ ≠ T₂) (m : ℤ) :
    T₁ - T₂ = 2 * Real.pi /
      (slowMeetingLog β₁ T₁ β₂ T₂ (m + 1) - slowMeetingLog β₁ T₁ β₂ T₂ m) := by
  have hd : T₁ - T₂ ≠ 0 := sub_ne_zero.mpr hT
  rw [slowMeetingLog_succ_sub hT m]
  field_simp

theorem fastMeetingLog_succ_sub (β₁ T₁ β₂ T₂ : ℝ) (m : ℤ) :
    fastMeetingLog β₁ T₁ β₂ T₂ (m + 1) - fastMeetingLog β₁ T₁ β₂ T₂ m =
      2 * Real.pi / (T₁ + T₂) := by
  unfold fastMeetingLog
  rw [div_sub_div_same]
  congr 1
  push_cast
  ring

/-- La somme des hauteurs est lue exactement dans deux rencontres rapides consécutives. -/
theorem sum_of_fastMeetings {β₁ T₁ β₂ T₂ : ℝ} (hT : T₁ + T₂ ≠ 0) (m : ℤ) :
    T₁ + T₂ = 2 * Real.pi /
      (fastMeetingLog β₁ T₁ β₂ T₂ (m + 1) - fastMeetingLog β₁ T₁ β₂ T₂ m) := by
  rw [fastMeetingLog_succ_sub β₁ T₁ β₂ T₂ m]
  field_simp

/-- À même position radiale, la rencontre lente d'indice zéro est au-delà de l'abscisse 1. -/
theorem slowMeetingLog_zero_pos {β T₁ T₂ : ℝ} (hβ : 0 < β) (hTT : T₁ < T₂) :
    0 < slowMeetingLog β T₁ β T₂ 0 := by
  unfold slowMeetingLog towerPhase
  have hφ : Real.arctan (T₁ / β) < Real.arctan (T₂ / β) :=
    Real.arctan_strictMono (div_lt_div_of_pos_right hTT hβ)
  have hnum : Real.arctan (T₁ / β) - Real.arctan (T₂ / β) + 2 * ((0 : ℤ) : ℝ) * Real.pi < 0 := by
    push_cast; linarith
  exact div_pos_of_neg_of_neg hnum (by linarith)

/-- ... et avant `exp(1/(2T₁))` : elle est collée à l'abscisse 1. -/
theorem slowMeetingLog_zero_lt {β T₁ T₂ : ℝ} (hβ : 0 < β) (hT₁ : 0 < T₁) (hTT : T₁ < T₂) :
    slowMeetingLog β T₁ β T₂ 0 < 1 / (2 * T₁) := by
  unfold slowMeetingLog towerPhase
  have hinc := phase_increment_lt hβ hT₁ hTT
  have key : (Real.arctan (T₁ / β) - Real.arctan (T₂ / β) + 2 * ((0 : ℤ) : ℝ) * Real.pi) /
      (T₁ - T₂) = (Real.arctan (T₂ / β) - Real.arctan (T₁ / β)) / (T₂ - T₁) := by
    push_cast
    rw [← neg_div_neg_eq]
    congr 1 <;> ring
  rw [key, div_lt_iff₀ (by linarith)]
  have e : 1 / (2 * T₁) * (T₂ - T₁) = (T₂ - T₁) / (2 * T₁) := by ring
  rw [e, lt_div_iff₀ (by positivity)]
  nlinarith

/-- À même position radiale, rencontre brute ⟺ égalité des trajectoires unitaires pondérées par
les modules inverses. -/
theorem towerMeeting_iff_same_radial {β T₁ T₂ x : ℝ} (hx : 0 < x) :
    towerMeeting β T₁ β T₂ x ↔
      unitTowerRe β T₁ x / ‖(⟨β, T₁⟩ : ℂ)‖ = unitTowerRe β T₂ x / ‖(⟨β, T₂⟩ : ℂ)‖ := by
  unfold towerMeeting
  rw [towerRe_eq_amp_mul_unit, towerRe_eq_amp_mul_unit]
  have hp : x ^ β ≠ 0 := (Real.rpow_pos_of_pos hx β).ne'
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc, mul_right_inj' hp]

/-- En un point de rencontre unitaire, la rencontre brute n'a lieu que si la valeur réelle est
nulle (modules distincts). -/
theorem towerMeeting_of_unitMeeting_iff {β T₁ T₂ x : ℝ} (hβ : 0 < β) (hx : 0 < x)
    (hu : unitTowerRe β T₁ x = unitTowerRe β T₂ x)
    (hn : ‖(⟨β, T₁⟩ : ℂ)‖ ≠ ‖(⟨β, T₂⟩ : ℂ)‖) :
    towerMeeting β T₁ β T₂ x ↔ unitTowerRe β T₂ x = 0 := by
  rw [towerMeeting_iff_same_radial hx, hu]
  have hn₁ : ‖(⟨β, T₁⟩ : ℂ)‖ ≠ 0 := (norm_mk_pos (T := T₁) hβ).ne'
  have hn₂ : ‖(⟨β, T₂⟩ : ℂ)‖ ≠ 0 := (norm_mk_pos (T := T₂) hβ).ne'
  constructor
  · intro h
    by_contra hc
    apply hn
    field_simp at h
    linarith
  · intro h
    rw [h, zero_div, zero_div]

/-- Hauteurs distinctes ⟹ modules distincts (même position radiale). -/
theorem norm_mk_ne {β T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hne : T₁ ≠ T₂) :
    ‖(⟨β, T₁⟩ : ℂ)‖ ≠ ‖(⟨β, T₂⟩ : ℂ)‖ := fun h => hne (norm_mk_inj hT₁ hT₂ h)

/-! ## 4. Succession des rencontres et cassure (C) -/

/-- Coïncidence d'une rencontre lente de `(1, 2)` avec une rencontre lente de `(2, 3)` ⟺ relation
exacte entre les deux écarts consécutifs et les phases. -/
theorem slowMeetings_coincide_iff {β₁ T₁ β₂ T₂ β₃ T₃ : ℝ} (h12 : T₁ ≠ T₂) (h23 : T₂ ≠ T₃)
    (m m' : ℤ) :
    slowMeetingLog β₁ T₁ β₂ T₂ m = slowMeetingLog β₂ T₂ β₃ T₃ m' ↔
      (towerPhase β₁ T₁ - towerPhase β₂ T₂ + 2 * m * Real.pi) * (T₂ - T₃) =
        (towerPhase β₂ T₂ - towerPhase β₃ T₃ + 2 * m' * Real.pi) * (T₁ - T₂) := by
  unfold slowMeetingLog
  exact div_eq_div_iff (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h23)

/-- Si deux rencontres lentes consécutives tombent aux deux bouts logarithmiques d'un écart premier
(la seconde au point de rencontre), l'écart des hauteurs vaut `2π` sur la longueur logarithmique de
l'écart premier. Hypothèse explicite, jamais posée. -/
theorem gap_of_slowMeetings_at_primeGap {β₁ T₁ β₂ T₂ : ℝ} (hT : T₁ ≠ T₂) (I : PrimeGapInterval)
    (m : ℤ) (h₁ : slowMeetingLog β₁ T₁ β₂ T₂ m = Real.log I.lower)
    (h₂ : slowMeetingLog β₁ T₁ β₂ T₂ (m + 1) = Real.log (meetingPoint I)) :
    T₁ - T₂ = 2 * Real.pi / (Real.log (meetingPoint I) - Real.log I.lower) := by
  rw [← h₁, ← h₂]
  exact gap_of_slowMeetings hT m

end RHV6Fresh

#print axioms RHV6Fresh.contactsCoincide_not_meeting
#print axioms RHV6Fresh.unitMeeting_iff
#print axioms RHV6Fresh.gap_of_slowMeetings
#print axioms RHV6Fresh.slowMeetingLog_zero_lt
#print axioms RHV6Fresh.towerMeeting_of_unitMeeting_iff
#print axioms RHV6Fresh.gap_of_slowMeetings_at_primeGap
