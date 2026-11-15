/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TowerMeetings
import RHV6Fresh.Terminal.ContactSeriesReading

/-!
# RHV6Fresh — Terminal/MeetingContactReading : ce que les contacts d'une Tour imposent à sa valeur
aux points de rencontre, et la lecture radiale aux rencontres (ON contre OFF)
(§19.44, 2026-11-04 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse, aucun
axiome,
aucun `sorry`)

Point de départ (révision demandée par l'auteur) : les contacts ne sont pas aveugles au radial. Deux
contacts consécutifs rendent la fréquence puis la position radiale (`radial_of_contact_value_ratio`,
`radial_of_contact_tangent`, `radial_from_amplitude_step`, `inversion_from_consecutive_contacts`).
Ce module relie cette lecture aux **points de rencontre** : la valeur réelle d'une Tour à une
abscisse
`x` quelconque (en particulier un point de rencontre `p_{n+1}`) est entièrement fixée par son
**dernier contact avant `x`** (position et valeur, qui lisent `β`), par la **fraction de cellule**
parcourue depuis ce contact (qui lit la fréquence, la position étant donnée), et par la croissance
radiale sur cette fraction.

## 1. Dernier contact avant une abscisse, fraction de cellule
* `lastContactBefore β T x = ⌊stagePosition β T x⌋`, `cellFraction β T x = fract(stagePosition)` ;
  `lastContact_le`, `lt_contact_succ` : `C_k ≤ x < C_{k+1}` ; `log_div_lastContact` :
  `log(x/C_k) = π·f/T`.
* `cellIndexAt_le_lastContactBefore` : l'indice de cellule du pivot (`⌈s⌉ − 1`) ne dépasse jamais le
  dernier contact (`⌊s⌋`) ; ils coïncident hors des abscisses qui sont elles-mêmes des contacts.
* `lastContact_difference_bounds` : entre deux abscisses, le nombre de contacts traversés diffère de
  `T·log(q/p)/π` de moins d'une unité, **quelle que soit `β`** (le comptage lit la fréquence).

## 2. La valeur à la rencontre depuis le dernier contact
* `towerRe_from_lastContact` : `Re Tour(x) = v_k · (x/C_k)^β · cos(π f)` avec `k` le dernier contact
  avant `x`, `v_k` sa valeur réelle signée, `f` la fraction de cellule. **La position et la valeur
  du
  contact lisent `β` ; la fraction `f` lit la fréquence ; la croissance `(x/C_k)^β = exp(βπf/T)`
  (`growth_factor_eq`) lit encore `β`.**
* `radial_of_meeting_value` : hors des zéros de la trajectoire (`f ≠ 0`, `cos(πf) ≠ 0`), la position
  radiale se lit aussi sur **la valeur à la rencontre** et la valeur au dernier contact.

## 3. Lecture radiale aux rencontres : ON contre OFF
* `radialReadingAt β T x` : lecture radiale depuis les deux contacts encadrant `x`
  (`radialReadingAt_eq` : elle vaut `β`, toujours, à toute fréquence).
* `mirror_readings_sum_one` : à une même abscisse, les lectures d'une Tour et de son miroir
  `(β, 1−β)` se somment à `1` ; `meetingReadingsAgree_iff_line` : **elles coïncident si et seulement
  si la Tour est en ligne**. Hors ligne, les deux membres d'une paire passent sur l'axe en des
  positions distinctes (`mirror_contacts_coincide_iff`) et lisent deux positions radiales
  distinctes.

## 4. Dépôt entre deux rencontres et résidu de cassure
* `meetingValueDeposit β T I = Re Tour(p_{n+1}) − Re Tour(p_n)` ;
  `meetingValueDeposit_eq_accumulation` :
  c'est l'accumulation de la Tour sur ses propres contacts entre les deux rencontres, pour tout
  découpage (instance de `contact_accumulation_eq_endpoint_difference`).
* `breakResidual s target x = target − Σ_{(β,T)∈s} Re Tour(x)` : ce que les Tours hors de la famille
  finie `s` doivent déposer à l'abscisse `x` pour que la cassure soit exacte ;
  `breakResidual_erase` : retirer un membre ajoute exactement sa valeur au résidu (la part d'une
  paire
  hors ligne retirée est ce que les autres doivent absorber ; garde-fou pour E429).

Portée : identités exactes. Rien ici n'exclut un zéro OFF ; le module compile les objets qu'E429
mesure (lecture radiale aux rencontres, fraction de cellule à la rencontre, résidu à absorber sur
une
série) et fixe les trois obligations comme questions mesurées, jamais posées.
-/

namespace RHV6Fresh

open Real

/-! ## 1. Dernier contact avant une abscisse, fraction de cellule -/

/-- Dernier contact de la Tour `(β, T)` avant (ou en) l'abscisse `x` : `⌊(T·log x − φ)/π⌋`. -/
noncomputable def lastContactBefore (β T x : ℝ) : ℤ := ⌊stagePosition β T x⌋

/-- Fraction de cellule parcourue en `x` depuis le dernier contact : `fract((T·log x − φ)/π) ∈ [0,
1)`. -/
noncomputable def cellFraction (β T x : ℝ) : ℝ := Int.fract (stagePosition β T x)

theorem cellFraction_nonneg (β T x : ℝ) : 0 ≤ cellFraction β T x := Int.fract_nonneg _

theorem cellFraction_lt_one (β T x : ℝ) : cellFraction β T x < 1 := Int.fract_lt_one _

theorem stagePosition_eq_last_add_fraction (β T x : ℝ) :
    stagePosition β T x = lastContactBefore β T x + cellFraction β T x :=
  (Int.floor_add_fract _).symm

/-- `T·log x − φ = π·(k + f)` avec `k` le dernier contact et `f` la fraction de cellule. -/
theorem height_mul_log_eq (β T x : ℝ) :
    T * Real.log x - towerPhase β T = Real.pi * (lastContactBefore β T x + cellFraction β T x) := by
  rw [← stagePosition_eq_last_add_fraction]
  unfold stagePosition towerPhase
  field_simp

/-- Le dernier contact avant `x` est avant `x`. -/
theorem lastContact_le {β T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    contactAt β T (lastContactBefore β T x) ≤ x := by
  have h := height_mul_log_eq β T x
  have hf := mul_nonneg Real.pi_pos.le (cellFraction_nonneg β T x)
  calc contactAt β T (lastContactBefore β T x)
      = Real.exp ((towerPhase β T + (lastContactBefore β T x : ℝ) * Real.pi) / T) := contactAt_eq _ _ _
    _ ≤ Real.exp (Real.log x) := by
        rw [Real.exp_le_exp, div_le_iff₀ hT, mul_comm (Real.log x) T]
        linarith
    _ = x := Real.exp_log hx

/-- Le contact suivant est après `x`. -/
theorem lt_contact_succ {β T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    x < contactAt β T (lastContactBefore β T x + 1) := by
  have h := height_mul_log_eq β T x
  have hf := mul_lt_mul_of_pos_left (cellFraction_lt_one β T x) Real.pi_pos
  calc x = Real.exp (Real.log x) := (Real.exp_log hx).symm
    _ < Real.exp ((towerPhase β T + ((lastContactBefore β T x + 1 : ℤ) : ℝ) * Real.pi) / T) := by
        rw [Real.exp_lt_exp, lt_div_iff₀ hT, mul_comm (Real.log x) T]
        push_cast
        linarith
    _ = contactAt β T (lastContactBefore β T x + 1) := (contactAt_eq _ _ _).symm

/-- `log(x / C_k) = π·f/T`. -/
theorem log_div_lastContact {β T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    Real.log (x / contactAt β T (lastContactBefore β T x)) = Real.pi * cellFraction β T x / T := by
  rw [Real.log_div hx.ne' (contactAt_pos _ _ _).ne', eq_div_iff hT.ne']
  have hC := height_mul_log_contactAt (β := β) hT.ne' (lastContactBefore β T x)
  have h := height_mul_log_eq β T x
  linear_combination h - hC

/-- L'indice de cellule du pivot ne dépasse jamais le dernier contact. -/
theorem cellIndexAt_le_lastContactBefore (β T x : ℝ) :
    cellIndexAt β T x ≤ lastContactBefore β T x := by
  rw [cellIndexAt_eq_ceil]
  unfold lastContactBefore
  have := Int.ceil_le_floor_add_one (stagePosition β T x)
  omega

/-- **Le comptage des contacts entre deux abscisses lit la fréquence** : il diffère de
`T·log(q/p)/π`
de moins d'une unité, pour toute position radiale. -/
theorem lastContact_difference_bounds (β T : ℝ) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    |((lastContactBefore β T q - lastContactBefore β T p : ℤ) : ℝ) -
        T * Real.log (q / p) / Real.pi| < 1 := by
  rw [← stagePosition_sub β T p q hp hq]
  unfold lastContactBefore
  have h1 := Int.floor_le (stagePosition β T p)
  have h2 := Int.lt_floor_add_one (stagePosition β T p)
  have h3 := Int.floor_le (stagePosition β T q)
  have h4 := Int.lt_floor_add_one (stagePosition β T q)
  push_cast
  rw [abs_lt]
  constructor <;> linarith

/-! ## 2. La valeur à la rencontre depuis le dernier contact -/

/-- **La valeur réelle en `x` est fixée par le dernier contact** :
`Re Tour(x) = v_k · (x/C_k)^β · cos(πf)`. La position `C_k` et la valeur `v_k` lisent `β`
(inversions compilées) ; la fraction `f` lit la fréquence. -/
theorem towerRe_from_lastContact {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    towerRe β T x =
      contactRealValue β T (lastContactBefore β T x) *
        (x / contactAt β T (lastContactBefore β T x)) ^ β *
        Real.cos (Real.pi * cellFraction β T x) := by
  have hC := contactAt_pos β T (lastContactBefore β T x)
  have hphase : T * Real.log x - towerPhase β T =
      Real.pi * cellFraction β T x + (lastContactBefore β T x : ℝ) * Real.pi := by
    rw [height_mul_log_eq]
    ring
  unfold towerRe contactRealValue
  rw [hphase, Real.cos_add_int_mul_pi, Real.div_rpow hx.le hC.le]
  have hCk : contactAt β T (lastContactBefore β T x) ^ β ≠ 0 :=
    (Real.rpow_pos_of_pos hC β).ne'
  have hn : ‖(⟨β, T⟩ : ℂ)‖ ≠ 0 := (norm_mk_pos hβ).ne'
  field_simp

/-- **La croissance radiale sur la fraction de cellule** : `(x/C_k)^β = exp(βπf/T)`. -/
theorem growth_factor_eq {β T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    (x / contactAt β T (lastContactBefore β T x)) ^ β =
      Real.exp (β * Real.pi * cellFraction β T x / T) := by
  rw [Real.rpow_def_of_pos (div_pos hx (contactAt_pos _ _ _)), log_div_lastContact hT hx]
  exact congrArg Real.exp (by ring)

/-- **Lecture radiale sur la valeur à la rencontre** : hors des zéros de la trajectoire, `β` se lit
sur
`Re Tour(x)`, la valeur au dernier contact et la fraction de cellule. -/
theorem radial_of_meeting_value {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) {x : ℝ} (hx : 0 < x)
    (hf : cellFraction β T x ≠ 0) (hc : Real.cos (Real.pi * cellFraction β T x) ≠ 0) :
    β = T * (Real.log |towerRe β T x| -
              Real.log |contactRealValue β T (lastContactBefore β T x)| -
              Real.log |Real.cos (Real.pi * cellFraction β T x)|) /
          (Real.pi * cellFraction β T x) := by
  have hv : |contactRealValue β T (lastContactBefore β T x)| ≠ 0 :=
    abs_ne_zero.mpr (contactRealValue_ne_zero hβ _)
  have he : Real.exp (β * Real.pi * cellFraction β T x / T) ≠ 0 := (Real.exp_pos _).ne'
  have hc' : |Real.cos (Real.pi * cellFraction β T x)| ≠ 0 := abs_ne_zero.mpr hc
  have hpf : Real.pi * cellFraction β T x ≠ 0 := mul_ne_zero Real.pi_pos.ne' hf
  rw [towerRe_from_lastContact hβ hT hx, growth_factor_eq hT hx, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos _), Real.log_mul (mul_ne_zero hv he) hc', Real.log_mul hv he,
    Real.log_exp]
  field_simp
  ring

/-! ## 3. Lecture radiale aux rencontres : ON contre OFF -/

/-- Lecture radiale de la Tour `(β, T)` depuis les deux contacts qui encadrent `x`
(rapport des valeurs signées, `radial_of_contact_value_ratio`). -/
noncomputable def radialReadingAt (β T x : ℝ) : ℝ :=
  T * Real.log (|contactRealValue β T (lastContactBefore β T x + 1)| /
    |contactRealValue β T (lastContactBefore β T x)|) / Real.pi

/-- La lecture aux deux contacts encadrant une rencontre rend `β`, à toute fréquence, sans limite.
-/
theorem radialReadingAt_eq {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (x : ℝ) :
    radialReadingAt β T x = β :=
  (radial_of_contact_value_ratio hβ hT.ne' _).symm

/-- **Paire miroir** : à une même abscisse, les deux lectures se somment à `1`. -/
theorem mirror_readings_sum_one {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) (x : ℝ) :
    radialReadingAt β T x + radialReadingAt (1 - β) T x = 1 := by
  rw [radialReadingAt_eq hβ hT, radialReadingAt_eq (by linarith) hT]
  ring

/-- Les lectures de la Tour et de son miroir à l'abscisse `x` coïncident. -/
def MeetingReadingsAgree (β T x : ℝ) : Prop :=
  radialReadingAt β T x = radialReadingAt (1 - β) T x

/-- **ON contre OFF à la rencontre** : les deux lectures coïncident si et seulement si la Tour est
en ligne. -/
theorem meetingReadingsAgree_iff_line {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T)
    (x : ℝ) :
    MeetingReadingsAgree β T x ↔ β = 1 / 2 := by
  unfold MeetingReadingsAgree
  rw [radialReadingAt_eq hβ hT, radialReadingAt_eq (by linarith) hT]
  constructor <;> intro h <;> linarith

/-- Hors ligne, la fraction de cellule du miroir diffère de celle de la Tour d'un décalage constant
(modulo 1) : `stagePosition(1−β) − stagePosition(β) = (φ_β − φ_{1−β})/π`
(`mirror_stagePosition_difference`). -/
theorem mirror_stage_shift_ne_zero {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T)
    (hβ2 : β ≠ 1 / 2) (q : ℝ) : stagePosition (1 - β) T q - stagePosition β T q ≠ 0 := by
  intro h0
  have h := mirror_stagePosition_difference β T q
  rw [neg_div] at h
  have hπ : 0 < Real.pi := Real.pi_pos
  have hdiv : mirrorPhaseShift β T / Real.pi = 0 := by linarith
  have hz : mirrorPhaseShift β T = 0 := (div_eq_zero_iff.mp hdiv).resolve_right hπ.ne'
  exact hβ2 ((mirrorPhaseShift_eq_zero_iff hβ hβ1 hT).mp hz)

/-! ## 4. Dépôt entre deux rencontres et résidu de cassure -/

/-- Dépôt réel de la Tour `(β, T)` sur l'écart premier `I` : `Re Tour(p_{n+1}) − Re Tour(p_n)`. -/
noncomputable def meetingValueDeposit (β T : ℝ) (I : PrimeGapInterval) : ℝ :=
  towerRe β T I.upper - towerRe β T I.lower

/-- **Le dépôt est l'accumulation sur les propres contacts de la Tour**, pour tout découpage
(`contact_accumulation_eq_endpoint_difference`). -/
theorem meetingValueDeposit_eq_accumulation (β T : ℝ) (I : PrimeGapInterval) (k₀ : ℤ)
    (n : ℕ) :
    ((meetingValueDeposit β T I : ℝ) : ℂ) =
      accumulationFrom (fun y => ((towerRe β T y : ℝ) : ℂ)) β T k₀ n I.lower I.upper := by
  rw [contact_accumulation_eq_endpoint_difference]
  unfold meetingValueDeposit
  push_cast
  ring

/-- Résidu de cassure à l'abscisse `x` pour une famille finie `s` de paramètres `(β, T)` et une
cible
`target` : ce que les Tours hors de `s` doivent déposer. -/
noncomputable def breakResidual (s : Finset (ℝ × ℝ)) (target x : ℝ) : ℝ :=
  target - ∑ ρ ∈ s, towerRe ρ.1 ρ.2 x

/-- **Retirer un membre ajoute exactement sa valeur au résidu** : la part d'une Tour retirée est ce
que les autres doivent absorber à cette abscisse. -/
theorem breakResidual_erase {s : Finset (ℝ × ℝ)} {ρ : ℝ × ℝ} (hρ : ρ ∈ s) (target x : ℝ) :
    breakResidual (s.erase ρ) target x = breakResidual s target x + towerRe ρ.1 ρ.2 x := by
  unfold breakResidual
  rw [← Finset.add_sum_erase s _ hρ]
  ring

/-- **Paire miroir dans la famille** : retirer la paire `(β, T), (1−β, T)` ajoute la somme de ses
deux valeurs, chacune fixée par son propre dernier contact (`towerRe_from_lastContact`). -/
theorem breakResidual_erase_pair {s : Finset (ℝ × ℝ)} {β T : ℝ} (h₁ : (β, T) ∈ s)
    (h₂ : (1 - β, T) ∈ s) (hne : (β, T) ≠ (1 - β, T)) (target x : ℝ) :
    breakResidual ((s.erase (β, T)).erase (1 - β, T)) target x =
      breakResidual s target x + (towerRe β T x + towerRe (1 - β) T x) := by
  rw [breakResidual_erase (Finset.mem_erase.mpr ⟨hne.symm, h₂⟩), breakResidual_erase h₁]
  ring

end RHV6Fresh

#print axioms RHV6Fresh.towerRe_from_lastContact
#print axioms RHV6Fresh.radial_of_meeting_value
#print axioms RHV6Fresh.meetingReadingsAgree_iff_line
#print axioms RHV6Fresh.lastContact_difference_bounds
#print axioms RHV6Fresh.breakResidual_erase_pair
