/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FirstExceedanceRaccord
import RHV6Fresh.Terminal.FirstZeroContactComparison
import RHV6Fresh.Terminal.FirstZeroDominance
import RHV6Fresh.Terminal.ContactSensitivity
import RHV6Fresh.Terminal.OnCrossReadings

/-!
# Loi de transport grammatical entre deux événements consécutifs (auteur, 2026-10-19, treizième message)

Proposition de l'auteur, mot pour mot : « Lorsqu'une Tour est engagée dans le régime dominé par le premier zéro, le
passage grammatical au premier suivant conserve la compatibilité entre la fréquence de la Tour d'arrivée, ses rencontres
authentiques et le besoin d'amplitude imposé par les deux cellules successives. » Formulée sans supposer l'arrivée ON.

Objets (Tour d'arrivée `l`, partie réelle quelconque) : événement `q` (premier événement de dépassement) ; cellule
authentique de `q` dans la Tour d'arrivée (`memberStage l q`) ; `stageChangePrime l q` = le premier nombre premier au-delà
du contact qui ferme la cellule de `q` (premier événement premier dans la cellule suivante) ; `GrammarTransport l q q'` =
conjonction de trois compatibilités : (F) fréquence : l'écart logarithmique des deux rencontres d'entrée est le nombre
d'étages fois `π/T` ; (R) rencontres authentiques : chaque événement est encadré par les deux contacts de sa cellule ;
(B) besoin d'amplitude : d'une cellule à l'autre, le rapport des amplitudes brutes aux rencontres d'entrée est celui
qu'impose l'échelle commune (racine du rapport des rencontres). Aucune normalisation.

Résultats (axiomes standard) : (F) et (R) valent pour TOUTE partie réelle ; (B) ⟺ même cellule ∨ `β = 1/2` ; au premier
suivant immédiat la loi est vide dès que les deux événements sont dans la même cellule ; au premier événement de la cellule
suivante la loi est ⟺ `β_l = 1/2` (caractérisation) ; elle équivaut au raccord local de contact et ferme le cas bas en
consommant le certificat de dépassement.
-/

namespace RHV6Fresh

open RHV3Lean
open scoped Classical

/-! ## 1. Rencontres d'une Tour sous forme exponentielle -/

/-- Exposant de la rencontre `k` de la Tour de `z`. -/
noncomputable def meetingExponent (z : TrueZero) (k : ℤ) : ℝ :=
  (Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) + (k : ℝ) * Real.pi) / rZeroHeight z.1

theorem contactMinusAt_eq_exp_meeting (z : TrueZero) (k : ℤ) :
    contactMinusAt z k = Real.exp (meetingExponent z k) := contactMinusAt_eq_exp z k

theorem meetingExponent_sub (z : TrueZero) (k k' : ℤ) :
    meetingExponent z k' - meetingExponent z k = ((k' - k : ℤ) : ℝ) * (Real.pi / rZeroHeight z.1) := by
  have hT : rZeroHeight z.1 ≠ 0 := (z.2 : 0 < rZeroHeight z.1).ne'
  unfold meetingExponent
  push_cast
  field_simp
  ring

/-! ## 2. Les deux cellules successives et l'événement suivant -/

/-- Le premier nombre premier au-delà du contact qui ferme la cellule de `q` dans la Tour de `l`. -/
noncomputable def stageChangePrime (l : TrueZero) (q : ℝ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (⌊contactMinusAt l (memberStage l q + 1)⌋₊ + 1))

theorem stageChangePrime_spec (l : TrueZero) (q : ℝ) :
    ⌊contactMinusAt l (memberStage l q + 1)⌋₊ + 1 ≤ stageChangePrime l q ∧ Nat.Prime (stageChangePrime l q) :=
  Nat.find_spec (Nat.exists_infinite_primes _)

theorem stageChangePrime_prime (l : TrueZero) (q : ℝ) : Nat.Prime (stageChangePrime l q) :=
  (stageChangePrime_spec l q).2

theorem stageChangePrime_gt_contact (l : TrueZero) (q : ℝ) :
    contactMinusAt l (memberStage l q + 1) < stageChangePrime l q := by
  have h := (stageChangePrime_spec l q).1
  have h1 : contactMinusAt l (memberStage l q + 1) < (⌊contactMinusAt l (memberStage l q + 1)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h2 : ((⌊contactMinusAt l (memberStage l q + 1)⌋₊ + 1 : ℕ) : ℝ) ≤ (stageChangePrime l q : ℝ) := by
    exact_mod_cast h
  push_cast at h2
  linarith

/-- Minimalité : aucun premier entre la fermeture de la cellule et `stageChangePrime` (premier événement de la cellule
suivante). -/
theorem stageChangePrime_min (l : TrueZero) (q : ℝ) {r : ℕ} (hr : contactMinusAt l (memberStage l q + 1) < r)
    (hprime : Nat.Prime r) : stageChangePrime l q ≤ r := by
  apply Nat.find_min'
  refine ⟨?_, hprime⟩
  have : ⌊contactMinusAt l (memberStage l q + 1)⌋₊ < r := by
    rw [Nat.floor_lt (contactMinusAt_positive l _).le]; exact hr
  omega

/-! ## 3. Les trois compatibilités -/

/-- (R) Une rencontre authentique encadre l'événement : `C_k < q ≤ C_{k+1}`, `k` = cellule de `q`, toute position radiale. -/
theorem event_in_own_cell (l : TrueZero) {q : ℝ} (hq : 0 < q) :
    contactMinusAt l (memberStage l q) < q ∧ q ≤ contactMinusAt l (memberStage l q + 1) := by
  have hT : 0 < rZeroHeight l.1 := l.2
  have hπ := Real.pi_pos
  set a := Real.arctan (rZeroHeight l.1 / rZeroRadialPosition l.1)
  set s := (rZeroHeight l.1 * Real.log q - a) / Real.pi with hs
  have hk : memberStage l q = ⌈s⌉ - 1 := rfl
  have hc1 : ((⌈s⌉ - 1 : ℤ) : ℝ) < s := by
    push_cast; linarith [Int.ceil_lt_add_one s]
  have hc2 : s ≤ ((⌈s⌉ - 1 + 1 : ℤ) : ℝ) := by push_cast; simpa using Int.le_ceil s
  rw [contactMinusAt_eq_exp, contactMinusAt_eq_exp, hk]
  constructor
  · rw [← Real.exp_log hq, Real.exp_lt_exp, div_lt_iff₀ hT]
    have := (lt_div_iff₀ hπ).mp (hs ▸ hc1)
    linarith
  · rw [← Real.exp_log hq, Real.exp_le_exp, le_div_iff₀ hT]
    have := (div_le_iff₀ hπ).mp (hs ▸ hc2)
    linarith

/-- (F) Fréquence : l'écart logarithmique de deux rencontres est le nombre d'étages fois `π/T`, toute position radiale. -/
theorem meeting_frequency_compatible (l : TrueZero) (k k' : ℤ) :
    Real.log (contactMinusAt l k') - Real.log (contactMinusAt l k) =
      ((k' - k : ℤ) : ℝ) * (Real.pi / rZeroHeight l.1) := by
  rw [contactMinusAt_eq_exp_meeting, contactMinusAt_eq_exp_meeting, Real.log_exp, Real.log_exp]
  exact meetingExponent_sub l k k'

/-- (B) Rapport des amplitudes brutes à deux rencontres : `e^{β·(k'−k)π/T}` ; besoin d'échelle commune : `e^{(k'−k)π/(2T)}`. -/
theorem need_ratio_two_cells (l : TrueZero) (k k' : ℤ) :
    ‖zeroTerm l (contactMinusAt l k')‖ / ‖zeroTerm l (contactMinusAt l k)‖ =
      Real.exp (((k' - k : ℤ) : ℝ) * (Real.pi / rZeroHeight l.1) * rZeroRadialPosition l.1) := by
  rw [norm_zeroTerm_eq l (contactMinusAt_positive l k'), norm_zeroTerm_eq l (contactMinusAt_positive l k),
    contactMinusAt_eq_exp_meeting, contactMinusAt_eq_exp_meeting, ← Real.exp_mul, ← Real.exp_mul,
    div_div_div_cancel_right₀ (norm_zeroPoint_pos l).ne', ← Real.exp_sub, ← sub_mul, meetingExponent_sub]

theorem scale_ratio_two_cells (l : TrueZero) (k k' : ℤ) :
    (contactMinusAt l k' / contactMinusAt l k) ^ (1 / 2 : ℝ) =
      Real.exp (((k' - k : ℤ) : ℝ) * (Real.pi / rZeroHeight l.1) * (1 / 2)) := by
  rw [contactMinusAt_eq_exp_meeting, contactMinusAt_eq_exp_meeting, ← Real.exp_sub, ← Real.exp_mul,
    meetingExponent_sub]

/-- **Besoin d'amplitude de deux cellules** : compatible avec l'échelle commune ⟺ même cellule ∨ `β = 1/2`. -/
theorem need_compatible_iff (l : TrueZero) (k k' : ℤ) :
    ‖zeroTerm l (contactMinusAt l k')‖ / ‖zeroTerm l (contactMinusAt l k)‖ =
        (contactMinusAt l k' / contactMinusAt l k) ^ (1 / 2 : ℝ) ↔
      k' = k ∨ rZeroRadialPosition l.1 = 1 / 2 := by
  have hT : 0 < rZeroHeight l.1 := l.2
  have hπT : 0 < Real.pi / rZeroHeight l.1 := div_pos Real.pi_pos hT
  rw [need_ratio_two_cells, scale_ratio_two_cells, Real.exp_eq_exp]
  constructor
  · intro h
    have h' : ((k' - k : ℤ) : ℝ) * (Real.pi / rZeroHeight l.1) * (rZeroRadialPosition l.1 - 1 / 2) = 0 := by
      linarith
    rcases mul_eq_zero.mp h' with h0 | h0
    · rcases mul_eq_zero.mp h0 with h1 | h1
      · left; exact_mod_cast (sub_eq_zero.mp (by exact_mod_cast h1 : (k' - k : ℤ) = 0))
      · exact absurd h1 hπT.ne'
    · right; linarith
  · rintro (h | h)
    · subst h; simp
    · rw [h]

/-! ## 4. La loi de transport et sa portée exacte -/

/-- **Loi de transport grammatical** entre deux événements `q` et `q'` pour la Tour d'arrivée `l` (aucune position
radiale supposée) : fréquence, rencontres authentiques, besoin d'amplitude des deux cellules successives. -/
def GrammarTransport (l : TrueZero) (q q' : ℝ) : Prop :=
  (Real.log (contactMinusAt l (memberStage l q')) - Real.log (contactMinusAt l (memberStage l q)) =
      ((memberStage l q' - memberStage l q : ℤ) : ℝ) * (Real.pi / rZeroHeight l.1)) ∧
  (contactMinusAt l (memberStage l q) < q ∧ q ≤ contactMinusAt l (memberStage l q + 1)) ∧
  (contactMinusAt l (memberStage l q') < q' ∧ q' ≤ contactMinusAt l (memberStage l q' + 1)) ∧
  ‖zeroTerm l (contactMinusAt l (memberStage l q'))‖ / ‖zeroTerm l (contactMinusAt l (memberStage l q))‖ =
    (contactMinusAt l (memberStage l q') / contactMinusAt l (memberStage l q)) ^ (1 / 2 : ℝ)

/-- **Portée exacte de la loi** : fréquence et rencontres sont acquises pour toute position radiale ; la loi entière est
⟺ « même cellule » ∨ `β = 1/2`. -/
theorem grammarTransport_iff (l : TrueZero) {q q' : ℝ} (hq : 0 < q) (hq' : 0 < q') :
    GrammarTransport l q q' ↔ memberStage l q' = memberStage l q ∨ rZeroRadialPosition l.1 = 1 / 2 := by
  unfold GrammarTransport
  rw [← need_compatible_iff]
  exact ⟨fun h => h.2.2.2, fun h =>
    ⟨meeting_frequency_compatible l _ _, event_in_own_cell l hq, event_in_own_cell l hq', h⟩⟩

/-- **Au premier suivant dans la même cellule, la loi est vide** : vraie pour toute partie réelle. -/
theorem grammarTransport_same_cell (l : TrueZero) {q q' : ℝ} (hq : 0 < q) (hq' : 0 < q')
    (h : memberStage l q' = memberStage l q) : GrammarTransport l q q' :=
  (grammarTransport_iff l hq hq').mpr (Or.inl h)

/-- Le premier événement de la cellule suivante change bien de cellule. -/
theorem stageChangePrime_stage_ne (l : TrueZero) {q : ℝ} :
    memberStage l (stageChangePrime l q) ≠ memberStage l q := by
  intro h
  have hpos : (0 : ℝ) < stageChangePrime l q :=
    lt_trans (contactMinusAt_positive l _) (stageChangePrime_gt_contact l q)
  have hin := (event_in_own_cell l hpos).1
  rw [h] at hin
  have hgt := stageChangePrime_gt_contact l q
  have hmono : contactMinusAt l (memberStage l q) < contactMinusAt l (memberStage l q + 1) := by
    rw [contactMinusAt_eq_exp_meeting, contactMinusAt_eq_exp_meeting, Real.exp_lt_exp, ← sub_pos,
      meetingExponent_sub]
    have hT : 0 < rZeroHeight l.1 := l.2
    push_cast; simp; positivity
  -- `q'` est dans la cellule de `q`, donc `q' ≤ C_{k+1} < q'`
  have hle := (event_in_own_cell l hpos).2
  rw [h] at hle
  linarith

/-- **La loi au premier événement de dépassement et au premier événement de la cellule suivante.** -/
def GrammarTransportAtEvent (z₁ l : TrueZero) : Prop :=
  GrammarTransport l (firstExceedPrime z₁ l) (stageChangePrime l (firstExceedPrime z₁ l))

/-- **Caractérisation** : la loi au changement de cellule ⟺ `β_l = 1/2`. -/
theorem grammarTransportAtEvent_iff_onLine (z₁ l : TrueZero) :
    GrammarTransportAtEvent z₁ l ↔ rZeroRadialPosition l.1 = 1 / 2 := by
  unfold GrammarTransportAtEvent
  have hq := firstExceedPrime_pos z₁ l
  have hq' : (0 : ℝ) < stageChangePrime l (firstExceedPrime z₁ l) :=
    lt_trans (contactMinusAt_positive l _) (stageChangePrime_gt_contact l _)
  rw [grammarTransport_iff l hq hq']
  exact ⟨fun h => h.resolve_left (stageChangePrime_stage_ne l), Or.inr⟩

/-- La loi de transport et le raccord local de contact sont la même obligation. -/
theorem grammarTransportAtEvent_iff_localRaccord (z₁ l : TrueZero) :
    GrammarTransportAtEvent z₁ l ↔ LocalRaccord z₁ l :=
  (grammarTransportAtEvent_iff_onLine z₁ l).trans (localRaccord_iff_onLine z₁ l).symm

/-- **Fermeture du cas bas** : la loi au changement de cellule contredit le certificat de dépassement. -/
theorem low_arrival_impossible_of_transport (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    {l : TrueZero} (hβ : rZeroRadialPosition l.1 < 1 / 2) (hT : GrammarTransportAtEvent (canonicalZero 1) l) : False :=
  low_arrival_impossible_of_localRaccord h₁ hβ ((grammarTransportAtEvent_iff_localRaccord _ l).mp hT)

theorem grammarTransportAtEvent_of_onLine (z₁ l : TrueZero) (hl : rZeroRadialPosition l.1 = 1 / 2) :
    GrammarTransportAtEvent z₁ l := (grammarTransportAtEvent_iff_onLine z₁ l).mpr hl

theorem grammarTransportAtEvent_of_riemannHypothesis (z₁ l : TrueZero) (hRH : RiemannHypothesis) :
    GrammarTransportAtEvent z₁ l :=
  grammarTransportAtEvent_of_onLine z₁ l (thm_zeroRadialPosition_half_of_riemannHypothesis hRH l.1)

/-- **Ce que le régime dominé ne fournit pas** : sous un demi, la loi entre deux événements de la MÊME cellule tient
(fréquence, rencontres et besoin tous compatibles) ; seule la traversée d'un contact porte la partie réelle. -/
theorem low_arrival_transport_within_cell (l : TrueZero) (hβ : rZeroRadialPosition l.1 < 1 / 2) {q q' : ℝ}
    (hq : 0 < q) (hq' : 0 < q') :
    (GrammarTransport l q q' ↔ memberStage l q' = memberStage l q) := by
  rw [grammarTransport_iff l hq hq']
  exact ⟨fun h => h.resolve_right (by intro h'; linarith), Or.inl⟩

#print axioms grammarTransport_iff
#print axioms grammarTransportAtEvent_iff_onLine
#print axioms low_arrival_impossible_of_transport
#print axioms low_arrival_transport_within_cell

/-! ## 5. Entrelacement : les contacts de l'arrivée sous ceux de la Tour du zéro initial (auteur, même jour)

Rappel de l'auteur : « les contacts doivent être entrelacés (inférieurs à ceux de la Tour du zéro initial), c'est compilé ».
Objet compilé `WindingNested z₁ l` : à tout indice `k ≥ 1`, `C_k(l) < C_k(z₁)`. Ce qui est compilé et ce qui ne l'est pas :
ON au-dessus du premier zéro, l'entrelacement tient (`interlacing_of_onLine`) ; pour toute position radiale, à l'infini
(`windingNestedAtInfinity_of_precedes`) ; à tout `k ≥ 1`, il équivaut à une borne du facteur radial par le décalage de
hauteur au premier indice (`interlacing_iff_factor_bound`) ; dès que la fenêtre radiale `1/(2T_l²)` est sous ce décalage,
il tient pour TOUTE arrivée sous un demi (`interlacing_blind_of_window`). -/

/-- Le décalage de hauteur est le plus petit, en valeur absolue, au premier indice. -/
theorem neg_lineHeightShift_ge_one {T₁ T : ℝ} (hT₁ : 0 < T₁) (hT : T₁ < T) {k : ℤ} (hk : 1 ≤ k) :
    -lineHeightShift T₁ T 1 ≤ -lineHeightShift T₁ T k := by
  rcases eq_or_lt_of_le hk with h | h
  · rw [← h]
  · linarith [lineHeightShift_strictAnti_index hT₁ hT h]

/-- **Entrelacement ⟺ borne du facteur radial au premier indice** (premier zéro sur la ligne, arrivée plus haute). -/
theorem interlacing_iff_factor_bound (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) (l : TrueZero)
    (hT : rZeroHeight (canonicalZero 1).1 < rZeroHeight l.1) :
    WindingNested (canonicalZero 1) l ↔
      Real.log (radialFactor l) < -lineHeightShift (rZeroHeight (canonicalZero 1).1) (rZeroHeight l.1) 1 := by
  have hT₁ : 0 < rZeroHeight (canonicalZero 1).1 := (canonicalZero 1).2
  constructor
  · intro h
    exact (contact_lt_iff_factor l (canonicalZero 1) h₁ 1).mp (h 1 le_rfl)
  · intro h k hk
    exact (contact_lt_iff_factor l (canonicalZero 1) h₁ k).mpr
      (lt_of_lt_of_le h (neg_lineHeightShift_ge_one hT₁ hT hk))

/-- **Une arrivée ON au-dessus du premier zéro est entrelacée.** -/
theorem interlacing_of_onLine (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) (l : TrueZero)
    (hT : rZeroHeight (canonicalZero 1).1 < rZeroHeight l.1) (hl : rZeroRadialPosition l.1 = 1 / 2) :
    WindingNested (canonicalZero 1) l := by
  rw [interlacing_iff_factor_bound h₁ l hT, (radialFactor_eq_one_iff l).mpr hl, Real.log_one]
  have hT₁ : 0 < rZeroHeight (canonicalZero 1).1 := (canonicalZero 1).2
  have hneg : lineHeightShift (rZeroHeight (canonicalZero 1).1) (rZeroHeight l.1) 1 < 0 :=
    lineHeightShift_neg_of_one_le hT₁ hT le_rfl
  linarith

/-- **Aveuglement de l'entrelacement dans la fenêtre** : si `1/(2T_l²)` ne dépasse pas le décalage de hauteur au premier
indice, toute arrivée sous un demi est entrelacée dans la Tour du zéro initial, quelle que soit sa partie réelle. -/
theorem interlacing_blind_of_window (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) (l : TrueZero)
    (hT : rZeroHeight (canonicalZero 1).1 < rZeroHeight l.1) (hlow : rZeroRadialPosition l.1 ≤ 1 / 2)
    (hwin : 1 / (2 * rZeroHeight l.1 ^ 2) ≤
      -lineHeightShift (rZeroHeight (canonicalZero 1).1) (rZeroHeight l.1) 1) :
    WindingNested (canonicalZero 1) l := by
  rw [interlacing_iff_factor_bound h₁ l hT]
  have hb := (log_radialFactor_bounds_of_low l hlow).2
  have hβ := thm_zeroRadialPosition_positive l.1
  have hT2 : 0 < rZeroHeight l.1 ^ 2 := by have : 0 < rZeroHeight l.1 := l.2; positivity
  have : (1 / 2 - rZeroRadialPosition l.1) / rZeroHeight l.1 ^ 2 < 1 / (2 * rZeroHeight l.1 ^ 2) := by
    rw [div_lt_div_iff₀ hT2 (by positivity)]
    nlinarith
  linarith

/-- **Loi de transport entrelacée** : la loi de transport au premier événement de dépassement ET l'entrelacement des
contacts de l'arrivée sous ceux de la Tour du zéro initial dès que l'arrivée est plus haute que lui (le passage du conjugué
du premier zéro au premier zéro est vertical : l'entrelacement d'une Tour avec elle-même n'est pas demandé). -/
def GrammarTransportNested (z₁ l : TrueZero) : Prop :=
  GrammarTransportAtEvent z₁ l ∧ (rZeroHeight z₁.1 < rZeroHeight l.1 → WindingNested z₁ l)

/-- **Portée** : au-dessus du premier zéro, la loi entrelacée ⟺ `β_l = 1/2` ; l'entrelacement n'ajoute rien au cas ON et
ne ferme pas seul le cas bas. -/
theorem grammarTransportNested_iff_onLine (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) (l : TrueZero) :
    GrammarTransportNested (canonicalZero 1) l ↔ rZeroRadialPosition l.1 = 1 / 2 := by
  constructor
  · intro h; exact (grammarTransportAtEvent_iff_onLine _ l).mp h.1
  · intro hl
    exact ⟨grammarTransportAtEvent_of_onLine _ l hl, fun hT => interlacing_of_onLine h₁ l hT hl⟩

theorem low_arrival_impossible_of_nested_transport (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    {l : TrueZero} (hβ : rZeroRadialPosition l.1 < 1 / 2) (hT : GrammarTransportNested (canonicalZero 1) l) : False :=
  low_arrival_impossible_of_transport h₁ hβ hT.1

#print axioms interlacing_iff_factor_bound
#print axioms interlacing_of_onLine
#print axioms interlacing_blind_of_window
#print axioms grammarTransportNested_iff_onLine

/-! ## 6. Condition UNIQUE, architecture Astra (auteur, 2026-10-19, seizième message)

La loi à cinq conditions (sections 1 à 5) mélangeait des faits déjà déterminés par les Tours (fréquence, rencontres,
entrelacement) et la propriété à démontrer. Une seule condition de compatibilité entre la grammaire première et les
contacts authentiques : entre deux rencontres authentiques consécutives de la Tour engagée (celles qui encadrent le premier
événement de dépassement), le rayon normalisé de la Tour d'arrivée ne dérive pas. La contradiction géométrique est
démontrée séparément : sous un demi, le rayon décroît strictement d'une rencontre à la suivante
(`low_radius_decreases_between_contacts`, OnCrossReadings §6). Les cinq anciennes conditions restent compilées, aucune
n'est plus une prémisse. -/

/-- **Aucune dérive du rayon normalisé de `l` entre les rencontres `k` et `k + 1` de la Tour engagée `e`.** -/
def NoRadiusDrift (e l : TrueZero) (k : ℤ) : Prop :=
  normalizedRadius l (contactMinusAt e (k + 1)) = normalizedRadius l (contactMinusAt e k)

/-- La condition unique ⟺ `β_l = 1/2` (`radius_step_between_contacts`, `radius_step_eq_one_iff`) : certificat. -/
theorem noRadiusDrift_iff_onLine (e l : TrueZero) (k : ℤ) :
    NoRadiusDrift e l k ↔ rZeroRadialPosition l.1 = 1 / 2 := by
  unfold NoRadiusDrift
  rw [radius_step_between_contacts]
  have hpos := normalizedRadius_pos l (contactMinusAt_positive e k)
  constructor
  · intro h
    rcases mul_left_eq_self₀.mp h with h1 | h0
    · exact (radius_step_eq_one_iff e l).mp h1
    · exact absurd h0 hpos.ne'
  · intro h
    rw [(radius_step_eq_one_iff e l).mpr h, one_mul]

/-- **Contradiction géométrique, démontrée séparément** : sous un demi, le rayon dérive (décroît strictement) entre
deux rencontres consécutives de toute Tour engagée. -/
theorem low_arrival_impossible_of_noRadiusDrift (e l : TrueZero) (hβ : rZeroRadialPosition l.1 < 1 / 2) (k : ℤ)
    (h : NoRadiusDrift e l k) : False :=
  (ne_of_lt (low_radius_decreases_between_contacts e l hβ k)) h

theorem noRadiusDrift_of_onLine (e l : TrueZero) (hl : rZeroRadialPosition l.1 = 1 / 2) (k : ℤ) :
    NoRadiusDrift e l k := (noRadiusDrift_iff_onLine e l k).mpr hl

theorem noRadiusDrift_of_riemannHypothesis (e l : TrueZero) (hRH : RiemannHypothesis) (k : ℤ) :
    NoRadiusDrift e l k :=
  noRadiusDrift_of_onLine e l (thm_zeroRadialPosition_half_of_riemannHypothesis hRH l.1) k

/-- La condition unique et la loi à cinq conditions sont la même obligation au-dessus du premier zéro. -/
theorem noRadiusDrift_iff_grammarTransportNested (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (e l : TrueZero) (k : ℤ) :
    NoRadiusDrift e l k ↔ GrammarTransportNested (canonicalZero 1) l :=
  (noRadiusDrift_iff_onLine e l k).trans (grammarTransportNested_iff_onLine h₁ l).symm

#print axioms noRadiusDrift_iff_onLine
#print axioms low_arrival_impossible_of_noRadiusDrift
#print axioms noRadiusDrift_iff_grammarTransportNested

/-! ## 7. Condition UNIQUE corrigée : aucune part radiale dans le déplacement des rencontres (auteur, 2026-10-19,
dix-septième message)

Correction de l'auteur : la §6 lisait le rayon de l'arrivée aux rencontres de la Tour ENGAGÉE, comme si une seule horloge
battait ; elle oubliait deux faits démontrés : la FRÉQUENCE AUGMENTE (pas logarithmique contracté, `arrival_frequency_rises`)
et les rencontres de l'arrivée sont ENTRELACÉES en deçà de celles de la Tour engagée par la hauteur seule
(`arrival_meetings_inward_by_height`). Ces deux faits valent pour toute position radiale. La condition unique porte désormais
sur les rencontres PROPRES de l'arrivée : le déplacement de sa rencontre d'indice `k` par rapport à la rencontre de même
indice de la Tour engagée est EXACTEMENT celui que la hausse de fréquence produit (`lineHeightShift`), sans aucune part
radiale. Abscisses brutes, aucune normalisation. Contradiction démontrée séparément : sous un demi, la part radiale est
strictement positive (`low_arrival_impossible_of_noRadialShift`). -/

/-- **Aucune part radiale** : à la rencontre propre d'indice `k`, le déplacement logarithmique de la Tour d'arrivée `l`
par rapport à la Tour engagée `e` est celui de la hausse de fréquence seule. -/
def NoRadialShift (e l : TrueZero) (k : ℤ) : Prop :=
  Real.log (contactMinusAt l k / contactMinusAt e k) = lineHeightShift (rZeroHeight e.1) (rZeroHeight l.1) k

/-- **Acquis, toute position radiale : la fréquence de l'arrivée augmente** (le pas logarithmique se contracte). -/
theorem arrival_frequency_rises (e l : TrueZero) (hT : rZeroHeight e.1 < rZeroHeight l.1) :
    towerPitch l < towerPitch e := (towerPitch_lt_iff e l).mpr hT

/-- **Acquis, toute position radiale : la hausse de fréquence entrelace les rencontres en deçà** (part de hauteur
strictement négative à tout indice `k ≥ 1`). -/
theorem arrival_meetings_inward_by_height (e l : TrueZero) (hT : rZeroHeight e.1 < rZeroHeight l.1) {k : ℤ}
    (hk : 1 ≤ k) : lineHeightShift (rZeroHeight e.1) (rZeroHeight l.1) k < 0 :=
  lineHeightShift_neg_of_one_le e.2 hT hk

/-- **Décomposition exacte du déplacement d'une rencontre propre** (départ sur la ligne) : part de hauteur (hausse de
fréquence) + part radiale de l'arrivée. -/
theorem meeting_displacement_split (e l : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2) (k : ℤ) :
    Real.log (contactMinusAt l k / contactMinusAt e k) =
      lineHeightShift (rZeroHeight e.1) (rZeroHeight l.1) k + Real.log (radialFactor l) := by
  rw [contact_log_ratio, (radialFactor_eq_one_iff e).mpr he, Real.log_one]
  ring

/-- La condition unique ⟺ `β_l = 1/2` (départ sur la ligne) : certificat. -/
theorem noRadialShift_iff_onLine (e l : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2) (k : ℤ) :
    NoRadialShift e l k ↔ rZeroRadialPosition l.1 = 1 / 2 := by
  unfold NoRadialShift
  rw [meeting_displacement_split e l he, ← radialFactor_eq_one_iff]
  constructor
  · intro h
    have h0 : Real.log (radialFactor l) = 0 := by linarith
    have := Real.exp_log (radialFactor_pos l)
    rw [h0, Real.exp_zero] at this
    exact this.symm
  · intro h
    rw [h, Real.log_one, add_zero]

/-- **Contradiction géométrique, démontrée séparément** : sous un demi, la rencontre propre de l'arrivée est déplacée au-delà
de ce que la hausse de fréquence produit (part radiale strictement positive). -/
theorem low_arrival_impossible_of_noRadialShift (e l : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2)
    (hβ : rZeroRadialPosition l.1 < 1 / 2) (k : ℤ) (h : NoRadialShift e l k) : False := by
  have hpos : 0 < Real.log (radialFactor l) :=
    Real.log_pos ((radialFactor_gt_one_iff l).mpr hβ)
  unfold NoRadialShift at h
  rw [meeting_displacement_split e l he] at h
  linarith

theorem noRadialShift_of_onLine (e l : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2)
    (hl : rZeroRadialPosition l.1 = 1 / 2) (k : ℤ) : NoRadialShift e l k :=
  (noRadialShift_iff_onLine e l he k).mpr hl

theorem noRadialShift_of_riemannHypothesis (e l : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2)
    (hRH : RiemannHypothesis) (k : ℤ) : NoRadialShift e l k :=
  noRadialShift_of_onLine e l he (thm_zeroRadialPosition_half_of_riemannHypothesis hRH l.1) k

/-- La condition corrigée et celle de la §6 sont la même obligation (départ sur la ligne). -/
theorem noRadialShift_iff_noRadiusDrift (e l : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2) (k k' : ℤ) :
    NoRadialShift e l k ↔ NoRadiusDrift e l k' :=
  (noRadialShift_iff_onLine e l he k).trans (noRadiusDrift_iff_onLine e l k').symm

#print axioms arrival_frequency_rises
#print axioms arrival_meetings_inward_by_height
#print axioms meeting_displacement_split
#print axioms noRadialShift_iff_onLine
#print axioms low_arrival_impossible_of_noRadialShift

end RHV6Fresh
