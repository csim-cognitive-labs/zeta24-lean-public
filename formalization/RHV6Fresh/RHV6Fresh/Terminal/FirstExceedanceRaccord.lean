/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.OffAmplificationAudit
import RHV6Fresh.Terminal.CellRestitution
import RHV6Fresh.Terminal.RaccordDetector

/-!
# Raccord local au premier événement de dépassement (auteur, 2026-10-19, douzième message)

Texte collé « Le point à challenger est la construction de la loi de domination » (quinze points). Points 8 à 15 :
repartir du PREMIER événement premier où le miroir dépasse le champ ; y calculer les contacts authentiques qui encadrent
le premier, leur étage, leur largeur, la fréquence ; comparer la lecture du membre ON précédent et celle de la paire OFF ;
tester séparément les deux issues géométriques (même cellule / cellule voisine) ; remplacer `hDomPrime` par un lemme
local de compatibilité entre cellules authentiques et événement premier, puis vérifier s'il contredit le certificat de
dépassement.

Objets : `firstExceedPrime z₁ l` = le plus petit premier au-delà de l'horizon exact (premier événement de dépassement) ;
étage d'un réel dans une Tour (`cellIndexAt β T q`), largeur `π/T`, fréquence `T` ; `LocalRaccord` = à cet événement, le
contact de la Tour miroir à l'étage de lecture est le contact de la Tour de ligne de même hauteur (lecture du membre ON
précédent transportée à la hauteur d'arrivée : c'est l'obligation de raccord « compatible avec le régime engagé »).

Résultats : (i) les deux issues géométriques (même cellule, cellule voisine) sont COMPILÉES pour le miroir ET pour
l'arrivée, pour TOUTE position radiale : la lecture de cellule ne discrimine pas (point 12 : aucune des deux issues
n'exclut l'arrivée OFF) ; (ii) le dépassement tient à l'événement dans les deux issues ; (iii) le raccord local en forme
de CONTACT ferme le cas bas et contredit le certificat de dépassement (domination à l'événement) ; il est vide sur ON,
impliqué par RH, et ⟺ `β_l = 1/2` : c'est la forme de contact de l'obligation, pas sa dérivation.
-/

namespace RHV6Fresh

open RHV3Lean
open scoped Classical

/-! ## 1. Le premier événement de dépassement -/

/-- Le plus petit nombre premier strictement au-delà de l'horizon exact du miroir : premier événement premier où le
dépassement est compilé. -/
noncomputable def firstExceedPrime (z₁ l : TrueZero) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (⌈mirrorHorizon z₁ l⌉₊ + 1))

theorem firstExceedPrime_spec (z₁ l : TrueZero) :
    ⌈mirrorHorizon z₁ l⌉₊ + 1 ≤ firstExceedPrime z₁ l ∧ Nat.Prime (firstExceedPrime z₁ l) :=
  Nat.find_spec (Nat.exists_infinite_primes (⌈mirrorHorizon z₁ l⌉₊ + 1))

theorem firstExceedPrime_prime (z₁ l : TrueZero) : Nat.Prime (firstExceedPrime z₁ l) :=
  (firstExceedPrime_spec z₁ l).2

/-- Minimalité : aucun premier au-delà de l'horizon ne le précède. -/
theorem firstExceedPrime_min (z₁ l : TrueZero) {p : ℕ} (hp : ⌈mirrorHorizon z₁ l⌉₊ + 1 ≤ p) (hprime : Nat.Prime p) :
    firstExceedPrime z₁ l ≤ p :=
  Nat.find_min' (Nat.exists_infinite_primes (⌈mirrorHorizon z₁ l⌉₊ + 1)) ⟨hp, hprime⟩

theorem firstExceedPrime_gt_horizon (z₁ l : TrueZero) : mirrorHorizon z₁ l < firstExceedPrime z₁ l := by
  have h1 : mirrorHorizon z₁ l ≤ ⌈mirrorHorizon z₁ l⌉₊ := Nat.le_ceil _
  have h2 : (⌈mirrorHorizon z₁ l⌉₊ : ℝ) + 1 ≤ firstExceedPrime z₁ l := by exact_mod_cast (firstExceedPrime_spec z₁ l).1
  linarith

theorem firstExceedPrime_pos (z₁ l : TrueZero) : (0 : ℝ) < firstExceedPrime z₁ l := by
  exact_mod_cast (firstExceedPrime_prime z₁ l).pos

/-- **Le certificat de dépassement à cet événement** (point 11 : conservé, non redémontré). -/
theorem exceedance_at_firstExceedPrime {z₁ l : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hβ : rZeroRadialPosition l.1 < 1 / 2) :
    firstField z₁ (firstExceedPrime z₁ l) < ‖zeroTerm (mirrorMember l) (firstExceedPrime z₁ l)‖ :=
  off_amplification_certificate h₁ hβ (firstExceedPrime_pos z₁ l) (firstExceedPrime_gt_horizon z₁ l)

/-! ## 2. Étages, largeur, fréquence : lecture de l'événement par les Tours (points 8, 9, 13) -/

/-- Étage de lecture d'un réel `q` dans la Tour de ligne de hauteur `T`. -/
noncomputable def lineStage (T q : ℝ) : ℤ := cellIndexAt (1 / 2) T q

/-- Étage de lecture de `q` dans la Tour d'un vrai zéro. -/
noncomputable def memberStage (z : TrueZero) (q : ℝ) : ℤ :=
  cellIndexAt (rZeroRadialPosition z.1) (rZeroHeight z.1) q

/-- Largeur logarithmique d'un étage de toute Tour : `π/T` (fréquence `T`), toute position radiale. -/
theorem event_stage_width (z : TrueZero) (k : ℤ) :
    Real.log (contactMinusAt z (k + 1)) - Real.log (contactMinusAt z k) = Real.pi / rZeroHeight z.1 :=
  contact_log_step z k

/-- Position de lecture de `q` dans une Tour de paramètres `(β, T)`, en étages. -/
noncomputable def stagePosition (β T q : ℝ) : ℝ := (T * Real.log q - Real.arctan (T / β)) / Real.pi

theorem cellIndexAt_eq_ceil (β T q : ℝ) : cellIndexAt β T q = ⌈stagePosition β T q⌉ - 1 := rfl

/-- **Comparaison des deux lectures** (point 9) : la différence de position entre le miroir et la Tour de ligne de même
hauteur est `(arctan 2T − arctan(T/(1 − β)))/π`, part RADIALE seule (la hauteur est commune) ; pour l'arrivée, c'est
`(arctan 2T − arctan(T/β))/π`. -/
theorem mirror_reading_difference (l : TrueZero) (q : ℝ) :
    stagePosition (1 - rZeroRadialPosition l.1) (rZeroHeight l.1) q - stagePosition (1 / 2) (rZeroHeight l.1) q =
      (Real.arctan (rZeroHeight l.1 / (1 / 2)) - Real.arctan (rZeroHeight l.1 / (1 - rZeroRadialPosition l.1))) /
        Real.pi := by
  unfold stagePosition; ring

theorem arrival_reading_difference (l : TrueZero) (q : ℝ) :
    stagePosition (rZeroRadialPosition l.1) (rZeroHeight l.1) q - stagePosition (1 / 2) (rZeroHeight l.1) q =
      (Real.arctan (rZeroHeight l.1 / (1 / 2)) - Real.arctan (rZeroHeight l.1 / rZeroRadialPosition l.1)) /
        Real.pi := by
  unfold stagePosition; ring

/-- La différence miroir − ligne est dans `[0, 1/2[` étage, pour toute arrivée `β ≤ 1/2`. -/
theorem mirror_reading_difference_mem (l : TrueZero) (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) (q : ℝ) :
    0 ≤ stagePosition (1 - rZeroRadialPosition l.1) (rZeroHeight l.1) q -
        stagePosition (1 / 2) (rZeroHeight l.1) q ∧
      stagePosition (1 - rZeroRadialPosition l.1) (rZeroHeight l.1) q -
        stagePosition (1 / 2) (rZeroHeight l.1) q < 1 / 2 := by
  rw [mirror_reading_difference]
  have hT : 0 < rZeroHeight l.1 := l.2
  have hb : 0 < rZeroRadialPosition l.1 := thm_zeroRadialPosition_positive l.1
  have h1b : 0 < 1 - rZeroRadialPosition l.1 := by linarith
  have hπ := Real.pi_pos
  constructor
  · apply div_nonneg _ hπ.le
    rw [sub_nonneg]
    apply Real.arctan_strictMono.monotone
    rw [div_le_div_iff_of_pos_left hT h1b (by norm_num : (0:ℝ) < 1 / 2)]
    linarith
  · rw [div_lt_iff₀ hπ]
    have ha := Real.arctan_lt_pi_div_two (rZeroHeight l.1 / (1 / 2))
    have hb' : 0 < Real.arctan (rZeroHeight l.1 / (1 - rZeroRadialPosition l.1)) :=
      Real.arctan_pos.mpr (div_pos hT h1b)
    linarith

/-- La différence arrivée − ligne est dans `]−1/2, 0]` étage, pour toute arrivée `β ≤ 1/2`. -/
theorem arrival_reading_difference_mem (l : TrueZero) (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) (q : ℝ) :
    -(1 / 2) < stagePosition (rZeroRadialPosition l.1) (rZeroHeight l.1) q -
        stagePosition (1 / 2) (rZeroHeight l.1) q ∧
      stagePosition (rZeroRadialPosition l.1) (rZeroHeight l.1) q -
        stagePosition (1 / 2) (rZeroHeight l.1) q ≤ 0 := by
  rw [arrival_reading_difference]
  have hT : 0 < rZeroHeight l.1 := l.2
  have hb : 0 < rZeroRadialPosition l.1 := thm_zeroRadialPosition_positive l.1
  have hπ := Real.pi_pos
  constructor
  · rw [lt_div_iff₀ hπ]
    have ha := Real.arctan_lt_pi_div_two (rZeroHeight l.1 / rZeroRadialPosition l.1)
    have hb' : 0 < Real.arctan (rZeroHeight l.1 / (1 / 2)) := Real.arctan_pos.mpr (div_pos hT (by norm_num))
    linarith
  · apply div_nonpos_of_nonpos_of_nonneg _ hπ.le
    rw [sub_nonpos]
    apply Real.arctan_strictMono.monotone
    rw [div_le_div_iff_of_pos_left hT (by norm_num : (0:ℝ) < 1 / 2) hb]
    exact hβ

/-- Lemme d'arrondi : si `0 ≤ δ < 1`, `⌈x + δ⌉ ∈ {⌈x⌉, ⌈x⌉ + 1}`. -/
theorem ceil_add_small {x δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) :
    ⌈x + δ⌉ = ⌈x⌉ ∨ ⌈x + δ⌉ = ⌈x⌉ + 1 := by
  have hlo : ⌈x⌉ ≤ ⌈x + δ⌉ := Int.ceil_le_ceil (by linarith)
  have hhi : ⌈x + δ⌉ ≤ ⌈x⌉ + 1 := by
    rw [← Int.ceil_add_one]; exact Int.ceil_le_ceil (by linarith)
  omega

/-! ## 3. Les deux issues géométriques (point 12), compilées pour toute position radiale -/

/-- **Issue géométrique du miroir** : à tout réel `q`, le miroir lit `q` dans la cellule de la Tour de ligne de même
hauteur, ou dans la cellule suivante ; pour TOUTE arrivée `β ≤ 1/2`. -/
theorem mirror_cell_same_or_next (l : TrueZero) (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) (q : ℝ) :
    memberStage (mirrorMember l) q = lineStage (rZeroHeight l.1) q ∨
      memberStage (mirrorMember l) q = lineStage (rZeroHeight l.1) q + 1 := by
  unfold memberStage lineStage
  rw [mirrorMember_ordinate, mirrorMember_radial, cellIndexAt_eq_ceil, cellIndexAt_eq_ceil]
  obtain ⟨h0, h1⟩ := mirror_reading_difference_mem l hβ q
  have key := ceil_add_small (x := stagePosition (1 / 2) (rZeroHeight l.1) q)
    (δ := stagePosition (1 - rZeroRadialPosition l.1) (rZeroHeight l.1) q -
      stagePosition (1 / 2) (rZeroHeight l.1) q) h0 (by linarith)
  rw [add_sub_cancel] at key
  rcases key with h | h
  · left; rw [h]
  · right; rw [h]; ring

/-- **Issue géométrique de l'arrivée** : même cellule que la ligne, ou la cellule précédente ; toute `β ≤ 1/2`. -/
theorem arrival_cell_same_or_previous (l : TrueZero) (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) (q : ℝ) :
    memberStage l q = lineStage (rZeroHeight l.1) q ∨
      memberStage l q = lineStage (rZeroHeight l.1) q - 1 := by
  unfold memberStage lineStage
  rw [cellIndexAt_eq_ceil, cellIndexAt_eq_ceil]
  obtain ⟨h0, h1⟩ := arrival_reading_difference_mem l hβ q
  have key := ceil_add_small (x := stagePosition (rZeroRadialPosition l.1) (rZeroHeight l.1) q)
    (δ := stagePosition (1 / 2) (rZeroHeight l.1) q -
      stagePosition (rZeroRadialPosition l.1) (rZeroHeight l.1) q) (by linarith) (by linarith)
  rw [add_sub_cancel] at key
  rcases key with h | h
  · left; rw [h]
  · right; rw [h]; ring

/-- **Aucune des deux issues n'exclut l'arrivée OFF** : à l'événement de dépassement, dans chacune des deux issues du
miroir, le dépassement tient (la lecture de cellule et l'amplitude sont indépendantes). -/
theorem both_cell_outcomes_compatible_with_exceedance {z₁ l : TrueZero}
    (h₁ : rZeroRadialPosition z₁.1 = 1 / 2) (hβ : rZeroRadialPosition l.1 < 1 / 2) :
    (memberStage (mirrorMember l) (firstExceedPrime z₁ l) = lineStage (rZeroHeight l.1) (firstExceedPrime z₁ l) ∨
      memberStage (mirrorMember l) (firstExceedPrime z₁ l) =
        lineStage (rZeroHeight l.1) (firstExceedPrime z₁ l) + 1) ∧
    firstField z₁ (firstExceedPrime z₁ l) < ‖zeroTerm (mirrorMember l) (firstExceedPrime z₁ l)‖ :=
  ⟨mirror_cell_same_or_next l hβ.le _, exceedance_at_firstExceedPrime h₁ hβ⟩

/-! ## 4. Le raccord local en forme de contact (point 15) et sa confrontation au certificat -/

/-- **Raccord local** : au premier événement de dépassement, le contact de la Tour MIROIR à l'étage de lecture de
l'événement est le contact de la Tour de ligne de même hauteur (lecture du membre ON précédent, transportée à la hauteur
d'arrivée par la fréquence seule). Aucune amplitude dans l'énoncé : étage, contact, fréquence. -/
def LocalRaccord (z₁ l : TrueZero) : Prop :=
  contactMinusAt (mirrorMember l) (lineStage (rZeroHeight l.1) (firstExceedPrime z₁ l)) =
    lineContact (rZeroHeight l.1) (lineStage (rZeroHeight l.1) (firstExceedPrime z₁ l))

/-- Le raccord local est l'arrivée en ligne : un contact de la Tour miroir égal au contact de ligne force `β_{l*} = 1/2`. -/
theorem localRaccord_iff_onLine (z₁ l : TrueZero) : LocalRaccord z₁ l ↔ rZeroRadialPosition l.1 = 1 / 2 := by
  unfold LocalRaccord
  have h := contact_eq_line_iff_onLine (mirrorMember l) (lineStage (rZeroHeight l.1) (firstExceedPrime z₁ l))
  rw [mirrorMember_ordinate, mirrorMember_radial] at h
  rw [h]; constructor <;> intro h' <;> linarith

/-- **Le raccord local contredit le certificat** : sous le raccord, le miroir est dominé par le premier zéro à
l'événement, ce que le certificat de dépassement interdit sous un demi. -/
theorem localRaccord_implies_domination_at_event (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (l : TrueZero) (hR : LocalRaccord (canonicalZero 1) l) :
    ‖zeroTerm (mirrorMember l) (firstExceedPrime (canonicalZero 1) l)‖ ≤
      firstField (canonicalZero 1) (firstExceedPrime (canonicalZero 1) l) :=
  mirror_dominated_at_primes_of_onLine h₁ l ((localRaccord_iff_onLine _ l).mp hR) _
    (firstExceedPrime_prime _ l)

theorem low_arrival_impossible_of_localRaccord (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    {l : TrueZero} (hβ : rZeroRadialPosition l.1 < 1 / 2) (hR : LocalRaccord (canonicalZero 1) l) : False :=
  absurd (localRaccord_implies_domination_at_event h₁ l hR)
    (not_le.mpr (exceedance_at_firstExceedPrime h₁ hβ))

theorem localRaccord_of_onLine (z₁ l : TrueZero) (hl : rZeroRadialPosition l.1 = 1 / 2) : LocalRaccord z₁ l :=
  (localRaccord_iff_onLine z₁ l).mpr hl

theorem localRaccord_of_riemannHypothesis (z₁ l : TrueZero) (hRH : RiemannHypothesis) : LocalRaccord z₁ l :=
  localRaccord_of_onLine z₁ l (thm_zeroRadialPosition_half_of_riemannHypothesis hRH l.1)

/-- La forme d'amplitude à un point (prémisse précédente) entraîne la forme de contact, sur toute arrivée d'un passage
qui monte (`β_l ≤ 1/2`). -/
theorem localRaccord_of_one_point (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) (l : TrueZero)
    (hβ : rZeroRadialPosition l.1 ≤ 1 / 2)
    (h : ∃ x : ℝ, mirrorHorizon (canonicalZero 1) l < x ∧
      ‖zeroTerm (mirrorMember l) x‖ ≤ firstField (canonicalZero 1) x) : LocalRaccord (canonicalZero 1) l :=
  localRaccord_of_onLine _ l ((one_point_iff_onLine h₁ l hβ).mp h)

/-- **Le raccord local ne lit pas les cellules** : la compatibilité des cellules (même cellule ou voisine) est vraie pour
toute `β ≤ 1/2`, alors que le raccord local en forme de contact est ⟺ `β = 1/2` ; la lecture de cellule ne porte pas
l'obligation (point 12, les deux issues sont ouvertes à l'OFF). -/
theorem cell_compatibility_does_not_carry_raccord (z₁ l : TrueZero) (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) :
    (memberStage (mirrorMember l) (firstExceedPrime z₁ l) = lineStage (rZeroHeight l.1) (firstExceedPrime z₁ l) ∨
      memberStage (mirrorMember l) (firstExceedPrime z₁ l) =
        lineStage (rZeroHeight l.1) (firstExceedPrime z₁ l) + 1) ∧
    (LocalRaccord z₁ l ↔ rZeroRadialPosition l.1 = 1 / 2) :=
  ⟨mirror_cell_same_or_next l hβ _, localRaccord_iff_onLine z₁ l⟩

#print axioms exceedance_at_firstExceedPrime
#print axioms mirror_cell_same_or_next
#print axioms arrival_cell_same_or_previous
#print axioms both_cell_outcomes_compatible_with_exceedance
#print axioms localRaccord_iff_onLine
#print axioms low_arrival_impossible_of_localRaccord
#print axioms localRaccord_of_one_point

end RHV6Fresh
