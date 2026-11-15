/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CellRestitution
import RHV6Fresh.Terminal.FirstGainPremise
import RHV6Fresh.Grammar.ExpectedMinimum
import RHV6Fresh.Voyage.Progression

/-!
# Rigidité des transitions au raccord entre Tours (auteur, 2026-10-12)

Notation historique : états `1` (`p ≡ 1 mod 6`) et `5` (`p ≡ 5 mod 6`) ; transitions `t11` (classe 0), `t15` (classe 4),
`t51` (classe 2), `t55` (classe 0). Successeurs autorisés : `t11 → t11 | t15`, `t15 → t55 | t51`, `t51 → t11 | t15`,
`t55 → t55 | t51`.

Démontré (axiomes standard), INDÉPENDAMMENT du statut ON :
1. Transition d'un couple d'entiers à bon état, source, but, classe = `gapClass6` (`transitionOf_cls`).
2. RACCORD EXACT : trois entiers ordonnés à bon état, l'état d'arrivée de la première transition est l'état de départ de la
   seconde (`raccord_exact`) ; classification des compositions autorisées (`allowedNext_iff`).
3. Après suppression des maintiens, les changements alternent : entre deux `t15` il y a un `t51`, et réciproquement
   (`exists_t51_between`, `exists_t15_between`). La classe ne détermine pas la magnitude (`magnitude_not_determined`).
4. Événement `r` = `(p_r, p_{r+1})`, transition, magnitude ; `g_r = 6 m_r + cls` ; raccord `r → r + 1` sur les premiers
   (`event_raccord`).
5. Correspondance membres / occurrences / premier partagé (index vérifié : `Occ(z) = p_n`, `p_min(z) = p_{n+1}`,
   `n = nZeroSourceIndex z`) : sur un passage, événement de l'arrivée = événement suivant, extrémité commune = `M`
   (`passage_event_raccord`), toute position radiale.
6. Lecture géométrique d'un événement par une Tour : indices de cellule des deux extrémités (`eventCellReading`). Sous
   `β ≤ 1/2`, chaque extrémité est lue dans la cellule de ligne ou la précédente (`eventCellReading_shift`). La transition
   lue sur les extrémités est celle des premiers, pour TOUTE Tour (`reading_transition_radial_blind`).
7. Liaison recherchée (TDD) : « une première rupture radiale force une violation de la rigidité dans la lecture
   authentique ». RÉFUTÉE dans cette lecture : sous `β_l < 1/2`, le raccord, l'extrémité commune et le pas d'index tiennent
   (`rupture_keeps_transition_rigidity`). La rigidité est une propriété des premiers, la lecture authentique conserve les
   mêmes extrémités ; aucune violation n'en découle.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Les quatre transitions -/

/-- Les quatre transitions, notation historique. -/
inductive PrimeTransition | t11 | t15 | t51 | t55
  deriving DecidableEq, Repr

namespace PrimeTransition

/-- État de départ (`true` = état `1`). -/
def src : PrimeTransition → Bool | t11 => true | t15 => true | t51 => false | t55 => false
/-- État d'arrivée (`true` = état `1`). -/
def dst : PrimeTransition → Bool | t11 => true | t15 => false | t51 => true | t55 => false
/-- Classe de l'écart modulo 6. -/
def cls : PrimeTransition → ℕ | t11 => 0 | t15 => 4 | t51 => 2 | t55 => 0

/-- Composition autorisée : l'arrivée de la première est le départ de la seconde. -/
def AllowedNext (t t' : PrimeTransition) : Prop := t.dst = t'.src

instance (t t' : PrimeTransition) : Decidable (AllowedNext t t') := by unfold AllowedNext; infer_instance

/-- **Classification des successeurs autorisés** (table historique). -/
theorem allowedNext_iff (t t' : PrimeTransition) :
    AllowedNext t t' ↔
      (t = t11 ∧ (t' = t11 ∨ t' = t15)) ∨ (t = t15 ∧ (t' = t55 ∨ t' = t51)) ∨
      (t = t51 ∧ (t' = t11 ∨ t' = t15)) ∨ (t = t55 ∧ (t' = t55 ∨ t' = t51)) := by
  cases t <;> cases t' <;> decide

/-- Une transition est un maintien ⟺ classe `0`. -/
theorem cls_eq_zero_iff (t : PrimeTransition) : t.cls = 0 ↔ t.src = t.dst := by cases t <;> decide

end PrimeTransition

open PrimeTransition

/-- Transition d'un couple d'entiers. -/
def pairTransition (m n : ℕ) : PrimeTransition :=
  if m % 6 = 1 then (if n % 6 = 1 then t11 else t15) else (if n % 6 = 1 then t51 else t55)

theorem transitionOf_src (m n : ℕ) : (pairTransition m n).src = state6 m := by
  unfold pairTransition state6; split_ifs <;> simp_all [PrimeTransition.src]

theorem transitionOf_dst (m n : ℕ) : (pairTransition m n).dst = state6 n := by
  unfold pairTransition state6; split_ifs <;> simp_all [PrimeTransition.dst]

/-- La classe de la transition est la classe d'écart modulo 6. -/
theorem transitionOf_cls {m n : ℕ} (hm : GoodMod6 m) (hn : GoodMod6 n) (h : m ≤ n) :
    (pairTransition m n).cls = gapClass6 m n := by
  unfold GoodMod6 at hm hn
  unfold pairTransition gapClass6
  rcases hm with hm | hm <;> rcases hn with hn | hn <;> simp [hm, hn, PrimeTransition.cls] <;> omega

/-- **Raccord exact** : pour trois entiers, l'arrivée de la première transition est le départ de la seconde (le
premier intermédiaire est partagé, son état est unique). -/
theorem raccord_exact (m n r : ℕ) : AllowedNext (pairTransition m n) (pairTransition n r) := by
  unfold AllowedNext; rw [transitionOf_dst, transitionOf_src]

/-! ## 2. Mots grammaticaux : alternance après suppression des maintiens -/

/-- Mot valide de longueur `k + 1` : compositions autorisées sur `[i, i + k]`. -/
def ValidWord (w : ℕ → PrimeTransition) (i j : ℕ) : Prop := ∀ l, i ≤ l → l < j → AllowedNext (w l) (w (l + 1))

/-- Si l'état est `5` après `w i` et `1` avant `w j`, un `t51` est intercalé strictement entre. -/
theorem exists_t51_of_states {w : ℕ → PrimeTransition} {i : ℕ} :
    ∀ j, i < j → ValidWord w i j → (w i).dst = false → (w j).src = true → ∃ l, i < l ∧ l < j ∧ w l = t51 := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro hij hW hi hj
    have hstep : (w j).dst = (w (j + 1)).src := hW j (by omega) (by omega)
    rcases Nat.lt_or_ge i j with hlt | hge
    · have hdj : (w j).dst = true := hstep.trans hj
      by_cases hs : (w j).src = true
      · obtain ⟨l, h1, h2, h3⟩ := ih hlt (fun l h1 h2 => hW l h1 (by omega)) hi hs
        exact ⟨l, h1, by omega, h3⟩
      · refine ⟨j, hlt, by omega, ?_⟩
        have hs' : (w j).src = false := by simpa using hs
        cases hwj : w j <;> simp_all [PrimeTransition.src, PrimeTransition.dst]
    · have : i = j := by omega
      subst this
      rw [hstep] at hi; rw [hi] at hj; exact absurd hj (by decide)

/-- Symétrique : état `1` après `w i`, `5` avant `w j` ⟹ un `t15` est intercalé. -/
theorem exists_t15_of_states {w : ℕ → PrimeTransition} {i : ℕ} :
    ∀ j, i < j → ValidWord w i j → (w i).dst = true → (w j).src = false → ∃ l, i < l ∧ l < j ∧ w l = t15 := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro hij hW hi hj
    have hstep : (w j).dst = (w (j + 1)).src := hW j (by omega) (by omega)
    rcases Nat.lt_or_ge i j with hlt | hge
    · have hdj : (w j).dst = false := hstep.trans hj
      by_cases hs : (w j).src = false
      · obtain ⟨l, h1, h2, h3⟩ := ih hlt (fun l h1 h2 => hW l h1 (by omega)) hi hs
        exact ⟨l, h1, by omega, h3⟩
      · refine ⟨j, hlt, by omega, ?_⟩
        have hs' : (w j).src = true := by simpa using hs
        cases hwj : w j <;> simp_all [PrimeTransition.src, PrimeTransition.dst]
    · have : i = j := by omega
      subst this
      rw [hstep] at hi; rw [hi] at hj; exact absurd hj (by decide)

/-- **Alternance** : entre deux `t15` d'un mot valide, un `t51`. -/
theorem exists_t51_between {w : ℕ → PrimeTransition} {i j : ℕ} (hij : i < j) (hW : ValidWord w i j)
    (hi : w i = t15) (hj : w j = t15) : ∃ l, i < l ∧ l < j ∧ w l = t51 :=
  exists_t51_of_states j hij hW (by rw [hi]; rfl) (by rw [hj]; rfl)

/-- **Alternance** : entre deux `t51` d'un mot valide, un `t15`. -/
theorem exists_t15_between {w : ℕ → PrimeTransition} {i j : ℕ} (hij : i < j) (hW : ValidWord w i j)
    (hi : w i = t51) (hj : w j = t51) : ∃ l, i < l ∧ l < j ∧ w l = t15 :=
  exists_t15_of_states j hij hW (by rw [hi]; rfl) (by rw [hj]; rfl)

/-- **La classe ne détermine pas la magnitude** : `29 → 31` et `113 → 127` sont deux `t51`, de magnitudes `0` et `2`. -/
theorem magnitude_not_determined :
    pairTransition 29 31 = pairTransition 113 127 ∧ (31 - 29) / 6 ≠ (127 - 113) / 6 := by decide

/-! ## 3. Événements premiers -/

/-- Transition de l'événement `r` : `(p_r, p_{r+1})`. -/
noncomputable def eventTransition (r : ℕ) : PrimeTransition := pairTransition (fnPrimeAtRank r) (fnPrimeSuccessor r)

/-- **Raccord des événements consécutifs** : l'extrémité d'arrivée de l'événement `r` est l'extrémité de départ de
l'événement `r + 1` (`p_{r+1}`), donc leurs transitions se composent. -/
theorem event_raccord (r : ℕ) : AllowedNext (eventTransition r) (eventTransition (r + 1)) := by
  unfold eventTransition fnPrimeSuccessor
  exact raccord_exact _ _ _

/-- Le mot de tous les événements est valide sur tout intervalle. -/
theorem event_word_valid (i j : ℕ) : ValidWord eventTransition i j := fun l _ _ => event_raccord l

/-- Classe et magnitude : `g_r = 6 m_r + cls(t_r)` dès `p_r > 3`. -/
theorem event_gap_eq (r : ℕ) (h3 : 3 < fnPrimeAtRank r) :
    nPrimeGap r = 6 * gapMagnitude r + (eventTransition r).cls := by
  have hp := prime_goodMod6 _ (thm_primeAtRank_isPrime r) h3
  have hq := prime_goodMod6 _ (thm_primeAtRank_isPrime (r + 1)) (lt_trans h3 (thm_primeAtRank_lt_successor r))
  rw [primeGap_eq_magnitude_class, eventTransition,
    transitionOf_cls (n := fnPrimeSuccessor r) hp hq (thm_primeAtRank_lt_successor r).le]
  rfl

/-! ## 4. Correspondance membres / occurrences / premier partagé -/

/-- Événement porté par un membre : son index source `n`, `(Occ z, p_min z) = (p_n, p_{n+1})`. -/
noncomputable def memberEvent (z : TrueZero) : ℕ := nZeroSourceIndex z.1

theorem memberEvent_endpoints (z : TrueZero) :
    occurrence z = fnPrimeAtRank (memberEvent z) ∧ expectedMinimumPrime z = fnPrimeSuccessor (memberEvent z) :=
  ⟨occurrence_eq_primeAtRank z, rfl⟩

/-- **Raccord sur un passage** (toute position radiale) : l'événement de l'arrivée est l'événement suivant ; l'extrémité
commune est le premier partagé `M = p_min(e) = Occ(l)` ; les transitions se composent. -/
theorem passage_event_raccord (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    memberEvent ⟨p.zLaterMember, hL⟩ = memberEvent ⟨p.zEarlierMember, hE⟩ + 1 ∧
      expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ = occurrence ⟨p.zLaterMember, hL⟩ ∧
      AllowedNext (eventTransition (memberEvent ⟨p.zEarlierMember, hE⟩))
        (eventTransition (memberEvent ⟨p.zLaterMember, hL⟩)) := by
  have hidx : memberEvent ⟨p.zLaterMember, hL⟩ = memberEvent ⟨p.zEarlierMember, hE⟩ + 1 :=
    eventIndex_succ_of_passage p hE
  refine ⟨hidx, expectedMinimumPrime_eq_laterOccurrence p hE hL, ?_⟩
  rw [hidx]; exact event_raccord _

/-! ## 5. Lecture géométrique d'un événement par une Tour -/

/-- Lecture d'un événement par la Tour de `z` : indices de cellule des deux extrémités. -/
noncomputable def eventCellReading (z : TrueZero) (r : ℕ) : ℤ × ℤ :=
  (pivotCoordinate z (fnPrimeAtRank r), pivotCoordinate z (fnPrimeSuccessor r))

/-- Transition lue sur les extrémités lues : ce sont les mêmes premiers, la transition ne dépend d'aucune Tour. -/
noncomputable def readTransition (_z : TrueZero) (r : ℕ) : PrimeTransition := eventTransition r

/-- **Lecture aveugle au radial** : deux Tours quelconques lisent la même transition. -/
theorem reading_transition_radial_blind (z z' : TrueZero) (r : ℕ) : readTransition z r = readTransition z' r := rfl

/-- **Conséquence d'un facteur radial `≥ 1`** sur la lecture : sous `β ≤ 1/2`, chaque extrémité est lue dans la cellule
de ligne ou dans la précédente ; l'écart des deux indices change d'au plus un. -/
theorem eventCellReading_shift (z : TrueZero) (hβ : rZeroRadialPosition z.1 ≤ 1 / 2) (r : ℕ) :
    let a := ⌈linePosition (rZeroHeight z.1) (fnPrimeAtRank r)⌉ - 1
    let b := ⌈linePosition (rZeroHeight z.1) (fnPrimeSuccessor r)⌉ - 1
    ((eventCellReading z r).1 = a ∨ (eventCellReading z r).1 = a - 1) ∧
      ((eventCellReading z r).2 = b ∨ (eventCellReading z r).2 = b - 1) ∧
      |((eventCellReading z r).2 - (eventCellReading z r).1) - (b - a)| ≤ 1 := by
  intro a b
  have h1 := arrival_cell_shift z hβ (fnPrimeAtRank r)
  have h2 := arrival_cell_shift z hβ (fnPrimeSuccessor r)
  have e1 : (eventCellReading z r).1 = pivotCoordinate z (fnPrimeAtRank r) := rfl
  have e2 : (eventCellReading z r).2 = pivotCoordinate z (fnPrimeSuccessor r) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; rcases h1 with h | h
    · left; rw [h]
    · right; rw [h]; ring
  · rw [e2]; rcases h2 with h | h
    · left; rw [h]
    · right; rw [h]; ring
  · rw [e1, e2, abs_le]
    rcases h1 with h | h <;> rcases h2 with h' | h' <;> rw [h, h'] <;> constructor <;> linarith

/-! ## 6. Liaison recherchée : réfutée dans la lecture authentique -/

/-- **Une première rupture radiale ne viole pas la rigidité dans la lecture authentique.** Sur tout passage dont
l'arrivée est sous la ligne : pas d'index exactement un (aucun événement omis ni répété), extrémité commune = premier
partagé, transitions composables, transition lue identique à la référence, extrémités lues décalées d'au plus une cellule.
La rigidité des transitions est une propriété des premiers ; la lecture authentique conserve les mêmes extrémités. -/
theorem rupture_keeps_transition_rigidity (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hβ : rZeroRadialPosition p.zLaterMember ≤ 1 / 2)
    (zRef : TrueZero) :
    memberEvent ⟨p.zLaterMember, hL⟩ = memberEvent ⟨p.zEarlierMember, hE⟩ + 1 ∧
      expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ = occurrence ⟨p.zLaterMember, hL⟩ ∧
      AllowedNext (readTransition ⟨p.zEarlierMember, hE⟩ (memberEvent ⟨p.zEarlierMember, hE⟩))
        (readTransition ⟨p.zLaterMember, hL⟩ (memberEvent ⟨p.zLaterMember, hL⟩)) ∧
      readTransition ⟨p.zLaterMember, hL⟩ (memberEvent ⟨p.zLaterMember, hL⟩) =
        readTransition zRef (memberEvent ⟨p.zLaterMember, hL⟩) ∧
      |((eventCellReading ⟨p.zLaterMember, hL⟩ (memberEvent ⟨p.zLaterMember, hL⟩)).2 -
          (eventCellReading ⟨p.zLaterMember, hL⟩ (memberEvent ⟨p.zLaterMember, hL⟩)).1) -
        ((⌈linePosition (rZeroHeight p.zLaterMember) (fnPrimeSuccessor (memberEvent ⟨p.zLaterMember, hL⟩))⌉ - 1) -
          (⌈linePosition (rZeroHeight p.zLaterMember) (fnPrimeAtRank (memberEvent ⟨p.zLaterMember, hL⟩))⌉ - 1))| ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := passage_event_raccord p hE hL
  exact ⟨h1, h2, h3, rfl, (eventCellReading_shift ⟨p.zLaterMember, hL⟩ hβ _).2.2⟩

#print axioms allowedNext_iff
#print axioms exists_t51_between
#print axioms event_gap_eq
#print axioms rupture_keeps_transition_rigidity

end RHV6Fresh
