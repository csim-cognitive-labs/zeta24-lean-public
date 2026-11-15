/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TransitionRigidity
import RHV6Fresh.Terminal.GrammarDwellDecomposition
import RHV6Fresh.Terminal.GrammarDrift
import RHV6Fresh.Terminal.ContactRealValue
import RHV6Fresh.Terminal.PrimeGapReconstruction

/-!
# RHV6Fresh — Terminal/GrammarContactStability : la grammaire des écarts premiers lue depuis les
Tours, et ce que son équilibre transporte (ou non) aux contacts (§19.41, 2026-11-04)

Module isolé (non ajouté à `RHV6Fresh.lean`). Aucune hypothèse, aucun axiome, aucune prémisse
équivalente à RH, aucun zéro OFF, aucune contradiction cherchée. Directive de l'auteur (E427) :
**reconstruire la grammaire depuis les Tours avant toute contrainte**, puis dire exactement ce que
l'équilibre grammatical transporte vers les contacts.

## 1. Orientation des transitions (grammaire de référence, réutilisée)
`PrimeTransition.orientation` : `+1` pour `t15` (état 1 → état 5), `−1` pour `t51`, `0` pour les
deux maintiens. `orientation_eq_ind` : orientation = indicatrice de l'état de départ moins celle de
l'état d'arrivée (c'est ce qui télescope). `orientation_eq_zero_iff` : nulle ⟺ classe nulle.

## 2. Bilan orienté d'un mot valide
`orientedBalance w i n` = somme des orientations de `n` transitions à partir de l'indice `i`.
* `orientedBalance_telescopes` : sur un mot valide, le bilan vaut l'indicatrice du premier état
  moins celle du dernier (**télescopage exact**) ;
* `orientedBalance_abs_le_one` : **confinement** dans `[−1, 1]`, quel que soit le nombre de
  séjours ;
* `orientedBalance_eq_zero_of_same_state`, `crossings_cancel_15_51`, `crossings_cancel_51_15` :
  **retour exact** après deux croisements inverses, indépendamment des séjours intermédiaires ;
* `orientedBalance_dwell` : un segment de maintiens est **neutre** ;
* `confinement_not_dwell_equality` : le confinement de l'orientation **n'affirme rien** sur
  l'égalité des nombres de séjours (mot valide de bilan nul avec deux `t11` et aucun `t55`).

## 3. Dénombrement
`validWordEquivPath` : les mots valides de `n + 1` transitions sont exactement les chemins
d'états de longueur `n + 2` ; `card_validWords_twelve` : **8 192** mots valides de douze
transitions (= 2¹³).
Aucune autre propriété n'est attribuée à ce dénombrement.

## 4. Grammaire des événements premiers (référence arithmétique)
`eventOrientation`, `eventBalance` sur `eventTransition` (TransitionRigidity) ;
`eventBalance_telescopes`, `eventBalance_abs_le_one`, `eventBalance_return` ;
`eventOrientation_of_gap` : orientation ⟺ résidu de l'écart modulo 6 (`4`, `2`, `0`).

## 5. Niveau 1 — la grammaire reconstruite depuis les Tours
Le prédicat `ReconstructedPrimeAbove` (PrimeGapReconstruction) est défini du seul côté spectral :
primitive spectrale = fond + canal des zéros (collectif des Tours), dont chaque pas est la limite
des accumulations par contacts (`reconstructedPsi_eq_limit_contact_accumulation`). Ici :
* `reconstructedState`, `reconstructedTransition`, `reconstructedBalance` : états, transitions et
  bilan **définis sur la suite reconstruite** (aucun premier injecté) ;
* `reconstructedPrimeAtRank_prime`, `reconstructedState_goodMod6` : chaque terme reconstruit est
  premier `≥ 3`, et dès le rang `1` dans l'un des **deux états** ;
* `reconstructedTransition_cls` : la classe reconstruite est l'écart reconstruit modulo 6 ;
* `reconstructedWord_valid` : les transitions reconstruites se **composent** (raccord exact) ;
* `reconstructedBalance_telescopes`, `reconstructedBalance_abs_le_one`,
  `reconstructedBalance_return` : télescopage, confinement et retour exact **sur la suite
  reconstruite** ;
* `reconstructedTransition_eq_actual` : validation — la transition reconstruite de rang `k` est la
  transition des vrais premiers `≥ 3` de rangs `k, k+1`.
Portée honnête : la reconstruction est celle de la formule explicite lissée compilée (limite en
hauteur de troncature, somme collective des Tours) ; les contacts y entrent comme découpage de
l'accumulation (identité `contact_accumulation_eq_endpoint_difference`), pas comme information
supplémentaire.

## 6. Niveau 2 — ce que l'équilibre transporte aux contacts
* `orientation_eq_half_sgn_sub`, `weightedBalance_abs_le`, `eventWeightedBalance_abs_le`,
  `contact_weighted_balance_abs_le` : tout bilan orienté **pondéré par des valeurs réelles aux
  contacts** est borné par la variation totale des poids (somme d'Abel) ; énoncé pour tout `(β, T)`
  — c'est le **test de séparation** : la borne ne lit ni les zéros ni la position radiale ;
* `logRatio_not_determined_by_transition`, `amplitude_ratio_not_determined_by_transition` : la
  transition ne détermine ni le rapport logarithmique des deux premiers ni le rapport des
  amplitudes `x^β` (même transition `t51` pour `29 → 31` et `113 → 127`) : **le lemme manquant**
  (une grandeur géométrique des contacts dont la variation serait fonction de la seule orientation)
  ne peut pas être une fonction de l'amplitude ni de la phase ;
* `segment_drift`, `return_drift_eq_one_iff` : sur un segment de bilan nul (retour exact), la
  dérive d'amplitude relative vaut `(p_fin/p_début)^(β − ½)` et **est neutre si et seulement si la
  Tour est sur la ligne** : la « correction des dérives » géométrique ⟺ `β = ½` (caractérisation,
  jamais posée).
-/

namespace RHV6Fresh

open PrimeTransition Finset RHV3Lean

/-! ## 1. Orientation -/

/-- Orientation d'une transition : `+1` (1 → 5), `−1` (5 → 1), `0` (maintien). -/
def PrimeTransition.orientation : PrimeTransition → ℤ
  | t11 => 0 | t15 => 1 | t51 => -1 | t55 => 0

theorem orientation_eq_ind (t : PrimeTransition) : t.orientation = ind1 t.src - ind1 t.dst := by
  cases t <;> decide

theorem orientation_eq_zero_iff (t : PrimeTransition) : t.orientation = 0 ↔ t.cls = 0 := by
  cases t <;> decide

theorem orientation_mem (t : PrimeTransition) :
    t.orientation = 0 ∨ t.orientation = 1 ∨ t.orientation = -1 := by
  cases t <;> decide

theorem orientation_eq_one_iff (t : PrimeTransition) : t.orientation = 1 ↔ t = t15 := by
  cases t <;> decide

theorem orientation_eq_neg_one_iff (t : PrimeTransition) : t.orientation = -1 ↔ t = t51 := by
  cases t <;> decide

/-! ## 2. Bilan orienté d'un mot valide -/

/-- Bilan orienté de `n` transitions à partir de l'indice `i`. -/
def orientedBalance (w : ℕ → PrimeTransition) (i n : ℕ) : ℤ :=
  ∑ l ∈ range n, (w (i + l)).orientation

theorem validWord_of_le {w : ℕ → PrimeTransition} {i j j' : ℕ} (h : ValidWord w i j')
    (hj : j ≤ j') :
    ValidWord w i j :=
  fun l hil hlj => h l hil (lt_of_lt_of_le hlj hj)

/-- **Télescopage exact** : bilan = indicatrice du premier état − indicatrice du dernier. -/
theorem orientedBalance_telescopes (w : ℕ → PrimeTransition) (i n : ℕ)
    (hW : ValidWord w i (i + n)) :
    orientedBalance w i (n + 1) = ind1 (w i).src - ind1 (w (i + n)).dst := by
  induction n with
  | zero => simp [orientedBalance, orientation_eq_ind]
  | succ n ih =>
    have hW' : ValidWord w i (i + n) := validWord_of_le hW (by omega)
    have hlink : (w (i + n)).dst = (w (i + n + 1)).src := hW (i + n) (by omega) (by omega)
    simp only [orientedBalance] at ih ⊢
    rw [sum_range_succ, ih hW', orientation_eq_ind, ← add_assoc, hlink]
    ring

/-- **Confinement** du bilan orienté dans `[−1, 1]`. -/
theorem orientedBalance_abs_le_one (w : ℕ → PrimeTransition) (i n : ℕ)
    (hW : ValidWord w i (i + n)) : |orientedBalance w i (n + 1)| ≤ 1 := by
  rw [orientedBalance_telescopes w i n hW]
  unfold ind1
  split_ifs <;> simp

/-- **Retour exact** : même état au départ et à l'arrivée ⟹ bilan nul, quels que soient les
séjours. -/
theorem orientedBalance_eq_zero_of_same_state (w : ℕ → PrimeTransition) (i n : ℕ)
    (hW : ValidWord w i (i + n)) (h : (w i).src = (w (i + n)).dst) :
    orientedBalance w i (n + 1) = 0 := by
  rw [orientedBalance_telescopes w i n hW, h, sub_self]

/-- Deux croisements inverses `t15 … t51` s'annulent exactement. -/
theorem crossings_cancel_15_51 (w : ℕ → PrimeTransition) (i n : ℕ) (hW : ValidWord w i (i + n))
    (h1 : w i = t15) (h2 : w (i + n) = t51) : orientedBalance w i (n + 1) = 0 :=
  orientedBalance_eq_zero_of_same_state w i n hW (by rw [h1, h2]; rfl)

/-- Deux croisements inverses `t51 … t15` s'annulent exactement. -/
theorem crossings_cancel_51_15 (w : ℕ → PrimeTransition) (i n : ℕ) (hW : ValidWord w i (i + n))
    (h1 : w i = t51) (h2 : w (i + n) = t15) : orientedBalance w i (n + 1) = 0 :=
  orientedBalance_eq_zero_of_same_state w i n hW (by rw [h1, h2]; rfl)

/-- Un maintien est neutre. -/
theorem dwell_neutral (t : PrimeTransition) (h : t.cls = 0) : t.orientation = 0 :=
  (orientation_eq_zero_iff t).2 h

/-- **Neutralité des séjours** : un segment de maintiens a un bilan nul. -/
theorem orientedBalance_dwell (w : ℕ → PrimeTransition) (i n : ℕ)
    (h : ∀ l, l < n → (w (i + l)).cls = 0) : orientedBalance w i n = 0 := by
  unfold orientedBalance
  exact sum_eq_zero fun l hl => dwell_neutral _ (h l (mem_range.1 hl))

/-! ## 3. Mots finis et dénombrement -/

instance : Fintype PrimeTransition :=
  ⟨{t11, t15, t51, t55}, fun t => by cases t <;> simp⟩

/-- Mot valide fini : compositions autorisées entre indices consécutifs. -/
def ValidFinWord {n : ℕ} (w : Fin n → PrimeTransition) : Prop :=
  ∀ i j : Fin n, (j : ℕ) = i + 1 → AllowedNext (w i) (w j)

instance {n : ℕ} (w : Fin n → PrimeTransition) : Decidable (ValidFinWord w) := by
  unfold ValidFinWord; infer_instance

/-- Bilan orienté d'un mot fini. -/
def finBalance {n : ℕ} (w : Fin n → PrimeTransition) : ℤ := ∑ i, (w i).orientation

/-- Nombre d'occurrences d'une transition dans un mot fini. -/
def finCount {n : ℕ} (w : Fin n → PrimeTransition) (t : PrimeTransition) : ℕ :=
  (univ.filter fun i => w i = t).card

/-- **Le confinement de l'orientation n'est pas l'égalité des séjours** : `t11 t11 t15 t51` est
valide, de bilan nul, avec deux `t11` et aucun `t55`. -/
theorem confinement_not_dwell_equality :
    ValidFinWord ![t11, t11, t15, t51] ∧ finBalance ![t11, t11, t15, t51] = 0 ∧
      finCount ![t11, t11, t15, t51] t11 ≠ finCount ![t11, t11, t15, t51] t55 := by
  decide

/-- La transition déterminée par deux états. -/
def ofStates : Bool → Bool → PrimeTransition
  | true, true => t11 | true, false => t15 | false, true => t51 | false, false => t55

theorem ofStates_src_dst (t : PrimeTransition) : ofStates t.src t.dst = t := by cases t <;> rfl
theorem src_ofStates (a b : Bool) : (ofStates a b).src = a := by cases a <;> cases b <;> rfl
theorem dst_ofStates (a b : Bool) : (ofStates a b).dst = b := by cases a <;> cases b <;> rfl

/-- Le mot d'un chemin d'états. -/
def wordOfPath (n : ℕ) (s : Fin (n + 1) → Bool) : Fin n → PrimeTransition :=
  fun i => ofStates (s i.castSucc) (s i.succ)

theorem wordOfPath_valid (n : ℕ) (s : Fin (n + 1) → Bool) : ValidFinWord (wordOfPath n s) := by
  intro i j hij
  unfold AllowedNext wordOfPath
  rw [dst_ofStates, src_ofStates]
  congr 1
  exact Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)

/-- Le chemin d'états d'un mot (états de départ, puis dernier état d'arrivée). -/
def pathOfWord (n : ℕ) (w : Fin (n + 1) → PrimeTransition) : Fin (n + 2) → Bool :=
  fun i => if h : (i : ℕ) < n + 1 then (w ⟨i, h⟩).src else (w (Fin.last n)).dst

theorem pathOfWord_wordOfPath (n : ℕ) (s : Fin (n + 2) → Bool) :
    pathOfWord n (wordOfPath (n + 1) s) = s := by
  funext i
  unfold pathOfWord wordOfPath
  split_ifs with h
  · rw [src_ofStates]; congr 1
  · rw [dst_ofStates]; congr 1
    exact Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; have := i.isLt; omega)

theorem wordOfPath_pathOfWord (n : ℕ) (w : Fin (n + 1) → PrimeTransition) (hw : ValidFinWord w) :
    wordOfPath (n + 1) (pathOfWord n w) = w := by
  funext i
  unfold wordOfPath pathOfWord
  have h1 : ((i.castSucc : Fin (n + 2)) : ℕ) < n + 1 := by
    simp only [Fin.val_castSucc]; exact i.isLt
  rw [dif_pos h1]
  have e1 : (⟨((i.castSucc : Fin (n + 2)) : ℕ), h1⟩ : Fin (n + 1)) = i := Fin.ext (by simp)
  rw [e1]
  by_cases h2 : ((i.succ : Fin (n + 2)) : ℕ) < n + 1
  · rw [dif_pos h2]
    have hlink : AllowedNext (w i) (w ⟨((i.succ : Fin (n + 2)) : ℕ), h2⟩) :=
      hw i _ (by simp [Fin.val_succ])
    unfold AllowedNext at hlink
    rw [← hlink, ofStates_src_dst]
  · rw [dif_neg h2]
    have e2 : i = Fin.last n := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last] at h2 ⊢
      have := i.isLt
      omega
    rw [e2, ofStates_src_dst]

/-- **Mots valides de `n + 1` transitions ≃ chemins d'états de longueur `n + 2`.** -/
def validWordEquivPath (n : ℕ) :
    {w : Fin (n + 1) → PrimeTransition // ValidFinWord w} ≃ (Fin (n + 2) → Bool) where
  toFun w := pathOfWord n w.1
  invFun s := ⟨wordOfPath (n + 1) s, wordOfPath_valid (n + 1) s⟩
  left_inv w := Subtype.ext (wordOfPath_pathOfWord n w.1 w.2)
  right_inv s := pathOfWord_wordOfPath n s

/-- **8 192 mots valides de douze transitions** (= 2¹³ chemins de treize états). -/
theorem card_validWords_twelve :
    Fintype.card {w : Fin 12 → PrimeTransition // ValidFinWord w} = 8192 := by
  rw [Fintype.card_congr (validWordEquivPath 11), Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  norm_num

/-! ## 4. Grammaire des événements premiers (référence) -/

/-- Orientation de l'événement `r` : `(p_r, p_{r+1})`. -/
noncomputable def eventOrientation (r : ℕ) : ℤ := (eventTransition r).orientation

/-- Bilan orienté de `n` événements à partir du rang `i`. -/
noncomputable def eventBalance (i n : ℕ) : ℤ := orientedBalance eventTransition i n

theorem eventTransition_src (r : ℕ) : (eventTransition r).src = state6 (fnPrimeAtRank r) :=
  transitionOf_src _ _

theorem eventTransition_dst (r : ℕ) : (eventTransition r).dst = state6 (fnPrimeAtRank (r + 1)) :=
  transitionOf_dst _ _

/-- Le bilan des événements télescope sur les états des premiers d'extrémité. -/
theorem eventBalance_telescopes (i n : ℕ) :
    eventBalance i (n + 1) =
      ind1 (state6 (fnPrimeAtRank i)) - ind1 (state6 (fnPrimeAtRank (i + n + 1))) := by
  unfold eventBalance
  rw [orientedBalance_telescopes _ i n (event_word_valid i (i + n)), eventTransition_src,
    eventTransition_dst]

theorem eventBalance_abs_le_one (i n : ℕ) : |eventBalance i (n + 1)| ≤ 1 :=
  orientedBalance_abs_le_one _ i n (event_word_valid _ _)

/-- Retour exact des événements : même état aux deux bouts ⟹ bilan nul. -/
theorem eventBalance_return (i n : ℕ)
    (h : state6 (fnPrimeAtRank i) = state6 (fnPrimeAtRank (i + n + 1))) :
    eventBalance i (n + 1) = 0 := by
  rw [eventBalance_telescopes, h, sub_self]

/-- **Orientation ⟺ résidu de l'écart modulo 6** (`p_r > 3`). -/
theorem eventOrientation_of_gap (r : ℕ) (h3 : 3 < fnPrimeAtRank r) :
    (eventOrientation r = 1 ↔ nPrimeGap r % 6 = 4) ∧
      (eventOrientation r = -1 ↔ nPrimeGap r % 6 = 2) ∧
      (eventOrientation r = 0 ↔ nPrimeGap r % 6 = 0) := by
  have hg := event_gap_eq r h3
  unfold eventOrientation
  rw [hg]
  generalize eventTransition r = t
  cases t <;> simp [PrimeTransition.orientation, PrimeTransition.cls]

/-! ## 5. Niveau 1 : la grammaire reconstruite depuis les Tours -/

/-- État reconstruit de rang `k` (sur le premier reconstruit, prédicat spectral). -/
noncomputable def reconstructedState (k : ℕ) : Bool := state6 (reconstructedPrimeAtRank k)

/-- Transition reconstruite de rang `k`. -/
noncomputable def reconstructedTransition (k : ℕ) : PrimeTransition :=
  pairTransition (reconstructedPrimeAtRank k) (reconstructedPrimeAtRank (k + 1))

/-- Bilan orienté reconstruit. -/
noncomputable def reconstructedBalance (i n : ℕ) : ℤ := orientedBalance reconstructedTransition i n

/-- Chaque premier reconstruit est un premier `≥ 3` (validation). -/
theorem reconstructedPrimeAtRank_prime (k : ℕ) :
    3 ≤ reconstructedPrimeAtRank k ∧ (reconstructedPrimeAtRank k).Prime := by
  rw [reconstructedPrimeAtRank_eq_primeAtRank]
  exact Nat.nth_mem_of_infinite primeAbove_infinite k

/-- Au-delà du rang `0` (qui porte le premier `3`), le premier reconstruit dépasse `3`. -/
theorem reconstructedPrimeAtRank_gt_three (k : ℕ) (hk : 1 ≤ k) :
    3 < reconstructedPrimeAtRank k :=
  lt_of_le_of_lt (reconstructedPrimeAtRank_prime 0).1
    (reconstructedPrimeSuccession (show 0 < k by omega))

/-- **Deux états** : chaque premier reconstruit de rang `≥ 1` est dans l'un des deux états
modulo 6 (le rang `0` porte `3`, hors des deux états, comme dans la grammaire de référence). -/
theorem reconstructedState_goodMod6 (k : ℕ) (hk : 1 ≤ k) : GoodMod6 (reconstructedPrimeAtRank k) :=
  prime_goodMod6 _ (reconstructedPrimeAtRank_prime k).2 (reconstructedPrimeAtRank_gt_three k hk)

theorem reconstructedTransition_src (k : ℕ) :
    (reconstructedTransition k).src = reconstructedState k := transitionOf_src _ _

theorem reconstructedTransition_dst (k : ℕ) :
    (reconstructedTransition k).dst = reconstructedState (k + 1) := transitionOf_dst _ _

/-- **Quatre transitions, classe = écart reconstruit modulo 6.** -/
theorem reconstructedTransition_cls (k : ℕ) (hk : 1 ≤ k) :
    (reconstructedTransition k).cls = reconstructedPrimeGap k % 6 := by
  unfold reconstructedTransition
  rw [transitionOf_cls (reconstructedState_goodMod6 k hk)
    (reconstructedState_goodMod6 (k + 1) (by omega))
    (reconstructedPrimeSuccession (Nat.lt_succ_self k)).le]
  rfl

/-- **Raccord exact** : les transitions reconstruites se composent. -/
theorem reconstructedWord_valid (i j : ℕ) : ValidWord reconstructedTransition i j :=
  fun _ _ _ => raccord_exact _ _ _

/-- **Télescopage** sur la suite reconstruite. -/
theorem reconstructedBalance_telescopes (i n : ℕ) :
    reconstructedBalance i (n + 1) =
      ind1 (reconstructedState i) - ind1 (reconstructedState (i + n + 1)) := by
  unfold reconstructedBalance
  rw [orientedBalance_telescopes _ i n (reconstructedWord_valid i (i + n)),
    reconstructedTransition_src, reconstructedTransition_dst]

/-- **Confinement** sur la suite reconstruite. -/
theorem reconstructedBalance_abs_le_one (i n : ℕ) : |reconstructedBalance i (n + 1)| ≤ 1 :=
  orientedBalance_abs_le_one _ i n (reconstructedWord_valid _ _)

/-- **Retour exact** sur la suite reconstruite. -/
theorem reconstructedBalance_return (i n : ℕ)
    (h : reconstructedState i = reconstructedState (i + n + 1)) :
    reconstructedBalance i (n + 1) = 0 := by
  rw [reconstructedBalance_telescopes, h, sub_self]

/-- **Validation** : la transition reconstruite est la transition des vrais premiers `≥ 3`. -/
theorem reconstructedTransition_eq_actual (k : ℕ) :
    reconstructedTransition k = pairTransition (primeAtRankAbove k) (primeAtRankAbove (k + 1)) := by
  unfold reconstructedTransition
  rw [reconstructedPrimeAtRank_eq_primeAtRank, reconstructedPrimeAtRank_eq_primeAtRank]

/-! ## 6. Niveau 2 : transport vers les contacts -/

theorem orientation_eq_half_sgn_sub (t : PrimeTransition) :
    (t.orientation : ℝ) = (sgn t.src - sgn t.dst) / 2 := by
  cases t <;> simp [PrimeTransition.orientation, sgn, src, dst] <;> norm_num

/-- Bilan orienté pondéré par des poids réels (un poids par transition). -/
noncomputable def weightedBalance (w : ℕ → PrimeTransition) (v : ℕ → ℝ) (i n : ℕ) : ℝ :=
  ∑ l ∈ range n, ((w (i + l)).orientation : ℝ) * v l

/-- **Somme d'Abel** : le bilan pondéré d'un mot valide est borné par la variation totale des
poids (aucune hypothèse sur les poids). -/
theorem weightedBalance_abs_le (w : ℕ → PrimeTransition) (v : ℕ → ℝ) (i n : ℕ) (hn : 1 ≤ n)
    (hW : ValidWord w i (i + n)) :
    |weightedBalance w v i n| ≤
      (|v 0| + |v (n - 1)| + ∑ l ∈ range (n - 1), |v (l + 1) - v l|) / 2 := by
  have hs : ∀ l, |sgn (w (i + l)).src| = 1 := by
    intro l; unfold sgn; split_ifs <;> simp
  have hform : weightedBalance w v i n =
      ∑ l ∈ range n, ((sgn (w (i + l)).src - sgn (w (i + (l + 1))).src) / 2) * v l := by
    unfold weightedBalance
    apply sum_congr rfl
    intro l hl
    have hl' : (w (i + l)).dst = (w (i + (l + 1))).src :=
      hW (i + l) (by omega) (by rw [mem_range] at hl; omega)
    rw [orientation_eq_half_sgn_sub, hl']
  rw [hform]
  exact G4.weighted_orientation_variation_bound hn (fun l => sgn (w (i + l)).src) v hs _
    (by linarith)

theorem eventWeightedBalance_abs_le (v : ℕ → ℝ) (i n : ℕ) (hn : 1 ≤ n) :
    |weightedBalance eventTransition v i n| ≤
      (|v 0| + |v (n - 1)| + ∑ l ∈ range (n - 1), |v (l + 1) - v l|) / 2 :=
  weightedBalance_abs_le _ v i n hn (event_word_valid _ _)

/-- Valeur réelle signée du contact qui ouvre la cellule du point de rencontre de rang `r`
(fin de l'écart `r`), dans la Tour `(β, T)`. -/
noncomputable def meetingContactValue (β T : ℝ) (r : ℕ) : ℝ :=
  contactRealValue β T (cellIndexAt β T (meetingPoint ⟨r⟩))

/-- **Test de séparation** : le bilan orienté pondéré par les valeurs réelles aux contacts est
borné par leur variation totale, pour **toute** hauteur et **toute** position radiale ; la borne ne
lit ni les zéros ni `β`. -/
theorem contact_weighted_balance_abs_le (β T : ℝ) (i n : ℕ) (hn : 1 ≤ n) :
    |weightedBalance eventTransition (fun l => meetingContactValue β T (i + l)) i n| ≤
      (|meetingContactValue β T (i + 0)| + |meetingContactValue β T (i + (n - 1))| +
        ∑ l ∈ range (n - 1),
          |meetingContactValue β T (i + (l + 1)) - meetingContactValue β T (i + l)|) / 2 :=
  eventWeightedBalance_abs_le _ i n hn

/-- **Le lemme manquant n'est pas une fonction du rapport des premiers** : `29 → 31` et
`113 → 127` sont la même transition `t51`, de rapports logarithmiques distincts. -/
theorem logRatio_not_determined_by_transition :
    pairTransition 29 31 = pairTransition 113 127 ∧
      Real.log ((31 : ℝ) / 29) ≠ Real.log ((127 : ℝ) / 113) := by
  refine ⟨by decide, fun h => ?_⟩
  have := Real.log_injOn_pos (by norm_num : (31 : ℝ) / 29 ∈ Set.Ioi 0)
    (by norm_num : (127 : ℝ) / 113 ∈ Set.Ioi 0) h
  norm_num at this

/-- **Ni une fonction du rapport des amplitudes** `x^β` : même transition, rapports distincts. -/
theorem amplitude_ratio_not_determined_by_transition {β : ℝ} (hβ : 0 < β) :
    pairTransition 29 31 = pairTransition 113 127 ∧
      ((31 : ℝ) / 29) ^ β < ((127 : ℝ) / 113) ^ β :=
  ⟨by decide, Real.rpow_lt_rpow (by norm_num) (by norm_num) hβ⟩

/-- Dérive d'amplitude relative du début de l'événement `i` à la fin de l'événement `i + n`. -/
theorem segment_drift (w : TrueZero) (i n : ℕ) :
    relativeAmplitude w (meetingPoint ⟨i + n⟩) / relativeAmplitude w (fnPrimeAtRank i) =
      ((fnPrimeAtRank (i + n + 1) : ℝ) / (fnPrimeAtRank i : ℝ)) ^
        (rZeroRadialPosition w.1 - 1 / 2) :=
  relativeAmplitude_ratio w (by exact_mod_cast (thm_primeAtRank_isPrime i).pos)
    (meetingPoint_pos ⟨i + n⟩)

/-- **La correction des dérives n'est pas transportée** : sur un segment de bilan nul (retour
exact), la dérive d'amplitude relative est neutre **si et seulement si** la Tour est sur la
ligne. -/
theorem return_drift_eq_one_iff (w : TrueZero) (i n : ℕ) (_hret : eventBalance i (n + 1) = 0) :
    relativeAmplitude w (meetingPoint ⟨i + n⟩) / relativeAmplitude w (fnPrimeAtRank i) = 1 ↔
      rZeroRadialPosition w.1 = 1 / 2 := by
  rw [segment_drift]
  have hp0 : (0 : ℝ) < fnPrimeAtRank i := by exact_mod_cast (thm_primeAtRank_isPrime i).pos
  have hb : 1 < (fnPrimeAtRank (i + n + 1) : ℝ) / (fnPrimeAtRank i : ℝ) := by
    rw [one_lt_div hp0]
    exact_mod_cast thm_primeAtRank_strictMono (show i < i + n + 1 by omega)
  have hb0 : 0 < (fnPrimeAtRank (i + n + 1) : ℝ) / (fnPrimeAtRank i : ℝ) := by linarith
  have hlog : Real.log ((fnPrimeAtRank (i + n + 1) : ℝ) / (fnPrimeAtRank i : ℝ)) ≠ 0 :=
    (Real.log_pos hb).ne'
  rw [Real.rpow_def_of_pos hb0, Real.exp_eq_one_iff, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hlog
    · linarith
  · intro h; right; linarith

end RHV6Fresh

#print axioms RHV6Fresh.orientedBalance_telescopes
#print axioms RHV6Fresh.orientedBalance_abs_le_one
#print axioms RHV6Fresh.crossings_cancel_15_51
#print axioms RHV6Fresh.confinement_not_dwell_equality
#print axioms RHV6Fresh.card_validWords_twelve
#print axioms RHV6Fresh.eventBalance_telescopes
#print axioms RHV6Fresh.eventOrientation_of_gap
#print axioms RHV6Fresh.reconstructedState_goodMod6
#print axioms RHV6Fresh.reconstructedTransition_cls
#print axioms RHV6Fresh.reconstructedBalance_abs_le_one
#print axioms RHV6Fresh.reconstructedTransition_eq_actual
#print axioms RHV6Fresh.weightedBalance_abs_le
#print axioms RHV6Fresh.contact_weighted_balance_abs_le
#print axioms RHV6Fresh.logRatio_not_determined_by_transition
#print axioms RHV6Fresh.return_drift_eq_one_iff
