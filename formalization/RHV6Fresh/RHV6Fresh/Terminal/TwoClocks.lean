/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.EventHeightProgression
import RHV6Fresh.Direct.PivotCell
import RHV3Lean.Objects.TowerPrimeGapSpan

/-!
# RHV6Fresh — les deux horloges (membres `n`, hauteurs `h`) et la portée `S_n(T)`

Plan TDD (auteur, 2026-09-28) : `experiments/PLAN_TDD_DEUX_HORLOGES_20260928.md`. Ce fichier
matérialise SIMULTANÉMENT, sur un même passage, les deux horloges déjà compilées séparément
(`Terminal/EventHeightProgression.lean` : événement/hauteur ; base `rhv3_lean`,
`TowerPrimeGapSpan.lean` : la portée de Tour d'une place première). Aucune contradiction n'est
produite : le fichier documente ce que le code force sur le carré `(n, h, T, S_n)`, en particulier
la dichotomie `Δh ∈ {0, 1}` gouvernée par `T_E < T_L` ou `T_E = T_L`, et instancie le glissement OFF
`(Δn, Δh) = (1, 0)` déjà annoncé (`off_event_increment_without_height`).

## TDD-5 — recherche d'un troisième objet canonique (verdict, aucun code forcé)

Relecture demandée par le plan :

* `Terminal/ExplicitFormulaLink.lean` : `zeroTerm` dépend de `(β, T, q)` seulement — ni l'index
  membre `n` ni l'index hauteur `h` n'y entrent ; aveugle à la distinction membre/hauteur, comme
  attendu.
* `Direct/Raccords.lean` : `reaches S p` lit `(T, φ, k, m, p)` avec `p = Occ(w)` — c'est le canal
  MEMBRE (`occurrence`, donc `nZeroSourceIndex`), jamais l'index hauteur `nZeroHeightEventIndex`.
* `TowerPrimeGapSpan z n` (base) est une fonction de `(T, n)` avec `n` un **paramètre libre** : rien
  n'empêche d'y substituer soit `n := nZeroSourceIndex z.1` (portée-membre, `clockState.Sn`
  ci-dessous) soit `n := nZeroHeightEventIndex (tZeroHeightEvent z)` (portée-hauteur) ; mais
  `rPrimeGapLogRatio` n'est monotone en aucun rang (les écarts premiers `g_n` ne sont pas
  monotones, `PrimeGapGrammar.lean`), donc AUCUNE comparaison `S_h ≤ S_n` ou `S_h ≥ S_n` n'est un
  théorème — on ne le force pas ici.
* `pivotCoordinate`/`towerPosition` (`Direct/PivotCell.lean`) sont des fonctions du seul membre (via
  `p_min`, `expectedMinimumPrime`) ; `pivotCoordinate_sameHeight_shift_le_one` ne vaut qu'à `q`
  commun (déjà noté par l'auteur, 2026-09-27).

**Verdict** : hors `fnPrimeAtRank` lui-même (calculé des deux côtés, `clock_pn_eq`/`clock_ph_eq`
ci-dessous, coïncidant partout ⟺ RH via `occurrences_agree_iff_riemannHypothesis`), aucun objet
compilé de la base n'est calculé À LA FOIS depuis la seule hauteur ET depuis le seul membre. Le seul
pont trouvé reste `n = h`, déjà équivalent à RH. Rien n'est fabriqué pour combler cette absence.

## TDD-6 — non traité

Aucun objet compilé de multiplicité/bifurcation (McPhedran) n'existe dans la hiérarchie CLAUDE.md
§2 ; ce fichier n'en introduit pas.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## TDD-1. La portée du passage en termes d'occurrences -/

/-- **La portée de Tour de la place `n_E` du membre précoce d'un passage** est exactement
`T_E/π · log(Occ(L)/Occ(E))` : l'écart logarithmique de la place `n_E` est lu, terme à terme, sur
les deux occurrences (membres) du passage lui-même, sans passer par `nPrimeGap`/`fnPrimeSuccessor`
explicitement. -/
theorem passage_span_eq_log_occurrences (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    TowerPrimeGapSpan ⟨p.zEarlierMember, hE⟩ (nZeroSourceIndex p.zEarlierMember) =
      rZeroHeight p.zEarlierMember / Real.pi *
        Real.log ((occurrence ⟨p.zLaterMember, hL⟩ : ℝ) /
          (occurrence ⟨p.zEarlierMember, hE⟩ : ℝ)) := by
  unfold TowerPrimeGapSpan rPrimeGapLogRatio rTowerHeight
  rw [occurrence_successor_of_passage p hE hL,
    occurrence_eq_canonicalAnchor (⟨p.zEarlierMember, hE⟩ : TrueZero)]
  unfold nMemberCanonicalAnchor
  rfl

/-- **La portée d'un passage est toujours strictement positive.**  Aucune approximation : produit
d'une hauteur strictement positive divisée par `π`, et d'un ratio logarithmique strictement positif
(`thm_primeGapLogRatio_pos`). -/
theorem passage_span_pos (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember) :
    0 < TowerPrimeGapSpan ⟨p.zEarlierMember, hE⟩ (nZeroSourceIndex p.zEarlierMember) := by
  unfold TowerPrimeGapSpan rTowerHeight
  exact mul_pos (div_pos hE Real.pi_pos) (thm_primeGapLogRatio_pos _)

/-! ## TDD-2. Dichotomie de l'horloge des hauteurs sur un passage -/

/-- **Sur tout passage, l'horloge des hauteurs avance d'exactement `0` ou `1`.**  Si la hauteur
avance strictement (`T_E < T_L`), l'événement de hauteur avance de un ; si elle stagne
(`T_E = T_L`), l'événement de hauteur ne bouge pas. Aucune troisième possibilité : l'ordre
membre-sensible (`thm_zeroMemberPrecedes_iff_height_radial_lex`) ne laisse que ces deux cas sur un
passage réellement consécutif. -/
theorem passage_heightEventIndex_dichotomy (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    (rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
        nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zLaterMember, hL⟩) =
          nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zEarlierMember, hE⟩) + 1) ∨
    (rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember ∧
        nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zLaterMember, hL⟩) =
          nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zEarlierMember, hE⟩)) := by
  rcases (thm_zeroMemberPrecedes_iff_height_radial_lex p.zEarlierMember p.zLaterMember).mp
      p.precedes with hLt | ⟨hEqHeight, _⟩
  · left
    refine ⟨hLt, ?_⟩
    apply thm_consecutiveHeightEvents_index_succ
      (g := { earlier := tZeroHeightEvent (⟨p.zEarlierMember, hE⟩ : TrueZero)
              later := tZeroHeightEvent (⟨p.zLaterMember, hL⟩ : TrueZero)
              height_lt := hLt
              consecutive := by
                rintro ⟨middle, hMidLt, hLtMid⟩
                obtain ⟨zMid, hzMid⟩ := middle.2
                have hMidLt' : rZeroHeight p.zEarlierMember < middle.1 := hMidLt
                have hLtMid' : middle.1 < rZeroHeight p.zLaterMember := hLtMid
                have hMidLt2 : rZeroHeight p.zEarlierMember < rZeroHeight zMid.1 := by
                  rw [hzMid]; exact hMidLt'
                have hLtMid2 : rZeroHeight zMid.1 < rZeroHeight p.zLaterMember := by
                  rw [hzMid]; exact hLtMid'
                have h1 : PZeroMemberPrecedes p.zEarlierMember zMid.1 :=
                  (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mpr (Or.inl hMidLt2)
                have h2 : PZeroMemberPrecedes zMid.1 p.zLaterMember :=
                  (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mpr (Or.inl hLtMid2)
                exact p.hConsecutive.2 ⟨zMid.1, h1, h2⟩ })
  · right
    exact ⟨hEqHeight, (thm_heightEventIndex_eq_of_sameHeight hEqHeight).symm⟩

/-! ## TDD-3. Le carré des deux horloges (matérialisation, pas de contradiction) -/

/-- **L'état de carré des deux horloges d'un zéro.**  Aucun champ n'est un certificat stocké : tous
sont des fonctions déjà compilées, appliquées au seul zéro reçu. `n`/`pn` sont l'horloge des
membres ; `h`/`ph` l'horloge des hauteurs ; `Sn` la portée de Tour de la place `n` ; `kc` la
coordonnée de pivot du minimum attendu, sur la Tour propre de `z`. -/
structure ClockState (z : TrueZero) where
  n : ℕ
  h : ℕ
  T : ℝ
  pn : ℕ
  ph : ℕ
  Sn : ℝ
  kc : ℤ

/-- **Construction du carré**, sur le seul zéro reçu, sans nouvelle hypothèse. -/
noncomputable def clockState (z : TrueZero) : ClockState z where
  n := nZeroSourceIndex z.1
  h := nZeroHeightEventIndex (tZeroHeightEvent z)
  T := rZeroHeight z.1
  pn := occurrence z
  ph := nHeightEventMZOccurrence (tZeroHeightEvent z)
  Sn := TowerPrimeGapSpan z (nZeroSourceIndex z.1)
  kc := pivotCoordinate z (expectedMinimumPrime z : ℝ)

/-- **L'horloge des hauteurs est toujours en retard ou à l'heure sur l'horloge des membres.** -/
theorem clock_h_le_n (z : TrueZero) : (clockState z).h ≤ (clockState z).n :=
  heightEventIndex_le_sourceIndex z

/-- **Le premier lu par l'horloge des membres est l'ancre canonique au rang `n`.** -/
theorem clock_pn_eq (z : TrueZero) : (clockState z).pn = fnPrimeAtRank (clockState z).n := by
  show occurrence z = fnPrimeAtRank (nZeroSourceIndex z.1)
  rw [occurrence_eq_canonicalAnchor]
  rfl

/-- **Le premier lu par l'horloge des hauteurs est l'ancre canonique au rang `h`.** -/
theorem clock_ph_eq (z : TrueZero) : (clockState z).ph = fnPrimeAtRank (clockState z).h := by
  show nHeightEventMZOccurrence (tZeroHeightEvent z) =
    fnPrimeAtRank (nZeroHeightEventIndex (tZeroHeightEvent z))
  rw [thm_heightEventMZOccurrence_eq_canonicalPrime_unconditional]
  rfl

/-- **Le premier lu par l'horloge des hauteurs est toujours en avance ou à l'heure sur celui de
l'horloge des membres.**  Conséquence directe de `clock_h_le_n` par la monotonie stricte de
l'énumération des premiers. -/
theorem clock_ph_le_pn (z : TrueZero) : (clockState z).ph ≤ (clockState z).pn := by
  rw [clock_ph_eq, clock_pn_eq]
  exact thm_primeAtRank_strictMono.monotone (clock_h_le_n z)

/-- **La portée du carré est toujours strictement positive.** -/
theorem clock_Sn_pos (z : TrueZero) : 0 < (clockState z).Sn := by
  show 0 < TowerPrimeGapSpan z (nZeroSourceIndex z.1)
  unfold TowerPrimeGapSpan rTowerHeight
  exact mul_pos (div_pos z.2 Real.pi_pos) (thm_primeGapLogRatio_pos _)

/-! ## TDD-5 (corollaire compilé). La portée est constante sur toute fibre de même hauteur -/

/-- **Sur toute place `n`, deux membres de même hauteur lisent la même portée.**  Réponse compilée à
la seule comparaison qui EST un théorème dans la recherche TDD-5 ci-dessus (celles impliquant un
rang libre ne le sont pas) : conséquence directe de `thm_towerPrimeGapSpan_eq_iff_height_eq`, sans
hypothèse nouvelle. -/
theorem span_eq_on_sameHeight_fiber (zLeft zRight : TrueZero) (n : ℕ)
    (h : rZeroHeight zLeft.1 = rZeroHeight zRight.1) :
    TowerPrimeGapSpan zRight n = TowerPrimeGapSpan zLeft n :=
  (thm_towerPrimeGapSpan_eq_iff_height_eq zLeft zRight n).mpr h.symm

/-! ## TDD-4. Instanciation OFF : le glissement d'une horloge sur l'autre -/

/-- **Le contraste ON** : sur un passage dont les deux extrémités sont sur la ligne critique,
l'événement des membres ET l'événement des hauteurs avancent tous deux de un. -/
theorem onLine_clock_sync (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOnE : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hOnL : rZeroRadialPosition p.zLaterMember = 1 / 2) :
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
      nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zLaterMember, hL⟩) =
        nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zEarlierMember, hE⟩) + 1 := by
  refine ⟨eventIndex_succ_of_passage p hE, ?_⟩
  have hHt := passage_height_lt_of_onLine p hOnE hOnL
  rcases passage_heightEventIndex_dichotomy p hE hL with ⟨_, hIdxSucc⟩ | ⟨hEq, _⟩
  · exact hIdxSucc
  · exact absurd hEq (ne_of_lt hHt)

/-- **Le glissement OFF, littéralement sur le carré des deux horloges.**  Un zéro hors ligne produit
un passage réel où l'horloge des membres avance de un (`Δn = 1`), où l'horloge des hauteurs ne
bouge pas (`Δh = 0`), où la portée de la place franchie est strictement positive, et où — parce que
la hauteur ne bouge pas — la portée du passage entier lue à l'ARRIVÉE est EXACTEMENT la même que
celle lue au DÉPART : l'horloge des membres a avancé sans que rien, du côté de la portée première
`S_n`, n'en porte la trace. -/
theorem off_clock_slip {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    ∃ p : TZeroPassage, ∃ hE : 0 < rZeroHeight p.zEarlierMember,
      ∃ hL : 0 < rZeroHeight p.zLaterMember,
        nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
        nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zLaterMember, hL⟩) =
          nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zEarlierMember, hE⟩) ∧
        0 < TowerPrimeGapSpan ⟨p.zEarlierMember, hE⟩ (nZeroSourceIndex p.zEarlierMember) ∧
        rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember ∧
        TowerPrimeGapSpan ⟨p.zLaterMember, hL⟩ (nZeroSourceIndex p.zEarlierMember) =
          TowerPrimeGapSpan ⟨p.zEarlierMember, hE⟩ (nZeroSourceIndex p.zEarlierMember) := by
  obtain ⟨p, hE, hL, _, hSame, hSucc, _, _⟩ := off_event_increment_without_height hOff
  refine ⟨p, hE, hL, hSucc, ?_, passage_span_pos p hE, hSame,
    (thm_towerPrimeGapSpan_eq_iff_height_eq ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
      (nZeroSourceIndex p.zEarlierMember)).mpr hSame.symm⟩
  rcases passage_heightEventIndex_dichotomy p hE hL with ⟨hLt, _⟩ | ⟨_, hEqIdx⟩
  · exact absurd hSame (ne_of_lt hLt)
  · exact hEqIdx

/-!
## Verdict final (ce que ce fichier ne prétend pas)

Aucun des théorèmes ci-dessus ne produit RH.  `off_clock_slip` matérialise, sur le carré des deux
horloges, exactement le fait déjà connu (`off_event_increment_without_height`,
`grammarsAgree_iff_riemannHypothesis`) : hors ligne, l'horloge des membres peut avancer seule, sans
que la portée première `S_n` n'en garde de trace lisible depuis la seule fibre de hauteur.  La
question de l'auteur — quelle structure analytique oblige `Δn = 1` à correspondre à `Δh = 1` plutôt
qu'à `Δβ ≠ 0` — reste, dans le code, exactement `grammarsAgree_iff_riemannHypothesis`
(`clock_agree_iff_riemannHypothesis` ci-dessus) : rendue lisible sur un seul record, pas fermée.
TDD-6 (McPhedran/multiplicité) n'est pas codé : aucun objet compilé de multiplicité n'existe dans la
hiérarchie CLAUDE.md §2.
-/

#print axioms off_clock_slip
#print axioms passage_heightEventIndex_dichotomy

end RHV6Fresh
