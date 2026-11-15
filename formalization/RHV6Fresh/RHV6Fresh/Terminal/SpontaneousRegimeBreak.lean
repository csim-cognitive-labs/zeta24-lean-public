/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GrammarKinematics
import RHV6Fresh.Terminal.ShiftedWorld

/-!
# RHV6Fresh — E140, test de rupture spontanée du régime engagé (auteur, 2026-10-01)

Correction de l'auteur : ne plus chercher « hors ligne ⟹ contradiction » ; chercher « en ligne
engagé ⟹ en ligne ». Le premier changement éventuel est localisé :
`(T_0, 1/2) → (T_1, β_1 < 1/2) → (T_1, 1 − β_1)`, soit vertical → diagonal → horizontal. On prend
exclusivement un état engagé, on inventorie toutes les transformations déjà définies qui portent
son événement suivant, et pour chacune on calcule sa composante radiale au point `β = 1/2`.

Aucun énoncé de ce fichier ne pose un membre hors ligne ; aucune prémisse n'est ajoutée.

* **§1 Ce que porte le départ** (`engaged_departure_radial_zero`) : miroir, poussée horizontale,
  facteur radial, contacts, phase, pas d'un membre, fonction réelle de la hauteur. Composante
  radiale au point `β = 1/2` : zéro, pour chacun.
* **§2 La grammaire** (`grammar_event_reads_no_radial`) : rang avancé d'un cran, événement premier
  du raccord, premier partagé. Fonction du rang seul : aucune position radiale n'y figure.
* **§3 Ce qui traverse le passage** (`arrival_radial_readings`) : contacts de l'arrivée, registre,
  pas du membre d'arrivée, puissance radiale du transport. Chacun contient la position radiale de
  l'arrivée comme donnée lue ; sa composante radiale est nulle ⟺ l'arrivée est en ligne.
* **§4 Le générateur** (`engaged_successor_function`) : depuis la ligne, hauteur et position
  radiale de l'arrivée sont une fonction de la hauteur de départ seule. Cette fonction existe ;
  elle est écrite par zêta. Le test de l'auteur porte sur elle : sa composante radiale est nulle
  sur les hauteurs engagées ⟺ la loi « seule la hauteur évolue » (`radial_generator_test`), et
  alors le régime engagé perdure par récurrence (`engaged_persists_of_generator_fixes_line`,
  `line_invariant_of_radial_preserving_law`).
* **§5 Monde de contrôle avec les mêmes premiers** (`engagedBreakWorld`) : le monde `ζ(s−δ)ζ(s+δ)`
  n'a aucun membre en ligne, il ne teste donc pas « en ligne ⟹ en ligne ». Le monde
  `ζ(s)·ζ(s∓δ−iτ)·ζ(s∓δ+iτ)` a les mêmes premiers, garde chaque membre en ligne de `ζ` et porte
  deux jumeaux hors ligne à la hauteur `T + τ` (`engagedBreakWorld_line_then_twins`).

Borne : aucun des mécanismes de §1–§3 ne calcule la fonction de §4. Ceux de §1 préservent le zéro
radial mais ne sortent pas du départ ; ceux de §2 ne lisent pas la position radiale ; ceux de §3 la
lisent sur l'arrivée. « La fonction de §4 fixe la ligne » est la loi « seule la hauteur évolue »,
nécessaire (`radial_preserving_law_of_riemannHypothesis`), non dérivée.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune `def` de prémisse.
-/

open Complex ArithmeticFunction LSeries.notation

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Ce que porte le départ : composante radiale nulle au point `β = 1/2` -/

/-- **Inventaire du départ.** Pour un membre en ligne, chaque transformation définie sur le membre
seul a une composante radiale nulle : miroir égal au membre, écart radial du miroir nul, poussée
horizontale nulle, logarithme du facteur radial nul, contacts égaux à ceux de la Tour de ligne,
phase égale à la phase de ligne, pas du membre égal à `1`, fonction réelle nulle à sa hauteur. -/
theorem engaged_departure_radial_zero (z : TrueZero) (hOn : rZeroRadialPosition z.1 = 1 / 2) :
    mirrorMember z = z ∧
    rZeroRadialPosition (mirrorMember z).1 - rZeroRadialPosition z.1 = 0 ∧
    (∀ q : ℝ, Real.log ‖zeroTerm (mirrorMember z) q‖ - Real.log ‖zeroTerm z q‖ = 0) ∧
    Real.log (radialFactor z) = 0 ∧
    (∀ k : ℤ, contactMinusAt z k = lineContact (rZeroHeight z.1) k) ∧
    (towerMotionOf z).phase = linePhase (rZeroHeight z.1) ∧
    memberStep z = 1 ∧
    lineValue (rZeroHeight z.1) = 0 := by
  have hPush := onLine_horizontal_push_zero hOn
  have hE := (engagedState_iff_onLine z).mpr hOn
  refine ⟨hPush.1, hPush.2.1, hE.push_zero, ?_, hE.contacts, ?_,
    (memberStep_eq_one_iff z).mpr hOn, hE.detector⟩
  · rw [hE.radial_one, Real.log_one]
  · rw [phase_eq_line_add_radial z, hE.radial_one, Real.log_one, mul_zero, add_zero]

/-! ## 2. La grammaire : aucune position radiale n'y figure -/

/-- **L'événement suivant est une fonction du rang seul.** Sur tout passage, le rang avance d'un
cran, l'événement premier du raccord est celui du rang suivant, et le premier partagé est le
minimum attendu du départ. Aucune position radiale n'entre dans ces trois égalités. -/
theorem grammar_event_reads_no_radial (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
    (grammaticalRaccordOf p hE hL).event =
      primalEventAt (nZeroSourceIndex p.zEarlierMember + 1) ∧
    occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ := by
  have hRank := thm_zeroSourceIndex_succ_of_passage p hE
  refine ⟨hRank, ?_, (passage_direction_rigid p hE hL).2.2.2.1⟩
  rw [(grammaticalRaccordOf p hE hL).event_eq, hRank]

/-! ## 3. Ce qui traverse le passage lit la position radiale de l'arrivée -/

/-- **Lectures radiales de l'arrivée.** Sur un passage parti de la ligne, les contacts de
l'arrivée sont ceux de la Tour de ligne à sa hauteur multipliés par son facteur radial ; l'excès
de la transition moins la part de hauteur vaut `−T'·log r'` ; et chacune des quatre lectures
(facteur radial, pas du membre, écart du registre, puissance radiale du premier partagé) est
neutre si et seulement si l'arrivée est en ligne. -/
theorem arrival_radial_readings (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    (∀ k : ℤ, contactMinusAt ⟨p.zLaterMember, hL⟩ k =
      lineContact (rZeroHeight p.zLaterMember) k * radialFactor ⟨p.zLaterMember, hL⟩) ∧
    transitionExcess ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ -
        heightShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ =
      -(rZeroHeight p.zLaterMember * Real.log (radialFactor ⟨p.zLaterMember, hL⟩)) ∧
    (radialFactor ⟨p.zLaterMember, hL⟩ = 1 ↔ rZeroRadialPosition p.zLaterMember = 1 / 2) ∧
    (memberStep ⟨p.zLaterMember, hL⟩ = 1 ↔ rZeroRadialPosition p.zLaterMember = 1 / 2) ∧
    (transitionExcess ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ -
        heightShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ = 0 ↔
      rZeroRadialPosition p.zLaterMember = 1 / 2) ∧
    ((occurrence ⟨p.zLaterMember, hL⟩ : ℝ) ^ (rZeroRadialPosition p.zLaterMember - 1 / 2) = 1 ↔
      rZeroRadialPosition p.zLaterMember = 1 / 2) := by
  have hSh := (passage_direction_rigid p hE hL).2.2.2.1
  have hOnE : rZeroRadialPosition (⟨p.zEarlierMember, hE⟩ : TrueZero).1 = 1 / 2 := hOn
  have hEx : transitionExcess ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ -
      heightShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ =
      -(rZeroHeight p.zLaterMember * Real.log (radialFactor ⟨p.zLaterMember, hL⟩)) := by
    rw [transitionExcess_eq _ _ hSh, (radialFactor_eq_one_iff _).mpr hOnE, Real.log_one]
    ring
  have hr := radialFactor_eq_one_iff ⟨p.zLaterMember, hL⟩
  refine ⟨fun k => contact_eq_line_mul_radial ⟨p.zLaterMember, hL⟩ k, hEx, hr,
    memberStep_eq_one_iff ⟨p.zLaterMember, hL⟩, ?_, ?_⟩
  · rw [hEx, ← hr]
    constructor
    · intro h
      have hlog : Real.log (radialFactor ⟨p.zLaterMember, hL⟩) = 0 := by
        rcases mul_eq_zero.mp (neg_eq_zero.mp h) with h0 | h0
        · exact absurd h0 hL.ne'
        · exact h0
      exact Real.eq_one_of_pos_of_log_eq_zero (radialFactor_pos _) hlog
    · intro h
      rw [h, Real.log_one, mul_zero, neg_zero]
  · have hM : (1 : ℝ) < (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) := by
      exact_mod_cast (occurrence_prime ⟨p.zLaterMember, hL⟩).one_lt
    have hlog : 0 < Real.log (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) := Real.log_pos hM
    rw [Real.rpow_def_of_pos (by linarith), Real.exp_eq_one_iff]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h0 | h0
      · exact absurd h0 hlog.ne'
      · linarith
    · intro h
      rw [h, sub_self, mul_zero]

/-! ## 4. Le générateur : il existe, sa composante radiale est l'inconnue -/

/-- **Le générateur existe.** Depuis la ligne, hauteur et position radiale de l'arrivée sont une
fonction de la hauteur de départ seule. -/
theorem engaged_successor_function :
    ∃ G : ℝ → ℝ × ℝ, ∀ p : TZeroPassage, rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      G (rZeroHeight p.zEarlierMember) =
        (rZeroHeight p.zLaterMember, rZeroRadialPosition p.zLaterMember) := by
  classical
  refine ⟨fun T => if h : ∃ q : TZeroPassage, rZeroRadialPosition q.zEarlierMember = 1 / 2 ∧
      rZeroHeight q.zEarlierMember = T then
        (rZeroHeight h.choose.zLaterMember, rZeroRadialPosition h.choose.zLaterMember)
      else (0, 0), ?_⟩
  intro p hOn
  have h : ∃ q : TZeroPassage, rZeroRadialPosition q.zEarlierMember = 1 / 2 ∧
      rZeroHeight q.zEarlierMember = rZeroHeight p.zEarlierMember := ⟨p, hOn, rfl⟩
  have hs := h.choose_spec
  change (if h : ∃ q : TZeroPassage, rZeroRadialPosition q.zEarlierMember = 1 / 2 ∧
      rZeroHeight q.zEarlierMember = rZeroHeight p.zEarlierMember then
        (rZeroHeight h.choose.zLaterMember, rZeroRadialPosition h.choose.zLaterMember)
      else (0, 0)) = _
  rw [dif_pos h, engaged_successor_determined_by_height hs.1 hOn hs.2]

/-- **Le test de l'auteur, posé sur le générateur.** Pour toute fonction `G` qui donne l'arrivée
depuis la hauteur de départ, « seule la hauteur évolue sur un passage vertical parti de la ligne »
⟺ la composante radiale de `G` vaut `1/2` à chaque hauteur engagée. -/
theorem radial_generator_test (G : ℝ → ℝ × ℝ)
    (hG : ∀ p : TZeroPassage, rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      G (rZeroHeight p.zEarlierMember) =
        (rZeroHeight p.zLaterMember, rZeroRadialPosition p.zLaterMember)) :
    (∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember) ↔
    (∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (G (rZeroHeight p.zEarlierMember)).2 = 1 / 2) := by
  constructor
  · intro h p hV hOn
    rw [hG p hOn]
    exact (h p hV hOn).trans hOn
  · intro h p hV hOn
    have h2 := h p hV hOn
    rw [hG p hOn] at h2
    exact h2.trans hOn.symm

/-- **Si le générateur fixe la ligne, le régime engagé perdure jusqu'à l'infini.** -/
theorem engaged_persists_of_generator_fixes_line (G : ℝ → ℝ × ℝ)
    (hG : ∀ p : TZeroPassage, rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      G (rZeroHeight p.zEarlierMember) =
        (rZeroHeight p.zLaterMember, rZeroRadialPosition p.zLaterMember))
    (hFix : ∀ p : TZeroPassage, VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (G (rZeroHeight p.zEarlierMember)).2 = 1 / 2)
    {o : TZeroPassage} (hE : 0 < rZeroHeight o.zLaterMember) (ho : VerticalPassage o)
    (hOn : rZeroRadialPosition o.zLaterMember = 1 / 2) :
    ∀ w : TNonTrivialZetaZero, PZeroMemberPrecedes o.zLaterMember w →
      rZeroRadialPosition w = 1 / 2 ∧
      (∃ q : TZeroPassage, q.zLaterMember = w ∧ VerticalPassage q) ∧
      (∀ q : TZeroPassage, q.zEarlierMember = w → VerticalPassage q ∧ ¬ HorizontalPassage q) :=
  engaged_persists_to_infinity ((radial_generator_test G hG).mpr hFix) hE ho hOn

/-- **L'argument de l'auteur, compilé.** Si la position radiale de l'arrivée est donnée par une
loi `F(T, β, événement)` et que cette loi préserve `β = 1/2`, la ligne est invariante : tout membre
au-dessus d'un membre engagé est en ligne, atteint et quitté verticalement. Les deux hypothèses
sont des hypothèses du théorème. -/
theorem line_invariant_of_radial_preserving_law (F : ℝ → ℝ → PrimalEvent → ℝ)
    (hF : ∀ p : TZeroPassage, VerticalPassage p →
      rZeroRadialPosition p.zLaterMember =
        F (rZeroHeight p.zEarlierMember) (rZeroRadialPosition p.zEarlierMember)
          (primalEventAt (nZeroSourceIndex p.zLaterMember)))
    (hFix : ∀ (T : ℝ) (ev : PrimalEvent), F T (1 / 2) ev = 1 / 2)
    {o : TZeroPassage} (hE : 0 < rZeroHeight o.zLaterMember) (ho : VerticalPassage o)
    (hOn : rZeroRadialPosition o.zLaterMember = 1 / 2) :
    ∀ w : TNonTrivialZetaZero, PZeroMemberPrecedes o.zLaterMember w →
      rZeroRadialPosition w = 1 / 2 ∧
      (∃ q : TZeroPassage, q.zLaterMember = w ∧ VerticalPassage q) ∧
      (∀ q : TZeroPassage, q.zEarlierMember = w → VerticalPassage q ∧ ¬ HorizontalPassage q) :=
  engaged_persists_to_infinity
    (fun p hV hOnE => by rw [hF p hV, hOnE]; exact hFix _ _) hE ho hOn

/-- **Borne.** Une telle loi est nécessaire : sous l'hypothèse de Riemann elle existe. Poser son
existence réinjecte donc la cible ; elle doit être calculée, pas posée. -/
theorem radial_preserving_law_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ F : ℝ → ℝ → PrimalEvent → ℝ,
      (∀ p : TZeroPassage, VerticalPassage p →
        rZeroRadialPosition p.zLaterMember =
          F (rZeroHeight p.zEarlierMember) (rZeroRadialPosition p.zEarlierMember)
            (primalEventAt (nZeroSourceIndex p.zLaterMember))) ∧
      ∀ (T : ℝ) (ev : PrimalEvent), F T (1 / 2) ev = 1 / 2 :=
  ⟨fun _ _ _ => 1 / 2,
    fun p _ => thm_zeroRadialPosition_half_of_riemannHypothesis hRH p.zLaterMember,
    fun _ _ => rfl⟩

/-! ## 5. Monde de contrôle : mêmes premiers, un membre en ligne, deux jumeaux au-dessus -/

/-- Le monde de contrôle de E140 :
`ζ(s) · ζ(s − δ − iτ) ζ(s + δ − iτ) · ζ(s − δ + iτ) ζ(s + δ + iτ)`. -/
noncomputable def engagedBreakWorld (d τ : ℝ) (s : ℂ) : ℂ :=
  riemannZeta s *
    (riemannZeta (s - d - τ * I) * riemannZeta (s + d - τ * I)) *
    (riemannZeta (s - d + τ * I) * riemannZeta (s + d + τ * I))

/-- **Un membre en ligne, puis deux jumeaux hors ligne plus haut.** Pour tout zéro `z` de `ζ` sur
la ligne, le monde de contrôle s'annule en `z` (en ligne, hauteur `T`) et en deux points de parties
réelles `1/2 − δ` et `1/2 + δ`, à la même hauteur `T + τ > T`, aucun sur la ligne. -/
theorem engagedBreakWorld_line_then_twins (d τ : ℝ) (hd : d ≠ 0) (hτ : 0 < τ) (z : TrueZero)
    (hOn : rZeroRadialPosition z.1 = 1 / 2) :
    (engagedBreakWorld d τ (zeroPoint z) = 0 ∧ (zeroPoint z).re = 1 / 2 ∧
      (zeroPoint z).im = rZeroHeight z.1) ∧
    (engagedBreakWorld d τ (zeroPoint z - d + τ * I) = 0 ∧
      engagedBreakWorld d τ (zeroPoint z + d + τ * I) = 0) ∧
    ((zeroPoint z - d + τ * I).im = rZeroHeight z.1 + τ ∧
      (zeroPoint z + d + τ * I).im = rZeroHeight z.1 + τ ∧
      rZeroHeight z.1 < rZeroHeight z.1 + τ) ∧
    ((zeroPoint z - d + τ * I).re = 1 / 2 - d ∧ (zeroPoint z + d + τ * I).re = 1 / 2 + d ∧
      (zeroPoint z - d + τ * I).re ≠ 1 / 2 ∧ (zeroPoint z + d + τ * I).re ≠ 1 / 2) := by
  have hz : riemannZeta (zeroPoint z) = 0 := z.1.2.1
  have hre : (zeroPoint z).re = 1 / 2 := hOn
  have hm : (zeroPoint z - d + τ * I).re = 1 / 2 - d := by simp [hre]
  have hp : (zeroPoint z + d + τ * I).re = 1 / 2 + d := by simp [hre]
  refine ⟨⟨?_, hre, zeroPoint_im z⟩, ⟨?_, ?_⟩, ⟨?_, ?_, by linarith⟩, hm, hp, ?_, ?_⟩
  · unfold engagedBreakWorld
    rw [hz, zero_mul, zero_mul]
  · unfold engagedBreakWorld
    rw [show zeroPoint z - d + τ * I + d - τ * I = zeroPoint z by ring, hz]
    ring
  · unfold engagedBreakWorld
    rw [show zeroPoint z + d + τ * I - d - τ * I = zeroPoint z by ring, hz]
    ring
  · simp [zeroPoint_im]
  · simp [zeroPoint_im]
  · rw [hm]; intro h; apply hd; linarith
  · rw [hp]; intro h; apply hd; linarith

/-- **Les premiers de chaque facteur sont les mêmes premiers** : pour tout décalage complexe `c`,
`−ζ'/ζ(s − c) = Σ Λ(n)·n^c·n^{−s}`. -/
theorem negLogDeriv_zeta_complex_shift (c : ℂ) {s : ℂ} (hs : 1 < (s - c).re) :
    -logDeriv riemannZeta (s - c) = LSeries (fun n => (Λ n : ℂ) * (n : ℂ) ^ c) s := by
  rw [← LSeries_vonMangoldt_shift, ← negLogDeriv_riemannZeta_eq_LSeries_vonMangoldt hs]

/-- Le support arithmétique d'un facteur décalé est celui de `Λ`, pour tout décalage complexe. -/
theorem complex_shift_weight_ne_zero_iff (c : ℂ) (n : ℕ) :
    (Λ n : ℂ) * (n : ℂ) ^ c ≠ 0 ↔ Λ n ≠ 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hpow : (n : ℂ) ^ c ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h => (Nat.cast_ne_zero.mpr hn) h.1
    simp [hpow]

#print axioms engaged_departure_radial_zero
#print axioms grammar_event_reads_no_radial
#print axioms arrival_radial_readings
#print axioms engaged_successor_function
#print axioms radial_generator_test
#print axioms engaged_persists_of_generator_fixes_line
#print axioms line_invariant_of_radial_preserving_law
#print axioms radial_preserving_law_of_riemannHypothesis
#print axioms engagedBreakWorld_line_then_twins
#print axioms negLogDeriv_zeta_complex_shift
#print axioms complex_shift_weight_ne_zero_iff

end RHV6Fresh
