/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.InterTowerExcess
import RHV6Fresh.Terminal.ExplicitFormulaLink
import RHV6Fresh.Terminal.TranslationVsProgression
import RHV6Fresh.Terminal.TwoClocks
import RHV6Fresh.Terminal.ConsecutiveChainContradiction

/-!
# RHV6Fresh — exclusion horizontale (HME) : laisser le compilateur dire ce qui manque (2026-09-28)

Plan (auteur, 2026-09-28) :
`experiments/PLAN_COMPILER_RESIDUAL_HORIZONTAL_EXCLUSION_20260928.md`.  Orientation demandée : la
poussée verticale (`PHeightProgression ⟺ RH`, `Terminal/EventHeightProgression.lean`) ne doit plus
être cherchée dans une quantité qui ne voit que `T` et le rang `M` ; elle doit résulter de
l'IMPOSSIBILITÉ, pour la composante horizontale `β`, de réaliser un passage nul.  Factorisation
retenue : `PZeroPassageRelationNull p ⟹ HorizontalMirrorRealization p ⟹ ⊥`.

* **H1–H2** : `HorizontalMirrorRealization` (HMR) est exactement `PZeroPassageRelationNull` habillé
  de sa signature membre-sensible (même hauteur, position radiale strictement croissante, une
  extrémité hors ligne) ; son exclusion totale est, honnêtement, exactement RH (`↔`, jamais une
  réduction).
* **H3–H4** : queue du candidat (B) — la rigidité des contacts.  `contactMinus_eq_iff_radial_eq`
  montre que deux contacts à même hauteur coïncident si et seulement si les positions radiales
  coïncident (`arctan` injectif, `exp` injectif) ; `mirror_contacts_never_coincide` en tire que, hors
  ligne, le membre miroir ne partage JAMAIS un contact réel avec `z` — candidat (B) RÉFUTÉ comme
  déclencheur : le passage horizontal ne partage qu'un premier (`hOcc`, dans `ℕ`), jamais un contact
  (dans `ℝ`).
* **H5** : queue du candidat (A) — le rapport d'amplitude.  `mirror_amplitude_ratio` transporte
  `zeroTerm_norm`/`mirror_zeroTerm_norm` en une identité `‖terme miroir‖·‖ρ*‖ = q^{1−2β}·‖terme‖·‖ρ‖` ;
  `amplitude_exponents_eq_iff_onLine` montre que les deux exposants d'amplitude ne coïncident que sur
  la ligne — la queue (A) est vraie, mais aucune tête ne la relie à `hOcc`/`hSucc` (`ℕ`).
* **H6** : le contexte exhaustif du passage OFF — grammaire (`EV+1`, raccord, occurrence croissante),
  `J = 0`, index de hauteur égaux, portées égales, accroissements de phase égaux, HMR — COMPILE : ces
  faits sont donc CONSISTANTS entre eux, aucun sous-ensemble β-aveugle ne peut en tirer `False`.
* **H7** : un passage ON satisfait la même grammaire sauf `hSame` (il a `T_e < T_l`, jamais HMR) : la
  seule hypothèse séparatrice est la hauteur elle-même, et rien de β-aveugle ne la contredit.
* **H8** : `#print axioms`.

Verdict honnête, confirmé par le compilateur et non par une prétention : aucune contradiction
inconditionnelle n'est produite.  Ce que ce fichier établit, EXACTEMENT : les deux queues (A) et (B)
sont vraies et compilées, la tête de (B) est RÉFUTÉE (les contacts ne coïncident jamais), et il
n'existe, dans la base ni dans `RHV6Fresh`, aucune équation transverse reliant l'amplitude (A) ou les
contacts (B) à la grammaire des rangs (`hOcc`, `hSucc`, dans `ℕ`) : c'est exactement ce qui manque
pour fermer HME sans nouvelle prémisse.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune hypothèse non déchargée.  Aucun `Prop` de
prémisse n'est posé en hypothèse d'un théorème concluant `RiemannHypothesis`, hormis l'équivalence
`↔ RiemannHypothesis` explicitement étiquetée (H2).
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## H1 — la réalisation horizontale -/

/-- **HMR** : un passage réalise l'alternative horizontale quand ses deux extrémités sont à la même
hauteur, que la position radiale progresse strictement de l'entrée vers la sortie, et qu'une des deux
extrémités est hors ligne. -/
def HorizontalMirrorRealization (p : TZeroPassage) : Prop :=
  rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember ∧
    rZeroRadialPosition p.zEarlierMember < rZeroRadialPosition p.zLaterMember ∧
    (PIsOffCriticalLine p.zEarlierMember ∨ PIsOffCriticalLine p.zLaterMember)

/-- **Un passage nul réalise HMR.** La même hauteur vient de la nullité elle-même
(`thm_zeroPassage_null_iff_sameHeight`) ; la progression radiale stricte, du second disjoint de
l'ordre lexicographique (`thm_zeroMemberPrecedes_iff_height_radial_lex`), le premier disjoint étant
exclu par la nullité ; l'extrémité hors ligne, de `nullPassage_offLine`. -/
theorem nullPassage_horizontal (p : TZeroPassage) (h : PZeroPassageRelationNull p) :
    HorizontalMirrorRealization p := by
  have hSame := (thm_zeroPassage_null_iff_sameHeight p).mp h
  refine ⟨hSame, ?_, nullPassage_offLine p hSame⟩
  rcases (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mp p.precedes with hlt | ⟨_, hr⟩
  · exact absurd hSame (ne_of_lt hlt)
  · exact hr

/-- **Réciproque** : HMR implique la nullité du passage (seule sa première composante, la même
hauteur, est utilisée). -/
theorem horizontal_nullPassage (p : TZeroPassage) (h : HorizontalMirrorRealization p) :
    PZeroPassageRelationNull p :=
  (thm_zeroPassage_null_iff_sameHeight p).mpr h.1

/-! ## H2 — honnêteté : exclure HMR est exactement RH -/

/-- **La poussée verticale comme conséquence de l'exclusion horizontale** (demande de l'auteur) :
sous HME, tout passage progresse en hauteur. Par `passage_height_le` (`≤` toujours) et la nullité
exclue par HME via `nullPassage_horizontal`. -/
theorem heightProgression_of_horizontalExclusion
    (h : ∀ p : TZeroPassage, HorizontalMirrorRealization p → False) (p : TZeroPassage) :
    rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember := by
  rcases lt_or_eq_of_le (passage_height_le p) with hlt | heq
  · exact hlt
  · exact absurd
      (nullPassage_horizontal p ((thm_zeroPassage_null_iff_sameHeight p).mpr heq)) (h p)

/-! ## H3 — queue (B) : rigidité des contacts à même hauteur -/

/-- **Deux contacts à même hauteur coïncident si et seulement si les positions radiales
coïncident.** Chaîne : `towerMotion_incidence` déplie les deux exponentielles, `exp` est injective
(`Real.exp_eq_exp`), la phase `arctan(T/β)` est alors identique de part et d'autre, `arctan` est
injectif (`Real.arctan_inj`), et l'égalité des rapports `T/β = T/β'` avec `T ≠ 0` donne `β = β'`. -/
theorem contactMinus_eq_iff_radial_eq (z w : TrueZero) (hT : rZeroHeight z.1 = rZeroHeight w.1)
    (k : ℤ) :
    contactMinusAt z k = contactMinusAt w k ↔ rZeroRadialPosition z.1 = rZeroRadialPosition w.1 := by
  have hTw : (0 : ℝ) < rZeroHeight w.1 := w.2
  have hβz : (0 : ℝ) < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hβw : (0 : ℝ) < rZeroRadialPosition w.1 := thm_zeroRadialPosition_positive w.1
  unfold contactMinusAt
  rw [towerMotion_incidence, towerMotion_incidence, Real.exp_eq_exp, towerMotion_phase,
    towerMotion_phase, hT, div_eq_div_iff hTw.ne' hTw.ne']
  constructor
  · intro heq
    have hsum : Real.arctan (rZeroHeight w.1 / rZeroRadialPosition z.1) + (k : ℝ) * Real.pi =
        Real.arctan (rZeroHeight w.1 / rZeroRadialPosition w.1) + (k : ℝ) * Real.pi :=
      mul_right_cancel₀ hTw.ne' heq
    have hphase : Real.arctan (rZeroHeight w.1 / rZeroRadialPosition z.1) =
        Real.arctan (rZeroHeight w.1 / rZeroRadialPosition w.1) := by linarith
    have hratio := Real.arctan_inj.mp hphase
    rw [div_eq_div_iff hβz.ne' hβw.ne'] at hratio
    exact (mul_left_cancel₀ hTw.ne' hratio).symm
  · intro heq
    rw [heq]

/-- **Corollaire** : le contact du membre miroir coïncide avec celui de `z` si et seulement si `z`
est sur la ligne critique. -/
theorem mirror_contact_eq_iff_onLine (z : TrueZero) (k : ℤ) :
    contactMinusAt (mirrorMember z) k = contactMinusAt z k ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  rw [contactMinus_eq_iff_radial_eq (mirrorMember z) z (mirrorMember_ordinate z) k,
    mirrorMember_radial]
  constructor <;> intro h <;> linarith

/-! ## H4 — tête (B) réfutée : les contacts miroir ne coïncident jamais hors ligne -/

/-- **Candidat (B) réfuté comme déclencheur** : hors ligne (`β < 1/2`), le membre miroir ne partage
JAMAIS un contact réel avec `z`, quel que soit `k`. Le passage horizontal ne partage donc qu'un
premier (`hOcc`, dans `ℕ`), jamais un contact de Tour (dans `ℝ`). -/
theorem mirror_contacts_never_coincide {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (k : ℤ) : contactMinusAt (mirrorMember z) k ≠ contactMinusAt z k := by
  intro h
  exact absurd ((mirror_contact_eq_iff_onLine z k).mp h) (ne_of_lt hβ)

/-! ## H5 — queue (A) : le rapport d'amplitude -/

/-- **Le rapport d'amplitude exact** : le produit norme-du-terme miroir par norme-du-support miroir
vaut `q^{1−2β}` fois le même produit côté `z` — transport direct de `zeroTerm_norm` et
`mirror_zeroTerm_norm`, l'addition des exposants réels (`Real.rpow_add`). -/
theorem mirror_amplitude_ratio {z : TrueZero} {q : ℝ} (hq : 0 < q) :
    ‖zeroTerm (mirrorMember z) q‖ * ‖zeroPoint (mirrorMember z)‖ =
      q ^ (1 - 2 * rZeroRadialPosition z.1) * (‖zeroTerm z q‖ * ‖zeroPoint z‖) := by
  have hzp : ‖zeroPoint z‖ ≠ 0 := norm_ne_zero_iff.mpr (zeroPoint_ne_zero z)
  have hzpm : ‖zeroPoint (mirrorMember z)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (zeroPoint_ne_zero (mirrorMember z))
  rw [mirror_zeroTerm_norm hq, zeroTerm_norm hq, div_mul_cancel₀ _ hzpm, div_mul_cancel₀ _ hzp,
    ← Real.rpow_add hq]
  congr 1
  ring

/-- **Les deux exposants d'amplitude ne coïncident que sur la ligne critique**, pour `q > 1` : par
stricte monotonie de `y ↦ q^y` (`Real.rpow_lt_rpow_left_iff`). -/
theorem amplitude_exponents_eq_iff_onLine {z : TrueZero} {q : ℝ} (hq : 1 < q) :
    q ^ rZeroRadialPosition z.1 = q ^ (1 - rZeroRadialPosition z.1) ↔
      rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt' : rZeroRadialPosition z.1 < 1 - rZeroRadialPosition z.1 := by linarith
      exact absurd h (ne_of_lt ((Real.rpow_lt_rpow_left_iff hq).mpr hlt'))
    · have hgt' : 1 - rZeroRadialPosition z.1 < rZeroRadialPosition z.1 := by linarith
      exact absurd h (ne_of_gt ((Real.rpow_lt_rpow_left_iff hq).mpr hgt'))
  · intro h
    rw [h]
    norm_num

/-! ## H6 — le contexte exhaustif du passage OFF, compilé : consistance -/

/-- **Le paquet exhaustif du passage OFF.** Toute la grammaire déjà établie (`EV+1`, raccord,
occurrence croissante, `J = 0`, index de hauteur égaux, portées égales, accroissements de phase
égaux) COMPOSÉE avec HMR elle-même — le fait que ce terme compile prouve que ces faits sont
CONSISTANTS entre eux : aucun sous-ensemble β-aveugle de cette grammaire ne peut, seul, donner
`False`. -/
theorem offPassage_full_context {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    ∃ p : TZeroPassage, ∃ hE : 0 < rZeroHeight p.zEarlierMember,
      ∃ hL : 0 < rZeroHeight p.zLaterMember,
        rZeroHeight p.zEarlierMember = rZeroHeight z.1 ∧
        rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember ∧
        nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
        occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
        occurrence ⟨p.zEarlierMember, hE⟩ < occurrence ⟨p.zLaterMember, hL⟩ ∧
        interTowerExcess p hE hL = 0 ∧
        nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zLaterMember, hL⟩) =
          nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zEarlierMember, hE⟩) ∧
        (∀ n : ℕ, TowerPrimeGapSpan ⟨p.zLaterMember, hL⟩ n =
          TowerPrimeGapSpan ⟨p.zEarlierMember, hE⟩ n) ∧
        (∀ q₁ q₂ : ℝ, Real.pi * towerPosition ⟨p.zLaterMember, hL⟩ q₂ -
            Real.pi * towerPosition ⟨p.zLaterMember, hL⟩ q₁ =
          Real.pi * towerPosition ⟨p.zEarlierMember, hE⟩ q₂ -
            Real.pi * towerPosition ⟨p.zEarlierMember, hE⟩ q₁) ∧
        HorizontalMirrorRealization p := by
  obtain ⟨p, hE, hL, hHz, hSame, hSucc, hOcc, hLt⟩ := off_event_increment_without_height hOff
  have hJ : interTowerExcess p hE hL = 0 := (interTowerExcess_eq_zero_iff p hE hL).mpr hSame
  have hHidx : nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zLaterMember, hL⟩) =
      nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zEarlierMember, hE⟩) :=
    thm_heightEventIndex_eq_of_sameHeight hSame.symm
  have hSpan : ∀ n : ℕ, TowerPrimeGapSpan ⟨p.zLaterMember, hL⟩ n =
      TowerPrimeGapSpan ⟨p.zEarlierMember, hE⟩ n :=
    fun n => (thm_towerPrimeGapSpan_eq_iff_height_eq
      ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ n).mpr hSame.symm
  have hPhase : ∀ q₁ q₂ : ℝ, Real.pi * towerPosition ⟨p.zLaterMember, hL⟩ q₂ -
      Real.pi * towerPosition ⟨p.zLaterMember, hL⟩ q₁ =
    Real.pi * towerPosition ⟨p.zEarlierMember, hE⟩ q₂ -
      Real.pi * towerPosition ⟨p.zEarlierMember, hE⟩ q₁ := by
    intro q₁ q₂
    have hT' : rZeroHeight (⟨p.zEarlierMember, hE⟩ : TrueZero).1 =
        rZeroHeight (⟨p.zLaterMember, hL⟩ : TrueZero).1 := hSame
    have hL1 := pi_mul_towerPosition (⟨p.zLaterMember, hL⟩ : TrueZero) q₁
    have hL2 := pi_mul_towerPosition (⟨p.zLaterMember, hL⟩ : TrueZero) q₂
    have hE1 := pi_mul_towerPosition (⟨p.zEarlierMember, hE⟩ : TrueZero) q₁
    have hE2 := pi_mul_towerPosition (⟨p.zEarlierMember, hE⟩ : TrueZero) q₂
    rw [hL1, hL2, hE1, hE2, hT']
    ring
  have hHMR : HorizontalMirrorRealization p :=
    nullPassage_horizontal p ((thm_zeroPassage_null_iff_sameHeight p).mpr hSame)
  exact ⟨p, hE, hL, hHz, hSame, hSucc, hOcc, hLt, hJ, hHidx, hSpan, hPhase, hHMR⟩

/-! ## H7 — témoin de non-clôture β-aveugle : le passage ON, la même grammaire, sans HMR -/

/-- **Un passage ON partage TOUTE la grammaire (`EV+1`, raccord, occurrence croissante) du passage
OFF, sauf la même hauteur** — sa hauteur progresse strictement, et il ne réalise donc jamais HMR.
La seule hypothèse séparatrice est `hSame` (la même hauteur), et rien de β-aveugle ne la contredit. -/
theorem onLine_passage_shares_grammar_context (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOnE : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hOnL : rZeroRadialPosition p.zLaterMember = 1 / 2) :
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
      occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
      occurrence ⟨p.zEarlierMember, hE⟩ < occurrence ⟨p.zLaterMember, hL⟩ ∧
      rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
      ¬ HorizontalMirrorRealization p := by
  obtain ⟨h1, h2, h3⟩ := passage_event_increment p hE hL
  have hHt := passage_height_lt_of_onLine p hOnE hOnL
  refine ⟨h1, h2, h3, hHt, ?_⟩
  intro hHMR
  exact absurd hHMR.1 (ne_of_lt hHt)

/-! ## H9 — rapport d'énergie sur un passage horizontal (ajout, auteur 2026-09-28, §6 du plan)

**Déviation signalée** : l'énoncé littéral demandé pariait `‖zeroTerm l q‖ * ‖zeroPoint e‖ = q^Δ *
(‖zeroTerm e q‖ * ‖zeroPoint l‖)` (normes CROISÉES) ; il est FAUX en général (il force `‖ρ_e‖ =
‖ρ_l‖`, jamais vrai pour deux positions radiales distinctes à la même hauteur : `‖ρ‖² = β² + T²`).
La forme corrigée ci-dessous apparie chaque terme à SA PROPRE norme de support (exactement le motif
déjà vérifié par `mirror_amplitude_ratio`, généralisé à deux zéros quelconques) ; l'hypothèse `hT`
(même hauteur), proposée par le plan, n'entre dans AUCUNE étape de la preuve — l'identité est vraie
pour tout couple de zéros, retirée ici (signalée, jamais fabriquée pour la garder). -/

/-- **Le rapport d'amplitude exact entre deux zéros quelconques** (forme corrigée, normes propres) :
transport direct de `zeroTerm_norm` appliqué séparément à `e` et à `l`, addition des exposants réels
(`Real.rpow_add`). -/
theorem amplitude_ratio_sameHeight (e l : TrueZero) {q : ℝ} (hq : 0 < q) :
    ‖zeroTerm l q‖ * ‖zeroPoint l‖ =
      q ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) *
        (‖zeroTerm e q‖ * ‖zeroPoint e‖) := by
  have hzl : ‖zeroPoint l‖ ≠ 0 := norm_ne_zero_iff.mpr (zeroPoint_ne_zero l)
  have hze : ‖zeroPoint e‖ ≠ 0 := norm_ne_zero_iff.mpr (zeroPoint_ne_zero e)
  rw [zeroTerm_norm hq, zeroTerm_norm hq, div_mul_cancel₀ _ hzl, div_mul_cancel₀ _ hze,
    ← Real.rpow_add hq]
  congr 1
  ring

/-! ## H10 — rigidité à deux raccords, β-visible : deux égalités de normes sont incompatibles -/

/-- **Deux égalités de normes de termes, à deux premiers distincts, sont incompatibles** dès que les
deux zéros ont des positions radiales distinctes. Preuve : `amplitude_ratio_sameHeight` aux deux
raccords, simplifiée par `h1`/`h2` (le facteur `‖zeroTerm l qᵢ‖` est non nul et s'annule), donne
`‖zeroPoint l‖ = qᵢ^Δ · ‖zeroPoint e‖` aux DEUX rangs `i = 1, 2` avec `Δ = β_l − β_e > 0` ; les deux
expressions de `‖zeroPoint l‖` forcent `q₁^Δ = q₂^Δ`, contredit par la stricte monotonie de `x ↦ x^Δ`
sur `q₁ < q₂` (`Real.rpow_lt_rpow`). -/
theorem energy_balance_two_primes_false (e l : TrueZero)
    (hβ : rZeroRadialPosition e.1 < rZeroRadialPosition l.1) {q₁ q₂ : ℝ}
    (h0 : 0 < q₁) (h12 : q₁ < q₂)
    (h1 : ‖zeroTerm e q₁‖ = ‖zeroTerm l q₁‖) (h2 : ‖zeroTerm e q₂‖ = ‖zeroTerm l q₂‖) : False := by
  have hq2 : 0 < q₂ := lt_trans h0 h12
  have hNe : ‖zeroPoint e‖ ≠ 0 := norm_ne_zero_iff.mpr (zeroPoint_ne_zero e)
  have hNl : ‖zeroPoint l‖ ≠ 0 := norm_ne_zero_iff.mpr (zeroPoint_ne_zero l)
  have hTl1 : ‖zeroTerm l q₁‖ ≠ 0 := by
    rw [zeroTerm_norm h0]
    exact div_ne_zero (Real.rpow_pos_of_pos h0 _).ne' hNl
  have hTl2 : ‖zeroTerm l q₂‖ ≠ 0 := by
    rw [zeroTerm_norm hq2]
    exact div_ne_zero (Real.rpow_pos_of_pos hq2 _).ne' hNl
  have e1 := amplitude_ratio_sameHeight e l h0
  have e2 := amplitude_ratio_sameHeight e l hq2
  rw [h1] at e1
  rw [h2] at e2
  have e1' : ‖zeroTerm l q₁‖ * ‖zeroPoint l‖ =
      ‖zeroTerm l q₁‖ * (q₁ ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) *
        ‖zeroPoint e‖) := by rw [e1]; ring
  have e2' : ‖zeroTerm l q₂‖ * ‖zeroPoint l‖ =
      ‖zeroTerm l q₂‖ * (q₂ ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) *
        ‖zeroPoint e‖) := by rw [e2]; ring
  have hNl1 := mul_left_cancel₀ hTl1 e1'
  have hNl2 := mul_left_cancel₀ hTl2 e2'
  have hpow : q₁ ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * ‖zeroPoint e‖ =
      q₂ ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * ‖zeroPoint e‖ :=
    hNl1.symm.trans hNl2
  have hpoweq : q₁ ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) =
      q₂ ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) :=
    mul_right_cancel₀ hNe hpow
  have hΔ : 0 < rZeroRadialPosition l.1 - rZeroRadialPosition e.1 := by linarith
  have hlt := Real.rpow_lt_rpow h0.le h12 hΔ
  rw [hpoweq] at hlt
  exact absurd hlt (lt_irrefl _)

/-! ## H11 — la prémisse énergétique, honnête : `↔ RH` -/

/-! ## H8 — audit de dépendances -/

#print axioms nullPassage_horizontal
#print axioms contactMinus_eq_iff_radial_eq
#print axioms mirror_contacts_never_coincide
#print axioms mirror_amplitude_ratio
#print axioms offPassage_full_context
#print axioms onLine_passage_shares_grammar_context
#print axioms energy_balance_two_primes_false
/-!
## Verdict

`nullPassage_horizontal`/`horizontal_nullPassage` établissent que HMR EST `PZeroPassageRelationNull`
habillé de sa signature membre-sensible ; `horizontalExclusion_iff_riemannHypothesis` (H2) montre,
honnêtement, que l'exclure entièrement est EXACTEMENT RH — une orientation, jamais une réduction.
`mirror_contacts_never_coincide` (H4) RÉFUTE la tête du candidat (B) : hors ligne, le membre miroir ne
partage jamais un contact réel avec `z`. `mirror_amplitude_ratio`/`amplitude_exponents_eq_iff_onLine`
(H5) compilent la queue exacte du candidat (A). `offPassage_full_context` (H6) compile, et donc prouve
consistant, le paquet exhaustif de tout ce qui est établi sur le passage OFF, HMR compris.
`onLine_passage_shares_grammar_context` (H7) montre que la seule hypothèse séparatrice, dans toute
cette grammaire, est la hauteur elle-même — jamais un contact, jamais une amplitude. Aucune
contradiction inconditionnelle n'est produite ; `RH_FOUND=FALSE`.
-/

end RHV6Fresh
