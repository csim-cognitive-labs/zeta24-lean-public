/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ConstraintPacket

/-!
# RHV6Fresh — le passage vertical diagonal parti de la ligne (auteur, 2026-09-30)

Correction demandée par l'auteur sur `RegimeTrigger.lean` et `ConstraintPacket.lean` : ces fichiers
caractérisent et certifient, ils ne produisent pas de cause. Le maillon à traiter n'est plus
l'entrée horizontale ; c'est le passage vertical qui la précède,

  `(T, 1/2) → (T', β' < 1/2)`,  `T' > T`,

et la question est : existe-t-il une quantité dont l'évolution est entièrement déterminée par
`ΔT` mais que `Δβ ≠ 0` modifierait ?

Ce fichier pose toutes les quantités du passage sur les mêmes deux membres, en même temps.

* **§1 La part de la Tour que la hauteur seule détermine.** `lineContact T k` : les contacts de la
  Tour de ligne à la hauteur `T`, fonction de `T` seul. Tout contact de tout membre est exactement
  `lineContact T k · radialFactor` (`contact_eq_line_mul_radial`) ; le facteur radial est unique
  pour toute la Tour, vaut `1` si et seulement si le membre est en ligne, est `> 1` sous la ligne
  et `< 1` au-dessus (`radialFactor_eq_one_iff`, `radialFactor_gt_one_iff`,
  `radialFactor_lt_one_iff`).
* **§2 Garde (tautologie fonctionnelle).** Une quantité définie comme fonction de la hauteur seule
  ne voit aucun déplacement radial (`height_determined_radial_blind`) et sa contraposée
  (`radial_sensitive_not_height_determined`). Ces deux énoncés n'excluent que la tentative naïve où
  le facteur radial serait directement une fonction de `T` ; ils ne disent rien d'une quantité
  couplée `Q(T, β)` contrainte par une autre identité, et ne réfutent pas la recherche d'une loi de
  transition conservant `r = 1`. Les
  contacts d'un membre sont ceux que la hauteur seule détermine si et seulement si le membre est
  en ligne (`contacts_height_determined_iff_onLine`).
* **§3 Le détecteur en `T` seul pendant le passage.** Strictement entre les deux hauteurs d'un
  passage, la fonction réelle `lineValue` ne s'annule pas et garde un signe constant
  (`lineValue_ne_zero_between`, `lineValue_sign_constant_between`).
* **§4 Le registre du passage diagonal parti de la ligne** (`diagonal_from_line_ledger`,
  `regime_entry_diagonal_ledger`) : `ΔT`, `Δβ`, pas, contacts du départ et de l'arrivée, phase,
  poids, détecteur en `T`, événement premier, reste et écart, en même temps.

Borne compilée : « les contacts de l'arrivée d'un passage vertical sont ceux que la hauteur seule
détermine » équivaut, passage par passage, à « l'arrivée est en ligne »
(`vertical_exhausts_iff_arrival_onLine`, spécialisation de
`contacts_height_determined_iff_onLine`). Aucune loi des bases ne fournit le membre gauche : il
manque une loi de transition indépendante qui conserve `r = 1` de `T` à `T'`.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean Set

/-! ## 1. La part de la Tour que la hauteur seule détermine -/

/-- La phase de la Tour de ligne à la hauteur `T` : fonction de `T` seul. -/
noncomputable def linePhase (T : ℝ) : ℝ := Real.arctan (T / (1 / 2))

/-- Les contacts de la Tour de ligne à la hauteur `T` : fonction de `T` seul. -/
noncomputable def lineContact (T : ℝ) (k : ℤ) : ℝ :=
  Real.exp ((linePhase T + (k : ℝ) * Real.pi) / T)

theorem lineContact_pos (T : ℝ) (k : ℤ) : 0 < lineContact T k := Real.exp_pos _

/-- **Le facteur radial d'un membre** : ce qui, dans ses contacts, ne vient pas de la hauteur. -/
noncomputable def radialFactor (z : TrueZero) : ℝ :=
  Real.exp (((towerMotionOf z).phase - linePhase (rZeroHeight z.1)) / rZeroHeight z.1)

theorem radialFactor_pos (z : TrueZero) : 0 < radialFactor z := Real.exp_pos _

/-- **Découpage exact de la Tour** : tout contact est le contact de la Tour de ligne à la même
hauteur, multiplié par un facteur radial unique pour toute la Tour. -/
theorem contact_eq_line_mul_radial (z : TrueZero) (k : ℤ) :
    contactMinusAt z k = lineContact (rZeroHeight z.1) k * radialFactor z := by
  rw [contactMinusAt_eq_exp, ← towerMotion_phase]
  unfold lineContact radialFactor
  rw [← Real.exp_add]
  congr 1
  ring

/-- La phase dépasse la phase de ligne si et seulement si le membre est sous la ligne. -/
theorem linePhase_lt_phase_iff (z : TrueZero) :
    linePhase (rZeroHeight z.1) < (towerMotionOf z).phase ↔ rZeroRadialPosition z.1 < 1 / 2 := by
  rw [towerMotion_phase]
  unfold linePhase
  rw [Real.arctan_strictMono.lt_iff_lt]
  exact div_lt_div_iff_of_pos_left z.2 (by norm_num) (thm_zeroRadialPosition_positive z.1)

/-- La phase est sous la phase de ligne si et seulement si le membre est au-dessus de la ligne. -/
theorem phase_lt_linePhase_iff (z : TrueZero) :
    (towerMotionOf z).phase < linePhase (rZeroHeight z.1) ↔ 1 / 2 < rZeroRadialPosition z.1 := by
  rw [towerMotion_phase]
  unfold linePhase
  rw [Real.arctan_strictMono.lt_iff_lt]
  exact div_lt_div_iff_of_pos_left z.2 (thm_zeroRadialPosition_positive z.1) (by norm_num)

/-- Sous la ligne, le facteur radial est strictement supérieur à `1`. -/
theorem radialFactor_gt_one_iff (z : TrueZero) :
    1 < radialFactor z ↔ rZeroRadialPosition z.1 < 1 / 2 := by
  unfold radialFactor
  have hT : (0 : ℝ) < rZeroHeight z.1 := z.2
  rw [Real.one_lt_exp_iff, lt_div_iff₀ hT, zero_mul, sub_pos]
  exact linePhase_lt_phase_iff z

/-- Au-dessus de la ligne, le facteur radial est strictement inférieur à `1`. -/
theorem radialFactor_lt_one_iff (z : TrueZero) :
    radialFactor z < 1 ↔ 1 / 2 < rZeroRadialPosition z.1 := by
  unfold radialFactor
  have hT : (0 : ℝ) < rZeroHeight z.1 := z.2
  rw [Real.exp_lt_one_iff, div_lt_iff₀ hT, zero_mul, sub_neg]
  exact phase_lt_linePhase_iff z

/-- **Le facteur radial vaut `1` si et seulement si le membre est en ligne.** -/
theorem radialFactor_eq_one_iff (z : TrueZero) :
    radialFactor z = 1 ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro h
    rcases lt_trichotomy (rZeroRadialPosition z.1) (1 / 2) with hlt | heq | hgt
    · exact absurd h (ne_of_gt ((radialFactor_gt_one_iff z).mpr hlt))
    · exact heq
    · exact absurd h (ne_of_lt ((radialFactor_lt_one_iff z).mpr hgt))
  · intro h
    unfold radialFactor linePhase
    rw [towerMotion_phase, h, sub_self, zero_div, Real.exp_zero]

/-! ## 2. Garde : fonction de la hauteur seule (tautologie fonctionnelle) -/

/-- **Une quantité définie comme fonction de la hauteur seule ne voit aucun déplacement radial** :
elle prend la même valeur sur deux membres de même hauteur. Tautologie fonctionnelle : elle
n'exclut aucune loi couplant `T` et `β` par une autre identité. -/
theorem height_determined_radial_blind {α : Type*} (Q : TrueZero → α) (f : ℝ → α)
    (hQ : ∀ z, Q z = f (rZeroHeight z.1)) (z w : TrueZero)
    (hT : rZeroHeight z.1 = rZeroHeight w.1) : Q z = Q w := by
  rw [hQ z, hQ w, hT]

/-- Contraposée de la précédente : une quantité que le déplacement radial modifie n'est pas une
fonction de la hauteur seule. -/
theorem radial_sensitive_not_height_determined {α : Type*} (Q : TrueZero → α) {z w : TrueZero}
    (hT : rZeroHeight z.1 = rZeroHeight w.1) (hne : Q z ≠ Q w) :
    ¬ ∃ f : ℝ → α, ∀ u, Q u = f (rZeroHeight u.1) := by
  rintro ⟨f, hQ⟩
  exact hne (height_determined_radial_blind Q f hQ z w hT)

/-- **Les contacts d'un membre sont ceux que la hauteur seule détermine si et seulement si le
membre est en ligne.** -/
theorem contacts_height_determined_iff_onLine (z : TrueZero) :
    (∀ k : ℤ, contactMinusAt z k = lineContact (rZeroHeight z.1) k) ↔
      rZeroRadialPosition z.1 = 1 / 2 := by
  rw [← radialFactor_eq_one_iff]
  constructor
  · intro h
    have h0 := h 0
    rw [contact_eq_line_mul_radial] at h0
    have hpos := lineContact_pos (rZeroHeight z.1) 0
    have : lineContact (rZeroHeight z.1) 0 * (radialFactor z - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hpos.ne'
    · linarith
  · intro h k
    rw [contact_eq_line_mul_radial, h, mul_one]

/-- **Borne** : sur un passage vertical, « les contacts de l'arrivée sont ceux que la hauteur
seule détermine » équivaut à « l'arrivée est en ligne ». -/
theorem vertical_exhausts_iff_arrival_onLine (p : TZeroPassage)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    (∀ k : ℤ, contactMinusAt ⟨p.zLaterMember, hL⟩ k =
        lineContact (rZeroHeight p.zLaterMember) k) ↔
      rZeroRadialPosition p.zLaterMember = 1 / 2 :=
  contacts_height_determined_iff_onLine ⟨p.zLaterMember, hL⟩

/-! ## 3. Le détecteur en `T` seul pendant le passage -/

/-- Strictement entre les deux hauteurs d'un passage, la fonction réelle ne s'annule pas. -/
theorem lineValue_ne_zero_between (p : TZeroPassage) {t : ℝ}
    (h1 : rZeroHeight p.zEarlierMember < t) (h2 : t < rZeroHeight p.zLaterMember) :
    lineValue t ≠ 0 := by
  intro h
  apply p.hConsecutive.2
  let w : TNonTrivialZetaZero := ⟨linePoint t, (onLine_zero_iff_lineValue t).mpr h⟩
  exact ⟨w, (thm_zeroMemberPrecedes_iff_height_radial_lex p.zEarlierMember w).mpr (Or.inl h1),
    (thm_zeroMemberPrecedes_iff_height_radial_lex w p.zLaterMember).mpr (Or.inl h2)⟩

/-- Strictement entre les deux hauteurs d'un passage, la fonction réelle garde un signe constant. -/
theorem lineValue_sign_constant_between (p : TZeroPassage) {t₁ t₂ : ℝ}
    (h1 : rZeroHeight p.zEarlierMember < t₁) (h12 : t₁ < t₂)
    (h2 : t₂ < rZeroHeight p.zLaterMember) : 0 < lineValue t₁ * lineValue t₂ := by
  have ha := lineValue_ne_zero_between p h1 (h12.trans h2)
  have hb := lineValue_ne_zero_between p (h1.trans h12) h2
  rcases lt_trichotomy (lineValue t₁ * lineValue t₂) 0 with h | h | h
  · obtain ⟨t, ht, hz⟩ := onLine_zero_of_sign_change h12 h
    exact absurd ((onLine_zero_iff_lineValue t).mp hz)
      (lineValue_ne_zero_between p (h1.trans ht.1) (ht.2.trans h2))
  · exact absurd h (mul_ne_zero ha hb)
  · exact h

/-! ## 4. Le registre du passage diagonal parti de la ligne -/

/-- **Registre complet du passage vertical diagonal parti de la ligne**, toutes les quantités sur
les mêmes deux membres, en même temps :

1. `ΔT > 0` et `Δβ < 0` ;
2. le pas de l'arrivée est `π/T'`, strictement contracté : déterminé par la hauteur seule ;
3. les contacts du départ sont ceux de la Tour de ligne à sa hauteur : déterminés par `T` seul ;
4. les contacts de l'arrivée sont ceux de la Tour de ligne à la hauteur `T'`, multipliés par un
   facteur radial unique `> 1` ; ceux de son miroir par un facteur `< 1` ;
5. la phase de l'arrivée dépasse la phase de ligne à la hauteur `T'` ;
6. le poids de l'arrivée est `x^{β'}/‖ρ'‖`, avec `x^{β'} < x^{1/2}` pour `x > 1` ;
7. le détecteur en `T` seul : la fonction réelle s'annule à la hauteur de départ et ne s'annule
   nulle part strictement entre les deux hauteurs ;
8. l'événement premier : le raccord grammatical existe, son événement est celui que les zéros
   reconstruisent, l'histoire première gagne exactement cet événement ;
9. le reste arithmétique reste égal au reste spectral, et l'écart au tout en ligne est non nul. -/
theorem diagonal_from_line_ledger (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hV : VerticalPassage p)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hLow : rZeroRadialPosition p.zLaterMember < 1 / 2) :
    (rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
      rZeroRadialPosition p.zLaterMember < rZeroRadialPosition p.zEarlierMember) ∧
    (towerPitch ⟨p.zLaterMember, hL⟩ = Real.pi / rZeroHeight p.zLaterMember ∧
      towerPitch ⟨p.zLaterMember, hL⟩ < towerPitch ⟨p.zEarlierMember, hE⟩) ∧
    (∀ k : ℤ, contactMinusAt ⟨p.zEarlierMember, hE⟩ k =
      lineContact (rZeroHeight p.zEarlierMember) k) ∧
    (1 < radialFactor ⟨p.zLaterMember, hL⟩ ∧
      radialFactor (mirrorMember ⟨p.zLaterMember, hL⟩) < 1 ∧
      ∀ k : ℤ, contactMinusAt ⟨p.zLaterMember, hL⟩ k =
        lineContact (rZeroHeight p.zLaterMember) k * radialFactor ⟨p.zLaterMember, hL⟩) ∧
    linePhase (rZeroHeight p.zLaterMember) < (towerMotionOf ⟨p.zLaterMember, hL⟩).phase ∧
    (∀ x : ℝ, 1 < x →
      ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ =
          x ^ rZeroRadialPosition p.zLaterMember / ‖zeroPoint ⟨p.zLaterMember, hL⟩‖ ∧
        x ^ rZeroRadialPosition p.zLaterMember < x ^ (1 / 2 : ℝ)) ∧
    (lineValue (rZeroHeight p.zEarlierMember) = 0 ∧
      ∀ t : ℝ, rZeroHeight p.zEarlierMember < t → t < rZeroHeight p.zLaterMember →
        lineValue t ≠ 0) ∧
    (∃ G : GrammaticalRaccord ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩,
      G.event = reconstructedEventAt (nZeroSourceIndex p.zLaterMember) ∧
      primalHistory (nZeroSourceIndex p.zLaterMember) =
        primalHistory (nZeroSourceIndex p.zEarlierMember) ++ [G.event]) ∧
    (∀ N : ℕ, 2 ≤ N → exactRemainder N = spectralRemainder N) ∧
    (∃ x : ℝ, 1 < x ∧ lineDeviation x ≠ 0) := by
  have hLow' : rZeroRadialPosition (⟨p.zLaterMember, hL⟩ : TrueZero).1 < 1 / 2 := hLow
  have hOffL : PIsOffCriticalLine (⟨p.zLaterMember, hL⟩ : TrueZero).1 := ne_of_lt hLow
  obtain ⟨G, _, hRec, hHist⟩ := globalRigidSystem.raccord p hE hL
  have hMir : radialFactor (mirrorMember ⟨p.zLaterMember, hL⟩) < 1 := by
    rw [radialFactor_lt_one_iff]
    have hr := mirrorMember_radial ⟨p.zLaterMember, hL⟩
    linarith
  refine ⟨⟨hV, by rw [hOn]; exact hLow⟩,
    ⟨rfl, (vertical_iff_pitch_contracts p hE hL).mp hV⟩,
    (contacts_height_determined_iff_onLine ⟨p.zEarlierMember, hE⟩).mpr hOn,
    ⟨(radialFactor_gt_one_iff ⟨p.zLaterMember, hL⟩).mpr hLow, hMir,
      fun k => contact_eq_line_mul_radial ⟨p.zLaterMember, hL⟩ k⟩,
    (linePhase_lt_phase_iff ⟨p.zLaterMember, hL⟩).mpr hLow,
    fun x hx => ⟨zeroTerm_norm (lt_trans one_pos hx),
      Real.rpow_lt_rpow_of_exponent_lt hx hLow⟩,
    ⟨lineValue_member_onLine _ hOn, fun t h1 h2 => lineValue_ne_zero_between p h1 h2⟩,
    ⟨G, hRec, hHist⟩, fun N hN => arithmetic_eq_spectral hN, off_member_deviates hOffL⟩

/-- **Le passage qui précède une entrée en régime horizontal depuis une chaîne verticale porte ce
registre** : sur trois passages consécutifs vertical, vertical, horizontal, le passage du milieu
part de la ligne, arrive sous la ligne, et ses contacts d'arrivée sont ceux que la hauteur seule
détermine multipliés par un facteur radial `> 1`. -/
theorem regime_entry_diagonal_ledger {o p q : TZeroPassage}
    (hJ₁ : o.zLaterMember = p.zEarlierMember) (hJ₂ : p.zLaterMember = q.zEarlierMember)
    (ho : VerticalPassage o) (hp : VerticalPassage p) (hq : HorizontalPassage q)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    (∀ k : ℤ, contactMinusAt ⟨p.zEarlierMember, hE⟩ k =
      lineContact (rZeroHeight p.zEarlierMember) k) ∧
    1 < radialFactor ⟨p.zLaterMember, hL⟩ ∧
    (∀ k : ℤ, contactMinusAt ⟨p.zLaterMember, hL⟩ k =
      lineContact (rZeroHeight p.zLaterMember) k * radialFactor ⟨p.zLaterMember, hL⟩) ∧
    (∀ t : ℝ, rZeroHeight p.zEarlierMember < t → t < rZeroHeight p.zLaterMember →
      lineValue t ≠ 0) := by
  obtain ⟨hOn, _, hLow, _⟩ := regime_entry_from_line hJ₁ hJ₂ ho hp hq
  obtain ⟨_, _, h3, ⟨h4, _, h5⟩, _, _, ⟨_, h7⟩, _⟩ :=
    diagonal_from_line_ledger p hE hL hp hOn hLow
  exact ⟨h3, h4, h5, h7⟩

#print axioms contact_eq_line_mul_radial
#print axioms radialFactor_eq_one_iff
#print axioms radialFactor_gt_one_iff
#print axioms radialFactor_lt_one_iff
#print axioms height_determined_radial_blind
#print axioms radial_sensitive_not_height_determined
#print axioms contacts_height_determined_iff_onLine
#print axioms vertical_exhausts_iff_arrival_onLine
#print axioms lineValue_ne_zero_between
#print axioms lineValue_sign_constant_between
#print axioms diagonal_from_line_ledger
#print axioms regime_entry_diagonal_ledger

end RHV6Fresh
