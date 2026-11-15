/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MeetingPoint
import RHV6Fresh.Terminal.TowerHierarchy
import RHV6Fresh.Terminal.CascadeContinuation
import RHV6Fresh.Terminal.MirrorEventCollision
import RHV6Fresh.Terminal.FixedGapRaccords
import RHV6Fresh.Terminal.PrimalEventRaccord

/-!
# RHV6Fresh — le porteur arithmétique d'un zéro OFF authentique (auteur, §19.8, 2026-10-30)

Module isolé (non importé par la chaîne, non ajouté à `RHV6Fresh.lean`). Point de départ : le zéro OFF, pas
un contrôle global. Aucune quantité statistique, aucune moyenne, aucune borne asymptotique ; les positions
sont exactes (premiers, contacts, décalages d'entrelacement).

## Objets

* **Porteur** (`OffCarrier`) : un premier changement de régime de l'énumération canonique, c'est-à-dire un
  rang `n` dont le membre est BAS (position radiale `< 1/2`) et dont tous les prédécesseurs sont ON. Si RH est
  fausse, un porteur existe (`exists_first_regime_break`) ; sous RH il n'en existe aucun.
* **Zéro OFF authentique** `C.zero = canonicalMember n` ; **passage d'arrivée** `C.arrival = canonicalPassage (n-1)` ;
  **passage sortant** `C.outgoing = canonicalPassage n`.
* **Les trois premiers consécutifs** `p_{n-1} < p_n < p_{n+1}` : occurrence du membre ON précédent, premier
  partagé du raccord d'arrivée (= occurrence du zéro OFF), premier partagé du raccord sortant (= premier minimal
  attendu du zéro OFF). Les deux écarts exacts sont `[p_{n-1}, p_n]` et `[p_n, p_{n+1}]`.

## Les trois contrôles au raccord, compilés

1. **Liaison (Obligation I)** : la rencontre de l'écart du zéro OFF, `[p_n, p_{n+1}]`, est à `p_{n+1}` et c'est
   exactement le premier partagé du raccord sortant ; tous les signaux s'y rencontrent (`liaison`).
2. **Lecture de la fréquence précédente** : au raccord d'arrivée, la fréquence monte strictement et les décalages
   d'entrelacement décroissent strictement (`previous_frequency_read`) — l'écart précédent a fixé la fréquence.
3. **Signature OFF au raccord sortant** : le pas sortant garde la hauteur (gel), ses décalages sont constants,
   son pas de Tour est conservé, la hiérarchie au raccord est brisée, et (dès la hauteur 2) l'énergie au premier
   partagé est strictement renversée (`outgoing_signature`). Le signal qui rencontre `p_{n+1}` n'apporte aucune
   fréquence nouvelle (`outgoing_no_new_frequency`).

## Composition de la cible (§5bis, §5ter, §5quater, §5quinquies, §5sexies, §5septies)

Au point de rencontre, le zéro OFF est sous l'amplitude de ligne, son miroir au-dessus, la paire au-dessus de deux
signaux de ligne, et les trois signaux sont deux à deux distincts au-delà de tout rang (§5bis). Le membre sortant est
pris dans la bande `]β, 1 − β]` : c'est le miroir, ou un zéro ON à la fréquence du zéro OFF, ou un second zéro OFF
(`outgoing_trichotomy`) ; dans le premier cas l'occurrence du miroir est exactement `p_{n+1}`. Le zéro OFF et le membre
sortant n'ont aucune rencontre lissée commune (§5ter) ; ce fait est consigné, pas transformé en contradiction.
Tout zéro à la fréquence du zéro OFF est dans la bande `[β, 1 − β]` ; dans le cas du miroir la fibre est exactement
la paire, le passage qui quitte le miroir remonte (cascade et hiérarchie reprises), et ce cas est exactement « le gel
dure un seul pas » ; hors de ce cas le gel dure au moins deux pas (§5quater).
Signature intégrée de la paire (§5quinquies, §19.12) : identité hyperbolique exacte de la paire moins deux signaux de
ligne (canal de comptage, forme réelle de l'auteur) ; quatre premiers consécutifs et télescopage sur les trois écarts ;
profil montée–gel–montée du cas (a) avec les trois événements canoniques ; transport vers le canal lissé compilé : la
cible lissée de tout écart est « paquet de la fréquence `T` » plus « autres fréquences », et dans le cas (a) le paquet
est exactement la paire et sa conjuguée. Identités de reconstruction, consignées ; aucune contradiction affirmée.
La cassure (§5sexies, §19.13) : la demande de l'écart est localisée dans la cassure terminale `log p_{n+1}` (plus
les pas intermédiaires, cassures aux seules puissances de premiers) ; la densité de la paire est `2cosh(dt)` fois la
densité de ligne, même calage exactement ; l'enveloppe du pas de la paire est explicite et dépasse strictement celle
de la ligne ; la cassure est réalisée par la totalité (compensation = autres fréquences). « La paire ne peut pas
réaliser la cassure à temps » n'est pas dérivable des éléments collectés ; ils établissent le contraire.
Le prochain point de rencontre (§5septies, §19.14) : dans le cas (a), le membre porté par `p_{n+2}` a une fréquence
strictement supérieure et n'est pas au-dessus d'un demi : il est ON, ou une seconde paire OFF qui gèle de nouveau et
dont l'amplitude relative n'est pas bornée. Aucune borne supérieure sur la fréquence suivante n'est compilée ;
« exactement ON » est la même frontière un pas plus loin.

## Ce qui reste : l'hypothèse nommée `ContinuationForced`

`ContinuationForced C` := le pas sortant monte (la rencontre à `p_{n+1}` exige une fréquence strictement
supérieure). Elle est **une définition étiquetée hypothèse, jamais un théorème**. Sous elle, le porteur est
contradictoire (`continuation_contradiction`). Exigée de tout porteur, elle équivaut à RH
(`continuationForced_iff_riemannHypothesis`) : c'est la forme locale exacte de la demande, sur un seul passage
et un seul premier. Elle est équivalente à la lecture au raccord sortant : décalages strictement décroissants
(`continuationForced_iff_reading`), et à la hiérarchie au raccord sortant (`continuationForced_iff_hierarchy`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **Le porteur** : un premier changement de régime de l'énumération canonique. -/
structure OffCarrier where
  /-- Rang canonique du zéro OFF authentique. -/
  n : ℕ
  /-- Le membre de rang `n` est bas. -/
  low : rZeroRadialPosition (canonicalMember n).1 < 1 / 2
  /-- Tout prédécesseur canonique est ON. -/
  hist : ∀ k < n, rZeroRadialPosition (canonicalMember k).1 = 1 / 2

/-- Si RH est fausse, un porteur existe. -/
theorem exists_offCarrier_of_not_riemannHypothesis (hNot : ¬ RiemannHypothesis) : Nonempty OffCarrier := by
  obtain ⟨n, hLow, hHist⟩ := exists_first_regime_break hNot
  exact ⟨⟨n, hLow, hHist⟩⟩

/-- Sous RH, aucun porteur. -/
theorem no_offCarrier_of_riemannHypothesis (hRH : RiemannHypothesis) (C : OffCarrier) : False := by
  have h := C.low
  rw [thm_zeroRadialPosition_half_of_riemannHypothesis hRH] at h
  exact lt_irrefl _ h

namespace OffCarrier

variable (C : OffCarrier)

/-! ## 1. Le zéro OFF authentique, son arrivée, son départ -/

/-- Le zéro OFF authentique. -/
noncomputable def zero : TrueZero := canonicalMember C.n

/-- Le passage d'arrivée : du dernier membre ON au zéro OFF. -/
noncomputable def arrival : TZeroPassage := canonicalPassage (C.n - 1)

/-- Le passage sortant : du zéro OFF au membre canonique suivant. -/
noncomputable def outgoing : TZeroPassage := canonicalPassage C.n

/-- Profil compilé du premier changement de régime (ancre ON). -/
theorem profile :
    1 ≤ C.n ∧
    0 < rZeroHeight C.arrival.zEarlierMember ∧
    rZeroRadialPosition C.arrival.zEarlierMember = 1 / 2 ∧
    C.arrival.zLaterMember = C.zero.1 ∧
    VerticalPassage C.arrival ∧
    (∀ w : TrueZero, PZeroMemberPrecedes w.1 C.zero.1 → rZeroRadialPosition w.1 = 1 / 2) ∧
    (∀ T : ℝ, T < rZeroHeight C.zero.1 → lowCount T = 0 ∧ upperCountWithMultiplicity T = onCount T) ∧
    1 ≤ lowCount (rZeroHeight C.zero.1) ∧
    PZeroMemberPrecedes C.zero.1 (mirrorMember C.zero).1 :=
  first_regime_break_profile anchor_canonical_one C.low C.hist

theorem one_le_n : 1 ≤ C.n := C.profile.1

theorem zero_low : rZeroRadialPosition C.zero.1 < 1 / 2 := C.low

theorem zero_index : nZeroSourceIndex C.zero.1 = C.n := canonicalMember_index C.n

theorem arrival_later : C.arrival.zLaterMember = C.zero.1 := C.profile.2.2.2.1

theorem arrival_earlier_onLine : rZeroRadialPosition C.arrival.zEarlierMember = 1 / 2 := C.profile.2.2.1

theorem arrival_vertical : VerticalPassage C.arrival := C.profile.2.2.2.2.1

theorem history_onLine : ∀ w : TrueZero, PZeroMemberPrecedes w.1 C.zero.1 → rZeroRadialPosition w.1 = 1 / 2 :=
  C.profile.2.2.2.2.2.1

theorem outgoing_earlier : C.outgoing.zEarlierMember = C.zero.1 := rfl

theorem arrival_earlier_pos : 0 < rZeroHeight C.arrival.zEarlierMember := C.profile.2.1

theorem arrival_later_pos : 0 < rZeroHeight C.arrival.zLaterMember := by
  rw [C.arrival_later]; exact C.zero.2

theorem outgoing_earlier_pos : 0 < rZeroHeight C.outgoing.zEarlierMember := C.zero.2

theorem outgoing_later_pos : 0 < rZeroHeight C.outgoing.zLaterMember := (canonicalMember (C.n + 1)).2

/-- **Le pas sortant est gelé** : même hauteur (passage horizontal) et décalages d'entrelacement constants. -/
theorem outgoing_frozen :
    HorizontalPassage C.outgoing ∧ ∀ k : ℤ,
      interlacingOffset ⟨C.outgoing.zEarlierMember, C.outgoing_earlier_pos⟩
          ⟨C.outgoing.zLaterMember, C.outgoing_later_pos⟩ (k + 1) =
        interlacingOffset ⟨C.outgoing.zEarlierMember, C.outgoing_earlier_pos⟩
          ⟨C.outgoing.zLaterMember, C.outgoing_later_pos⟩ k :=
  low_arrival_freezes_cascade (p := C.arrival) (q := C.outgoing) C.arrival_later C.arrival_vertical
    (C.arrival_later ▸ C.low) C.outgoing_earlier_pos C.outgoing_later_pos

theorem outgoing_horizontal : HorizontalPassage C.outgoing := C.outgoing_frozen.1

/-- **Le signal qui suit n'apporte aucune fréquence nouvelle** : même fréquence que le zéro OFF. -/
theorem outgoing_no_new_frequency : zeroFrequency C.outgoing.zLaterMember = zeroFrequency C.zero.1 :=
  C.outgoing_horizontal.symm

/-- Le membre suivant est strictement plus à droite radialement (seul profil d'un passage à fréquence partagée). -/
theorem outgoing_radial_lt : rZeroRadialPosition C.zero.1 < rZeroRadialPosition C.outgoing.zLaterMember :=
  horizontalPassage_radial_lt C.outgoing_horizontal

/-! ## 2. Les deux raccords et les trois premiers consécutifs -/

/-- Le raccord d'arrivée (unique, tous champs fixés). -/
noncomputable def arrivalRaccord :
    TowerRaccord ⟨C.arrival.zEarlierMember, C.arrival_earlier_pos⟩ ⟨C.arrival.zLaterMember, C.arrival_later_pos⟩ :=
  towerRaccordOf C.arrival C.arrival_earlier_pos C.arrival_later_pos

/-- Le raccord sortant (unique, tous champs fixés). -/
noncomputable def outgoingRaccord :
    TowerRaccord ⟨C.outgoing.zEarlierMember, C.outgoing_earlier_pos⟩ ⟨C.outgoing.zLaterMember, C.outgoing_later_pos⟩ :=
  towerRaccordOf C.outgoing C.outgoing_earlier_pos C.outgoing_later_pos

/-- Occurrence du zéro OFF : `p_n`. -/
theorem zero_occurrence : occurrence C.zero = fnPrimeAtRank C.n := by
  rw [occurrence_eq_primeAtRank, zero_index]

/-- Premier minimal attendu du zéro OFF : `p_{n+1}`. -/
theorem zero_expectedMinimumPrime : expectedMinimumPrime C.zero = fnPrimeAtRank (C.n + 1) := by
  unfold expectedMinimumPrime; rw [zero_index]; rfl

/-- Occurrence du dernier membre ON : `p_{n-1}`. -/
theorem arrival_earlier_occurrence :
    occurrence ⟨C.arrival.zEarlierMember, C.arrival_earlier_pos⟩ = fnPrimeAtRank (C.n - 1) := by
  exact (occurrence_eq_primeAtRank _).trans (congrArg fnPrimeAtRank (canonicalMember_index (C.n - 1)))

/-- Premier partagé du raccord d'arrivée : l'occurrence du zéro OFF, `p_n`. -/
theorem arrivalRaccord_M : C.arrivalRaccord.M = fnPrimeAtRank C.n := by
  rw [C.arrivalRaccord.entry_eq]
  exact (occurrence_eq_primeAtRank _).trans
    (congrArg fnPrimeAtRank ((congrArg nZeroSourceIndex C.arrival_later).trans C.zero_index))

/-- Premier partagé du raccord sortant : le premier minimal attendu du zéro OFF, `p_{n+1}`. -/
theorem outgoingRaccord_M : C.outgoingRaccord.M = fnPrimeAtRank (C.n + 1) := by
  rw [C.outgoingRaccord.exit_eq]
  exact C.zero_expectedMinimumPrime

/-- **Les trois premiers consécutifs du porteur** `p_{n-1} < p_n < p_{n+1}`. -/
theorem carrier_primes :
    occurrence ⟨C.arrival.zEarlierMember, C.arrival_earlier_pos⟩ = fnPrimeAtRank (C.n - 1) ∧
    C.arrivalRaccord.M = fnPrimeAtRank C.n ∧
    C.outgoingRaccord.M = fnPrimeAtRank (C.n + 1) ∧
    fnPrimeAtRank (C.n - 1) < fnPrimeAtRank C.n ∧ fnPrimeAtRank C.n < fnPrimeAtRank (C.n + 1) :=
  ⟨C.arrival_earlier_occurrence, C.arrivalRaccord_M, C.outgoingRaccord_M,
    thm_primeAtRank_strictMono (by have := C.one_le_n; omega),
    thm_primeAtRank_strictMono (Nat.lt_succ_self _)⟩

/-! ## 3. Contrôle 1 — la liaison : la rencontre obligatoire de l'écart du zéro OFF -/

/-- L'écart du zéro OFF : `[p_n, p_{n+1}]`. -/
def gap : PrimeGapInterval := ⟨C.n⟩

/-- L'écart précédent : `[p_{n-1}, p_n]`. -/
def previousGap : PrimeGapInterval := ⟨C.n - 1⟩

theorem gap_lower : C.gap.lower = (occurrence C.zero : ℝ) := by
  unfold PrimeGapInterval.lower gap; rw [zero_occurrence]

/-- **Liaison** : le point de rencontre de l'écart du zéro OFF est le premier partagé du raccord sortant, et tous les
signaux s'y rencontrent (synchronisation compilée). -/
theorem liaison :
    meetingPoint C.gap = (C.outgoingRaccord.M : ℝ) ∧
    localArithmeticTarget C.gap = ∑' ρ : ExplicitIndex, smoothedLocalContribution ρ C.gap := by
  refine ⟨?_, all_signals_meet C.gap⟩
  rw [meetingPoint_eq_upper, outgoingRaccord_M]; rfl

/-- La rencontre de l'écart précédent est l'occurrence du zéro OFF, premier partagé du raccord d'arrivée. -/
theorem previous_liaison : meetingPoint C.previousGap = (C.arrivalRaccord.M : ℝ) := by
  rw [meetingPoint_eq_upper, arrivalRaccord_M]
  unfold previousGap
  have := C.one_le_n
  simp only
  congr 2
  omega

/-! ## 4. Contrôle 2 — la lecture de la fréquence précédente au raccord d'arrivée -/

/-- **Lecture de la fréquence précédente** : au raccord d'arrivée, la fréquence monte strictement et les décalages
d'entrelacement décroissent strictement à tout indice. L'écart précédent a fixé la fréquence du zéro OFF. -/
theorem previous_frequency_read :
    zeroFrequency C.arrival.zEarlierMember < zeroFrequency C.zero.1 ∧
    ∀ k : ℤ, interlacingOffset ⟨C.arrival.zEarlierMember, C.arrival_earlier_pos⟩
        ⟨C.arrival.zLaterMember, C.arrival_later_pos⟩ (k + 1) <
      interlacingOffset ⟨C.arrival.zEarlierMember, C.arrival_earlier_pos⟩
        ⟨C.arrival.zLaterMember, C.arrival_later_pos⟩ k :=
  ⟨C.arrival_later ▸ C.arrival_vertical, fun k =>
    (cascade_step_rises_iff C.arrival C.arrival_earlier_pos C.arrival_later_pos k).mpr C.arrival_vertical⟩

/-- Le raccord d'arrivée est orienté et la hiérarchie y tient (dès la hauteur 2) : l'arrivée du zéro OFF est
invisible à l'amplitude seule — c'est le no-go connu, consigné. -/
theorem arrival_hierarchy (hT2 : 2 ≤ rZeroHeight C.zero.1) :
    RaccordHierarchy C.arrival C.arrival_earlier_pos C.arrival_later_pos :=
  raccordHierarchy_of_height_advance C.arrival C.arrival_earlier_pos C.arrival_later_pos C.arrival_vertical
    (C.arrival_later ▸ hT2)

/-! ## 5. Contrôle 3 — la signature OFF au raccord sortant -/

/-- **Signature du zéro OFF à son raccord sortant** : pas de Tour conservé, hiérarchie brisée, et dès la hauteur 2
l'énergie au premier partagé `p_{n+1}` est strictement renversée (le suivant lit plus d'énergie que le zéro OFF). -/
theorem outgoing_signature :
    towerPitch ⟨C.outgoing.zLaterMember, C.outgoing_later_pos⟩ =
        towerPitch ⟨C.outgoing.zEarlierMember, C.outgoing_earlier_pos⟩ ∧
    (2 ≤ rZeroHeight C.zero.1 →
      ‖zeroTerm ⟨C.outgoing.zEarlierMember, C.outgoing_earlier_pos⟩ C.outgoingRaccord.M‖ <
        ‖zeroTerm ⟨C.outgoing.zLaterMember, C.outgoing_later_pos⟩ C.outgoingRaccord.M‖) ∧
    ¬ RaccordHierarchy C.outgoing C.outgoing_earlier_pos C.outgoing_later_pos :=
  sameHeight_breaks_hierarchy C.outgoing C.outgoing_earlier_pos C.outgoing_later_pos C.outgoing_horizontal

/-- Le miroir du zéro OFF garde l'événement de hauteur, le suit strictement, et son occurrence est strictement
au-dessus : on n'égale jamais les deux occurrences. -/
theorem mirror_facts :
    tZeroHeightEvent (mirrorMember C.zero) = tZeroHeightEvent C.zero ∧
    PZeroMemberPrecedes C.zero.1 (mirrorMember C.zero).1 ∧
    occurrence C.zero < occurrence (mirrorMember C.zero) :=
  ⟨mirror_sameHeightEvent C.zero, C.profile.2.2.2.2.2.2.2.2, mirror_occurrence_strict C.low⟩

/-! ## 5bis. Amplitude et rigidité au point de rencontre (révision de E301 ; décision de l'auteur, 2026-10-30)

L'auteur déclare FAUSSES les conclusions de E301 (« rien de compilé ne distingue OFF de ON »). Ce que la bibliothèque
compilée dit au contraire, composé ici sur le porteur, au point de rencontre `p_{n+1}` de l'écart du zéro OFF :
* à fréquence identique, le signal OFF n'est PAS le signal ON : amplitude strictement sous la ligne pour le zéro,
  strictement au-dessus pour son miroir, et la paire (zéro, miroir) dépasse strictement la paire de ligne ;
* le zéro OFF, son miroir et le point de ligne de même fréquence sont trois signaux deux à deux distincts sur les
  écarts premiers au-delà de tout rang (rigidité des contributions individuelles, raccords fixés).
Ces faits sont des THÉORÈMES. Ils n'affirment pas, à eux seuls, la continuation forcée ; ils ne l'excluent pas non
plus : leur composition avec la rencontre obligatoire reste la frontière (§6). -/

/-- Le décalage radial du zéro OFF : `d = 1/2 − β > 0`. -/
noncomputable def radialShift : ℝ := 1 / 2 - rZeroRadialPosition C.zero.1

theorem radialShift_pos : 0 < C.radialShift := by
  unfold radialShift; linarith [C.zero_low]

theorem zero_radial_eq : rZeroRadialPosition C.zero.1 = 1 / 2 - C.radialShift := by
  unfold radialShift; ring

theorem mirror_radial_eq : rZeroRadialPosition (mirrorMember C.zero).1 = 1 / 2 + C.radialShift := by
  rw [mirrorMember_radial]; unfold radialShift; ring

/-- **Amplitude du zéro OFF au point de rencontre** : strictement sous l'amplitude de ligne de même fréquence. -/
theorem zero_amplitude_below_line_at_meeting :
    ‖(meetingPoint C.gap : ℂ) ^ (zeroPoint C.zero - 1)‖ < (meetingPoint C.gap) ^ (-(1 / 2) : ℝ) := by
  have hx : 1 < meetingPoint C.gap := one_lt_meetingPoint C.gap
  rw [zeroTerm_density_norm C.zero (by linarith)]
  exact Real.rpow_lt_rpow_of_exponent_lt hx (by linarith [C.zero_low])

/-- **Amplitude du miroir au point de rencontre** : strictement au-dessus de l'amplitude de ligne. -/
theorem mirror_amplitude_above_line_at_meeting :
    (meetingPoint C.gap) ^ (-(1 / 2) : ℝ) <
      ‖(meetingPoint C.gap : ℂ) ^ (zeroPoint (mirrorMember C.zero) - 1)‖ := by
  have hx : 1 < meetingPoint C.gap := one_lt_meetingPoint C.gap
  rw [zeroTerm_density_norm _ (by linarith), mirrorMember_radial]
  exact Real.rpow_lt_rpow_of_exponent_lt hx (by linarith [C.zero_low])

/-- **La paire OFF dépasse la paire de ligne au point de rencontre** : le zéro OFF et son miroir, à la même
fréquence, ont ensemble une amplitude strictement supérieure à deux signaux de ligne. -/
theorem pair_amplitude_exceeds_line_at_meeting :
    2 * (meetingPoint C.gap) ^ (-(1 / 2) : ℝ) <
      ‖(meetingPoint C.gap : ℂ) ^ (zeroPoint C.zero - 1)‖ +
        ‖(meetingPoint C.gap : ℂ) ^ (zeroPoint (mirrorMember C.zero) - 1)‖ :=
  off_pair_density_exceeds_line C.zero (mirrorMember C.zero) (one_lt_meetingPoint C.gap)
    C.radialShift_pos.ne' C.zero_radial_eq C.mirror_radial_eq

/-- Rigidité : les raccords du zéro OFF sont fixés. -/
theorem zero_fixedRaccords : FixedRaccords (zeroPoint C.zero) := trueZero_fixedRaccords C.zero

/-- Rigidité : les raccords du miroir sont fixés. -/
theorem mirror_fixedRaccords : FixedRaccords (zeroPoint (mirrorMember C.zero)) :=
  trueZero_fixedRaccords (mirrorMember C.zero)

/-- **Le signal OFF n'est pas le signal de ligne de même fréquence** : ils diffèrent sur un écart premier au-delà
de tout rang. -/
theorem zero_signal_ne_line_signal (n₀ : ℕ) :
    ∃ n, n₀ ≤ n ∧ primeGapContribution (zeroPoint C.zero) n ≠
      primeGapContribution ((1 / 2 : ℂ) + (rZeroHeight C.zero.1 : ℂ) * Complex.I) n := by
  have hz : 0 < (zeroPoint C.zero).im := C.zero.2
  refine distinct_points_differ_beyond_any_rank (zeroPoint_re_pos C.zero) (by norm_num) hz
    (by simpa [zeroPoint_im] using hz) ?_ n₀
  intro he
  have := congrArg Complex.re he
  simp [zeroPoint_re] at this
  linarith [C.zero_low]

/-- **Le miroir n'est pas non plus le signal de ligne** de même fréquence. -/
theorem mirror_signal_ne_line_signal (n₀ : ℕ) :
    ∃ n, n₀ ≤ n ∧ primeGapContribution (zeroPoint (mirrorMember C.zero)) n ≠
      primeGapContribution ((1 / 2 : ℂ) + (rZeroHeight C.zero.1 : ℂ) * Complex.I) n := by
  have hz : 0 < (zeroPoint (mirrorMember C.zero)).im := (mirrorMember C.zero).2
  have hz' : 0 < rZeroHeight C.zero.1 := by
    have := hz; rw [zeroPoint_im, mirrorMember_ordinate] at this; exact this
  refine distinct_points_differ_beyond_any_rank (zeroPoint_re_pos _) (by norm_num) hz
    (by simpa using hz') ?_ n₀
  intro he
  have := congrArg Complex.re he
  simp [zeroPoint_re, mirrorMember_radial] at this
  linarith [C.zero_low]

/-- **Le zéro OFF et son miroir sont deux signaux distincts** sur les écarts premiers au-delà de tout rang. -/
theorem zero_signal_ne_mirror_signal (n₀ : ℕ) :
    ∃ n, n₀ ≤ n ∧ primeGapContribution (zeroPoint C.zero) n ≠
      primeGapContribution (zeroPoint (mirrorMember C.zero)) n := by
  refine distinct_points_differ_beyond_any_rank (zeroPoint_re_pos _) (zeroPoint_re_pos _)
    C.zero.2 (mirrorMember C.zero).2 ?_ n₀
  intro he
  have := congrArg Complex.re he
  simp [zeroPoint_re, mirrorMember_radial] at this
  linarith [C.zero_low]

/-! ## 5ter. Le membre sortant est pris dans la bande du zéro OFF et de son miroir (cible §19.9.5, 2026-10-30)

Composition de la cible avec l'ordre canonique et la rencontre obligatoire. Faits exacts, locaux, sans moyenne :
le membre qui rencontre `p_{n+1}` est consécutif au zéro OFF, à sa fréquence, et sa position radiale est prise dans
`]β, 1 − β]` ; au-dessus d'un demi il ne peut être que le miroir (sinon son propre miroir s'intercalerait, contre la
consécutivité). Trichotomie compilée : le miroir lui-même, un zéro ON à la fréquence du zéro OFF, ou un second zéro OFF
strictement entre `β` et un demi. Dans le premier cas, l'occurrence du miroir est exactement le point de rencontre de
l'écart du zéro OFF. Enfin, le zéro OFF et le membre sortant, à fréquence partagée, n'ont aucune rencontre lissée commune,
alors que l'écart leur impose une rencontre unique à `p_{n+1}` : la rencontre lissée n'est pas la rencontre arithmétique,
et cette non-coïncidence est consignée, pas transformée en contradiction. -/

/-- Le membre sortant est le membre canonique suivant : consécutif au zéro OFF. -/
theorem outgoing_consecutive : PZeroMembersConsecutive C.zero.1 C.outgoing.zLaterMember :=
  canonicalMember_consecutive C.n

/-- Le membre sortant a la hauteur du zéro OFF (lecture directe du gel). -/
theorem outgoing_same_height : rZeroHeight C.outgoing.zLaterMember = rZeroHeight C.zero.1 :=
  C.outgoing_horizontal.symm

/-- Le membre sortant comme vrai zéro. -/
noncomputable def outgoingMember : TrueZero := ⟨C.outgoing.zLaterMember, C.outgoing_later_pos⟩

theorem outgoingMember_val : (C.outgoingMember).1 = C.outgoing.zLaterMember := rfl

/-- **Le membre sortant ne dépasse pas le miroir** : `β < β' ≤ 1 − β`. -/
theorem outgoing_radial_le_mirror :
    rZeroRadialPosition C.outgoing.zLaterMember ≤ rZeroRadialPosition (mirrorMember C.zero).1 := by
  rw [mirrorMember_radial]
  exact fiberSuccessor_radial_le_mirror (z := C.zero) (z' := C.outgoingMember) C.low C.outgoing_same_height
    C.outgoing_consecutive

/-- **Au-dessus d'un demi, le membre sortant est le miroir** : sinon le miroir du membre sortant, de même hauteur et de
position radiale strictement entre `β` et `β'`, s'intercalerait entre le zéro OFF et lui. -/
theorem outgoing_eq_mirror_of_high (h : 1 / 2 < rZeroRadialPosition C.outgoing.zLaterMember) :
    C.outgoing.zLaterMember = (mirrorMember C.zero).1 := by
  by_contra hne
  have hle := C.outgoing_radial_le_mirror
  rw [mirrorMember_radial] at hle
  have hlt : rZeroRadialPosition C.outgoing.zLaterMember < 1 - rZeroRadialPosition C.zero.1 := by
    rcases lt_or_eq_of_le hle with h' | h'
    · exact h'
    · exfalso
      apply hne
      apply thm_zero_identity_of_sameSupport
      apply Complex.ext
      · show rZeroRadialPosition C.outgoing.zLaterMember = rZeroRadialPosition (mirrorMember C.zero).1
        rw [mirrorMember_radial]; exact h'
      · show rZeroHeight C.outgoing.zLaterMember = rZeroHeight (mirrorMember C.zero).1
        rw [mirrorMember_ordinate]; exact C.outgoing_same_height
  have hmR : rZeroRadialPosition (mirrorMember C.outgoingMember).1 = 1 - rZeroRadialPosition C.outgoing.zLaterMember :=
    mirrorMember_radial C.outgoingMember
  have hmH : rZeroHeight (mirrorMember C.outgoingMember).1 = rZeroHeight C.outgoing.zLaterMember :=
    mirrorMember_ordinate C.outgoingMember
  apply C.outgoing_consecutive.2
  refine ⟨(mirrorMember C.outgoingMember).1, ?_, ?_⟩
  · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    refine ⟨?_, ?_⟩
    · rw [hmH]; exact C.outgoing_same_height.symm
    · rw [hmR]; linarith
  · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    refine ⟨hmH, ?_⟩
    rw [hmR]; linarith

/-- **Trichotomie du membre sortant** : le miroir, ou un zéro ON à la fréquence du zéro OFF, ou un second zéro OFF
strictement entre `β` et un demi. -/
theorem outgoing_trichotomy :
    C.outgoing.zLaterMember = (mirrorMember C.zero).1 ∨
    rZeroRadialPosition C.outgoing.zLaterMember = 1 / 2 ∨
    (rZeroRadialPosition C.zero.1 < rZeroRadialPosition C.outgoing.zLaterMember ∧
      rZeroRadialPosition C.outgoing.zLaterMember < 1 / 2) := by
  rcases lt_trichotomy (rZeroRadialPosition C.outgoing.zLaterMember) (1 / 2) with h | h | h
  · exact Or.inr (Or.inr ⟨C.outgoing_radial_lt, h⟩)
  · exact Or.inr (Or.inl h)
  · exact Or.inl (C.outgoing_eq_mirror_of_high h)

/-- **Si le membre sortant est le miroir, l'occurrence du miroir est le point de rencontre de l'écart du zéro OFF** :
`p_{n+1}` exactement. -/
theorem mirror_occurrence_eq_meeting (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    (occurrence (mirrorMember C.zero) : ℝ) = meetingPoint C.gap := by
  have hEq : mirrorMember C.zero = canonicalMember (C.n + 1) := Subtype.ext h.symm
  rw [hEq, occurrence_eq_primeAtRank, canonicalMember_index, meetingPoint_eq_upper]
  rfl

/-- Dans les deux autres cas, l'occurrence du miroir est strictement au-delà du point de rencontre. -/
theorem mirror_occurrence_gt_meeting (h : C.outgoing.zLaterMember ≠ (mirrorMember C.zero).1) :
    meetingPoint C.gap < (occurrence (mirrorMember C.zero) : ℝ) := by
  have hpre : PZeroMemberPrecedes C.outgoing.zLaterMember (mirrorMember C.zero).1 := by
    have hle := C.outgoing_radial_le_mirror
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
      right
      exact ⟨by rw [mirrorMember_ordinate]; exact C.outgoing_same_height, hlt⟩
    · exfalso
      apply h
      apply thm_zero_identity_of_sameSupport
      apply Complex.ext
      · exact heq
      · show rZeroHeight C.outgoing.zLaterMember = rZeroHeight (mirrorMember C.zero).1
        rw [mirrorMember_ordinate]; exact C.outgoing_same_height
  have hidx := thm_zeroSourceIndex_strictMono C.outgoing_later_pos hpre
  rw [show C.outgoing.zLaterMember = (canonicalMember (C.n + 1)).1 from rfl, canonicalMember_index] at hidx
  rw [occurrence_eq_primeAtRank, meetingPoint_eq_upper]
  exact_mod_cast thm_primeAtRank_strictMono hidx

/-- **Aucune rencontre lissée commune** : le zéro OFF et le membre sortant, à fréquence partagée, n'ont aucun point de
rencontre lissée en commun, à aucun couple d'indices — alors que l'écart `[p_n, p_{n+1}]` leur impose à tous deux la
rencontre arithmétique unique à `p_{n+1}` (`liaison`). Les deux notions de rencontre ne coïncident pas ; ce fait est
consigné, il n'est pas une contradiction. -/
theorem outgoing_no_common_smoothed_meeting (k k' : ℤ) :
    smoothedMeeting (zeroPoint C.zero) k ≠ smoothedMeeting (zeroPoint C.outgoingMember) k' :=
  shared_frequency_no_common_meeting C.zero C.outgoingMember C.outgoing_same_height.symm
    C.outgoing_radial_lt k k'

/-- **Amplitude du membre sortant au point de rencontre** : strictement au-dessus de celle du zéro OFF, à la même
fréquence (position radiale strictement plus grande, point strictement supérieur à un). -/
theorem outgoing_amplitude_gt_zero_at_meeting :
    ‖(meetingPoint C.gap : ℂ) ^ (zeroPoint C.zero - 1)‖ <
      ‖(meetingPoint C.gap : ℂ) ^ (zeroPoint C.outgoingMember - 1)‖ := by
  have hx : 0 < meetingPoint C.gap := by linarith [one_lt_meetingPoint C.gap]
  rw [zeroTerm_density_norm C.zero hx, zeroTerm_density_norm C.outgoingMember hx]
  have hr : rZeroRadialPosition C.zero.1 < rZeroRadialPosition C.outgoingMember.1 := C.outgoing_radial_lt
  exact Real.rpow_lt_rpow_of_exponent_lt (one_lt_meetingPoint C.gap) (by linarith)

/-! ## 5quater. La fibre de la fréquence du zéro OFF ; reprise de la cascade après le miroir (cas (a), 2026-10-30)

Confirmation de l'auteur : la position radiale au-dessus d'un demi est déjà exclue pour le premier zéro hors ligne
(`later_le_half_of_history_onLine`, `exists_first_regime_break`), et « un OFF reproduit un ON » est réfuté au
compilateur (§5bis). Le régime ON est engagé et certifié jusqu'au zéro OFF (`history_onLine`, `arrival_vertical`).

Compilé ici, exact et local : (i) tout zéro à la fréquence du zéro OFF a sa position radiale dans `[β, 1 − β]` (à gauche,
il précéderait le zéro OFF et serait ON ; à droite, son miroir le ferait) ; (ii) dans le cas (a), la fibre de la fréquence
est exactement la paire `{z, z*}` ; (iii) dans le cas (a), le passage qui quitte le miroir **remonte** : la cascade
reprend, les décalages décroissent de nouveau strictement, la hiérarchie tient de nouveau (dès la hauteur 2) — le gel est
exactement un pas, l'écart `[p_n, p_{n+1}]` est le seul écart reconstitué sans fréquence nouvelle entre deux écarts qui
en apportent une ; (iv) hors du cas (a), le passage qui quitte le membre sortant est encore gelé (le miroir attend) :
le gel dure au moins deux pas. Le cas (a) est donc exactement « le gel dure un seul pas ». -/

/-- Aucun zéro à la fréquence du zéro OFF n'est strictement à sa gauche : il le précéderait et serait ON. -/
theorem fiber_radial_ge (w : TrueZero) (hw : rZeroHeight w.1 = rZeroHeight C.zero.1) :
    rZeroRadialPosition C.zero.1 ≤ rZeroRadialPosition w.1 := by
  by_contra hlt
  push_neg at hlt
  have hpre : PZeroMemberPrecedes w.1 C.zero.1 := by
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    exact ⟨hw, hlt⟩
  have hOn := C.history_onLine w hpre
  linarith [C.zero_low]

/-- Aucun zéro à cette fréquence n'est strictement à droite du miroir : son propre miroir serait à gauche du zéro OFF. -/
theorem fiber_radial_le (w : TrueZero) (hw : rZeroHeight w.1 = rZeroHeight C.zero.1) :
    rZeroRadialPosition w.1 ≤ rZeroRadialPosition (mirrorMember C.zero).1 := by
  rw [mirrorMember_radial]
  have h := C.fiber_radial_ge (mirrorMember w) (by rw [mirrorMember_ordinate]; exact hw)
  rw [mirrorMember_radial] at h
  linarith

/-- **La bande de la fibre** : tout zéro à la fréquence du zéro OFF a sa position radiale entre `β` et `1 − β`. -/
theorem fiber_band (w : TrueZero) (hw : rZeroHeight w.1 = rZeroHeight C.zero.1) :
    rZeroRadialPosition C.zero.1 ≤ rZeroRadialPosition w.1 ∧
      rZeroRadialPosition w.1 ≤ 1 - rZeroRadialPosition C.zero.1 := by
  refine ⟨C.fiber_radial_ge w hw, ?_⟩
  have := C.fiber_radial_le w hw
  rwa [mirrorMember_radial] at this

/-- **Cas (a) : la fibre de la fréquence est exactement la paire** zéro OFF et miroir. -/
theorem fiber_eq_pair_of_mirror (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1)
    (w : TrueZero) (hw : rZeroHeight w.1 = rZeroHeight C.zero.1) :
    w = C.zero ∨ w = mirrorMember C.zero := by
  rcases lt_trichotomy (rZeroRadialPosition w.1) (rZeroRadialPosition C.zero.1) with hlt | heq | hgt
  · exact absurd hlt (not_lt.mpr (C.fiber_radial_ge w hw))
  · left
    exact Subtype.ext (thm_zero_identity_of_sameSupport (Complex.ext heq hw))
  · have hle := C.fiber_radial_le w hw
    rcases lt_or_eq_of_le hle with hlt' | heq'
    · exfalso
      apply C.outgoing_consecutive.2
      refine ⟨w.1, ?_, ?_⟩
      · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
        right
        exact ⟨hw.symm, hgt⟩
      · rw [thm_zeroMemberPrecedes_iff_height_radial_lex, h]
        right
        exact ⟨by rw [mirrorMember_ordinate]; exact hw, hlt'⟩
    · right
      have hH : rZeroHeight w.1 = rZeroHeight (mirrorMember C.zero).1 := by
        rw [mirrorMember_ordinate]; exact hw
      exact Subtype.ext (thm_zero_identity_of_sameSupport (Complex.ext heq' hH))

/-- Le passage qui quitte le membre sortant : du membre de rang `n + 1` au membre de rang `n + 2`. -/
noncomputable def postPassage : TZeroPassage := canonicalPassage (C.n + 1)

theorem postPassage_earlier : C.postPassage.zEarlierMember = C.outgoing.zLaterMember := rfl

theorem postPassage_earlier_pos : 0 < rZeroHeight C.postPassage.zEarlierMember := C.outgoing_later_pos

theorem postPassage_later_pos : 0 < rZeroHeight C.postPassage.zLaterMember :=
  (canonicalMember (C.n + 1 + 1)).2

theorem postPassage_earlier_height : rZeroHeight C.postPassage.zEarlierMember = rZeroHeight C.zero.1 :=
  C.outgoing_same_height

/-- Hors du cas (a), le membre sortant précède le miroir. -/
theorem outgoing_precedes_mirror_of_ne (h : C.outgoing.zLaterMember ≠ (mirrorMember C.zero).1) :
    PZeroMemberPrecedes C.outgoing.zLaterMember (mirrorMember C.zero).1 := by
  have hle := C.outgoing_radial_le_mirror
  rcases lt_or_eq_of_le hle with hlt | heq
  · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    exact ⟨by rw [mirrorMember_ordinate]; exact C.outgoing_same_height, hlt⟩
  · exfalso
    apply h
    apply thm_zero_identity_of_sameSupport
    apply Complex.ext
    · exact heq
    · show rZeroHeight C.outgoing.zLaterMember = rZeroHeight (mirrorMember C.zero).1
      rw [mirrorMember_ordinate]; exact C.outgoing_same_height

/-- **Cas (a) : après le miroir, la fréquence remonte.** Le passage qui quitte le miroir est vertical : s'il gardait la
hauteur, son membre postérieur serait à la fréquence du zéro OFF et strictement à droite du miroir, hors de la bande. -/
theorem post_mirror_vertical (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    VerticalPassage C.postPassage := by
  rcases passage_regime_dichotomy C.postPassage with ⟨hV, _⟩ | ⟨hH, _⟩
  · exact hV
  · exfalso
    have hr := horizontalPassage_radial_lt hH
    have hH' : rZeroHeight C.postPassage.zEarlierMember = rZeroHeight C.postPassage.zLaterMember := hH
    have hw : rZeroHeight C.postPassage.zLaterMember = rZeroHeight C.zero.1 := by
      rw [← hH']; exact C.postPassage_earlier_height
    have hle := C.fiber_radial_le ⟨C.postPassage.zLaterMember, C.postPassage_later_pos⟩ hw
    rw [postPassage_earlier, h] at hr
    exact absurd hle (not_le.mpr hr)

/-- **Hors du cas (a), le gel continue** : le passage qui quitte le membre sortant garde encore la hauteur, car le miroir,
à la même fréquence, suit le membre sortant et précéderait tout membre de hauteur supérieure. -/
theorem post_horizontal_of_ne (h : C.outgoing.zLaterMember ≠ (mirrorMember C.zero).1) :
    HorizontalPassage C.postPassage := by
  rcases passage_regime_dichotomy C.postPassage with ⟨hV, _⟩ | ⟨hH, _⟩
  · exfalso
    apply (canonicalMember_consecutive (C.n + 1)).2
    refine ⟨(mirrorMember C.zero).1, C.outgoing_precedes_mirror_of_ne h, ?_⟩
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    left
    have hV' : rZeroHeight C.postPassage.zEarlierMember < rZeroHeight C.postPassage.zLaterMember := hV
    rw [C.postPassage_earlier_height] at hV'
    rw [mirrorMember_ordinate]
    exact hV'
  · exact hH

/-- **Le cas (a) est exactement « le gel dure un seul pas »** : le passage qui quitte le membre sortant remonte si et
seulement si le membre sortant est le miroir. -/
theorem post_vertical_iff_mirror :
    VerticalPassage C.postPassage ↔ C.outgoing.zLaterMember = (mirrorMember C.zero).1 := by
  constructor
  · intro hV
    by_contra hne
    exact absurd (C.post_horizontal_of_ne hne) (ne_of_lt hV)
  · exact C.post_mirror_vertical

/-- **Cas (a) : la cascade reprend après le miroir** : les décalages d'entrelacement décroissent de nouveau strictement. -/
theorem post_mirror_cascade_resumes (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) (k : ℤ) :
    interlacingOffset ⟨C.postPassage.zEarlierMember, C.postPassage_earlier_pos⟩
        ⟨C.postPassage.zLaterMember, C.postPassage_later_pos⟩ (k + 1) <
      interlacingOffset ⟨C.postPassage.zEarlierMember, C.postPassage_earlier_pos⟩
        ⟨C.postPassage.zLaterMember, C.postPassage_later_pos⟩ k :=
  (cascade_step_rises_iff C.postPassage C.postPassage_earlier_pos C.postPassage_later_pos k).mpr
    (C.post_mirror_vertical h)

/-- **Cas (a) : la hiérarchie tient de nouveau au raccord qui quitte le miroir** (dès la hauteur 2). -/
theorem post_mirror_hierarchy (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1)
    (hT2 : 2 ≤ rZeroHeight C.zero.1) :
    RaccordHierarchy C.postPassage C.postPassage_earlier_pos C.postPassage_later_pos := by
  have hV := C.post_mirror_vertical h
  have hV' : rZeroHeight C.postPassage.zEarlierMember < rZeroHeight C.postPassage.zLaterMember := hV
  have he := C.postPassage_earlier_height
  exact raccordHierarchy_of_height_advance C.postPassage C.postPassage_earlier_pos C.postPassage_later_pos hV
    (by linarith)

/-- **Cas (a), profil complet du gel d'un pas** : arrivée verticale, pas sortant horizontal, pas suivant vertical. La
hiérarchie tient avant et après, elle est brisée sur le seul pas du zéro OFF vers son miroir. -/
theorem single_frozen_step_of_mirror (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1)
    (hT2 : 2 ≤ rZeroHeight C.zero.1) :
    VerticalPassage C.arrival ∧ HorizontalPassage C.outgoing ∧ VerticalPassage C.postPassage ∧
    RaccordHierarchy C.arrival C.arrival_earlier_pos C.arrival_later_pos ∧
    ¬ RaccordHierarchy C.outgoing C.outgoing_earlier_pos C.outgoing_later_pos ∧
    RaccordHierarchy C.postPassage C.postPassage_earlier_pos C.postPassage_later_pos :=
  ⟨C.arrival_vertical, C.outgoing_horizontal, C.post_mirror_vertical h, C.arrival_hierarchy hT2,
    C.outgoing_signature.2.2, C.post_mirror_hierarchy h hT2⟩

/-! ## 5quinquies. Signature intégrée de la paire OFF/miroir sur trois écarts premiers consécutifs (§19.12, 2026-10-30)

Changement d'objet intermédiaire (relecture du 2026-10-30) : la continuation forcée (§6) reste la caractérisation
terminale, mais n'est plus l'objectif de recherche. L'objet étudié est la **signature exacte de la paire** `(β + iT,
(1 − β) + iT)` sur les trois écarts `[p_{n−1}, p_n]`, `[p_n, p_{n+1}]`, `[p_{n+1}, p_{n+2}]`, dans le cas (a).

Compilé ici, exact et local, sans moyenne ni borne :
* **A. Identité hyperbolique de la paire** (canal de comptage, `countingGapTerm_mirror_pair` réutilisé, aucune nouvelle
  définition de reconstruction) : la paire moins deux signaux de ligne de même fréquence est l'intégrale d'un facteur
  d'amplitude `2(cosh(dt) − 1) > 0` fois le signal de ligne ; forme réelle de l'auteur
  `−4 ∫ e^{t/2}(cosh(dt) − 1) cos(Tt)/t dt`. Le facteur d'amplitude est strictement positif, le cosinus change de signe :
  la différence intégrée sur un écart donné n'est PAS automatiquement non nulle (consigné, pas affirmé).
* **B. Transport sur les trois écarts** : quatre premiers consécutifs strictement croissants ; télescopage exact de la
  signature de la paire ; dans le cas (a), profil des trois écarts : montée, gel, montée, avec les trois événements
  canoniques `p_n = Occ(z)`, `p_{n+1} = Occ(z*)`, `p_{n+2} = Occ(membre n+2)`.
* **D. Raccord au canal arithmétique compilé** (choix explicite : transport vers le canal LISSÉ, seul canal dont la
  reconstruction est compilée ; la reconstruction du canal de COMPTAGE n'est PAS formalisée, audit E301) : pour tout
  écart, la cible lissée se découpe exactement en « paquet de la fréquence `T` » plus « autres fréquences »
  (`target_split`) ; dans le cas (a), le paquet est exactement quatre indices (`z`, `z*` et leurs conjugués) et sa
  contribution à chaque écart est la paire lissée plus la paire conjuguée (`target_split_of_mirror`).

Ce que cela ne dit pas : l'identité `target_split_of_mirror` vaut pour toute famille de zéros ; la part « autres
fréquences » n'est pas contrainte ici. L'incompatibilité de la signature avec les trois raccords est la question
ouverte de §19.12, pas un théorème. -/

open MeasureTheory intervalIntegral ComplexConjugate

/-- Le point de ligne à la fréquence du zéro OFF : `1/2 + iT`. -/
noncomputable def linePoint : ℂ := (1 / 2 : ℂ) + (rZeroHeight C.zero.1 : ℂ) * Complex.I

theorem linePoint_re : C.linePoint.re = 1 / 2 := by simp [linePoint]

theorem linePoint_im : C.linePoint.im = rZeroHeight C.zero.1 := by simp [linePoint]

/-- `ρ = (1/2 + iT) − d`, `d = 1/2 − β`. -/
theorem zeroPoint_eq_line_sub_shift : zeroPoint C.zero = C.linePoint - (C.radialShift : ℂ) := by
  apply Complex.ext
  · rw [Complex.sub_re, Complex.ofReal_re, C.linePoint_re, zeroPoint_re]
    exact C.zero_radial_eq
  · rw [Complex.sub_im, Complex.ofReal_im, C.linePoint_im, zeroPoint_im, sub_zero]

/-- `ρ* = (1/2 + iT) + d`. -/
theorem mirrorPoint_eq_line_add_shift :
    zeroPoint (mirrorMember C.zero) = C.linePoint + (C.radialShift : ℂ) := by
  apply Complex.ext
  · rw [Complex.add_re, Complex.ofReal_re, C.linePoint_re, zeroPoint_re]
    exact C.mirror_radial_eq
  · rw [Complex.add_im, Complex.ofReal_im, C.linePoint_im, zeroPoint_im, add_zero]
    exact mirrorMember_ordinate C.zero

theorem gap_b_pos (I : PrimeGapInterval) : 0 < I.b := lt_trans I.a_pos I.a_lt_b

/-! ### A. La signature intégrée de la paire (canal de comptage) -/

/-- Contribution de la paire (zéro OFF, miroir) à l'écart `I`, canal de comptage : `C_ρ(I) + C_{ρ*}(I)`. -/
noncomputable def pairCounting (I : PrimeGapInterval) : ℂ :=
  countingGapTerm (zeroPoint C.zero) I.a I.b + countingGapTerm (zeroPoint (mirrorMember C.zero)) I.a I.b

/-- Contribution d'un signal de ligne de même fréquence à l'écart `I`. -/
noncomputable def lineCounting (I : PrimeGapInterval) : ℂ := countingGapTerm C.linePoint I.a I.b

/-- **Identité hyperbolique de la paire** : `P_ρ(I) − 2 C_{1/2+iT}(I) = ∫_a^b 2(cosh(dt) − 1) e^{(1/2+iT)t}/t dt`.
Même fréquence (même facteur oscillant), facteur d'amplitude `2(cosh(dt) − 1) > 0` pour `t > 0`, bornes exactes de
l'écart premier. -/
theorem pair_hyperbolic_signature (I : PrimeGapInterval) :
    C.pairCounting I - 2 * C.lineCounting I =
      ∫ t in I.a..I.b, 2 * (Complex.cosh ((C.radialShift : ℂ) * t) - 1) * Complex.exp (C.linePoint * t) / t := by
  unfold pairCounting lineCounting
  rw [C.zeroPoint_eq_line_sub_shift, C.mirrorPoint_eq_line_add_shift]
  exact countingGapTerm_mirror_pair C.linePoint C.radialShift I.a_pos (gap_b_pos I)

/-- Contribution signée réelle de la paire (chaque membre regroupé avec son conjugué). -/
noncomputable def pairReal (I : PrimeGapInterval) : ℝ :=
  zeroLocalContribution (zeroPoint C.zero) I + zeroLocalContribution (zeroPoint (mirrorMember C.zero)) I

/-- Contribution signée réelle d'un signal de ligne de même fréquence. -/
noncomputable def lineReal (I : PrimeGapInterval) : ℝ := zeroLocalContribution C.linePoint I

/-- Forme réelle : la différence `D_OFF − D_ON` est `−2` fois la partie réelle de l'intégrale hyperbolique. -/
theorem pair_real_signature (I : PrimeGapInterval) :
    C.pairReal I - 2 * C.lineReal I =
      -2 * (∫ t in I.a..I.b,
        2 * (Complex.cosh ((C.radialShift : ℂ) * t) - 1) * Complex.exp (C.linePoint * t) / t).re := by
  rw [← C.pair_hyperbolic_signature I]
  unfold pairReal lineReal zeroLocalContribution pairCounting lineCounting
  have h2 : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp
  rw [Complex.sub_re, Complex.add_re, h2]
  ring

theorem realCountingDensity_intervalIntegrable (ρ : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (realCountingDensity ρ) volume a b := by
  have h := countingDensity_intervalIntegrable ρ ha hb
  have h2 : IntervalIntegrable (fun t => (countingDensity ρ t).re) volume a b := ⟨h.1.re, h.2.re⟩
  have h3 := h2.const_mul (-2)
  have hfun : realCountingDensity ρ = fun t => -2 * (countingDensity ρ t).re :=
    funext (realCountingDensity_eq ρ)
  rw [hfun]
  exact h3

/-- **Formule réelle de l'auteur** : `D_OFF(a, b) − D_ON(a, b) = −4 ∫_a^b e^{t/2} (cosh(dt) − 1) cos(Tt)/t dt`. Fréquence
`T` commune, amplitude `e^{t/2}(cosh(dt) − 1) > 0` pour `t > 0`, bornes exactes. Le cosinus change de signe : le signe de
la différence sur un écart donné n'est pas décidé par cette identité. -/
theorem pair_real_signature_explicit (I : PrimeGapInterval) :
    C.pairReal I - 2 * C.lineReal I =
      ∫ t in I.a..I.b, -4 * (Real.exp (t / 2) * (Real.cosh (C.radialShift * t) - 1) *
        Real.cos (rZeroHeight C.zero.1 * t) / t) := by
  have ha := I.a_pos
  have hb := gap_b_pos I
  unfold pairReal lineReal zeroLocalContribution
  rw [zeroLocalContribution_eq_real_integral _ ha hb, zeroLocalContribution_eq_real_integral _ ha hb,
    zeroLocalContribution_eq_real_integral _ ha hb, C.zeroPoint_eq_line_sub_shift,
    C.mirrorPoint_eq_line_add_shift]
  have hI1 := realCountingDensity_intervalIntegrable (C.linePoint - (C.radialShift : ℂ)) ha hb
  have hI2 := realCountingDensity_intervalIntegrable (C.linePoint + (C.radialShift : ℂ)) ha hb
  have hI3 := realCountingDensity_intervalIntegrable C.linePoint ha hb
  rw [← intervalIntegral.integral_const_mul, ← integral_add hI1 hI2,
    ← integral_sub (hI1.add hI2) (hI3.const_mul 2)]
  congr 1
  funext t
  have hre1 : (C.linePoint - (C.radialShift : ℂ)).re = 1 / 2 - C.radialShift := by
    rw [Complex.sub_re, Complex.ofReal_re, C.linePoint_re]
  have hre2 : (C.linePoint + (C.radialShift : ℂ)).re = 1 / 2 + C.radialShift := by
    rw [Complex.add_re, Complex.ofReal_re, C.linePoint_re]
  have him1 : (C.linePoint - (C.radialShift : ℂ)).im = rZeroHeight C.zero.1 := by
    rw [Complex.sub_im, Complex.ofReal_im, C.linePoint_im, sub_zero]
  have him2 : (C.linePoint + (C.radialShift : ℂ)).im = rZeroHeight C.zero.1 := by
    rw [Complex.add_im, Complex.ofReal_im, C.linePoint_im, add_zero]
  simp only [realCountingDensity, hre1, hre2, him1, him2, C.linePoint_re, C.linePoint_im]
  have e1 : Real.exp ((1 / 2 - C.radialShift) * t) = Real.exp (t / 2) * Real.exp (-(C.radialShift * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp ((1 / 2 + C.radialShift) * t) = Real.exp (t / 2) * Real.exp (C.radialShift * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (1 / 2 * t) = Real.exp (t / 2) := by congr 1; ring
  rw [e1, e2, e3, Real.cosh_eq]
  ring

/-! ### B. Les trois écarts consécutifs et les quatre premiers -/

/-- L'écart suivant `[p_{n+1}, p_{n+2}]`. -/
def nextGap : PrimeGapInterval := ⟨C.n + 1⟩

theorem previousGap_upper_eq_gap_lower : C.previousGap.upper = C.gap.lower := by
  have h : C.n - 1 + 1 = C.n := by have := C.one_le_n; omega
  simp only [PrimeGapInterval.upper, PrimeGapInterval.lower, previousGap, gap, h]

theorem gap_upper_eq_nextGap_lower : C.gap.upper = C.nextGap.lower := rfl

theorem previousGap_b_eq_gap_a : C.previousGap.b = C.gap.a := by
  unfold PrimeGapInterval.b PrimeGapInterval.a
  rw [C.previousGap_upper_eq_gap_lower]

theorem gap_b_eq_nextGap_a : C.gap.b = C.nextGap.a := rfl

/-- **Quatre premiers consécutifs strictement croissants** : `p_{n−1} < p_n < p_{n+1} < p_{n+2}`. -/
theorem four_primes :
    fnPrimeAtRank (C.n - 1) < fnPrimeAtRank C.n ∧ fnPrimeAtRank C.n < fnPrimeAtRank (C.n + 1) ∧
      fnPrimeAtRank (C.n + 1) < fnPrimeAtRank (C.n + 1 + 1) := by
  have := C.one_le_n
  exact ⟨thm_primeAtRank_strictMono (by omega), thm_primeAtRank_strictMono (by omega),
    thm_primeAtRank_strictMono (by omega)⟩

/-- **Télescopage exact** de la signature de la paire sur les trois écarts : la somme des trois contributions est la
contribution à la fenêtre `[p_{n−1}, p_{n+2}]`. Cohérence de la formalisation, pas une contradiction. -/
theorem pairCounting_three_gaps :
    C.pairCounting C.previousGap + C.pairCounting C.gap + C.pairCounting C.nextGap =
      countingGapTerm (zeroPoint C.zero) C.previousGap.a C.nextGap.b +
        countingGapTerm (zeroPoint (mirrorMember C.zero)) C.previousGap.a C.nextGap.b := by
  have h1 : ∀ ρ : ℂ, countingGapTerm ρ C.previousGap.a C.previousGap.b +
      countingGapTerm ρ C.gap.a C.gap.b + countingGapTerm ρ C.nextGap.a C.nextGap.b =
        countingGapTerm ρ C.previousGap.a C.nextGap.b := by
    intro ρ
    rw [C.previousGap_b_eq_gap_a, C.gap_b_eq_nextGap_a,
      countingGapTerm_add ρ C.previousGap.a_pos C.gap.a_pos C.nextGap.a_pos,
      countingGapTerm_add ρ C.previousGap.a_pos C.nextGap.a_pos (gap_b_pos C.nextGap)]
  unfold pairCounting
  rw [← h1 (zeroPoint C.zero), ← h1 (zeroPoint (mirrorMember C.zero))]
  ring

/-- L'occurrence du membre de rang `n + 2` est le point de rencontre de l'écart suivant, `p_{n+2}`. -/
theorem postPassage_later_occurrence :
    (occurrence ⟨C.postPassage.zLaterMember, C.postPassage_later_pos⟩ : ℝ) = meetingPoint C.nextGap := by
  change (occurrence (canonicalMember (C.n + 1 + 1)) : ℝ) = _
  rw [occurrence_eq_primeAtRank, canonicalMember_index, meetingPoint_eq_upper]
  rfl

/-- Le point de rencontre de l'écart précédent est l'occurrence du zéro OFF, `p_n`. -/
theorem previousGap_meeting_eq_zero_occurrence :
    meetingPoint C.previousGap = (occurrence C.zero : ℝ) := by
  rw [C.previous_liaison, C.arrivalRaccord_M, C.zero_occurrence]

/-- **Profil des trois écarts dans le cas (a)** : montée (l'écart précédent apporte `T`), gel (l'écart du zéro OFF est
reconstitué à la fréquence `T`), montée (l'écart suivant apporte une fréquence strictement supérieure) ; et les trois
événements premiers canoniques portés : `p_n = Occ(z)`, `p_{n+1} = Occ(z*)`, `p_{n+2} = Occ(membre n+2)`. -/
theorem three_gap_profile_of_mirror (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    VerticalPassage C.arrival ∧ HorizontalPassage C.outgoing ∧ VerticalPassage C.postPassage ∧
      meetingPoint C.previousGap = (occurrence C.zero : ℝ) ∧
      meetingPoint C.gap = (occurrence (mirrorMember C.zero) : ℝ) ∧
      meetingPoint C.nextGap = (occurrence ⟨C.postPassage.zLaterMember, C.postPassage_later_pos⟩ : ℝ) :=
  ⟨C.arrival_vertical, C.outgoing_horizontal, C.post_mirror_vertical h,
    C.previousGap_meeting_eq_zero_occurrence, (C.mirror_occurrence_eq_meeting h).symm,
    C.postPassage_later_occurrence.symm⟩

/-! ### D. Raccord au canal arithmétique compilé (canal lissé) -/

/-- Identité hyperbolique pour le terme lissé (sans le facteur `1/t`). -/
theorem gapTerm_mirror_pair (ρ₀ : ℂ) (d : ℝ) (a b : ℝ) :
    gapTerm (ρ₀ - d) a b + gapTerm (ρ₀ + d) a b - 2 * gapTerm ρ₀ a b =
      ∫ t in a..b, 2 * (Complex.cosh (d * t) - 1) * Complex.exp (ρ₀ * t) := by
  unfold gapTerm
  have hc : ∀ σ : ℂ, IntervalIntegrable (fun t : ℝ => Complex.exp (σ * t)) volume a b :=
    fun σ => (by fun_prop : Continuous fun t : ℝ => Complex.exp (σ * t)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_const_mul, ← integral_add (hc _) (hc _),
    ← integral_sub ((hc _).add (hc _)) ((hc ρ₀).const_mul 2)]
  congr 1
  funext t
  exact mirror_pair_density ρ₀ d t

/-- Signature hyperbolique de la paire dans le canal lissé (termes non pondérés). -/
theorem pair_gapTerm_signature (I : PrimeGapInterval) :
    gapTerm (zeroPoint C.zero) I.a I.b + gapTerm (zeroPoint (mirrorMember C.zero)) I.a I.b -
        2 * gapTerm C.linePoint I.a I.b =
      ∫ t in I.a..I.b, 2 * (Complex.cosh ((C.radialShift : ℂ) * t) - 1) * Complex.exp (C.linePoint * t) := by
  rw [C.zeroPoint_eq_line_sub_shift, C.mirrorPoint_eq_line_add_shift]
  exact gapTerm_mirror_pair C.linePoint C.radialShift I.a I.b

/-- Le paquet de la fréquence du zéro OFF : tous les indices de hauteur absolue `T`. -/
def packet : Set ExplicitIndex := heightPacket (rZeroHeight C.zero.1)

/-- Contribution du paquet de fréquence `T` à l'écart `I` (canal lissé). -/
noncomputable def packetContribution (I : PrimeGapInterval) : ℂ :=
  channelOn C.packet I.upper - channelOn C.packet I.lower

/-- Contribution des autres fréquences à l'écart `I` (canal lissé). -/
noncomputable def otherFrequenciesContribution (I : PrimeGapInterval) : ℂ :=
  channelOn C.packetᶜ I.upper - channelOn C.packetᶜ I.lower

/-- **Découpage exact de la cible lissée** : pour tout écart, l'incrément du reste lissé des premiers est la part de la
fréquence `T` plus la part des autres fréquences. Identité, valable pour toute famille de zéros. -/
theorem target_split (I : PrimeGapInterval) :
    localArithmeticTarget I = C.packetContribution I + C.otherFrequenciesContribution I := by
  unfold localArithmeticTarget packetContribution otherFrequenciesContribution
  rw [smoothedRemainder_eq_tsum_residueTerm I.one_lt_upper,
    smoothedRemainder_eq_tsum_residueTerm I.one_lt_lower,
    channel_eq_packet_add_complement C.packet I.one_lt_upper,
    channel_eq_packet_add_complement C.packet I.one_lt_lower]
  ring

theorem zero_off : PIsOffCriticalLine C.zero.1 := by
  unfold PIsOffCriticalLine
  exact ne_of_lt C.zero_low

theorem memberIndex_ne_mirrorIndex : memberIndex C.zero ≠ memberIndex (mirrorMember C.zero) :=
  (off_packet_mirror_distinct C.zero_off).symm

theorem conjIndex_ne_memberIndex (w w' : TrueZero) : conjIndex w ≠ memberIndex w' := by
  intro h
  have him := congrArg (fun σ : ExplicitIndex => (σ : ℂ).im) h
  simp only [conjIndex, memberIndex, Complex.conj_im, zeroPoint_im] at him
  have hw : 0 < rZeroHeight w.1 := w.2
  have hw' : 0 < rZeroHeight w'.1 := w'.2
  linarith

theorem conjIndex_ne_mirrorConjIndex : conjIndex C.zero ≠ conjIndex (mirrorMember C.zero) := by
  intro h
  apply C.memberIndex_ne_mirrorIndex
  have h1 : conj (zeroPoint C.zero) = conj (zeroPoint (mirrorMember C.zero)) :=
    congrArg (fun σ : ExplicitIndex => (σ : ℂ)) h
  have h2 : zeroPoint C.zero = zeroPoint (mirrorMember C.zero) := by
    have := congrArg conj h1
    rwa [Complex.conj_conj, Complex.conj_conj] at this
  exact Subtype.ext h2

theorem conjIndex_mem_packet (w : TrueZero) (hw : rZeroHeight w.1 = rZeroHeight C.zero.1) :
    conjIndex w ∈ C.packet := by
  have hpos : 0 < rZeroHeight w.1 := w.2
  change |(conj (zeroPoint w)).im| = rZeroHeight C.zero.1
  rw [Complex.conj_im]
  change |-(rZeroHeight w.1)| = rZeroHeight C.zero.1
  rw [abs_neg, abs_of_pos hpos, hw]

/-- Dans le cas (a), tout indice du paquet est l'un des quatre : `z`, `z*`, ou leurs conjugués. -/
theorem packet_mem_cases (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) (σ : ExplicitIndex)
    (hσ : σ ∈ C.packet) :
    σ = memberIndex C.zero ∨ σ = memberIndex (mirrorMember C.zero) ∨
      σ = conjIndex C.zero ∨ σ = conjIndex (mirrorMember C.zero) := by
  obtain ⟨w, rfl⟩ := upperOrConj_surjective σ
  cases w with
  | inl w =>
    have hw : rZeroHeight w.1 = rZeroHeight C.zero.1 := by
      have hpos : 0 < rZeroHeight w.1 := w.2
      have h0 : |rZeroHeight w.1| = rZeroHeight C.zero.1 := hσ
      rwa [abs_of_pos hpos] at h0
    rcases C.fiber_eq_pair_of_mirror h w hw with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  | inr w =>
    have hw : rZeroHeight w.1 = rZeroHeight C.zero.1 := by
      have hpos : 0 < rZeroHeight w.1 := w.2
      have h0 : |(conj (zeroPoint w)).im| = rZeroHeight C.zero.1 := hσ
      rw [Complex.conj_im] at h0
      have h1 : |-(rZeroHeight w.1)| = rZeroHeight C.zero.1 := h0
      rwa [abs_neg, abs_of_pos hpos] at h1
    rcases C.fiber_eq_pair_of_mirror h w hw with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- **Dans le cas (a), le paquet de la fréquence `T` est exactement quatre indices.** -/
theorem packet_eq_four_of_mirror (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    C.packet = {memberIndex C.zero, memberIndex (mirrorMember C.zero),
      conjIndex C.zero, conjIndex (mirrorMember C.zero)} := by
  ext σ
  constructor
  · intro hσ
    rcases C.packet_mem_cases h σ hσ with rfl | rfl | rfl | rfl <;> simp
  · intro hσ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl | rfl | rfl
    · exact memberIndex_mem_heightPacket C.zero
    · exact mirrorMember_mem_heightPacket C.zero
    · exact C.conjIndex_mem_packet C.zero rfl
    · exact C.conjIndex_mem_packet (mirrorMember C.zero) (mirrorMember_ordinate C.zero)

theorem four_sdiff_two {α : Type*} {a b c d : α} (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    ({a, b, c, d} : Set α) \ {a, b} = {c, d} := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1 with rfl | rfl | rfl | rfl
    · exact absurd (Or.inl rfl) h2
    · exact absurd (Or.inr rfl) h2
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), fun h => h.elim hca hcb⟩
    · exact ⟨Or.inr (Or.inr (Or.inr rfl)), fun h => h.elim hda hdb⟩

theorem channelOn_empty (x : ℝ) : channelOn (∅ : Set ExplicitIndex) x = 0 := by
  unfold channelOn
  simp

/-- **Le canal du paquet, explicité dans le cas (a)** : exactement les quatre termes. -/
theorem packet_channel_four_of_mirror (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) {x : ℝ}
    (hx : 1 < x) :
    channelOn C.packet x =
      nontrivialZeroResidueTerm x (memberIndex C.zero) +
        nontrivialZeroResidueTerm x (memberIndex (mirrorMember C.zero)) +
        nontrivialZeroResidueTerm x (conjIndex C.zero) +
        nontrivialZeroResidueTerm x (conjIndex (mirrorMember C.zero)) := by
  rw [C.packet_eq_four_of_mirror h]
  have hA := packet_two_members (S := {memberIndex C.zero, memberIndex (mirrorMember C.zero),
      conjIndex C.zero, conjIndex (mirrorMember C.zero)}) (a := memberIndex C.zero)
    (b := memberIndex (mirrorMember C.zero)) (by simp) (by simp) C.memberIndex_ne_mirrorIndex hx
  rw [hA, four_sdiff_two (conjIndex_ne_memberIndex _ _) (conjIndex_ne_memberIndex _ _)
    (conjIndex_ne_memberIndex _ _) (conjIndex_ne_memberIndex _ _)]
  have hB := packet_two_members (S := {conjIndex C.zero, conjIndex (mirrorMember C.zero)})
    (a := conjIndex C.zero) (b := conjIndex (mirrorMember C.zero)) (by simp) (by simp)
    C.conjIndex_ne_mirrorConjIndex hx
  rw [hB, Set.sdiff_self, channelOn_empty]
  ring

/-- Contribution lissée de la paire (branche supérieure). -/
noncomputable def smoothedPair (I : PrimeGapInterval) : ℂ :=
  smoothedLocalContribution (memberIndex C.zero) I +
    smoothedLocalContribution (memberIndex (mirrorMember C.zero)) I

/-- Contribution lissée de la paire conjuguée (branche inférieure). -/
noncomputable def smoothedConjPair (I : PrimeGapInterval) : ℂ :=
  smoothedLocalContribution (conjIndex C.zero) I +
    smoothedLocalContribution (conjIndex (mirrorMember C.zero)) I

/-- **Transport exact de la signature vers le canal lissé compilé, cas (a)** : pour TOUT écart premier, la cible
arithmétique lissée est la paire lissée, plus la paire conjuguée, plus les autres fréquences. Aucune autre contribution
à la fréquence `T`. Identité de reconstruction : elle ne contraint pas, à elle seule, la part des autres fréquences. -/
theorem target_split_of_mirror (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1)
    (I : PrimeGapInterval) :
    localArithmeticTarget I = C.smoothedPair I + C.smoothedConjPair I + C.otherFrequenciesContribution I := by
  rw [C.target_split I]
  congr 1
  unfold packetContribution smoothedPair smoothedConjPair
  rw [C.packet_channel_four_of_mirror h I.one_lt_upper, C.packet_channel_four_of_mirror h I.one_lt_lower,
    smoothedLocalContribution_eq, smoothedLocalContribution_eq, smoothedLocalContribution_eq,
    smoothedLocalContribution_eq]
  ring

/-! ## 5sexies. La cassure : où se trouve la demande de l'écart, et ce que la paire peut y faire (§19.13, 2026-10-30)

Demande de l'auteur : tirer parti du fait que **la demande de l'écart se trouve presque entièrement dans la cassure**
(le saut exact de l'escalier des premiers au bout de l'écart), et établir rigoureusement, sur les seuls éléments
collectés, ce que l'amplitude cumulée du zéro OFF et de son miroir peut ou ne peut pas réaliser à cette cassure.

Compilé ici, exact, local, sans moyenne :
* **C1. Localisation arithmétique de la cassure.** Au pas qui atteint `p_{n+1}`, l'incrément du reste exact est
  `log p_{n+1}` moins la variation du fond (`break_at_meeting`) ; à tout pas dont l'arrivée n'est pas une puissance de
  premier, l'incrément est la seule variation du fond (`no_break_off_prime_powers`) ; la demande de l'écart entier est
  la somme des pas intermédiaires plus la cassure terminale (`gap_demand_eq_break_add_rest`). Consigné : les puissances
  de premiers intérieures à l'écart portent elles aussi une cassure (`Λ ≠ 0`) ; « entre deux premiers l'escalier
  n'avance pas » vaut hors de ces points.
* **C2. Le calage de la paire est celui de la ligne.** Point par point, la densité de la paire est `2cosh(dt)` fois la
  densité de ligne de même fréquence (`pair_density_eq_cosh_line`, forme réelle `pair_real_density_eq_cosh_line`) ; la
  paire s'annule exactement où s'annule la ligne, aux points `(π/2 + kπ)/T` qui ne dépendent que de la fréquence
  (`pair_density_zero_iff`). **La paire n'est ni en avance ni en retard sur la ligne : « à temps » n'est pas un levier ;
  seule l'amplitude, `cosh(dt) > 1` strictement croissante le long du logarithme, la distingue.**
* **C3. Le pas de la paire avant la cassure est borné** par une enveloppe explicite (`pair_step_norm_le`), et cette
  enveloppe **dépasse strictement** celle de la paire de ligne (`pair_step_bound_gt_line_bound`) : l'amplitude cumulée
  rapproche la paire OFF de la cassure, elle ne l'en éloigne pas.
* **C4. La cassure est réalisée par la totalité.** Au pas de la cassure, ce que le paquet de la fréquence `T` ne
  fournit pas est fourni exactement par les autres fréquences (`break_compensated_by_other_frequencies`) — pour la paire
  OFF comme pour toute famille : aucun signal isolé, ON ou OFF, ne réalise une cassure.

Conclusion consignée (§19.13) : « le zéro OFF ne peut pas réaliser la cassure à temps du fait de son amplitude cumulée
avec son miroir » n'est pas dérivable des éléments collectés ; ils établissent le contraire sur le calage (identique à la
ligne) et sur l'amplitude (strictement supérieure). Ce qui distingue la paire OFF est son amplitude relative non bornée
aux rencontres (`pairRelativeAmplitude_unbounded`), et sa confrontation à la demande exige un fait sur le niveau de la
demande ou sur les autres fréquences qui n'est pas dans le corpus. -/

/-! ### C1. Localisation arithmétique de la cassure -/

/-- L'entier qui précède l'événement `p_{n+1}` : le pas `meetingPred → meetingPred + 1` est la cassure. -/
noncomputable def meetingPred : ℕ := fnPrimeAtRank (C.n + 1) - 1

theorem meetingPred_succ : C.meetingPred + 1 = fnPrimeAtRank (C.n + 1) := by
  unfold meetingPred
  have := (thm_primeAtRank_isPrime (C.n + 1)).two_le
  omega

theorem two_le_meetingPred : 2 ≤ C.meetingPred := by
  have h0 : fnPrimeAtRank 0 < fnPrimeAtRank (C.n + 1) := thm_primeAtRank_strictMono (by omega)
  rw [thm_primeAtRank_zero_eq_two] at h0
  unfold meetingPred
  omega

/-- **La cassure au point de rencontre** : l'incrément du reste exact au pas qui atteint `p_{n+1}` est `log p_{n+1}`
moins la variation du fond. -/
theorem break_at_meeting :
    remainderIncrement C.meetingPred =
      ((Real.log (fnPrimeAtRank (C.n + 1)) : ℝ) : ℂ) -
        (stepAt backgroundPrimitive (fnPrimeAtRank (C.n + 1)) - stepAt backgroundPrimitive C.meetingPred) := by
  rw [remainderIncrement_arithmetic, C.meetingPred_succ,
    ArithmeticFunction.vonMangoldt_apply_prime (thm_primeAtRank_isPrime (C.n + 1))]

/-- **Hors des puissances de premiers, aucune cassure** : l'incrément du reste exact est la seule variation du fond. -/
theorem no_break_off_prime_powers (N : ℕ) (hN : ¬ IsPrimePow (N + 1)) :
    remainderIncrement N = -(stepAt backgroundPrimitive (N + 1) - stepAt backgroundPrimitive N) := by
  rw [remainderIncrement_arithmetic, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hN]
  simp

/-- Télescopage des pas du reste exact. -/
theorem gap_demand_sum_increments (a m : ℕ) :
    ∑ k ∈ Finset.range m, remainderIncrement (a + k) = exactRemainder (a + m) - exactRemainder a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    unfold remainderIncrement
    rw [← add_assoc]
    ring

/-- **La demande de l'écart est ses pas intermédiaires plus la cassure terminale** : l'incrément du reste exact sur
`[p_n, p_{n+1}]` est la somme des pas de `p_n` à `p_{n+1} − 1`, puis la cassure `log p_{n+1}` moins le fond. -/
theorem gap_demand_eq_break_add_rest :
    exactRemainder (fnPrimeAtRank (C.n + 1)) - exactRemainder (fnPrimeAtRank C.n) =
      (∑ k ∈ Finset.range (C.meetingPred - fnPrimeAtRank C.n),
        remainderIncrement (fnPrimeAtRank C.n + k)) +
        (((Real.log (fnPrimeAtRank (C.n + 1)) : ℝ) : ℂ) -
          (stepAt backgroundPrimitive (fnPrimeAtRank (C.n + 1)) -
            stepAt backgroundPrimitive C.meetingPred)) := by
  have hlt : fnPrimeAtRank C.n < fnPrimeAtRank (C.n + 1) := thm_primeAtRank_strictMono (by omega)
  have hsucc := C.meetingPred_succ
  have hw : fnPrimeAtRank C.n + (C.meetingPred - fnPrimeAtRank C.n) = C.meetingPred := by omega
  have hsum := gap_demand_sum_increments (fnPrimeAtRank C.n) (C.meetingPred - fnPrimeAtRank C.n + 1)
  rw [Finset.sum_range_succ, hw, ← add_assoc, hw, hsucc, C.break_at_meeting] at hsum
  exact hsum.symm

/-! ### C2. Le calage de la paire est celui de la ligne -/

/-- **Densité de la paire = `2cosh(dt)` × densité de ligne** (canal de comptage), point par point. -/
theorem pair_density_eq_cosh_line (t : ℝ) :
    countingDensity (zeroPoint C.zero) t + countingDensity (zeroPoint (mirrorMember C.zero)) t =
      2 * Complex.cosh ((C.radialShift : ℂ) * t) * countingDensity C.linePoint t := by
  rw [C.zeroPoint_eq_line_sub_shift, C.mirrorPoint_eq_line_add_shift]
  unfold countingDensity
  have h := mirror_pair_density C.linePoint C.radialShift t
  have h' : Complex.exp ((C.linePoint - C.radialShift) * t) + Complex.exp ((C.linePoint + C.radialShift) * t) =
      2 * Complex.cosh ((C.radialShift : ℂ) * t) * Complex.exp (C.linePoint * t) := by
    linear_combination h
  rw [← add_div, h']
  ring

/-- Forme réelle : `D_ρ(t) + D_{ρ*}(t) = 2cosh(dt) · D_{1/2+iT}(t)`. -/
theorem pair_real_density_eq_cosh_line (t : ℝ) :
    realCountingDensity (zeroPoint C.zero) t + realCountingDensity (zeroPoint (mirrorMember C.zero)) t =
      2 * Real.cosh (C.radialShift * t) * realCountingDensity C.linePoint t := by
  rw [C.zeroPoint_eq_line_sub_shift, C.mirrorPoint_eq_line_add_shift]
  have hre1 : (C.linePoint - (C.radialShift : ℂ)).re = 1 / 2 - C.radialShift := by
    rw [Complex.sub_re, Complex.ofReal_re, C.linePoint_re]
  have hre2 : (C.linePoint + (C.radialShift : ℂ)).re = 1 / 2 + C.radialShift := by
    rw [Complex.add_re, Complex.ofReal_re, C.linePoint_re]
  have him1 : (C.linePoint - (C.radialShift : ℂ)).im = rZeroHeight C.zero.1 := by
    rw [Complex.sub_im, Complex.ofReal_im, C.linePoint_im, sub_zero]
  have him2 : (C.linePoint + (C.radialShift : ℂ)).im = rZeroHeight C.zero.1 := by
    rw [Complex.add_im, Complex.ofReal_im, C.linePoint_im, add_zero]
  simp only [realCountingDensity, hre1, hre2, him1, him2, C.linePoint_re, C.linePoint_im]
  have e1 : Real.exp ((1 / 2 - C.radialShift) * t) = Real.exp (t / 2) * Real.exp (-(C.radialShift * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp ((1 / 2 + C.radialShift) * t) = Real.exp (t / 2) * Real.exp (C.radialShift * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (1 / 2 * t) = Real.exp (t / 2) := by congr 1; ring
  rw [e1, e2, e3, Real.cosh_eq]
  ring

/-- **Le calage de la paire est celui de la ligne** : la densité réelle de la paire s'annule exactement aux points
`(π/2 + kπ)/T` de la ligne, qui ne dépendent que de la fréquence. La paire n'est ni en avance ni en retard. -/
theorem pair_density_zero_iff {t : ℝ} (ht : 0 < t) :
    realCountingDensity (zeroPoint C.zero) t + realCountingDensity (zeroPoint (mirrorMember C.zero)) t = 0 ↔
      ∃ k : ℤ, t = densitySignChangeLog (rZeroHeight C.zero.1) k := by
  rw [C.pair_real_density_eq_cosh_line, mul_eq_zero, mul_eq_zero]
  have hcosh : Real.cosh (C.radialShift * t) ≠ 0 := (Real.cosh_pos _).ne'
  have hT : C.linePoint.im ≠ 0 := by rw [C.linePoint_im]; exact C.zero.2.ne'
  rw [realCountingDensity_eq_zero_iff C.linePoint hT ht, C.linePoint_im]
  constructor
  · rintro ((h2 | h) | h)
    · norm_num at h2
    · exact absurd h hcosh
    · exact h
  · intro h
    exact Or.inr h

/-! ### C3. Le pas de la paire avant la cassure : enveloppe explicite, strictement au-dessus de la ligne -/

/-- **Enveloppe du pas de la paire** sur `[log N, log(N + 1)]` (canal de comptage) :
`(e^{β log(N+1)} + e^{(1−β) log(N+1)}) / log N · (log(N+1) − log N)`. -/
theorem pair_step_norm_le (N : ℕ) (hN : 2 ≤ N) :
    ‖countingGapTerm (zeroPoint C.zero) (Real.log N) (Real.log (N + 1)) +
        countingGapTerm (zeroPoint (mirrorMember C.zero)) (Real.log N) (Real.log (N + 1))‖ ≤
      (Real.exp (rZeroRadialPosition C.zero.1 * Real.log (N + 1)) / Real.log N +
          Real.exp ((1 - rZeroRadialPosition C.zero.1) * Real.log (N + 1)) / Real.log N) *
        (Real.log (N + 1) - Real.log N) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 < Real.log N := Real.log_pos hN1
  have hab : Real.log N ≤ Real.log (N + 1) := Real.log_le_log (by linarith) (by linarith)
  have h1 := countingGapTerm_norm_le (zeroPoint C.zero) (zeroPoint_re_pos C.zero).le ha hab
  have h2 := countingGapTerm_norm_le (zeroPoint (mirrorMember C.zero)) (zeroPoint_re_pos _).le ha hab
  rw [zeroPoint_re] at h1
  rw [zeroPoint_re, mirrorMember_radial] at h2
  refine le_trans (norm_add_le _ _) ?_
  rw [add_mul]
  exact add_le_add h1 h2

/-- **L'enveloppe de la paire OFF dépasse strictement celle de la paire de ligne** : pour tout `b > 0`,
`2 e^{b/2} < e^{βb} + e^{(1−β)b}` (facteur `cosh(db) > 1`). L'amplitude cumulée rapproche la paire de la cassure. -/
theorem pair_step_bound_gt_line_bound {b : ℝ} (hb : 0 < b) :
    2 * Real.exp (1 / 2 * b) <
      Real.exp (rZeroRadialPosition C.zero.1 * b) + Real.exp ((1 - rZeroRadialPosition C.zero.1) * b) := by
  rw [C.zero_radial_eq]
  have e1 : Real.exp ((1 / 2 - C.radialShift) * b) = Real.exp (1 / 2 * b) * Real.exp (-(C.radialShift * b)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp ((1 - (1 / 2 - C.radialShift)) * b) =
      Real.exp (1 / 2 * b) * Real.exp (C.radialShift * b) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, e2]
  have hc : 1 < Real.cosh (C.radialShift * b) :=
    Real.one_lt_cosh.mpr (mul_pos C.radialShift_pos hb).ne'
  rw [Real.cosh_eq] at hc
  have hp : 0 < Real.exp (1 / 2 * b) := Real.exp_pos _
  nlinarith

/-! ### C4. La cassure est réalisée par la totalité -/

/-- **La cassure est réalisée par la totalité** : au pas de la cassure, la différence entre la demande et le paquet de la
fréquence `T` est, par identité, la somme des autres fréquences — pour la paire OFF comme pour toute famille (identité du
complément, §19.21 ; nom conservé, renommage `break_complement_identity` proposé, non exécuté). Aucun signal isolé ne
réalise une cassure ; aucune lecture « la paire doit réaliser la cassure à temps » n'est compilable. -/
theorem break_compensated_by_other_frequencies :
    eventCompensation C.packet C.meetingPred = packetIncrement C.packetᶜ C.meetingPred :=
  eventCompensation_eq_complement C.packet C.two_le_meetingPred

/-! ## 5septies. Ce que le prochain point de rencontre exige : compilé et ouvert (§19.14, 2026-10-30)

Demande de l'auteur : prouver que le prochain point de rencontre et le prochain pic exigent une fréquence strictement
supérieure, sans être trop grande, donc exactement une fréquence ON, et non une seconde paire OFF/miroir, trop forte.

Compilé ici (cas (a), le membre porté par `p_{n+2}` est `nextMember`, celui qui suit le miroir) :
* `next_meeting_higher_frequency` : **le membre porté par `p_{n+2}` a une fréquence strictement supérieure à `T`.**
  Source : l'ordre canonique et la bande de la fibre (`post_mirror_vertical`) — pas la rencontre elle-même.
* `nextMember_radial_le_half`, `nextMember_onLine_or_low` : **ce membre est ON, ou sous un demi** ; au-dessus d'un demi,
  son propre miroir s'intercalerait entre le miroir du zéro OFF et lui, contre la consécutivité.
* `second_off_freezes_again` : **s'il est sous un demi, le pas qui le quitte gèle de nouveau** (son miroir attend à la
  même fréquence) ; `second_pair_amplitude_exceeds_line`, `second_pair_relativeAmplitude_unbounded` : **cette seconde
  paire dépasse strictement la ligne en tout point, et son amplitude relative aux rencontres n'est pas bornée.**

Non compilé, consigné : aucune borne supérieure sur la fréquence suivante (« sans être trop grande ») n'existe dans le
corpus ; « exactement une fréquence ON » pour `nextMember` est la même frontière un pas plus loin (une seconde paire OFF
n'est contredite par rien de compilé : elle coûte un pas gelé et une amplitude relative non bornée, qui ne contredisent
la demande que sous un fait sur son niveau, absent du corpus). -/

/-- Le membre porté par le point de rencontre suivant `p_{n+2}`. -/
noncomputable def nextMember : TrueZero := ⟨C.postPassage.zLaterMember, C.postPassage_later_pos⟩

theorem nextMember_occurrence : (occurrence C.nextMember : ℝ) = meetingPoint C.nextGap :=
  C.postPassage_later_occurrence

/-- **Le prochain point de rencontre porte une fréquence strictement supérieure** (cas (a)). -/
theorem next_meeting_higher_frequency (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    zeroFrequency C.zero.1 < zeroFrequency C.nextMember.1 := by
  have hv : rZeroHeight C.postPassage.zEarlierMember < rZeroHeight C.postPassage.zLaterMember :=
    C.post_mirror_vertical h
  rw [C.postPassage_earlier_height] at hv
  exact hv

/-- **Le membre porté par `p_{n+2}` n'est pas au-dessus d'un demi** : sinon son miroir, de même hauteur et de position
radiale strictement inférieure, s'intercalerait entre le miroir du zéro OFF et lui. -/
theorem nextMember_radial_le_half (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    rZeroRadialPosition C.nextMember.1 ≤ 1 / 2 := by
  by_contra hgt
  have hgt' : 1 / 2 < rZeroRadialPosition C.nextMember.1 := lt_of_not_ge hgt
  have hv : rZeroHeight C.postPassage.zEarlierMember < rZeroHeight C.postPassage.zLaterMember :=
    C.post_mirror_vertical h
  have hm_h : rZeroHeight (mirrorMember C.nextMember).1 = rZeroHeight C.nextMember.1 :=
    mirrorMember_ordinate _
  have hm_r : rZeroRadialPosition (mirrorMember C.nextMember).1 = 1 - rZeroRadialPosition C.nextMember.1 :=
    mirrorMember_radial _
  have h1 : PZeroMemberPrecedes C.postPassage.zEarlierMember (mirrorMember C.nextMember).1 := by
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    left
    rw [hm_h]
    exact hv
  have h2 : PZeroMemberPrecedes (mirrorMember C.nextMember).1 C.nextMember.1 := by
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    exact ⟨hm_h, by rw [hm_r]; linarith⟩
  exact (canonicalMember_consecutive (C.n + 1)).2 ⟨_, h1, h2⟩

/-- **Dichotomie du membre suivant** : ON, ou sous un demi (une seconde paire OFF). -/
theorem nextMember_onLine_or_low (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    rZeroRadialPosition C.nextMember.1 = 1 / 2 ∨ rZeroRadialPosition C.nextMember.1 < 1 / 2 := by
  rcases lt_or_eq_of_le (C.nextMember_radial_le_half h) with hlt | heq
  · exact Or.inr hlt
  · exact Or.inl heq

/-- **Une seconde paire OFF gèle de nouveau** : si le membre porté par `p_{n+2}` est sous un demi, le passage qui le
quitte garde sa fréquence (son miroir attend). -/
theorem second_off_freezes_again (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1)
    (hlow : rZeroRadialPosition C.nextMember.1 < 1 / 2) :
    HorizontalPassage (canonicalPassage (C.n + 1 + 1)) :=
  (low_arrival_freezes_cascade (p := C.postPassage) (q := canonicalPassage (C.n + 1 + 1)) rfl
    (C.post_mirror_vertical h) hlow C.postPassage_later_pos (canonicalMember (C.n + 1 + 1 + 1)).2).1

/-- **La seconde paire dépasse strictement la ligne** en tout point `x > 1`. -/
theorem second_pair_amplitude_exceeds_line (hlow : rZeroRadialPosition C.nextMember.1 < 1 / 2) {x : ℝ}
    (hx : 1 < x) :
    2 * x ^ (-(1 / 2) : ℝ) <
      ‖(x : ℂ) ^ (zeroPoint C.nextMember - 1)‖ + ‖(x : ℂ) ^ (zeroPoint (mirrorMember C.nextMember) - 1)‖ :=
  off_pair_density_exceeds_line C.nextMember (mirrorMember C.nextMember) hx
    (d := 1 / 2 - rZeroRadialPosition C.nextMember.1) (by linarith : (0 : ℝ) < _).ne' (by ring)
    (by rw [mirrorMember_radial]; ring)

/-- **L'amplitude relative de la seconde paire aux rencontres n'est pas bornée.** -/
theorem second_pair_relativeAmplitude_unbounded (hlow : rZeroRadialPosition C.nextMember.1 < 1 / 2) (c : ℝ) :
    ∃ I : PrimeGapInterval, c < pairRelativeAmplitude C.nextMember (meetingPoint I) :=
  pairRelativeAmplitude_unbounded C.nextMember hlow c

/-! ## 6. L'hypothèse nommée : la continuation forcée par la rencontre suivante -/

/-- **HYPOTHÈSE NOMMÉE (jamais un théorème) — continuation forcée** : la rencontre obligatoire à `p_{n+1}` exige du
signal qui y arrive une fréquence strictement supérieure, c'est-à-dire que le pas sortant monte. -/
def ContinuationForced : Prop := VerticalPassage C.outgoing

/-- **Contradiction locale** : sous la continuation forcée, le porteur est contradictoire (le pas sortant est gelé). -/
theorem continuation_contradiction (h : C.ContinuationForced) : False :=
  absurd C.outgoing_horizontal (ne_of_lt h)

/-- La continuation forcée est exactement la lecture au raccord sortant : décalages strictement décroissants. -/
theorem continuationForced_iff_reading :
    C.ContinuationForced ↔ ∀ k : ℤ,
      interlacingOffset ⟨C.outgoing.zEarlierMember, C.outgoing_earlier_pos⟩
          ⟨C.outgoing.zLaterMember, C.outgoing_later_pos⟩ (k + 1) <
        interlacingOffset ⟨C.outgoing.zEarlierMember, C.outgoing_earlier_pos⟩
          ⟨C.outgoing.zLaterMember, C.outgoing_later_pos⟩ k :=
  ⟨fun h k => (cascade_step_rises_iff C.outgoing C.outgoing_earlier_pos C.outgoing_later_pos k).mpr h,
    fun h => (cascade_step_rises_iff C.outgoing C.outgoing_earlier_pos C.outgoing_later_pos 0).mp (h 0)⟩

/-- La continuation forcée est exactement la hiérarchie au raccord sortant (dès la hauteur 2). -/
theorem continuationForced_iff_hierarchy (hT2 : 2 ≤ rZeroHeight C.zero.1) :
    C.ContinuationForced ↔ RaccordHierarchy C.outgoing C.outgoing_earlier_pos C.outgoing_later_pos :=
  ⟨fun h => raccordHierarchy_of_height_advance C.outgoing C.outgoing_earlier_pos C.outgoing_later_pos h
      (by rw [← C.outgoing_horizontal]; exact hT2),
    raccordHierarchy_forces_height⟩

end OffCarrier

/-- **Continuation forcée sur tout porteur** (hypothèse nommée, quantifiée). -/
def ContinuationForcedOnCarriers : Prop := ∀ C : OffCarrier, C.ContinuationForced

/-- Sous la continuation forcée sur tout porteur, RH. -/
theorem riemannHypothesis_of_continuationForced (h : ContinuationForcedOnCarriers) : RiemannHypothesis := by
  by_contra hNot
  obtain ⟨C⟩ := exists_offCarrier_of_not_riemannHypothesis hNot
  exact C.continuation_contradiction (h C)

/-- **Équivalence exacte** : la continuation forcée sur tout porteur est RH (sous RH, aucun porteur : vacuité). Ce
n'est pas une réduction démontrée ; c'est la forme locale exacte de ce qui reste à dériver des premiers seuls. -/
theorem continuationForced_iff_riemannHypothesis : ContinuationForcedOnCarriers ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_continuationForced, fun hRH C => (no_offCarrier_of_riemannHypothesis hRH C).elim⟩

end RHV6Fresh

#print axioms RHV6Fresh.OffCarrier.carrier_primes
#print axioms RHV6Fresh.OffCarrier.liaison
#print axioms RHV6Fresh.OffCarrier.previous_frequency_read
#print axioms RHV6Fresh.OffCarrier.outgoing_signature
#print axioms RHV6Fresh.OffCarrier.continuation_contradiction
#print axioms RHV6Fresh.OffCarrier.pair_amplitude_exceeds_line_at_meeting
#print axioms RHV6Fresh.OffCarrier.zero_signal_ne_line_signal
#print axioms RHV6Fresh.OffCarrier.zero_signal_ne_mirror_signal
#print axioms RHV6Fresh.OffCarrier.outgoing_trichotomy
#print axioms RHV6Fresh.OffCarrier.mirror_occurrence_eq_meeting
#print axioms RHV6Fresh.OffCarrier.outgoing_no_common_smoothed_meeting
#print axioms RHV6Fresh.OffCarrier.fiber_band
#print axioms RHV6Fresh.OffCarrier.fiber_eq_pair_of_mirror
#print axioms RHV6Fresh.OffCarrier.post_vertical_iff_mirror
#print axioms RHV6Fresh.OffCarrier.single_frozen_step_of_mirror
#print axioms RHV6Fresh.continuationForced_iff_riemannHypothesis
#print axioms RHV6Fresh.OffCarrier.pair_hyperbolic_signature
#print axioms RHV6Fresh.OffCarrier.pair_real_signature_explicit
#print axioms RHV6Fresh.OffCarrier.pairCounting_three_gaps
#print axioms RHV6Fresh.OffCarrier.three_gap_profile_of_mirror
#print axioms RHV6Fresh.OffCarrier.target_split
#print axioms RHV6Fresh.OffCarrier.packet_eq_four_of_mirror
#print axioms RHV6Fresh.OffCarrier.target_split_of_mirror
#print axioms RHV6Fresh.OffCarrier.break_at_meeting
#print axioms RHV6Fresh.OffCarrier.gap_demand_eq_break_add_rest
#print axioms RHV6Fresh.OffCarrier.pair_density_zero_iff
#print axioms RHV6Fresh.OffCarrier.pair_step_norm_le
#print axioms RHV6Fresh.OffCarrier.pair_step_bound_gt_line_bound
#print axioms RHV6Fresh.OffCarrier.break_compensated_by_other_frequencies
#print axioms RHV6Fresh.OffCarrier.next_meeting_higher_frequency
#print axioms RHV6Fresh.OffCarrier.nextMember_onLine_or_low
#print axioms RHV6Fresh.OffCarrier.second_off_freezes_again
#print axioms RHV6Fresh.OffCarrier.second_pair_amplitude_exceeds_line
#print axioms RHV6Fresh.OffCarrier.second_pair_relativeAmplitude_unbounded
