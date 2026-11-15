/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TransportAtSharedPrime
import RHV6Fresh.Terminal.MeetingContactReading

/-!
# RHV6Fresh — Terminal/RaccordTransportObligation : le transport au premier partagé écrit avec les contacts,
et ce que l'obligation du raccord exige du transport (§19.45, 2026-11-04 ; module isolé, NON importé par
`RHV6Fresh.lean` ; aucune hypothèse, aucun axiome, aucun `sorry`)

Méthode (demande de l'auteur) : développement guidé par le compilateur. On écrit d'abord les énoncés cibles, on
laisse le compilateur dire ce qui manque, puis on nomme exactement l'hypothèse manquante. Rien n'est posé.

## 1. Le transport au premier partagé, écrit avec les contacts
* `amplitude_from_lastContact` : `q^β/‖β+iT‖ = |v_k| · e^{βπf/T}` avec `k` le dernier contact avant `q`, `v_k` sa
  valeur réelle, `f` la fraction de cellule (instance de `abs_contactRealValue` et `growth_factor_eq`).
* `energyRatio_from_contacts` : le transport d'un membre `e` à un membre `l` à l'abscisse `q`
  (`energyRatio`, `‖zeroTerm l q‖/‖zeroTerm e q‖`) est le rapport des valeurs absolues aux derniers contacts,
  multiplié par le rapport des croissances sur les fractions de cellule. **Le premier partagé n'entre que par les
  deux derniers contacts avant lui et les deux fractions de cellule.**
* `pair_transport_from_contacts` : la paire au premier partagé `p_{n+1}` (même fréquence, positions `½ ∓ δ`).

## 2. L'obligation du raccord, formulée sur le transport
* `RaccordTransportObligation C` : le détour (trois transports) transporte exactement la valeur de la chaîne ON
  entre les mêmes extrêmes. `obligation_iff_factor_one` : ⟺ `(p_{n+1}²/(p_n p_{n+2}))^δ = 1`.
  `not_raccordTransportObligation` : cette obligation est **fausse pour tout porteur** (reprise en ligne).
  Donc la « prouver depuis la cassure » reviendrait à prouver qu'aucun porteur n'existe : c'est l'hypothèse.

## 3. Ce que la cassure donne, et ce qui manque (guidé par le compilateur)
* `break_split_any_packet` : au pas de la cassure, le reste exact est paquet + complément **pour tout paquet** ;
  l'identité de la cassure ne distingue aucun paquet : elle ne contraint pas celui de la paire.
* `PairDepositOnLine C` : hypothèse nommée (jamais posée) « la densité de la paire au pas de la cassure vaut celle
  de la paire en ligne ». `pairDepositOnLine_forces_sign_change` : elle force la cassure sur un changement de
  signe de la densité de ligne (`log p_{n+1} = (π/2 + kπ)/T`) — en termes de contacts, le premier partagé tombe
  à une demi-cellule de phase de densité. `pairDepositOnLine_iff_sign_change` : réciproque.
* `obligation_of_link` : la seule hypothèse qui ferme `RaccordTransportObligation` est `δ·log(contenu) = 0`,
  déjà réfutée. Le chaînon manquant n'est donc pas une égalité de transport : il doit être une relation entre
  le dépôt de la paire à la cassure et les contacts, et `PairDepositOnLine` en est la forme la plus faible qui
  dise quelque chose (elle contraint la position de la cassure dans la cellule, pas `δ`).
-/

namespace RHV6Fresh

open Real RHV3Lean

/-! ## 1. Le transport au premier partagé, écrit avec les contacts -/

/-- **Amplitude à une abscisse depuis le dernier contact** : `q^β/‖β+iT‖ = |v_k| · e^{βπf/T}`. -/
theorem amplitude_from_lastContact {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) {q : ℝ} (hq : 0 < q) :
    q ^ β / ‖(⟨β, T⟩ : ℂ)‖ =
      |contactRealValue β T (lastContactBefore β T q)| *
        Real.exp (β * Real.pi * cellFraction β T q / T) := by
  rw [abs_contactRealValue hβ, ← growth_factor_eq hT hq]
  have hC := contactAt_pos β T (lastContactBefore β T q)
  rw [Real.div_rpow hq.le hC.le]
  have hCk : contactAt β T (lastContactBefore β T q) ^ β ≠ 0 := (Real.rpow_pos_of_pos hC β).ne'
  have hn : ‖(⟨β, T⟩ : ℂ)‖ ≠ 0 := (norm_mk_pos hβ).ne'
  field_simp

/-- Position radiale strictement positive d'un membre. -/
theorem member_radial_pos (z : TrueZero) : 0 < rZeroRadialPosition z.1 := zeroPoint_re_pos z

/-- Hauteur strictement positive d'un membre. -/
theorem member_height_pos (z : TrueZero) : 0 < rZeroHeight z.1 := z.2

/-- Norme du point d'un membre, écrite avec ses coordonnées. -/
theorem zeroPoint_norm_eq_mk (z : TrueZero) :
    ‖zeroPoint z‖ = ‖(⟨rZeroRadialPosition z.1, rZeroHeight z.1⟩ : ℂ)‖ := by
  rw [zeroPoint_eq_mk]

/-- Amplitude d'un membre à `q`, lue depuis son dernier contact avant `q`. -/
theorem member_amplitude_from_lastContact (z : TrueZero) {q : ℝ} (hq : 0 < q) :
    q ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖ =
      |contactRealValue (rZeroRadialPosition z.1) (rZeroHeight z.1)
          (lastContactBefore (rZeroRadialPosition z.1) (rZeroHeight z.1) q)| *
        Real.exp (rZeroRadialPosition z.1 * Real.pi *
          cellFraction (rZeroRadialPosition z.1) (rZeroHeight z.1) q / rZeroHeight z.1) := by
  rw [zeroPoint_norm_eq_mk]
  exact amplitude_from_lastContact (member_radial_pos z) (member_height_pos z) hq

/-- **Le transport entre deux membres à l'abscisse `q`, écrit avec les contacts** : rapport des valeurs absolues
aux derniers contacts avant `q`, fois rapport des croissances sur les fractions de cellule. -/
theorem energyRatio_from_contacts (e l : TrueZero) {q : ℝ} (hq : 0 < q) :
    energyRatio e l q =
      (|contactRealValue (rZeroRadialPosition l.1) (rZeroHeight l.1)
          (lastContactBefore (rZeroRadialPosition l.1) (rZeroHeight l.1) q)| *
        Real.exp (rZeroRadialPosition l.1 * Real.pi *
          cellFraction (rZeroRadialPosition l.1) (rZeroHeight l.1) q / rZeroHeight l.1)) /
      (|contactRealValue (rZeroRadialPosition e.1) (rZeroHeight e.1)
          (lastContactBefore (rZeroRadialPosition e.1) (rZeroHeight e.1) q)| *
        Real.exp (rZeroRadialPosition e.1 * Real.pi *
          cellFraction (rZeroRadialPosition e.1) (rZeroHeight e.1) q / rZeroHeight e.1)) := by
  unfold energyRatio
  rw [zeroTerm_norm hq, zeroTerm_norm hq, member_amplitude_from_lastContact l hq,
    member_amplitude_from_lastContact e hq]

namespace OffCarrier

variable (C : OffCarrier)

/-- **La paire au premier partagé, écrite avec les contacts** : positions `½ − δ` et `½ + δ`, même fréquence `T`. -/
theorem pair_transport_from_contacts :
    energyRatio C.zero (mirrorMember C.zero) (fnPrimeAtRank (C.n + 1) : ℝ) =
      (|contactRealValue (1 / 2 + C.radialShift) (rZeroHeight C.zero.1)
          (lastContactBefore (1 / 2 + C.radialShift) (rZeroHeight C.zero.1) (fnPrimeAtRank (C.n + 1)))| *
        Real.exp ((1 / 2 + C.radialShift) * Real.pi *
          cellFraction (1 / 2 + C.radialShift) (rZeroHeight C.zero.1) (fnPrimeAtRank (C.n + 1)) /
            rZeroHeight C.zero.1)) /
      (|contactRealValue (1 / 2 - C.radialShift) (rZeroHeight C.zero.1)
          (lastContactBefore (1 / 2 - C.radialShift) (rZeroHeight C.zero.1) (fnPrimeAtRank (C.n + 1)))| *
        Real.exp ((1 / 2 - C.radialShift) * Real.pi *
          cellFraction (1 / 2 - C.radialShift) (rZeroHeight C.zero.1) (fnPrimeAtRank (C.n + 1)) /
            rZeroHeight C.zero.1)) := by
  have hq : (0 : ℝ) < fnPrimeAtRank (C.n + 1) := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  have hT : rZeroHeight (mirrorMember C.zero).1 = rZeroHeight C.zero.1 := mirrorMember_ordinate C.zero
  rw [energyRatio_from_contacts _ _ hq, hT, C.mirror_radial_eq, C.zero_radial_eq]

/-! ## 2. L'obligation du raccord, formulée sur le transport -/

/-- **Obligation de transport du raccord** : le détour OFF transporte exactement la valeur de la chaîne ON entre
`prev` et `next` (au premier `p_{n+2}`). Définition, jamais posée. -/
def RaccordTransportObligation : Prop :=
  energyRatio C.prevMember C.zero (fnPrimeAtRank C.n : ℝ) *
      energyRatio C.zero (mirrorMember C.zero) (fnPrimeAtRank (C.n + 1) : ℝ) *
      energyRatio (mirrorMember C.zero) C.nextMember (fnPrimeAtRank (C.n + 2) : ℝ) =
    energyRatio C.prevMember C.nextMember (fnPrimeAtRank (C.n + 2))

/-- **L'obligation équivaut à `(p_{n+1}²/(p_n p_{n+2}))^δ = 1`** (reprise en ligne). -/
theorem obligation_iff_factor_one (hON : rZeroRadialPosition C.nextMember.1 = 1 / 2) :
    C.RaccordTransportObligation ↔ C.detourPrimeContent ^ C.radialShift = 1 := by
  unfold RaccordTransportObligation
  rw [C.detour_transport_product_onLine hON, C.onLine_chain_transport hON (thm_primeAtRank_isPrime _)]
  have hpos : 0 < ‖zeroPoint C.prevMember‖ / ‖zeroPoint C.nextMember‖ :=
    div_pos (zeroPoint_norm_pos _) (zeroPoint_norm_pos _)
  constructor
  · intro h
    exact mul_right_cancel₀ hpos.ne' (h.trans (one_mul _).symm)
  · intro h
    rw [h, one_mul]

/-- **L'obligation de transport est fausse pour tout porteur** (reprise en ligne) : elle n'est donc pas ce que
la cassure pourrait imposer sans que ce soit déjà l'hypothèse. -/
theorem not_raccordTransportObligation (hON : rZeroRadialPosition C.nextMember.1 = 1 / 2) :
    ¬ C.RaccordTransportObligation := fun h =>
  C.detour_arithmetic_factor_ne_one ((C.obligation_iff_factor_one hON).mp h)

/-- **La seule hypothèse qui ferme l'obligation** est `δ · log(contenu) = 0` ; elle est réfutée
(`radialShift_pos`, `detourPrimeContent_ne_one`). Le compilateur ne demande rien d'autre. -/
theorem obligation_of_link (hON : rZeroRadialPosition C.nextMember.1 = 1 / 2)
    (hlink : C.radialShift * Real.log C.detourPrimeContent = 0) : C.RaccordTransportObligation := by
  rw [C.obligation_iff_factor_one hON, Real.rpow_def_of_pos C.detourPrimeContent_pos, mul_comm, hlink,
    Real.exp_zero]

theorem link_false : C.radialShift * Real.log C.detourPrimeContent ≠ 0 := by
  intro h
  rcases mul_eq_zero.mp h with h | h
  · exact C.radialShift_pos.ne' h
  · rcases Real.log_eq_zero.mp h with h | h | h
    · exact C.detourPrimeContent_pos.ne' h
    · exact C.detourPrimeContent_ne_one h
    · linarith [C.detourPrimeContent_pos]

/-! ## 3. Ce que la cassure donne, et ce qui manque -/

/-- **Au pas de la cassure, le reste exact est paquet + complément, pour TOUT paquet** : l'identité de la cassure
ne distingue aucun paquet, donc ne contraint pas celui de la paire. -/
theorem break_split_any_packet (S : Set ExplicitIndex) :
    remainderIncrement C.meetingPred = packetIncrement S C.meetingPred + packetIncrement Sᶜ C.meetingPred :=
  remainderIncrement_eq_packet_add_complement S C.two_le_meetingPred

/-- Le logarithme du premier partagé de la sortie. -/
noncomputable def breakLog : ℝ := Real.log (fnPrimeAtRank (C.n + 1))

theorem breakLog_pos : 0 < C.breakLog := by
  unfold breakLog
  have : (5 : ℝ) ≤ fnPrimeAtRank (C.n + 1) := by exact_mod_cast C.sharedPrime_ge_five
  exact Real.log_pos (by linarith)

/-- **Hypothèse nommée, jamais posée** : au pas de la cassure, la densité réelle de la paire est celle de la paire
en ligne (deux membres en ligne à la même fréquence). -/
def PairDepositOnLine : Prop :=
  realCountingDensity (zeroPoint C.zero) C.breakLog +
      realCountingDensity (zeroPoint (mirrorMember C.zero)) C.breakLog =
    2 * realCountingDensity C.linePoint C.breakLog

/-- **Ce que `PairDepositOnLine` force** : la densité de ligne s'annule à la cassure, c'est-à-dire
`log p_{n+1} = (π/2 + kπ)/T` — le premier partagé tombe sur un changement de signe de la densité de ligne. -/
theorem pairDepositOnLine_forces_sign_change (h : C.PairDepositOnLine) :
    ∃ k : ℤ, C.breakLog = densitySignChangeLog (rZeroHeight C.zero.1) k := by
  unfold PairDepositOnLine at h
  rw [C.pair_real_density_eq_cosh_line] at h
  have hcosh : 1 < Real.cosh (C.radialShift * C.breakLog) :=
    Real.one_lt_cosh.mpr (mul_pos C.radialShift_pos C.breakLog_pos).ne'
  have hD : realCountingDensity C.linePoint C.breakLog = 0 := by
    have : (2 * Real.cosh (C.radialShift * C.breakLog) - 2) * realCountingDensity C.linePoint C.breakLog = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact h0
  have hT : C.linePoint.im ≠ 0 := by rw [C.linePoint_im]; exact C.zero.2.ne'
  have := (realCountingDensity_eq_zero_iff C.linePoint hT C.breakLog_pos).mp hD
  rwa [C.linePoint_im] at this

/-- Réciproque : sur un changement de signe de la densité de ligne, la paire dépose exactement comme la ligne
(zéro des deux côtés). -/
theorem pairDepositOnLine_of_sign_change (h : ∃ k : ℤ, C.breakLog = densitySignChangeLog (rZeroHeight C.zero.1) k) :
    C.PairDepositOnLine := by
  unfold PairDepositOnLine
  rw [C.pair_real_density_eq_cosh_line]
  have hT : C.linePoint.im ≠ 0 := by rw [C.linePoint_im]; exact C.zero.2.ne'
  have hD : realCountingDensity C.linePoint C.breakLog = 0 := by
    rw [realCountingDensity_eq_zero_iff C.linePoint hT C.breakLog_pos, C.linePoint_im]
    exact h
  rw [hD]
  ring

theorem pairDepositOnLine_iff_sign_change :
    C.PairDepositOnLine ↔ ∃ k : ℤ, C.breakLog = densitySignChangeLog (rZeroHeight C.zero.1) k :=
  ⟨C.pairDepositOnLine_forces_sign_change, C.pairDepositOnLine_of_sign_change⟩

/-- **`PairDepositOnLine` n'implique pas l'obligation de transport et ne la contredit pas** : les deux énoncés sont
indépendants dans le corpus ; le premier contraint la position de la cassure dans la cellule, le second est faux.
(Énoncé compilé : l'obligation reste fausse sous `PairDepositOnLine`.) -/
theorem not_obligation_of_pairDepositOnLine (hON : rZeroRadialPosition C.nextMember.1 = 1 / 2)
    (_h : C.PairDepositOnLine) : ¬ C.RaccordTransportObligation :=
  C.not_raccordTransportObligation hON

end OffCarrier

#print axioms amplitude_from_lastContact
#print axioms energyRatio_from_contacts
#print axioms OffCarrier.pair_transport_from_contacts
#print axioms OffCarrier.obligation_iff_factor_one
#print axioms OffCarrier.not_raccordTransportObligation
#print axioms OffCarrier.obligation_of_link
#print axioms OffCarrier.link_false
#print axioms OffCarrier.break_split_any_packet
#print axioms OffCarrier.pairDepositOnLine_iff_sign_change

end RHV6Fresh
