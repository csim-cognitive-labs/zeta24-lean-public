# Audit de compilation — `Terminal/AmplitudeContact.lean` (2026-11-02)

Module isolé (non ajouté à `RHV6Fresh.lean`), écrit en réponse à la question de l'auteur du 2026-11-02 (projection
contre axe réel). Cible : `lake build RHV6Fresh.Terminal.AmplitudeContact`.

## Tentatives (journal complet)
| # | Résultat | Erreur exacte | Correction |
|---|---|---|---|
| 1 | échec (`build_attempt1.log`) | `AmplitudeContact.lean:166:67: unsolved goals … ⊢ meetingPoint I ^ 1 = (meetingPoint I ^ β) ^ 2 * meetingPoint I ^ (1 − β − β)` : `Real.rpow_sub hp` sans arguments a réécrit `p^(1−β)` du membre gauche au lieu de l'exposant `(1−β) − β` du membre droit ; `field_simp` a ensuite laissé le but ci-dessus. Plus un avertissement `show` → `change` (ligne 190). | arguments explicites `Real.rpow_sub hp (1 − β) β` puis `div_mul_div_comm` (les deux lemmes de §3) ; `show` remplacé par `change` |
| 2 | **succès** (`build_attempt2.log`) : `Built RHV6Fresh.Terminal.AmplitudeContact (12s)` ; seuls avertissements : lignes > 100 caractères dans l'en-tête | — | — |

Aucun `sorry`, aucun `admit`, aucune hypothèse nouvelle. Axiomes rapportés par `#print axioms` :
```
RHV6Fresh/Terminal/AmplitudeContact.lean:223:0: 'RHV6Fresh.contactAmplitude_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
RHV6Fresh/Terminal/AmplitudeContact.lean:224:0: 'RHV6Fresh.radial_from_amplitude_step' depends on axioms: [propext, Classical.choice, Quot.sound]
RHV6Fresh/Terminal/AmplitudeContact.lean:225:0: 'RHV6Fresh.OffCarrier.mirror_amplitude_ratio_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
RHV6Fresh/Terminal/AmplitudeContact.lean:226:0: 'RHV6Fresh.amplitudeContactRigidity_iff_riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Dépendances (théorèmes acquis composés)
| Énoncé du module | Dépend de | Statut |
|---|---|---|
| `contactAmplitude_eq`, `meetingDeposit_norm` | `norm_residueTerm_eq` (RemainderRegime), `contactMinusAt_positive` | théorèmes |
| `contactAmplitude_ratio` | `contactAt_consecutive_logWidth` (Tower/Incidences), `Real.rpow_def_of_pos`, `Real.div_rpow` | théorèmes |
| `contactAmplitude_ratio_eq_iff`, `radial_from_amplitude_step` | `contactAmplitude_ratio`, `Real.exp_eq_exp`, `Real.log_exp` | théorèmes |
| `meeting_demand_eq_tsum_deposits`, `gap_demand_eq_deposits` | `smoothedRemainder_eq_tsum_residueTerm` (C126), `one_lt_meetingPoint` | théorèmes |
| `norm_crowdSum_le_amplitudeSum` | `crowdSum_eq_finite_sum` (CollectiveContactRigidity), `norm_sum_le` | théorèmes |
| `OffCarrier.mirror_deposit_ratio`, `mirror_amplitude_ratio_tendsto` | `mirrorMember_radial`, `OffCarrier.zero_low`, `tendsto_rpow_atTop` | théorèmes (sous l'existence d'un porteur, c.-à-d. ¬RH) |
| `amplitudeContactRigidity_iff_riemannHypothesis` | `riemannHypothesis_of_noLowerSide`, `thm_zeroRadialPosition_half_of_riemannHypothesis` | théorème ; le but nommé `AmplitudeContactRigidity` n'est jamais posé |

## Ce que le module établit et ce qu'il laisse
* Établi : le contact porteur d'amplitude (position, amplitude) lit `β` par le pas d'amplitude `exp(βπ/T)` ; contraste
  exact avec `contactLog_step_blind_to_radial`. La demande aux vrais points de rencontre est la somme signée des dépôts
  avec leurs vraies amplitudes. Le rapport miroir/OFF des dépôts croît comme `p^{1−2β}`.
* Laissé : aucune identité ne fixe l'amplitude d'un contact depuis les premiers seuls ; lire `β = 1/2` sur les amplitudes
  EST RH. Le module ne contient donc aucun énoncé dont une paire OFF violerait la conclusion.
