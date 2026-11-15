/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Direct.MirrorCount
import RHV3Lean.Objects.Universalization

/-!
# RHV6Fresh — niveau UNIVERSALISATION (maîtres finaux 2026-09-23, §9 ; destruction de V, 2026-09-26)

`RiemannHypothesis` n'apparaît **que** dans ce module et dans le raccord `RHV6Closure.lean`.  Aucun
module de géométrie ou de lecture arithmétique ne l'utilise comme hypothèse ni comme théorème parent.

Le sens `RiemannHypothesis → …` n'est jamais étudié ni mentionné (maîtres finaux §9, §10).

**Destruction (auteur, 2026-09-26)** : tout ce qui câblait une conclusion `RiemannHypothesis` sur la
notion « V » (dernier rayon de la seconde Tour comparé à `p_min(z)`, une référence d'un AUTRE zéro, via
l'inversion d'une cellule fixe) — `riemannHypothesis_of_constats`, `mirror_lock_iff_counted_lt`,
`riemannHypothesis_of_pairTowers`, `riemannHypothesis_of_pairTowers_counted`,
`riemannHypothesis_of_secondTower_readings`, et le module `Terminal/PairContradiction.lean`/
`Terminal/TwoTowersComparison.lean` qu'ils instanciaient — est retiré. Seule reste la chaîne
RHV3Lean, jamais remise en cause : aucun zéro hors droite ⟹ RH.
-/

namespace RHV6Fresh

open RHV3Lean

/-- Aucun zéro OFF ⇒ hypothèse de Riemann (RHV3Lean, universalisation compilée). -/
theorem riemannHypothesis_of_noOff
    (h : ∀ z : TrueZero, ¬ PIsOffCriticalLine z.1) : RiemannHypothesis := by
  apply thm_riemannHypothesis_of_allUpperOnCriticalLine
  intro z
  exact not_ne_iff.mp (h z)

/-- Aucun membre de côté `β < 1/2` ⇒ hypothèse de Riemann (via `off_lowerSide`). -/
theorem riemannHypothesis_of_noLowerSide
    (h : ∀ z : TrueZero, ¬ rZeroRadialPosition z.1 < 1 / 2) : RiemannHypothesis := by
  apply riemannHypothesis_of_noOff
  intro z hOff
  rcases off_lowerSide hOff with hz | hm
  · exact h z hz
  · exact h (mirrorMember z) hm

end RHV6Fresh
