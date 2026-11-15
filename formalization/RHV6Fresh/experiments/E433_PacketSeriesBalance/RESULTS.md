# E433 — Résultats (2026-11-04)

Pré-enregistrement : commit f378dff1. Compilation seule, aucun jumeau requis.

## Sondes (`SeriesBalanceProbe_SCRATCH.lean`, supprimé après capture)
- Tentative 1 (`logs/probe_attempt1.txt`) : 3 erreurs — une réécriture `Real.rpow_one` mal ordonnée dans les deux
  normes (corrigée en explicitant `Real.rpow_add hx 1`), plus les deux buts de sonde. Tous les bilans de série passent.
- Tentative 2 (`logs/probe_attempt2.txt`) : seules les deux sondes restent ouvertes (buts exacts ci-dessous).

### S1 — « complément de la paire nul sur tous les pas d'une fenêtre ⟹ False »
But laissé par le compilateur : `0 = Σ_{k<m} Λ(a+k+1) − (pas du fond en a+m − pas du fond en a) −
(P(a+m+1) − P(a+m) − (P(a+1) − P(a)))`, où `P` est la primitive des quatre membres de la paire. Pas de contradiction :
un complément silencieux impose que le contenu arithmétique de la fenêtre soit exactement l'effet de bords de la
paire. Conforme à l'attendu.

### S2 — « complément de la paire borné en norme sur la série des fenêtres ⟹ False »
But laissé : la famille des bilans `Σ complément = Σ reste exact − effet de bords`, avec la borne. Pas de
contradiction : il faudrait que la croissance `N^{1−β}` du pas local de la paire excède celle du contenu arithmétique
des fenêtres, c'est-à-dire un exposant du reste strictement inférieur à `1 − β` — l'exposant du reste lui-même
(`RemainderExponent.lean`, ⟺ RH). Conforme à l'attendu.

## Module `Terminal/PacketSeriesBalance.lean` (isolé, 10 déclarations, aucun `sorry`)
- Une tentative (`logs/lean_attempt1.txt`, EXIT=0) ; 7 `#print axioms` standards.
- `packetIncrement_series_telescopes`, `remainderIncrement_series_arithmetic`, `complement_series_balance` (tout
  paquet) ; `pairPrimitive`, `channelPrimitive_packet_eq`, `localPacket_pair_eq`, `pair_complement_series_balance`,
  `pair_series_eq_boundary`, `norm_mirror_primitive_term`, `norm_zero_primitive_term` (paire, cas (a)).
- `lake build RHV6Fresh` : « Build completed successfully (9064 jobs) », EXIT=0 (`logs/lake_build_full_trimmed.txt`).

## Verdict
L'effondrement aux bords est compilé : sur toute série de pas consécutifs, la paire n'entre dans le bilan que par sa
primitive aux deux bords de la fenêtre ; les pas intérieurs s'annulent exactement. « Absorber sur la série » n'est
donc pas une condition pas à pas mais une seule équation par fenêtre, entre le contenu arithmétique de la fenêtre et
l'effet de bords de la paire, de croissance `N^{1−β}` par le membre miroir. Aucune contradiction ; le chaînon restant
est exactement l'exposant du reste.
