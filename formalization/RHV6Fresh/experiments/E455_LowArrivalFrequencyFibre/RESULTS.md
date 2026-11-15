# E455 — Résultats (2026-11-08, tentative 1 verte)

* Sonde scratch (`attempts/probe1.txt`) : EXIT=0 ; un avertissement « hypothèse `hlow` non utilisée » sur M1 → l'hypothèse
  radiale est RETIRÉE de M1 : la montée de hauteur sous historique sur la ligne vaut pour TOUTE arrivée. Fait consigné : l'OFF
  prend sa hauteur neuve exactement comme un ON l'aurait prise.
* Module `RHV6Fresh/Terminal/LowArrivalFrequencyFibre.lean` : 6 déclarations (M1–M6), 0 avertissement
  (`attempts/build_attempt1.txt`, 9098 jobs), 6/6 sur `[propext, Classical.choice, Quot.sound]` (`attempts/axioms_attempt1.txt`),
  grep du ban vide, `lake build RHV6Fresh` complet vert (`logs/lake_build_full.txt`, 9064 jobs). Scratch supprimé.
* Aucune amplitude ; ordre et hauteurs seuls.

## Verdict A — conforme à la réponse consignée d'avance
* (a) « un OFF ne peut pas prendre la hauteur d'un ON occupée » : VRAI et compilé pour tout ON de son historique (M1) ; OUVERT pour
  un ON qui viendrait après lui à sa hauteur : c'est `NoMixedHeight` (⟸ RH), réfutée par toute fibre mixte (M5) ; le côté du
  successeur de l'entrée basse décide (M2–M4).
* (b) « un OFF ne peut pas atteindre le prochain ON » : compilé sous la forme « jamais dépassé » (M1 second point, M6) ; atteint
  seulement dans la fibre mixte.
* (c) « sa fréquence est forcément affectée » : compilé comme RÉPÉTITION (fibre ≥ 2, deux rangs consécutifs à la même
  fréquence, passage gelé), non comme valeur différente.
* AUCUNE contradiction. Frontière inchangée : prémisse unique ⟺ RH ; `NoMixedHeight` ⟸ RH, non dérivée.
