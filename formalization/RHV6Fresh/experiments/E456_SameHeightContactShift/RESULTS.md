# E456 — Résultats (2026-11-08 ; pré-enregistrement 33c36e43)

## Lean K6 — `RHV6Fresh/Terminal/SameHeightContactShift.lean` (isolé)
Tentative 1 verte (`attempts/build_attempt1.txt`, 9 093 tâches) ; sonde scratch : probe1 (M4 : deux réécritures manquées), probe2 EXIT 0 ;
0 avertissement dans le module ; 6/6 énoncés sur `[propext, Classical.choice, Quot.sound]` (`attempts/axioms_attempt1.txt`) ; grep du
ban 0 ; `lake build RHV6Fresh` complet vert (`logs/lake_build_full.txt`, 9 064 tâches).
M0 phases de même hauteur à moins d'un quart de tour ; M1 aucun contact partagé à même hauteur (tous indices) ; M2 un OFF de hauteur T ne
prend aucune rencontre de la Tour de ligne de hauteur T ; M3 rencontre commune ⟹ hauteurs différentes ; M4 décalage < demi-cellule ;
M5 pas `e^{π/T}` aveugle à β.

## Volet déterministe — `e456_causal_mod6_contact_shift.py` (sortie `logs/e456_output.txt`, `logs/e456_run.txt`)
* P1 jumeau exact (rapports de cellule 4·10⁻¹⁶ ; décalage ≤ 0,009 demi-cellule ; grilles jamais confondues).
* P2 : effectifs du texte sur 5 000 écarts EXACTS (994, 1 490, 1 490, 1 026) ; cadre faux (9 590 premiers / 799 fenêtres = 9 588
  transitions : 1 915, 2 868, 2 868, 1 937) ; bilan orienté ∈ {−1, 0}, nul ⟺ mêmes états aux bouts ; énumération : 11,28 / 44,36 /
  44,36 % (texte 10,5 / 43,8 / 43,8 faux) ; « A » 51,9 % reproduit par aucune définition pré-écrite ; fenêtres réelles 13,27 / 42,55 /
  44,18 % (texte 10,6 / 40,4 / 42,4 faux) ; biais des maintiens 41,8 %.
* P3 Gauss : NON à douze (khi-deux 28,9 / 10 ddl contre la binomiale ajustée, sous-dispersion 0,92) ; normale approchée aux fenêtres
  de 120–1 200 ; dérive aux grandes fenêtres (dispersion 4,4 à 12 000).
* P4 causalité : β → Jaccard des écarts touchés 0,992, composition mod 6 identique à 10⁻⁴, contingence nulle (p médiane 0,81) ;
  T → Jaccard 0,24, tout change. Le résidu mod 6 n'est lu par aucune Tour, ON ou OFF.

## Verdict
A pour K6 et P1 ; B pour l'audit préalable (e1 rectifiée : effectifs justes, cadre faux). Aucune contradiction OFF ; frontière
inchangée ; rien du texte collé n'est ajouté au corpus (E427 le contenait exactement).
