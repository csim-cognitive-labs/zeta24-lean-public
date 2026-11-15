> Version française conservée à titre de référence. Main language: English, see README.md.

# E467 (Ψ1) — la constance par membre comme loi de série — pré-enregistrement (2026-11-13)
Module `Terminal/MemberConstancySeries.lean` (isolé). Plan Ψ §19.100, cible H3 validée par l'auteur. Commit AVANT compilation ; deux
tentatives au plus, journal exact dans `attempts/`.
## Stratégie (règle R-Ψ)
* Cible : la part relative d'une Tour réalisée reste bornée le long de la série de ses cellules (⟺ ligne, R-RH : non une objection).
* Objet cumulé : suite des parts de cellule (E463) rapportées à l'échelle de la ligne x^{3/2}, composée sur N cellules.
* Pourquoi la lecture ponctuelle ne suffit pas : sur une cellule la part est non nulle pour toute Tour réalisée et rien de plus ; le facteur de cellule n'avait jamais été composé.
* Signature attendue d'un hors-ligne : croissance géométrique de la part relative du miroir, raison e^{π(β−1/2)/T} par cellule, A^{β−1/2} sur une plage de facteur A ; le membre bas s'évanouit ; la paire est non bornée.
* Suite dans les deux issues : si tout compile : côté premiers par Ψ2 ; sinon consigner l'énoncé réclamé par le compilateur et passer à Ψ3 (indépendant).
## Énoncés (C1–C7) : voir l'en-tête du module. Attendu : tous compilent, axiomes standard.
## Jumeau (twin_psi.py, section Ψ1) : 20 premières Tours réelles, 2 000 cellules, part relative constante à 10^-12 ; paire témoin
0,4 / 0,6 à la hauteur du zéro 1 000 : croissance mesurée contre la forme close (erreur relative < 10^-10). Verdict A si tout conforme.
