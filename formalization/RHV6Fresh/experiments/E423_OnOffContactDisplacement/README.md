# E423 — Comparaison ON/OFF aux contacts : déplacements réels des contacts et valeurs associées (pré-enregistrée 2026-11-03)

Objectif : comparer, à la même hauteur T* (milieu de deux zéros réels consécutifs : jamais la hauteur d'un zéro réel), une
Tour ON (β = ½) et une Tour OFF (β ≠ ½, seule ou en paire miroir β, 1−β), en conservant les vrais déplacements des contacts
et les valeurs réelles aux contacts déplacés. Scénario synthétique, fichier séparé, sans premiers, écarts, cellules ni li.

Prédictions (module Lean `ContactRealValue.lean`, écrites avant exécution) :
* déplacement logarithmique du contact k : (φ(β) − φ(½))/T*, le même pour tout k, de module < π/(2T*) (moins d'un demi-pas) ;
* valeur au contact déplacé : (−1)^k C_k(β)^β/|ρ_β| contre (−1)^k C_k(½)^{½}/|ρ_½| : même signe à même k, rapport des modules
  C_k(β)^β |ρ_½| / (C_k(½)^{½} |ρ_β|) ;
* paire miroir : les contacts de β et de 1−β ne coïncident jamais (β ≠ ½) ; au contact du membre β, le membre 1−β a une partie
  imaginaire non nulle ; la somme des deux membres (avec conjugués) passe sur l'axe en des positions propres (racines de Im de la
  somme complexe), à mesurer et à comparer aux contacts ON ;
* dans la famille des 2 001 052 zéros de ligne (E422), l'insertion de la Tour OFF ou de la paire change S_F aux contacts ON de
  la hauteur T* de la seule contribution insérée (identité), que l'on mesure en valeur et en part.
Aucune de ces mesures n'est lue comme une exclusion des zéros OFF.
