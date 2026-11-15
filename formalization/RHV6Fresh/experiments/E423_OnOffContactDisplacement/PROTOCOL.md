# E423 — protocole (pré-enregistré 2026-11-03)
1. Hauteurs T* : milieux des couples (1,2), (100,101), (2000,2001) ; β ∈ {0,3, 0,45, 0,49} ; scénarios : ON (½), OFF seule (β), paire
   miroir (β, 1−β). Fenêtre [100, 1000].
2. Par scénario : contacts de chaque membre ; déplacement par rapport aux contacts ON (log et fraction de pas, constance sur k) ;
   valeurs réelles aux contacts déplacés et aux contacts ON ; accord de signe à même k ; rapport des modules (mesuré, prédit) ;
   paire : distance minimale entre les deux ensembles de contacts (fraction de pas) ; Im du membre miroir aux contacts de β
   (rapport à son module) ; passages sur l'axe de la somme de la paire (racines de Im(x^ρ/ρ + x^{ρ'}/ρ') par bissection entre
   changements de signe sur une grille de 64 points par pas) et leur déplacement par rapport aux contacts ON.
3. Contexte collectif : S_F aux 15 contacts ON de T* (famille réelle, 2 001 052 zéros) ; variation apportée par l'insertion
   (valeur, part de |S_F|) ; même mesure aux contacts déplacés.
4. Jumeau mpmath (25 chiffres) : valeurs aux 3 premiers contacts de chaque scénario.
5. Durée < 5 min, nohup, pas de sondage. Résultats descriptifs, consignés tels quels.
