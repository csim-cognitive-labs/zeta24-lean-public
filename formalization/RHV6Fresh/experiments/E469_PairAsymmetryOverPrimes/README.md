# E469 (Ψ3) — l'asymétrie de la paire intégrée sur les premiers — pré-enregistrement (2026-11-13)
Module `Terminal/PairAsymmetryOverPrimes.lean` (isolé). Cible H17 R3' validée par l'auteur. Commit AVANT compilation ; deux tentatives.
## Stratégie (règle R-Ψ)
* Cible : les termes du zéro et du miroir ont le même poids cumulé sur la série des premiers (⟺ ligne).
* Objet cumulé : somme sur les premiers ≤ N du logarithme du rapport des puissances p^{1−β} et p^β = (1 − 2β) θ(N).
* Pourquoi la lecture ponctuelle ne suffit pas : en un premier le rapport est p^{1−2β} (E450), identité vraie pour tout β.
* Signature attendue d'un hors-ligne : cumul non borné, linéaire en la fonction de Tchebychev ; par premier, fraction |1 − 2β| ≤ 1 du poids log p.
* Suite dans les deux issues : si tout compile : écrire le côté premiers (la paire doit être payée sur TOUS les premiers) dans Ψ4/Ψ6 ; sinon consigner.
## Énoncés (A1–A5) : voir l'en-tête du module.
## Jumeau (section Ψ3) : cumul exact sur les premiers ≤ 10^6 pour β ∈ {0,3 ; 0,4 ; 0,45} contre (1−2β)·θ(N) (égalité à 10^-12) ;
croissance linéaire en θ vérifiée ; nullité à β = 1/2.
