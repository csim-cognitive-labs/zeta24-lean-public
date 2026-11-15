# E466 — résultats (2026-11-12) — verdict A : le gain mesuré vient de la suppression de l'amortissement, non de la lecture

Exécution réelle : `logs/run.txt` (1 084 s, `nohup`, borné), `results.json` (28 fenêtres × 4 canaux, scores bruts, marges, erreurs
par catégorie). Méthode, fenêtres, règles et attentes : celles du `README.md` pré-enregistré (commit `8f975ee3`), rien retouché.

## A1 — reproduction d'E464 : vraie
Le canal J-F reproduit E464 fenêtre par fenêtre : mêmes comptes (justes, manqués, faux) et mêmes scores à 3·10^-14 près.

## Tableau principal (famille de 2 001 052 Tours ; « marge » = score min sur premiers − score max sur composés ; R0 = seuil 0,75)

| début | cellule | inédite | premiers | J-F justes | J-F marge | J-noF justes | J-noF marge | D2-F justes | D2-F marge | D2-noF justes | D2-noF marge |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 10^3 | 0,003 | non | 43 | 43 | +0,998 | 43 | +0,997 | 43 | +0,988 | 43 | +0,999 |
| 10^4 | 0,028 | non | 33 | 33 | +0,981 | 33 | +0,979 | 33 | +0,931 | 33 | +0,988 |
| 5·10^4 | 0,139 | OUI | 29 | 29 | +0,915 | 29 | +0,942 | 29 | +0,754 | 29 | +0,945 |
| 10^5 | 0,277 | non | 23 | 23 | +0,840 | 23 | +0,820 | 23 | +0,588 | 23 | +0,899 |
| 1,5·10^5 | 0,416 | OUI | 27 | 27 | +0,727 | 27 | +1,093 | 0 | +0,452 | 27 | +0,805 |
| 2·10^5 | 0,555 | non | 25 | 0 | +0,626 | 25 | +1,153 | 0 | +0,474 | 25 | +0,854 |
| 2,5·10^5 | 0,694 | OUI | 21 | 0 | +0,350 | 21 | +1,000 | 0 | +0,215 | 21 | +0,792 |
| 3·10^5 | 0,832 | non | 22 | 0 | +0,187 | 22 | +0,770 | 0 | +0,107 | 22 | +0,684 |
| 4·10^5 | 1,110 | OUI | 24 | 0 | −0,022 | 18 | +0,390 | 0 | −0,046 | 4 | +0,282 |
| 5·10^5 | 1,387 | non | 25 | 0 | −0,118 | 1 | +0,071 | 0 | −0,125 | 0 | +0,041 |
| 7·10^5 | 1,942 | OUI | 22 | 0 | −0,159 | 0 | −0,170 | 0 | −0,159 | 0 | −0,171 |
| 10^6 | 2,774 | non | 24 | 0 | −0,148 | 0 | −0,403 | 0 | −0,147 | 0 | −0,392 |
| 10^7, 10^8 | ≥ 27 | non | 31 | 0 | < 0 | 0 | < 0 | 0 | < 0 | 0 | < 0 |

Aucun faux positif dans aucune fenêtre, aucun canal (composés et puissances de premiers confondus). Famille de 500 000 Tours : même
image aux mêmes cellules (J-noF exact jusqu'à cellule 0,98 avec marge +0,80, perdu à 1,47 ; J-F perd la marge entre 0,49 et 0,98).

## Sur les fenêtres décidées par R2 (cellule ≤ 1), les deux familles, règle R0 fixe à 0,75
| canal | justes | manqués | faux |
|---|---|---|---|
| J-F (E464) | 260 | 91 | 0 |
| J-noF | 351 | 0 | 0 |
| D2-F | 204 | 147 | 0 |
| D2-noF | 351 | 0 | 0 |

## Lecture, point par point de l'audit
* (B) Le seuil n'était pas le problème principal : avec le même seuil 0,75, le canal sans amortissement est exact sur toutes les
  fenêtres décidées. La marge de J-F s'effondrait à cause de l'amortissement, pas du seuil.
* (C) L'effet de Fejér est MESURÉ : il coûte un facteur d'horizon. Marge positive jusqu'à cellule 0,83 avec Fejér, jusqu'à 1,39 sans
  (famille 2M) ; 0,49–0,98 contre 0,98–1,47 (famille 500k). Rapport entre 1,4 et 2,3 : compatible avec « hauteur efficace divisée par
  deux », pas démontré. Sans Fejér, les oscillations parasites existent bien (erreur sur composés plus forte à 10^5–3·10^5 : 0,09–0,17
  contre 0,06–0,10 avec Fejér) mais la marge reste large car l'erreur sur les premiers chute davantage (0,09 contre 0,45 à 3·10^5).
* (D) La seconde différence du signal intégré n'apporte PAS de résolution : D2-noF est très proche de J-noF (attente A2 confirmée),
  légèrement inférieur au-delà de cellule 1 (4 justes contre 18 à 4·10^5). D2-F est nettement inférieur à J-F : le poids de Fejér
  appliqué au signal intégré amortit davantage. L'erreur de troncature reste dans la seconde différence, mesurée colonne par colonne.
  À 10^8, D2 est en plus limité par la précision flottante du fond (moitié du carré à 5·10^15) : ses scores y sont sans valeur ; J et D2
  avaient de toute façon tous échoué à cette cellule.
* (A, grammaire modulo 6) : aucun faux positif à retirer, la règle R1 ne change aucun compte (attente A4 confirmée). Elle reste
  nécessaire, non suffisante, et n'a rien apporté ici.
* (A, contacts/cellules) : la seule information non circulaire trouvée, la longueur de la cellule la plus fine, sert à l'abstention R2.
  Sur les fenêtres décidées, J-noF et D2-noF sont exacts ; sur les fenêtres différées, J-noF garde une marge positive à cellule 1,11 et
  1,39 (18/24 puis 1/25 avec le seuil fixe) et la perd à 1,94. Le critère R2 « cellule ≤ 1 » est donc prudent et juste : aucune erreur
  sur les fenêtres décidées, et de l'information encore présente au-delà, non exploitée par un seuil fixe.
* (E) Horizon : l'échelle de résolution est confirmée comme variable d'échelle (mêmes régimes aux mêmes cellules dans les deux familles
  et sur les cinq fenêtres inédites, attente A5 confirmée). Elle n'est PAS une impossibilité démontrée ; la rectification de ma phrase
  du 2026-11-12 est maintenue.
* (6) Puissances de premiers : scores 0,49–0,50 sur les carrés présents (10^3, 10^4), à moins de 0,02 de la valeur exacte 1/2, dans les
  quatre canaux ; aucune confusion avec un premier.

## Verdict : A
Un canal (J-noF) possède une marge positive sur des fenêtres où J-F n'en a pas (4·10^5 et 5·10^5, famille 2M ; 10^5, famille 500k).
Le gain vérifié sur fenêtres inédites, sans recours aux premiers pendant la prédiction, vient d'une seule chose : utiliser toute la
hauteur des Tours disponibles au lieu de l'amortir. La grammaire modulo 6 n'a rien ajouté ; les contacts n'ont fourni que la
résolution (abstention). Réponse à la question centrale de l'audit : dans cette expérience, la grammaire et les contacts n'apportent
aucune information discriminante que le score des Tours ne possède pas ; ce négatif est consigné tel quel.

## Ce qui n'est pas acquis
Pas de fenêtre entre cellule 1,39 et 1,94 (horizon de marge positive du canal sans Fejér situé dans cet intervalle) ; fenêtres de 300
entiers ; aucune règle de décision autre que le seuil fixe n'a été évaluée (les scores bruts sont conservés pour cela) ; le million de
chiffres reste hors de portée des Tours disponibles (il faudrait des hauteurs plusieurs fois l'abscisse ; cela reste une échelle de
méthode, non un théorème).
