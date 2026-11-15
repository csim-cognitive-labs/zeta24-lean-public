# E415 — résultats (exécutée le 2026-11-03, 94 s, `logs/e415.log`, `data/e415_results.json`, `data/e415_W*_full.txt`)

Aucune donnée arithmétique n'est entrée dans le calcul de Λ̂ (validation après coup). Erreur E_H(n) = Λ̂_H(n) − Λ(n).

## W1 = [3, 300] (298 entiers, 61 premiers, 17 puissances, 220 vides)

| Zéros | γ_max | A (brut) rms / max | A premiers / vides | B (intégré) rms / max | B premiers / vides |
|---|---|---|---|---|---|
| 3 | 25,0 | 1,866 / 4,73 | 3,62 / 1,02 | 1,866 / 4,73 | 3,62 / 1,02 |
| 10 | 49,8 | 1,822 / 5,13 | 3,49 / 1,03 | 1,822 / 5,13 | 3,49 / 1,03 |
| 40 | 123,0 | 1,671 / 4,94 | 3,07 / 1,06 | 1,673 / 4,94 | 3,08 / 1,05 |
| 100 | 236,5 | 1,434 / 4,75 | 2,44 / 1,04 | 1,439 / 4,74 | 2,48 / 1,02 |
| 300 | 541,9 | 0,917 / 3,92 | 1,34 / 0,79 | 0,933 / 3,78 | 1,44 / 0,77 |
| 1 000 | 1 419,4 | 0,316 / 0,98 | 0,53 / 0,24 | 0,211 / 0,63 | 0,36 / 0,15 |
| 5 000 | 5 447,9 | 0,0925 / 0,370 | 0,152 / 0,070 | 0,0597 / 0,191 | 0,102 / 0,043 |
| 10 000 | 9 877,8 | 0,0468 / 0,191 | 0,075 / 0,037 | 0,0325 / 0,111 | 0,055 / 0,023 |
| 100 000 | 74 920,8 | 0,0061 / 0,0269 | 0,0098 / 0,0048 | 4,3e−3 / 1,4e−2 | 7,4e−3 / 3,1e−3 |
| 1 000 000 | 600 269,7 | 6e−4 / 3,0e−3 | 8e−4 / 6e−4 | 5,4e−4 / 1,8e−3 | 9,2e−4 / 3,9e−4 |
| 2 001 052 | 1 132 490,7 | 3e−4 / 1,4e−3 | 5e−4 / 3e−4 | 2,9e−4 / 9,4e−4 | 4,9e−4 / 2,1e−4 |

## W2 = [10000, 10060] (4 premiers) et W3 = [100000, 100030] (2 premiers)

| Zéros | W2 A rms / max | W2 B rms / max | W3 A rms / max | W3 B rms / max |
|---|---|---|---|---|
| ≤ 1 000 | ≈ 2,3 / 8,6 | ≈ 2,3 / 8,6 | ≈ 2,84 / 10,7 | ≈ 2,84 / 10,7 |
| 5 000 | 1,978 / 6,60 | 1,978 / 6,60 | 2,832 / 10,62 | 2,832 / 10,62 |
| 10 000 | 1,813 / 5,35 | 1,810 / 5,38 | 2,822 / 10,92 | 2,822 / 10,92 |
| 100 000 | 0,453 / 1,44 | 0,302 / 0,907 | 2,610 / 9,24 | 2,610 / 9,25 |
| 1 000 000 | 0,0265 / 0,064 | 0,0334 / 0,0975 | 0,576 / 2,07 | 0,345 / 1,12 |
| 2 001 052 | 0,0298 / 0,097 | 0,0179 / 0,0519 | 0,297 / 0,907 | 0,181 / 0,596 |

## Lectures
- **Critère (i) tenu** : B converge comme 1/T_max : B_rms·T_max = 325, 321, 323, 323, 323 pour 5 000 → 2 001 052 zéros (E417) ;
  aux événements comme hors événements (rapport ≈ 2 constant).
- **Critère (ii) tenu** : A (brut) converge plus lentement (A_rms·√T_max décroît : 6,8 → 0,36), et au voisinage des
  événements le dépassement de Gibbs du canal brut est constant (E417) : mais aux demi-entiers le résidu de A reste
  comparable à celui de B (3e−4 contre 2,9e−4 sur W1 à troncature complète).
- **Critère (iii) tenu** : C = D à 6,7e−16 sur 30 212 600 contacts (5 000 zéros, n = 3..60).
- Le nombre de zéros nécessaire croît avec x : W1 lisible dès 1 000 zéros, W2 (x ≈ 10⁴) dès 10⁵, W3 (x ≈ 10⁵) dès 10⁶
  (il faut T_max ≳ πx : E404, E417). À x = 10⁵, l'erreur max reste 0,6 (B) avec les 2 001 052 zéros.
- Les approches A, B, C, D ne sont pas sélectionnées sur les résultats : elles sont toutes rapportées.
