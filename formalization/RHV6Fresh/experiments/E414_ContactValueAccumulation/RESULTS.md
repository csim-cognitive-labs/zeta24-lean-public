# E414 — résultats (exécutée le 2026-11-03, 69 s, `logs/e414.log`, `data/e414_results.json`)

**Verdict : identité vérifiée à l'arrondi dans les 12 cas ; théorème Lean compilé** (`contact_accumulation_eq_endpoint_difference`,
`finite_contact_accumulation_eq_spectral_difference`). Niveaux 1 et 2 de la mission atteints.

| Zéros | [a, x] | Canal | Contacts | Somme complexe A | |A − (F(x)−F(a))| | relative | borne d'arrondi | max par zéro | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 3 | [2, 50] | brut | 61 | −0,37778 − 0,31945 i | 1,6e−16 | 3,2e−16 | 2,0e−14 | 2,3e−16 | ARRONDI |
| 3 | [2, 50] | intégré | 61 | −0,02597 + 0,02465 i | 1,6e−17 | 4,3e−16 | 1,0e−15 | 2,0e−17 | ARRONDI |
| 40 | [2, 50] | brut | 3 113 | −0,74588 − 0,67798 i | 5,6e−16 | 5,5e−16 | 2,6e−13 | 7,4e−16 | ARRONDI |
| 40 | [2, 50] | intégré | 3 113 | −0,03470 + 0,03012 i | 3,5e−17 | 7,7e−16 | 4,5e−15 | 2,0e−17 | ARRONDI |
| 300 | [2, 50] | brut | 95 282 | −0,64561 − 1,02316 i | 2,0e−15 | 1,7e−15 | 1,9e−12 | 7,4e−16 | ARRONDI |
| 300 | [2, 50] | intégré | 95 282 | −0,03680 + 0,02950 i | 3,5e−17 | 7,5e−16 | 1,0e−14 | 2,0e−17 | ARRONDI |
| 5 000 | [2, 50] | brut | 15 163 512 | −0,64098 − 1,29799 i | 7,0e−15 | 4,8e−15 | 3,2e−11 | 7,4e−16 | ARRONDI |
| 5 000 | [2, 50] | intégré | 15 163 512 | −0,03702 + 0,02949 i | 6,3e−17 | 1,3e−15 | 2,3e−14 | 2,0e−17 | ARRONDI |
| 100 000 | [100, 102,5] | brut | 31 198 828 | −1,06023 + 1,08475 i | 5,3e−15 | 3,5e−15 | 1,4e−11 | 3,0e−17 | ARRONDI |
| 100 000 | [100, 102,5] | intégré | 31 198 828 | +0,03007 + 0,04452 i | 6,9e−18 | 1,3e−16 | 1,1e−15 | 8,7e−19 | ARRONDI |
| 2 001 052 | [1000, 1000,085] | brut | 32 036 264 | +0,04334 − 0,02203 i | 1,3e−15 | 2,7e−14 | 3,2e−12 | 4,8e−17 | ARRONDI |
| 2 001 052 | [1000, 1000,085] | intégré | 32 036 264 | +5,18e−5 + 4,33e−5 i | 4,9e−20 | 7,3e−16 | 2,3e−17 | 8,5e−22 | ARRONDI |

- Parties réelle et imaginaire : toutes deux reproduites (les sommes complexes sur les hauteurs positives seules ne sont pas réelles ;
  la réalité n'apparaît qu'avec la branche conjuguée, `finite_contact_accumulation_real`).
- Contributions de bord : incluses dans chaque cas (de 61 à 32 millions de contacts complets) ; sans elles l'identité est fausse.
- Précision : en float32 (300 zéros, brut), l'erreur passe de 2,0e−15 à 8,0e−6 : l'écart est entièrement un effet d'arrondi.
- Conséquence (Lean, `contact_accumulation_partition_independent`) : le découpage par contacts conserve valeurs, phases et
  signes, et ne crée aucune information au-delà de F(x) − F(a).
