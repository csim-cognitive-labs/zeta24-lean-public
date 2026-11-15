# E418 — résultats (exécutée le 2026-11-03, 49 s, `logs/e418.log`, `data/e418_results.json`)

Scénario SYNTHÉTIQUE (jamais une constellation de vrais zéros). Base : ligne complète (2 001 052 hauteurs), W1 = [3, 300],
résidu de troncature de la ligne : rms(Λ̂ᴮ − Λ) = 2,85e−4.

## Géométrie d'une Tour déplacée (à la hauteur T, contre la Tour de ligne)

| β | déplacement des contacts (log) | rapport d'amplitude à x = 100 | module 1/|ρ| relatif |
|---|---|---|---|
| 0,30 | (arctan(T/0,3) − arctan(2T))/T ≈ (½−β)/T² : +1,0e−3 (T = 14,1), +3,6e−6 (T = 236), +3,2e−8 (T = 2515) | 100^{−0,2} = 0,398 | ≈ 1 (T ≫ 1) |
| 0,45 | +2,5e−4 (14,1) … | 0,794 | ≈ 1 |
| 0,49 | +5,0e−5 (14,1) … | 0,955 | ≈ 1 |
| miroir 1−β | déplacement opposé, amplitude 100^{+0,2} = 2,51 (β = 0,3) | | |

Le déplacement des contacts est en 1/T² (la phase arctan(T/β) tend vers π/2 pour toute β) : la position radiale est quasi
invisible dans les CONTACTS d'un membre haut ; elle est visible dans l'AMPLITUDE (x^β), et pour la paire miroir, dans
l'amplitude x^{1−β} du membre droit.

## Variation des poids reconstruits ΔΛ̂ = Λ̂(OFF) − Λ̂(ligne), W1

| rang | T | β | scénario | ΔΛ̂ᴮ max | ΔΛ̂ᴮ rms | borne démontrée max | Δ/borne max | ΔΛ̂ᴬ max | reclassements B / A | erreurs de primalité B / A |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 14,13 | 0,30 | Tour seule | 0,197 | 0,083 | 2,65 | 0,50 | 0,202 | 0 / 0 | 0 / 0 |
| 1 | 14,13 | 0,30 | paire miroir | 0,602 | 0,268 | 4,27 | 0,54 | 0,713 | 1 / 2 | 0 / 0 |
| 1 | 14,13 | 0,45 | paire miroir | 0,507 | 0,163 | 4,24 | 0,35 | 0,637 | 0 / 2 | 0 / 0 |
| 1 | 14,13 | 0,49 | paire miroir | 0,501 | 0,157 | 4,24 | 0,33 | 0,632 | 0 / 2 | 0 / 0 |
| 100 | 236,5 | 0,30 | Tour seule | 0,083 | 0,049 | 2,65 | 0,48 | 0,094 | 0 / 0 | 0 / 0 |
| 100 | 236,5 | 0,30 | paire miroir | 0,281 | 0,167 | 4,27 | 0,51 | 0,306 | 0 / 0 | 0 / 0 |
| 100 | 236,5 | 0,49 | paire miroir | 0,132 | 0,077 | 4,24 | 0,31 | 0,155 | 0 / 0 | 0 / 0 |
| 2000 | 2515,3 | 0,30 | Tour seule | 3,8e−3 | 1,2e−3 | 2,65 | 0,024 | 1,8e−2 | 0 / 0 | 0 / 0 |
| 2000 | 2515,3 | 0,30 | paire miroir | 1,36e−2 | 4,3e−3 | 4,27 | 0,026 | 6,3e−2 | 0 / 0 | 0 / 0 |
| 2000 | 2515,3 | 0,45 | paire miroir | 6,1e−3 | 1,9e−3 | 4,24 | 0,016 | 2,8e−2 | 0 / 0 | 0 / 0 |
| 2000 | 2515,3 | 0,49 | paire miroir | 5,7e−3 | 1,8e−3 | 4,24 | 0,016 | 2,6e−2 | 0 / 0 | 0 / 0 |

(Les 18 combinaisons sont dans le journal ; borne = 2[(n−1)^{−½} + Σ_{ρ nouveau}(n−1)^{Re ρ−1}], accroissements finis.)

## Lectures
1. **Borne démontrable tenue** dans les 18 cas (Δ ≤ borne ; rapport max 0,54). La borne est en n^{−β} + n^{β−1} : elle NE
   DÉCROÎT PAS vers zéro plus vite que n^{−½} ; elle est insensible à T. Elle majore le défaut, elle ne l'exclut pas.
2. **Le défaut est mesurable mais n'est pas un détecteur** : à tout rang, ΔΛ̂ᴮ (1,8e−3 à 0,27 en rms) dépasse le résidu de
   troncature de la ligne (2,85e−4) ; pourtant la LECTURE des cassures (règle E416) ne change pas (0 erreur de primalité dans
   les 18 cas ; 1 à 2 reclassements seulement au rang 1, puissances ↔ vides). La reconstruction des écarts reste exacte avec
   un quartet OFF : **l'accumulation par contacts tronquée ne lit pas la position radiale d'un membre**, en accord avec E402,
   E403 (0/1229 au-dessus des bornes) et E406–E411 (3 à 6 ordres sous la borne).
3. **Paire miroir contre Tour seule** : la paire miroir (symétries de ζ respectées) produit un défaut 3 à 8 fois plus grand
   que la Tour seule, dominé par le membre droit 1−β (amplitude x^{1−β}) : c'est le membre à grande partie réelle qui porte la
   perturbation (E405 : `off_member_forces_raw_excess_at_event` lit `Re ρ > θ`).
4. **Compensation collective** : en libérant les amplitudes de 1 000 zéros de ligne (hauteurs conservées), les moindres carrés
   annulent ΔΛ̂ᴮ sur W1 au résidu relatif 3,3e−15 avec des coefficients ≤ 9,7e−3 : la compensation est POSSIBLE à troncature
   finie par des amplitudes réelles non entières. Ces coefficients ne sont pas des multiplicités (entiers ≥ 0) : la
   compensation n'est donc pas réalisable par de vrais zéros SANS changer leurs hauteurs ; mais rien ici n'exclut une
   compensation par des hauteurs différentes. **Aucune borne démontrable excluant la compensation n'a été obtenue** ; une telle
   borne (reste ≤ C·E^{1/2+ε} aux rencontres) est équivalente à RH (`riemannHypothesis_of_contact_accumulation_bound`).
5. Aucune conclusion sur RH n'est tirée de ces mesures (critère iv).
