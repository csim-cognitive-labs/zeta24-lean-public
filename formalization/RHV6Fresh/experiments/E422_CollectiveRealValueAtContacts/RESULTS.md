# E422 — résultats (exécutée le 2026-11-03, 120 s ; une première passe interrompue pour mémoire (histogramme de phases sur
une matrice de 16 Go, journal `logs/e422_run1_interrompue_memoire.log`), remplacée par un sous-échantillon déterministe ;
aucun autre changement ; `data/e422_collective.json`)

Définition appliquée (fixée au pré-enregistrement) : S_N(x) = Σ_{j ≤ N} 2Re(x^{ρ_j}/ρ_j) aux contacts x = C_k d'une Tour de
rang r, famille des N premiers zéros posés sur la ligne ; valeur propre 2v_k = 2(−1)^k C_k^{½}/|ρ_r| ; reste = S_N − 2v_k
(les autres Tours évaluées à la même position). Aucune comparaison arithmétique. Jumeau mpmath (25 chiffres, N = 100,
3 contacts de la Tour 1) : écart 7,7e−14.

## Somme collective aux contacts, par Tour et par taille de famille (fenêtre [100, 1000])

| Tour (rang, T) | contacts | rms valeur propre | N | part propre médiane |2v|/|S| | accord de signe v/S | rms S_N | rms reste | rms(S_N − S_{N préc.}) |
|---|---|---|---|---|---|---|---|---|
| 1 (14,13) | 10 | 2,80 | 10 / 1 000 / 2 001 052 | 1,24 / 0,87 / 0,79 | 0,90 / 0,90 / 0,90 | 3,53 / 4,75 / 4,83 | 3,09 / 3,09 / 2,93 | — / 1,22 / 0,058 |
| 2 (21,02) | 15 | 1,87 | 10 / 1 000 / 2 001 052 | 1,02 / 0,70 / 0,96 | 0,73 / 0,53 / 0,53 | 3,38 / 3,95 / 4,02 | 2,59 / 3,68 / 3,70 | — / 1,55 / 0,007 |
| 3 (25,01) | 18 | 1,59 | 10 / 1 000 / 2 001 052 | 0,69 / 0,43 / 0,44 | 0,72 / 0,89 / 0,78 | 3,37 / 4,05 / 4,01 | 2,95 / 3,06 / 3,09 | — / 1,45 / 0,011 |
| 100 (236,5) | 173 | 0,167 | 10 / 1 000 / 2 001 052 | 0,083 / 0,060 / 0,064 | 0,48 / 0,52 / 0,52 | 3,08 / 3,81 / 3,80 | 3,09 / 3,80 / 3,78 | — / 1,44 / 0,115 |
| 1 000 (1 419,4) | 1 040 | 0,0279 | 10 / 1 000 / 2 001 052 | 0,013 / 0,010 / 0,010 | 0,50 / 0,50 / 0,51 | 3,08 / 3,89 / 3,94 | 3,08 / 3,89 / 3,94 | — / 1,43 / 0,068 |

(valeurs intermédiaires N = 100, 10⁴, 10⁵ dans le fichier de données ; la variation entre N = 10⁵ et 2 001 052 est de 0,007 à
0,115 en rms : la somme collective aux contacts est stabilisée à cette taille, sur cette fenêtre.)

* **La valeur propre n'est jamais la somme** : aux contacts de la Tour 1 elle en fait environ 0,8 en médiane et le signe de S
  suit celui de v_k dans 9 cas sur 10 ; dès le rang 100 la part propre tombe à 6 % et le signe de S est indépendant du signe
  propre (accord ≈ ½). Aux contacts d'une Tour haute, S est le reste des autres Tours, à l'arrondi près.
* **Les autres Tours ne se rangent nulle part** : l'histogramme de leur phase (position dans leur propre cycle, en fraction
  de π) aux contacts de la Tour r est plat pour toutes les Tours et toutes les familles (classes à ±3 %).
* **Le reste est de même taille partout** : rms du reste 2,9 à 3,9 pour les cinq Tours, indépendant de la Tour hôte ; c'est la
  somme collective réelle elle-même (rms de 3,5 à 4,8 sur [100, 1000]) et non une quantité liée au contact.
* Exemple (Tour 1, 10 contacts, N = 2 001 052) : S = −0,58, 4,67, −1,84, 1,51, −3,93, −0,60, −3,99, 11,03, −5,22, 5,00 ;
  à N = 10 : −1,37, 1,21, −0,47, 2,95, −4,34, 1,15, −2,24, 8,13, −2,76, −3,67. L'alternance stricte de la valeur propre ne se
  transmet pas à la somme (le dernier contact change de signe entre N = 10 et N = 2 001 052).

Conclusion descriptive : évaluée aux positions des contacts, la somme collective se décompose exactement en valeur propre
réelle plus les autres Tours à la même position (`collectiveAxisSum_at_contact`) ; les contributions des autres Tours y sont
des valeurs hors contact, de phases équiréparties, dont la somme domine dès que la Tour hôte n'est pas l'une des toutes
premières. Les contacts d'une Tour ne sont pas des points remarquables de la somme collective. Rien ici n'exclut un zéro OFF.
