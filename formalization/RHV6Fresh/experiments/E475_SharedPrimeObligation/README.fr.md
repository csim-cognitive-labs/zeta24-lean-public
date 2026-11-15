> Version française conservée à titre de référence. Main language: English, see README.md.

# E475 — Mesures M1–M3 à la rencontre au premier partagé (pré-enregistrement, 2026-11-14)

Ordre de l'auteur (§19.108) : chercher la contrainte que la reconstruction exacte d'un écart impose à la première Tour OFF au premier
partagé, sans construction géométrique sans obligation arithmétique ; jamais de coïncidence contact/premier. Audit préalable :
`AUDIT_20261114.md` (tableau O1–O7, question Q475). Ici : MESURES seulement, aucun module Lean, aucune hypothèse de contradiction.

## Stratégie (R-Ψ)
Objets compilés reproduits à l'identique dans le jumeau (définitions, pas approximations) :
- `canonicalMember n` = membre supérieur précédé d'exactement `n` membres (zéro numéro `n+1` par hauteur croissante) ;
- `occurrence z = fnPrimeAtRank (nZeroSourceIndex z)` ; `expectedMinimumPrime z = fnPrimeAtRank (index + 1)` ; `fnPrimeAtRank 0 = 2` ;
- raccord `e = canonicalMember n → l = canonicalMember (n+1)` au premier partagé `M = expectedMinimumPrime e = occurrence l` ;
- `meetingPoint ⟨n⟩ = fnPrimeAtRank (n+1)` ; `sharedPrime_eq_meeting : M = meetingPoint (occurrenceGap e)` ;
- `imposedShare w I = memberJoint σ_w (meetingPoint I) − memberJoint σ_w I.lower`, avec
  `memberJoint σ x = −m · (x^β/N) · exp(i(T log x − θ))`, `N = ‖ρ‖·‖ρ+1‖`, `θ = arctan(T/β) + arctan(T/(β+1))` (`imposedShare_at_meeting`) ;
- `energyRatio e l q = ‖zeroTerm l q‖/‖zeroTerm e q‖ = q^{β_l−β_e}·‖ρ_e‖/‖ρ_l‖` (`energyRatio_eq`) ;
- `pairJoint l x = memberJoint l x + memberJoint (mirrorMember l) x` (M3, paire fictive `(β,T_l)`, `(1−β,T_l)`).
Données : zéros d'Odlyzko (`experiments/data/odlyzko_zeros6_2001052.txt`, `β = 1/2`, multiplicité 1 : hypothèse de calcul consignée,
jamais une prémisse Lean), premiers par crible. Raccords `n = 0 … 1999` (mesures détaillées sur les dix premiers).

## Mesures et seuils (écrits AVANT exécution)
**M1** — Pour `n = 0 … 1999` : `M_n = p_{n+1}` calculé par les deux définitions (`expectedMinimumPrime e`, `occurrence l`) et comparé à
`meetingPoint ⟨n⟩`. Test : égalité entière exacte partout (ce point est un théorème compilé ; le jumeau vérifie l'indexation).
**M2** — Pour chaque `n` : `s_e = imposedShare e ⟨n⟩`, `s_l = imposedShare l ⟨n⟩` (formule compilée), rapport `r_n = |s_l|/|s_e|`, et
transport `E_n = energyRatio e l M_n` (sur la ligne `‖ρ_e‖/‖ρ_l‖`). Contrôle d'identité : `|s_w|` contre la forme close
`(m/N_w)·|p_{n+1}^{1/2} e^{iT_w log p_{n+1}} − p_n^{1/2} e^{iT_w log p_n}|` (résidu < 1e-12). Test principal : `|r_n/E_n − 1| < 1e-6` sur les
dix premiers raccords. Si échec : consigner la décomposition exacte `r_n/E_n = (‖ρ_e+1‖/‖ρ_l+1‖)·(Φ_l/Φ_e)` avec `Φ_w = |p_{n+1}^{1/2}
e^{iT_w log p_{n+1}} − p_n^{1/2} e^{iT_w log p_n}|` (facteur de phase de l'écart lu par la fréquence du membre), et la loi de `Φ_l/Φ_e` en `n`
(médiane, quartiles, par tranches de 200 raccords).
**M3** — Contrôle de sensibilité radiale : au membre `l`, substituer la paire fictive `(β, T_l)`, `(1−β, T_l)` pour `β ∈ {0,30 ; 0,40 ;
0,45 ; 0,50}` ; mesurer `|pairShare|/|s_e|` et sa variation relative par rapport à `β = 1/2` (où la paire vaut `2 s_l`). Test : variation
relative > 1e-3 pour `β = 0,40` sur au moins un des dix premiers raccords ⟹ « sensible » ; sinon « insensible » (la relation relèverait
d'O1–O5 et ne serait pas la contrainte).

## Verdicts
A : M1 exact, M2 < 1e-6, M3 sensible. B : M1 exact, M2 échoue mais loi consignée, M3 quelconque. C : M1 échoue (indexation fausse).
Aucun verdict ne conclut sur RH ; rien n'est déclaré manquant qui ne manque pas ; R-RH.
