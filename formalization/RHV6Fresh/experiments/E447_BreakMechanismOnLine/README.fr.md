> Version française conservée à titre de référence. Main language: English, see README.md.

# E447 — Le mécanisme de cassure sur la ligne critique, écrit avec les contacts (pré-enregistrement, §19.69, 2026-11-07)

Ordre de l'auteur (R-LIGNE) : tant qu'il reste du Lean à écrire, ne pas chercher la contradiction ; maîtriser
parfaitement le mécanisme de cassure depuis la ligne (zéros ON, `β = 1/2`) avant toute déduction sur les OFF.
Objets autorisés : une Tour `(1/2, T)`, ses contacts, ses cellules, ses valeurs réelles aux contacts ; les
premiers, `rawDemand`, `cellDemand`, `cellWeight`, `cellPrimeWeight` ; les règles signées. Aucune somme de Tours,
aucun objet spectral, aucune hypothèse, aucun énoncé sur `β ≠ 1/2`.

## Hypothèses (à décider par le compilateur, puis par le nombre)
* H1 (attribution exacte) : la cassure `log q` au premier `q` entre dans le budget pondéré avec la valeur du
  dernier contact avant `q` ; sur la ligne cette valeur est EXACTEMENT `√q · e^{−π f/(2T)} / ‖(1/2, T)‖` avec `f`
  la fraction de cellule au point `q` ; donc comprise entre `√q · e^{−π/(2T)}` et `√q` (sur la norme).
* H2 (bilan d'Abel) : la somme pondérée des pentes de cellules d'un bloc est, EXACTEMENT, le terme de bord
  (valeur × demande brute aux deux contacts extrêmes) plus `(1 + e^{π/(2T)})` fois la somme pondérée des demandes
  brutes aux contacts intérieurs : le budget collectif se lit sur la demande brute AUX CONTACTS, pas sur les cellules.
* H3 (règle du carré sur la ligne) : le carré de la valeur au contact est l'abscisse du contact sur le carré de la
  norme ; le rapport des carrés de deux valeurs consécutives est le rapport des longueurs de cellules.
* H4 (cassure puis descente) : dans une cellule qui ne franchit qu'un poids, la demande brute entre le contact et le
  premier vaut `log q − (q − C_k)` : montée d'un coup, descente linéaire.
* H5 (taille de la demande pondérée aux contacts) : `|v_k · R(C_k)| / C_k^{3/2} → 0` le long de la Tour (PNT porté).

## Énoncés prévus (module isolé `Terminal/BreakMechanismOnLine.lean`, import `MeetingRegimeFinite`)
L1 `demandAtContact`, `cellDemand_telescope` ; L2 `valueCellSum_abel` (toute `β`), `contactRealValue_succ`,
`valueCellSum_abel_signed` ; L3 `line_contactRealValue_sq`, `line_value_sq_succ`, `line_value_sq_ratio_eq_length_ratio` ;
L4 `contact_of_fraction` (`C_k = x·e^{−π f/T}`), `line_break_amplitude_exact`, `line_break_amplitude_bounds`,
`line_break_price_bounds` ; L5 `rawDemand_prime_from_contact`, `break_then_descent` ; L6 `demandAtContact_div_tendsto_zero`,
`line_weighted_demand_at_contact_small`. Deux tentatives de compilation au plus, chaque sortie conservée dans `attempts/`.

## Expérience (après compilation ; zéros d'Odlyzko, `β = 1/2`, 7 hauteurs, premiers ≤ 10⁷)
(a) résidu de l'identité d'Abel sur des blocs de 50 cellules à chaque décade ; (b) formule exacte de l'amplitude à la
cassure contre le calcul direct, et encadrement ; (c) `|v_k R(C_k)| / C_k^{3/2}` par décade ; (d) H4 sur les cellules à
un seul poids. Jumeau déterministe mpmath 30 chiffres sur un sous-ensemble. Critère : A si toutes les identités sont
exactes à la précision flottante et (c) décroît ; B si une identité compile mais le nombre contredit ; C sinon.
Aucune conclusion sur les OFF n'est tirée, par ordre.
