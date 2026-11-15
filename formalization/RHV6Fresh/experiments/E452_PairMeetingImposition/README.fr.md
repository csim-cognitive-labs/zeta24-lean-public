> Version française conservée à titre de référence. Main language: English, see README.md.

# E452 — K2b : ce que la rencontre exacte impose aux deux termes de même poids au même premier — pré-enregistrement

Date : 2026-11-08. Statut : pré-enregistré avant toute compilation et toute exécution (§19.74). Direction validée par l'auteur.
Ordres : ban spectral total (usage et citation ; deux termes seulement, aucune somme de Tours, aucun canal, aucune formule
explicite) ; troisième ordre (contacts lisent `β` ; fréquence ET amplitude ; bilan signé par `contactRealValue`) ; R-E446 ;
§19.44 ; interdit « amplitude contre budget » ; aucune prémisse équivalente à RH ; deux tentatives de compilation au plus,
chacune journalisée dans `attempts/`.

## Vérification de non-équivalence avec RH (faite avant pré-enregistrement, §19.74.2)
K2b ne pose aucune hypothèse : tous ses énoncés sont des théorèmes pour toute `β ∈ (0,1)` ; la condition `β > 1/2` des
énoncés de non-compensation est un cas sur une paire donnée (le miroir couvre `β < 1/2`). Rien n'est à confronter à RH.
Aucune comparaison avec `log q`, `ψ`, `rawDemand`, une longueur de cellule. Conséquence consignée d'avance : K2b fixe la FORME
de la paire au premier partagé ; il ne fournit pas la contradiction ; K3 (inversion de la paire) suit.

## Objet
Paire `(β, T)`, `(1−β, T)` ; au point `x > 0` : mots `k = lastContactBefore β T x`, `k* = lastContactBefore (1−β) T x`,
fractions `f`, `f*`, valeurs `v = contactRealValue β T k`, `v* = contactRealValue (1−β) T k*`, décalage de phase
`δ = mirrorPhaseShift β T` (nul ⟺ `β = 1/2`, E428) ; pour un zéro vrai, poids commun `m = zeroMult ρ ≥ 1` (E451).

## Hypothèses
* H1 (mot exact) : `k* = k + s`, `s := ⌊f + δ/π⌋` (`mirrorWordShift`).
* H2 : `|s| ≤ 1` ; `s ∈ {−1, 0, 1}`.
* H3 (fenêtre) : `k* = k ⟺ −δ/π ≤ f < 1 − δ/π` ; sur la ligne `s = 0` partout.
* H4 (signes) : `v·v* = (−1)^s |v||v*|` ; même signe ⟺ `s = 0`.
* H5 (valeur de la paire) : `|v + v*| = | |v| + (−1)^s |v*| |` ; `= |v| + |v*|` si `s = 0`, `= ||v| − |v*||` sinon ;
  `|v| − |v*| ≤ |v + v*|` toujours.
* H6 (non-compensation) : si `β > 1/2`, `∀ᶠ x, |v|/2 < |v + v*|` ; à toute rencontre au-delà d'un rang.
* H7 (ligne) : `v + v* = 2v` à `β = 1/2`.
* H8 (zéro vrai, poids) : `|m v + m* v*| = m |v + v*| ≥ |v + v*|` ; non-compensation au paramètre d'un zéro vrai hors ligne.

## Énoncés Lean (module isolé `Terminal/PairMeetingImposition.lean`, import `PairBreakOfZero` seul)
L1 `mirrorWordShift`, `mirror_stagePosition_eq`, `mirror_lastContactBefore`, `abs_mirrorWordShift_le_one`,
`mirrorWordShift_trichotomy` ; L2 `pair_same_word_iff`, `line_mirrorWordShift_eq_zero` ; L3 `pair_value_tower_eq`,
`pair_value_mirror_eq`, `abs_sign_sum`, `pair_value_product`, `pair_same_sign_iff` ; L4 `pair_value_sum_abs`,
`pair_value_sum_of_same_word`, `pair_value_sum_of_shifted_word`, `pair_value_sum_ge` ; L5 `pair_value_no_cancellation`,
`pair_meeting_no_cancellation` ; L6 `line_pair_value_sum` ; L7 `zero_pair_value_no_cancellation`,
`zero_weighted_pair_value_abs`, `zero_weighted_pair_value_ge`.

## Expériences
* (a) `scripts/e452a_pair_imposition.py` (numpy) : 18 couples OFF témoins `β ∈ {0,3 ; 0,4 ; 0,45}` × six fréquences de K0
  (zéros de rangs 1, 10, 100, 1000, 10000, 100000) + six couples ligne ; 10⁵ premiers ≤ 10⁷ (graine 452) ; H1–H7 à `10⁻¹²` ;
  premier rang de non-compensation ; observation sans loi : part des premiers à mots décalés contre `|δ|/π`.
* (b) `scripts/e452b_twin_mpmath.py` : jumeau mpmath 30 chiffres, 10 premiers par couple, écart aux valeurs numpy.

## Critère
A : module vert (≤ 2 tentatives), axiomes standards, grep du ban vide, toutes identités à `10⁻¹²`, jumeau concordant ;
B : une identité manque (consignée) ; aucune hypothèse, aucune contradiction tirée.
