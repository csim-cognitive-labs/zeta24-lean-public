> Version française conservée à titre de référence. Main language: English, see README.md.

# E451 — La Tour est le terme du zéro : pont « zéro vrai → objets d'E450 » par le calcul de zêta (K2a du plan §19.72) — pré-enregistrement

Date : 2026-11-08. Statut : pré-enregistré avant toute compilation et toute exécution. Ordres : ban spectral total (usage et
citation ; aucune somme de Tours, aucun canal, aucune formule explicite consommée) ; troisième ordre ; R-E446 ; §19.44 ; aucune
prémisse équivalente à RH ; deux tentatives de compilation au plus, chacune journalisée dans `attempts/`.

## Ordre de l'auteur vérifié (§19.73)
« Si on calcule le zéro par zêta, on obtient une Tour ; dans le cas contraire la Tour n'existe pas. » Compilé dans le corpus :
`zeroContribution_eq_mul_zeroTerm` (poids `m(ρ)` = ordre d'annulation de zêta en `ρ`), `one_le_zeroMult` (`m ≥ 1` en un zéro),
`zeroTerm_real_iff_ray` + `contactAt_eq_contactMinusAt` (la grille `(β, T)` est la suite des points réels du terme),
`zeroTerm_norm` (module `x^β/‖ρ‖`), `upperMirror_multiplicity` (le miroir a le même poids). Manque au corpus le corollaire
explicite « `m(ρ) = 0 ⟺ ζ(ρ) ≠ 0` hors pôle » : E451 l'écrit.

## Objet
Un zéro vrai `z` (`TrueZero`), de point `ρ = zeroPoint z = (β, T)`, son miroir `mirrorMember z` de point `(1−β, T)`, le poids
`zeroMult ρ = (analyticOrderAt riemannZeta ρ).toNat` (`Foundation/ZetaReflect`), le terme `zeroTerm z x = x^ρ/ρ`, les objets
d'E450 au paramètre `(β, T)` : `contactRealValue`, `lastContactBefore`, `cellFraction`.

## Hypothèses
* H1 (poids) : `zeroMult ρ = 0 ⟺ riemannZeta ρ ≠ 0` pour `ρ ≠ 1` ; `1 ≤ zeroMult (zeroPoint z)` ; le terme pondéré de la
  base est `zeroMult · zeroTerm`.
* H2 (miroir) : `zeroMult (zeroPoint (mirrorMember z)) = zeroMult (zeroPoint z)` ; `mirrorMember z ≠ z` dès que `β ≠ 1/2`.
* H3 (cassure d'E450 au zéro) : `|contactRealValue β T (lastContactBefore β T x)| = ‖zeroTerm z x‖ · e^{−βπ f/T}`.
* H4 (deux mots) : `|lastContactBefore (1−β) T x − lastContactBefore β T x| ≤ 1` pour le zéro et son miroir.
* H5 (produit exact) : `‖zeroTerm z x‖ · ‖zeroTerm (mirrorMember z) x‖ = x/(‖ρ‖ ‖ρ*‖)` ; pondéré : `m² x/(‖ρ‖ ‖ρ*‖)`.
* H6 (séparation) : `‖zeroTerm z x‖/‖zeroTerm (mirrorMember z) x‖ = x^{2β−1} ‖ρ*‖/‖ρ‖` ; non bornée si `β > 1/2`.

## Énoncés Lean (module isolé `Terminal/PairBreakOfZero.lean`, import `PairBreakAtPrime` seul)
* L1 `zeroMult_eq_zero_iff (hρ : ρ ≠ 1)`, `one_le_zeroMult_zeroPoint (z)`, `zeroContribution_eq_zeroMult_mul (z) (x)`.
* L2 `zeroMult_mirrorMember (z)`, `mirrorMember_ne_self_of_off (hβ : β ≠ 1/2)`.
* L3 `zero_break_amplitude_exact (z) (hx)`.
* L4 `zero_mirror_word_difference_le_one (z) (x)`.
* L5 `zero_pair_term_product (z) (hx)`, `zero_pair_weighted_product (z) (hx)`.
* L6 `zero_pair_term_ratio (z) (hx)`, `zero_pair_term_ratio_unbounded (z) (hβ : 1/2 < β) (K)`.

## Expériences
* (a) `scripts/e451a_zeta_weight.py` (mpmath, 30 chiffres) : `|ζ(1/2 + iγ)|` aux six zéros de K0 (rangs 1, 10, 100, 1000,
  10000, 100000, hauteurs du fichier Odlyzko) et aux trois contrôles de K0 (milieux des rangs 1–2, 100–101, 10000–10001).
  Critère : `< 10^{−20}` aux zéros (à la précision des hauteurs lues, `~10^{−9}` : on consigne la valeur telle quelle et on la
  compare à `|ζ'|·δγ`), `> 10^{−3}` aux contrôles. C'est le « calcul de zêta » qui décide de l'existence de la Tour.
* (b) `scripts/e451b_zero_terms.py` (numpy, 100 000 premiers, graine 451) : H3, H5, H6 pour les six zéros (`β = 1/2`,
  miroir = zéro) et pour trois paires OFF témoins `β ∈ {0,3 ; 0,4 ; 0,45}` aux mêmes fréquences ; erreurs relatives
  `≤ 10^{−12}` ; H4 : 0 violation.
Verdict attendu : A.
