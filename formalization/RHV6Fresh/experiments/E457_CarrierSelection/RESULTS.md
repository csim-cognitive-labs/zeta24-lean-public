# E457 — Résultats (2026-11-08 ; pré-enregistrement 8bf3b5db)

## Lean Φ0 + Φ1 — `RHV6Fresh/Terminal/CarrierSelection.lean` (isolé, 313 lignes, 22 déclarations)
Sondes scratch : probe1 (deux noms Mathlib erronés dans Φ1 : `Metric.eventually_nhdsWithin_iff` n'existe pas, remplacé par
`eventually_nhdsWithin_iff` + `Metric.eventually_nhds_iff` ; tous les énoncés Φ0 déjà verts), probe2 (tout vert sauf la sonde
`NoMixedHeight ⟹ RH` : `exact?` épuise le budget d'heartbeats sans preuve — constat consigné, pas une non-implication démontrée).
Tentative 1 du module définitif VERTE (`attempts/build_attempt1.txt`, 9 097 tâches) ; 0 avertissement dans le module ; 9/9 énoncés
imprimés sur `[propext, Classical.choice, Quot.sound]` (`attempts/axioms_attempt1.txt`) ; grep du ban 0 ; `lake build RHV6Fresh` complet
vert (`logs/lake_build_full.txt`, 9 064 tâches).

Compilé :
* R1 `carrierWordsSelfMirror_iff_riemannHypothesis` ; R2 `heightInjectiveOnCarriers_iff_riemannHypothesis` ; R2 ⟹ `NoMixedHeight`
  (`noMixedHeight_of_heightInjective`) ; R3 `priceRadiallyBlindOnCarriers_iff_riemannHypothesis` (prix d'E445 `offPrice`, normalisation
  `pair_amplitude_eq_price`, prix de la ligne `offPrice_line = 1`) ; R3' `termModulusMirrorBlind_iff_riemannHypothesis` et
  `radial_half_of_term_modulus_eq_two_primes` (deux premiers distincts suffisent, à cause du facteur de normalisation constant
  `‖ρ*‖/‖ρ‖` du rapport `x^{2β−1}`).
* Φ1 : `continuousAt_stagePosition_radial`, `floor_stable_right_of_continuous_mono`, `towerWord_stable_right`,
  `towerWord_stable_right_finset`, `exists_nonCarrier_same_word_on_finset` (même hauteur, `β < β' < min(β+ε, 1)`, zêta non nulle,
  poids nul, même mot sur tout ensemble fini de rangs), `finite_window_predicate_not_carrier_selective`.
* Convention de bord : la partie entière est continue à droite, donc un premier exactement sur un contact reste dans sa cellule quand
  la position d'étage croît ; la direction « β croissant à T fixé » préserve toutes les lectures du préfixe, bord compris. C'est la
  réponse compilée à l'objection « un premier exactement sur un contact ».

## Volet déterministe — `e457_carrier_isolation.py` (`logs/e457_output.txt`, `logs/e457_run.txt`)
200 hauteurs (14,13 → 396,38), premiers ≤ 10⁶ (78 498), ligne + trois contrôles β ∈ {0,30 ; 0,40 ; 0,45} = 800 Tours.
* Marge radiale conservant tout le mot : ligne min 2,4·10⁻⁶, médiane 4,7·10⁻³, max 6,8·10⁻² ; contrôles médianes 4,6–4,9·10⁻³.
* Marge en hauteur : ligne min 2,5·10⁻⁹, médiane 1,9·10⁻⁶, max 1,6·10⁻⁵ ; contrôles médianes 1,9–2,1·10⁻⁶ ; rapport au demi-écart vers
  la hauteur suivante ≤ 2,9·10⁻⁵ (médiane 2·10⁻⁶) : la Tour voisine de même mot est des milliers de fois plus proche que le zéro suivant.
* Premier limitant : fraction de cellule médiane 0,99999 (le mot casse d'abord là où un premier est le plus près du contact suivant) ;
  approximation π(1−f)/log q exacte à 2·10⁻⁴ près.
* Vérification directe aux deux bords (mot conservé juste en deçà de la marge, changé juste au-delà) : 791/800 en double précision ; les
  9 écarts ont tous `1−f ≤ 1,6·10⁻⁷`, donc une marge de test absolue (1−f)·10⁻⁶ ≤ 1,6·10⁻¹³ sous le bruit double (|s|·2,2·10⁻¹⁶ ≈ 3·10⁻¹³) ;
  recontrôle en précision étendue (40 chiffres, `e457_boundary_recheck_mp.py`, `logs/e457_boundary_recheck_mp.txt`) : 9/9 conformes.
  Bilan : 800/800. (`e457_boundary_diagnostic.py` : premier diagnostic, critère de bruit mal posé, conservé tel quel.)
* Ligne / contrôles : médianes des marges dans un rapport 0,98–1,11 ; corrélation des rangs des marges en hauteur entre la ligne et un
  contrôle −0,02 à −0,09 : la marge est une propriété du mot (du couple (β, T) et des premiers), pas du poids.

## Verdict
A : Φ0 et Φ1 compilés en une tentative, attendus du jumeau tous réalisés (deux prévisions exactes : marge en hauteur ≪ demi-écart,
contrôles du même ordre que la ligne), aucune contradiction tirée, aucune hypothèse posée. Conséquences : K0 (E450) et A4 (E429) sont
des théorèmes ; la route des fenêtres finies (grammaire modulo 6 incluse) est fermée par théorème ; la sélection des porteurs ne peut pas être
caractérisée par un prédicat portant exclusivement sur une fenêtre finie du mot (rectification du 2026-11-09, maître §19.85 : la
formule antérieure « propriété de queue du mot » disait plus que le théorème ; une propriété peut exiger le mot infini entier tout en
dépendant de ses premiers termes ; et le théorème n'exclut que les critères fondés sur ces seules valeurs du mot, pas une condition
arithmétique locale enrichie d'une information indépendante). Écart au plan : perturbation en β à T fixé (plus forte : même fréquence) au lieu de T' > T.
