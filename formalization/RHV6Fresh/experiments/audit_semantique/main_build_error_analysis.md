SIGNATURE=c779ba960ff0
EXPLICATION DE L'ERREUR (un seul théorème ouvert, but `False`)
  [0] 2026-10-27 (Fable) : même théorème, même but, ligne `:797` (ex-`:857`) après le retrait des blocs 22/28 de
    `DemonstrationChain` (cible optionnelle `RHV6FreshCertificates`) ; `hT3` inchangé, `hProfile` affiche `15 < T` au lieu de
    `28 < T`. Aucun fait ajouté ni retiré du contexte sinon ce chiffre. Analyse structurelle complète et plan :
    `experiments/PLAN_FABLE_CLOTURE_TERMINALE_20261027.md` (cellule du pivot insensible à β ; marge Δ ≥ 0 fausse pour
    4 534/5 000 rangs ; seule route séparante = exposant du reste `θ < 1 − β_n`, équivalent à une bande sans zéro, ouvert).
  [1] `:856` `authentic_engaged_cascade_forbids_insertion (p) : ¬ HorizontalMirrorRealization p`.
  Première rupture authentique : membre canonique `n` sous un demi, historique ON, atteint en montant ; le pas sortant est GELÉ
  (`hFrozen : δ₁ = δ₀`). Contexte : contacts, miroir, reconstruction exacte (`hImposedBreak`, `hImposedNext`, `hGapSync`) et,
  depuis ce jour, deux CONTRAINTES nouvelles : `hBand` (région sans zéro inconditionnelle : `A/log⁹T < β_n < 1/2 < 1 − β_n <
  1 − A/log⁹T`) et `hProfile` (profil démontré de la perturbation : `T_n > 28`, miroir distinct après `n`, fibre finie, pas sortant
  gelé, déficit de comptage `≥ 2`, toute sortie en montant depuis cette hauteur part d'un membre `β > 1/2`). Aucun de ces faits
  n'en contredit un autre : tous tiennent dans le monde témoin `ζ(s−δ)ζ(s+δ)`.
PROGRÈS (fait, certifié compilé)
  - Cinq modules nouveaux dans le build unique, 51 théorèmes, axiomes standard : bande sans zéro sur les vrais zéros
    (`ZeroFreeRegionBand`), paquet de stabilité ON et profil OFF (`OnRegimeStabilityPackage`), identité des séjours et canaux
    pondérés (`GrammarDwellDecomposition`), raccord G4 (`GrammarWeightedG4`), rigidité radiale finie Z1 (`FiniteRadialRigidity`).
  - Le canal des séjours pondéré est EXACTEMENT le canal du caractère modulo 3 moins une somme d'Abel bornée
    (`weighted_dwell_balance`, `weighted_character_channel`, `weighted_orientation_abs_le`) : la grammaire modulo 6 n'a aucun
    porteur propre de la position radiale ; E373 le confirme (asymétrie `cosh` identique dans les quatre familles à 1 %).
  - Campagne de fermeture E372 (`experiments/E372_ClosureAttempts_ZeroFreeBand/`, six sondes hors build, aucun `sorry`) :
    P1 bande + gel : `δ₀ = (arctan(T/β_s) − arctan(T/β_n))/T ∈ ]−π/(2T), 0[`, compatible avec le gel ; but `⊢ False`.
    P2 comptage : `N(T_l) ≥ N(T_e) + 2` acquis ; but `⊢ fiberCountWithMultiplicity T_l < 2` (fibre réduite à un point simple :
      plus fort que RH).
    P3 rigidité finie : la paire {rupture, miroir} normalisée n'est PAS bornée (Z1 appliqué) ; but `⊢ ∃ B, ∀ x ≥ 1, ‖terme lissé
      de la rupture + terme lissé du miroir‖ ≤ B√x`, réfuté par le même lemme dans le même contexte : équivalent à `False`.
    P4 G4 + blocs : G4 instancié sur les premiers donne `N log N` sur la seule orientation ; `primePart` reste à l'exposant 2 ;
      but `⊢ ∃ θ < 1 − β_n, C, ∀ N ≥ 2, |primePart N − N²/2| ≤ C N^{1+θ}` (bande sans zéro).
    P5 synchronisation + bande : but `⊢ ∃ θ < 1 − β_n, C, ∀ x > 1, ‖smoothedRemainder x‖ ≤ C x^θ` (exposant 1 seul acquis).
    P6 mots de régime : aucun théorème n'interdit un départ vertical depuis `β > 1/2` (`junction_horizontal_vertical` l'impose) ;
      l'instance V·H est `riemannHypothesis_iff_no_regimeEntry` ; but `⊢ False`.
RESTE À FAIRE
  L'énoncé le plus faible qui fermerait P3, P4 et P5 à la fois : `∃ θ < 1 − β_n, ∃ C, ∀ x > 1, ‖smoothedRemainder x‖ ≤ C·x^θ`
  (borne du reste des premiers d'exposant strictement sous la position radiale du miroir de la rupture). Acquis : exposant 1
  (`smoothedRemainder_linear_growth`) ; la région sans zéro compilée n'abaisse pas l'exposant (`1 − ε(x)`, pas de gain en
  puissance). C'est l'asymétrie de croissance `x^{1/2±δ}` nommée par l'auteur, lue sur le reste ; aucune donnée grammaticale ne la
  contient. Prochaine étape dirigée : instancier G4 sur `transitionSum` (réindexation par `fnPrimeAtRank`), formaliser T2 et Z3
  (vague 3 du plan), sans attendre d'eux un gain d'exposant.
PRÉMISSES ET SUPPOSITIONS PAR RAPPORT AU TERME FINAL
  - Aucune hypothèse nommée ; un seul théorème ouvert, dont dépendent `radius_premise` et `riemannHypothesis_terminal` ;
    `sorryAx` provient de ce seul but.
  - Les cinq modules nouveaux et les sondes n'utilisent aucun théorème conditionnel de la chaîne.
RÉFUTÉ (maîtres et démarche, jamais le code)
  - « Les deux stabilités grammaticales (orientation, séjours) pourraient porter une contrainte indépendante sur la position
    radiale » : l'identité pondérée les réduit à un canal de caractère et à une somme d'Abel ; E373 mesure une asymétrie OFF
    répartie au prorata des masses. La phrase « chercher le porteur OFF dans les croisements, les séjours ou leurs motifs » est
    retirée de la démarche.
  - Le chiffre de référence de la mission (« 88 055 transitions, N15 − N51 = +1 ») n'est pas un préfixe de premiers > 3.
