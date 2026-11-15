#!/usr/bin/env python3
"""Classement G/E/S/R/X des théorèmes sélectionnés (selected.json), heuristique sur le type
puis décisions manuelles (listes MANUAL ci-dessous, issues de la lecture des énoncés).
Sortie : audit_thms.csv (base, name, file, line, classe, sous_classe, anticipe, note, source, type).

G invariant de grille ; E évaluation en une étiquette ; S Tour qui sélectionne un premier / cellule
à un premier / Tour à deux contacts ; R caractérisation de régime ; X ⟺ RH ou sous prémisse."""
import json, re, csv, os
from collections import Counter

OUT = os.path.dirname(os.path.abspath(__file__))
sel = json.load(open(f"{OUT}/selected.json"))

# Prédicats descriptifs (pas des prémisses non déchargées)
DESCR = {"PZeroMembersConsecutive", "PIsOffCriticalLine", "PZeroMemberPrecedes", "PIsNonTrivialZetaZero",
         "PZeroPassageRelationNull", "PPrimeTransitionAtRank", "PPrimeFromPsi", "PGrammaticalProgression",
         "PIsOnCriticalLine"}
# Prémisses de type T1 / sélection d'un premier par la Tour
S_PREM = {"PUniqueCenterRegime", "PCanonicalT1", "PCanonicalTerminalPrimeCountOne",
          "PEveryTerminalCellHasUniqueCanonicalPrime", "PT1", "PUniquePrimeLocalizationAt",
          "PCanonicalCellFoundCountOne", "PCanonicalCentralityT1", "PCanonicalPrimeCountEqOne",
          "PCentralPrimeInjective", "PMirrorCollision", "PMemberAnchorLandsInOwnCell"}

RX_LABEL = re.compile(r"occurrence|expectedMinimumPrime|nMemberCanonicalAnchor|\.M\b|M₁|M₂|M₃|towerRaccordOf|"
                      r"TowerRaccord|GrammaticalRaccord|grammaticalRaccordOf|CanonicalTransition|pivotCell\b|"
                      r"firstTowerOf|secondTowerOf|lineTowerOf|memberMZOccurrence|MZOccurrence|CentralPrime|"
                      r"centralPrime|canonicalState|nCarrierCentralPrime|tCarrierCell|tOperatorCell|"
                      r"canonicalTrueTowerState|memberStep|primalEventAt|ZeroChain")
RX_TOWEROBJ = re.compile(r"contact|Contact|tower|Tower|zeroTerm|Position|pivot|radial|Radial|phase|Phase|"
                         r"energy|Energy|reaches|Cell|cell|ledger|raccordShift|transitionExcess|Incidence")
RX_REGIME = re.compile(r"regime|Regime|vertical|Vertical|horizontal|Horizontal|ranslation|contract|itch|"
                       r"onLine|OnLine|diagonal|Diagonal|radialFactor|changeResidue|sameHeight|SameHeight|rigid|"
                       r"heightOnly|engaged|Engaged|offLine|OffLine|Oriented|oriented|mirror_contacts|"
                       r"PIsOffCriticalLine|rZeroRadialPosition [^ ]+ = 1 / 2|≠ 1 / 2|< 1 / 2|1 / 2 <")

ANTICIPE = {
    # rhv3
    "RHV3Lean.thm_foundPrimes_generallyPlural": "une cellule algébrique contient en général ≥ 2 premiers",
    "RHV3Lean.Certification.cmp_C2_foundPrimes_generallyPlural": "idem (certification)",
    "RHV3Lean.thm_ratioFourInterval_containsTwoPrimes": "toute fenêtre de rapport 4 contient deux premiers",
    "RHV3Lean.Certification.cmp_C6_ratioFourInterval_containsTwoPrimes": "idem (certification)",
    "RHV3Lean.thm_PCanonicalCellFoundCountOne_is_false": "« la cellule canonique contient exactement un premier » est faux (T ≥ 2π/log 1,5)",
    "RHV3Lean.thm_count_not_determined_by_T_beta_alone": "le compte de premiers d'une cellule n'est pas fonction de (β,T) seul : cellule terminale vide, fenêtre voisine ≥ 1",
    "RHV3Lean.thm_count_not_determined_by_T_beta_alone_v2": "idem v2",
    "RHV3Lean.thm_canonicalCell_foundCount_eq_zero_of_height_large": "la cellule canonique est vide à grande hauteur : la Tour ne pointe pas un premier",
    "RHV3Lean.thm_T1_alone_does_not_force_T2_countDiff": "T1 (un premier par cellule) ne force pas la succession de rang",
    "RHV3Lean.thm_T1_alone_does_not_force_T2_rankEquality": "idem",
    "RHV3Lean.thm_foundPrimes_eq_image_rankInterval": "les premiers d'une cellule = un intervalle de rangs (pluriel en général)",
    "RHV3Lean.thm_cellFoundCount_eq_edgeRankDifference": "compte d'une cellule = différence de rangs aux bords (0, 1 ou plus)",
    # rhv2
    "RHV2Fresh.thm_originNormalization_refuted_by_T1": "T1 tue la fenêtre ancrée à l'origine",
    "RHV2Fresh.thm_originNormalization_refuted_by_T1_heightThreshold": "idem, seuil explicite",
    "RHV2Fresh.thm_arbitraryOperator_violates_canonicalT1": "un opérateur de Tour arbitraire viole T1",
    "RHV2Fresh.thm_inhabitation_is_not_M4": "le type opérateur est habité sans T1",
    "RHV2Fresh.thm_cellBelowTwo_contradicts_T1": "cellule sous 2 : T1 impossible",
    "RHV2Fresh.subPrimeAuditReadout_not_uniquePrimeLocalization": "lecture sous-première : pas de localisation unique",
    "RHV2Fresh.TCanonicalTowerState.thm_canonicalTowerState_carrier_not_subsingleton": "un zéro porte plusieurs états de Tour",
    # RHV5
    "RHV5Fresh.Diagnostics.thm_contactLawState_not_subsingleton": "les lois de contact ne déterminent pas un état unique",
    "RHV5Fresh.Diagnostics.thm_contactLaws_do_not_determine_state": "idem",
    "RHV5Fresh.Diagnostics.thresholdCell_empty_of_height": "cellule seuil vide à grande hauteur",
    # RHV6
    "RHV6Fresh.tower_reads_any_prime": "D1 (RayEnergy) : une Tour à toute hauteur lit tout premier dans une cellule unique",
    "RHV6Fresh.prime_raccord_has_unique_tower_cell": "tout q > 0 a sa cellule (énoncé ∀ q, porteur de every_prime_in_every_tower)",
    "RHV6Fresh.every_prime_in_every_tower": "le fait nouveau lui-même",
    "RHV6Fresh.occurrence_is_rank_label": "le fait nouveau lui-même",
    "RHV6Fresh.tower_offset_rigid": "le fait nouveau lui-même",
    "RHV6Fresh.onLine_iff_entry_at_point": "le fait nouveau lui-même",
    "RHV6Fresh.onLine_iff_no_grid_translation": "le fait nouveau lui-même",
    "RHV6Fresh.entry_arrow_point_irrelevant": "le fait nouveau lui-même",
    "RHV6Fresh.towerPosition_eq_line_add_residue": "décalage D/π indépendant de q : forme compilée du fait",
    "RHV6Fresh.contact_eq_line_mul_radial": "tous les contacts = contacts de ligne × un facteur radial unique",
    "RHV6Fresh.sameHeight_grid_rigid_translation": "translation rigide de toute la grille à même hauteur",
    "RHV6Fresh.tower_grid_normal_form": "forme normale de la grille (TowerGrid)",
    "RHV6Fresh.competing_regime_at_any_point": "le régime se lit en tout point de la grille",
    "RHV6Fresh.pointed_primes_rank_only": "Occ et p_min fonctions du rang seul",
    "RHV6Fresh.expectedMinimumPrime_injective": "l'étiquette est injective : un comptage",
    "RHV6Fresh.analyticPairAt_entryContact": "les paires à toute coordonnée k sont des cellules (ProperTower §6 les disait « jamais des contacts »)",
    "RHV6Fresh.analyticPairAt_lastRayContact": "idem",
    "RHV6Fresh.reaches_analyticPairAt_iff": "idem",
    "RHV6Fresh.countedPrime_analyticPairAt": "idem",
    "RHV6Fresh.grammar_event_reads_no_radial": "la grammaire ne lit aucun radial",
    "RHV6Fresh.grammar_step_regime_blind": "pas grammatical aveugle au régime",
    "RHV6Fresh.zeroTerm_real_iff_ray": "le terme q^ρ/ρ est réel exactement aux C_k, pour TOUT k : tous les C_k sont des contacts",
    "RHV6Fresh.towerMotion_incidence": "le mouvement porte une incidence pour tout k ∈ ℤ",
    "RHV6Fresh.towerMotion_incidence_strictOrder": "incidences strictement ordonnées sur ℤ : grille infinie",
}

# Décisions manuelles RHV6Fresh (lecture des 289 énoncés en Occ/M/pivot/p_min et des cas douteux)
MANUAL = {}
def m(cls, sub, note, *names):
    for n in names:
        MANUAL["RHV6Fresh." + n] = (cls, sub, note)

m("S", "S-structure", "TrueTower z = mouvement (grille) + UNE paire de contacts distinguée ; module TrueTowerStructure : « deux contacts, et deux seulement, l'agrégat de cellules n'existe pas » ; type vrai, lecture à requalifier : la paire est une cellule de la grille, la Tour est la grille",
  "TrueTower.ext_pair", "TrueTower.readings_injective")
m("S", "S-définition", "état propre de la Tour défini comme la cellule de p_min(z) : la sélection du premier est faite par l'étiquette de rang dans la définition, pas par la géométrie ; type vrai (rfl)",
  "firstTowerOf_properState", "lineTowerOf_properState", "secondTowerOf_properState", "firstTowerOf_eq_lineTowerOf")
m("S", "S-nom", "nom et docstring « la géométrie sélectionne le raccord » ; le type dit : occurrence l = p_min e (grammaire) ∧ la cellule pivot de q existe et est unique pour tout q ; la géométrie localise n'importe quel q, c'est le rang qui sélectionne",
  "geometry_selects_raccord_prime")
m("S", "S-nom", "« la paire de contacts de la première Tour est unique » : type = unicité de la coordonnée k dont la cellule contient p_min(z), vraie pour tout q (pivotCoordinate_unique) ; la Tour n'est pas cette paire",
  "firstTower_contactPair_unique")

# G : énoncés ∀ q / ∀ k / paire générique (vrais en tout point de la grille)
m("G", "G-grille", "énoncé pour tout q ou toute coordonnée k : propriété de la grille",
  "invertedPivotPair_entryContact", "invertedPivotPair_lastRayContact", "invertedPivotPair_upright",
  "invertedPivotPair_cell_contains", "invertedPivotPair_lastRay_lt_pivot", "invertedPivotPair_not_reaches",
  "invertedPivotPair_not_reaches_of_le", "invertedPivotPair_entryCoordinate", "invertedPivotPair_stageCount",
  "pivotPair_entryContact", "pivotPair_lastRayContact", "pivotCoordinate_unique", "pivotPair_entryReading",
  "pivotPair_entryCoordinate", "pivotPair_stageReading", "pivotPair_stageCount", "entry_lt_pivot",
  "pivot_le_lastRay", "pivotPair_reaches", "pivotPair_reaches_of_le", "pivotCoordinate_eq_of_same_cell",
  "pivotCoordinate_le_of_le_contactPlus", "pivot_le_contactPlus_pivotCoordinate", "pivotCoordinate_isLeast",
  "canonicalOrigin_lt_iff_zero_le_pivotCoordinate", "pivot_countedRank_pos", "pivot_le_counted",
  "pivotCoordinate_sameHeight_shift_le_one", "prime_raccord_has_unique_tower_cell", "pivotCell_entry_zeroTerm_real",
  "pivotCell_lastRay_zeroTerm_real", "pivotCell_amplitude_brackets", "sameCell_four_contacts_bracket",
  "pivotCoordinate_mono", "sameRing_imp_gap_lt_pi", "coordinate_lt_of_gap_ge_pi", "every_prime_in_every_tower",
  "tower_reads_any_prime", "entry_cell_eq_line_cell_of_margin", "phase_increment_pos",
  "phase_increment_le_height_mul_log_two", "phase_increment_ge_height_mul_log_one_add_inv",
  "phase_increment_ge_height_mul_log_one_add_two_div", "height_lower_bound_of_phase_quantum",
  "phase_increment_eq_pi_span", "local_euler_term_norm", "local_euler_factor_ne_zero",
  "local_euler_factor_at_member_ne_zero", "rpow_exponent_injective", "energyRatio_unbounded_of_deltaBeta_pos",
  "two_raccord_transport", "fibre_transport_product_off", "history_inner_eq_line_mul_charge",
  "historyCharge_succ", "historyCharge_const_one_iff", "history_transport_product")
m("G", "G-comptage", "comptage de Tchebychev au dernier rayon d'une paire QUELCONQUE de la grille : vrai en toute cellule",
  "countedPrimeAt_eq_vonMangoldt", "countedPrimeAt_eq_primeAtRank", "contactPlusAt_lt_primeAtRank_counted",
  "countedPrimeAt_of_contactPlus_eq", "countedPrimeAt_mono_oriented", "countedPrime_eq_vonMangoldt",
  "countedPrime_eq_countedPrimeAt_lastRay", "countedPrime_of_one_stage", "countedPrime_analyticPairAt",
  "countedPrime_le_lastRay", "countedPrime_prime", "InvertedContactPair.countedPrime_prime",
  "reaches_iff_le_countedPrime", "InvertedContactPair.reaches_iff_le_countedPrime",
  "InvertedContactPair.countedPrime_lt_of_not_reaches_succ", "reaches_primeAtRank_iff",
  "InvertedContactPair.reaches_primeAtRank_iff", "lastPrimeAtStateUpper_prime", "lastPrimeAtStateUpper_le_contact",
  "producedPrime_eq_vonMangoldt", "vonMangoldt_channel_reflectionFixed", "remainder_increment_at_prime",
  "reconstructed_weight_at_prime", "expectedMinimumPrime_gapClass6_alternates")

# E-grammaire : étiquettes de rang sans objet de Tour
m("E", "E-grammaire", "étiquette de rang pure (aucun objet de Tour) : contenu radial nul",
  "occurrence_eq_canonicalAnchor", "occurrence_strict_of_passage", "occurrence_successor_of_passage",
  "occurrence_prime", "occurrence_pos", "expectedMinimumPrime_prime", "occurrence_lt_expectedMinimumPrime",
  "expectedMinimumPrime_eq_laterOccurrence", "expectedMinimumPrime_injective", "expectedMinimumPrime_succ_of_passage",
  "expectedMinimumPrime_pos", "three_le_expectedMinimumPrime", "expectedMinimum_eq_succ_occurrence",
  "occurrence_eq_primeAtRank", "occurrence_is_rank_label", "ZeroChain.occurrence_eq", "pointed_primes_rank_only",
  "pointed_gapClass6_rank_only", "passage_event_increment", "rank_grammar_unconditional",
  "grammar_hypotheses_of_passage", "passage_direction_rigid", "passage_raccords", "grammar_event_reads_no_radial",
  "grammar_step_regime_blind", "event_prime", "event_predecessor", "event_successor", "rank_pos",
  "event_inGap_pos", "event_outGap_pos", "M_add_outGap", "event_reconstructed", "history_step",
  "occurrence_add_inGap", "occurrence_div_expectedMinimum_mem", "grammaticalRaccord_eq",
  "grammaticalRaccord_M_injective", "primes", "arithmetic_depends_on_rank_only", "mirror_sameHeightPrime",
  "mirror_no_new_height_event", "mirror_occurrence_strict", "mirror_expectedMinimum_ne",
  "expectedMinimum_lt_mirror_expectedMinimum", "expectedMinimum_le_mirror_occurrence", "raccords")

# R : relectures de régime parmi les énoncés en étiquette
m("R", "R-raccord", "orientation du raccord ⟺ la hauteur avance ; relecture : le transport M^{β_l−β_e}·‖ρ_e‖/‖ρ_l‖ a le même signe de log en tout q > 1 (M est un point de la grille) ; reste valide",
  "towerRaccord_oriented_iff_height_lt", "towerRaccord_oriented_of_height_lt", "towerRaccord_oriented_of_vertical",
  "towerRaccord_reverses_of_sameHeight", "TowerRaccord.oriented_iff_transport_le_one",
  "towerRaccord_oriented_iff_window_separates", "sameHeight_amplitude_inverts_at_raccords")
m("R", "R-translation", "décalage d'au plus une cellule à même hauteur / au miroir, pour tout q : lecture cellule par cellule de la translation rigide de la grille ; reste valide",
  "horizontal_pivot_shift", "sameHeight_pivotCoordinate_dichotomy", "pivotCoordinate_mirror_mem",
  "horizontal_cell_dichotomy_at_raccords", "central_cell_shift", "phase_increment_eq_of_sameHeight")
m("R", "R-flèche", "conservation ⟺ M entre à sa position de ligne ⟺ (fait nouveau) un point quelconque y entre ⟺ la Tour d'arrivée n'est pas translatée ; reste valide, M n'a pas de rôle propre",
  "transition_conserves_iff_entry_position", "transition_conserves_iff_shared_prime_shift",
  "arrival_onLine_iff_ledger_height_determined", "entry_arrow_iff_upper_conservation", "vertical_regime")
m("R", "R-cinématique", "excès de transition par configuration : seule la part radiale T_e log r_e − T_l log r_l distingue, indépendante de M ; reste valide",
  "transitionExcess_onLine", "transitionExcess_diagonal_lt", "transitionExcess_horizontal",
  "transition_kinematics_by_configuration", "first_off_configuration_alternation_floor",
  "horizontal_ledger_exceeds_grammar", "onLine_pair_ledger", "off_pair_vs_onLine_pair",
  "chain_from_line_radial_content", "chain_transitionExcess_sum", "chain_raccordShift_eq",
  "first_off_configuration_two_transitions")


def heuristic(r):
    t = r["type"] or ""
    n = r["name"]
    blob = n + " " + t
    prem = set(re.findall(r"\bP[A-Z][A-Za-z0-9]+\b", t))
    neg_s = any(re.search(r"¬\s*(?:[A-Za-z0-9_.]*\.)?" + p, t) for p in S_PREM)
    sp = prem & S_PREM
    if sp and not neg_s:
        return "S", "S-prémisse", "prémisse/objet de type T1 : " + ",".join(sorted(sp))
    if re.search(r"RiemannHypothesis|riemannHypothesis|RhGap\.RH\b", blob):
        return "X", "X-RH", "⟺ RH / ⟹ RH / sous RH"
    real = {p for p in prem - DESCR - S_PREM if not p.startswith(("Prime", "Pi"))}
    if real:
        return "X", "X-prémisse", "sous prémisse " + ",".join(sorted(real)[:3])
    label = RX_LABEL.search(t)
    reg = RX_REGIME.search(blob)
    if label and reg and ("↔" in t or "False" in t or "¬" in t):
        return "R", "R-heur", "caractérisation de régime énoncée en une étiquette"
    if label:
        if RX_TOWEROBJ.search(t):
            return "E", "E-Tour", "objet de Tour évalué en une étiquette (Occ/p_min/M/cellule choisie)"
        return "E", "E-grammaire", "étiquette de rang, sans objet de Tour"
    if reg:
        return "R", "R-heur", "énoncé de régime / position radiale"
    return "G", "G-heur", "invariant de grille ou sans premier particulier"


rows = []
for r in sel:
    if r["base"] == "RHV6Fresh" and not r["name"].startswith("RHV6Fresh."):
        r["name"] = "RHV6Fresh." + r["name"]
    if r["name"] in MANUAL:
        c, sub, note = MANUAL[r["name"]]
        note = "manuel: " + note
    else:
        c, sub, note = heuristic(r)
    ant = ANTICIPE.get(r["name"], "")
    if r["name"] in ("RHV2Fresh.thm_anchorState_terminalPrimeCountOne",
                     "RHV2Fresh.thm_anchoredTowerState_terminalPrimeCountOne"):
        sub, note = "S-fenêtre", ("affirme qu'une fenêtre construite (ancrée) contient exactement un premier : "
                                  "compatible avec la grille (une cellule peut contenir 0, 1 ou plusieurs premiers) ; "
                                  "à requalifier seulement si on la lit comme « la » cellule de la Tour")
    rows.append(dict(base=r["base"], name=r["name"], file=r["file"], line=r["line"], classe=c,
                     sous_classe=sub, anticipe=ant, note=note, source=r.get("source", "jsonl"),
                     type=re.sub(r"\s+", " ", r["type"] or "")[:400]))
with open(f"{OUT}/audit_thms.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
    w.writeheader()
    w.writerows(rows)
missing = [k for k in MANUAL if k not in {r["name"] for r in rows}]
if missing:
    print("MANUAL non trouvés:", missing)
cnt = Counter((r["base"], r["classe"]) for r in rows)
bases = ["RHV6Fresh", "rhv3_lean", "RHV5Fresh", "rhv2_fresh", "rhv4_lean", "rh_gap_criterion"]
bases = [b for b in bases if any(r["base"] == b for r in rows)]
print("base", *"GESRX", "total", sep="\t")
for b in bases:
    print(b, *[cnt[(b, c)] for c in "GESRX"], sum(cnt[(b, c)] for c in "GESRX"), sep="\t")
print("total", *[sum(cnt[(b, c)] for b in bases) for c in "GESRX"], len(rows), sep="\t")
print("anticipe:", sum(1 for r in rows if r["anticipe"]))
