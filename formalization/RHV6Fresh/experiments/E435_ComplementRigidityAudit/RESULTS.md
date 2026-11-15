# E435 — Résultats : audit de la rigidité du complément au premier partagé (2026-11-04)

Pré-enregistrement : commit `36998f6d` (README.md). Module isolé `RHV6Fresh/Terminal/ComplementRigidityAudit.lean`
(non ajouté à `RHV6Fresh.lean`) : 16 déclarations (15 théorèmes, 1 définition), **une seule tentative de compilation**
(`logs/lean_attempt1.txt`, EXIT=0), `sorry = 0`, `admit = 0`, 9 `#print axioms` tous `[propext, Classical.choice,
Quot.sound]`. Sondes : `logs/probe_attempt1.txt` (3 erreurs : un découpage `gcongr` dans la majoration de la primitive
de la paire, un `ring` superflu, et les deux buts `False` de S4), `logs/probe_attempt2.txt` (seuls les deux buts `False`
de S4 restent). `lake build RHV6Fresh` : `logs/lake_build_full_trimmed.txt`.

**Verdict : D** (aucune rigidité indépendante dans le corpus), avec la forme C de la propriété absente compilée
(`no_offCarrier_iff_remainderExponent_half`). Ni B, ni C, ni D ne sont une preuve de RH.

## 1. Inventaire exhaustif des théorèmes sur le complément (forme Lean vérifiée)

Définitions (`Terminal/HeightPacket.lean`, build principal) : `channelOn S x = Σ'_{ρ∈S} residu(x, ρ)` ;
`heightPacket T = {ρ | |Im ρ| = T}` ; `C.packet = heightPacket (hauteur du zéro)` (`OffCarrier.lean:896`), et dans le cas
miroir `C.packet = {z, z', z̄, z̄'}` (`packet_eq_four_of_mirror`) ; `backgroundPrimitive x = x·fond lissé(x)` ;
`channelPrimitive S x = x·channelOn S x` ; `stepAt F N = F(N+1) − F(N)` ; `exactRemainder N = ψ(N) − stepAt fond N` ;
`localPacket S N = stepAt (channelPrimitive S) N` ; `remainderIncrement N = exactRemainder(N+1) − exactRemainder N` ;
`packetIncrement S N = localPacket S (N+1) − localPacket S N` ; `packetᶜ` est le complément ensembliste `Sᶜ` des
indices (toutes les fréquences autres que celles du paquet). `pairPrimitive` (`PacketSeriesBalance.lean`) :
`−m·x·(T_z/(ρ_z+1) + conj + T_z'/(ρ_z'+1) + conj)`. `smoothedRemainder x` (`ArithmeticReading.lean:452`) : somme lissée
de von Mangoldt moins le fond, définie par les premiers seuls.

| # | Nom (fichier) | Énoncé | Hypothèses | Domaine | Cond. | Dép. RH | Famille infinie de rencontres | Nature |
|---|---|---|---|---|---|---|---|---|
| 1 | `channel_eq_packet_add_complement` (HeightPacket) | canal entier = canal(S) + canal(Sᶜ) | `1 < x` | tout S | incond. | non | oui (tout x) | identité de décomposition |
| 2 | `psi_eq_background_add_packet_add_complement` (HeightPacket) | ψ(N) = fond + paquet + complément | `2 ≤ N` | tout S | incond. | non | oui (tout N) | identité |
| 3 | `exactRemainder_eq_packet_add_complement`, `compensation_eq_complement` (HeightPacket) | reste exact = paquet + complément | `2 ≤ N` | tout S | incond. | non | oui | identité |
| 4 | `remainderIncrement_eq_packet_add_complement`, `eventCompensation_eq_complement` (HeightPacket) | incrément du reste = incrément paquet + incrément complément | `2 ≤ N` | tout S | incond. | non | oui | identité |
| 5 | `remainderIncrement_arithmetic` (HeightPacket) | incrément du reste = Λ(N+1) − variation du pas du fond | aucune | tout N | incond. | non | oui | identité (côté premiers) |
| 6 | `spectralRemainder_eq_packet_add_complement`, `remainderBetween_eq_packet_add_complement`, `complementBetween_forced` (InverseReading) | ΔR(a,b) = paquet + complément ; complément = ΔR − paquet | `2 ≤ a, b` | tout S | incond. | non | oui | identité |
| 7 | `complement_forced_at_prime_event` (GrammaticalRaccordJump) | à l'événement premier de rang n : complément = log p − variation du fond − paquet | `1 ≤ n` | tout S | incond. | non | oui (tout rang) | identité (égalité de raccord à l'événement) |
| 8 | `packetIncrement_series_telescopes`, `complement_series_balance`, `pair_complement_series_balance` (PacketSeriesBalance, isolé) | somme de fenêtre du complément = contenu arithmétique − effet de bords du paquet | `2 ≤ a` ; cas miroir pour la paire | toute fenêtre | incond. | non | oui | identité (effondrement aux bords) |
| 9 | `pair_window_re_balance`, `pairPrimitive_re_from_contacts` (BoundaryContactReading, isolé) | bilan de fenêtre en partie réelle ; effet de bords par les contacts | `2 ≤ a`, cas miroir, `0 < x` | toute fenêtre | incond. | non | oui | identité |
| 10 | `norm_packetIncrement_finset_le` (RawSpectralChannel, isolé) | ‖incrément d'une famille FINIE s‖ ≤ Σ multiplicités | `1 ≤ N` | famille finie | incond. | non | oui, mais radialement aveugle (ne lit pas β) | majoration |
| 11 | `norm_remainderIncrement_ge`, `break_realized_by_high_frequencies` (RawSpectralChannel) | Λ(N+1) − 1 − 4τ − Σm ≤ ‖incrément du complément de s‖ | `2 ≤ N` | famille finie | incond. | non | oui ; borne inférieure ponctuelle, sans exposant | majoration (inférieure) |
| 12 | `window_complement_bound` (FiniteGrammarLayer), `window_complement_margin` (LocalWindowTransmission), `complement_filtered_le` (GrammarWindowEstimate) | sommes « suivantes » (hautes fréquences) bornées par un budget × (x₀ + x_m) ou une marge | `1 < x_r` | queue au-dessus d'une hauteur | incond. | non | oui, à l'exposant 1 seulement | majoration |
| 13 | `smoothedRemainder_linear_growth`, `one_mem_remainderExponents`, `remainderExponent_mem_bracket` (RemainderExponent) | ‖reste lissé‖ ≤ C·x ; 1/2 ≤ θ* ≤ 1 | aucune | tout x > 1 | incond. | non | oui, exposant 1 | asymptotique |
| 14 | `mirror_pair_exponent_le`, `mirror_pair_exponent_le_remainderExponent` (RemainderExponent) | sous une borne x^θ du reste : max(β, 1−β) ≤ θ ; donc max(β,1−β) ≤ θ* | borne du reste | tout membre | cond. (la borne) / incond. (θ*) | non | oui | asymptotique (lecture du pôle, membre par membre) |
| 15 | `off_debt_visible_in_exponent`, `compensation_closure_verdict` (CompensationRigidity) | membre hors ligne ⟹ 1/2 < θ* ; poids non effacé dans toute représentation spectrale | hors ligne | — | incond. | non | oui | asymptotique + unicité |
| 16 | `infinite_complement_closes`, `mirror_closes_of_remainder_growth` (OffAmplificationAudit, MirrorGroupNonCompensation) | ∃ θ < 1−β, ‖reste‖ ≤ C·x^θ ⟹ False | la borne | membre bas | cond. | la borne est FAUSSE en présence du membre (ce n'est pas RH) | oui | asymptotique (no-go) |
| 17 | `finite_group_noncompensation` (OffAmplificationAudit) | aucun groupe fini ne compense le miroir sous son exposant | hauteur dans ]H, H''] | groupe fini | cond. | non | non (fini) | asymptotique |
| 18 | `acquired_exponent_not_below_mirror`, `acquired_exponent_admits_any_off_signature` (OffAmplificationAudit, JointSignatureHorizon) | l'exposant acquis est 1, jamais < 1−β | aucune | — | incond. | non | — | constat |
| 19 | `riemannHypothesis_iff_remainderExponent_eq_half` (RemainderExponent), `all_off_signatures_excluded_iff_remainderExponent_half` (JointSignatureHorizon) | RH ⟺ θ* = 1/2 ; aucune signature OFF ⟺ θ* = 1/2 | aucune | — | équivalences | = RH | — | frontière |
| 20 | `complement_modification_tendsto`, `complement_unchanged_forces_defect_zero` (InsertionExclusion) | si une autre famille reconstruit le même reste, la différence tend vers −Δ ; famille inchangée ⟹ Δ = 0 | deux représentations convergentes | abstrait (espace normé) | cond. | non | oui | convergence (unicité de limite) |
| 21 | `detour_transport_product`, `detour_arithmetic_factor_ne_one`, `detour_defect_eq_memberStep_product` (TransportAtSharedPrime, isolé) | produit des trois transports du détour ; facteur (p²_{n+1}/(p_n p_{n+2}))^δ ≠ 1 ; = produit des deux pas de membre | cas miroir | 3 premiers | incond. | non | non (3 premiers) | identité (pas une contrainte : §19.19, aucune conservation) |
| 22 | `inversion_height`, `inversion_radial`, `radial_of_contact_value_ratio`, `mirror_contacts_coincide_iff`, `mirror_amplitude_ratio_tendsto` | lectures de T et β par les contacts ; contacts Tour/miroir coïncident ⟺ β = 1/2 ; rapport miroir/OFF → ∞ | β > 0, T > 0 | une Tour, sa paire | incond. | non | — | identités / asymptotique sur la paire seule (pas sur le complément) |

Lecture : les lignes 1–9 sont des **identités** (le complément est DÉFINI comme différence : aucune ne contraint sa
valeur). Les lignes 10–12 sont des majorations **à l'exposant 1** ou **sans exposant**, radialement aveugles. Les
lignes 13–19 sont les seules propriétés asymptotiques : elles portent sur le **reste total**, jamais sur le complément
seul, et la seule borne acquise est l'exposant 1. Les lignes 20–22 ne portent pas sur le complément collectif.

## 2. Réduction mathématique exacte du bilan (compilée)

`complement_window_re_by_contacts` (fenêtre `[a, a+m]`, `2 ≤ a`, cas miroir) :

    Re(Σ_{k<m} incrément du complément (a+k))
      = Σ_{k<m} Λ(a+k+1)
        − Re(stepAt fond (a+m) − stepAt fond a)
        − [ (R(a+m+1) − R(a+m)) − (R(a+1) − R(a)) ]

où `R(x) = contactReading C x` est EXACTEMENT (définition `contactReading`, égale à la partie réelle de la primitive de
la paire par `pairPrimitive_re_eq_contactReading`, `0 < x`) :

    R(x) = −2m·x·( v_z(k_z(x)) · (x / C_z(k_z(x)))^{1/2−δ} · ((3/2−δ)·cos(π f_z(x)) + T·sin(π f_z(x))) / ‖ρ_z+1‖²
                 + v_z'(k_z'(x)) · (x / C_z'(k_z'(x)))^{1/2+δ} · ((3/2+δ)·cos(π f_z'(x)) + T·sin(π f_z'(x))) / ‖ρ_z'+1‖² )

avec, pour chaque membre (zéro `z` à `β = 1/2−δ`, miroir `z'` à `1/2+δ`, même hauteur `T`) : `k(x)` le dernier contact
avant `x`, `v(k)` la valeur réelle signée au contact, `C(k)` la position du contact, `f(x)` la fraction de cellule.
Valeurs signées, fractions de cellule, retards d'angle conservés ; aucun module, aucun terme supprimé ; le complément
n'est supposé ni nul, ni borné.

Valeur ponctuelle (`complement_value_eq`, `2 ≤ N`) : `localPacket packetᶜ N = exactRemainder N − (P(N+1) − P(N))`.
Au niveau des primitives (`complementPrimitive_eq`, `1 < x`) : `channelPrimitive packetᶜ x = x·reste lissé(x) − P(x)`.

## 3. Sondes

- **S1 réussie** : `complement_window_re_by_contacts` (réécriture de `pair_window_re_balance` et de
  `pairPrimitive_re_from_contacts` aux quatre points).
- **S2 réussie** : `complement_window_eq_boundary`, `complement_windows_concat`, `complement_series_of_windows`,
  `channelPrimitive_compl_eq`, `complement_value_eq`, `complementPrimitive_eq`. Constat : pour TOUTE suite de fenêtres,
  la série du complément ne lit que les bords ; la série de fenêtres ne porte aucune information au-delà de la suite
  ponctuelle `N ↦ exactRemainder N − pas de la paire en N`. Aucune borne uniforme supposée.
- **S3 réussie** (instances des seules rigidités retrouvées) : `complement_break_lower_bound` (la part de la cassure
  qui dépasse `1 + 4τ + Σ multiplicités des quatre membres` est portée par le complément de la paire, en tout `N ≥ 2`) ;
  `remainderExponent_ge_mirror` (`1/2 + δ ≤ θ*`) ; `no_remainder_bound_below_mirror` (toute borne du reste sous
  `1/2 + δ` est contradictoire avec le porteur) ; `acquired_exponent_admits_carrier` (l'exposant acquis est `1`) ;
  `norm_pairPrimitive_le` (‖primitive de la paire‖ ≤ 2m(1/(‖ρ_z‖‖ρ_z+1‖) + 1/(‖ρ_z'‖‖ρ_z'+1‖))·x^{3/2+δ}) ;
  `complement_bound_transfers` (une borne `K·x^{1+θ}` du complément seul donne au reste lissé l'exposant
  `max(θ, 1/2+δ)` : jamais mieux que `1/2 + δ`).
- **S4 échouée (attendu)** : deux buts `False` laissés, reproduits intégralement en §4.

## 4. Buts Lean terminaux restants (reproduits intégralement, `logs/probe_attempt2.txt`)

Sonde S4a (porteur + cas miroir + S1–S3) :

```
RHV6Fresh/Terminal/ComplementRigidityProbe_SCRATCH.lean:234:2: error: unsolved goals
C : OffCarrier
h : C.outgoing.zLaterMember = ↑(mirrorMember C.zero)
hS1 :
  ∀ (a : ℕ),
    2 ≤ a →
      ∀ (m : ℕ),
        (∑ k ∈ Finset.range m, packetIncrement C.packetᶜ (a + k)).re =
          ∑ k ∈ Finset.range m, ArithmeticFunction.vonMangoldt (a + k + 1) -
              (stepAt backgroundPrimitive (a + m) - stepAt backgroundPrimitive a).re -
            (C.contactReading (↑(a + m) + 1) - C.contactReading ↑(a + m) -
              (C.contactReading (↑a + 1) - C.contactReading ↑a))
hS3a :
  ∀ (N : ℕ),
    2 ≤ N →
      ArithmeticFunction.vonMangoldt (N + 1) - 1 - 4 * trivialTailConstant -
          ∑
            ρ ∈
              {memberIndex C.zero, memberIndex (mirrorMember C.zero), conjIndex C.zero,
                conjIndex (mirrorMember C.zero)},
            ↑(zetaZeroMultiplicity ↑ρ) ≤
        ‖packetIncrement C.packetᶜ N‖
hS3b : 1 / 2 + C.radialShift ≤ remainderExponent
hS3c : ∀ {θ K : ℝ}, θ < 1 / 2 + C.radialShift → (∀ (x : ℝ), 1 < x → ‖smoothedRemainder x‖ ≤ K * x ^ θ) → False
hS3d : 1 ∈ remainderExponents ∧ ¬1 < 1 / 2 + C.radialShift
hS3e :
  ∀ {θ K : ℝ},
    (∀ (x : ℝ), 1 < x → ‖channelPrimitive C.packetᶜ x‖ ≤ K * x ^ (1 + θ)) →
      ∃ K', ∀ (x : ℝ), 1 < x → ‖smoothedRemainder x‖ ≤ K' * x ^ max θ (1 / 2 + C.radialShift)
⊢ False
```

Sonde S4b (complément borné à l'exposant `1 + θ`, `θ < 1/2 + δ`) :

```
RHV6Fresh/Terminal/ComplementRigidityProbe_SCRATCH.lean:242:2: error: unsolved goals
C : OffCarrier
h : C.outgoing.zLaterMember = ↑(mirrorMember C.zero)
θ K : ℝ
hθ : θ < 1 / 2 + C.radialShift
hK : ∀ (x : ℝ), 1 < x → ‖channelPrimitive C.packetᶜ x‖ ≤ K * x ^ (1 + θ)
K' : ℝ
hK' : ∀ (x : ℝ), 1 < x → ‖smoothedRemainder x‖ ≤ K' * x ^ (1 / 2 + C.radialShift)
this :
  1 / 2 + C.radialShift < 1 / 2 + C.radialShift →
    (∀ (x : ℝ), 1 < x → ‖smoothedRemainder x‖ ≤ K' * x ^ (1 / 2 + C.radialShift)) → False
⊢ False
```

Lecture de S4b : le transfert donne le reste à l'exposant exactement `1/2 + δ` ; le no-go exige strictement moins. Une
borne du complément seul, même sous l'exposant du miroir, ne produit donc aucune contradiction : le reste total est
autorisé à croître comme le miroir.

## 5. Non-circularité

Aucune contrainte candidate retenue ne suppose le membre suivant ON, n'impose β = 1/2, ne suppose une conservation du
transport (§19.19 : aucune dans le corpus), ni une absence de compensation non démontrée. Les deux bornes du reste
(`mirror_pair_exponent_le`, `infinite_complement_closes`) sont conditionnelles à une borne de croissance du reste qui
n'est acquise qu'à l'exposant `1` ; la borne `< 1/2 + δ` est fausse en présence du porteur, et la borne `= 1/2`, qui
exclut tout porteur, est RH (`no_offCarrier_iff_remainderExponent_half`, compilé).

## 6. Verdict : D

> **Note du 2026-11-06 (auteur, §19.51).** Le paragraphe « propriété absente » ci-dessous est retiré comme formulation :
> l'absorption par le complément et la borne d'exposant sont des ajustements après coup exclus par la seconde obligation ;
> aucune propriété manquante n'est déclarée dans ces termes. Le verdict D (aucune rigidité indépendante dans les énoncés
> audités) et les théorèmes compilés restent ; le texte d'origine est conservé comme preuve d'exécution.

**Les théorèmes retrouvés ne fournissent aucune contrainte indépendante suffisante.** Propriété absente, nommée
exactement : une majoration inconditionnelle du reste lissé (ou, équivalemment par `complementPrimitive_eq`, du
complément collectif) par `K·x^θ` avec `θ < 1/2 + δ`, c'est-à-dire **un exposant admissible du reste strictement
inférieur à l'exposant du miroir**. Pourquoi les théorèmes existants ne la produisent pas : (i) toutes les égalités sur le
complément sont des identités de décomposition (le complément est une différence, jamais un objet contraint en
lui-même) ; (ii) les majorations compilées portent sur des familles finies (bornées par leurs multiplicités, aveugles
à β) ou sur des queues à l'exposant `1` ; (iii) la lecture du pôle fixe une borne **inférieure** de l'exposant par les
membres (`1/2 + δ ≤ θ*`), jamais une borne supérieure sous `1` ; (iv) une borne du complément seul se transfère au reste
à l'exposant `max(θ, 1/2+δ)`, donc n'apporte rien. La dérive OFF (Tour + miroir) est compatible avec toutes les
identités du corpus : elle n'est exclue que par `θ* = 1/2`, qui est RH.

Rien de B : aucune réduction nouvelle du chaînon (le chaînon reste « exposant du reste < 1 − β », §19.48). Rien de A.
