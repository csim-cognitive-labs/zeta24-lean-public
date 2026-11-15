# AUDIT DE RÉORIENTATION — contacts des Tours, contributions par écart, point de rencontre (2026-11-01)

Demande de l'auteur (2026-11-01) : réorienter tout le projet sur la lecture « contacts → contribution exacte par écart →
rencontre (cassure) », sans aucune démarche statistique ni partielle ; prouver que les écarts des contributions sont bien
les écarts de la rencontre ; auditer tous les théorèmes, les `.md`, les expériences ; produire le plan. Lecture seule :
aucun Lean modifié, aucune compilation lancée (doctrine §19.21 : aucune étape Lean avant feu vert). Jumeau déterministe des
nombres du texte collé : `twin.py` (mpmath, 30 chiffres, 11 écarts, 3 zéros), reproduit ci-dessous.

## 1. « Ce sont bien les mêmes écarts » : déjà prouvé par construction, dans le compilé

Toutes les notions d'écart du dépôt sont indexées par UNE structure, `PrimeGapInterval` (champ unique : le rang `n`), et
par UNE fonction, `fnPrimeAtRank`. Il n'existe aucune seconde notion d'écart. Vérifié objet par objet :

| Objet compilé | Module:ligne | Bornes | Canal |
|---|---|---|---|
| `PrimeGapInterval.lower/upper` | LocalPrimeGapSynchronization.lean:53-55 | `p_n`, `p_{n+1}` | — |
| `PrimeGapInterval.a/b` | :57-59 | `log p_n`, `log p_{n+1}` | — |
| `gapTerm ρ a b = ∫_a^b e^{ρt} dt` | GapSynchronization.lean:38 | libres | brut (Tour `x^ρ/ρ`) |
| `gapTerm_eq_cpow` | :99 | `(b^ρ − a^ρ)/ρ` | brut : c'est exactement `Δ_{ρ,n}` du texte collé |
| `primeGapContribution ρ n = gapTerm ρ (log p_n) (log p_{n+1})` | FixedGapRaccords.lean:40 | `p_n`, `p_{n+1}` | brut |
| `countingGapTerm ρ a b = ∫_a^b e^{ρt}/t dt` | LocalPrimeGapSynchronization.lean:84 | libres | comptage (= différence d'`Ei`, canal `J` historique) |
| `zeroLocalContribution ρ I` | :87 | `I.a`, `I.b` | comptage, forme réelle |
| `smoothedLocalContribution ρ I = (−m/(ρ+1))·gapTerm ρ I.a I.b` | :256 | `I.a`, `I.b` | lissé |
| `residueTerm_gap_eq` | GapSynchronization.lean:141 | | lissé = `(−m/(ρ+1))` × brut, mêmes bornes |
| `localArithmeticTarget I = R(I.upper) − R(I.lower)` | LocalPrimeGapSynchronization.lean:260 | `p_n`, `p_{n+1}` | premiers seuls |
| `localSynchronization I` | :283 | même `I` | cible = Σ sur TOUS les zéros des contributions lissées |
| `prime_gap_synchronization n` | GapSynchronization.lean:162 | `p_n`, `p_{n+1}` | même loi écrite avec `gapTerm` et `fnPrimeAtRank` |
| `meetingPoint I = I.upper` | MeetingPoint.lean:54-56 | `p_{n+1}` | rencontre |
| `imposedShare w I` | :72 | `I.lower`, `meetingPoint I` | lissé, terme conjoint |
| `OffCarrier.gap = ⟨C.n⟩`, `gap_lower : lower = occurrence du zéro OFF` | OffCarrier.lean:221-227 | `p_n`, `p_{n+1}` | porteur |
| `OffCarrier.liaison : meetingPoint C.gap = M du raccord sortant` | :231 | `p_{n+1}` | porteur |
| `pairCounting`, `pairReal`, `pair_hyperbolic_signature`, `pair_gapTerm_signature`, `target_split` | OffCarrier.lean:725-908 | `I.a`, `I.b` | paire OFF sur le même `I` |
| `exactRemainder N = ψ(N) − pas du fond`, `remainderIncrement` | HeightPacket.lean:138,181 | entiers | ψ exact |
| `break_at_meeting : remainderIncrement(p_{n+1}−1) = log p_{n+1} − fond` | OffCarrier.lean:1104 | `p_{n+1}` | cassure exacte |
| `gap_demand_eq_break_add_rest` | :1130 | `p_n` … `p_{n+1}` | demande de l'écart = pas intérieurs + cassure |
| `smoothedZeroPrimitive_nat_difference : P(N+1) − P(N) = ψ(N)` (N ≥ 2) | RHV3Lean/Objects/ZetaSmoothedUnsmoothingP5.lean:107 | entiers | pont canal lissé → escalier exact |
| `psi_eq_background_add_packet_add_complement` | HeightPacket.lean:123 | entiers | ψ(N) = fond + paquet + complément, exact |

Conclusion 1. L'écart de la contribution (brute, lissée ou de comptage), l'écart de la cible arithmétique, l'écart de la
rencontre et l'écart de la cassure sont le même objet `⟨n⟩`, aux mêmes bornes `fnPrimeAtRank n` et `fnPrimeAtRank (n+1)`.
La rencontre est la borne supérieure de cet écart, par définition (`rfl`). Il n'y a rien à prouver de plus : la preuve est
la définition partagée, et toutes les identités du tableau sont compilées sans axiome ni `sorry` (journal de reconstruction
`audits_compilation/exactmeetingaudit/etapeC_full_build.log` ; seule erreur : clash racine `windowProjection`, antérieur).

Conclusion 2 (ce qui N'EST PAS compilé, et doit rester dit). La somme sur tous les zéros des contributions BRUTES
(`Σ_ρ (p_{n+1}^ρ − p_n^ρ)/ρ`, canal de Chebyshev du texte collé) n'est identifiée à aucun objet arithmétique dans le dépôt :
la formule explicite de ψ non lissée (convergence conditionnelle) n'est ni dans Mathlib ni dans le dépôt. Le texte collé
l'écrit lui-même (« il faut respecter la prescription de sommation infinie »). De même le canal de comptage `J` : `Ei`
absent de Mathlib, `CountingExplicitFormula` est un `def : Prop` NOMMÉ, non démontré (CountingFieldArchitecture.lean:386).
Le seul pont compilé entre les contributions individuelles et la cassure exacte `log p_{n+1}` est : contribution lissée
(`−m/(ρ+1)` × brute) → somme = incrément du reste lissé (`localSynchronization`) → ψ(N) = pas de la primitive lissée
(`smoothedZeroPrimitive_nat_difference`) → cassure `log p_{n+1}` (`break_at_meeting`). C'est une chaîne d'identités exactes,
sans approximation, sans statistique : elle est la forme compilée de la flèche « contributions → rencontre ».

Conclusion 3 (contacts). Les contacts `C_k = exp((arctan(T/β) + kπ)/T)` sont compilés (`towerMotionOf`, Tower/TrueTower.lean:23-40 ;
`contactMinusAt`, Tower/Incidences.lean:17), avec, en tête de module, « aucun premier n'entre ici ». Trois familles de points
sont compilées DISTINCTES : contacts de phase `C_k`, changements de signe de la densité de comptage `x_k = exp((π/2+kπ)/T)`
(`densitySignChangeLog`), extrema du champ autour de `li` `D_k` (`modulationExtremum`) ; `contact_vs_densitySignChange`
(LocalPrimeGapSynchronization.lean:240) : `log C_k − log x_k = −arctan(β/T)/T`, et CountingFieldContacts.lean : `C_k < D_k < C_{k+1}`,
`β = T·tan(T·(log D_k − log C_k))`. Le texte collé est exact sur ce point et confirme §19.10 : contact ≠ rencontre.
« Un contact ne tombe pas sur un premier » n'est pas un théorème (égalité d'un nombre transcendant présumé et d'un entier :
indécidable ici) et n'a pas à l'être : aucun théorème du dépôt n'identifie un contact à un premier (vérification §4).

## 2. Jumeau déterministe des nombres du texte collé (`twin.py`, mpmath 30 chiffres)

Contacts `C_0…C_10` des trois premiers zéros : identiques aux onze valeurs du texte, aux dix chiffres affichés.
Contributions brutes `−2 Re((p_{n+1}^ρ − p_n^ρ)/ρ)` et sommes des trois Tours, canal brut et canal `J` : identiques aux
valeurs du texte sur les onze écarts (2–3 … 31–37), aux sept chiffres affichés. Ajouté : canal lissé (colonne compilée).

| écart | brut T1 | brut T2 | brut T3 | somme brute | somme J | somme lissée |
|---|---|---|---|---|---|---|
| 2–3 | −0,1145041 | +0,2694753 | −0,2098291 | −0,054858 | −0,0756716 | −0,0093666 |
| 3–5 | +0,2604683 | −0,2858498 | +0,0010391 | −0,0243424 | −0,0114111 | −0,0040201 |
| 5–7 | −0,4759428 | +0,1596571 | +0,3075858 | −0,0087000 | −0,0003371 | −0,0043784 |
| 7–11 | −0,0251360 | −0,0750551 | −0,1323653 | −0,2325564 | −0,0909474 | +0,0086873 |
| 11–13 | +0,7789462 | +0,2278985 | −0,3597564 | +0,6470883 | +0,2618614 | +0,0220283 |
| 13–17 | −0,9042799 | −0,2171873 | −0,0427767 | −1,164244 | −0,4309572 | −0,0525905 |
| 17–19 | +0,8490128 | +0,3690107 | +0,6671627 | +1,885186 | +0,6543623 | +0,0398957 |
| 19–23 | −0,6946744 | −0,3433474 | −0,3814655 | −1,419487 | −0,4726782 | +0,0200411 |
| 23–29 | +0,6166900 | −0,4921257 | −0,1997264 | −0,0751621 | −0,0222141 | −0,0688827 |
| 29–31 | +0,4116461 | +0,4851757 | +0,6308250 | +1,527647 | +0,4492747 | +0,0301310 |
| 31–37 | −1,404101 | −0,2716780 | −0,7333684 | −2,409147 | −0,6761970 | +0,0781173 |

Lecture, en mots : trois Tours ne reconstituent aucune cassure ; leurs sommes sur un écart ne sont pas la demande de
l'écart (`no_finite_family_accomplishes_demand`). Ce tableau caractérise trois contributions exactes ; il ne contraint rien.
Les trois canaux portent les mêmes trois zéros et diffèrent par un facteur exact dans l'intégrande (`1`, `1/t`, `1/(ρ+1)`).

## 3. Les théorèmes cités par le texte collé : vérification nom par nom

| Nom cité | Existe ? | Énoncé réel (module:ligne) | Lecture à privilégier (texte collé) | Verdict |
|---|---|---|---|---|
| `meetingPoint_eq_upper` | oui | MeetingPoint.lean:56 : `meetingPoint I = fnPrimeAtRank (I.rank+1)`, `rfl` | le premier supérieur est le lieu de la cassure | FIDÈLE ; aucune mention de contact |
| `meetingPoint_unique` | oui | :63 : même rang ⟹ même point de rencontre | unique par écart | FIDÈLE |
| `all_signals_meet` | oui | :83 : `localArithmeticTarget I = Σ' smoothedLocalContribution` (= `localSynchronization`) | identité de synchronisation collective | FIDÈLE ; canal lissé, pas de contact géométrique commun |
| `imposedShare_eq` | oui | :75 : part = incrément du reste − incrément des autres (`imposed_joint_gap`) | deux passages partagent un événement identifié | FIDÈLE, mais c'est une identité (§19.21 P2) : « part imposée » = définie par le membre, jamais par l'écart |
| `thm_passage_occurrence_succ` | NON dans RHV6Fresh | RHV5Fresh/Off/PassageArithmetic.lean:108 (dépôt antérieur) | — | HORS CORPUS : ne pas citer pour RHV6Fresh |
| `thm_expectedMinimum_cases` | NON (nulle part dans `formalization/`) | — | — | INEXISTANT : à retirer du texte |
| `mirror_contacts_never_coincide` | oui | HorizontalExclusion.lean:136 : `β < 1/2` ⟹ `contactMinusAt (miroir) k ≠ contactMinusAt z k` | les contacts miroirs diffèrent, les deux contributions portent sur le même écart | FIDÈLE ; et `OffCarrier.pairCounting` le compile sur le même `I` |
| `gap_demand_eq_break_add_rest` | oui | OffCarrier.lean:1130 : demande de l'écart = pas intérieurs + cassure `log p_{n+1}` − fond | le complément n'est pas une erreur autorisée | FIDÈLE ; identité exacte, canal ψ |
| `no_finite_family_accomplishes_demand` | oui | MeetingExactness.lean:323 : aucune famille finie n'égale le reste lissé sur un voisinage de la rencontre | une famille finie ne réalise pas la cassure | FIDÈLE |
| `tail_not_eventually_zero` | oui | :334 : la queue n'est jamais identiquement nulle près d'une rencontre | la contribution collective ne se réduit pas à une dernière Tour | FIDÈLE |

Huit noms sur dix existent et leurs énoncés portent exactement la lecture demandée ; aucune des « anciennes lectures
problématiques » du texte (« le premier est un contact de Tour », « contact géométrique commun », « reste toléré ») ne
figure dans un énoncé ou une docstring de ces huit théorèmes : elles étaient des lectures de textes, pas du Lean.
Deux noms sont à retirer.

## 4. Audit des 219 modules Terminal (4 135 théorèmes) — méthode et résultat

Méthode : recensement mécanique (`census.csv` : théorèmes par module, présence dans la racine, import par
`DemonstrationChain`, usage de `PrimeGapInterval`, contacts, `gapTerm`, contributions lissées, comptage, reste exact,
`meetingPoint`) ; puis lecture des énoncés et docstrings de chaque module par quatre lecteurs indépendants (groupes
alphabétiques de 55), classement selon la doctrine : FIDÈLE / À RECONTEXTUALISER / ÉQUIVALENT-RH / PARTIEL / MIXTE ;
recherche ciblée de toute identification contact = premier ; relevé du lexique proscrit ; relevé des hypothèses nommées ⟺ RH ;
grep `sorry/admit/axiom`. Les quatre rapports sont annexés (§8). Résultats agrégés en §8.0.

Point fixe de l'audit, vérifié directement : AUCUN théorème du dépôt n'identifie un contact (`contactMinusAt`,
`contactPlusAt`, `incidence`, `towerPosition`) à un premier (`fnPrimeAtRank`, `Nat.Prime`, `primalEventAt`,
`memberOccurrence`). Les modules qui comparent contacts et premiers le font par inégalités ou par ordre
(`FirstZeroContactComparison`, `TowerTwoSidedRoom`, `ThreeZeroWindow`) ou par décalage exact
(`contact_vs_densitySignChange`, `CountingFieldContacts`). `HorizontalExclusion.lean:132-138` dit explicitement : le passage
horizontal ne partage qu'un premier (dans `ℕ`), jamais un contact de Tour (dans `ℝ`).

## 5. Audit des expériences citées

| Expérience | Canal | Ce qu'elle établit (maître) | Statut sous la nouvelle doctrine |
|---|---|---|---|
| E218–E223 (2026-10-13) | brut `x^ρ/ρ` par écart (E219), comptage `J` par écart (E220, `Ei`, 5000 zéros) | variation exacte de la Tour sur chaque écart, jamais nulle, télescopage, repondération radiale ; incrément d'un écart porté par aucun zéro isolé | E219 : exact, compilé depuis (FixedGapRaccords, GapSynchronization) ; E220 : canal non formalisé, corrélations/RMS/médianes = **observations statistiques** → à ne plus citer comme résultat, seulement comme journal |
| E224–E230 | Tour à l'échelle de la ligne | fréquence = hauteur, enveloppe = position radiale (démontré) ; force de rappel ⟺ RH | exact ; aucune contrainte sur β (dit tel quel) |
| E239–E241 | courant harmonique | courant calculable, rapport constant ⟺ même partie réelle (= but) | exact ; « 27 fenêtres sur 27 » (retrait du premier zéro) = mesure fenêtrée → journal seulement |
| E305 (FixedGapRaccords.lean, 16 thm) | brut par écart | contribution = une primitive aux deux bornes ; point déterminé par ses contributions sur les écarts à partir de tout rang ; vaut pour toute β | COMPILÉ, exact ; identifie, ne contraint pas ; T3 reconstruction aveugle = mesure (jumeau Davenport–Heilbronn) |
| E309 | comptage `J`, 5000 zéros | vrais zéros : aucun écart raté ; toute insertion fabriquée laisse un défaut | **partiel** (troncature à 5000 zéros, « échelle de Gibbs », médianes) ; conforme au compilé (`localSynchronization`, `insertTwo_not_reconstruct`) mais la partie numérique est une mesure de troncature → journal |
| E310–E311 | courbe des premiers → modes | premier zéro retrouvé, exposant lu 1/2 (12 modes) | **mesure à précision finie** (dit tel quel) ; aucune contrainte ; journal |
| Synchronisation locale (2026-10-14, LocalPrimeGapSynchronization.lean, 43 thm) | lissé + comptage | contributions intégrales, additives, fixées par les bornes ; synchronisation exacte (lissé) ; rigidité ; sensibilité radiale | COMPILÉ, exact ; « détecter, retrouver, imposer sont trois choses : la troisième est le but » |
| E301 | — | — | FAUSSE (§19.9), jamais citée |

Règle demandée (« plus aucune démarche statistique ou partielle ») appliquée : les lignes marquées « journal » restent
consignées comme historique ; elles ne sont plus des appuis du raisonnement. Les appuis sont les identités compilées du §1.

## 6. Audit des `.md`

- Maître : aucune phrase n'identifie un contact à un premier (grep « contact … tombe sur / est / coïncide avec un premier » :
  zéro occurrence) ; §19.10 et §19.23 (ligne 3063) disent déjà que la lecture « contact à la fin de chaque écart » est fausse.
- `experiments/riemann_graphique_ANALYSE.md` : déjà conforme (panneau 1 : « le contact au coin est une image du canal de
  comptage non formalisé »).
- README E305, E309, E218–E223 : conformes à leur portée ; E220/E309 contiennent des corrélations, RMS, médianes :
  à lire comme journal (ci-dessus).
- Texte collé (le nouveau) : fidèle sur la chaîne « (β,T) → Tour → contacts → contribution par écart → rencontre » ; à
  rectifier : (i) deux noms de théorèmes inexistants dans RHV6Fresh ; (ii) « canal de Chebyshev » : le canal compilé qui
  rejoint ψ est le canal lissé, le canal brut n'a pas de formule explicite compilée ; (iii) « les contacts déterminent
  exactement ρ » : vrai pour un zéro ISOLÉ (deux contacts donnent T et β : `height_of_consecutive_extrema`,
  `radial_of_extremum_offset`), mais le signal arithmétique ne voit que la somme (E163 : aucun canal antisymétrique) ;
  (iv) « point 5, décomposition par cellules de contacts » : le découpage d'un écart aux contacts est le télescopage
  (`countingGapTerm_add`, `primeGapContribution_chain`) ; exact, mais il ne crée aucune information nouvelle (E218 : « la
  lecture de toute la suite des écarts ne contient rien de plus que la Tour elle-même »).

## 7. Plan de réorientation (pré-enregistré ; aucune étape Lean ni expérience lancée avant feu vert)

Principe : un seul fil, « (β, T) → Tour → contacts → contribution exacte par écart → rencontre → cassure », porté
uniquement par des identités compilées. Tout ce qui est statistique, fenêtré, asymptotique ou tronqué est relégué au
journal. Les acquis ne sont pas remis en cause : ils sont reclassés (§3–§6).

**Étape F — `SameGapsAudit.lean` (module isolé, non importé par la racine ni par la chaîne).** Rend explicite, en
théorèmes nommés, ce que §1 établit par définition partagée :
- F1 la contribution brute d'un point au rang `n` a pour bornes `a`, `b` de `⟨n⟩ : PrimeGapInterval` (`rfl`) ;
- F2 le point de rencontre de `⟨n⟩` est l'exponentielle de la borne supérieure de la contribution (`exp b = p_{n+1}`) ;
- F3 contribution brute sur l'écart = `(p_{n+1}^ρ − p_n^ρ)/ρ` (instance de `gapTerm_eq_cpow`) : c'est `Δ_{ρ,n}` du texte ;
- F4 contribution lissée = `(−m/(ρ+1))` × contribution brute, sur le même écart (instance de `residueTerm_gap_eq`) ;
- F5 somme sur tous les vrais zéros des contributions lissées de `⟨n⟩` = incrément du reste lissé entre `p_n` et `p_{n+1}`
  (instance de `prime_gap_synchronization`, réécrite avec `meetingPoint`) ;
- F6 pour un porteur OFF, l'écart de sa paire (`pairCounting`, `pair_gapTerm_signature`), l'écart de la rencontre (`liaison`)
  et l'écart de la cassure (`break_at_meeting`) sont `⟨C.n⟩` (égalités de bornes) ;
- F7 pour tout `k`, le contact `C_k` d'un vrai zéro n'est pas un changement de signe de sa densité de comptage
  (`contact_vs_densitySignChange` + `arctan(β/T)/T > 0`) ;
- F8 la somme des trois premiers zéros certifiés (`FirstThreeZerosCertified`) n'égale le reste lissé sur aucun voisinage
  d'aucune rencontre (instance de `no_finite_family_accomplishes_demand`).
Aucun énoncé ne conclut sur β ; aucun ne pose d'hypothèse. Deux tentatives journalisées au plus, log complet, comme §19.23.

**Étape G — registre déterministe des trois Tours connues (expérience pré-enregistrée, bornée, sans statistique).**
Pour chaque écart `[p_n, p_{n+1}]` avec `p_{n+1} ≤ 1000` (168 écarts) : contacts traversés par l'écart, portions de cellules
(`J_{k,n}`), contributions brute, lissée et `J` de chaque Tour, somme des trois ; et, EN REGARD, la demande exacte de
l'écart dans le canal compilé : incrément de la somme lissée de von Mangoldt moins le fond, avec la formule du fond prise
telle quelle dans `ZetaPerronLineIdentity` (aucune autre). Deux implémentations indépendantes (mpmath 30 et 50 chiffres)
= jumeau. Aucun zéro synthétique, aucune fenêtre, aucune moyenne, aucune corrélation. Résultat attendu, dit d'avance :
égalité exacte des télescopages ; somme des trois ≠ demande sur tout écart (c'est F8) ; aucune conclusion sur β.
Valeur : un registre exact remplaçant les figures autour de `li`.

**Étape E (inchangée, désormais le seul objet radial côté axe) — signature de la paire sur trois écarts consécutifs
(§19.12).** La question « la Tour d'une première arrivée OFF et son miroir peuvent-elles respecter toutes les obligations
de rencontre ? » est, une fois écrite, la question ouverte de §19.12 : `pair signature ⟹ ⊥ ?`. Elle se traite après F et G,
sur les identités seules, et sous hypothèse nommée si une hypothèse est nécessaire. Rien n'est promis.

**Étape H — `.md`.** §19.24 consigné ; les lignes E220, E239 (fenêtres), E309 (troncature), E310–E311 (précision finie)
reçoivent la mention « journal, non appui » dans leur paragraphe du maître ; le texte collé est consigné avec ses deux
noms à retirer.

**Ce que le plan ne contient pas, par doctrine.** Aucune exclusion d'OFF à ce stade (frontière inchangée :
`ContinuationForced ⟺ RH`, constance par membre ⟺ RH, `no_carrier_iff_riemannHypothesis`) ; aucune borne sur le reste ;
aucune fenêtre ; aucun théorème « contact = premier » ; aucune hypothèse ⟺ RH posée.

## 8. Audit des 219 modules : résultat agrégé et annexes

**8.0 Décompte (219 modules, 4 135 théorèmes).** FIDÈLE 128 ; À RECONTEXTUALISER 32 ; ÉQUIVALENT-RH 29 (contenu
principal = hypothèse nommée ⟺ RH, étiquetée comme telle) ; PARTIEL 9 (antécédents fenêtrés ou bornes non dérivés :
`FiniteGrammarLayer`, `GrammarOperator`, `GrammarTailBound`, `GrammarWindowEstimate`, `GrammarWindowSeparation`,
`JointComparison`, `PrimeBlockDecomposition`, `PrimeCellError`, `PrimeTransitionDecomposition`) ; MIXTE 21.
`sorry` / `admit` / `axiom` : aucun dans les 219 modules (toutes les occurrences textuelles sont des docstrings « aucun
sorry » ou des identifiants `…admit…`).

**8.1 Contacts identifiés à des premiers : aucun énoncé, dans aucun module.** Trois familles de co-occurrences, toutes
conformes ou à recontextualiser sans toucher aux preuves :
1. encadrements et lectures (premier dans une cellule `C⁻ < q ≤ C⁺`, position de Tour évaluée en un premier) :
   `GeometricEnergyRaccord`, `GrammarTransportLaw`, `TowerRaccord`, `SuccessionInvariants`, `CaptivityWithoutOn`,
   `DemonstrationWithoutRH`, `OneZeroOnePrime`, `RayEnergy`, `ConstraintCorrelation`, `TowerWinding` — conformes
   (`GeometricEnergyRaccord:40` dit explicitement : le premier « n'est en général PAS un rayon ») ;
2. docstrings conditionnelles « un premier égal à un contact » sur un réel générique `q` : `TangentialInversion:17,151,167`
   (`contact_eq_iff_phase`, `contact_radial_formula`, `two_contacts_height_quantized`) — hypothèse d'exercice, jamais
   réalisée ; à réécrire « un réel égal à un contact » ;
3. le mot « rencontre » employé pour un CONTACT de Tour : `GeneratedFrequency` (`meetingOf` = `contactMinusAt z 0`,
   `ArithmeticMeeting`, `MeetingOnLine`, `smoothedMeeting`), `DemonstrationChain:74-87, 633-646, 792`, `OccupiedFrequency:46-121`,
   `ConstantAmplitudeNeed:17,76,87`, `CoupleLock:17-186`, `GrammarTransportLaw:36,378-415`, `MeetingPoint:125`. La doctrine
   réserve « rencontre » à `meetingPoint I = p_{n+1}` ; `OffCarrier:489` dit déjà que « les deux notions de rencontre ne
   coïncident pas ». Conflit de VOCABULAIRE, aucune égalité formelle. Correction = docstrings seules (noms conservés), à
   faire sur feu vert, car `GeneratedFrequency` et `DemonstrationChain` sont dans la chaîne.

**8.2 Lexique proscrit (§19.21) restant** : relevé module par module dans les annexes (compensation, payer, marge,
« impose ») ; `OffAmplificationAudit` ×5, `PrimeGrammarQuantitative` ×4, modules de grammaire. Docstrings seules.

**8.3 Hypothèses nommées ⟺ RH** : toutes étiquetées ; liste complète dans les annexes. Aucune posée comme acquise.

### Annexe A — groupe 1 (modules A–E)
# Audit des ÉNONCÉS Lean — groupe 1 (55 modules, `RHV6Fresh/Terminal/`)

Date : 2026-11-01. Doctrine de référence : réorientation de l'auteur du 2026-11-01 (contacts de Tour ≠ premiers ;
contribution exacte par écart ; point de rencontre = `p_{n+1}` ; cassure réalisée par la totalité ; lexique
compensation/payer/prix/marge admissible proscrit ; aucune hypothèse ⟺ RH présentée comme acquise).
Méthode : lecture des docstrings de module et de chaque `theorem`/`lemma`/`def` avec sa docstring (corps de preuve non lus) ;
greps `sorry|admit|^axiom` hors commentaires ; greps lexicaux.

Légende des verdicts : FIDÈLE = aucun conflit ; À RECONTEXTUALISER = contenu correct mais lecture/lexique à réécrire ;
ÉQUIVALENT-RH = contenu principal = hypothèse nommée ⟺ RH (honnêtement étiquetée sauf mention) ; PARTIEL = lecture
fenêtre finie/asymptotique présentée comme contrainte ; MIXTE = au moins deux défauts distincts.

## 1. Tableau

| module | nb théorèmes | classe d'objet | verdict | notes |
|---|---|---|---|---|
| AmplitudePhase | 9 | other | FIDÈLE | Identités individuelles amplitude–phase, `li` ; spécialisation ON sous `β = 1/2` explicite. |
| AmplitudeStableSynchronization | 14 | RH-equivalence/conditional | ÉQUIVALENT-RH | `AmplitudeStableSync p ⟺ β_l = β_e` ; loi quantifiée ⟺ RH, dit « caractérisation du but ». |
| AnchorContour | 27 | counting/background | FIDÈLE | `ξ₁` entière, contour admissible, raccord à `upperWindowOpen`. |
| AnchorStructure | 22 | counting/background | FIDÈLE | Ancre sous `∃!` nommée (non démontrée) ; comptage avec multiplicité. |
| ArgumentPrinciple | 28 | counting/background | FIDÈLE | Principe de l'argument sur rectangle, instance `ξ₁`. |
| ArithmeticReading | 15 | RH-equivalence/conditional | ÉQUIVALENT-RH | `RH ⟺ ‖A(x)‖ ≤ C√x` ; borne non dérivée, dit explicitement. |
| ArrivalFiberHypotheses | 15 | contact-reading | FIDÈLE | H1 (grille d'arrivée = grille de ligne) reconnue ⟺ `β_l = 1/2` ; contacts non identifiés aux premiers. |
| AstraSeparation | 34 | contact-reading | FIDÈLE | Réfutation de la prémisse Astra ; réductions ⟺ RH étiquetées ; aucune contrainte sur `β_l` revendiquée. |
| AuthenticPassageProfile | 26 | RH-equivalence/conditional | FIDÈLE | Profil du passage ON→l ; fermetures conditionnelles (ancre ∧ loi ⟹ RH, loi ⟸ RH) honnêtes. |
| BackgroundModulation | 17 | counting/background | FIDÈLE | Contacts = « repère des extrema, non ces extrema » ; borne individuelle, aucune somme. |
| BoxAnchor | 8 | counting/background | FIDÈLE | Comptage première bande par deux rectangles, sans `Γ`. |
| BoxCount | 14 | counting/background | FIDÈLE | Élimination de `Γ`. |
| BoxCountHeight | 5 | counting/background | FIDÈLE | Bande de hauteur `T` à valeur `K`, logique seule. |
| CadenceStability | 17 | meeting-break | À RECONTEXTUALISER | `meetingPoint` correct ; lexique « paie un minimum fixe », « cadence imposée » ; « seul régime stable » = caractérisation. |
| CanonicalEnumeration | 31 | other | FIDÈLE | Énumération canonique, `ExplicitIndex ≃ ℕ × Bool`. |
| CanonicalTransition | 12 | contact-reading | FIDÈLE | Position de Tour du premier partagé ; `⟺ β_l = 1/2` par membre, dit « la liaison lit, ne fixe pas ». |
| CaptivityWithoutOn | 5 | contact-reading | À RECONTEXTUALISER | « Captivité par le premier partagé » = encadrement `entryContact < p_min ≤ lastRayContact` ; lecture de contact. |
| CascadeContinuation | 6 | RH-equivalence/conditional | ÉQUIVALENT-RH | Condition réduite ⟺ cascade continue ; « quantifiée, force de RH ». |
| CellRestitution | 20 | contact-reading | FIDÈLE | Indices de cellule, charge `Σ Λ`, paire miroir ; « aucun ne fixe le facteur radial ». |
| CertifiedRemoval | 9 | finite-window | À RECONTEXTUALISER | Retrait de 3 contributions certifiées ; `windowMargin`/« marge » (déjà annoté §19.21) ; estimation non démontrée. |
| ChangePredictor | 25 | RH-equivalence/conditional | ÉQUIVALENT-RH | Résidu `D` ; prédicteur exact+nul ⟺ loi « seule la hauteur évolue » ; `D ≡ 0 ⟺` borne `√x`. |
| ChebyshevAsymptoticToLogGaps | 8 | RH-equivalence/conditional | ÉQUIVALENT-RH | PNT nommé (vrai) ; `DemandBoundedAtMeetings ∧ SummitAttained ⟹ RH` : route §16.7 retirée au §19. |
| ClosureRoutes | 12 | RH-equivalence/conditional | ÉQUIVALENT-RH | RH ⟺ transports plats ⟺ croissance `x^{1/2+ε}` ; identités `W`, `D` fidèles. |
| CollectiveCurvature | 24 | mirror-pair | MIXTE | Courbure de paire fidèle ; observable fenêtrée `[a, a+L]` ; « les écarts imposent une amplitude constante » (non démontré). |
| CompensationRigidity | 11 | counting/background | À RECONTEXTUALISER | Lexique compensation/dette partout (nom du module, `compensation_closure_verdict`). Math : unicité spectrale, `θ* > 1/2`. |
| ConsecutiveChainContradiction | 5 | contact-reading | À RECONTEXTUALISER | Question « C_lecture » (contact de Tour atteint-il `p_min` ?) : lecture de contact caduque ; `hReaches` conditionnelle. |
| ConstantAmplitudeNeed | 11 | meeting-break | MIXTE | Contacts `C_k` appelés « points de rencontre » (§2) ; loi ⟺ RH ; « imposent » l.11. |
| ConstraintCorrelation | 18 | contact-reading | À RECONTEXTUALISER | « Lecture » d'un premier par `lastRayContact` (`pivot_reading_iff_residual`) ; dit « ne produit pas l'obligation ». |
| ConstraintPacket | 16 | RH-equivalence/conditional | ÉQUIVALENT-RH | `lineDeviation ≡ 0 ⟺ RH` ; « compensée » l.167. |
| ContactSensitivity | 17 | contact-reading | FIDÈLE | Taille du décalage ; contre-modèle `β = 1/4` ; « aucun énoncé ne fixe la position radiale ». |
| ContinuousProgression | 14 | contact-reading | FIDÈLE | `ΔΘ_n = T log(p_{n+1}/p_n)` aveugle à `β` ; `RH_FOUND=FALSE` consigné. |
| CountingDeficit | 45 | counting/background | FIDÈLE | `N = N₀ + 2W` ; `CountingExtension` nommée, ⟸ RH, non démontrée. |
| CountingFieldArchitecture | 30 | counting/background | FIDÈLE | Taxonomie C/D/Z : « les événements premiers ne sont dans aucune de ces familles » ; formule explicite `J` nommée. |
| CountingFieldContacts | 8 | contact-reading | FIDÈLE | `β`, `T`, `λ` restitués ; « lire ne fixe pas ». |
| CoupleLock | 16 | contact-reading | MIXTE | Contacts `C_k` = « rencontres » (§2) ; loi ⟺ RH ; « impose » l.38. |
| CriticalRemainderIntegration | 5 | RH-equivalence/conditional | ÉQUIVALENT-RH | `remainderExponent ≤ 1/2` paramètre explicite ⟹ RH. |
| DemandLevelPremise | 20 | RH-equivalence/conditional | MIXTE | `ExpectedFrequencyRises ⟺ DemandBoundedEverywhere ⟺ RH` ; « paie » l.21 ; demande bornée = lecture par borne. |
| DemonstrationChain | 40 | RH-equivalence/conditional | MIXTE | « marge admissible » l.290 ; « imposent » ×5 ; rencontre = `lineContact` l.646 ; prémisse `NoRadialShift` ⟺ RH. |
| DemonstrationWithoutRH | 11 | contact-reading | À RECONTEXTUALISER | `stop_event`, `reaches_*` : contact « atteint » `p_min`/`Occ` ; règle du pivot = lecture de contact. |
| DiagonalPassage | 16 | contact-reading | FIDÈLE | `contact = lineContact · λ` ; borne ⟺ arrivée en ligne, étiquetée. |
| DominantExponent | 7 | meeting-break | À RECONTEXTUALISER | Lexique « prix », « payer », « paie » ; demande bornée aux rencontres (hypothèse nommée). |
| DoubleRigidity | 10 | contact-reading | FIDÈLE | `M^Z = M`, écarts lus par la hauteur seule ; la paire témoin « sort » ; `no_sameHeight_iff_RH`. |
| EnergyIdentity | 4 | other | À RECONTEXTUALISER | « `V` ne compense pas `H` » l.81 ; `PVerticalDominatesAtRaccord` citée non compilée. |
| EngagedAllConstraints | 19 | contact-reading | ÉQUIVALENT-RH | `TowerSymmetric`, `PrisonAtInfinity`, `UnderLineScaleAtInfinity` ⟺ RH, « non dérivée ». |
| EngagedClosureVerdict | 8 | RH-equivalence/conditional | ÉQUIVALENT-RH | RH ⟺ conservation ∧ amorce ; témoin viole la loi. |
| EngagedNoTranslation | 17 | contact-reading | MIXTE | « enroulement imposé » (titre) ; enroulement à l'infini ⟺ RH ; emboîtement supposé §5. |
| EngagedPersistence | 4 | RH-equivalence/conditional | ÉQUIVALENT-RH | Loi `hOnly` hypothèse, ⟸ RH. |
| EngagedProgression | 6 | contact-reading | FIDÈLE | `EngagedState ⟺` ON ; `Δβ ≤ 0` seulement, dit. |
| EngagedRadialFloor | 7 | RH-equivalence/conditional | ÉQUIVALENT-RH | Plancher ⟺ « seule la hauteur évolue », ⟸ RH. |
| EntryPositionArrow | 7 | contact-reading | ÉQUIVALENT-RH | Flèche (position de Tour de `Occ(l)` = position de ligne) ⟺ conservation ; RH ⟺ flèche ∧ amorce. |
| EscapeFinancing | 9 | RH-equivalence/conditional | MIXTE | Lexique « financement », « se paie » ; `RemainderCaptive ⟺ RH`. |
| EulerMaclaurinFine | 11 | counting/background | FIDÈLE | Borne fine EM ; non-annulation certifiée. |
| EulerMaclaurinTenCertificate | 1 (+338 lemmes) | counting/background | FIDÈLE | Certificat numérique généré, `em10_fifteen_certificate`. |
| EventHeightProgression | 9 | RH-equivalence/conditional | ÉQUIVALENT-RH | Progression de `T` sur tout passage ⟺ RH ; honnête. |
| ExactAxisReading | 10 | contact-reading | FIDÈLE | Trois lectures d'un écart ; diagonale aveugle aux signes ; « aucune contrainte nouvelle ». |

## 2. Contacts identifiés à des premiers

**Égalité d'un contact/incidence avec un premier dans un ÉNONCÉ ou une hypothèse : aucun.** Le seul `=` liant une position de Tour et un
premier est `EntryPositionArrow:113` (`towerPosition l (occurrence l) = linePosition …`), égalité de deux POSITIONS d'un même premier,
pas d'un contact avec un premier.

Relations d'ORDRE contact–premier (encadrement, « atteindre »), à recontextualiser (le contact n'est pas l'événement premier) :
- CaptivityWithoutOn:38 `regime_captive_of_prime` — `entryContact < p_min ≤ lastRayContact`, docstring « captivité par le premier partagé ».
- ConsecutiveChainContradiction:96 `terminalCollision_conditional_on_reflectedObligation` — hypothèse `hReaches : p_min(z*) ≤ reflectedIncidence (j+1)` (conditionnelle, non prouvée, dit) ; :163 `secondTowerOwnContacts_meets_arithmeticChain` (`Occ(z*) < entryContact`, `lastRayContact < p_min`).
- ConstraintCorrelation:227 `pivot_reading_iff_residual` (`p ≤ lastRayContact` = « lecture ») ; :271 `passage_reading_excluded_of_residual_gap` ; :287 `expected_reading_excluded_of_magnitude_gap`.
- DemonstrationWithoutRH:53 `stop_event` (`IsLeast {k | p_min ≤ contactPlusAt z k}`) ; :60 `cell_contains_expected` ; :89 `reaches_expected` ; :94 `reaches_occurrence` (« l'occurrence est atteinte à l'état propre ») ; :107 `reached_progression` ; :115 `verification_passes`.
- EnergyIdentity:36 `geometry_selects_raccord_prime` — docstring « la cellule `(C⁻,C⁺]` … porte `q₁ = p_min(e) = Occ(l)` ».

Contacts appelés « rencontres / points de rencontre / points de passage obligés » (la doctrine réserve « rencontre » à `p_{n+1}`) :
- ConstantAmplitudeNeed:17–18 (en-tête « à deux rencontres consécutives (contacts) ») ; :76–77 `constantNeed_meeting_points` (« Points de rencontre consécutifs (contacts `C_k`, `C_{k+1}`) ») ; :87 `need_ratio_meeting_points`.
- CoupleLock:17 (en-tête « l'espacement des rencontres (… les contacts `C_k`) ») ; :49 `spacing_eq_pitch` ; :73 `radial_of_meeting_point` ; :79 `radial_of_need_ratio` ; :107 `shift_moves_meeting_points` ; :115 `need_change_moves_meeting_points` ; :186 `meeting_need_law_iff_riemannHypothesis`.
- DemonstrationChain:74–75, 80, 84–87 (en-tête : « rencontres aux positions de la ligne », « point de rencontre … à la position de la ligne ») ; :633–637, 646 (`ArithmeticMeeting T_w (lineContact T_w 0)`) ; :792 (`ExpectedFrequencyRises` : « points de rencontre obligés du signal suivant ⟹ espacement »).

Conforme à la doctrine (rencontre = premier) : CadenceStability:101 `exists_rank_of_prime` (« Tout premier est une rencontre »), `meetingPoint`.

## 3. Lexique à corriger

| module:ligne | phrase exacte |
|---|---|
| CadenceStability:7 | « la cadence imposée par la grammaire aux rencontres est une stabilité » |
| CadenceStability:20 | « Chaque paire de changements consécutifs paie un minimum fixe. » |
| CollectiveCurvature:16 | « les écarts exacts imposent une amplitude constante à chaque composante » |
| CompensationRigidity:10 | « croisés (renforcements et compensations) → dette d'un membre hors ligne » |
| CompensationRigidity:20–21 | « des contributions de même signe ne se compensent pas … la diagonale ne voit pas les compensations » |
| CompensationRigidity:26 | « la rigidité de compensation est l'unicité de la représentation spectrale » |
| CompensationRigidity:70 | « (renforcements et compensations) » |
| CompensationRigidity:94 | « **Compensation nette** ⟺ la diagonale dépasse le carré de la demande » |
| CompensationRigidity:100 | « Des contributions de même signe ne se compensent pas. » |
| CompensationRigidity:128,131 | « Verdict de la rigidité de compensation » ; nom `compensation_closure_verdict` |
| ConstantAmplitudeNeed:11 | « les écarts immuables des premiers imposent aux zéros fréquence et amplitude » |
| ConstraintPacket:167 | « ni remplacée par des membres en ligne, ni compensée par une déviation de leurs poids » |
| CoupleLock:38 | « ce que la courbe des premiers impose au signal placé à la hauteur du zéro suivant » |
| DemandLevelPremise:21 | « ce qu'une infinité de zéros à droite paie aux rencontres » |
| DemonstrationChain:69 | « amplitude imposée par la courbe des premiers à chaque signal » |
| DemonstrationChain:70 | « les écarts immuables des premiers imposent aux zéros leur fréquence et leur amplitude » |
| DemonstrationChain:84 | « la rencontre du signal engendré impose sa position radiale » |
| DemonstrationChain:290 | « identité exacte avec le groupe d'arrivée et marge admissible du complément » |
| DemonstrationChain:630 | « la courbe des premiers impose son amplitude à chaque signal (les écarts imposent, le signal subit) » |
| DemonstrationChain:653 | « la contrainte que les événements imposent simultanément aux rencontres propres et à leur résultante » |
| DominantExponent:6–7 | « (le prix d'un couple) … (ce que la ligne peut payer) » |
| DominantExponent:61 | « Le reste d'une famille paie au moins la famille moins la demande » |
| EnergyIdentity:81 | « À même hauteur, `V` ne compense pas `H > 0` » |
| EscapeFinancing:6–9 | « financement de l'évasion … ce que le reste exact peut financer » |
| EscapeFinancing:60 | « L'évasion se paie dans le reste exact » |

Cas limites (hors sens proscrit, signalés seulement) : AnchorStructure:14,15,42 (« l'unicité impose », miroir) ; AuthenticPassageProfile:20
(« le passage … impose ») ; CertifiedRemoval:7,75 (« marge » / `certifiedRemoved_within_margin`, déjà annoté « aucune tolérance », §19.21) ;
CanonicalTransition:23 (« marge de `1/(πT)` cellule », géométrique) ; ContinuousProgression:102 (« plancher … imposé par la discrétisation ») ;
EngagedNoTranslation:11,20 (« enroulement imposé »). Aucune occurrence de « fixe β » / « fixe la partie réelle » ; les modules écrivent au contraire « ne fixe pas ».

## 4. Hypothèses nommées ⟺ RH (ou impliquées par RH)

- AmplitudeStableSynchronization — `def AmplitudeStableSync p` : ⟺ `β_l = β_e` ; quantifiée sur les passages ON qui montent ⟺ RH (`amplitudeStable_law_iff_riemannHypothesis`).
- ArithmeticReading — hypothèse `∃ C, ‖smoothedRemainder x‖ ≤ C√x` ⟺ RH (`riemannHypothesis_iff_remainder_sqrt_growth`).
- ArrivalFiberHypotheses — H1 « grille d'arrivée = grille de ligne » ⟺ `β_l = 1/2` (`arrival_grid_unique_iff_onLine`).
- AstraSeparation — forme à même hauteur de la prémisse Astra, plancher `1/T² ≤ sep`, fermetures A∧B : ⟺ RH (`astra_sameHeight_premise_iff_riemannHypothesis`, `sep_floor_sameHeight_iff_riemannHypothesis`, `closures_A_B_iff_riemannHypothesis`).
- AuthenticPassageProfile — loi de conservation radiale `hLaw` : ⟸ RH (`conservation_of_riemannHypothesis`) ; ancre ∧ loi ⟹ RH.
- CanonicalTransition — `transition_conserves_iff_entry_position` : `β_l = 1/2` ⟺ entrée à la position de ligne (par membre).
- CascadeContinuation — condition réduite ⟺ continuation (`cascade_continuation_iff`) ; « quantifiée, force de RH ».
- ChangePredictor — `predictor_pair_iff_heightOnly` ; `changeResidue_vanishes_iff_remainder_sqrt_growth` (⟺ RH via ArithmeticReading).
- ChebyshevAsymptoticToLogGaps — `def ChebyshevAsymptotic` (PNT, vrai hors Lean) ; `DemandBoundedAtMeetings`, `SummitAttained` (importées) : `∧ ⟹ RH` ; `ExpectedFrequencyRises` en sort.
- ClosureRoutes — `riemannHypothesis_iff_remainder_growth_all_eps`, `riemannHypothesis_iff_mirror_transport_flat`, `riemannHypothesis_iff_all_transports_flat`.
- CollectiveCurvature — antécédent de `pair_curvature_closes` : « quantifié sur tous les zéros il a la force de RH » ; `hCollective`, `hRest` non démontrées.
- CompensationRigidity — `riemannHypothesis_iff_remainderExponent_eq_half` (cité en-tête).
- ConstantAmplitudeNeed — `def ConstantNeed z` ⟺ `β = 1/2` ; `∀ z, ConstantNeed z ⟺ RH` ; forme avec historique ⟺ RH.
- ConstraintPacket — `lineDeviation_vanishes_iff` ⟺ RH ; `riemannHypothesis_iff_remainder_eq_lineWhole`.
- CountingDeficit — `def CountingExtension H` : ⟸ RH (`extension_of_riemannHypothesis`) ; avec saturation ⟹ RH.
- CoupleLock — `meeting_need_law_iff_riemannHypothesis`.
- CriticalRemainderIntegration — `remainderExponent ≤ 1/2` ⟹ RH ; `off_pair_forces_strictly_supercritical` (réciproque).
- DemandLevelPremise — `def DemandBoundedAtMeetings` (⟸ RH), `def DemandBoundedEverywhere` (⟺ RH), `def RestNeverRight` (⟸ RH), `def MeetingsBridge` (⟸ RH), `def RestBoundedAtMeetings` ; `ExpectedFrequencyRises ⟺ DemandBoundedEverywhere ⟺ DemandBoundedAtMeetings ∧ RestNeverRight`.
- DemonstrationChain — `def ExpectedFrequencyRises` ⟺ RH (`expectedFrequencyRises_iff_riemannHypothesis`) ; prémisse `hRaccord`/`NoRadialShift` ⟺ RH (`mirror_domination_premise_iff_riemannHypothesis`) ; `radius_premise_iff_localRaccord_premise` (⟺ `β_l = 1/2` sur toute arrivée) ; `riemannHypothesis_terminal` conditionnel.
- DiagonalPassage — `vertical_exhausts_iff_arrival_onLine`, `contacts_height_determined_iff_onLine` (par membre).
- DominantExponent — `hdem` (demande bornée aux rencontres) : hypothèse nommée, ⟸ RH via DemandLevelPremise.
- DoubleRigidity — `no_sameHeight_iff_riemannHypothesis`.
- EngagedAllConstraints — `def TowerSymmetric` (⟺ ON) ; `def PrisonAtInfinity`, `def UnderLineScaleAtInfinity` : `∀` ⟺ RH (`prisonAtInfinity_iff_riemannHypothesis`, `underLineScale_iff_riemannHypothesis`, `towerSymmetric_all_iff_riemannHypothesis`).
- EngagedClosureVerdict — `riemannHypothesis_iff_conservation_and_base` ; `conservation_leaves_only_base`.
- EngagedNoTranslation — `def WindingNested` ; `winding_to_infinity_iff_riemannHypothesis` ; `conservation_iff_nested_and_noTranslation` ; `no_translation_iff_next_winds`.
- EngagedPersistence — `hOnly` (seule la hauteur évolue) ⟸ RH (`heightOnly_of_riemannHypothesis`).
- EngagedProgression — `structure EngagedState` ⟺ ON (`engagedState_iff_onLine`) ; point 9 : `β' = 1/2 ⟺ λ = 1 ⟺ fibre réduite ⟺ passage suivant vertical`.
- EngagedRadialFloor — plancher `hFloor` ⟺ `heightOnly` (`radial_floor_iff_heightOnly`), ⟸ RH ; `engaged_radial_floor_target_iff`.
- EntryPositionArrow — flèche ⟺ conservation (`entry_arrow_iff_upper_conservation`) ; RH ⟺ flèche ∧ amorce.
- EscapeFinancing — `def RemainderCaptive z` ⟺ RH (`remainderCaptive_iff_riemannHypothesis`).
- EventHeightProgression — progression de `T` sur tout passage ⟺ RH (`heightProgression_iff_riemannHypothesis`, en-tête) ; `grammarsAgree_iff_riemannHypothesis`.

Hypothèses nommées NON équivalentes à RH (pour mémoire) : CountingFieldArchitecture `def CountingExplicitFormula` (formule explicite de `J`, obligation de transport) ;
ContactSensitivity `def ReducedContactSystem` (contre-modèle, satisfait par `β = 1/4`) ; AnchorStructure `hU : ∃! w, T_w ≤ 15` (certification externe E185).

## 5. sorry / axiom / admit

Grep `\bsorry\b|\badmit\b|^axiom` hors lignes de commentaire, sur les 55 modules : **aucun**.
Seule occurrence textuelle hors commentaire : `DemonstrationChain:577` identifiant `hContactsAdmit` (nom de variable, pas une tactique).
Les autres occurrences (AnchorContour, AnchorStructure, ArithmeticReading, AstraSeparation ×6, CadenceStability, CanonicalTransition,
CaptivityWithoutOn, CellRestitution ×2, ChangePredictor, Chebyshev…, ClosureRoutes, CompensationRigidity, ConsecutiveChain…, ConstraintPacket,
ContinuousProgression, CountingDeficit, DemandLevelPremise, DemonstrationChain ×3, DemonstrationWithoutRH, DiagonalPassage, DominantExponent,
DoubleRigidity, EngagedClosureVerdict, EngagedNoTranslation, EngagedPersistence, EngagedProgression, EngagedRadialFloor, EntryPositionArrow,
EscapeFinancing, ExactAxisReading) sont des mentions « Aucun `sorry` » ou historiques (« `sorry` en phase 3 », `sorryAx` RHV4) dans les docstrings.
Note : `DemonstrationChain` déclare ses buts ouverts comme « véritables buts non fermés » (chaîne rouge), sans `sorry`.

## 6. Décompte final

Modules FIDÈLE 25 / À RECONTEXTUALISER 9 / ÉQUIVALENT-RH 14 / PARTIEL 0 / MIXTE 7 (total 55).

### Annexe B — groupe 2 (modules E–L)
# Audit des énoncés — groupe 2 (ExactMeetingAudit … LocalFourSectors)

Base : `/opt/zeta24-lean/formalization/RHV6Fresh/RHV6Fresh/Terminal/<module>.lean`. Lecture des docstrings de tête et des
énoncés (`theorem`/`lemma`/`def`), jamais des preuves. Doctrine de référence : réorientation de l'auteur du 2026-11-01
(contacts de Tour ≠ premiers ; contribution exacte par écart ; point de rencontre `meetingPoint I = p_{n+1}` ; cassure
`log p_{n+1}` réalisée par la totalité ; lexique « identité du complément »).

## 1. Tableau par module

| module | nb théorèmes | classe d'objet | verdict | notes |
|---|---|---|---|---|
| ExactMeetingAudit | 18 | meeting-break | FIDÈLE | Porteur OFF, `meetingPoint C.gap = p_{n+1}`, B3/B4/B5 étiquetés ⟺ RH, B8 identité du complément. |
| ExactSignalArchitecture | 41 | other | FIDÈLE | Signal exact `x^ρ/ρ` ; contacts = phases, « aucune identité n'impose β = 1/2 ». |
| ExpectedObserved | 3 | contact-reading | À RECONTEXTUALISER | Compte les premiers « jusqu'au contact » (`primeCountAtStateUpper`) : lecture des premiers par un contact. |
| ExplicitFormulaLink | 28 | contact-reading | FIDÈLE | Rayons `C_k` = points réels du terme ; « la formule ne contraint que la somme ». |
| FiniteGrammarLayer | 11 | finite-window | PARTIEL | Séparation « écart imposé > compensation maximale » : antécédent non dérivé ; lexique. |
| FiniteRadialRigidity | 9 | other | FIDÈLE | Outil analytique fini, conditionnel à une borne non acquise (dit explicitement). |
| FirstArrivalsAnchor | 16 | counting/background | FIDÈLE | Comptages certifiés ; `first_rupture_forbidden_iff` ⟺ RH étiqueté ; lexique L210. |
| FirstExceedanceRaccord | 23 | contact-reading | ÉQUIVALENT-RH | `LocalRaccord` (contact miroir = contact de ligne) ⟺ β_l = 1/2 ; ferme le cas bas sous cette hypothèse. |
| FirstGainPremise | 227 | other | MIXTE | Prémisse de gain sur support fini ; fermetures ⟺ RH étiquetées ; lexique compensation/coût/prix abondant. |
| FirstThreeZerosCertified | 7 | counting/background | FIDÈLE | Certificats N(22)=2, N(28)=3, hors chaîne. |
| FirstTowerHorizon | 14 | other | À RECONTEXTUALISER | Lecture asymptotique globale (`must_be_financed`, « coût de sortie ») ; horizon ≠ objet local. |
| FirstZeroContactComparison | 28 | contact-reading | FIDÈLE | Ordre des contacts ne borne pas λ ; contacts d'indice < 0 « aucun premier ». |
| FirstZeroDominance | 17 | RH-equivalence/conditional | ÉQUIVALENT-RH | `DominanceStage z w ⟺ β_w = 1/2` ; étage caractérise ON, ne le produit pas (dit). |
| FirstZeroField | 8 | RH-equivalence/conditional | ÉQUIVALENT-RH | `InsideField` pour tous ⟺ RH (`first_field_iff_riemannHypothesis`). |
| FixedExponentField | 11 | RH-equivalence/conditional | ÉQUIVALENT-RH | `TowerPrisoner` pour tous ⟺ RH ; hauteur qui avance partout ⟹ RH. |
| FixedGapRaccords | 16 | gap-contribution | FIDÈLE | `primeGapContribution` identifie le point, ne contraint pas β ; `NoMixedHeight` nommée, impliquée par RH. |
| FrequencyCap | 16 | counting/background | FIDÈLE | Caps RvM inconditionnels, radialement aveugles (dit). |
| FrequencyCascadeStability | 10 | RH-equivalence/conditional | ÉQUIVALENT-RH | Cascade stricte à tout rang ⟺ RH ; non-décroissance et rupture par miroir démontrées. |
| GapDemandStability | 35 | gap-contribution | MIXTE | `gapDemand_eq_sum` fidèle ; lois de stabilité ⟺ ON/RH ; lexique « contribution imposée ». |
| GapSynchronization | 13 | gap-contribution | FIDÈLE | `gapTerm`, loi de synchronisation par écart sur TOUS les zéros ; « ne fixe pas β ». |
| GapTranslationInvariance | 22 | finite-window | ÉQUIVALENT-RH | `GrammaticalRadialInvariance z ⟺ β = 1/2` ; quantifiée ⟺ RH ; fenêtres translatées. |
| GeneratedFrequency | 96 | contact-reading | MIXTE | `meetingOf` = contact `C_0` nommé « rencontre » ; « la rencontre impose β » ; compensation ; plusieurs ⟺ RH. |
| GeometricEnergyRaccord | 8 | contact-reading | FIDÈLE | Dit explicitement : le premier n'est jamais un contact, il est encadré par `C⁻ < q ≤ C⁺`. |
| GlobalGapSignature | 16 | gap-contribution | FIDÈLE | Variation sur écart, télescopage, « ne contraint pas β ». |
| GlobalRigidSystem | 3 | other | FIDÈLE | Système sans hypothèse ; OFF conserve les trois égalités. |
| GrammarDrift | 11 | meeting-break | FIDÈLE | `meetingPoint ⟨n⟩` = premier ; dérive entre rencontres ; lexique « impose ». |
| GrammarDwellDecomposition | 19 | counting/background | FIDÈLE | Identités combinatoires mod 6 ; « compensation » au sens comptage. |
| GrammarForcesStop | 2 | RH-equivalence/conditional | FIDÈLE | Dit que la grammaire par hauteur EST RH ; rang seul n'exige aucune amplitude. |
| GrammarKinematics | 42 | other | FIDÈLE | Registre au premier partagé ; β intérieur disparaît ; lexique « rembourse », « imposée ». |
| GrammarOperator | 23 | finite-window | PARTIEL | `B_G(D_G)` et borne du complément = hypothèses explicites non démontrées. |
| GrammarTailBound | 15 | finite-window | PARTIEL | Borne uniforme de la queue ⟺ « tout zéro au-dessus de H en ligne » ; non dérivée (dit). |
| GrammarTransportLaw | 39 | contact-reading | ÉQUIVALENT-RH | `GrammarTransportAtEvent`, `NoRadiusDrift`, `NoRadialShift` ⟺ β_l = 1/2 ; contacts nommés « rencontres ». |
| GrammarWeightedG4 | 11 | other | FIDÈLE | Théorème indépendant (poids réels), aucun zéro. |
| GrammarWindowEstimate | 36 | finite-window | PARTIEL | `passage_window_reduction` : antécédent (estimations) non démontré ; « marge ». |
| GrammarWindowSeparation | 27 | finite-window | PARTIEL | Titre « Compensation sur une fenêtre » ; condition suffisante non démontrée (dit). |
| GrammarWordLoad | 9 | other | FIDÈLE | Identités mod 6 ; lexique « dette miroir ». |
| GrammaticalRaccordJump | 13 | meeting-break | FIDÈLE | Saut collectif `Λ(p)=log p` par TOUS les zéros ; complément = identité ; contact=ligne ⟺ ON (caractérisation). |
| HarmonicCrossCurrent | 15 | other | FIDÈLE | Identités de courant ; « aucune n'impose d = 0 ». |
| HarmonicCurrentTransport | 18 | other | FIDÈLE | Caractérisations ; contre-modèle A. |
| HarmonicRestoringLaw | 23 | other | FIDÈLE | ODE harmonique ; énergie détecte, n'interdit pas. |
| HeightPacket | 21 | gap-contribution | À RECONTEXTUALISER | Identité du complément correcte (§19.21) mais docstrings/defs gardent « compensation forcée ». |
| HorizontalExclusion | 12 | mirror-pair | FIDÈLE | Contacts miroir jamais égaux ; passage horizontal partage un premier, jamais un contact ; ⟺ RH étiqueté. |
| IncrementMatrix | 6 | finite-window | FIDÈLE | Télescopages ; inégalités triangulaires (« indices de compensation » = lexique). |
| IndependentContactComparison | 2 | contact-reading | À RECONTEXTUALISER | Compare `expectedMinimumPrime` à un « readout » de contact ; docstring anglais, lecture premier↔contact. |
| InsertionExclusion | 36 | other | FIDÈLE | Unicité de la limite ; aveugle à β (dit) ; borne √x log x conditionnelle étiquetée. |
| InterTowerExcess | 8 | RH-equivalence/conditional | FIDÈLE | `J(p) > 0 ⟺ T_e < T_l` ; header cite des `…_iff_riemannHypothesis` absents du fichier. |
| InterlacingLink | 12 | contact-reading | FIDÈLE | Décalages d'entrelacement, identités ; « ne fixe pas la position radiale » ; lexique « imposé ». |
| InversePrimeSpectral | 9 | counting/background | FIDÈLE | Impulsions → normalisation exacte ; dernier maillon ⟺ RH étiqueté caractérisation. |
| InverseReading | 15 | meeting-break | FIDÈLE | `ΔR(a,b)` entre événements premiers ; `complementBetween_forced` identité. |
| JointComparison | 7 | finite-window | PARTIEL | Fermeture sous comparaison stricte non démontrée ; « compensation maximale du complément ». |
| JointParameterReading | 38 | contact-reading | FIDÈLE | « Aucun premier n'entre dans le producteur de contacts » ; enroulement entier ⟺ RH étiqueté. |
| JointSignatureHorizon | 13 | RH-equivalence/conditional | FIDÈLE | Reclassé honnêtement : identifiabilité conditionnelle, OFF ⟹ croissance, pas d'exclusion. |
| LineCountingDefect | 25 | counting/background | FIDÈLE | Défaut `δ = 2ΔW` ; défaut nul ⟺ ON sous `W(T)=0` (caractérisation). |
| LinkedProduction | 2 | other | À RECONTEXTUALISER | Header : « position radiale fixée par le côté arithmétique seul » alors que le théorème est un ⟺. |
| LocalFourSectors | 5 | mirror-pair | FIDÈLE | Symétrie à quatre secteurs ; « ne sélectionne pas l'axe ». |

## 2. Contacts identifiés à des premiers

Énoncés dont l'ÉNONCÉ ou une hypothèse pose `contactMinusAt/contactPlusAt/incidence/towerPosition = premier`, ou dont
la docstring dit qu'un contact « est »/« tombe sur » un premier : **aucun**.

Les énoncés suivants mettent un contact et un premier dans la même relation, mais par encadrement, évaluation ou
comparaison, jamais par identification (à conserver tels quels, avec la lecture doctrinale « contact = passage de phase ») :
- GeometricEnergyRaccord:40 `prime_raccord_has_unique_tower_cell` : `C⁻ < q ≤ C⁺` (encadrement ; docstring explicite : le premier « n'est en général PAS un rayon »).
- GrammarTransportLaw:86 `event_in_own_cell`, :53 `stageChangePrime` (premier premier au-delà du contact), :151 `GrammarTransport` (R) encadrement.
- FirstExceedanceRaccord:199 `LocalRaccord` : contact miroir à l'étage de `firstExceedPrime` = contact de ligne (contact = contact, indexé par un premier).
- ExpectedObserved:36 `lastPrimeAtStateUpper_le_contact` : dernier premier ≤ contact (borne).
- IndependentContactComparison:16,35 : `expectedMinimumPrime` comparé au « readout » de contact (borne).
- InterTowerExcess:41 : `towerPosition z (fnPrimeSuccessor k)` (évaluation de la position de Tour au premier).
- GrammarKinematics:64 `occurrencePosition` : `T·log(Occ) − φ` (position d'un premier dans la Tour).
- InterlacingLink:139 `next_contribution_at_shared_prime` : contribution évaluée au premier partagé, lue sur les contacts.

Contacts NOMMÉS « rencontre » (conflit de vocabulaire avec `meetingPoint I = p_{n+1}`, à distinguer) :
- GeneratedFrequency:127 `meetingOf` (« point de rencontre d'un signal » = `contactMinusAt z 0`, :303 `contactMinusAt_eq_meetingOf`), :150 `ArithmeticMeeting`, :165 `MeetingOnLine`, :610–620 `verticalMeetingShift`/`radialMeetingShift`, :1261 `smoothedMeeting` (« rencontres lissées »), :1275 `smoothedMeeting_eq_contact`.
- GrammarTransportLaw:36 `meetingExponent` (exposant du contact k), :18/:150 « rencontres authentiques » = contacts, :378/:393/:415 « rencontre propre d'indice k ».
- FirstExceedanceRaccord:827–837 « contacts authentiques qui encadrent le premier » (vocabulaire correct), mais `LocalRaccord` est présenté comme « obligation de raccord ».

## 3. Lexique à corriger

Format `module:ligne — phrase`. (Noms d'objets doctrinaux `imposedShare`, et négations « n'impose pas » exclus.)

Compensation / payer / prix / coût / dette / marge :
- FiniteGrammarLayer:23 « écart imposé par une rupture > compensation maximale démontrée du complément » ; :60 « Compensation maximale démontrée du complément sur une fenêtre » ; :159 même phrase (théorème `separation_excludes_profile`) ; :19,116,132 « écart (de réponse) imposé par une rupture ».
- FirstArrivalsAnchor:210 « aucune compensation n'est possible sur le champ complet ».
- FirstGainPremise:1542 « cible d'interdiction de compensation » ; :1560–1561 (`compensation_bound_incompatible`, `compensation_target_iff_ownEnergy_le`) ; :1654,1667,1680 « interdiction de compensation » ; :1689 « La marge de la prémisse, décomposée » ; :1959 « ne reste masquée … qu'au prix d'une interaction » ; :1957,2005,2012 « Coût d'un masquage » ; :2278,2304–2310 « compensation nécessaire contre majoration acquise » ; :2488 « Masquage ⟺ compensation nécessaire » ; :2496 « Compensation nécessaire ≤ majoration acquise » ; :2829 « la compensation nécessaire ne dépasse pas la majoration acquise ».
- FirstTowerHorizon:30,194 `upper_member_gain_must_be_financed` (« financé ») ; :38–40 « `financing_ledger` », « coût de sortie contre disponible » ; :191 « le coût de sortie ».
- FirstThreeZerosCertified:86 « une rupture coûte deux unités de comptage ».
- GapDemandStability:3322 (header) `mirror_word_energy_debt` (« dette »).
- GeneratedFrequency:585 « Loi de compensation entre déplacement vertical et déplacement radial » ; :589 « ces deux déplacements ne peuvent pas se compenser » ; :598–606 « COMPENSATION DE LA RENCONTRE DU DÉPART … la part radiale compense exactement la part verticale » ; :719–721 `meeting_compensation_iff` ; :734–736 `meeting_compensation_requires_low` ; :753 `meeting_compensation_realizable` ; :787 `exists_compensating_frequency` ; :811 « écrit dans le vocabulaire de la compensation » ; :826–828 `compensation_law_closes` ; :878 « Non-compensation et amplitude imposée ».
- GrammarDwellDecomposition:17,108 « quasi-compensation des séjours » (sens combinatoire, bénin mais à renommer « solde »).
- GrammarKinematics:617 « elle rembourse le déficit de la première ».
- GrammarWindowEstimate:23,163 « marge triangulaire … non imposée » ; :381 « toutes les compensations conservées ».
- GrammarWindowSeparation:5 titre « Compensation sur une fenêtre grammaticale authentique » ; :6109 (L338) « la marge triangulaire du complément ».
- GrammarWordLoad:6,18,23,80,82,90,106 « dette miroir » (`mirror_word_energy_debt`, `alternating_two_step_mirror_debt`, `mirror_word_debt_pos_iff`).
- GrammaticalRaccordJump:111 « Identité (compensation au niveau de l'événement) ».
- HeightPacket:4 titre « paquet de hauteur et compensation forcée » ; :15 « `compensation` (nom conservé) » ; :22 `off_forced_compensation` ; :135 « § 3 … la compensation forcée » ; :156 « La compensation est fournie exactement par le complément » ; :163 « La compensation est réalisée pour tout x > 1 » ; :171 « la différence des compensations » ; :187 « La compensation forcée sur l'incrément » (`eventCompensation`) ; :215 « La compensation de l'événement est fournie exactement par le complément » ; :272–276 « Compensation forcée par un zéro hors ligne … la compensation de cet incrément ».
- IncrementMatrix:12,14,53 « Indices de compensation » (`incrementMatrix_compensation`).
- JointComparison:17 « la compensation maximale du complément ».

« Impose / fixe » (un écart, une rencontre ou une lecture imposant/fixant β ou un membre) :
- GapDemandStability:37,191,193 « contribution imposée (`R − part fixe des autres`) … `ImposedScaleStable` » ; :243,377,389 « échelle imposée stable » (à écrire « identité du complément »).
- GapSynchronization:17 « L'amplitude commune de la structure imposée ».
- GeneratedFrequency:175 « Rigidités renversées : la rencontre impose la position radiale » ; :177 « la position de la rencontre d'un signal engendré impose sa position radiale » (`radial_from_meeting`) ; :183 « le rapport des besoins … impose la position radiale » (`radial_from_need_ratio`) ; :878–884,891,907,950–954 « contribution (d'un vrai zéro) imposée », « la présence et l'unicité sont imposées » ; :1081,1086–1093,1249 « contribution conjointe imposée », `ImposedNotFasterAtGap`, `ImposedOnScaleAtGap` (:1394–1402).
- GlobalRigidSystem:30 « toutes les couches imposées au même ensemble de zéros ».
- GrammarDrift:5 « La grammaire des écarts impose la dérive de l'amplitude aux rencontres » ; :9 « Ce que la grammaire IMPOSE aux rencontres » ; :195 « la dérive imposée par deux changements obligés ».
- GrammarKinematics:141 « la progression imposée par la grammaire » ; :416 « l'événement imposé est le même ».
- GrammarTransportLaw:12 « le besoin d'amplitude imposé par les deux cellules successives » ; :20 « celui qu'impose l'échelle commune ».
- InterlacingLink:15,70 « signe imposé » ; :19,109 « Liaison imposée au premier contact ».
- JointParameterReading:585 « cette identité impose, à chaque zéro, la non-croissance de son amplitude ».
- JointSignatureHorizon:84 « Une signature OFF SUPPOSÉE impose au signal … de dépasser ».
- LinkedProduction:21–22 (header) « la position radiale du membre d'arrivée n'est pas un degré de liberté. Elle est fixée par le côté arithmétique seul ».
- FirstGainPremise:2091–2099 « un maintien impose `g_r ≥ 6` … variation OBLIGATOIRE … imposée par la grammaire » (plancher grammatical ; sens non radial, à reformuler « minore »).

Aucune occurrence de « marge admissible » ni de « fixe β / fixe la partie réelle » affirmative (toutes les occurrences de « fixe » sont des négations : « ne fixe pas β »).

## 4. Hypothèses nommées ⟺ RH (ou impliquées par RH)

Définitions `… : Prop` et hypothèses de théorèmes déclarées équivalentes à RH, ou à `β = 1/2` pour un zéro (donc ⟺ RH une fois quantifiées), ou impliquées par RH, d'après leur propre docstring :
- ExactMeetingAudit:85 `(∀ _ : OffCarrier, False) ↔ RiemannHypothesis` ; :98 `ConstantRelativeAmplitudeAtMeetings` (∀ ⟺ RH) ; :109 `ConstantNeed` (∀ ⟺ RH) ; :132 `DemandBoundedAtMeetings ∧ RestNeverRight ↔ RiemannHypothesis` ; :143 hypothèses `hdem`, `hrest` (`RestNotRight`).
- FirstArrivalsAnchor:190 `first_rupture_forbidden_iff` (`∀ w, ¬β_w < 1/2 ↔ RH`).
- FirstExceedanceRaccord:199 `def LocalRaccord` ⟺ `β_l = 1/2` (:204) ; :227 impliquée par RH ; hypothèse `hR` de :212,:219.
- FirstGainPremise:1300 `InsideField` ⟺ domination d'amplitude ; :1326 `individual_domination_iff_riemannHypothesis` ; :1529 `hLink` (raccord, non dérivé) ; :1575 `hAllOn` = RH ; :1745/:1760 captivité ⟹ RH ; :2728 `no_upper_canonical_iff_riemannHypothesis` ; :2787 `gain_upper_of_riemannHypothesis` (prémisse au miroir impliquée par RH) ; :2795 `hLinkUp`.
- FirstZeroDominance:34 `structure DominanceStage` ⟺ `β_w = 1/2` (:65,:121).
- FirstZeroField:41 `def InsideField` ; :120 `(∀ w, InsideField z₁ w) ↔ RH`.
- FixedExponentField:129 `def TowerPrisoner` ; :172 `prison_iff_riemannHypothesis` ; :70 `hSame` (même β pour tous) ⟹ RH ; :151 `hV` (hauteur avance partout) ⟹ RH.
- FixedGapRaccords:261 `def NoMixedHeight` (impliquée par RH, :266) ; :239 `prime_gaps_line_reading_iff` ⟺ ON par zéro.
- FrequencyCascadeStability:60 cascade stricte à tout rang ⟺ RH ; :142 `hOn` (tous ON) = RH.
- GapDemandStability:155 `def WindowStable` ⟺ ON ; :165 `def DemandTransported` ⟺ même β ; :193 `def ImposedScaleStable` ⟺ ON ; :354–389 lois quantifiées ⟺ RH (sous ancre).
- GapTranslationInvariance:230 `def GrammaticalRadialInvariance` ⟺ ON (:236) ; :263 ∀ ⟺ RH ; :246,:254 hypothèses d'invariance sur une fenêtre.
- GeneratedFrequency:165 `def MeetingOnLine` (« PROPRIÉTÉ À ÉTABLIR ») ; :169 `SingleSignal` ; :173 `def NoMeetingBelow` ⟺ RH (:274) ; :145/150 `ArithmeticFrequency`/`ArithmeticMeeting` : loi ⟺ RH (:384) ; :835 `radialMeetingShift = 0` ∀ ⟺ RH ; :1396 `ImposedNotFasterAtGap` ⟺ `β ≤ 1/2`, :1402 `ImposedOnScaleAtGap` ⟺ ON, :1437 ∀ ⟺ RH ; :828 `hDecr` (amplitude strictement décroissante) = cas bas.
- GrammarForcesStop:20–27 (header) grammaire par hauteur ⟺ RH (`grammarsAgree_iff_riemannHypothesis`, module externe).
- GrammarOperator:289 `hCollective` (`B_G(D_G)`) et borne du complément : non démontrées, non caractérisées.
- GrammarTailBound:87 `tailSignal_bounded_iff` ⟺ « tout zéro au-dessus de H en ligne » ; :75,:108,:146,:202 hypothèses `hOn` de cette forme.
- GrammarTransportLaw:151 `def GrammarTransport` ⟺ même cellule ∨ β = 1/2 ; :193 `def GrammarTransportAtEvent` ⟺ β_l = 1/2 (:197), impliquée par RH (:219) ; :294 `def GrammarTransportNested` ⟺ (:299) ; :326 `def NoRadiusDrift` ⟺ (:330), par RH (:352) ; :380 `def NoRadialShift` ⟺ (:402), par RH (:429).
- GrammaticalRaccordJump:175 `contact_eq_line_iff_onLine` (caractérisation par zéro).
- HarmonicCurrentTransport:167,:185 ⟺ `radialFactor l = 1` ; HarmonicRestoringLaw:205,:235 ⟺ `radialFactor z = 1` ; HarmonicCrossCurrent:161 ⟺ même partie réelle ; ExactSignalArchitecture:269 ⟺ `radialFactor l = 1`.
- HorizontalExclusion:59 `def HorizontalMirrorRealization` ; exclusion totale ⟺ RH (H2, header :13–15) ; :125 `mirror_contact_eq_iff_onLine`.
- InterTowerExcess:113 `J(p) > 0 ⟺ T_e < T_l` (= `PHeightProgression` ⟺ RH, header).
- InversePrimeSpectral:189 `def IndividualAmplitudeRigidity` ⟺ ON (:194) ; :206 ∀ ⟺ RH.
- JointParameterReading:527,:556 hypothèse d'enroulement entier (⟺ RH, :575) ; :596 non-croissance aux contacts propres pour tous ⟹ RH.
- JointSignatureHorizon:150 exclusion de toute signature OFF ⟺ `remainderExponent = 1/2`.
- LineCountingDefect:89 `lineDefect_zero_iff_onLine` (sous `W(T)=0`) ; :346 `passage_lineDefect_zero_iff`.
- LinkedProduction:39 `vertical_arrival_written_in_arithmetic` ⟺ (par passage).
- ExpectedObserved, ExplicitFormulaLink, FiniteGrammarLayer, FiniteRadialRigidity, FirstThreeZerosCertified, FirstTowerHorizon, FirstZeroContactComparison, FrequencyCap, GapSynchronization, GeometricEnergyRaccord, GlobalGapSignature, GlobalRigidSystem, GrammarDrift, GrammarDwellDecomposition, GrammarKinematics, GrammarWeightedG4, GrammarWindowEstimate, GrammarWindowSeparation, GrammarWordLoad, HeightPacket, IncrementMatrix, IndependentContactComparison, InsertionExclusion, InterlacingLink, InverseReading, JointComparison, LocalFourSectors : aucune.

## 5. sorry / admit / axiom

`grep -n "sorry\|admit\|^axiom"` hors lignes de commentaire, par module : **aucun** pour les 55 modules.
Seules occurrences : docstrings de tête (« Aucun `sorry`, aucun `admit`, aucun axiome ») et deux noms de théorèmes
contenant la chaîne « admit » : GrammaticalRaccordJump:189 `grammar_contacts_admit_any_radial`,
JointSignatureHorizon:156 `acquired_exponent_admits_any_off_signature`. Aucune déclaration `axiom`.

## 6. Décompte final

FIDÈLE 34 / À RECONTEXTUALISER 5 / ÉQUIVALENT-RH 7 / PARTIEL 6 / MIXTE 3 (total 55).

### Annexe C — groupe 3 (modules L–R)
# Audit des énoncés Lean — groupe 3 (55 modules, `RHV6Fresh/Terminal/`)

Doctrine de référence : réorientation de l'auteur du 2026-11-01 (Tour / contacts ≠ premiers ; contribution exacte par écart ;
point de rencontre `p_{n+1}` réalisé par la totalité ; lexique « compensation / payer / prix / marge admissible / impose /
fixe β » proscrit ; aucune hypothèse ⟺ RH présentée comme acquise). Lecture limitée aux en-têtes `/-! … -/`, aux docstrings
et aux signatures (`theorem`/`lemma`/`def`), jamais aux preuves. Comptes de théorèmes = `grep -c '^theorem\|^lemma'`.

## 1. Tableau par module

| module | nb theorems | object class | verdict | notes |
|---|---|---|---|---|
| LocalGlobalGapMatrix | 19 | gap-contribution | FIDÈLE | Identités matrice écart/zéro, télescopage ; « aucune contrainte sur β » explicite. « se compensent » (facteurs numériques). |
| LocalPrimeGapSynchronization | 43 | gap-contribution | MIXTE | §1–4 fidèles (`localSynchronization`, rigidité, `contact_vs_densitySignChange` distingue contact/densité) ; §5 `LocalOnScale` ⟺ β=1/2, loi ⟺ RH, déclaré. |
| LocalRaccordCaptivity | 15 | other | À RECONTEXTUALISER | Lexique budget/coût de sortie/disponible ; `sameHeight_capture_target_iff` ⟺ aucun passage horizontal. Objets Tour au premier du raccord, sans identification. |
| LocalReading | 2 | other | FIDÈLE | Deux faits de mode A/C ; prémisse locale retirée (≈ RH), documentée dans l'en-tête. |
| LocalWindowTransmission | 11 | finite-window | À RECONTEXTUALISER | Fenêtre finie de contacts acquis, « marge admissible » ×6, « compensation admissible » ; `windowMargin` déjà re-docstringé §19.21 mais pas le reste. |
| LogGapsTheorem | 7 | RH-equivalence/conditional | MIXTE | 3 théorèmes (PNT porté) ; 4 conditionnels à `DemandBoundedAtMeetings`/`SummitAttained` (route clôture/sommet retirée §19). |
| LowNextZeroSignatures | 7 | counting/background | FIDÈLE | Signatures comptage/amplitude d'un zéro bas ; « aucune n'exclut » ; titre « ce qu'il impose » (sens : zéro → ses paramètres). |
| MeetingExactness | 22 | meeting-break | FIDÈLE | Cœur doctrinal : état fixé par rencontre précédente, non-dérivabilité au premier, `no_finite_family_accomplishes_demand`, `exactness_is_a_demand`. |
| MeetingPoint | 44 | meeting-break | MIXTE | §2–3 fidèles (`meetingPoint`, `imposedShare`, `all_signals_meet`) ; §4 prémisse `ExpectedFrequencyRisesAtMeetings` ⟹ RH ; §9 `ConstantRelativeAmplitudeAtMeetings` ⟺ β=1/2 (relation ⟺ RH). |
| MeetingSampling | 7 | RH-equivalence/conditional | À RECONTEXTUALISER | Conditionnel à `MeetingsSampleFrequencies` (devenue théorème) + demande bornée ; en-tête « le prix … payé … ce que paie ». |
| MeetingsBridge | 13 | RH-equivalence/conditional | ÉQUIVALENT-RH | Pont demande bornée aux rencontres + `GapsRootOrder` ⟹ RH ; hypothèses nommées, jamais posées ; route §16.7 retirée. |
| MirrorAntisymmetry | 11 | mirror-pair | FIDÈLE | Canal antisymétrique de Tour vs canal collectif symétrique ; borne honnête. |
| MirrorDegeneracy | 17 | contact-reading | FIDÈLE | Géométrie des contacts du miroir (translation rigide, TFAE β=1/2) ; « exclu ssi RH » dit. Contacts jamais identifiés à des premiers. |
| MirrorEventCollision | 12 | mirror-pair | FIDÈLE | Occurrence/événement de hauteur du miroir ; cible C réfutée ; aucune contradiction affirmée. |
| MirrorFrequency | 11 | mirror-pair | FIDÈLE | Miroir = second état de même fréquence ; `towerPosition` lu aux premiers (lecture, pas identité) ; honnêteté sur `n(z*)=n(z)+1`. |
| MirrorGroupNonCompensation | 11 | finite-window | À RECONTEXTUALISER | Groupe fini `]H,H'']`, « non-compensation », « reste à consommer » ; hypothèse de fermeture = borne du reste θ<1−β (bande sans zéro). |
| MirrorLoop | 20 | mirror-pair | FIDÈLE | Trajectoire d'une Tour, boucle miroir, étalon ; identités pour toute famille stable. |
| MirrorPairExactSum | 9 | mirror-pair | À RECONTEXTUALISER | Identités exactes fidèles ; lexique « compensation » dans 2 noms de théorèmes et 3 docstrings. |
| NoRegimeChange | 22 | RH-equivalence/conditional | ÉQUIVALENT-RH | `PNoRegimeChange ↔ RiemannHypothesis` déclaré ; §1 théorème `exists_verticalPassage` indépendant. |
| OccupiedFrequency | 13 | contact-reading | À RECONTEXTUALISER | Contacts appelés « points de rencontre », « points de passage obligés » imposés par les écarts ; « fixe β » ; lois ⟺ RH déclarées. |
| OccurrenceHeightComposition | 18 | RH-equivalence/conditional | MIXTE | Cible « occurrences distinctes ⟹ hauteurs distinctes » ⟺ RH déclarée ; §3–5 faits du porteur fidèles. |
| OffAmplificationAudit | 39 | RH-equivalence/conditional | MIXTE | Certificats compilés fidèles ; domination/InsideField ⟺ RH déclarés ; lexique « (non-)compensation » ×5. |
| OffCarrier | 124 | meeting-break | FIDÈLE | Module doctrinal (liaison, cassure, `ContinuationForced` nommée). Renommer `break_compensated_by_other_frequencies` (docstring déjà rectifiée §19.21). |
| OnCrossReadings | 38 | contact-reading | À RECONTEXTUALISER | Lectures croisées rayons/contacts fidèles ; « ce que l'événement supplémentaire impose à la Tour suivante » (événement → Tour) ×2. |
| OnLineBetaEqPrevious | 18 | RH-equivalence/conditional | ÉQUIVALENT-RH | Théorèmes principaux conditionnels à `hDom` (domination individuelle, « ferme RH ») ; « ne se compensent jamais », « compensation exacte ». |
| OnRadialRing | 13 | other | FIDÈLE | Anneau radial ON seulement ; « rien ne démontre qu'un zéro suivant est en ligne ». |
| OnRegimeInduction | 18 | counting/background | MIXTE | Parité des fibres, déficit (fidèle) ; invariant `ΔD=0` quantifié ⟺ RH déclaré. |
| OnRegimeStabilityPackage | 6 | other | FIDÈLE | Consolidation ; profil d'une rupture « démontré, aucune ligne n'est une contradiction ». |
| OneZeroOnePrime | 6 | contact-reading | FIDÈLE | « la Tour ne sélectionne aucun premier » ; occurrence = étiquette de rang ; tout premier dans une cellule. |
| OscillationResultant | 23 | counting/background | FIDÈLE | Résultante, identités ; « compensation interfréquences » (ligne 262, sens algébrique). |
| PairCurvature | 17 | mirror-pair | FIDÈLE | Courbure radiale, horizon fini explicitement « n'exclut rien ». |
| PairInteraction | 12 | mirror-pair | FIDÈLE | Interaction paire/Tours engagées, identités, aucune sélection. |
| PersistentCapture | 9 | RH-equivalence/conditional | ÉQUIVALENT-RH | `PersistentCapture` ∀ ⟺ RH déclaré « à ne pas chercher à démontrer » ; « anti-compensation / compenser » en-tête. |
| PointedPrimeComparison | 9 | contact-reading | FIDÈLE | Position d'un premier dans une Tour (lecture) ; en-tête « premiers pointés par les contacts » (prose, pas d'énoncé). |
| PrimalEventRaccord | 56 | other | FIDÈLE | Événement premier complet, raccord grammatical, organisme spectral ; premier partagé dans une cellule (inégalités). |
| PrimeBlockDecomposition | 10 | counting/background | PARTIEL | Route borne de croissance du reste (blocs) ; exposant 1 seul ; hypothèse de blocs = bande sans zéro. |
| PrimeCellError | 22 | finite-window | PARTIEL | Fenêtres 12/24/36 transitions, identités exactes ; « aucune compensation entre fenêtres n'est imposée » ; contrôle θ<1 non démontré. |
| PrimeGapLedger | 13 | gap-contribution | FIDÈLE | Enveloppe et registre par écart ; « rien ici ne fixe la position radiale ». |
| PrimeGrammarQuantitative | 55 | counting/background | MIXTE | Identités premières fidèles ; fermetures conditionnelles (von Koch, lois pondérées) ⟹ RH déclarées ; « compensation » ×4. |
| PrimeOnlyRadialRigidity | 8 | RH-equivalence/conditional | FIDÈLE | Séparation stricte réfutée, identifier ≠ égaliser ; loi de conservation ⟺ RH déclarée. |
| PrimeTransitionDecomposition | 22 | counting/background | PARTIEL | Route blocs ; `prime_blocks_iff_zero_free` caractérisation ; aucune dérivation. |
| PrimeWeightResponse | 11 | other | FIDÈLE | Réponse radiale à une famille `ζ(s−εc)` ; borne honnête (Hamburger non compilé). |
| ProgressionDirection | 4 | other | FIDÈLE | Sens de progression rigidifié ; la somme ne porte aucun ordre. |
| QuadraticVariation | 15 | finite-window | FIDÈLE | Identités d'énergie de fenêtre ; « aucune identité ne fixe le terme croisé ». |
| RaccordDetector | 13 | other | FIDÈLE | Détecteur orienté ⟺ hauteur avance ; charge d'une fibre ; « impose donc β_l ≤ 1/2 ≤ β_e » (sens logique). |
| RadialSlope | 8 | other | FIDÈLE | Hauteur → fréquence, β → pente ; « aucun énoncé ne la fixe ». |
| RayCapture | 13 | contact-reading | FIDÈLE | Profondeur d'insertion, dichotomie ; en-tête R5 annonce un TFAE ⟺ RH absent du fichier (seul `capture_of_onLine`). |
| RayEnergy | 11 | contact-reading | FIDÈLE | Énergie sur les rayons ; `tower_reads_any_prime` : tout premier dans une cellule, « la géométrie n'impose aucune hauteur ». |
| ReadingArithmetic | 8 | contact-reading | FIDÈLE | Pivot linéaire en log ; notion « V » détruite ; `riemannHypothesis_iff_noLowerSide`. |
| RegimeCell | 38 | other | FIDÈLE | Cellule a→e→l→b, charge, enregistrement du résidu ; « aucune n'est une contradiction ». |
| RegimeChange | 17 | RH-equivalence/conditional | MIXTE | Dichotomie/jonctions fidèles ; `riemannHypothesis_iff_no_regimeEntry` déclaré « RH elle-même ». |
| RegimeTower | 18 | contact-reading | FIDÈLE | Régime lu sur pas/translation des contacts ; « lire le régime ne l'interdit pas ». |
| RegimeTransportAudit | 13 | other | FIDÈLE | Fibre mixte, domaines d'inclusion, égalités E116 fausses. |
| RegimeTrigger | 28 | counting/background | MIXTE | Fibres, détecteur en T (fidèle) ; `riemannHypothesis_iff_fibres_singleton`, `_iff_no_diagonal` déclarés. |
| RegimeWindow | 14 | other | FIDÈLE | Fenêtre minimale, charge impaire, côté premier pair en d ; « aucune n'exclut la cellule ». |

## 2. Contacts identifiés à des premiers

Aucun énoncé (hypothèse ou conclusion) ne pose une ÉGALITÉ entre un contact/incidence (`contactMinusAt`, `contactPlusAt`,
`incidence`, `towerPosition`) et un premier (`fnPrimeAtRank`, `Nat.Prime`, `occurrence`, `expectedMinimumPrime`). Les seules
co-occurrences sont des LECTURES d'une Tour en un premier (valeur de `towerPosition` en `p_n`) ou des encadrements
« premier dans la cellule `[C⁻_k, C⁺_k]` » (inégalités strictes/larges), conformes à la doctrine :

- MirrorFrequency:31 `phase_increment_eq_pi_span` ; OccurrenceHeightComposition:127 `pair_reads_own_step_identically` ;
  OneZeroOnePrime:41 `every_prime_in_every_tower`, :79 `entry_arrow_point_irrelevant` ; RayEnergy:158 `tower_reads_any_prime`,
  :169 `passage_double_constraint` ; PrimalEventRaccord:618 `grammaticalRaccord_environment` ; LocalRaccordCaptivity:313
  champ `position` de `ExactPrimeTransition`. Aucun ne dit qu'un contact « est » un premier.

Conflations de VOCABULAIRE (contact appelé « rencontre ») à corriger, sans égalité formelle :

- OccupiedFrequency:46 (`occupied_signal_meeting_points`, « ses rencontres sont exactement les positions de la ligne », conclusion
  `contactMinusAt z k = lineContact T k`) ; :65 (`OneSignalPerFrequency`, « deux signaux partagent leur point de rencontre
  d'indice 0 (les écarts des premiers imposent, à chaque fréquence, les points de passage obligés) ») ; :105 (`FrequencyTaken`,
  « dont `w` partage le point de rencontre ») ; :121 (`frequencyTaken_closes`, hypothèse `contactMinusAt w 0 = contactMinusAt z 0`
  appelée « point de rencontre »). Ici « rencontre » = contact de Tour, pas `meetingPoint I = p_{n+1}`.
- MeetingPoint:125 `shared_frequency_no_common_meeting` : « réseaux de rencontres lissées » (`smoothedMeeting`) ; OffCarrier:489
  `outgoing_no_common_smoothed_meeting` précise que « les deux notions de rencontre ne coïncident pas » — à reporter dans MeetingPoint.
- PointedPrimeComparison:7 (en-tête) : « les premiers pointés par les contacts » (prose ; les énoncés lisent `pointedPosition`
  d'un premier, et §1 dit que le pointage est une étiquette de rang).

## 3. Lexique à corriger

Termes : compens-, payer/paye/prix, marge admissible, impos- (écart/événement → membre), fixe β.

- LocalGlobalGapMatrix:15 « et le `½` du facteur se compensent » (sens numérique, bénin).
- LocalPrimeGapSynchronization:313 « aucune compensation entre écarts n'est masquée ».
- LocalWindowTransmission:9 « démontrer sa marge admissible » ; :22 « marge admissible DÉMONTRÉE » ; :31 « au-delà de la compensation
  admissible » ; :81 « Complément collectif et marge admissible » ; :100 « **Marge admissible démontrée** » ; :121 « par plus que la
  marge admissible » ; :132 « si une arrivée basse impose sur une fenêtre … plus la marge admissible ».
- LocalRaccordCaptivity (hors liste mais même famille) : « coût de sortie », « disponible », « budget », « déficit » (:20–27, :58, :62, :102, :175).
- LowNextZeroSignatures:5 et :13 « ce qu'il impose à sa fréquence » (zéro → ses propres paramètres, bénin).
- MeetingPoint:15 « la part de chacun est imposée » ; :68 « Part imposée d'un membre sur un écart » (`imposedShare`) ; :73 « la part imposée » ;
  :295 « Ce que l'ordre seul impose à l'arrivée ». (`imposedShare` est un objet autorisé par la doctrine ; seul le verbe est à peser.)
- MeetingSampling:32–33 « le prix d'un zéro hors ligne ne peut être payé que par une infinité … ce que paie une infinité n'est pas compilé ».
- MirrorGroupNonCompensation:5 titre « non-compensation » ; :9 « non-compensation de la contribution erratique » ; :17 « NON-COMPENSATION
  dans le groupe » ; :48 ; :51 « n'y est compensé par aucun autre membre » ; :66 ; :102 ; noms `mirror_group_not_compensated`,
  `group_noncompensation_closes`.
- MirrorPairExactSum:44 « les deux phases en `x` se compensent exactement » ; :88 et :162 « Aucune compensation à l'intérieur de la paire » ;
  noms `mirror_pair_no_internal_compensation(_smoothed)`.
- OccupiedFrequency:20 et :64 « les écarts des premiers imposent, à chaque fréquence, les points de passage obligés » ; :71 « une rencontre
  commune à fréquence égale fixe `β` ».
- OccurrenceHeightComposition:53 « deux occurrences premières distinctes imposent deux hauteurs distinctes » (cible déclarée ⟺ RH).
- OffAmplificationAudit:14–15 « impossibilité collective de compensation » ; :26 « la non-compensation par un groupe fini » ; :93 « n'imposent
  pas l'incompatibilité » (négation, bénin) ; :102 « n'est compensé par aucun groupe fini » ; :465 « non-compensation par tout groupe fini ».
- OffCarrier:55 « la cassure est réalisée par la totalité (compensation = autres fréquences) » ; :387 et :486 « l'écart leur impose … la
  rencontre unique à `p_{n+1}` » ; :1077 ; :1243 nom `break_compensated_by_other_frequencies` (docstring :1237 déjà rectifiée, renommage
  `break_complement_identity` proposé, non exécuté).
- OnCrossReadings:24 « ce que les données précédentes imposent » ; :471 « Ce que l'événement supplémentaire impose à la Tour suivante ».
- OnLineBetaEqPrevious:269 « ne se compensent jamais » ; :314 « compensation exacte ».
- OscillationResultant:262 « diagonale + compensation interfréquences ».
- PersistentCapture:23–24 « sans énoncé d'anti-compensation, les autres membres peuvent compenser ».
- PrimeCellError:184 « aucune compensation entre fenêtres n'est imposée ».
- PrimeGrammarQuantitative:24 « ni une compensation entre fenêtres » ; :405 « la compensation est entièrement dans les termes croisés » ;
  :498 et :592 « Loi de compensation à l'échelle logarithmique ».
- RaccordDetector:12 « impose donc `β_l ≤ 1/2 ≤ β_e` » (sens logique, bénin).
- Négations bénignes non à corriger : LocalGlobalGapMatrix:25, PrimeOnlyRadialRigidity:42, RayEnergy:23/:155, ReadingArithmetic:16/:106,
  OnCrossReadings:452, PairCurvature:7 (« référence imposée par l'auteur »), MirrorFrequency:14.

## 4. Hypothèses nommées ⟺ RH (ou impliquées par RH), selon leur propre docstring

- LocalPrimeGapSynchronization:562 `def LocalOnScale` ⟺ β=1/2 (:566) ; quantifiée sur les passages ON ⟺ RH (:587 `local_on_law_iff_riemannHypothesis`).
- LocalRaccordCaptivity:386 `sameHeight_capture_target_iff` : lemme cible ⟺ « aucun passage de même hauteur » (= RH par RegimeChange:260).
- LogGapsTheorem:34–51 : hypothèses importées `DemandBoundedAtMeetings`, `SummitAttained` (clôture + sommet ⟹ RH ; route retirée §19).
- MeetingPoint:90 `def ExpectedFrequencyRisesAtMeetings` ⟺ `ExpectedFrequencyRises` (:98), ⟹ RH (:109), ⟺ « aucun passage à fréquence
  partagée » (:115) ; :384 `def ConstantRelativeAmplitudeAtMeetings w` ⟺ β=1/2 (:402).
- MeetingSampling:85 `def MeetingsSampleFrequencies` (théorème depuis LogGapsTheorem:30) ; hypothèse `hdem` (demande bornée aux rencontres).
- MeetingsBridge:265 `def GapsRootOrder` (« plus forte que ce que RH fournit ») ; :345 `DemandBoundedAtMeetings ↔ ExpectedFrequencyRises` sous GapsRootOrder.
- MirrorEventCollision:93 `def memberHeightTransport` (en-tête : exigé au miroir de tout zéro bas ⟺ RH, théorèmes hors de ce fichier).
- MirrorGroupNonCompensation:70 / PrimeBlockDecomposition:260 / PrimeTransitionDecomposition:251 / OffAmplificationAudit:112 : hypothèse
  « borne du reste (ou des blocs) d'exposant θ < 1−β_l » = bande sans zéro contenant le miroir (contradictoire avec le zéro bas).
- NoRegimeChange:291 `def PNoRegimeChange` ⟺ RH (:363).
- OccupiedFrequency:65 `def OneSignalPerFrequency` ⟺ RH (:130) ; :105 `def FrequencyTaken w` ⟺ β=1/2 (:115), ∀ ⟺ RH (:146).
- OccurrenceHeightComposition:54 `def DistinctOccurrencesDistinctHeights` ⟺ RH (:60) ; forme consécutive ⟺ RH (:86).
- OffAmplificationAudit:171 `def DominationConserved` ; ∀ ⟺ RH (:229) ; `InsideField` universel ⟺ RH (:152) ; domination du miroir à un
  premier/un point ⟺ β=1/2 (:348, :410).
- OffCarrier:1336 `def ContinuationForced` (« jamais un théorème ») ; :1362 `def ContinuationForcedOnCarriers` ⟺ RH (:1372).
- OnLineBetaEqPrevious:470, :489 : hypothèse `hDom` (domination individuelle sur tout l'horizon) « ferme RH ».
- OnRegimeInduction:321 : invariant `ΔD = 0` quantifié sur les passages d'historique ON ⟺ RH.
- PersistentCapture:33 `def PersistentCapture` ; ∀ ⟺ RH (:126, :136).
- PrimeOnlyRadialRigidity:86 : loi de conservation radiale à historique ON ⟺ RH.
- PrimeGrammarQuantitative:274 : borne du résidu cumulé (von Koch) ⟹ RH, « de la force de RH » ; :728 : lois pondérées ∀α ⟹ RH.
- PrimeTransitionDecomposition:371 : estimation de blocs d'exposant 1+θ ⟺ tout zéro ≤ θ (θ>1/2) ; :383 forme « avenir ».
- ReadingArithmetic:132 `riemannHypothesis_iff_noLowerSide`.
- RegimeChange:260 `allVertical_iff_riemannHypothesis` ; :292 `riemannHypothesis_iff_no_regimeEntry`.
- RegimeTrigger:240 `riemannHypothesis_iff_fibres_singleton` ; :258 `riemannHypothesis_iff_no_diagonal`.
- RayCapture (en-tête :24–27) : annonce « `PNoNullPassage`, exclusion horizontale, superposition, … toutes équivalentes à RH (TFAE) » ; aucun
  théorème correspondant dans le fichier.

Aucune de ces hypothèses n'est présentée comme établie ; toutes sont étiquetées équivalence, prémisse ou cible.

## 5. sorry / admit / axiom

`grep -n "sorry\|admit\|^axiom"` sur les 55 fichiers, lignes de commentaires exclues : **aucun** pour chaque module.
Seuls faux positifs : mentions « Aucun `sorry` » dans les en-têtes (35 modules) et les noms de théorèmes
OffAmplificationAudit:95 `contact_constraints_admit_low`, :125 `reconstruction_admits_any_radial` (identifiant, pas la tactique).

## 6. Décompte final

Modules FIDÈLE 32 / À RECONTEXTUALISER 7 / ÉQUIVALENT-RH 4 / PARTIEL 3 / MIXTE 9 (total 55).

### Annexe D — groupe 4 (modules R–Z)
# Audit des énoncés — groupe 4 (54 modules, `RHV6Fresh/Terminal/`)

Doctrine de référence : réorientation de l'auteur du 2026-11-01 (contacts de Tour ≠ premiers ; contribution exacte par écart ; rencontre = `meetingPoint I = p_{n+1}` ; cassure réalisée par la totalité ; lexique « compensation / payer / prix / marge admissible / impose / fixe β » proscrit ; aucune hypothèse ⟺ RH présentée comme acquise).
Méthode : lecture de l'en-tête `/-! … -/`, de chaque `theorem`/`lemma`/`def` et de sa docstring (signatures seulement, pas les preuves). Nombre de théorèmes = `grep -c '^theorem\|^lemma'`.

## 1. Tableau

| module | nb thm | classe d'objet | verdict | notes |
|---|---|---|---|---|
| RemainderEnergy | 13 | contact-reading | FIDÈLE | Cellules de contacts du terme propre ; `ownCellEnergyDensity_flat_iff` est une caractérisation, pas une fixation de β. |
| RemainderExponent | 16 | counting/background | MIXTE | `riemannHypothesis_iff_remainderExponent_eq_half` étiqueté ⟺ ; §3 « anti-compensation / aucune compensation » = lexique proscrit. |
| RemainderRegime | 16 | meeting-break | À RECONTEXTUALISER | Mathématique fidèle (rencontres `meetingPoint`), hypothèses nommées ; titre et §5 en lexique « payer / prix / paie ». |
| RemainderRepresentation | 23 | RH-equivalence/conditional | MIXTE | Identité de représentation fidèle ; `CollectiveBudget` ⟺ membres ON ; `whole_winding ⟺ √x ⟺ RH` étiquetés ; « compensation durable » l.268. |
| RemovalExponent | 6 | finite-window | FIDÈLE | Caractérisation exacte de l'exposant du retrait (⟺, aucun côté dérivé) ; exposant 1 seul acquis. |
| RiemannHypothesisDefinition | 1 | other | FIDÈLE | Mathlib ⟺ définition classique. |
| RightSetDichotomy | 10 | RH-equivalence/conditional | FIDÈLE | Tout conditionnel à `DemandBoundedAtMeetings`, `MeetingsSampleFrequencies`, `SummitAttained` (nommées). |
| SamplingFromLogGaps | 11 | meeting-break | FIDÈLE | `LogGapsVanish` nommée (PNT) ; docstring « absent de Mathlib » périmée depuis le port PNT (`LogGapsTheorem.lean`). |
| ShiftedWorld | 5 | other | FIDÈLE | Monde témoin `ζ(s−δ)ζ(s+δ)`, contrôle. |
| SignedWindowComparison | 11 | finite-window | À RECONTEXTUALISER | §5 montre que la comparaison signée est renversée (antécédent = False) ; « compensations exactes » l.6-7. |
| SpectralIdentity | 16 | gap-contribution | À RECONTEXTUALISER | Indépendance des profils, fidèle ; « pas de compensation finie » l.25, l.183 = lexique proscrit. |
| SpectralUniqueness | 17 | gap-contribution | FIDÈLE | Unicité de la décomposition ; `riemannHypothesis_iff_onLine_representation` étiqueté caractérisation. |
| SpectralWindowProjection | 21 | finite-window | FIDÈLE | D4 hypothèse d'erreur explicite ; D6 exposant 1 ; D7 `stableProjection_iff_onLine` = réécriture du but. |
| SpontaneousRegimeBreak | 11 | RH-equivalence/conditional | FIDÈLE | Loi radiale posée en hypothèse de théorème ; `radial_preserving_law_of_riemannHypothesis` montre la circularité. |
| StableTowerSignals | 16 | contact-reading | FIDÈLE | Contacts = abscisses où le mode est réel ; « aucune ne fixe β » explicite. |
| StageCell | 52 | contact-reading | FIDÈLE | Étages/contacts, fond `li` par cellule, fibre suivante : bornes d'exposant 1, `fixed_cut_budget_not_sqrt` honnête. |
| SuccessionInvariants | 10 | other | FIDÈLE | Trichotomie A/B/C ; raccords encadrés dans des cellules (pas d'identification contact = premier). |
| SummitAttained | 14 | RH-equivalence/conditional | FIDÈLE | Hypothèse nommée, vraie sous RH par vacuité, jamais posée. |
| SummitVertical | 25 | RH-equivalence/conditional | FIDÈLE | `riemannHypothesis_iff_supremumAttained_of_closure` étiqueté ; route sommet retirée au §19 (dérive). |
| SymmetricWinding | 10 | RH-equivalence/conditional | ÉQUIVALENT-RH | Enroulement symétrique/entier ⟺ β = 1/2 ⟺ RH ; en-tête cite « pas de choix », mais théorèmes en ⟺. |
| SynchronizationAudit | 8 | meeting-break | À RECONTEXTUALISER | Audit E301 : conclusions E301 déclarées FAUSSES par l'auteur (§19.9) ; énoncés exacts mais cadre à requalifier. |
| SynchronizationMatrix | 11 | gap-contribution | FIDÈLE | Cellules = `gapTerm` ; `matrix_compatibility_law_iff_riemannHypothesis` étiqueté. |
| TangentialInversion | 14 | contact-reading | À RECONTEXTUALISER | §4 « Premier égal à un contact », « fixe la partie réelle » : contact identifié à un premier (voir §2). |
| ThreeZeroWindow | 16 | counting/background | FIDÈLE | RvM inconditionnel ; contacts comparés en pas seulement. |
| TotalityPays | 10 | meeting-break | À RECONTEXTUALISER | Mathématique fidèle (rencontres, totalité) ; titre et docstrings « payer / paie / paiement » ; une docstring déjà corrigée (§19.21). |
| TowerFourSectors | 15 | contact-reading | FIDÈLE | Symétries de la Tour ⟺ en ligne ; « ne fixe pas la Tour suivante ». |
| TowerGrid | 9 | contact-reading | FIDÈLE | Forme normale, caractérisations, « elles lisent, n'interdisent pas ». |
| TowerHierarchy | 10 | RH-equivalence/conditional | ÉQUIVALENT-RH | `RaccordHierarchy` à tous les raccords ⟺ RH, étiqueté. |
| TowerRaccord | 6 | other | FIDÈLE | Structure : `M` encadré par deux contacts (pas d'égalité) ; docstring « prémisse unique `PNoRegimeChange` » périmée. |
| TowerTwoSidedRoom | 9 | contact-reading | FIDÈLE | `TowerRoom` non dérivé, RH ⟹ TowerRoom ; modèle paramétrique avec paire miroir. |
| TowerWinding | 11 | contact-reading | FIDÈLE | `contact_below_of_height` : un réel/premier au-dessus d'un contact (inégalité, pas identification). |
| TransitionRigidity | 19 | counting/background | FIDÈLE | Grammaire mod 6 ; liaison recherchée réfutée honnêtement. |
| TranslationVsProgression | 10 | mirror-pair | FIDÈLE | Prémisse (B) réfutée par E111 ; `RH_FOUND=FALSE`. |
| TransmissionIncrements | 6 | gap-contribution | FIDÈLE | Identités d'incréments, exposant 1. |
| TransportAtSharedPrime | 26 | mirror-pair | FIDÈLE | `Λ(M)` canal local ; §4 doublon `memberStep` compilé ; rectifié §19.19. |
| TripletReadings | 5 | RH-equivalence/conditional | À RECONTEXTUALISER | `AmplitudeImposedByGaps` : « amplitude imposée par les écarts » = lexique proscrit ; ⟺ ligne. |
| TwoClocks | 11 | counting/background | À RECONTEXTUALISER | Docstring finale cite `clock_agree_iff_riemannHypothesis` « ci-dessus » : absent du fichier. |
| TwoGapWindow | 15 | mirror-pair | FIDÈLE | Charge = lecture de d, « aucune identité ne la fixe ». |
| UniformVariationBridge | 12 | RH-equivalence/conditional | ÉQUIVALENT-RH | Sous clôture RH ⟺ `UniformVariationAtGaps` ; route retirée au §19. |
| Universalization | 2 | other | FIDÈLE | Docstring « RH n'apparaît que dans ce module » périmée (nombreux modules). |
| VerticalEnergyPush | 12 | RH-equivalence/conditional | À RECONTEXTUALISER | En-tête V5 annonce `PVerticalEnergyPush ↔ RH` ; section V5 vide, aucune def/théorème. |
| VerticalForce | 10 | mirror-pair | FIDÈLE | F1–F4 ; force verticale échoue, dit honnêtement. |
| WholeWindingObligation | 8 | RH-equivalence/conditional | ÉQUIVALENT-RH | Obligation ⟺ RH étiquetée ; docstring « prémisse unique `hGain` » périmée. |
| WindingReadingChain | 10 | contact-reading | À RECONTEXTUALISER | « rencontre » = contact k (≠ `meetingPoint`) ; « compensation signée », « contribution imposée ». |
| WindowComparison | 8 | finite-window | FIDÈLE | Identités ; bornes sous hypothèse ON explicite ; `H ≥ 28` numérique. |
| WindowCorrespondence | 14 | counting/background | FIDÈLE | « Appartenance à une fibre ≠ localisation entre contacts » explicite. |
| WindowFeasibility | 11 | contact-reading | FIDÈLE | Faisabilité de la fenêtre OFF pour tout d ; aucune contrainte. |
| WindowProgression | 16 | counting/background | FIDÈLE | Progression première minimale ; Abel pour toute suite de hauteurs. |
| ZeroCascadeReading | 12 | contact-reading | À RECONTEXTUALISER | « rencontres » = contacts de Tour ; `approach_iff_onLine` ⟺ β = 1/2 ; citation « impose » de l'auteur. |
| ZeroFreeRegionBand | 6 | counting/background | FIDÈLE | Région sans zéro ; « ne fixe pas β = 1/2 » ; « épaisseur admissible » l.839. |
| ZetaBoxGeneric | 36 | other | FIDÈLE | Certificat de ζ sur rectangle. |
| ZetaBoxNumeric | 27 | other | FIDÈLE | Briques numériques `norm_num`. |
| ZetaParameters | 8 | other | FIDÈLE | Hypothèse √x explicite (⟺ RH via RemainderRepresentation), non posée. |
| ZetaRealSegment | 2 | other | FIDÈLE | ζ ≠ 0 sur (0,1). |

## 2. Contacts identifiés à des premiers

Aucun ÉNONCÉ n'égale `contactMinusAt`/`contactPlusAt`/`incidence`/`towerPosition` à `fnPrimeAtRank`, `Nat.Prime`, `primalEventAt` ou `memberOccurrence`. Les identifications sont dans les DOCSTRINGS, sur un réel générique `q` nommé « premier » :

- TangentialInversion:136 `contact_eq_iff_phase` — en-tête l.17 : « **Premier égal à un contact** : `C_k = q` ⟺ … » (hypothèse `windingContact β T k = q`, `q : ℝ`).
- TangentialInversion:152 `contact_radial_formula` — docstring l.151 : « Un premier égal au contact d'indice `k` fixe la partie réelle … `β = T cot(T log q)` ».
- TangentialInversion:168 `two_contacts_height_quantized` — docstring l.167 : « Deux premiers tous deux contacts d'une même Tour ».
- TangentialInversion:5 (titre) : « un premier encadré ne rend qu'une région ».

Non comptés (encadrement strict, pas égalité) : TowerRaccord:39 `exitCell_contains`/`entryCell_contains` (`contact < M ≤ contact`), SuccessionInvariants:171 `passage_raccords` et `succession_invariants` (cellules contenant `occurrence`), TowerWinding:145 `contact_below_of_height` (`windingContact < q`).

## 3. Lexique à corriger

- RemainderRegime:4 « ce que des zéros sur la ligne peuvent **payer** » (titre).
- RemainderRegime:6 « le **prix** d'un couple hors ligne était écrit ».
- RemainderRegime:8 « ce qu'un zéro de la ligne peut **payer** ».
- RemainderRegime:174 « L'historique ne **paie** pas : aucune famille finie non à droite ne couvre le **prix** ».
- RemainderRegime:183 (en-tête) « **l'historique ne paie pas** ».
- RemainderRepresentation:268 « ce qui interdit toute **compensation** durable par les autres ».
- RemainderExponent:18 « **Anti-compensation** (§3) » ; :22 « l'argument d'anti-**compensation** ».
- RemainderExponent:197 « ## 3. Anti-**compensation** » ; :199 « **Aucune compensation dans la paire miroir** ».
- SignedWindowComparison:7 « ces trois opérations perdent les **compensations** exactes ».
- SpectralIdentity:25 et :183 « **Pas d'intrus, pas de compensation finie** ».
- TotalityPays:4 « Ce que la totalité doit **payer** » (titre).
- TotalityPays:83 « **Ce que le reste doit payer en un point** ».
- TotalityPays:470 (docstring de `restRelative_ge_members`) « le reste **paie** au moins l'amplitude relative du miroir ».
- TotalityPays:500 (docstring de `rest_unbounded_beyond_rank`) « Le **paiement** croît sans borne ».
- TangentialInversion:151 « Un premier égal au contact d'indice `k` **fixe la partie réelle** ».
- TripletReadings:44 « l'amplitude **imposée** par les écarts à un vrai zéro » ; :46 `AmplitudeImposedByGaps` ; :49 « amplitude **imposée** par les écarts (prémisse nommée, de force RH) » ; :54 « l'amplitude **imposée** par les écarts est incompatible ».
- WindingReadingChain:10 « Chaîne de lecture, d'enroulement et de **compensation** » ; :13-14 « **compensation** signée » ; :22 et :63 « **compensation** signée (…, contribution **imposée**) » ; :88 `imposed_contribution_eq` (nom importé).
- ZeroCascadeReading:8 « cette stabilité **impose** que chaque zéro plus haut possède une fréquence supérieure » (citation de l'auteur, sens stabilité → fréquence, pas écart → membre : à conserver comme citation, signaler).
- Limite : ZeroFreeRegionBand:839 « L'épaisseur **admissible** `1/2 − A/(log T)^9` » et :844 « La **marge** `A/(log T)^9` » (pas « marge admissible » littéral ; à surveiller).
- Non retenus (sens différent) : SuccessionInvariants:9,30,32 « égalité/signe imposé(e) », « identité de raccord imposée par la Tour » (il s'agit des prémisses P6/P7, pas d'un écart imposant à un membre) ; TransportAtSharedPrime:31,38 « impossible », « aucune loi n'impose ».

## 4. Hypothèses nommées ⟺ RH (ou impliquées par RH)

`def … : Prop` du groupe et hypothèses de théorèmes qui, selon leur propre docstring, équivalent à RH ou en découlent :

- RemainderRepresentation:251 `CollectiveBudget H` — ⟺ tous les membres au-dessus de `H` en ligne (:341 `collectiveBudget_iff_following_onLine`) ; réfuté par un suivant hors ligne (:269).
- RemainderRepresentation:452 hypothèse d'enroulement entier ⟺ borne `√x` du reste ; « les deux côtés chacun équivalents à RH ».
- RemainderExponent:185 `remainderExponent = 1/2` ⟺ RH.
- RemainderRegime:138 `RestNotRight l` — nommée ; avec demande bornée ⟹ non arrivée basse (:159) ; AUDIT_FIDELITE §19.21 : hypothèses ⟺ RH.
- SpectralWindowProjection:264 `StableProjection A β T` ⟺ `β = 1/2` (:269), « réécriture du but ».
- SpectralUniqueness:522 représentation en ligne ⟺ RH (caractérisation).
- SummitAttained:52 `SummitAttained`, :58 `SummitAttainedIsolated` — vraies sous RH par vacuité (:70) ; avec clôture + échantillonnage ⟹ RH (:204).
- SummitVertical:383 `SupremumAttained` — vraie sous RH (:393) ; sous clôture ⟺ RH (:418).
- UniformVariationBridge:38 `UniformVariationAtGaps` — vraie sous RH (:113) ; sous clôture ⟺ RH (:130).
- TowerTwoSidedRoom:39 `TowerRoom z` — RH ⟹ TowerRoom (:44) ; `TowerRoomAtInfinity` (:168) inconditionnel.
- TowerRaccord:87 `TowerRaccord.Oriented` — RH ⟹ orienté sur tout passage (:119).
- TowerHierarchy:60 `RaccordHierarchy` — à tous les raccords ⟺ RH (:133).
- TripletReadings:46 `AmplitudeImposedByGaps z q` ⟺ `β = 1/2` (:50), « de force RH ».
- SymmetricWinding:149, :192 ; WholeWindingObligation:110, :132 — enroulement entier (premier zéro / tous passages / « ordre ⟹ domination ») ⟺ RH.
- SynchronizationMatrix:145 loi de compatibilité sur toutes les colonnes ⟺ RH.
- SpontaneousRegimeBreak:219 loi radiale préservant la ligne : existe sous RH (« poser son existence réinjecte la cible »).
- ZetaParameters:137 hypothèse `‖smoothedRemainder x‖ ≤ C√x` (⟺ RH par RemainderRepresentation:452).
- WindingReadingChain:137 `one_sided_iff_onLine`, ZeroCascadeReading:156 `approach_iff_onLine` — condition réduite ⟺ arrivée ON (« quantifiée de la force de RH »).
- Hypothèses `hOn` (membres ON jusqu'à `H`) dans StageCell, WindowComparison, RemovalExponent : RH partielle explicite.
- Hypothèses importées d'autres groupes, utilisées ici : `DemandBoundedAtMeetings`, `MeetingsSampleFrequencies`, `ExpectedFrequencyRises`, `ChebyshevAsymptotic`, `GapsRootOrder`, `NoRadialShift`.
- `LogGapsVanish` (SamplingFromLogGaps:145) : nommée mais de force PNT, pas RH.
- Fantômes : VerticalEnergyPush en-tête l.23-27 (`PVerticalEnergyPush ↔ RH`, absent) ; TwoClocks:232 (`clock_agree_iff_riemannHypothesis`, absent).

## 5. sorry / axiom / admit

`grep -n "sorry\|admit\|^axiom"` (hors lignes de commentaire pur) sur les 54 modules : **aucun** `sorry`, `admit` ou `axiom` en code. Toutes les occurrences sont dans des docstrings (« Aucun `sorry`, aucun `admit`, aucun axiome ») ou dans le nom `tail_bound_admits_offline_point` (SynchronizationAudit:111, :125 `#print axioms`). Modules sans aucune occurrence textuelle : RemainderRepresentation, RemovalExponent, RiemannHypothesisDefinition, SignedWindowComparison, SpectralWindowProjection, StableTowerSignals, StageCell, SynchronizationMatrix, TransitionRigidity, TransmissionIncrements, TransportAtSharedPrime, TwoClocks, Universalization, VerticalForce (n'a que la docstring), WindowComparison, WindowCorrespondence, ZeroCascadeReading, ZeroFreeRegionBand, ZetaBoxNumeric, ZetaRealSegment.

## 6. Décompte final

Modules FIDÈLE : 37 / À RECONTEXTUALISER : 11 / ÉQUIVALENT-RH : 4 / PARTIEL : 0 / MIXTE : 2 (total 54).

## 9. Exécution du plan sur feu vert (2026-11-01) et consolidation par le texte « Tour issue du zéro authentique »

- **F** : `Terminal/SameGapsAudit.lean`, 24 théorèmes (F1–F8, T1–T5, E1), axiomes standard, aucun `sorry`, module isolé ;
  journal `audits_compilation/SAMEGAPS_20261101.md` (quatre tentatives, erreurs exactes).
- **Texte « Tour géométrique »** : compilé intégralement (T1–T5) ; la similitude annoncée est une homothétie de rapport
  `‖ρ‖²·exp(−2βφ/T)` sous `s = T·log x − 2φ` ; identités pour toute position radiale, rien sur β.
- **G** : `experiments/E401_ThreeTowersRegister/` (pré-enregistrement, script, registres à 30 et 50 chiffres, bilans) : jumeau
  identique, télescopage exact, 0/168 écarts où trois Tours égalent la demande, résidu décroissant 0,149 → 0,032 → 0,013
  (3 → 30 → 100 zéros, contrôle d'implémentation).
- **E** : E1 compilé (télescopage de la signature sur trois écarts) ; question §19.12 ouverte.
- **H** : mentions « journal, non appui » posées dans le maître (E239–E241, E309, E310, E311) ; docstrings de la chaîne non
  modifiées (règle d'arrêt), liste exacte en §19.25.4 du maître, en attente de l'auteur ; `MeetingPoint.lean:125` retiré de la
  liste des mésusages (relecture).
- Maître : §19.25. CLAUDE.md (zeta24-lean) : paragraphe « Réorientation contacts → contributions par écart → rencontre ».
