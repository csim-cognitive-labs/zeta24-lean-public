> Version française conservée à titre de référence. Main language: English, see README.md.

# E445 — Le Théorème du Prix au point de rencontre : pré-enregistrement (copie du §19.65, 2026-11-07)

### 19.65 Plan d'attaque de l'auteur (2026-11-07) : le Théorème du Prix au point de rencontre — pré-enregistrement d'E445

**Ordre.** Chaîne : `(β, T)` → contacts → amplitudes et fractions → bilan signé des rencontres → raccord arithmétique.
Les builds E441–E443 établissent des propriétés réelles des cellules et des rencontres mais ne démontrent pas que la
position radiale est sans effet ; les théorèmes d'inversion acquis rendent cette exclusion injustifiée. Piste
prioritaire : (1) le facteur `x^{β−1/2}` est exactement l'écart radial d'amplitude entre une Tour OFF et une Tour ON ;
(2) pour `β < 1/2` il décroît, celui du miroir `x^{1/2−β}` croît ; (3) les contacts rendent `β` et `T` exactement :
l'écart est identifiable ; (4) au point de rencontre l'amplitude est imposée par le zéro ; (5) le Théorème du Prix doit
quantifier le coût exact de cette différence au raccord ; (6) le bilan signé conserve phases, signes et amplitudes des
deux membres ; (7) la constellation complète réalise exactement la cassure arithmétique : c'est le budget collectif ;
(8) un budget exact et fini à chaque rencontre n'est pas une borne uniforme ; (9) la contradiction exige que les autres
contributions ne puissent satisfaire à la fois le budget et le prix OFF ; (10) démontrer l'incompatibilité. Exigence :
au moins trois tentatives de fermeture, dont une libre, erreur exacte et demandes du compilateur consignées.
Amendement consigné dans `CLAUDE.md` : la constellation entre uniquement à l'étape de confrontation (7)–(10).

**Pré-enregistrement E445 (`experiments/E445_MeetingPrice/`).** Module isolé `Terminal/MeetingPriceTheorem.lean`
(partie compilable, une Tour et la paire `(β, T)`, `(1−β, T)` en amplitudes réelles) : P1 `offPrice β x =
cosh((β−1/2) log x)` et `x^β + x^{1−β} = 2 x^{1/2} · offPrice` (prix exact de la paire contre deux Tours ON) ; P2
`offPrice ≥ 1 + ((β−1/2) log x)²/2`, non borné dès que `β ≠ 1/2` ; P3 prix identifié par les valeurs aux rencontres
(`radial_of_meeting_values`) ; P4 amplitude imposée à la cellule de rencontre : `p^β e^{−βπ/T}/‖ρ‖ < |v| ≤ p^β/‖ρ‖` ;
P5 réponse à la question §19.64 : `|valueCellSum| ≤ |v_dernière| · D · q/(q−1)` (`q = e^{βπ/T}`) si toutes les pentes
de cellule sont bornées par `D` ; P6 le prix bat le budget d'une rencontre : `K log x < x^r` pour `x` grand (`r > 0`).
**Trois tentatives de fermeture** (fichiers d'essai conservés en `attempts/*.lean.txt` avec la sortie exacte du
compilateur) : T1 prix contre budget à une rencontre via `complement_break_lower_bound` (E435) ; T2 bilan pondéré de la
série (P5) des deux membres contre le budget cumulé (Tchebychev `ψ ≤ (log 4 + 4) x`) ; T3 libre : non-compensation
interne du miroir + prix non borné + cassure portée par le complément. Critère : A si `False` compile sans hypothèse
nouvelle ; sinon consigner l'énoncé exact que le compilateur réclame et son statut dans le corpus (⟺ RH ou non).
Expérience chiffrée : prix et budget aux rencontres pour `β` témoin ∈ {0,3 ; 0,4 ; 0,45}, bornes P4–P5 sur les sept
Tours réelles, jumeau mpmath.

**Révocation (2026-11-07, §19.67)** : l'amendement « constellation à l'étape de confrontation » est annulé ; T1 et T3 et leurs conclusions sont annulées (étude spectrale) ; voir `RESULTS.md`, section « Révocation ».
