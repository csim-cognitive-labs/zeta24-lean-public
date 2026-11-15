# RHV3Lean — contrat terminal consolidé

Autorité : `docs/RHV2_STRATEGIE_LEAN.md`.

## Sorties déjà réalisées

```text
CORE-01 true mirror                         PROVED
CORE-02 distinct same-fibre members         PROVED
CORE-03 finite height fibre                 PROVED
CORE-04 consecutive pair in fibre           PROVED
CORE-05 real OFF passage                    PROVED
CORE-06 Null_Z(E_OFF)                       PROVED
CORE-09 EncZ=M on reconstructed prime data  PROVED
CORE-12 canonical place non-null            PROVED
CORE-16 universalization consumer           PROVED
```

## Conservation produite

```text
CORE-07a same source passage                 PROVED
CORE-07b exact source gap through Towers     PROVED
CORE-07c source gap nullity through Towers   PROVED
```

Il s'agit de `T(B)-T(A)` et non d'une hauteur individuelle nulle.

## Sorties non réalisées

```text
CORE-08 concrete canonical T2 attachment      NOT_PROVED
CORE-10 source-nullity -> prime-diagonal       NOT_PROVED
```

La première doit attacher sans argument scientifique libre chaque
`TZeroPassage` à une `TPrimeHistoryPlace`. Le passage et son gap source sont
déjà conservés dans `TSourceTaggedPrimePlace` et par les théorèmes de décodage
des Tours. La seconde doit démontrer séparément la conversion de `Null_Z(E)`
en diagonalité première. `EncZ=M` seul ne réalise pas cette conversion.

## Test de force obligatoire

Le code doit certifier :

```text
existence d’une conversion Null_Z vers diagonalité des places canoniques
<-> absence de tout passage zéro nul,
```

et en particulier que ce transport implique RH. Une structure contenant le
transport comme champ, ou un theorem le prenant comme argument, est seulement
un consumer conditionnel.

## Interdictions

Sont interdits comme prémisses d’un theorem RH sans argument : `hLocalLaw`,
`hRPass`, `hNullity`, `hTransitionTransport`, `PNoNullZeroPassage`, collision
C3, égalité numérique des deux gaps, ou certificat contenant ces conclusions.

## Statut

```text
SCIENTIFIC_RESIDUAL_INPUT_COUNT = 2
FIRST_RESIDUAL_INPUT = concrete canonical T2 attachment
SECOND_RESIDUAL_INPUT = source-nullity to prime-diagonal conversion
TERMINAL_BUILD_TARGET = dependency audit, not a fabricated RH theorem
```
