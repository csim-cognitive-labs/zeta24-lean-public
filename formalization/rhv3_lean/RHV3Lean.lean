/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.AlgebraicAxis
import RHV3Lean.Objects.PrimeGapGrammar
import RHV3Lean.Objects.PrimeTransitionGrammar
import RHV3Lean.Objects.TrueZero
import RHV3Lean.Objects.ZeroGapGrammar
import RHV3Lean.Objects.Passage
import RHV3Lean.Objects.RPassFull
import RHV3Lean.Objects.Triple
import RHV3Lean.Objects.HarmonicTower
import RHV3Lean.Objects.ContactsAndCell
import RHV3Lean.Objects.CountingRigidity
import RHV3Lean.Objects.VonMangoldtChebyshev
import RHV3Lean.Objects.PrimeOccurrence
import RHV3Lean.Objects.CanonicalTowerOperator
import RHV3Lean.Objects.PlaceAndLocalLaw
import RHV3Lean.Objects.FunctionalMirror
import RHV3Lean.Objects.OffFibreAndPassage
import RHV3Lean.Objects.ZetaRealSegment
import RHV3Lean.Objects.UpperRepresentative
import RHV3Lean.Objects.CanonicalWindowRule
import RHV3Lean.Objects.TransportOnOperator
import RHV3Lean.Objects.Universalization
import RHV3Lean.Objects.TrueTowerState
import RHV3Lean.Objects.TrueTowerCarrier
import RHV3Lean.Objects.CanonicalT1
import RHV3Lean.Objects.CanonicalT2
import RHV3Lean.Objects.CanonicalRiemannHypothesis
import RHV3Lean.Objects.CanonicalTrueTowerState
import RHV3Lean.Objects.SamePrimeCollision
import RHV3Lean.Objects.OffNullPassageContactSeparation
import RHV3Lean.Objects.OffMirrorDifferenceBands
import RHV3Lean.Objects.OffMirrorOverlapReduction
import RHV3Lean.Objects.OffMirrorChebyshevChannel
import RHV3Lean.Objects.OffPassageHeightSignature
import RHV3Lean.Objects.TripleTransitionRigidity
import RHV3Lean.Objects.TerminalCoreStrength
import RHV3Lean.Objects.RatioFourStateControl
import RHV3Lean.Objects.ZeroSourceReconstruction
import RHV3Lean.Objects.ZeroSourceExplicitFormulaChannel
import RHV3Lean.Objects.TowerCriticalDefect
import RHV3Lean.Objects.TowerTransition
import RHV3Lean.Objects.TowerTransitionOffSignature
import RHV3Lean.Objects.TowerPrimeGapSpan
import RHV3Lean.Objects.TowerGrammarMorphism
import RHV3Lean.Objects.TripleGrammarEvolution
import RHV3Lean.Objects.OffGrammarDetection
import RHV3Lean.Objects.OffGrammarSuccessionContradiction
import RHV3Lean.Objects.OffTripleInsertion
import RHV3Lean.Objects.PrimeSuccessionBridge
import RHV3Lean.Objects.T1AloneCounterexampleForT2
import RHV3Lean.Objects.OffMirrorCollisionViaCanonicalSuccession
import RHV3Lean.Objects.MemberZeroSourceOccurrence
import RHV3Lean.Objects.MemberSensitiveMZCorrespondence
import RHV3Lean.Objects.HeightEventPrimeGap
import RHV3Lean.Objects.CanonicalOccurrenceTransport
import RHV3Lean.Objects.PrimeGrammarTransitionRigidity
import RHV3Lean.Objects.MemberPassagePrimeNonNull
import RHV3Lean.Objects.ExplicitFormulaArithmeticBridge
import RHV3Lean.Objects.ZetaZeroMultiplicity
import RHV3Lean.Objects.ZetaHeightReflection
import RHV3Lean.Objects.ZetaReflectionMultiplicity
import RHV3Lean.Objects.ZetaConjugationOrbit
import RHV3Lean.Objects.ZetaLogDerivVonMangoldt
import RHV3Lean.Objects.PerronPort.Asymptotics.Asymptotics
import RHV3Lean.Objects.PerronPort.Asymptotics.Uniformly
import RHV3Lean.Objects.PerronPort.Rectangle
import RHV3Lean.Objects.PerronPort.Tactic.AdditiveCombination
import RHV3Lean.Objects.PerronPort.ResidueCalcOnRectangles
import RHV3Lean.Objects.PerronPort.PerronFormula
import RHV3Lean.Objects.ZetaPerronResidueInterface
import RHV3Lean.Objects.ZetaPerronLineIdentity
import RHV3Lean.Objects.ZetaPerronFiniteRectangle
import RHV3Lean.Objects.ZetaRightVerticalTailsP4_5
import RHV3Lean.Objects.P4Port.NumberTheory.LSeries.ZetaFunctionalEquation
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.CompletedXi
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.Complex.LogBounds
import RHV3Lean.Objects.P4Port.Analysis.Complex.Norm
import RHV3Lean.Objects.P4Port.Analysis.Complex.WeierstrassFactor
import RHV3Lean.Objects.P4Port.Analysis.Complex.CanonicalProduct
import RHV3Lean.Objects.P4Port.Analysis.Meromorphic.DivisorSupport
import RHV3Lean.Objects.P4Port.Analysis.Complex.DivisorIndex
import RHV3Lean.Objects.P4Port.Analysis.Complex.LocallyUniformLimit
import RHV3Lean.Objects.P4Port.Analysis.Complex.DivisorConvergence
import RHV3Lean.Objects.P4Port.Analysis.Complex.DivisorUnits
import RHV3Lean.Objects.P4Port.Analysis.Complex.DivisorFiber
import RHV3Lean.Objects.P4Port.Analysis.Complex.DivisorComplement
import RHV3Lean.Objects.P4Port.Analysis.Complex.DivisorPartialProductFactor
import RHV3Lean.Objects.P4Port.Analysis.Complex.DivisorQuotientConvergence
import RHV3Lean.Objects.P4Port.Analysis.Complex.DivisorQuotientRemovable
import RHV3Lean.Objects.P4Port.Analysis.Complex.Divisor
import RHV3Lean.Objects.P4Port.Topology.MetricSpace.Annulus
import RHV3Lean.Objects.P4Port.Analysis.Complex.HadamardFactorization
import RHV3Lean.Objects.P4Port.Analysis.Complex.ValueDistribution.LogCounting.Basic
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.Log.PosLog
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.Exp
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.Log.ExpGrowth
import RHV3Lean.Objects.P4Port.Analysis.Complex.ValueDistribution.LogCounting.Growth
import RHV3Lean.Objects.P4Port.Analysis.Meromorphic.DivisorHolomorphic
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.Log.Dyadic
import RHV3Lean.Objects.P4Port.Analysis.Complex.HadamardFactorization.Summability
import RHV3Lean.Objects.P4Port.Analysis.Complex.AbsMax
import RHV3Lean.Objects.P4Port.Analysis.Complex.CartanBound
import RHV3Lean.Objects.P4Port.Analysis.Complex.CartanInverseFactorBound
import RHV3Lean.Objects.P4Port.Analysis.Complex.CartanMajorantBound
import RHV3Lean.Objects.P4Port.Analysis.Complex.CartanProductBound
import RHV3Lean.Objects.P4Port.Analysis.Complex.BorelCaratheodory
import RHV3Lean.Objects.P4Port.Analysis.Complex.ExpPoly
import RHV3Lean.Objects.P4Port.Analysis.Complex.ExpPoly.Growth
import RHV3Lean.Objects.P4Port.Analysis.Complex.HadamardFactorization.Growth
import RHV3Lean.Objects.P4Port.Analysis.Complex.HadamardFactorization.Order
import RHV3Lean.Objects.P4Port.Analysis.Calculus.Deriv.Polynomial
import RHV3Lean.Objects.P4Port.Analysis.Complex.Basic
import RHV3Lean.Objects.P4Port.Analysis.Complex.Trigonometric
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.Gamma.IntegralBounds
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.GammaBounds
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.Gamma.GammaStirlingAux
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.Gamma.StripBounds
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.Pow.Real
import RHV3Lean.Objects.P4Port.NumberTheory.LSeries.RiemannZeta
import RHV3Lean.Objects.P4Port.Analysis.Complex.Convex
import RHV3Lean.Objects.P4Port.MeasureTheory.Integral.IntegrableOn
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.ImproperIntegrals
import RHV3Lean.Objects.P4Port.Algebra.Order.Floor.Ring
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.Pow.Deriv
import RHV3Lean.Objects.P4Port.MeasureTheory.Integral.IntervalIntegral.Basic
import RHV3Lean.Objects.P4Port.NumberTheory.LSeries.RiemannZetaAbelKernel
import RHV3Lean.Objects.P4Port.NumberTheory.AbelSummation
import RHV3Lean.Objects.P4Port.NumberTheory.LSeries.RiemannZetaPartialSum
import RHV3Lean.Objects.P4Port.NumberTheory.LSeries.RiemannZetaAbelContinuation
import RHV3Lean.Objects.P4Port.NumberTheory.LSeries.RiemannZetaConvexity
import RHV3Lean.Objects.P4Port.NumberTheory.LSeries.RiemannZetaStripBound
import RHV3Lean.Objects.P4Port.NumberTheory.LSeries.ZetaFiniteOrder
import RHV3Lean.Objects.P4Port.NumberTheory.LSeries.RiemannZetaValues
import RHV3Lean.Objects.P4Port.NumberTheory.LSeries.RiemannZetaHadamard
import RHV3Lean.Objects.P4Port.Analysis.SpecialFunctions.Gamma.DigammaSeries
import RHV3Lean.Objects.P4Port.IEANTN.ZetaDefinitions
import RHV3Lean.Objects.P4Port.IEANTN.HadamardLogDerivative
import RHV3Lean.Objects.ZetaXiHadamardP4_4aExactContract
import RHV3Lean.Objects.PerronPort.Auxiliary
import RHV3Lean.Objects.PerronPort.LogBasic
import RHV3Lean.Objects.PerronPort.EulerMaclaurin
import RHV3Lean.Objects.PerronPort.ZetaBounds
import RHV3Lean.Objects.P4Port.Analysis.Complex.HadamardCounting
import RHV3Lean.Objects.ZetaZeroCountingCrude
import RHV3Lean.Objects.P4Port.IEANTN.KadiriZeroCounting
import RHV3Lean.Objects.ZetaPerronFiniteResidues
import RHV3Lean.Objects.ZetaZeroHeightTruncation
import RHV3Lean.Objects.ZetaZeroHeightSummability
import RHV3Lean.Objects.ZetaZeroHeightPerronBridge
import RHV3Lean.Objects.ZetaPerronAdmissibleHeights
import RHV3Lean.Objects.ZetaQuantitativeGoodHeightsP4_4b
import RHV3Lean.Objects.ZetaHorizontalLogDerivBoundP4_4c
import RHV3Lean.Objects.ZetaHorizontalPerronVanishingP4_4d
import RHV3Lean.Objects.ZetaLeftVerticalPerronVanishingP4_4e
import RHV3Lean.Objects.ZetaTrivialZeroSimplicityP4_5
import RHV3Lean.Objects.ZetaTrivialZeroResidueSeriesP4_5
import RHV3Lean.Objects.ZetaNontrivialZeroResidueSeriesP4_5
import RHV3Lean.Objects.ZetaP4_5Closure
import RHV3Lean.Objects.ZetaSmoothedExplicitFormulaP4_6
import RHV3Lean.Objects.ZetaSmoothedZeroFormulaP5
import RHV3Lean.Objects.ZetaSmoothedUnsmoothingP5
import RHV3Lean.Objects.ZetaSmoothedUnsmoothingArithmeticBridge

/-!
# RHV3Lean — racine active

La route normative et sa matrice L01–L30 sont dans
`docs/RH_STRATEGIE_LEAN.md`. Cette racine compile toute la surface publique,
mais les imports ne constituent pas une certification de route.

## ACTIVE_EXACT

`AlgebraicAxis`, `PrimeGapGrammar`, `PrimeTransitionGrammar`, `TrueZero`,
`ZeroGapGrammar`, `FunctionalMirror`, `OffFibreAndPassage`, `Triple`,
`ZetaRealSegment`, `UpperRepresentative`.

## ACTIVE_PARTIAL / TO_REWRITE

`HarmonicTower`, `ContactsAndCell`, `CountingRigidity`,
`VonMangoldtChebyshev`, `TrueTowerState`, `TrueTowerCarrier`,
`CanonicalTowerOperator`, `PrimeOccurrence`, `Passage`, `PlaceAndLocalLaw`,
`TransportOnOperator`, `Universalization`.

Leur compilation garantit les corps présents, jamais les producteurs encore
absents : Tour canonique causale, T1 sur sa cellule, reconstruction depuis la
source zéro, transport T2 et R-PASS relationnel complet.

## CONTROL_ONLY / LEGACY

`CanonicalWindowRule`, `RatioFourStateControl`, `SamePrimeCollision`,
`TripleTransitionRigidity`, `TerminalCoreStrength` restent importés pour le
replay et les audits de force. Aucun theorem final ne peut dépendre d'eux comme
substitut d'un producteur actif.

La cible terminale demeure un theorem sans argument scientifique :

```lean
RiemannHypothesis_proved : RiemannHypothesis
```

Elle n'est exportable qu'après production de toutes les arêtes L01–L30 et
contrôle de leur identité SAME_MEMBER/SAME_PASSAGE/SAME_OCCURRENCE/SAME_HISTORY.
-/
