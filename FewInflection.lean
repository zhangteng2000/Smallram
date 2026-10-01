import FewInflection.Definitions
import FewInflection.Results
import FewInflection.TargetSnapshot
import FewInflection.Gauge
import FewInflection.GaugeTranscendental
import FewInflection.ScalarGauge
import FewInflection.Jensen
import FewInflection.Nevanlinna
import FewInflection.WronskianRegularity
import FewInflection.VectorJensen
import FewInflection.GrowthBasics
import FewInflection.FundamentalOperator
import FewInflection.FundamentalAnalytic
import FewInflection.LogDerivativeFacts
import FewInflection.MatrixGaugeBounds
import FewInflection.GaugeFundamental
import FewInflection.RationalGauge
import FewInflection.ScalarWronskian
import FewInflection.ScalarGaugeRamification
import FewInflection.Dilation
import FewInflection.AffineDilation
import FewInflection.FundamentalDilation
import FewInflection.FundamentalAffineDilation
import FewInflection.WronskianLimits
import FewInflection.FundamentalLimits
import FewInflection.LogDerivativeRecursion
import FewInflection.CanonicalGauge
import FewInflection.AnalyticLogBranch
import FewInflection.CanonicalLocalGauge
import FewInflection.PolynomialSpaces
import FewInflection.DerivativeMinors
import FewInflection.DerivativeMinorRatios
import FewInflection.PluckerBounds
import FewInflection.PolynomialJets
import FewInflection.PolynomialRootMinors
import FewInflection.MeasureConvergence
import FewInflection.InitialBasis
import FewInflection.InitialBasisLimits
import FewInflection.PolynomialGauge
import FewInflection.EntireTaylor
import FewInflection.TaylorLimits
import FewInflection.DerivativeMinorLimits
import FewInflection.PolynomialGrowth
import FewInflection.GrowthFoundations
import FewInflection.Growth.PowerBounds
import FewInflection.Growth.SharpnessBounds
import FewInflection.Growth.Scaling
import FewInflection.Growth.Transfer
import FewInflection.Nevanlinna.CountingBounds
import FewInflection.Nevanlinna.PoissonKernelBounds
import FewInflection.Nevanlinna.CountingCharacteristic
import FewInflection.Nevanlinna.BoundaryMean
import FewInflection.Nevanlinna.FiniteSingularSums
import FewInflection.Nevanlinna.PoissonJensen
import FewInflection.Nevanlinna.PoissonDerivative
import FewInflection.Nevanlinna.PoissonLogFactor
import FewInflection.Nevanlinna.PoissonLogDerivative
import FewInflection.Nevanlinna.CanonicalKernels
import FewInflection.Nevanlinna.PoissonJensenDerivative
import FewInflection.Nevanlinna.PoissonBoundaryBounds
import FewInflection.Nevanlinna.BoundaryMeanBounds
import FewInflection.Nevanlinna.PoissonLogDerivativeBound
import FewInflection.Nevanlinna.AbsoluteDivisorCount
import FewInflection.Nevanlinna.CharacteristicMassBound
import FewInflection.Nevanlinna.PoissonHigherDerivative
import FewInflection.ExplicitExamples
import FewInflection.ExplicitHigherDim
import FewInflection.ExplicitExponentialFamily

/-!
The root module exports the formal definitions and the target propositions for
the paper.  A small executable check below verifies the concrete Wronskian
calculation at projective dimension one.
-/

namespace FewInflection

example (z : ℂ) :
    wronskian 1 (monomialFamily 1) z =
      ∏ j : Index 1, (Nat.factorial (j : ℕ) : ℂ) :=
  wronskian_monomialFamily 1 z

end FewInflection

