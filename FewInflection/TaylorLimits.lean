import FewInflection.EntireTaylor
import FewInflection.DerivativeMinorLimits
import FewInflection.FundamentalLimits
import FewInflection.InitialBasisLimits
import FewInflection.WronskianLimits
import FewInflection.MeasureConvergence

/-!
# Derivative convergence of entire Taylor approximants

Locally uniform convergence of holomorphic functions controls every fixed
derivative jet.  This module instantiates the general Wronskian-limit lemma
with the Taylor polynomial sequence from `EntireTaylor`.
-/

open scoped Topology
open Filter Set MeasureTheory

namespace FewInflection

noncomputable section

theorem tendsto_taylorPolynomial_iteratedDeriv_of_entire
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a z : ℂ) (k : ℕ) :
    Tendsto
      (fun N => iteratedDeriv k
        (fun w : ℂ => (taylorPolynomial f a N).eval w) z) atTop
      (𝓝 (iteratedDeriv k f z)) := by
  apply tendsto_iteratedDeriv_of_locallyUniformlyOn_at
    isOpen_univ (Set.mem_univ z)
    (tendstoLocallyUniformlyOn_taylorPolynomial_eval_of_entire hf a)
  exact Filter.Eventually.of_forall (fun N =>
    (taylorPolynomial f a N).differentiable)

theorem tendsto_taylorPolynomial_wronskian_of_entire
    {n : ℕ} {f : Index n → ℂ → ℂ}
    (hf : ∀ j : Index n, Differentiable ℂ (f j)) (a z : ℂ) :
    Tendsto
      (fun N => wronskian n
        (fun j w => (taylorPolynomial (f j) a N).eval w) z) atTop
      (𝓝 (wronskian n f z)) := by
  apply tendsto_wronskian_of_locallyUniformlyOn
    isOpen_univ (Set.mem_univ z)
  · intro j
    exact tendstoLocallyUniformlyOn_taylorPolynomial_eval_of_entire (hf j) a
  · exact Filter.Eventually.of_forall (fun N j =>
      (taylorPolynomial (f j) a N).differentiable)

theorem tendsto_taylorPolynomial_iteratedDeriv_on_ball
    {f : ℂ → ℂ} {a : ℂ} {R : NNReal} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall a (R : ℝ)))
    (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun N z => iteratedDeriv k
        (fun w : ℂ => (taylorPolynomial f a N).eval w) z)
      (iteratedDeriv k f) atTop (Metric.ball a (R : ℝ)) := by
  apply tendstoLocallyUniformlyOn_iteratedDeriv_of_differentiableOn
    Metric.isOpen_ball
    (tendstoLocallyUniformlyOn_taylorPolynomial_eval_on_ball hR hf)
  exact Filter.Eventually.of_forall (fun N =>
    (taylorPolynomial f a N).differentiableOn)

/-! The same finite-continuity argument applies to every prescribed list of
derivative orders, not only to the consecutive orders in a Wronskian. -/
theorem tendsto_taylorPolynomial_derivativeMinor_of_entire
    {n : ℕ} {orders : Index n → ℕ}
    {f : Index n → ℂ → ℂ}
    (hf : ∀ j : Index n, Differentiable ℂ (f j)) (a z : ℂ) :
    Tendsto
      (fun N => derivativeMinor orders
        (fun j w => (taylorPolynomial (f j) a N).eval w) z) atTop
      (𝓝 (derivativeMinor orders f z)) := by
  apply tendsto_derivativeMinor_of_tendsto_iteratedDeriv
  intro i j
  exact tendsto_taylorPolynomial_iteratedDeriv_of_entire
    (hf j) a z (orders i)

theorem tendsto_taylorPolynomial_derivativeMinor_on_ball
    {n : ℕ} {orders : Index n → ℕ}
    {f : Index n → ℂ → ℂ} {a : ℂ} {R : NNReal} (hR : 0 < R)
    (hf : ∀ j : Index n,
      DifferentiableOn ℂ (f j) (Metric.closedBall a (R : ℝ)))
    {z : ℂ} (hz : z ∈ Metric.ball a (R : ℝ)) :
    Tendsto
      (fun N => derivativeMinor orders
        (fun j w => (taylorPolynomial (f j) a N).eval w) z) atTop
      (𝓝 (derivativeMinor orders f z)) := by
  apply tendsto_derivativeMinor_of_tendsto_iteratedDeriv
  intro i j
  exact (tendsto_taylorPolynomial_iteratedDeriv_on_ball
    (f := f j) (a := a) hR (hf j) (orders i)).tendsto_at hz

theorem tendsto_taylorPolynomial_fundamentalCoefficients_of_entire
    {n : ℕ} {f : Index n → ℂ → ℂ}
    (hf : ∀ j : Index n, Differentiable ℂ (f j)) (a z : ℂ)
    (hW : wronskian n f z ≠ 0) :
    Tendsto
      (fun N => fundamentalCoefficients n
        (fun j w => (taylorPolynomial (f j) a N).eval w) z) atTop
      (𝓝 (fundamentalCoefficients n f z)) := by
  apply tendsto_fundamentalCoefficients_of_tendsto_iteratedDeriv (hjet := ?_) hW
  intro k j
  exact tendsto_taylorPolynomial_iteratedDeriv_of_entire
    (hf j) a z k

theorem tendsto_taylorPolynomial_fundamentalCoefficients_on_ball
    {n : ℕ} {f : Index n → ℂ → ℂ} {a : ℂ} {R : NNReal}
    (hR : 0 < R)
    (hf : ∀ j : Index n,
      DifferentiableOn ℂ (f j) (Metric.closedBall a (R : ℝ)))
    {z : ℂ} (hz : z ∈ Metric.ball a (R : ℝ))
    (hW : wronskian n f z ≠ 0) :
    Tendsto
      (fun N => fundamentalCoefficients n
        (fun j w => (taylorPolynomial (f j) a N).eval w) z) atTop
      (𝓝 (fundamentalCoefficients n f z)) := by
  apply tendsto_fundamentalCoefficients_of_tendsto_iteratedDeriv (hjet := ?_) hW
  intro k j
  exact (tendsto_taylorPolynomial_iteratedDeriv_on_ball
    (f := f j) (a := a) hR (hf j) k).tendsto_at hz

theorem tendsto_taylorPolynomial_initialBasis_of_entire
    {n : ℕ} {f : Index n → ℂ → ℂ}
    (hf : ∀ j : Index n, Differentiable ℂ (f j)) (a x : ℂ)
    (hW : wronskian n f a ≠ 0) (j : Index n) :
    Tendsto
      (fun N => initialBasis
        (fun k w => (taylorPolynomial (f k) a N).eval w) a j x) atTop
      (𝓝 (initialBasis f a j x)) := by
  apply tendsto_initialBasis_of_tendsto_iteratedDeriv (hW := hW) (j := j)
  · intro i k
    exact tendsto_taylorPolynomial_iteratedDeriv_of_entire
      (hf k) a a i
  · intro k
    exact tendsto_taylorPolynomial_eval_of_entire (hf k) a x

theorem tendsto_taylorPolynomial_initialBasis_on_ball
    {n : ℕ} {f : Index n → ℂ → ℂ} {a : ℂ} {R : NNReal}
    (hR : 0 < R)
    (hf : ∀ j : Index n,
      DifferentiableOn ℂ (f j) (Metric.closedBall a (R : ℝ)))
    {x : ℂ} (hx : x ∈ Metric.ball a (R : ℝ))
    (hW : wronskian n f a ≠ 0) (j : Index n) :
    Tendsto
      (fun N => initialBasis
        (fun k w => (taylorPolynomial (f k) a N).eval w) a j x) atTop
      (𝓝 (initialBasis f a j x)) := by
  apply tendsto_initialBasis_of_tendsto_iteratedDeriv (hW := hW) (j := j)
  · intro i k
    exact (tendsto_taylorPolynomial_iteratedDeriv_on_ball
      (f := f k) (a := a) hR (hf k) i).tendsto_at
        (Metric.mem_ball_self hR)
  · intro k
    exact (tendstoLocallyUniformlyOn_taylorPolynomial_eval_on_ball
      (f := f k) (a := a) hR (hf k)).tendsto_at hx

theorem eventually_taylorPolynomial_wronskian_ne_zero_of_entire
    {n : ℕ} {f : Index n → ℂ → ℂ}
    (hf : ∀ j : Index n, Differentiable ℂ (f j)) (a z : ℂ)
    (hW : wronskian n f z ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      wronskian n
        (fun j w => (taylorPolynomial (f j) a N).eval w) z ≠ 0 := by
  exact (tendsto_taylorPolynomial_wronskian_of_entire hf a z).eventually_ne hW

theorem eventually_taylorPolynomial_derivativeMinor_ne_zero_of_entire
    {n : ℕ} {orders : Index n → ℕ}
    {f : Index n → ℂ → ℂ}
    (hf : ∀ j : Index n, Differentiable ℂ (f j)) (a z : ℂ)
    (hminor : derivativeMinor orders f z ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      derivativeMinor orders
        (fun j w => (taylorPolynomial (f j) a N).eval w) z ≠ 0 := by
  exact (tendsto_taylorPolynomial_derivativeMinor_of_entire hf a z).eventually_ne
    hminor

theorem tendstoInMeasure_taylorPolynomial_eval_closedBall
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) (R : ℝ)
    {μ : Measure ℂ} :
    TendstoInMeasure (μ.restrict (Metric.closedBall a R))
      (fun N z => (taylorPolynomial f a N).eval z) atTop f := by
  exact tendstoInMeasure_restrict_of_tendstoUniformlyOn
    Metric.isClosed_closedBall.measurableSet
    (tendstoUniformlyOn_taylorPolynomial_eval_closedBall hf a R)

theorem tendstoInMeasure_taylorPolynomial_eval_on_subdisk
    {f : ℂ → ℂ} {a : ℂ} {r R : NNReal} (hR : 0 < R) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall a (R : ℝ)))
    {μ : Measure ℂ} :
    TendstoInMeasure (μ.restrict (Metric.closedBall a (r : ℝ)))
      (fun N z => (taylorPolynomial f a N).eval z) atTop f := by
  exact tendstoInMeasure_restrict_of_tendstoUniformlyOn
    Metric.isClosed_closedBall.measurableSet
    (tendstoUniformlyOn_taylorPolynomial_eval_on_subdisk hR hrR hf)

theorem tendstoInMeasure_taylorPolynomial_iteratedDeriv_on_subdisk
    {f : ℂ → ℂ} {a : ℂ} {r R : NNReal} (hR : 0 < R) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall a (R : ℝ))) (k : ℕ)
    {μ : Measure ℂ} :
    TendstoInMeasure (μ.restrict (Metric.closedBall a (r : ℝ)))
      (fun N z => iteratedDeriv k
        (fun w : ℂ => (taylorPolynomial f a N).eval w) z) atTop
      (iteratedDeriv k f) := by
  have hloc := tendsto_taylorPolynomial_iteratedDeriv_on_ball
    (f := f) (a := a) hR hf k
  have hsub : Metric.closedBall a (r : ℝ) ⊆ Metric.ball a (R : ℝ) := by
    apply Metric.closedBall_subset_ball
    exact_mod_cast hrR
  have hunif : TendstoUniformlyOn
      (fun N z => iteratedDeriv k
        (fun w : ℂ => (taylorPolynomial f a N).eval w) z)
      (iteratedDeriv k f) atTop (Metric.closedBall a (r : ℝ)) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (ProperSpace.isCompact_closedBall a (r : ℝ))).mp (hloc.mono hsub)
  exact tendstoInMeasure_restrict_of_tendstoUniformlyOn
    Metric.isClosed_closedBall.measurableSet hunif

end

end FewInflection
