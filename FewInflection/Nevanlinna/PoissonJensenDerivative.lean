import FewInflection.Nevanlinna.PoissonLogFactor
import FewInflection.Nevanlinna.CanonicalKernels

/-!
# Differentiated Poisson--Jensen formula

At a regular boundary radius the extended canonical decomposition has no
boundary divisor. Its zero-free analytic factor has the same boundary log
norm as the original function. Combining its proved Poisson derivative
formula with the finite divisor kernels gives the meromorphic logarithmic
derivative on a codiscrete subset of the disk.
-/

open scoped BigOperators ComplexConjugate Topology
open Complex Filter Function MeromorphicOn Metric Real Set

namespace FewInflection

theorem ecanonicalDecomp_log_norm_boundary
    {f g : ℂ → ℂ} {R : ℝ} (D : ECanonicalDecomp f g R) (hR : 0 < R)
    (hboundary : ∀ w ∈ sphere 0 R, AnalyticAt ℂ f w ∧ f w ≠ 0) :
    ∀ w ∈ sphere 0 R, Real.log ‖g w‖ = Real.log ‖f w‖ := by
  have hdiv := divisor_sphere_eq_zero_of_regular_boundary D.meromorphicOn hboundary
  intro w hw
  have hwo : meromorphicOrderAt f w = 0 := by
    rw [(hboundary w hw).1.meromorphicOrderAt_eq,
      (hboundary w hw).1.analyticOrderAt_eq_zero.mpr (hboundary w hw).2]
    rfl
  have heq := D.log_norm_eq (sphere_subset_closedBall hw) hwo hR
  have hsum : (∑ᶠ a, (divisor f (ball 0 R) a : ℝ) *
      Real.log ‖canonicalFactor R a w‖) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro a
    by_cases ha : a ∈ ball 0 R
    · rw [norm_canonicalFactor_eval_circle_eq_one ha hw]
      simp
    · simp [locallyFinsuppWithin.apply_eq_zero_of_notMem
        (divisor f (ball 0 R)) ha]
  simpa [hdiv, hsum,
    (hboundary w hw).1.meromorphicTrailingCoeffAt_of_ne_zero (hboundary w hw).2]
    using heq

theorem ecanonicalDecomp_to_canonicalDecomp_of_regular_boundary
    {f g : ℂ → ℂ} {R : ℝ} (D : ECanonicalDecomp f g R)
    (hboundary : ∀ w ∈ sphere 0 R, AnalyticAt ℂ f w ∧ f w ≠ 0) :
    CanonicalDecomp f g R := by
  have hdiv := divisor_sphere_eq_zero_of_regular_boundary D.meromorphicOn hboundary
  refine ⟨D.meromorphicOn, D.analyticOnNhd.meromorphicNFOn,
    fun w hw => D.ne_zero w (ball_subset_closedBall hw), ?_⟩
  simpa [hdiv] using D.eventuallyEq

/-- Exact differentiated Poisson--Jensen formula for a given canonical factor.
The factor is eliminated from the conclusion using equality of boundary log
norms; its existence is supplied by the next theorem. -/
theorem ecanonicalDecomp_logDeriv_poisson_jensen_eventuallyEq
    {f g : ℂ → ℂ} {R : ℝ} (D : ECanonicalDecomp f g R) (hR : 0 < R)
    (hboundary : ∀ w ∈ sphere 0 R, AnalyticAt ℂ f w ∧ f w ≠ 0) :
    logDeriv f =ᶠ[codiscreteWithin (ball 0 R)]
      (fun z =>
        (∑ᶠ a, (divisor f (ball 0 R) a : ℂ) *
          ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))) +
        Real.circleAverage (fun ζ : ℂ =>
          (2 * ζ / (ζ - z) ^ 2) * (Real.log ‖f ζ‖ : ℂ)) 0 R) := by
  have hD := ecanonicalDecomp_to_canonicalDecomp_of_regular_boundary D hboundary
  have hb := ecanonicalDecomp_log_norm_boundary D hR hboundary
  filter_upwards [canonicalDecomp_logDeriv_kernels_eventuallyEq hD hR,
    self_mem_codiscreteWithin (ball (0 : ℂ) R)] with z hz hzin
  rw [hz, logDeriv_eq_circleAverage_poisson_derivative_of_nonvanishing
    D.analyticOnNhd D.ne_zero hzin]
  congr 1
  apply Real.circleAverage_congr_sphere
  intro ζ hζ
  dsimp only
  rw [hb ζ (by simpa [abs_of_pos hR] using hζ)]

/-- The meromorphic formula itself, derived from Mathlib's proved canonical
decomposition. The nonzero analytic center rules out the identically zero
case; all zeros and poles enter through their actual divisor multiplicities. -/
theorem logDeriv_poisson_jensen_eventuallyEq
    {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MeromorphicOn f (closedBall 0 R))
    (hf0 : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hboundary : ∀ w ∈ sphere 0 R, AnalyticAt ℂ f w ∧ f w ≠ 0) :
    logDeriv f =ᶠ[codiscreteWithin (ball 0 R)]
      (fun z =>
        (∑ᶠ a, (divisor f (ball 0 R) a : ℂ) *
          ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))) +
        Real.circleAverage (fun ζ : ℂ =>
          (2 * ζ / (ζ - z) ^ 2) * (Real.log ‖f ζ‖ : ℂ)) 0 R) := by
  have horder : meromorphicOrderAt f 0 = 0 := by
    rw [hf0.meromorphicOrderAt_eq, hf0.analyticOrderAt_eq_zero.mpr h0]
    rfl
  have hfinite : ∀ w : closedBall (0 : ℂ) R, meromorphicOrderAt f w ≠ ⊤ := by
    intro w
    exact hf.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) R).isPreconnected
      (mem_closedBall_self hR.le) w.property (by simp [horder])
  obtain ⟨g, D⟩ := hf.exists_ecanonicalDecomp hfinite
  exact ecanonicalDecomp_logDeriv_poisson_jensen_eventuallyEq D hR hboundary

end FewInflection
