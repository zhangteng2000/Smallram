import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.JensenFormula

/-!
# The finite Poisson--Jensen formula

The formula is proved for a function meromorphic in a neighborhood of a
closed disk, at an analytic nonzero interior point. The boundary is assumed
free of zeros and poles. The proof uses Mathlib's proved extended canonical
decomposition and the Poisson formula for the harmonic logarithm of its
nonvanishing analytic factor. Multiplicities are the actual meromorphic
divisor, and the sum has finite support.
-/

open scoped Topology ComplexConjugate BigOperators
open Complex Filter Function MeromorphicOn Metric Real Set

namespace FewInflection

theorem divisor_sphere_eq_zero_of_regular_boundary
    {f : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicOn f (closedBall 0 R))
    (hboundary : ∀ z ∈ sphere 0 R, AnalyticAt ℂ f z ∧ f z ≠ 0) :
    divisor f (sphere 0 R) = 0 := by
  ext z
  by_cases hz : z ∈ sphere 0 R
  · rw [(hf.mono_set sphere_subset_closedBall).divisor_apply hz]
    have ho : meromorphicOrderAt f z = 0 := by
      rw [(hboundary z hz).1.meromorphicOrderAt_eq,
        (hboundary z hz).1.analyticOrderAt_eq_zero.mpr (hboundary z hz).2]
      rfl
    simp [ho]
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz

/-- The precise scalar Poisson--Jensen formula. `canonicalFactor` is the
reciprocal of the factor used in the paper, hence the minus sign. -/
theorem poisson_jensen_log_norm
    {f : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hf : MeromorphicOn f (closedBall 0 R))
    (hboundary : ∀ w ∈ sphere 0 R, AnalyticAt ℂ f w ∧ f w ≠ 0)
    (hz : z ∈ ball 0 R) (hfz : AnalyticAt ℂ f z) (hfz0 : f z ≠ 0) :
    Real.log ‖f z‖ =
      Real.circleAverage (fun w => poissonKernel 0 z w * Real.log ‖f w‖) 0 R -
        ∑ᶠ a, (divisor f (ball 0 R) a : ℝ) *
          Real.log ‖canonicalFactor R a z‖ := by
  have hR : 0 < R := pos_of_mem_ball hz
  have hzorder : meromorphicOrderAt f z = 0 := by
    rw [hfz.meromorphicOrderAt_eq, hfz.analyticOrderAt_eq_zero.mpr hfz0]
    rfl
  have hzfinite : meromorphicOrderAt f z ≠ (⊤ : WithTop ℤ) := by
    rw [hzorder]
    exact WithTop.coe_ne_top
  have hfinite : ∀ w : closedBall (0 : ℂ) R, meromorphicOrderAt f w ≠ ⊤ := by
    intro w
    exact hf.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) R).isPreconnected (ball_subset_closedBall hz)
      w.property hzfinite
  obtain ⟨g, D⟩ := hf.exists_ecanonicalDecomp hfinite
  have hdiv := divisor_sphere_eq_zero_of_regular_boundary hf hboundary
  have hlog_boundary : ∀ w ∈ sphere 0 R, Real.log ‖g w‖ = Real.log ‖f w‖ := by
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
      · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem
          (divisor f (ball 0 R)) ha]
    simpa [hdiv, hsum,
      (hboundary w hw).1.meromorphicTrailingCoeffAt_of_ne_zero (hboundary w hw).2]
      using heq
  have hgH : InnerProductSpace.HarmonicOnNhd (fun w => Real.log ‖g w‖)
      (closedBall 0 R) := by
    intro w hw
    exact (D.analyticOnNhd w hw).harmonicAt_log_norm (D.ne_zero w hw)
  have hpoisson := hgH.circleAverage_poissonKernel_smul hz
  have hintegral :
      Real.circleAverage (fun w => poissonKernel 0 z w * Real.log ‖f w‖) 0 R =
        Real.log ‖g z‖ := by
    calc
      _ = Real.circleAverage (poissonKernel 0 z • (fun w => Real.log ‖g w‖)) 0 R := by
        apply Real.circleAverage_congr_sphere
        intro w hw
        have hw' : w ∈ sphere 0 R := by simpa [abs_of_pos hR] using hw
        change poissonKernel 0 z w * Real.log ‖f w‖ =
          poissonKernel 0 z w * Real.log ‖g w‖
        rw [hlog_boundary w hw']
      _ = _ := hpoisson
  have heq := D.log_norm_eq (ball_subset_closedBall hz) hzorder hR
  rw [hintegral]
  have heq' : Real.log ‖g z‖ =
      (∑ᶠ a, (divisor f (ball 0 R) a : ℝ) * Real.log ‖canonicalFactor R a z‖) +
        Real.log ‖f z‖ := by
    simpa [hdiv, hfz.meromorphicTrailingCoeffAt_of_ne_zero hfz0] using heq
  linarith

end FewInflection
