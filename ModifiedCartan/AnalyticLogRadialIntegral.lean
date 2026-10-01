import ModifiedCartan.AnalyticLogCircleMean
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open scoped Topology
open Filter Set Metric MeasureTheory MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

/-- Polar integration of an analytic logarithm uses its locally integrable
representative, so zeros on circles cause no exception. -/
theorem integral_ball_log_norm_eq_radial_mean {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    (∫ z in ball (0 : ℂ) R, Real.log ‖f z‖) =
      2 * Real.pi * ∫ t in (0 : ℝ)..R,
        t * Real.circleAverage (fun z => Real.log ‖f z‖) 0 t := by
  classical
  let F : ℂ → ℂ := (closedBall (0 : ℂ) R).piecewise f (fun _ => 0)
  have hm : Measurable F :=
    hf.continuousOn.measurable_piecewise continuousOn_const measurableSet_closedBall
  have he : EqOn F f (closedBall (0 : ℂ) R) := fun _ hz => piecewise_eq_of_mem _ _ _ hz
  have hi : IntegrableOn (fun z => Real.log ‖f z‖) (ball (0 : ℂ) R) :=
    (integrableOn_log_norm_on_compact hf (Subset.refl _) (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall
  have hiF : IntegrableOn (fun z => Real.log ‖F z‖) (ball (0 : ℂ) R) :=
    hi.congr_fun (fun z hz => by rw [he (ball_subset_closedBall hz)]) measurableSet_ball
  have heint : (∫ z in ball (0 : ℂ) R, Real.log ‖f z‖) =
      ∫ z in ball (0 : ℂ) R, Real.log ‖F z‖ := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    dsimp only
    rw [he (ball_subset_closedBall hz)]
  rw [heint, integral_ball_eq_circleAverage (H := fun z => Real.log ‖F z‖) (Real.measurable_log.comp hm.norm) hiF,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le hR.le
  intro t ht
  have hmF : Real.circleAverage (fun z => Real.log ‖F z‖) 0 t =
      Real.circleAverage (fun z => Real.log ‖f z‖) 0 t := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hzR : z ∈ closedBall (0 : ℂ) R := by
      rw [abs_of_pos ht.1] at hz
      exact closedBall_subset_closedBall ht.2.le (sphere_subset_closedBall hz)
    dsimp only
    rw [he hzR]
  dsimp only
  rw [hmF]
  ring

/-- The radial weight removes the possible logarithmic singularity at radius zero. -/
theorem analytic_log_circleAverage_weighted_integrable {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (ho : ∀ z : closedBall (0 : ℂ) R, meromorphicOrderAt f z ≠ ⊤) :
    IntervalIntegrable (fun t => t * Real.circleAverage (fun z => Real.log ‖f z‖) 0 t)
      volume 0 R := by
  obtain ⟨S, w, C, _, he⟩ := analytic_log_circleAverage_finite_formula hf ho
  have hk (a : ℂ) : ContinuousOn (fun t : ℝ => t * Real.log (max t ‖a‖)) (Icc 0 R) := by
    by_cases ha : a = 0
    · subst a
      exact Real.continuous_mul_log.continuousOn.congr (fun t ht => by
        simp only [norm_zero, max_eq_left ht.1])
    · exact continuousOn_id.mul ((continuousOn_id.sup continuousOn_const).log
        (fun t _ => ne_of_gt ((norm_pos_iff.mpr ha).trans_le (le_max_right _ _))))
  have hc : ContinuousOn (fun t : ℝ => (∑ a ∈ S, w a * (t * Real.log (max t ‖a‖))) + C * t)
      (Icc 0 R) :=
    by
      apply ContinuousOn.add _ (continuousOn_const.mul continuousOn_id)
      apply continuousOn_finsetSum
      intro a _
      exact continuousOn_const.mul (hk a)
  apply (hc.congr ?_).intervalIntegrable_of_Icc hR.le
  intro t ht
  dsimp only
  rcases ht.1.eq_or_lt with ht0 | ht0
  · simp [← ht0]
  · rw [he t ht0 ht.2, mul_add, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro a _
      ring
    · ring

end ModifiedCartan
#print axioms ModifiedCartan.integral_ball_log_norm_eq_radial_mean
#print axioms ModifiedCartan.analytic_log_circleAverage_weighted_integrable
