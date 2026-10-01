import ModifiedCartan.ScalarActualTargetLimits
import ModifiedCartan.AnalyticLogCircleLimits

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Constructed circle-mean limits for the original fixed-target components.
Auxiliary to LaTeX `thm:A` (b). -/
theorem ScalarTargetLogLimitData.exists_actual_target_circle_limit
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} {d : ArbitraryRadiusLimitData f r ρ}
    {β : WithTop ℂ} (e : ScalarTargetLogLimitData d β)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop)
    (hA : (Real.pi / 2) * (2 : ℝ) ^ ρ ≤ d.A) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ t : ℝ, 0 < t → t < 2 →
      Tendsto (fun ν => (characteristic f (r (d.subseq (ns ν))))⁻¹ *
        Real.circleAverage (fun z =>
          Real.log ‖scalarActualTarget f β (r (d.subseq (ns ν))) (d.gauge (ns ν)) z‖) 0 t)
        atTop (𝓝 (Real.circleAverage (fun z => (e.u z).toReal) 0 t)) := by
  obtain ⟨ns, hns, hfn, hlim⟩ := e.exists_actual_target_log_limit hρ hr hA
  exact ⟨ns, hns, normalized_analytic_log_circleAverage_tendsto
    (fun ν => (hfn ν).1) (fun ν => (hfn ν).2) (fun ν => d.scale_pos (ns ν))
    hlim (e.regular.2.continuousOn.mono (ball_subset_ball (by norm_num)))⟩

end ModifiedCartan
#print axioms ModifiedCartan.ScalarTargetLogLimitData.exists_actual_target_circle_limit
