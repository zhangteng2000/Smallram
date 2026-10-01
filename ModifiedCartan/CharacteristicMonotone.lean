import ModifiedCartan.HerglotzNormalization
import Mathlib.Analysis.Complex.Harmonic.MeanValue

open scoped Topology
open Filter Set Metric InnerProductSpace
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Radial monotonicity of the manuscript's Euclidean characteristic.
This is a proved prerequisite of LaTeX `eq:index-order-bounds`. -/
theorem characteristic_monotoneOn {n : ℕ} (f : Curve n) :
    MonotoneOn (characteristic f) (Ioi 0) := by
  intro r hr R hR hrR
  rcases eq_or_lt_of_le hrR with rfl | hrR
  · exact le_rfl
  have hsub : closedBall (0 : ℂ) |r| ⊆ ball 0 R := by
    rw [abs_of_pos hr]
    exact closedBall_subset_ball hrR
  have hL : HarmonicOnNhd (fun z => (curveHerglotz f R z).re)
      (closedBall 0 |r|) := by
    intro z hz
    exact ((curveHerglotz_analytic f R) z (hsub hz)).harmonicAt_re
  have hmean := Real.circleAverage_mono
    (curve_log_euclideanNorm_continuous f).continuousOn.circleIntegrable'
    (hL.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
    (fun z hz => curve_log_norm_le_herglotz f (hsub (sphere_subset_closedBall hz)))
  rw [hL.circleAverage_eq, curveHerglotz_re_zero f hR] at hmean
  exact sub_le_sub_right hmean _

end
end ModifiedCartan
#print axioms ModifiedCartan.characteristic_monotoneOn
