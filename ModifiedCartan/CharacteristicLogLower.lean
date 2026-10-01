import ModifiedCartan.ZeroJensenLowerBound
import ModifiedCartan.ScalarCurveBounds
import ModifiedCartan.PeakScaleBounds

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- A logarithmic lower bound derived from Jensen and an actual scalar
linear combination vanishing at zero. This is used only at the positive
peak orders in the alternative normalization argument for `prop:indices`. -/
theorem characteristic_log_lower_of_transcendental {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) :
    ∃ C : ℝ, ∀ r, 1 ≤ r → Real.log r - C ≤ characteristic f r := by
  obtain ⟨H, M, hH, hHnonzero, hHzero, hM, hb⟩ := exists_scalar_zero_of_transcendental f htrans
  refine ⟨Real.log M + Real.log (euclideanNorm (f.vector 0)) -
    Real.log ‖meromorphicTrailingCoeffAt H 0‖, ?_⟩
  intro r hr
  have hlo := scalar_logarithmic_circle_lower_bound hH hHnonzero hHzero hr
  have hhi := scalar_circle_log_le_curve_mean f hH hHnonzero hM hb (zero_lt_one.trans_le hr)
  unfold characteristic
  linarith

theorem characteristic_tendsto_atTop_of_transcendental {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) : Tendsto (characteristic f) atTop atTop := by
  obtain ⟨C, hC⟩ := characteristic_log_lower_of_transcendental f htrans
  have ht : Tendsto (fun r : ℝ => Real.log r - C) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-C) Real.tendsto_log_atTop
  exact tendsto_atTop_mono' atTop ((eventually_ge_atTop 1).mono (fun r hr => hC r hr)) ht

theorem characteristic_unbounded_of_transcendental {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) :
    ∀ M : ℝ, ∃ r : ℝ, 0 < r ∧ M < characteristic f r := by
  intro M
  exact ((eventually_gt_atTop (0 : ℝ)).and
    ((characteristic_tendsto_atTop_of_transcendental f htrans).eventually_gt_atTop M)).exists

end
end ModifiedCartan
#print axioms ModifiedCartan.characteristic_log_lower_of_transcendental
#print axioms ModifiedCartan.characteristic_tendsto_atTop_of_transcendental
