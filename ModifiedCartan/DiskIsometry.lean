import ModifiedCartan.DiskAverages
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Complex.Isometry

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Translation and a real linear isometry preserve the disk integral,
with the disk center translated at the same time. -/
theorem integral_ball_affine_isometry (e : ℂ ≃ₗᵢ[ℝ] ℂ) (c : ℂ) (r : ℝ) (f : ℂ → ℝ) :
    (∫ z in ball (0 : ℂ) r, f (c + e z)) = ∫ z in ball c r, f z := by
  classical
  have hm (z : ℂ) : c + e z ∈ ball c r ↔ z ∈ ball (0 : ℂ) r := by
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, e.norm_map]
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  calc
    _ = ∫ z, (ball c r).indicator f (c + e z) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      dsimp only
      by_cases hz : z ∈ ball (0 : ℂ) r
      · rw [indicator_of_mem hz, indicator_of_mem ((hm z).mpr hz)]
      · rw [indicator_of_notMem hz, indicator_of_notMem (fun hh => hz ((hm z).mp hh))]
    _ = ∫ z, (ball c r).indicator f (c + z) :=
      MeasureTheory.integral_comp e (fun z => (ball c r).indicator f (c + z))
    _ = ∫ z, (ball c r).indicator f z := integral_add_left_eq_self _ c

theorem diskAverage_affine_isometry (e : ℂ ≃ₗᵢ[ℝ] ℂ) (c : ℂ) {r : ℝ}
    (hr : 0 ≤ r) (f : ℂ → ℝ) :
    diskAverage r (fun z => f (c + e z)) 0 = diskAverage r f c := by
  rw [diskAverage_eq hr, diskAverage_eq hr, integral_ball_affine_isometry]

end ModifiedCartan
#print axioms ModifiedCartan.integral_ball_affine_isometry
