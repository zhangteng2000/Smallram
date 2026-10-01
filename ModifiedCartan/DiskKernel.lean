import ModifiedCartan.DiskAverages
import ModifiedCartan.HarmonicSmoothing

open scoped Topology ENNReal Convolution
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

noncomputable def diskKernel (r : ℝ) : ℂ → ℝ :=
  (ball 0 r).indicator (fun _ => (Real.pi * r ^ 2)⁻¹)

theorem diskKernel_nonneg (r : ℝ) (z : ℂ) : 0 ≤ diskKernel r z := by
  classical
  by_cases hz : z ∈ ball (0 : ℂ) r
  · simp only [diskKernel, indicator_of_mem hz]
    exact inv_nonneg.mpr (mul_nonneg Real.pi_pos.le (sq_nonneg r))
  · simp [diskKernel, hz]

theorem norm_diskKernel_le (r : ℝ) (z : ℂ) : ‖diskKernel r z‖ ≤ (Real.pi * r ^ 2)⁻¹ := by
  classical
  rw [Real.norm_eq_abs, abs_of_nonneg (diskKernel_nonneg r z)]
  by_cases hz : z ∈ ball (0 : ℂ) r
  · simp [diskKernel, hz]
  · simpa only [diskKernel, indicator_of_notMem hz] using
      inv_nonneg.mpr (mul_nonneg Real.pi_pos.le (sq_nonneg r))

theorem diskKernel_neg (r : ℝ) (z : ℂ) : diskKernel r (-z) = diskKernel r z := by
  classical
  have hneg : -z ∈ ball (0 : ℂ) r ↔ z ∈ ball (0 : ℂ) r := by
    simp only [mem_ball, dist_zero_right, norm_neg]
  by_cases hz : z ∈ ball (0 : ℂ) r
  · simp [diskKernel, hz, hneg.mpr hz]
  · simp [diskKernel, hz, mt hneg.mp hz]

theorem diskKernel_hasCompactSupport (r : ℝ) : HasCompactSupport (diskKernel r) := by
  apply (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  by_contra hnot
  have hb : z ∉ ball (0 : ℂ) r := fun h => hnot (ball_subset_closedBall h)
  exact hz (by simp [diskKernel, hb])

theorem diskKernel_integrable (r : ℝ) : Integrable (diskKernel r) := by
  have hvol : volume (ball (0 : ℂ) r) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : ℂ) r).measure_lt_top
  have : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) r)) := ⟨by simpa using hvol⟩
  have hint : IntegrableOn (fun _ : ℂ => (Real.pi * r ^ 2)⁻¹) (ball (0 : ℂ) r) := integrable_const _
  exact hint.integrable_indicator isOpen_ball.measurableSet

theorem diskKernel_integral {r : ℝ} (hr : 0 < r) : (∫ z, diskKernel r z) = 1 := by
  rw [diskKernel, integral_indicator isOpen_ball.measurableSet, setIntegral_const, smul_eq_mul]
  change (volume (ball (0 : ℂ) r)).toReal * (Real.pi * r ^ 2)⁻¹ = 1
  rw [complex_ball_real_volume 0 hr.le]
  exact mul_inv_cancel₀ (ne_of_gt (mul_pos Real.pi_pos (sq_pos_of_pos hr)))

theorem diskKernel_eval_sub (r : ℝ) (c a : ℂ) :
    diskKernel r (c - a) = (ball c r).indicator (fun _ => (Real.pi * r ^ 2)⁻¹) a := by
  classical
  have hmem : c - a ∈ ball (0 : ℂ) r ↔ a ∈ ball c r := by
    simp only [mem_ball, dist_eq_norm, sub_zero]
    rw [norm_sub_rev]
  unfold diskKernel
  by_cases ha : a ∈ ball c r
  · rw [indicator_of_mem (hmem.mpr ha), indicator_of_mem ha]
  · rw [indicator_of_notMem (mt hmem.mp ha), indicator_of_notMem ha]

theorem diskAverage_eq_scalarConvolution {r : ℝ} (hr : 0 ≤ r) (f : ℂ → ℝ) (c : ℂ) :
    diskAverage r f c = scalarConvolution f (diskKernel r) c := by
  classical
  rw [diskAverage_eq hr, scalarConvolution_eq_integral]
  have heq : (fun a => f a • diskKernel r (c - a)) =
      (ball c r).indicator (fun a => (Real.pi * r ^ 2)⁻¹ * f a) := by
    funext a
    rw [diskKernel_eval_sub]
    by_cases ha : a ∈ ball c r
    · simp only [indicator_of_mem ha, smul_eq_mul, mul_comm]
    · simp only [indicator_of_notMem ha, smul_zero]
  rw [heq, integral_indicator isOpen_ball.measurableSet, integral_const_mul]

theorem diskAverage_integrable {r : ℝ} (hr : 0 ≤ r) {f : ℂ → ℝ} (hf : Integrable f) :
    Integrable (diskAverage r f) := by
  have heq : diskAverage r f = scalarConvolution f (diskKernel r) :=
    funext (diskAverage_eq_scalarConvolution hr f)
  rw [heq]
  exact hf.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (diskKernel_integrable r)

theorem integral_diskAverage {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ} (hf : Integrable f) :
    (∫ z, diskAverage r f z) = ∫ z, f z := by
  simp_rw [diskAverage_eq_scalarConvolution hr.le, scalarConvolution]
  rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf (diskKernel_integrable r),
    diskKernel_integral hr]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_one]


end ModifiedCartan

