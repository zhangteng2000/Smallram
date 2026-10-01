import ModifiedCartan.DiskKernel

open scoped Topology ENNReal Convolution
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem diskKernel_sub_comm (r : ℝ) (x y : ℂ) : diskKernel r (x - y) = diskKernel r (y - x) := by
  rw [← neg_sub y x, diskKernel_neg]

/-- Fubini and the even disk kernel move an average between the two factors. -/
theorem integral_mul_diskAverage {r : ℝ} (hr : 0 ≤ r) {f χ : ℂ → ℝ}
    (hf : Integrable f) (hχ : AEStronglyMeasurable χ volume)
    {C : ℝ} (hχbound : ∀ z, ‖χ z‖ ≤ C) :
    (∫ z, χ z * diskAverage r f z) = ∫ z, f z * diskAverage r χ z := by
  have hbase := hf.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) (diskKernel_integrable r)
  have hjoint : Integrable (fun p : ℂ × ℂ => χ p.1 * (f p.2 * diskKernel r (p.1 - p.2)))
      (volume.prod volume) := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      hbase.bdd_mul hχ.comp_fst (Eventually.of_forall (fun p => hχbound p.1))
  simp_rw [diskAverage_eq_scalarConvolution hr, scalarConvolution_eq_integral, smul_eq_mul]
  calc
    _ = ∫ x : ℂ, ∫ y : ℂ, χ x * (f y * diskKernel r (x - y)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => (integral_const_mul (χ x) _).symm)
    _ = ∫ y : ℂ, ∫ x : ℂ, χ x * (f y * diskKernel r (x - y)) := integral_integral_swap hjoint
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      change (∫ x : ℂ, χ x * (f y * diskKernel r (x - y))) =
        f y * ∫ x : ℂ, χ x * diskKernel r (y - x)
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      change χ x * (f y * diskKernel r (x - y)) = f y * (χ x * diskKernel r (y - x))
      rw [diskKernel_sub_comm r x y]
      ring

theorem norm_diskAverage_le_of_bound {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ}
    {C : ℝ} (hbound : ∀ z, ‖f z‖ ≤ C) (c : ℂ) : ‖diskAverage r f c‖ ≤ C := by
  have harea : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  have hvol : volume (ball c r) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall c r).measure_lt_top
  have hint := norm_setIntegral_le_of_norm_le_const_ae hvol (Eventually.of_forall hbound)
  change ‖∫ z in ball c r, f z‖ ≤ C * (volume (ball c r)).toReal at hint
  rw [complex_ball_real_volume c hr.le] at hint
  rw [diskAverage_eq hr.le, norm_mul,
    show ‖(Real.pi * r ^ 2)⁻¹‖ = (Real.pi * r ^ 2)⁻¹ from by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr harea)]]
  calc
    _ ≤ (Real.pi * r ^ 2)⁻¹ * (C * (Real.pi * r ^ 2)) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr harea.le)
    _ = C := by field_simp


end ModifiedCartan
