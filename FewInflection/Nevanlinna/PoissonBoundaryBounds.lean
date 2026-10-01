import FewInflection.Nevanlinna.PoissonJensenDerivative
import FewInflection.Nevanlinna.BoundaryMean

/-!
# The boundary term in the fixed-radius logarithmic-derivative bound

The differentiated Poisson kernel is uniformly bounded on the closed unit
disk when the boundary radius is between two and three. Its circle integral
is controlled by the absolute boundary log mean, which is then bounded by
the characteristic and the explicit logarithm of the central value.
-/

open scoped Topology
open Complex Filter MeasureTheory MeromorphicOn Metric Real Set

namespace FewInflection

theorem norm_circleAverage_le_of_norm_le
    {F : ℂ → ℂ} {b : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hb : CircleIntegrable b c R)
    (hbound : ∀ ζ ∈ sphere c |R|, ‖F ζ‖ ≤ b ζ) :
    ‖Real.circleAverage F c R‖ ≤ Real.circleAverage b c R := by
  simp only [Real.circleAverage_def, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr Real.two_pi_pos), smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.two_pi_pos.le)
  apply intervalIntegral.norm_integral_le_of_norm_le Real.two_pi_pos.le
  · filter_upwards [] with θ hθ
    exact hbound _ (circleMap_mem_sphere' c R θ)
  · exact hb

theorem poisson_first_derivative_kernel_le_six
    {R : ℝ} (hR2 : 2 < R) (hR3 : R < 3) {z ζ : ℂ}
    (hz : ‖z‖ ≤ 1) (hζ : ζ ∈ sphere 0 R) :
    ‖2 * ζ / (ζ - z) ^ 2‖ ≤ 6 := by
  have hζnorm : ‖ζ‖ = R := by simpa using hζ
  have hden : 1 < ‖ζ - z‖ := by
    have hd := norm_sub_norm_le ζ z
    rw [hζnorm] at hd
    linarith
  rw [norm_div, norm_mul, Complex.norm_ofNat, norm_pow, hζnorm]
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < ‖ζ - z‖))).mpr
  nlinarith [sq_nonneg (‖ζ - z‖ - 1)]

theorem norm_circleAverage_poisson_first_derivative_le
    {f : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hR2 : 2 < R) (hR3 : R < 3) (hz : ‖z‖ ≤ 1)
    (hf : MeromorphicOn f (sphere 0 R)) :
    ‖Real.circleAverage (fun ζ : ℂ =>
        (2 * ζ / (ζ - z) ^ 2) * (Real.log ‖f ζ‖ : ℂ)) 0 R‖ ≤
      6 * Real.circleAverage (fun ζ : ℂ => |Real.log ‖f ζ‖|) 0 R := by
  have hR : 0 < R := by linarith
  have hint := hf.circleIntegrable_log_norm_of_nonneg hR.le
  have hint6 : CircleIntegrable ((6 : ℝ) • fun ζ : ℂ =>
      |Real.log ‖f ζ‖|) 0 R :=
    CircleIntegrable.const_smul (a := (6 : ℝ)) hint.abs
  have h := norm_circleAverage_le_of_norm_le
    (b := (6 : ℝ) • fun ζ : ℂ => |Real.log ‖f ζ‖|) hint6
    (F := fun ζ : ℂ =>
      (2 * ζ / (ζ - z) ^ 2) * (Real.log ‖f ζ‖ : ℂ)) (fun ζ hζ => ?_)
  · simpa only [Real.circleAverage_smul, smul_eq_mul] using h
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (poisson_first_derivative_kernel_le_six hR2 hR3 hz
        (by simpa [abs_of_pos hR] using hζ)) (abs_nonneg _)

end FewInflection
