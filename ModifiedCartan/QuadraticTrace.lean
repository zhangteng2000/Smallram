import ModifiedCartan.WeakGradientZeroTests
import Mathlib.Analysis.InnerProductSpace.Laplacian

open scoped Topology
set_option autoImplicit false
namespace ModifiedCartan

theorem complex_bilinear_coordinates (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (z w : ℂ) :
    B z w = z.re * w.re * B 1 1 + z.re * w.im * B 1 Complex.I +
      z.im * w.re * B Complex.I 1 + z.im * w.im * B Complex.I Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  calc
    B z w = B (z.re • (1 : ℂ) + z.im • Complex.I) w := by rw [← hz]
    _ = z.re * B 1 w + z.im * B Complex.I w := by
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
    _ = _ := by
      rw [realCLM_apply_complex (B 1), realCLM_apply_complex (B Complex.I)]
      ring

/-- Two perpendicular quadratic evaluations recover the trace; no symmetry
assumption on the real bilinear map is needed. -/
theorem complex_bilinear_quarter_turn (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (z : ℂ) :
    B z z + B (Complex.I * z) (Complex.I * z) =
      ‖z‖ ^ 2 * (B 1 1 + B Complex.I Complex.I) := by
  rw [complex_bilinear_coordinates B z z,
    complex_bilinear_coordinates B (Complex.I * z) (Complex.I * z)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub, zero_add, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- A coordinate bound for the real bilinear operator norm. -/
theorem norm_complex_bilinear_le_coordinates (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :
    ‖B‖ ≤ |B 1 1| + |B 1 Complex.I| + |B Complex.I 1| + |B Complex.I Complex.I| := by
  let C := |B 1 1| + |B 1 Complex.I| + |B Complex.I 1| + |B Complex.I Complex.I|
  have hC : 0 ≤ C := by positivity
  apply ContinuousLinearMap.opNorm_le_bound B hC
  intro z
  apply ContinuousLinearMap.opNorm_le_bound (B z) (mul_nonneg hC (norm_nonneg _))
  intro w
  have hb : ‖B z w‖ ≤
      |z.re| * |w.re| * |B 1 1| + |z.re| * |w.im| * |B 1 Complex.I| +
      |z.im| * |w.re| * |B Complex.I 1| + |z.im| * |w.im| * |B Complex.I Complex.I| := by
    rw [complex_bilinear_coordinates]
    calc
      _ ≤ ‖z.re * w.re * B 1 1‖ + ‖z.re * w.im * B 1 Complex.I‖ +
          ‖z.im * w.re * B Complex.I 1‖ + ‖z.im * w.im * B Complex.I Complex.I‖ :=
        (norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ = _ := by simp only [norm_mul, Real.norm_eq_abs]
  calc
    _ ≤ _ := hb
    _ ≤ ‖z‖ * ‖w‖ * |B 1 1| + ‖z‖ * ‖w‖ * |B 1 Complex.I| +
        ‖z‖ * ‖w‖ * |B Complex.I 1| + ‖z‖ * ‖w‖ * |B Complex.I Complex.I| := by
      gcongr <;> first | exact Complex.abs_re_le_norm _ | exact Complex.abs_im_le_norm _
    _ = C * ‖z‖ * ‖w‖ := by dsimp only [C]; ring

theorem second_derivative_quarter_turn (f : ℂ → ℝ) (c z : ℂ) :
    iteratedFDeriv ℝ 2 f c (fun _ => z) +
      iteratedFDeriv ℝ 2 f c (fun _ => Complex.I * z) =
        ‖z‖ ^ 2 * Laplacian.laplacian f c := by
  simpa [iteratedFDeriv_two_apply,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane] using
      complex_bilinear_quarter_turn (fderiv ℝ (fderiv ℝ f) c) z

end ModifiedCartan
#print axioms ModifiedCartan.second_derivative_quarter_turn
