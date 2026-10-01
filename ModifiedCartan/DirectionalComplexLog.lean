import ModifiedCartan.RegularizedLogTest
import ModifiedCartan.WeakGradientZeroTests

open scoped Topology ContDiff ComplexConjugate
open Filter Set MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

theorem complexCLM_apply_complex (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w = (w.re : ℂ) * L 1 + (w.im : ℂ) * L Complex.I := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im w).symm
  calc
    L w = L (w.re • (1 : ℂ) + w.im • Complex.I) := congrArg L hw
    _ = _ := by rw [map_add, map_smul, map_smul]; rfl

theorem complexCLM_rotated_trace (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w + Complex.I * L (Complex.I * w) = conj w * (L 1 + Complex.I * L Complex.I) := by
  rw [complexCLM_apply_complex L w, complexCLM_apply_complex L (Complex.I * w)]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem fderiv_shifted_gradient_mul_apply {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f)
    (a w z v : ℂ) :
    fderiv ℝ (fun y => (classicalComplexGradient f y - a) * w) z v =
      w * fderiv ℝ (classicalComplexGradient f) z v := by
  have hd := (((hasFDerivAt_classicalComplexGradient hf z).differentiableAt.hasFDerivAt.sub_const a).mul_const w)
  have he := congrArg (fun A : ℂ →L[ℝ] ℂ => A v) hd.fderiv
  simpa using! he

/-- The logarithm sign in an arbitrary real direction, for any extremal
gradient value. The squared norm factor is derived, not assumed. -/
theorem directional_regularized_clog_nonpos {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f)
    (a w : ℂ) {z : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hg : ((classicalComplexGradient f z - a) * w).re ≤ 0)
    (hΔ : 0 ≤ Laplacian.laplacian f z) :
    (fderiv ℝ (fun y => Complex.log ((ε : ℂ) - (classicalComplexGradient f y - a) * w)) z w).re -
      (fderiv ℝ (fun y => Complex.log ((ε : ℂ) - (classicalComplexGradient f y - a) * w)) z (Complex.I * w)).im ≤ 0 := by
  let g : ℂ → ℂ := fun y => (classicalComplexGradient f y - a) * w
  let L : ℂ → ℂ := fun y => Complex.log ((ε : ℂ) - g y)
  have hd : DifferentiableAt ℝ g z :=
    (((hasFDerivAt_classicalComplexGradient hf z).sub_const a).mul_const w).differentiableAt
  have hgder (v : ℂ) : fderiv ℝ g z v = w * fderiv ℝ (classicalComplexGradient f) z v :=
    fderiv_shifted_gradient_mul_apply hf a w z v
  have heq : fderiv ℝ L z w + Complex.I * fderiv ℝ L z (Complex.I * w) =
      -((ε : ℂ) - g z)⁻¹ * ((Complex.normSq w * Laplacian.laplacian f z : ℝ) : ℂ) := by
    dsimp only [L]
    rw [fderiv_regularized_clog_apply hd hε hg, fderiv_regularized_clog_apply hd hε hg,
      hgder w, hgder (Complex.I * w)]
    calc
      _ = -((ε : ℂ) - g z)⁻¹ * w *
          (fderiv ℝ (classicalComplexGradient f) z w +
            Complex.I * fderiv ℝ (classicalComplexGradient f) z (Complex.I * w)) := by ring
      _ = -((ε : ℂ) - g z)⁻¹ * w * (conj w * (Laplacian.laplacian f z : ℂ)) := by
        rw [complexCLM_rotated_trace, classicalComplexGradient_bar_derivative hf z]
      _ = _ := by rw [Complex.ofReal_mul, ← Complex.mul_conj w]; ring
  have hpos : 0 ≤ (((ε : ℂ) - g z)⁻¹).re := by
    rw [Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp only [Complex.sub_re, Complex.ofReal_re]
    exact sub_nonneg.mpr (hg.trans hε.le)
  have hreal := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hreal
  change (fderiv ℝ L z w).re - (fderiv ℝ L z (Complex.I * w)).im ≤ 0
  nlinarith [mul_nonneg hpos (mul_nonneg (Complex.normSq_nonneg w) hΔ)]

end ModifiedCartan
#print axioms ModifiedCartan.directional_regularized_clog_nonpos
