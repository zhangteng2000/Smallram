import ModifiedCartan.ClassicalGradientLaplacian
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open scoped Topology ContDiff
open Filter Set MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

theorem regularized_sub_mem_slitPlane {g : ℂ → ℂ} {z : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hg : (g z).re ≤ 0) : (ε : ℂ) - g z ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

theorem fderiv_regularized_clog_apply {g : ℂ → ℂ} {z : ℂ} {ε : ℝ}
    (hg : DifferentiableAt ℝ g z) (hε : 0 < ε) (hgre : (g z).re ≤ 0) (w : ℂ) :
    fderiv ℝ (fun y => Complex.log ((ε : ℂ) - g y)) z w =
      -((ε : ℂ) - g z)⁻¹ * fderiv ℝ g z w := by
  have hd := (Complex.hasStrictFDerivAt_log_real
    (regularized_sub_mem_slitPlane hε hgre)).hasFDerivAt.comp z
    ((hasFDerivAt_const (ε : ℂ) z).sub hg.hasFDerivAt)
  have he := congrArg (fun A : ℂ →L[ℝ] ℂ => A w) hd.fderiv
  simpa [Function.comp_def, Pi.sub_apply, mul_neg] using! he

/-- The real part of twice the antiholomorphic derivative of a regularized
logarithm has the required sign when the complex gradient lies in a half-plane. -/
theorem regularized_clog_bar_derivative_nonpos {f : ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) {z : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hg : (classicalComplexGradient f z).re ≤ 0) (hΔ : 0 ≤ Laplacian.laplacian f z) :
    (fderiv ℝ (fun y => Complex.log ((ε : ℂ) - classicalComplexGradient f y)) z 1).re -
      (fderiv ℝ (fun y => Complex.log ((ε : ℂ) - classicalComplexGradient f y)) z Complex.I).im ≤ 0 := by
  let g := classicalComplexGradient f
  let L : ℂ → ℂ := fun y => Complex.log ((ε : ℂ) - g y)
  have hd := (hasFDerivAt_classicalComplexGradient hf z).differentiableAt
  have heq : fderiv ℝ L z 1 + Complex.I * fderiv ℝ L z Complex.I =
      -((ε : ℂ) - g z)⁻¹ * (Laplacian.laplacian f z : ℂ) := by
    dsimp only [L]
    rw [fderiv_regularized_clog_apply hd hε hg, fderiv_regularized_clog_apply hd hε hg]
    rw [← classicalComplexGradient_bar_derivative hf z]
    dsimp only [g]
    ring
  have hpos : 0 ≤ (((ε : ℂ) - g z)⁻¹).re := by
    rw [Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp only [Complex.sub_re, Complex.ofReal_re]
    exact sub_nonneg.mpr (hg.trans hε.le)
  have hreal := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hreal
  change (fderiv ℝ L z 1).re - (fderiv ℝ L z Complex.I).im ≤ 0
  nlinarith [mul_nonneg hpos hΔ]

end ModifiedCartan
#print axioms ModifiedCartan.regularized_clog_bar_derivative_nonpos
