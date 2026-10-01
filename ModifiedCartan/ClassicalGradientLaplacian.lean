import ModifiedCartan.WeakGradientCalculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open scoped Topology ContDiff
open Filter Set MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

theorem hasFDerivAt_classicalComplexGradient {f : ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) (z : ℂ) :
    HasFDerivAt (classicalComplexGradient f)
      (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) z).flip 1) -
        Complex.I • Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) z).flip Complex.I)) z := by
  have hdf := contDiff_one_fderiv_of_two hf
  have hc (w : ℂ) : HasFDerivAt (fun y => fderiv ℝ f y w)
      ((fderiv ℝ (fderiv ℝ f) z).flip w) z := by
    simpa using ((hdf.differentiable_one z).hasFDerivAt.clm_apply (hasFDerivAt_const w z))
  exact ((Complex.ofRealCLM.hasFDerivAt.comp z (hc 1)).sub
    ((Complex.ofRealCLM.hasFDerivAt.comp z (hc Complex.I)).const_mul Complex.I))

theorem fderiv_classicalComplexGradient_apply {f : ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) (z w : ℂ) :
    fderiv ℝ (classicalComplexGradient f) z w =
      (fderiv ℝ (fderiv ℝ f) z w 1 : ℂ) -
        Complex.I * (fderiv ℝ (fderiv ℝ f) z w Complex.I : ℂ) := by
  rw [(hasFDerivAt_classicalComplexGradient hf z).fderiv]
  rfl

/-- Twice the antiholomorphic derivative of the actual complex gradient
equals the real Laplacian. The imaginary part vanishes by Schwarz symmetry. -/
theorem classicalComplexGradient_bar_derivative {f : ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) (z : ℂ) :
    fderiv ℝ (classicalComplexGradient f) z 1 +
      Complex.I * fderiv ℝ (classicalComplexGradient f) z Complex.I =
      (Laplacian.laplacian f z : ℂ) := by
  have hs := (hf.contDiffAt (x := z)).isSymmSndFDerivAt (by norm_num) (1 : ℂ) Complex.I
  have hΔ : Laplacian.laplacian f z =
      fderiv ℝ (fderiv ℝ f) z 1 1 +
        fderiv ℝ (fderiv ℝ f) z Complex.I Complex.I := by
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply]
    rfl
  rw [fderiv_classicalComplexGradient_apply hf, fderiv_classicalComplexGradient_apply hf, hΔ]
  apply Complex.ext <;> simp [hs]

end ModifiedCartan
#print axioms ModifiedCartan.classicalComplexGradient_bar_derivative
