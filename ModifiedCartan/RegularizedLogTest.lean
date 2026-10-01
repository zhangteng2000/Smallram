import ModifiedCartan.RegularizedComplexLog

open scoped Topology ContDiff
open Filter Set MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

theorem contDiff_one_classicalComplexGradient {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (classicalComplexGradient f) := by
  have hc (w : ℂ) : ContDiff ℝ 1 (fun z => fderiv ℝ f z w) :=
    (contDiff_one_fderiv_of_two hf).clm_apply contDiff_const
  exact (Complex.ofRealCLM.contDiff.comp (hc 1)).sub
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hc Complex.I)))

theorem contDiffOn_regularized_clog_gradient {U : Set ℂ} {f : ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ z ∈ U, (classicalComplexGradient f z).re ≤ 0) :
    ContDiffOn ℝ 1 (fun z => Complex.log ((ε : ℂ) - classicalComplexGradient f z)) U := by
  intro z hz
  have hlog : ContDiffAt ℝ 1 Complex.log ((ε : ℂ) - classicalComplexGradient f z) :=
    (Complex.contDiffAt_log (regularized_sub_mem_slitPlane hε (hg z hz))).restrict_scalars ℝ
  exact (hlog.comp z (contDiff_const.sub (contDiff_one_classicalComplexGradient hf)).contDiffAt).contDiffWithinAt

theorem fderiv_complex_re_apply {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) (w : ℂ) :
    fderiv ℝ (fun y => (g y).re) z w = (fderiv ℝ g z w).re := by
  have he := congrArg (fun A : ℂ →L[ℝ] ℝ => A w)
    (Complex.reCLM.hasFDerivAt.comp z hg.hasFDerivAt).fderiv
  simpa [Function.comp_def] using! he

theorem fderiv_complex_im_apply {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) (w : ℂ) :
    fderiv ℝ (fun y => (g y).im) z w = (fderiv ℝ g z w).im := by
  have he := congrArg (fun A : ℂ →L[ℝ] ℝ => A w)
    (Complex.imCLM.hasFDerivAt.comp z hg.hasFDerivAt).fderiv
  simpa [Function.comp_def] using! he

/-- Integration by parts turns the pointwise logarithm inequality into the
test inequality required for passage to the nonsmooth weak gradient. -/
theorem regularized_clog_gradient_test_inequality {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ z ∈ U, (classicalComplexGradient f z).re ≤ 0)
    (hΔ : ∀ z ∈ U, 0 ≤ Laplacian.laplacian f z)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφpos : ∀ z, 0 ≤ φ z) :
    (∫ z, (Complex.log ((ε : ℂ) - classicalComplexGradient f z)).im * fderiv ℝ φ z Complex.I) ≤
      ∫ z, (Complex.log ((ε : ℂ) - classicalComplexGradient f z)).re * fderiv ℝ φ z 1 := by
  let L : ℂ → ℂ := fun z => Complex.log ((ε : ℂ) - classicalComplexGradient f z)
  have hL : ContDiffOn ℝ 1 L U := contDiffOn_regularized_clog_gradient hf hε hg
  have hσ : ContDiffOn ℝ 1 (fun z => (L z).re) U := Complex.reCLM.contDiff.comp_contDiffOn hL
  have hτ : ContDiffOn ℝ 1 (fun z => (L z).im) U := Complex.imCLM.contDiff.comp_contDiffOn hL
  change (∫ z, (L z).im * fderiv ℝ φ z Complex.I) ≤ ∫ z, (L z).re * fderiv ℝ φ z 1
  rw [integral_mul_test_fderiv_of_contDiffOn hU hτ hφ hφc hφU Complex.I,
    integral_mul_test_fderiv_of_contDiffOn hU hσ hφ hφc hφU 1]
  apply neg_le_neg
  have hσd : ContinuousOn (fun z => fderiv ℝ (fun y => (L y).re) z 1) U :=
    (hσ.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hτd : ContinuousOn (fun z => fderiv ℝ (fun y => (L y).im) z Complex.I) U :=
    (hτ.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  apply integral_mono_ae
    (integrable_mul_test_of_continuousOn hU hσd hφ.continuous hφc hφU)
    (integrable_mul_test_of_continuousOn hU hτd hφ.continuous hφc hφU)
  apply Eventually.of_forall
  intro z
  dsimp only
  by_cases hz : z ∈ U
  · have hd := (hL.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero
    rw [fderiv_complex_re_apply hd, fderiv_complex_im_apply hd]
    apply mul_le_mul_of_nonneg_right _ (hφpos z)
    exact sub_nonpos.mp (regularized_clog_bar_derivative_nonpos hf hε (hg z hz) (hΔ z hz))
  · have hzφ : z ∉ tsupport φ := fun hh => hz (hφU hh)
    rw [image_eq_zero_of_notMem_tsupport hzφ, mul_zero, mul_zero]

end ModifiedCartan
#print axioms ModifiedCartan.regularized_clog_gradient_test_inequality
