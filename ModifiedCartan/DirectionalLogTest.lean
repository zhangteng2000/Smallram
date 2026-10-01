import ModifiedCartan.DirectionalComplexLog

open scoped Topology ContDiff
open Filter Set MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

theorem complex_directional_test_inequality {U : Set ℂ} (hU : IsOpen U)
    {L : ℂ → ℂ} (hL : ContDiffOn ℝ 1 L U) (w : ℂ)
    (hsign : ∀ z ∈ U, (fderiv ℝ L z w).re - (fderiv ℝ L z (Complex.I * w)).im ≤ 0)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφpos : ∀ z, 0 ≤ φ z) :
    (∫ z, (L z).im * fderiv ℝ φ z (Complex.I * w)) ≤ ∫ z, (L z).re * fderiv ℝ φ z w := by
  have hσ : ContDiffOn ℝ 1 (fun z => (L z).re) U := Complex.reCLM.contDiff.comp_contDiffOn hL
  have hτ : ContDiffOn ℝ 1 (fun z => (L z).im) U := Complex.imCLM.contDiff.comp_contDiffOn hL
  rw [integral_mul_test_fderiv_of_contDiffOn hU hτ hφ hφc hφU (Complex.I * w),
    integral_mul_test_fderiv_of_contDiffOn hU hσ hφ hφc hφU w]
  apply neg_le_neg
  have hσd : ContinuousOn (fun z => fderiv ℝ (fun y => (L y).re) z w) U :=
    (hσ.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hτd : ContinuousOn (fun z => fderiv ℝ (fun y => (L y).im) z (Complex.I * w)) U :=
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
    exact mul_le_mul_of_nonneg_right (sub_nonpos.mp (hsign z hz)) (hφpos z)
  · have hzφ : z ∉ tsupport φ := fun hh => hz (hφU hh)
    rw [image_eq_zero_of_notMem_tsupport hzφ, mul_zero, mul_zero]

theorem directional_regularized_clog_test_inequality {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (a w : ℂ) {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ z ∈ U, ((classicalComplexGradient f z - a) * w).re ≤ 0)
    (hΔ : ∀ z ∈ U, 0 ≤ Laplacian.laplacian f z)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφpos : ∀ z, 0 ≤ φ z) :
    (∫ z, (Complex.log ((ε : ℂ) - (classicalComplexGradient f z - a) * w)).im *
      fderiv ℝ φ z (Complex.I * w)) ≤
      ∫ z, (Complex.log ((ε : ℂ) - (classicalComplexGradient f z - a) * w)).re * fderiv ℝ φ z w := by
  have hL : ContDiffOn ℝ 1 (fun z => Complex.log ((ε : ℂ) - (classicalComplexGradient f z - a) * w)) U := by
    intro z hz
    have hlog : ContDiffAt ℝ 1 Complex.log ((ε : ℂ) - (classicalComplexGradient f z - a) * w) :=
      (Complex.contDiffAt_log (regularized_sub_mem_slitPlane hε (hg z hz))).restrict_scalars ℝ
    exact (hlog.comp z (contDiff_const.sub
      (((contDiff_one_classicalComplexGradient hf).sub contDiff_const).mul contDiff_const)).contDiffAt).contDiffWithinAt
  exact complex_directional_test_inequality hU hL w
    (fun z hz => directional_regularized_clog_nonpos hf a w hε (hg z hz) (hΔ z hz)) hφ hφc hφU hφpos

end ModifiedCartan
#print axioms ModifiedCartan.directional_regularized_clog_test_inequality
