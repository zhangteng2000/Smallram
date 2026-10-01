import ModifiedCartan.WeakGradient
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.InnerProductSpace.Laplacian

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Distributional Laplacians for the Riesz-measure step in
`lem:logderivlimit`. Polar integration and the fundamental theorem of calculus
prove the kernel identity. Fubini proves the finite-measure potential identity. -/

theorem integrable_polar_weight {f : ℂ → ℝ} (hm : Measurable f) (hi : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm p))
      polarCoord.target := by
  have hc : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  refine ⟨(measurable_fst.mul (hm.comp hc.measurable)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    _ = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 * ‖f (Complex.polarCoord.symm p)‖ₑ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (by rw [polarCoord_target]; measurability)] with p hp
      rw [enorm_mul, Real.enorm_of_nonneg hp.1.le]
    _ = ∫⁻ z : ℂ, ‖f z‖ₑ := Complex.lintegral_comp_polarCoord_symm (fun z => ‖f z‖ₑ)
    _ < ⊤ := hasFiniteIntegral_iff_enorm.mp hi.2

noncomputable def polarRay (θ r : ℝ) : ℂ :=
  (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)

theorem polarRay_isometry (θ : ℝ) : Isometry (polarRay θ) := by
  apply isometry_iff_dist_eq.mpr
  intro r s
  simp only [polarRay, dist_eq_norm, ← sub_mul, ← Complex.ofReal_sub,
    norm_mul, Complex.ofReal_cos, Complex.ofReal_sin, Complex.norm_cos_add_sin_mul_I, mul_one, Complex.norm_real]

theorem test_polarRay_contDiff {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (θ : ℝ) :
    ContDiff ℝ 1 (fun r => φ (polarRay θ r)) :=
  hφ.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)

theorem test_polarRay_hasCompactSupport {φ : ℂ → ℝ} (hφ : HasCompactSupport φ) (θ : ℝ) :
    HasCompactSupport (fun r => φ (polarRay θ r)) :=
  hφ.comp_isClosedEmbedding (polarRay_isometry θ).isClosedEmbedding

theorem deriv_test_polarRay {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (θ r : ℝ) :
    deriv (fun t => φ (polarRay θ t)) r =
      fderiv ℝ φ (polarRay θ r) ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
  have hd : HasDerivAt (polarRay θ)
      ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) r := by
    change HasDerivAt (fun t : ℝ => (t : ℂ) *
      ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)) _ r
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const
        ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)
  exact ((hφ.differentiable_one (polarRay θ r)).hasFDerivAt.comp_hasDerivAt r hd).deriv

theorem integral_polarRay_fderiv {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (θ : ℝ) :
    (∫ r : ℝ in Ioi 0,
      fderiv ℝ φ (polarRay θ r) ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)) = -φ 0 := by
  have h := HasCompactSupport.integral_Ioi_deriv_eq
    (test_polarRay_contDiff hφ θ) (test_polarRay_hasCompactSupport hφc θ) 0
  simp_rw [deriv_test_polarRay hφ] at h
  simpa only [polarRay, Complex.ofReal_zero, zero_mul] using h

noncomputable def logGradientPair (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  (z⁻¹).re * fderiv ℝ φ z 1 + (-(z⁻¹).im) * fderiv ℝ φ z Complex.I

theorem measurable_logGradientPair {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Measurable (logGradientPair φ) := by
  have hc (v : ℂ) : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  exact (Complex.continuous_re.measurable.comp measurable_inv |>.mul (hc 1).measurable).add
    (Complex.continuous_im.measurable.comp measurable_inv |>.neg |>.mul (hc Complex.I).measurable)

theorem integrable_logGradientPair {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) : Integrable (logGradientPair φ) := by
  have hc (v : ℂ) : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  have h1 := locallyIntegrable_inv_re.integrable_smul_right_of_hasCompactSupport
    (hc 1) (hφc.fderiv_apply ℝ 1)
  have hI := locallyIntegrable_neg_inv_im.integrable_smul_right_of_hasCompactSupport
    (hc Complex.I) (hφc.fderiv_apply ℝ Complex.I)
  exact h1.fun_add hI

theorem polar_weight_logGradientPair (φ : ℂ → ℝ) (θ : ℝ) {r : ℝ} (hr : 0 < r) :
    r * logGradientPair φ (polarRay θ r) =
      fderiv ℝ φ (polarRay θ r) ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
  have hrep : ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) =
      Real.cos θ • (1 : ℂ) + Real.sin θ • Complex.I := by
    simp only [Complex.real_smul, mul_one]
  rw [hrep, map_add, map_smul, map_smul]
  have hre : (polarRay θ r).re = r * Real.cos θ := by
    simp only [polarRay, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him : (polarRay θ r).im = r * Real.sin θ := by
    simp only [polarRay, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hn : Complex.normSq (polarRay θ r) = r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    simp only [polarRay, norm_mul, Complex.ofReal_cos, Complex.ofReal_sin,
      Complex.norm_cos_add_sin_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  dsimp only [logGradientPair]
  rw [Complex.inv_re, Complex.inv_im, hn, hre, him]
  simp only [smul_eq_mul]
  field_simp

theorem integral_logGradientPair {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) :
    (∫ z : ℂ, logGradientPair φ z) = -(2 * Real.pi) * φ 0 := by
  have hi := integrable_polar_weight (measurable_logGradientPair hφ)
    (integrable_logGradientPair hφ hφc)
  rw [← Complex.integral_comp_polarCoord_symm (logGradientPair φ)]
  simp only [IntegrableOn, polarCoord_target, Measure.volume_eq_prod,
    ← Measure.prod_restrict, smul_eq_mul] at hi ⊢
  rw [integral_prod_symm _ hi]
  calc
    _ = ∫ θ : ℝ in Ioo (-Real.pi) Real.pi, ∫ r : ℝ in Ioi 0,
        fderiv ℝ φ (polarRay θ r) ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro θ
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      simpa only [Complex.polarCoord_symm_apply, polarRay, Complex.ofReal_cos, Complex.ofReal_sin] using
        polar_weight_logGradientPair φ θ hr
    _ = ∫ _θ : ℝ in Ioo (-Real.pi) Real.pi, -φ 0 := by
      simp_rw [integral_polarRay_fderiv hφ hφc]
    _ = _ := by
      rw [setIntegral_const, measureReal_def, ← Measure.real, Real.volume_real_Ioo_of_le
        (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
      simp only [smul_eq_mul]
      ring

theorem contDiff_one_fderiv_of_two {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 1 (fderiv ℝ φ) := by
  have h : ContDiff ℝ ((1 : ℕ∞ω) + 1) φ := by convert! hφ using 1
  exact (contDiff_succ_iff_fderiv.mp h).2.2

theorem laplacian_complex_eq_coordinate_derivatives {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (z : ℂ) :
    Laplacian.laplacian φ z = fderiv ℝ (fun w => fderiv ℝ φ w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ φ w Complex.I) z Complex.I := by
  have hdf := contDiff_one_fderiv_of_two hφ
  have heq (v : ℂ) : fderiv ℝ (fun w => fderiv ℝ φ w v) z v =
      fderiv ℝ (fderiv ℝ φ) z v v := by
    rw [fderiv_clm_apply (hdf.differentiable_one z) (differentiableAt_const v)]
    simp
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply, heq]
  rfl

theorem integral_log_norm_mul_laplacian {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ z : ℂ, Real.log ‖z‖ * Laplacian.laplacian φ z) = 2 * Real.pi * φ 0 := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hdf := contDiff_one_fderiv_of_two hφ
  have hd (v : ℂ) : ContDiff ℝ 1 (fun z => fderiv ℝ φ z v) :=
    hdf.clm_apply contDiff_const
  have hx := integrable_log_norm_mul_test_fderiv (hd 1) (hφc.fderiv_apply ℝ 1) 1
  have hy := integrable_log_norm_mul_test_fderiv (hd Complex.I)
    (hφc.fderiv_apply ℝ Complex.I) Complex.I
  have h1 : Integrable (fun z : ℂ => (z⁻¹).re * fderiv ℝ φ z 1) := by
    exact locallyIntegrable_inv_re.integrable_smul_right_of_hasCompactSupport
      (hd 1).continuous (hφc.fderiv_apply ℝ 1)
  have hI : Integrable (fun z : ℂ => (-(z⁻¹).im) * fderiv ℝ φ z Complex.I) := by
    exact locallyIntegrable_neg_inv_im.integrable_smul_right_of_hasCompactSupport
      (hd Complex.I).continuous (hφc.fderiv_apply ℝ Complex.I)
  simp_rw [laplacian_complex_eq_coordinate_derivatives hφ, mul_add]
  rw [integral_add hx hy,
    integral_log_norm_mul_fderiv_one (hd 1) (hφc.fderiv_apply ℝ 1),
    integral_log_norm_mul_fderiv_I (hd Complex.I) (hφc.fderiv_apply ℝ Complex.I),
    ← neg_add, ← integral_add h1 hI]
  change -(∫ z, logGradientPair φ z) = _
  rw [integral_logGradientPair hφ1 hφc]
  ring

theorem laplacian_comp_add_right_complex (φ : ℂ → ℝ) (a z : ℂ) :
    Laplacian.laplacian (fun w => φ (w + a)) z = Laplacian.laplacian φ (z + a) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_comp_add_right]

theorem integral_logKernel_mul_laplacian (a : ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ z : ℂ, Real.log ‖z - a‖ * Laplacian.laplacian φ z) = 2 * Real.pi * φ a := by
  have hψ : ContDiff ℝ 2 (fun z => φ (z + a)) := hφ.comp (contDiff_id.add contDiff_const)
  have hψc : HasCompactSupport (fun z => φ (z + a)) :=
    hφc.comp_homeomorph (Homeomorph.addRight a)
  have hs := integral_log_norm_mul_laplacian hψ hψc
  simp only [laplacian_comp_add_right_complex, zero_add] at hs
  calc
    _ = ∫ z : ℂ, Real.log ‖z‖ * Laplacian.laplacian φ (z + a) := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self
          (fun z : ℂ => Real.log ‖z - a‖ * Laplacian.laplacian φ z) a).symm
    _ = _ := hs

theorem continuous_laplacian_complex {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Continuous (Laplacian.laplacian φ) := by
  have hd (v : ℂ) : ContDiff ℝ 1 (fun z => fderiv ℝ φ z v) :=
    (contDiff_one_fderiv_of_two hφ).clm_apply contDiff_const
  have hc (v : ℂ) : Continuous (fun z => fderiv ℝ (fun w => fderiv ℝ φ w v) z v) :=
    ((hd v).continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  have heq : Laplacian.laplacian φ = fun z =>
      fderiv ℝ (fun w => fderiv ℝ φ w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ φ w Complex.I) z Complex.I :=
    funext (laplacian_complex_eq_coordinate_derivatives hφ)
  rw [heq]
  exact (hc 1).add (hc Complex.I)

theorem hasCompactSupport_laplacian_complex {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    HasCompactSupport (Laplacian.laplacian φ) := by
  have heq : Laplacian.laplacian φ = fun z =>
      fderiv ℝ (fun w => fderiv ℝ φ w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ φ w Complex.I) z Complex.I :=
    funext (laplacian_complex_eq_coordinate_derivatives hφ)
  rw [heq]
  exact ((hφc.fderiv_apply ℝ 1).fderiv_apply ℝ 1).add
    ((hφc.fderiv_apply ℝ Complex.I).fderiv_apply ℝ Complex.I)

theorem integral_logPotential_mul_laplacian (ν : Measure ℂ) [IsFiniteMeasure ν]
    {S : Set ℂ} (hS : IsCompact S) (hsupp : ∀ᵐ a ∂ν, a ∈ S)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ z : ℂ, logPotential ν z * Laplacian.laplacian φ z) =
      2 * Real.pi * ∫ a, φ a ∂ν := by
  rw [integral_logPotential_mul_test_eq ν hS hsupp
    (continuous_laplacian_complex hφ) (hasCompactSupport_laplacian_complex hφ hφc)]
  simp_rw [integral_logKernel_mul_laplacian _ hφ hφc]
  exact integral_const_mul (2 * Real.pi) φ


end ModifiedCartan







