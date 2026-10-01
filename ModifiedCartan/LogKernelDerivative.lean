import ModifiedCartan.LogWeak
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Weak derivatives of the planar logarithmic kernel, required in the proof of
`lem:logderivlimit`. Coordinate slices avoid the singular origin for almost every
slice. One-dimensional integration by parts, Fubini, and translation invariance
then give the exact two coordinate identities for every center. -/

theorem log_norm_mk (x y : ℝ) :
    Real.log ‖(⟨x, y⟩ : ℂ)‖ = (1 / 2 : ℝ) * Real.log (x ^ 2 + y ^ 2) := by
  have hn : x ^ 2 + y ^ 2 = ‖(⟨x, y⟩ : ℂ)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, pow_two]
  rw [hn, Real.log_pow]
  ring

theorem hasDerivAt_log_norm_mk_left (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖(⟨t, y⟩ : ℂ)‖) (x / (x ^ 2 + y ^ 2)) x := by
  have hpos : 0 < x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg x, sq_pos_of_ne_zero hy]
  simp_rw [log_norm_mk]
  convert! ((((hasDerivAt_id x).pow 2).add_const (y ^ 2)).log hpos.ne').const_mul
    (1 / 2 : ℝ) using 1
  norm_num
  ring

theorem hasDerivAt_log_norm_mk_right (y : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖(⟨x, t⟩ : ℂ)‖) (y / (x ^ 2 + y ^ 2)) y := by
  have heq : (fun t : ℝ => Real.log ‖(⟨x, t⟩ : ℂ)‖) =
      (fun t : ℝ => Real.log ‖(⟨t, x⟩ : ℂ)‖) := by
    funext t
    simp only [log_norm_mk, add_comm]
  rw [heq, add_comm (x ^ 2)]
  exact hasDerivAt_log_norm_mk_left y hx

theorem integral_log_norm_mk_mul_deriv_left {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) {y : ℝ} (hy : y ≠ 0) :
    (∫ x : ℝ, Real.log ‖(⟨x, y⟩ : ℂ)‖ * deriv ψ x) =
      -(∫ x : ℝ, (x / (x ^ 2 + y ^ 2)) * ψ x) := by
  have hlog : Continuous (fun x : ℝ => Real.log ‖(⟨x, y⟩ : ℂ)‖) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_log_norm_mk_left x hy).continuousAt
  have hrat : Continuous (fun x : ℝ => x / (x ^ 2 + y ^ 2)) := by
    apply continuous_id.div ((continuous_id.pow 2).add continuous_const)
    intro x
    change x ^ 2 + y ^ 2 ≠ 0
    nlinarith [sq_nonneg x, sq_pos_of_ne_zero hy]
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => Real.log ‖(⟨x, y⟩ : ℂ)‖)
    (u' := fun x : ℝ => x / (x ^ 2 + y ^ 2)) (v := ψ) (v' := deriv ψ)
    (fun x _ => hasDerivAt_log_norm_mk_left x hy)
    (fun x _ => (hψ.differentiable_one x).hasDerivAt)
    ((hlog.mul hψ.continuous_deriv_one).integrable_of_hasCompactSupport hψc.deriv.mul_left)
    ((hrat.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left)
    ((hlog.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left)

theorem integral_log_norm_mk_mul_deriv_right {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) {x : ℝ} (hx : x ≠ 0) :
    (∫ y : ℝ, Real.log ‖(⟨x, y⟩ : ℂ)‖ * deriv ψ y) =
      -(∫ y : ℝ, (y / (x ^ 2 + y ^ 2)) * ψ y) := by
  have heq : (fun y : ℝ => Real.log ‖(⟨x, y⟩ : ℂ)‖) =
      (fun y : ℝ => Real.log ‖(⟨y, x⟩ : ℂ)‖) := by
    funext y
    simp only [log_norm_mk, add_comm]
  simp_rw [show ∀ y : ℝ, Real.log ‖(⟨x, y⟩ : ℂ)‖ = Real.log ‖(⟨y, x⟩ : ℂ)‖
    from fun y => congrFun heq y, add_comm (x ^ 2)]
  exact integral_log_norm_mk_mul_deriv_left hψ hψc hx

theorem test_slice_left_contDiff {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (y : ℝ) :
    ContDiff ℝ 1 (fun x : ℝ => φ (⟨x, y⟩ : ℂ)) :=
  hφ.comp (Complex.equivRealProdCLM.symm.contDiff.comp (contDiff_id.prodMk contDiff_const))

theorem test_slice_right_contDiff {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (x : ℝ) :
    ContDiff ℝ 1 (fun y : ℝ => φ (⟨x, y⟩ : ℂ)) :=
  hφ.comp (Complex.equivRealProdCLM.symm.contDiff.comp (contDiff_const.prodMk contDiff_id))

theorem test_slice_left_hasCompactSupport {φ : ℂ → ℝ} (hφ : HasCompactSupport φ) (y : ℝ) :
    HasCompactSupport (fun x : ℝ => φ (⟨x, y⟩ : ℂ)) := by
  have hiso : Isometry (fun x : ℝ => (⟨x, y⟩ : ℂ)) :=
    isometry_iff_dist_eq.mpr fun x x' => Complex.dist_of_im_eq rfl
  exact hφ.comp_isClosedEmbedding hiso.isClosedEmbedding

theorem test_slice_right_hasCompactSupport {φ : ℂ → ℝ} (hφ : HasCompactSupport φ) (x : ℝ) :
    HasCompactSupport (fun y : ℝ => φ (⟨x, y⟩ : ℂ)) := by
  have hiso : Isometry (fun y : ℝ => (⟨x, y⟩ : ℂ)) :=
    isometry_iff_dist_eq.mpr fun y y' => Complex.dist_of_re_eq rfl
  exact hφ.comp_isClosedEmbedding hiso.isClosedEmbedding

theorem deriv_test_slice_left {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (x y : ℝ) :
    deriv (fun t : ℝ => φ (⟨t, y⟩ : ℂ)) x = fderiv ℝ φ (⟨x, y⟩ : ℂ) 1 := by
  have hline : HasDerivAt (fun t : ℝ => (⟨t, y⟩ : ℂ)) (1 : ℂ) x := by
    simpa only [Complex.mk_eq_add_mul_I, Complex.ofRealCLM_apply, Complex.ofReal_one] using
      (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I)
  exact ((hφ.differentiable_one (⟨x, y⟩ : ℂ)).hasFDerivAt.comp_hasDerivAt x hline).deriv

theorem deriv_test_slice_right {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (x y : ℝ) :
    deriv (fun t : ℝ => φ (⟨x, t⟩ : ℂ)) y = fderiv ℝ φ (⟨x, y⟩ : ℂ) Complex.I := by
  have hline : HasDerivAt (fun t : ℝ => (⟨x, t⟩ : ℂ)) Complex.I y := by
    simpa only [Complex.mk_eq_add_mul_I, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      (((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (x : ℂ))
  exact ((hφ.differentiable_one (⟨x, y⟩ : ℂ)).hasFDerivAt.comp_hasDerivAt y hline).deriv

theorem locallyIntegrable_inv_complex : LocallyIntegrable (fun z : ℂ => z⁻¹) := by
  rw [locallyIntegrable_iff]
  intro K hK
  have h := memLp_cauchyKernel_on_compact (p := 1) zero_lt_one (by norm_num) 0 hK
  simpa only [IntegrableOn, sub_zero, ENNReal.ofReal_one, memLp_one_iff_integrable] using h

theorem locallyIntegrable_inv_re : LocallyIntegrable (fun z : ℂ => (z⁻¹).re) := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact Complex.reCLM.integrable_comp (locallyIntegrable_inv_complex.integrableOn_isCompact hK)

theorem locallyIntegrable_neg_inv_im : LocallyIntegrable (fun z : ℂ => -(z⁻¹).im) := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact (Complex.imCLM.integrable_comp
    (locallyIntegrable_inv_complex.integrableOn_isCompact hK)).neg

theorem integrable_log_norm_mul_test_fderiv {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (v : ℂ) :
    Integrable (fun z : ℂ => Real.log ‖z‖ * fderiv ℝ φ z v) := by
  have hd : Continuous (fun z : ℂ => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  simpa only [sub_zero, smul_eq_mul] using
    (locallyIntegrable_logKernel 0).integrable_smul_right_of_hasCompactSupport hd
      (hφc.fderiv_apply ℝ v)

theorem integral_complex_eq_iterated_left (f : ℂ → ℝ) (hf : Integrable f) :
    (∫ z : ℂ, f z) = ∫ y : ℝ, ∫ x : ℝ, f (⟨x, y⟩ : ℂ) := by
  have hvol := Complex.volume_preserving_equiv_real_prod.symm
  calc
    _ = ∫ p : ℝ × ℝ, f (⟨p.1, p.2⟩ : ℂ) :=
      (hvol.integral_comp Complex.measurableEquivRealProd.symm.measurableEmbedding f).symm
    _ = _ := integral_prod_symm _ (hvol.integrable_comp_of_integrable hf)

theorem integral_complex_eq_iterated_right (f : ℂ → ℝ) (hf : Integrable f) :
    (∫ z : ℂ, f z) = ∫ x : ℝ, ∫ y : ℝ, f (⟨x, y⟩ : ℂ) := by
  have hvol := Complex.volume_preserving_equiv_real_prod.symm
  calc
    _ = ∫ p : ℝ × ℝ, f (⟨p.1, p.2⟩ : ℂ) :=
      (hvol.integral_comp Complex.measurableEquivRealProd.symm.measurableEmbedding f).symm
    _ = _ := integral_prod _ (hvol.integrable_comp_of_integrable hf)

theorem integral_log_norm_mul_fderiv_one {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ z : ℂ, Real.log ‖z‖ * fderiv ℝ φ z 1) =
      -(∫ z : ℂ, (z⁻¹).re * φ z) := by
  have hr : Integrable (fun z : ℂ => (z⁻¹).re * φ z) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_inv_re.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  rw [integral_complex_eq_iterated_left _ (integrable_log_norm_mul_test_fderiv hφ hφc 1),
    integral_complex_eq_iterated_left _ hr, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with y hy
  have hs := integral_log_norm_mk_mul_deriv_left (test_slice_left_contDiff hφ y)
    (test_slice_left_hasCompactSupport hφc y) hy
  simpa only [deriv_test_slice_left hφ, Complex.inv_re, Complex.normSq_mk,
    pow_two] using hs

theorem integral_log_norm_mul_fderiv_I {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ z : ℂ, Real.log ‖z‖ * fderiv ℝ φ z Complex.I) =
      -(∫ z : ℂ, (-(z⁻¹).im) * φ z) := by
  have hr : Integrable (fun z : ℂ => (-(z⁻¹).im) * φ z) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_neg_inv_im.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  rw [integral_complex_eq_iterated_right _ (integrable_log_norm_mul_test_fderiv hφ hφc Complex.I),
    integral_complex_eq_iterated_right _ hr, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  have hs := integral_log_norm_mk_mul_deriv_right (test_slice_right_contDiff hφ x)
    (test_slice_right_hasCompactSupport hφc x) hx
  simpa only [deriv_test_slice_right hφ, Complex.inv_im, Complex.normSq_mk,
    pow_two, neg_div, neg_neg] using hs

theorem integral_logKernel_mul_fderiv_one (a : ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ z : ℂ, Real.log ‖z - a‖ * fderiv ℝ φ z 1) =
      -(∫ z : ℂ, ((z - a)⁻¹).re * φ z) := by
  have hψ : ContDiff ℝ 1 (fun z => φ (z + a)) := hφ.comp (contDiff_id.add contDiff_const)
  have hψc : HasCompactSupport (fun z => φ (z + a)) :=
    hφc.comp_homeomorph (Homeomorph.addRight a)
  have hs := integral_log_norm_mul_fderiv_one hψ hψc
  simp only [fderiv_comp_add_right] at hs
  calc
    _ = ∫ z : ℂ, Real.log ‖z‖ * fderiv ℝ φ (z + a) 1 := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self
          (fun z : ℂ => Real.log ‖z - a‖ * fderiv ℝ φ z 1) a).symm
    _ = -(∫ z : ℂ, (z⁻¹).re * φ (z + a)) := hs
    _ = _ := by
      congr 1
      simpa only [add_sub_cancel_right] using
        integral_add_right_eq_self (fun z : ℂ => ((z - a)⁻¹).re * φ z) a

theorem integral_logKernel_mul_fderiv_I (a : ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ z : ℂ, Real.log ‖z - a‖ * fderiv ℝ φ z Complex.I) =
      -(∫ z : ℂ, (-((z - a)⁻¹).im) * φ z) := by
  have hψ : ContDiff ℝ 1 (fun z => φ (z + a)) := hφ.comp (contDiff_id.add contDiff_const)
  have hψc : HasCompactSupport (fun z => φ (z + a)) :=
    hφc.comp_homeomorph (Homeomorph.addRight a)
  have hs := integral_log_norm_mul_fderiv_I hψ hψc
  simp only [fderiv_comp_add_right] at hs
  calc
    _ = ∫ z : ℂ, Real.log ‖z‖ * fderiv ℝ φ (z + a) Complex.I := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self
          (fun z : ℂ => Real.log ‖z - a‖ * fderiv ℝ φ z Complex.I) a).symm
    _ = -(∫ z : ℂ, (-(z⁻¹).im) * φ (z + a)) := hs
    _ = _ := by
      congr 1
      simpa only [add_sub_cancel_right] using
        integral_add_right_eq_self (fun z : ℂ => (-((z - a)⁻¹).im) * φ z) a


end ModifiedCartan



