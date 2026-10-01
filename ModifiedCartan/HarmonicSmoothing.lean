import ModifiedCartan.RadialKernel
import ModifiedCartan.HarmonicRadialMean
import Mathlib.Analysis.Calculus.ContDiff.Convolution

open scoped Topology ENNReal ContDiff Convolution
open Filter MeasureTheory Set Metric InnerProductSpace

set_option autoImplicit false

namespace ModifiedCartan

/-! Smooth convolution for the harmonic estimates in `lem:logderivlimit`.
The radial convolution reproduces harmonic functions; global L1 convergence
implies uniform convergence of smoothed functions and their first two total
derivatives. The Laplacian therefore converges pointwise. -/

noncomputable def scalarConvolution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → ℝ) (k : ℂ → E) : ℂ → E :=
  f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k

theorem scalarConvolution_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → ℝ) (k : ℂ → E) (z : ℂ) :
    scalarConvolution f k z = ∫ a : ℂ, f a • k (z - a) := rfl

theorem scalarConvolution_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → ℝ} {k : ℂ → E} (hf : LocallyIntegrable f) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) : ContDiff ℝ ∞ (scalarConvolution f k) :=
  hkc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hk

theorem scalarConvolution_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → ℝ} {k : ℂ → E} (hf : LocallyIntegrable f) (hk : ContDiff ℝ 1 k)
    (hkc : HasCompactSupport k) (z : ℂ) :
    fderiv ℝ (scalarConvolution f k) z = scalarConvolution f (fderiv ℝ k) z := by
  have hd := (hkc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hk z).fderiv
  have heq : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).precompR ℂ =
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (ℂ →L[ℝ] E) →L[ℝ] (ℂ →L[ℝ] E)) := by
    ext r L
    rfl
  simpa only [scalarConvolution, heq] using hd

theorem radialKernel_neg (R : ℝ) (z : ℂ) : radialKernel R (-z) = radialKernel R z := by
  rw [radialKernel_radial R (-z), norm_neg, ← radialKernel_radial R z]

theorem scalarConvolution_radialKernel_eq {H : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hH : HarmonicOnNhd H (closedBall c (2 * R))) :
    scalarConvolution H (radialKernel R) c = H c := by
  change (H ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] radialKernel R) c = H c
  rw [convolution_eq_swap]
  change (∫ z : ℂ, H (c - z) * radialKernel R z) = H c
  rw [← integral_neg_eq_self (fun z : ℂ => H (c - z) * radialKernel R z) volume]
  simp only [sub_neg_eq_add, radialKernel_neg]
  simpa only [mul_comm, radialKernel_integral hR, one_mul, mul_one] using
    integral_radial_mul_harmonic (radialKernel_contDiff R).continuous
      (radialKernel_hasCompactSupport hR) (radialKernel_radial R) (radialKernel_tsupport hR) hH

theorem integrable_scalarConvolution_integrand {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → ℝ} {k : ℂ → E} (hf : Integrable f) (hk : Continuous k)
    {M : ℝ} (hM : ∀ a, ‖k a‖ ≤ M) (z : ℂ) :
    Integrable (fun a => f a • k (z - a)) :=
  hf.smul_bdd M ((hk.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall (fun a => hM (z - a)))

theorem norm_scalarConvolution_sub_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : ℂ → ℝ} {k : ℂ → E} (hf : Integrable f) (hg : Integrable g) (hk : Continuous k)
    {M : ℝ} (hM : ∀ a, ‖k a‖ ≤ M) (z : ℂ) :
    ‖scalarConvolution f k z - scalarConvolution g k z‖ ≤ M * ∫ a : ℂ, ‖f a - g a‖ := by
  rw [scalarConvolution_eq_integral, scalarConvolution_eq_integral,
    ← integral_sub (integrable_scalarConvolution_integrand hf hk hM z)
      (integrable_scalarConvolution_integrand hg hk hM z)]
  simp_rw [← sub_smul]
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le ((hf.sub hg).norm.const_mul M)
  apply Eventually.of_forall
  intro a
  rw [norm_smul, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM (z - a)) (norm_nonneg _)

theorem scalarConvolution_tendstoUniformly {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {k : ℂ → E}
    (hf : ∀ n, Integrable (f n)) (hg : Integrable g) (hk : Continuous k)
    (hkc : HasCompactSupport k)
    (hlim : Tendsto (fun n => ∫ a : ℂ, ‖f n a - g a‖) atTop (𝓝 0)) :
    TendstoUniformly (fun n => scalarConvolution (f n) k) (scalarConvolution g k) atTop := by
  obtain ⟨M, hM⟩ := hkc.exists_bound_of_continuous hk
  have ht : Tendsto (fun n => M * ∫ a : ℂ, ‖f n a - g a‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul M
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  intro z
  rw [dist_comm, dist_eq_norm]
  exact (norm_scalarConvolution_sub_le (hf n) hg hk hM z).trans_lt hn


theorem scalarConvolution_fderiv_tendstoUniformly {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {k : ℂ → E}
    (hf : ∀ n, Integrable (f n)) (hg : Integrable g) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k)
    (hlim : Tendsto (fun n => ∫ a : ℂ, ‖f n a - g a‖) atTop (𝓝 0)) :
    TendstoUniformly (fun n => fderiv ℝ (scalarConvolution (f n) k))
      (fderiv ℝ (scalarConvolution g k)) atTop := by
  have hdf : Continuous (fderiv ℝ k) := hk.continuous_fderiv (by simp)
  have ht := scalarConvolution_tendstoUniformly hf hg hdf (hkc.fderiv ℝ) hlim
  have heq (v : ℂ → ℝ) (hv : Integrable v) :
      fderiv ℝ (scalarConvolution v k) = scalarConvolution v (fderiv ℝ k) :=
    funext fun z => scalarConvolution_fderiv hv.locallyIntegrable (hk.of_le (by simp)) hkc z
  simpa only [heq _ hg, heq _ (hf _)] using ht


theorem scalarConvolution_second_fderiv_tendstoUniformly {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {k : ℂ → E}
    (hf : ∀ n, Integrable (f n)) (hg : Integrable g) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k)
    (hlim : Tendsto (fun n => ∫ a : ℂ, ‖f n a - g a‖) atTop (𝓝 0)) :
    TendstoUniformly (fun n => fderiv ℝ (fderiv ℝ (scalarConvolution (f n) k)))
      (fderiv ℝ (fderiv ℝ (scalarConvolution g k))) atTop := by
  have hdk : ContDiff ℝ ∞ (fderiv ℝ k) := (contDiff_infty_iff_fderiv.mp hk).2
  have ht := scalarConvolution_fderiv_tendstoUniformly hf hg hdk (hkc.fderiv ℝ) hlim
  have heq (v : ℂ → ℝ) (hv : Integrable v) :
      fderiv ℝ (scalarConvolution v k) = scalarConvolution v (fderiv ℝ k) :=
    funext fun z => scalarConvolution_fderiv hv.locallyIntegrable (hk.of_le (by simp)) hkc z
  simpa only [heq _ hg, heq _ (hf _)] using ht

theorem scalarConvolution_laplacian_tendsto
    {f : ℕ → ℂ → ℝ} {g k : ℂ → ℝ}
    (hf : ∀ n, Integrable (f n)) (hg : Integrable g) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k)
    (hlim : Tendsto (fun n => ∫ a : ℂ, ‖f n a - g a‖) atTop (𝓝 0)) (z : ℂ) :
    Tendsto (fun n => Laplacian.laplacian (scalarConvolution (f n) k) z) atTop
      (𝓝 (Laplacian.laplacian (scalarConvolution g k) z)) := by
  have ht := (scalarConvolution_second_fderiv_tendstoUniformly hf hg hk hkc hlim).tendsto_at z
  have hc : Continuous (fun B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ =>
      B 1 1 + B Complex.I Complex.I) := by fun_prop
  simpa [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply, Function.comp_def] using (hc.tendsto _).comp ht


end ModifiedCartan
