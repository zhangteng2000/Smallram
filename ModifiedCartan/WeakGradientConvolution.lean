import ModifiedCartan.WeakGradientDirectional
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.MetricSpace.IsometricSMul

open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

/-- The derivative of the smoothing equals the smoothing of the actual
weak directional derivative. No regularity of that derivative is assumed. -/
theorem HasWeakComplexGradient.fderiv_convolution_apply {U : Set ℂ} (hU : IsOpen U)
    {u v : ℂ → ℝ} {g : ℂ → ℂ} (hu : HasWeakComplexGradient U u g)
    (hv : LocallyIntegrable v) (hvu : EqOn v u U)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (x : ℂ) (hx : (fun z : ℂ => x - z) ⁻¹' tsupport χ ⊆ U) (w : ℂ) :
    fderiv ℝ (v ⋆[lsmul ℝ ℝ, volume] χ) x w =
      ∫ z, (g z * w).re * χ (x - z) := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by norm_num)
  rw [(hχc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hv hχ1 x).fderiv]
  rw [convolution_precompR_apply (lsmul ℝ ℝ) hv (hχc.fderiv ℝ)
    (hχ1.continuous_fderiv one_ne_zero), convolution_def]
  change (∫ z, v z * fderiv ℝ χ (x - z) w) = _
  let φ : ℂ → ℝ := fun z => χ (x - z)
  have hφ : ContDiff ℝ ∞ φ := hχ.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ :=
    hχc.comp_homeomorph (IsometryEquiv.subLeft x).toHomeomorph
  have hφU : tsupport φ ⊆ U :=
    (tsupport_comp_subset_preimage χ (continuous_const.sub continuous_id)).trans hx
  have hderiv (z : ℂ) : fderiv ℝ φ z w = -fderiv ℝ χ (x - z) w := by
    have hd := ((hχ1.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp z
      ((hasFDerivAt_const x z).sub (hasFDerivAt_id z))).fderiv
    have hval := congrArg (fun L : ℂ →L[ℝ] ℝ => L w) hd
    simpa only [φ, Function.comp_def, Pi.sub_apply, id_eq,
      ContinuousLinearMap.comp_apply, sub_zero, zero_sub,
      neg_apply, ContinuousLinearMap.id_apply, map_neg] using hval
  have huv : u =ᵐ[volume.restrict U] v := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact (hvu hz).symm
  have ht := hu.integral_mul_fderiv hφ hφc hφU w
  rw [integral_mul_test_congr_ae hU.measurableSet huv
    ((tsupport_fderiv_apply_subset ℝ w).trans hφU)] at ht
  simp only [hderiv, mul_neg, integral_neg] at ht
  exact neg_injective ht

end ModifiedCartan
#print axioms ModifiedCartan.HasWeakComplexGradient.fderiv_convolution_apply
