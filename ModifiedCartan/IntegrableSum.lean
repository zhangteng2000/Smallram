import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.InfiniteSum

open scoped Topology ENNReal
open MeasureTheory Filter Set ENNReal
set_option autoImplicit false
namespace ModifiedCartan

/-- The real-valued series integrability needed in `cor:convolution`.
The finite bound on the integral of the sum of norms is obtained by
Tonelli, before taking a real-valued integral of the sum. -/
theorem integrable_real_tsum_of_summable_integral_norm {ι : Type*} [Countable ι]
    {μ : Measure ℝ} {F : ι → ℝ → ℝ}
    (hF : ∀ i, Integrable (F i) μ)
    (hS : Summable (fun i => ∫ t, ‖F i t‖ ∂μ)) :
    Integrable (fun t => ∑' i, F i t) μ := by
  have hlin (i : ι) : (∫⁻ t, ‖F i t‖ₑ ∂μ) = ‖∫ t, ‖F i t‖ ∂μ‖ₑ := by
    rw [Real.enorm_of_nonneg (integral_nonneg (fun t => norm_nonneg (F i t)))]
    simpa only [ofReal_norm] using
      (ofReal_integral_eq_lintegral_ofReal (hF i).norm
        (Filter.Eventually.of_forall (fun t => norm_nonneg (F i t)))).symm
  have hfinite : (∑' i, ∫⁻ t, ‖F i t‖ₑ ∂μ) < ∞ := by
    rw [funext hlin, lt_top_iff_ne_top]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hS.abs)
  refine ⟨?_, ?_⟩
  · have hm : ∀ i, AEStronglyMeasurable (F i) μ := fun i => (hF i).aestronglyMeasurable
    fun_prop
  · change (∫⁻ t, ‖∑' i, F i t‖ₑ ∂μ) < ∞
    calc
      _ ≤ ∫⁻ t, ∑' i, ‖F i t‖ₑ ∂μ := lintegral_mono (fun t => enorm_tsum_le_tsum_enorm)
      _ = ∑' i, ∫⁻ t, ‖F i t‖ₑ ∂μ := lintegral_tsum (fun i => (hF i).aestronglyMeasurable.enorm)
      _ < ∞ := hfinite

end ModifiedCartan
#print axioms ModifiedCartan.integrable_real_tsum_of_summable_integral_norm
