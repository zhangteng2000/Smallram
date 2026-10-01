import ModifiedCartan.PhaseLogLimit

open scoped Topology
open Filter Set MeasureTheory ContinuousLinearMap
set_option autoImplicit false
namespace ModifiedCartan

theorem integral_phaseLogApprox_tendsto {μ : Measure ℂ} {g : ℂ → ℂ}
    (hg : AEStronglyMeasurable g μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ z ∂μ, (g z).re ≤ 0 ∧ ‖g z‖ ≤ C)
    {ψ : ℂ → ℝ} (hψ : Integrable ψ μ) (L : ℂ →L[ℝ] ℝ) :
    Tendsto (fun ν => ∫ z, L (phaseLogApprox ν (g z)) * ψ z ∂μ) atTop
      (𝓝 (∫ z, (if g z = 0 then L 1 else 0) * ψ z ∂μ)) := by
  classical
  let B := 1 + Real.log (C + 2) + Real.pi
  apply tendsto_integral_of_dominated_convergence (fun z => (‖L‖ * B) * ‖ψ z‖)
  · intro ν
    have hm : AEStronglyMeasurable (fun z => Complex.log ((Real.exp (-phaseLogScale ν) : ℂ) - g z)) μ :=
      (Complex.measurable_log.comp_aemeasurable (aemeasurable_const.sub hg.aemeasurable)).aestronglyMeasurable
    exact (L.continuous.comp_aestronglyMeasurable (hm.const_smul (-(phaseLogScale ν)⁻¹))).mul
      hψ.aestronglyMeasurable
  · exact hψ.norm.const_mul _
  · intro ν
    filter_upwards [hbound] with z hz
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (norm_phaseLogApprox_le hC hz.1 hz.2 ν) (norm_nonneg _))
  · filter_upwards [hbound] with z hz
    have hh := (L.continuous.continuousAt.tendsto.comp (phaseLogApprox_tendsto hz.1)).mul_const (ψ z)
    simpa only [apply_ite, map_zero, Function.comp_def] using! hh

end ModifiedCartan
#print axioms ModifiedCartan.integral_phaseLogApprox_tendsto
