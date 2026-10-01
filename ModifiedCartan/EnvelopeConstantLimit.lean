import ModifiedCartan.EnvelopeKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem envelopeConstant_zero : envelopeConstant 0 = 1 := by
  have hint : IntegrableOn (fun u : ℝ => 1 / (1 + u) ^ 2) (Ioi 0) := by
    have hh := envelope_integrand_integrable (α := 0) le_rfl (by norm_num)
    change IntegrableOn (fun u => envelopeIntegrand 0 u) (Ioi 0) at hh
    simpa only [envelopeIntegrand, Real.rpow_zero, max_self] using hh
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun t : ℝ => -(1 + t)⁻¹) (1 / (1 + x) ^ 2) x := by
    intro x hx
    have hn : 1 + x ≠ 0 := by change 0 ≤ x at hx; linarith
    convert! (((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).inv hn).neg using 1 <;>
      simp only [zero_add, neg_div, neg_neg, Pi.add_apply, id_eq]
  have ht : Tendsto (fun u : ℝ => -(1 + u)⁻¹) atTop (𝓝 0) := by
    have hplus : Tendsto (fun u : ℝ => 1 + u) atTop atTop := by
      simpa only [add_comm, id_eq] using tendsto_atTop_add_const_right atTop 1 tendsto_id
    simpa only [Function.comp_def, neg_zero] using (tendsto_inv_atTop_zero.comp hplus).neg
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint ht
  simpa only [envelopeConstant, envelopeIntegrand, Real.rpow_zero, max_self,
    add_zero, inv_one, zero_sub, neg_neg] using hi

/-- The last assertion of LaTeX `lem:envelope`: I_alpha tends to one from
the right at zero. The dominating kernel has exponent 1/2. -/
theorem envelopeConstant_tendsto_one : Tendsto envelopeConstant (𝓝[>] 0) (𝓝 1) := by
  have hsmall : ∀ᶠ α : ℝ in 𝓝[>] 0, 0 ≤ α ∧ α ≤ 1 / 2 := by
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds] with α hα hα1
    exact ⟨hα.le, hα1.le⟩
  have hmeas : ∀ᶠ α : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (envelopeIntegrand α) (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [hsmall] with α hα
    exact ((envelopeIntegrand_continuousOn hα.1).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ᶠ α : ℝ in 𝓝[>] 0, ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ‖envelopeIntegrand α u‖ ≤ envelopeIntegrand (1 / 2) u := by
    filter_upwards [hsmall] with α hα
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (envelopeIntegrand_nonneg α u)]
    exact envelopeIntegrand_mono_exponent hα.1 hα.2 hu
  have hlim : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun α => envelopeIntegrand α u) (𝓝[>] 0) (𝓝 (envelopeIntegrand 0 u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hcont : Continuous (fun α => envelopeIntegrand α u) :=
      (continuous_const.max (Real.continuous_const_rpow ((mul_pos (by norm_num : (0 : ℝ) < 3) hu).ne'))).div_const _
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht := tendsto_integral_filter_of_dominated_convergence (envelopeIntegrand (1 / 2))
    hmeas hbound (envelope_integrand_integrable (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) hlim
  change Tendsto envelopeConstant (𝓝[>] 0) (𝓝 (envelopeConstant 0)) at ht
  rwa [envelopeConstant_zero] at ht

theorem one_le_envelopeConstant {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    1 ≤ envelopeConstant α := by
  rw [← envelopeConstant_zero]
  apply integral_mono_ae (envelope_integrand_integrable (α := 0) le_rfl (by norm_num))
    (envelope_integrand_integrable hα hα1)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact envelopeIntegrand_mono_exponent (α := 0) le_rfl hα hu

end ModifiedCartan
#print axioms ModifiedCartan.envelopeConstant_tendsto_one
