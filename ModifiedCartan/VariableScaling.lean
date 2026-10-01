import ModifiedCartan.RegularVariation
import ModifiedCartan.ScalarSpherePotentialLimit
import ModifiedCartan.MeasureLimitTransfer

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The compact-uniform regular-variation statement controls a multiplier that
itself varies with the sequence. -/
theorem regularlyVarying_tendsto_variable_multiplier {T : ℝ → ℝ} {ρ : ℝ}
    (h : FewInflection.RegularlyVarying T ρ) {K : Set ℝ} (hK : IsCompact K)
    (hKpos : K ⊆ Ioi 0) {c : ℕ → ℝ} {c₀ : ℝ}
    (hc : ∀ ν, c ν ∈ K) (hc₀ : 0 < c₀) (hclim : Tendsto c atTop (𝓝 c₀))
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    Tendsto (fun ν => T (c ν * r ν) / T (r ν)) atTop (𝓝 (c₀ ^ ρ)) := by
  have he : Tendsto (fun ν => T (c ν * r ν) / T (r ν) - (c ν) ^ ρ) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨R, _, hR⟩ := h K hK hKpos ε hε
    filter_upwards [hr.eventually_gt_atTop R] with ν hν
    simpa only [Real.dist_eq, sub_zero, Real.rpow_eq_pow] using hR (r ν) hν (c ν) (hc ν)
  have hp := (Real.continuousAt_rpow_const c₀ ρ (Or.inl hc₀.ne')).tendsto.comp hclim
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using he.add hp

/-- All representatives of the physical potential are measurable, including
its explicitly chosen values at critical points. -/
theorem scalarNormalizedSpherePotential_measurable (f : Curve 1) (t : ℝ) :
    Measurable (scalarNormalizedSpherePotential f t) := by
  have hraw : Measurable (scalarSphericalLogPotential f.coord) :=
    (measurable_const.mul (curve_log_euclideanNorm_continuous f).measurable).sub
      (FewInflection.differentiable_wronskian f).continuous.norm.measurable.log
  exact (hraw.comp (measurable_const.mul measurable_id)).div_const (characteristic f t)

/-- Multiplication by a convergent scalar preserves local convergence in
measure. Membership here is the measurability of the actual source functions. -/
theorem LocalMeasureConvergence.variable_const_mul {U : Set ℂ}
    {F : ℕ → ℂ → ℝ} {u : ℂ → ℝ} (h : LocalMeasureConvergence U F u)
    (hF : ∀ K, IsCompact K → K ⊆ U → ∀ ν, AEStronglyMeasurable (F ν) (volume.restrict K))
    {c : ℕ → ℝ} {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀)) :
    LocalMeasureConvergence U (fun ν z => c ν * F ν z) (fun z => c₀ * u z) := by
  have hconst : LocalMeasureConvergence U (fun ν _ => c ν) (fun _ => c₀) :=
    uniformlyOn_localMeasureConvergence (hc.tendstoUniformlyOn_const U) (Subset.rfl)
  exact hconst.continuous_map₂ h
    (fun _ _ _ _ => aestronglyMeasurable_const) hF (continuous_fst.mul continuous_snd)

end ModifiedCartan
#print axioms ModifiedCartan.regularlyVarying_tendsto_variable_multiplier
#print axioms ModifiedCartan.scalarNormalizedSpherePotential_measurable
#print axioms ModifiedCartan.LocalMeasureConvergence.variable_const_mul

