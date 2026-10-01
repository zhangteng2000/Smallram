import ModifiedCartan.ScalarActualTargetCircleLimits
import ModifiedCartan.ScalarTargetGaugeMean

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual gauged norm has normalized unit-circle mean tending to one. -/
theorem ArbitraryRadiusLimitData.normalized_norm_circleAverage_tendsto_one
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ) :
    Tendsto (fun ν => (characteristic f (r (d.subseq ν)))⁻¹ *
      Real.circleAverage (fun z => Real.log (euclideanNorm
        (fun j => rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν) j z))) 0 1)
      atTop (𝓝 1) := by
  have ht : Tendsto (fun ν => 1 + d.mean_error ν) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add d.mean_error_zero
  apply ht.congr'
  filter_upwards [d.radial_mean] with ν hν
  have hh := hν 1 (by norm_num) (by norm_num)
  rw [one_mul, div_self (d.scale_pos ν).ne'] at hh
  have hmean : Real.circleAverage (fun z => (characteristic f (r (d.subseq ν)))⁻¹ *
      Real.log (euclideanNorm
        (fun j => rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν) j z))) 0 1 =
      (characteristic f (r (d.subseq ν)))⁻¹ *
      Real.circleAverage (fun z => Real.log (euclideanNorm
        (fun j => rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν) j z))) 0 1 := by
    simpa only [smul_eq_mul] using (Real.circleAverage_fun_smul
      (a := (characteristic f (r (d.subseq ν)))⁻¹)
      (f := fun z => Real.log (euclideanNorm
        (fun j => rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν) j z))) (c := 0) (R := 1))
  exact hh.symm.trans hmean

/-- The original projective proximity converges along a constructed subsequence.
The right side is the actual target-limit mean, still to be evaluated by sectors. -/
theorem ScalarTargetLogLimitData.exists_projective_proximity_ratio_limit
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} {d : ArbitraryRadiusLimitData f r ρ}
    {β : WithTop ℂ} (e : ScalarTargetLogLimitData d β)
    (hlin : f.linearlyNonDegenerate) (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop)
    (hA : (Real.pi / 2) * (2 : ℝ) ^ ρ ≤ d.A) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      Tendsto (fun ν => scalarProjectiveProximity f β (r (d.subseq (ns ν))) /
        characteristic f (r (d.subseq (ns ν)))) atTop
        (𝓝 (1 - Real.circleAverage (fun z => (e.u z).toReal) 0 1)) := by
  obtain ⟨ns, hns, htgt⟩ := e.exists_actual_target_circle_limit hρ hr hA
  refine ⟨ns, hns, ?_⟩
  have ht := (d.normalized_norm_circleAverage_tendsto_one.comp hns.tendsto_atTop).sub
    (htgt 1 (by norm_num) (by norm_num))
  apply ht.congr'
  filter_upwards [hns.tendsto_atTop.eventually d.replacement.gauge_analytic,
    ((hr.comp d.strictMono.tendsto_atTop).comp hns.tendsto_atTop).eventually
      (eventually_gt_atTop 0)] with ν hH hrν
  dsimp only [Function.comp_def] at hrν ⊢
  rw [scalarProjectiveProximity_eq_gauged_means f hlin β hrν.ne' hH]
  ring

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.normalized_norm_circleAverage_tendsto_one
#print axioms ModifiedCartan.ScalarTargetLogLimitData.exists_projective_proximity_ratio_limit
