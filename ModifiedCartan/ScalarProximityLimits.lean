import ModifiedCartan.ScalarProximityComparison
import ModifiedCartan.ScalarProjectiveProximityLimits
import ModifiedCartan.ScalarTheoremGrowth

open scoped Topology
open Filter Set Metric Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

/-- A projective proximity ratio limit transfers to classical proximity
through the proved bounded comparison, with the actual curve denominator. -/
theorem scalar_proximity_ratio_tendsto_of_projective_limit {f : ℂ → ℂ}
    (F : Curve 1) (hlin : F.linearlyNonDegenerate)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => F.coord 1 z / F.coord 0 z))
    (β : WithTop ℂ) {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (hT : Tendsto (fun ν => characteristic F (r ν)) atTop atTop) {L : ℝ}
    (hP : Tendsto (fun ν => scalarProjectiveProximity F β (r ν) / characteristic F (r ν))
      atTop (𝓝 L)) :
    Tendsto (fun ν => ValueDistribution.proximity f β (r ν) / characteristic F (r ν))
      atTop (𝓝 L) := by
  obtain ⟨C, _, hC⟩ := scalar_proximity_abs_sub_projective_le F hlin he β
  have herr : Tendsto (fun ν => (ValueDistribution.proximity f β (r ν) -
      scalarProjectiveProximity F β (r ν)) / characteristic F (r ν)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (hT.const_div_atTop C)
    filter_upwards [hr.eventually (eventually_gt_atTop 0), hT.eventually (eventually_gt_atTop 0)]
      with ν hrν hTν
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hTν]
    exact div_le_div_of_nonneg_right (hC (r ν) hrν.ne') hTν.le
  have hh := herr.add hP
  simpa only [sub_div, sub_add_cancel, zero_add] using hh

/-- The same scalar limit uses the manuscript's actual scalar characteristic. -/
theorem scalar_proximity_ratio_tendsto_of_lift {f : ℂ → ℂ} (hf : Meromorphic f)
    (F : Curve 1) (hFt : F.Transcendental) (hFl : F.linearlyNonDegenerate)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => F.coord 1 z / F.coord 0 z))
    (hD : MeromorphicOn.divisor (F.coord 0) univ = (MeromorphicOn.divisor f univ)⁻)
    (β : WithTop ℂ) {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) {L : ℝ}
    (hP : Tendsto (fun ν => scalarProjectiveProximity F β (r ν) / characteristic F (r ν))
      atTop (𝓝 L)) :
    Tendsto (fun ν => ValueDistribution.proximity f β (r ν) / scalarCharacteristic f (r ν))
      atTop (𝓝 L) := by
  have hTF := characteristic_tendsto_atTop_of_transcendental F hFt
  have hraw := scalar_proximity_ratio_tendsto_of_projective_limit F hFl he β hr (hTF.comp hr) hP
  have hpos : ∀ᶠ R in atTop, characteristic F R ≠ 0 :=
    (hTF.eventually (eventually_gt_atTop 0)).mono (fun _ h => h.ne')
  have ht := ((isEquivalent_iff_tendsto_one hpos).mp
    (scalarCharacteristic_isEquivalent_lift hf F hFt hFl he hD)).comp hr
  have hh := hraw.div ht one_ne_zero
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [hr.eventually hpos] with ν hν
  change (ValueDistribution.proximity f β (r ν) / characteristic F (r ν)) /
    (scalarCharacteristic f (r ν) / characteristic F (r ν)) = _
  exact div_div_div_cancel_right₀ hν _ _

/-- Actual classical scalar proximity has the constructed target circle-mean
limit. The remaining task is the sector evaluation and all-radius uniqueness. -/
theorem ScalarTargetLogLimitData.exists_scalar_proximity_ratio_limit
    {f : ℂ → ℂ} (hf : Meromorphic f) {F : Curve 1}
    (hFt : F.Transcendental) (hFl : F.linearlyNonDegenerate)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => F.coord 1 z / F.coord 0 z))
    (hD : MeromorphicOn.divisor (F.coord 0) univ = (MeromorphicOn.divisor f univ)⁻)
    {r : ℕ → ℝ} {ρ : ℝ} {d : ArbitraryRadiusLimitData F r ρ}
    {β : WithTop ℂ} (e : ScalarTargetLogLimitData d β)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop)
    (hA : (Real.pi / 2) * (2 : ℝ) ^ ρ ≤ d.A) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      Tendsto (fun ν => ValueDistribution.proximity f β (r (d.subseq (ns ν))) /
        scalarCharacteristic f (r (d.subseq (ns ν)))) atTop
        (𝓝 (1 - Real.circleAverage (fun z => (e.u z).toReal) 0 1)) := by
  obtain ⟨ns, hns, hP⟩ := e.exists_projective_proximity_ratio_limit hFl hρ hr hA
  refine ⟨ns, hns, scalar_proximity_ratio_tendsto_of_lift hf F hFt hFl he hD β
    ((hr.comp d.strictMono.tendsto_atTop).comp hns.tendsto_atTop) hP⟩

end ModifiedCartan
#print axioms ModifiedCartan.scalar_proximity_ratio_tendsto_of_lift
#print axioms ModifiedCartan.ScalarTargetLogLimitData.exists_scalar_proximity_ratio_limit
