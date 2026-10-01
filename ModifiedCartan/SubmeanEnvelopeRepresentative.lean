import ModifiedCartan.SubmeanEnvelope
import ModifiedCartan.DiskAverageDifferentiation

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem submeanEnvelope_ae_eq {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ}
    (hf : LocallyIntegrableOn f U)
    (hsub : ∀ᵐ z ∂volume.restrict U, ∀ r : ℝ, 0 < r → closedBall z r ⊆ U →
      f z ≤ diskAverage r f z) :
    submeanEnvelope U f =ᵐ[volume.restrict U] (fun z => (f z : EReal)) := by
  filter_upwards [hsub, ae_tendsto_diskAverage_of_locallyIntegrableOn hU hf,
    ae_restrict_mem hU.measurableSet] with z hzsub hzlim hzU
  apply le_antisymm
  · have ht : Tendsto (fun r : ℝ => (diskAverage r f z : EReal)) (𝓝[>] 0) (𝓝 (f z : EReal)) :=
      EReal.tendsto_coe.mpr hzlim
    apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hzU
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds hε).filter_mono nhdsWithin_le_nhds] with r hr hrε
    exact submeanEnvelope_le (mem_Ioi.mp hr) ((closedBall_subset_ball hrε).trans hεU)
  · exact le_submeanEnvelope (fun r hr hball => EReal.coe_le_coe_iff.mpr (hzsub r hr hball))


end ModifiedCartan
