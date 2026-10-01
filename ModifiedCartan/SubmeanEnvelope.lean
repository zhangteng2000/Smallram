import ModifiedCartan.LocalDiskAverageContinuity

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-- The infimum of all admissible disk means. It is used to construct, rather than assume,
the subharmonic representative in manuscript `lem:subharmonic-compactness`. -/
noncomputable def submeanEnvelope (U : Set ℂ) (f : ℂ → ℝ) (z : ℂ) : EReal :=
  ⨅ (r : ℝ) (_ : 0 < r) (_ : closedBall z r ⊆ U), (diskAverage r f z : EReal)

theorem submeanEnvelope_le {U : Set ℂ} {f : ℂ → ℝ} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : closedBall z r ⊆ U) :
    submeanEnvelope U f z ≤ (diskAverage r f z : EReal) := by
  exact iInf_le_of_le r (iInf_le_of_le hr (iInf_le_of_le hball le_rfl))

theorem le_submeanEnvelope {U : Set ℂ} {f : ℂ → ℝ} {z : ℂ} {a : EReal}
    (h : ∀ r : ℝ, 0 < r → closedBall z r ⊆ U → a ≤ (diskAverage r f z : EReal)) :
    a ≤ submeanEnvelope U f z := by
  exact le_iInf (fun r => le_iInf (fun hr => le_iInf (fun hball => h r hr hball)))

theorem submeanEnvelope_ne_top {U : Set ℂ} (hU : IsOpen U) (f : ℂ → ℝ)
    {z : ℂ} (hz : z ∈ U) : submeanEnvelope U f z ≠ ⊤ := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hz
  have hball : closedBall z (ε / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεU
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (submeanEnvelope_le (half_pos hε) hball)

theorem upperSemicontinuousOn_submeanEnvelope {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℝ} (hf : LocallyIntegrableOn f U) :
    UpperSemicontinuousOn (submeanEnvelope U f) U := by
  intro z hz a ha
  obtain ⟨r, hr, hball, hra⟩ : ∃ r : ℝ, ∃ hr : 0 < r,
      ∃ hball : closedBall z r ⊆ U, (diskAverage r f z : EReal) < a := by
    simpa only [submeanEnvelope, iInf_lt_iff] using ha
  have hcont : ContinuousAt (fun w => (diskAverage r f w : EReal)) z :=
    continuous_coe_real_ereal.continuousAt.comp
      (continuousAt_diskAverage_of_locallyIntegrableOn hU hf hr hball)
  have hnear : ∀ᶠ w in 𝓝 z, (diskAverage r f w : EReal) < a := hcont (gt_mem_nhds hra)
  have hballs : ∀ᶠ w in 𝓝 z, closedBall w r ⊆ U :=
    (isOpen_setOf_closedBall_subset hU r).mem_nhds hball
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, hballs.filter_mono nhdsWithin_le_nhds]
    with w hw hwb
  exact (submeanEnvelope_le hr hwb).trans_lt hw


end ModifiedCartan
