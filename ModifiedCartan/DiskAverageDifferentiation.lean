import ModifiedCartan.SubharmonicAveragingOrder
import ModifiedCartan.SubharmonicLocalIntegrability
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem complex_closedBall_ae_eq_ball (c : ℂ) (r : ℝ) :
    closedBall c r =ᵐ[volume] ball c r := by
  rw [ae_eq_set, closedBall_sdiff_ball, sdiff_eq_empty.mpr ball_subset_closedBall, measure_empty]
  exact ⟨Measure.addHaar_sphere volume c r, rfl⟩

theorem diskAverage_eq_closedBallAverage (r : ℝ) (f : ℂ → ℝ) (c : ℂ) :
    diskAverage r f c = ⨍ z in closedBall c r, f z := by
  exact setAverage_congr (complex_closedBall_ae_eq_ball c r).symm

/-- Lebesgue differentiation for the disk averaging operator, at every positive radius tending to zero. -/
theorem ae_tendsto_diskAverage {f : ℂ → ℝ} (hf : Integrable f) :
    ∀ᵐ z, Tendsto (fun r : ℝ => diskAverage r f z) (𝓝[>] 0) (𝓝 (f z)) := by
  have h := IsUnifLocDoublingMeasure.ae_tendsto_average volume hf.locallyIntegrable 1
  filter_upwards [h] with z hz
  have hmem : ∀ᶠ r : ℝ in 𝓝[>] 0, z ∈ closedBall z (1 * r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [one_mul] using mem_closedBall_self (mem_Ioi.mp hr).le
  simpa only [diskAverage_eq_closedBallAverage, id_eq] using
    hz (fun _ : ℝ => z) id tendsto_id hmem

theorem ae_tendsto_diskAverage_of_locallyIntegrableOn {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℝ} (hf : LocallyIntegrableOn f U) :
    ∀ᵐ z ∂volume.restrict U,
      Tendsto (fun r : ℝ => diskAverage r f z) (𝓝[>] 0) (𝓝 (f z)) := by
  classical
  apply ae_on_set_of_open_neighborhoods
  intro c hc
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU c hc
  let T := closedBall c (ε / 2)
  have hTU : T ⊆ U := (closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hεU
  have hT : IsCompact T := isCompact_closedBall _ _
  have hFi := (hf.integrableOn_compact_subset hTU hT).integrable_indicator hT.measurableSet
  refine ⟨ball c (ε / 4), isOpen_ball, mem_ball_self (by positivity), ?_⟩
  filter_upwards [ae_restrict_of_ae (ae_tendsto_diskAverage hFi),
    ae_restrict_mem isOpen_ball.measurableSet] with z hz hzV
  have hzT : z ∈ T := ball_subset_closedBall
    (ball_subset_ball (by linarith : ε / 4 ≤ ε / 2) hzV)
  have heq : (fun r : ℝ => diskAverage r (T.indicator f) z) =ᶠ[𝓝[>] 0]
      (fun r : ℝ => diskAverage r f z) := by
    filter_upwards [(gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4)).filter_mono
      nhdsWithin_le_nhds] with r hr
    apply diskAverage_congr
    intro w hw
    have hball : closedBall z r ⊆ T := closedBall_subset_closedBall'
      (by have := mem_ball.mp hzV; linarith)
    exact indicator_of_mem (hball (ball_subset_closedBall hw)) f
  have hval : T.indicator f z = f z := indicator_of_mem hzT f
  rw [hval] at hz
  exact hz.congr' heq


end ModifiedCartan
