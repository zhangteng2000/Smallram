import ModifiedCartan.DiskNeighborhoods
import ModifiedCartan.DiskAverageContinuity
import ModifiedCartan.SubharmonicAveragingOrder

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem continuousAt_diskAverage_of_locallyIntegrableOn
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ} (hf : LocallyIntegrableOn f U)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hball : closedBall c r ⊆ U) :
    ContinuousAt (diskAverage r f) c := by
  classical
  obtain ⟨δ, T, hδ, hT, hTU, hballs⟩ := exists_compact_disk_neighborhood hU hball
  have hfi := (hf.integrableOn_compact_subset hTU hT).integrable_indicator hT.measurableSet
  apply (continuous_diskAverage hfi hr).continuousAt.congr
  filter_upwards [ball_mem_nhds c hδ] with y hy
  apply diskAverage_congr
  intro z hz
  exact indicator_of_mem (hballs y hy (ball_subset_closedBall hz)) _


end ModifiedCartan
