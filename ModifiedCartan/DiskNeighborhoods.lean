import ModifiedCartan.DiskAverages

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem closedBall_near_center_subset_cthickening {c y : ℂ} {r δ : ℝ}
    (hy : dist y c ≤ δ) : closedBall y r ⊆ cthickening δ (closedBall c r) := by
  intro z hz
  let w : ℂ := z + (c - y)
  have hw : w ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm]
    have heq : w - c = z - y := by dsimp [w]; ring
    rw [heq]
    simpa only [dist_eq_norm] using mem_closedBall.mp hz
  apply closedBall_subset_cthickening hw δ
  rw [mem_closedBall, dist_eq_norm]
  have heq : z - w = y - c := by dsimp [w]; ring
  rw [heq]
  simpa only [dist_eq_norm] using hy

theorem exists_compact_disk_neighborhood {U : Set ℂ} (hU : IsOpen U)
    {c : ℂ} {r : ℝ} (hball : closedBall c r ⊆ U) :
    ∃ (δ : ℝ) (T : Set ℂ), 0 < δ ∧ IsCompact T ∧ T ⊆ U ∧
      ∀ y ∈ ball c δ, closedBall y r ⊆ T := by
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall c r).exists_cthickening_subset_open hU hball
  exact ⟨δ, cthickening δ (closedBall c r), hδ, (isCompact_closedBall c r).cthickening,
    hδU, fun y hy => closedBall_near_center_subset_cthickening (mem_ball.mp hy).le⟩

theorem isOpen_setOf_closedBall_subset {U : Set ℂ} (hU : IsOpen U) (r : ℝ) :
    IsOpen {c : ℂ | closedBall c r ⊆ U} := by
  apply Metric.isOpen_iff.mpr
  intro c hc
  obtain ⟨δ, T, hδ, _, hTU, hballs⟩ := exists_compact_disk_neighborhood hU hc
  exact ⟨δ, hδ, fun y hy => (hballs y hy).trans hTU⟩


end ModifiedCartan
