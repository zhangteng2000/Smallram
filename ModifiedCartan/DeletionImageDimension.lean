import ModifiedCartan.DeletionImageSpecht
import ModifiedCartan.SubmoduleImageRankNullity
import ModifiedCartan.SpechtFiltrationRanks

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem youngDeletionImage_finrank_add (μ : YoungDiagram) (b : YoungCorner μ) :
    Module.finrank ℂ (youngDeletionImageSubrepresentation μ b (b.val.val.1 + 1)).toSubmodule +
      youngSpechtRowRank μ b.val b.val.val.1 = youngSpechtRowRank μ b.val (b.val.val.1 + 1) := by
  apply submodule_finrank_map_add_of_kernel (youngTabloidDeleteLinear μ b)
    (youngSpechtRowFiltration μ b.val b.val.val.1).toSubmodule
    (youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toSubmodule
    (youngSpechtRowFiltration_mono μ b.val (Nat.le_succ _))
  intro v hv
  rw [youngTabloidDeleteLinear_kernel_cutoff μ b v hv.2]
  constructor
  · intro h
    exact ⟨hv.1, h⟩
  · intro h
    exact h.2

theorem youngDeletionImage_finrank_eq_increment (μ : YoungDiagram) (b : YoungCorner μ) :
    Module.finrank ℂ (youngDeletionImageSubrepresentation μ b (b.val.val.1 + 1)).toSubmodule =
      youngSpechtRowIncrement μ b.val b.val.val.1 := by
  have h := youngDeletionImage_finrank_add μ b
  unfold youngSpechtRowIncrement
  omega

/-- Every removable corner supplies the required lower bound for that row's
actual Specht-filtration dimension increment. -/
theorem youngSpechtRowIncrement_corner_lower_bound (μ : YoungDiagram) (a : YoungBoxes μ)
    (b : YoungCorner μ) :
    Module.finrank ℂ (YoungSpechtModule (removePartitionBox μ b)) ≤
      youngSpechtRowIncrement μ a b.val.val.1 := by
  have h := youngSpecht_finrank_le_deletionImage μ b
  rw [youngDeletionImage_finrank_eq_increment] at h
  unfold youngSpechtRowIncrement at h ⊢
  rw [youngSpechtRowRank_letter_independent μ a b.val (b.val.val.1 + 1),
    youngSpechtRowRank_letter_independent μ a b.val b.val.val.1]
  exact h

end
end ModifiedCartan


