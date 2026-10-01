import ModifiedCartan.SpechtBranchingEquiv
import ModifiedCartan.TraceSurjectiveKernel
import ModifiedCartan.NestedSubmoduleTrace

open scoped Classical

namespace ModifiedCartan
noncomputable section

def youngSpechtRowCharacter (μ : YoungDiagram) (a : YoungBoxes μ) (r : ℕ) :
    youngLetterStabilizer μ a → ℂ :=
  (youngSpechtRowFiltration μ a r).toRepresentation.character

/-- The character increment at a removable corner is the character of the smaller Specht module. -/
theorem youngSpechtRowCharacter_corner (μ : YoungDiagram) (b : YoungCorner μ)
    (g : Equiv.Perm (YoungBoxes (removePartitionBox μ b))) :
    youngSpechtRowCharacter μ b.val (b.val.val.1 + 1) (youngRemovalPermutationEquiv μ b g) =
      youngSpechtRowCharacter μ b.val b.val.val.1 (youngRemovalPermutationEquiv μ b g) +
        (youngSpechtRepresentation (removePartitionBox μ b)).character g := by
  let U := (youngSpechtRowFiltration μ b.val b.val.val.1).toSubmodule
  let W := (youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toSubmodule
  let h := youngRemovalPermutationEquiv μ b g
  let T := youngLetterRepresentation μ b.val h
  have hU : ∀ v ∈ U, T v ∈ U :=
    (youngSpechtRowFiltration μ b.val b.val.val.1).apply_mem_toSubmodule h
  have hW : ∀ v ∈ W, T v ∈ W :=
    (youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).apply_mem_toSubmodule h
  have hUW : U ≤ W := youngSpechtRowFiltration_mono μ b.val (Nat.le_succ _)
  have ht := trace_eq_submodule_add_of_surjective
    (youngSpechtBranchingMap μ b) (youngSpechtBranchingMap_surjective μ b)
    (T.restrict hW) (youngSpechtRepresentation (removePartitionBox μ b) g)
    (youngSpechtBranchingMap_action μ b g) (U.comap W.subtype)
    (nested_submodule_invariant U W T hU hW) (youngSpechtBranchingMap_ker μ b)
  rw [trace_restrict_nested U W hUW T hU hW] at ht
  exact ht

theorem youngSpechtRowFiltration_eq_of_no_corner (μ : YoungDiagram) (a : YoungBoxes μ)
    (r : ℕ) (hr : r < μ.colLen 0) (hn : ¬ ∃ b : YoungCorner μ, b.val.val.1 = r) :
    youngSpechtRowFiltration μ a r = youngSpechtRowFiltration μ a (r + 1) := by
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.eq_of_le_of_finrank_eq (youngSpechtRowFiltration_mono μ a (Nat.le_succ r))
  have hz := youngSpechtRowIncrement_zero_of_no_corner μ a r hr hn
  have hle := youngSpechtRowRank_mono μ a (Nat.le_succ r)
  change youngSpechtRowRank μ a r ≤ youngSpechtRowRank μ a (r + 1) at hle
  change youngSpechtRowRank μ a r = youngSpechtRowRank μ a (r + 1)
  unfold youngSpechtRowIncrement at hz
  omega

theorem youngSpechtRowCharacter_eq_of_no_corner (μ : YoungDiagram) (a : YoungBoxes μ)
    (r : ℕ) (hr : r < μ.colLen 0) (hn : ¬ ∃ b : YoungCorner μ, b.val.val.1 = r)
    (g : youngLetterStabilizer μ a) :
    youngSpechtRowCharacter μ a (r + 1) g = youngSpechtRowCharacter μ a r g := by
  unfold youngSpechtRowCharacter
  rw [youngSpechtRowFiltration_eq_of_no_corner μ a r hr hn]

end
end ModifiedCartan


