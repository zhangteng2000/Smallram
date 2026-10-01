import ModifiedCartan.TwoBoxSpechtDistinction
import ModifiedCartan.PartitionPredecessorReconstruction

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem partition_eq_bot_of_size_zero (μ : YoungDiagram) (h : partitionSize μ = 0) : μ = ⊥ := by
  apply YoungDiagram.ext
  exact Finset.card_eq_zero.mp h

/-- Predecessors together with the actual character resolve the two-box ambiguity. -/
theorem partition_eq_of_predecessors_and_character {A : Type*} [Fintype A] [DecidableEq A]
    (μ ν : YoungDiagram) (hμ : Fintype.card A = partitionSize μ) (hν : Fintype.card A = partitionSize ν)
    (hp : youngPredecessors μ = youngPredecessors ν)
    (he : spechtCharacterOn μ hμ = spechtCharacterOn ν hν) : μ = ν := by
  have hs : partitionSize μ = partitionSize ν := hμ.symm.trans hν
  by_cases hz : partitionSize μ = 0
  · exact (partition_eq_bot_of_size_zero μ hz).trans
      (partition_eq_bot_of_size_zero ν (hs ▸ hz)).symm
  by_contra hne
  obtain ⟨b⟩ := youngCorner_exists_of_pos μ (Nat.pos_of_ne_zero hz)
  have hm : removePartitionBox μ b ∈ youngPredecessors ν := hp ▸ Set.mem_range_self b
  obtain ⟨c, hbc⟩ := hm
  have hb : ∀ d : YoungCorner μ, d = b := by
    intro d
    by_contra hd
    exact hne (partition_eq_of_same_predecessors_two_corners μ ν hs hp d b hd)
  have hc : ∀ d : YoungCorner ν, d = c := by
    intro d
    by_contra hd
    exact hne (partition_eq_of_same_predecessors_two_corners ν μ hs.symm hp.symm d c hd).symm
  rcases unique_corner_same_removal_shapes μ ν b c hb hc hbc.symm hne with hh | hh
  · exact two_box_unique_corner_characters_ne μ ν hμ hν b c hb hc hh.1 hh.2 he
  · exact two_box_unique_corner_characters_ne ν μ hν hμ c b hc hb hh.2 hh.1 he.symm

end
end ModifiedCartan


