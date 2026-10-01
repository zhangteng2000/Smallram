import ModifiedCartan.SpechtFiniteAlphabetBranching

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem sum_corner_characters_of_character_eq {A : Type*} [Fintype A] [DecidableEq A]
    (μ ν : YoungDiagram) (hμ : Fintype.card A = partitionSize μ) (hν : Fintype.card A = partitionSize ν)
    (he : spechtCharacterOn μ hμ = spechtCharacterOn ν hν) (a : A)
    (p : Equiv.Perm (↥(Finset.univ.erase a))) :
    (∑ b : YoungCorner μ, spechtCharacterOn (removePartitionBox μ b)
      (card_erase_eq_partition_remove μ hμ a b) p) =
    ∑ c : YoungCorner ν, spechtCharacterOn (removePartitionBox ν c)
      (card_erase_eq_partition_remove ν hν a c) p := by
  let g := supportedPermutationEquiv (Finset.univ.erase a) p
  have hg : g.val a = a := g.property a (by simp)
  have hd : deleteFixedPoint a g.val hg = p :=
    (supportedPermutationEquiv (Finset.univ.erase a)).symm_apply_apply p
  have hh := congrFun he g.val
  rw [spechtCharacterOn_branching μ hμ a g.val hg,
    spechtCharacterOn_branching ν hν a g.val hg, hd] at hh
  exact hh

end
end ModifiedCartan


