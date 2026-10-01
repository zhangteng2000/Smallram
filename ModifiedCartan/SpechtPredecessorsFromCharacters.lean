import ModifiedCartan.SpechtCharacterPairingStep
import ModifiedCartan.SpechtRestrictedCharacterSums
import ModifiedCartan.CornerPredecessors

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The separation hypothesis is the strictly smaller alphabet in the induction. -/
theorem youngPredecessors_subset_of_character_eq {A : Type*} [Fintype A] [DecidableEq A]
    (a : A)
    (hsep : ∀ (ξ ζ : YoungDiagram) (hξ : Fintype.card (↥(Finset.univ.erase a)) = partitionSize ξ)
      (hζ : Fintype.card (↥(Finset.univ.erase a)) = partitionSize ζ),
      spechtCharacterOn ξ hξ = spechtCharacterOn ζ hζ → ξ = ζ)
    (μ ν : YoungDiagram) (hμ : Fintype.card A = partitionSize μ) (hν : Fintype.card A = partitionSize ν)
    (he : spechtCharacterOn μ hμ = spechtCharacterOn ν hν) : youngPredecessors μ ⊆ youngPredecessors ν := by
  rintro τ ⟨b, rfl⟩
  by_contra hn
  have hL : (∑ d : YoungCorner μ,
      if removePartitionBox μ d = removePartitionBox μ b then (1 : ℂ) else 0) = 1 := by
    simp [(removePartitionBox_injective μ).eq_iff]
  have hR : (∑ d : YoungCorner ν,
      if removePartitionBox ν d = removePartitionBox μ b then (1 : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro d _
    have hd : removePartitionBox ν d ≠ removePartitionBox μ b := fun hd => hn ⟨d, hd⟩
    simp [hd]
  have hpL := sum_spechtCharacterOn_pairing_of_separation hsep (removePartitionBox μ)
    (card_erase_eq_partition_remove μ hμ a) (removePartitionBox μ b)
    (card_erase_eq_partition_remove μ hμ a b)
  have hpR := sum_spechtCharacterOn_pairing_of_separation hsep (removePartitionBox ν)
    (card_erase_eq_partition_remove ν hν a) (removePartitionBox μ b)
    (card_erase_eq_partition_remove μ hμ a b)
  rw [hL] at hpL
  rw [hR] at hpR
  have hh : (Nat.card (Equiv.Perm (↥(Finset.univ.erase a))) : ℂ)⁻¹ *
      ∑ p : Equiv.Perm (↥(Finset.univ.erase a)),
        (∑ d : YoungCorner μ, spechtCharacterOn (removePartitionBox μ d)
          (card_erase_eq_partition_remove μ hμ a d) p) *
          spechtCharacterOn (removePartitionBox μ b) (card_erase_eq_partition_remove μ hμ a b) p⁻¹ =
    (Nat.card (Equiv.Perm (↥(Finset.univ.erase a))) : ℂ)⁻¹ *
      ∑ p : Equiv.Perm (↥(Finset.univ.erase a)),
        (∑ d : YoungCorner ν, spechtCharacterOn (removePartitionBox ν d)
          (card_erase_eq_partition_remove ν hν a d) p) *
          spechtCharacterOn (removePartitionBox μ b) (card_erase_eq_partition_remove μ hμ a b) p⁻¹ := by
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [sum_corner_characters_of_character_eq μ ν hμ hν he a p]
  exact one_ne_zero (hpL.symm.trans (hh.trans hpR))

theorem youngPredecessors_eq_of_character_eq {A : Type*} [Fintype A] [DecidableEq A]
    (a : A)
    (hsep : ∀ (ξ ζ : YoungDiagram) (hξ : Fintype.card (↥(Finset.univ.erase a)) = partitionSize ξ)
      (hζ : Fintype.card (↥(Finset.univ.erase a)) = partitionSize ζ),
      spechtCharacterOn ξ hξ = spechtCharacterOn ζ hζ → ξ = ζ)
    (μ ν : YoungDiagram) (hμ : Fintype.card A = partitionSize μ) (hν : Fintype.card A = partitionSize ν)
    (he : spechtCharacterOn μ hμ = spechtCharacterOn ν hν) : youngPredecessors μ = youngPredecessors ν :=
  Set.Subset.antisymm (youngPredecessors_subset_of_character_eq a hsep μ ν hμ hν he)
    (youngPredecessors_subset_of_character_eq a hsep ν μ hν hμ he.symm)

end
end ModifiedCartan


