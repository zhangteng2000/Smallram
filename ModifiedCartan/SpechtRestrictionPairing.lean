import ModifiedCartan.InducedSpechtClassFunction
import ModifiedCartan.SpechtDistinctCharacters
import ModifiedCartan.PartitionCovers

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem sum_corner_removal_indicator (μ ν : YoungDiagram) :
    (∑ b : YoungCorner ν, if removePartitionBox ν b = μ then (1 : ℂ) else 0) =
      if PartitionCovers ν μ then 1 else 0 := by
  by_cases hc : PartitionCovers ν μ
  · rw [if_pos hc]
    obtain ⟨b, hb⟩ := hc.exists_corner_removal
    simp [← hb, (removePartitionBox_injective ν).eq_iff]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro b _
    have hb : removePartitionBox ν b ≠ μ := fun hb =>
      hc ((partitionCovers_iff_corner_removal μ ν).mpr ⟨b, hb⟩)
    rw [if_neg hb]

/-- The normalized pairing with the restriction of a larger actual Specht
character is the one-box cover indicator. -/
theorem specht_restriction_pairing {A : Type*} [Fintype A] [DecidableEq A]
    (μ ν : YoungDiagram) (hμ : Fintype.card A = partitionSize μ + 1)
    (hν : Fintype.card A = partitionSize ν) (a : A) :
    (Nat.card (Equiv.Perm (↥(Finset.univ.erase a))) : ℂ)⁻¹ *
      ∑ p : Equiv.Perm (↥(Finset.univ.erase a)),
        spechtCharacterOn μ (card_erase_of_successor_size μ hμ a) p⁻¹ *
        spechtCharacterOn ν hν (fixedPointPermutationEquiv a p).val =
      if PartitionCovers ν μ then 1 else 0 := by
  have hb (p : Equiv.Perm (↥(Finset.univ.erase a))) :
      spechtCharacterOn ν hν (fixedPointPermutationEquiv a p).val =
        ∑ b : YoungCorner ν, spechtCharacterOn (removePartitionBox ν b)
          (card_erase_eq_partition_remove ν hν a b) p := by
    rw [spechtCharacterOn_branching ν hν a _ (fixedPointPermutationEquiv a p).property]
    have hd : deleteFixedPoint a (fixedPointPermutationEquiv a p).val
        (fixedPointPermutationEquiv a p).property = p :=
      (fixedPointPermutationEquiv a).symm_apply_apply p
    rw [hd]
  simp_rw [hb, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ b : YoungCorner ν, if removePartitionBox ν b = μ then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      simpa only [Finset.mul_sum, mul_comm] using spechtCharacterOn_orthogonality (removePartitionBox ν b) μ
        (card_erase_eq_partition_remove ν hν a b) (card_erase_of_successor_size μ hμ a)
    _ = _ := sum_corner_removal_indicator μ ν

end
end ModifiedCartan


