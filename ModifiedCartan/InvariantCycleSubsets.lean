import ModifiedCartan.InvariantCycleSets
import ModifiedCartan.CycleWeightedPowers

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem permutationCycleUnion_subset_iff (σ : Equiv.Perm A) (T : Finset A)
    (hT : ∀ a, σ a ∈ T ↔ a ∈ T) (C : Finset (PermutationCycles σ)) :
    permutationCycleUnion σ C ⊆ T ↔ C ⊆ permutationCycleImage σ T := by
  constructor
  · intro h c hc
    revert hc
    refine Quotient.inductionOn c (fun a => ?_)
    intro ha
    apply (mem_permutationCycleImage_iff σ T hT a).mpr
    exact h ((mem_permutationCycleUnion σ C a).mpr ha)
  · intro h a ha
    exact (mem_permutationCycleImage_iff σ T hT a).mp
      (h ((mem_permutationCycleUnion σ C a).mp ha))

def invariantSubsetCycleEquiv (σ : Equiv.Perm A) (T : Finset A)
    (hT : ∀ a, σ a ∈ T ↔ a ∈ T) :
    {C : Finset (PermutationCycles σ) // C ⊆ permutationCycleImage σ T} ≃
      {D : Finset A // D ⊆ T ∧ ∀ a, σ a ∈ D ↔ a ∈ D} where
  toFun C := ⟨permutationCycleUnion σ C.val,
    (permutationCycleUnion_subset_iff σ T hT C.val).mpr C.property,
    permutationCycleUnion_invariant σ C.val⟩
  invFun D := ⟨permutationCycleImage σ D.val, by
    apply (permutationCycleUnion_subset_iff σ T hT _).mp
    rw [permutationCycleUnion_image σ D.val D.property.2]
    exact D.property.1⟩
  left_inv C := Subtype.ext (permutationCycleImage_union σ C.val)
  right_inv D := Subtype.ext (permutationCycleUnion_image σ D.val D.property.2)

theorem permutationCycleUnion_card (σ : Equiv.Perm A) (C : Finset (PermutationCycles σ)) :
    (permutationCycleUnion σ C).card = ∑ c ∈ C, permutationCycleWeight σ (fun _ => 1) c := by
  simpa [permutationCycleUnion, permutationCycleWeight] using
    (Finset.sum_card_fiberwise_eq_card_filter Finset.univ C (permutationCycleClass σ)).symm

end
end ModifiedCartan

