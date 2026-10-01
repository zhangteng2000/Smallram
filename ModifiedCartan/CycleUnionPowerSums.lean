import ModifiedCartan.CycleUnionCoordinates
import ModifiedCartan.TransitiveSigmaColorings

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem cycleUnion_restriction_fixedColoringSum {A B R : Type*} [Fintype A] [Fintype B]
    [CommSemiring R] (σ : Equiv.Perm A) (C : Finset (PermutationCycles σ)) (x : B → R) :
    permutationFixedColoringSum (σ.subtypePerm (permutationCycleUnion_invariant σ C)) x =
      ∏ c ∈ C, ∑ b : B, x b ^ permutationCycleWeight σ (fun _ => 1) c := by
  rw [cycleUnion_restriction_eq, permutationFixedColoringSum_conjugate,
    permutationFixedColoringSum_sigma_transitive (fun c : C => PermutationCycleFiber σ c.val)
      (fun c : C => permutationCycleFiberPerm σ c.val)
      (fun c : C => permutationCycleFiber_sameCycle σ c.val) x]
  simp only [permutationCycleFiber_card]
  exact Finset.prod_coe_sort C (fun c => ∑ b : B, x b ^ permutationCycleWeight σ (fun _ => 1) c)

end
end ModifiedCartan

