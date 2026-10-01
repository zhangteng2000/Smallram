import ModifiedCartan.CycleUnionCoordinates
import ModifiedCartan.TransitivePermutationSign
import ModifiedCartan.SigmaPermutationSign

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem permutationCycleFiber_sign {A : Type*} [Fintype A] (σ : Equiv.Perm A)
    (c : PermutationCycles σ) :
    Equiv.Perm.sign (permutationCycleFiberPerm σ c) =
      (-1) ^ (permutationCycleWeight σ (fun _ => 1) c + 1) := by
  rw [transitivePermutation_sign (permutationCycleFiberPerm σ c)
    (permutationCycleFiber_sameCycle σ c), permutationCycleFiber_card]

theorem cycleUnion_restriction_sign {A : Type*} [Fintype A] (σ : Equiv.Perm A)
    (C : Finset (PermutationCycles σ)) :
    Equiv.Perm.sign (σ.subtypePerm (permutationCycleUnion_invariant σ C)) =
      ∏ c ∈ C, (-1) ^ (permutationCycleWeight σ (fun _ => 1) c + 1) := by
  rw [cycleUnion_restriction_eq, Equiv.Perm.sign_permCongr,
    sign_sigmaCongrRight (fun c : C => PermutationCycleFiber σ c.val)
      (fun c : C => permutationCycleFiberPerm σ c.val)]
  simp only [permutationCycleFiber_sign]
  exact Finset.prod_coe_sort C (fun c => (-1 : ℤˣ) ^ (permutationCycleWeight σ (fun _ => 1) c + 1))

end
end ModifiedCartan

