import ModifiedCartan.CycleUnionSign
import ModifiedCartan.InvariantCycleSubsets

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem cycleUnion_restriction_sign_twist {A : Type*} [Fintype A] (σ : Equiv.Perm A)
    (C : Finset (PermutationCycles σ)) :
    (-1 : ℤˣ) ^ (permutationCycleUnion σ C).card *
      Equiv.Perm.sign (σ.subtypePerm (permutationCycleUnion_invariant σ C)) = (-1) ^ C.card := by
  rw [cycleUnion_restriction_sign, permutationCycleUnion_card]
  simp only [pow_add, pow_one, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_const]
  have hs : ((-1 : ℤˣ) ^ (∑ c ∈ C, permutationCycleWeight σ (fun _ => 1) c)) *
      ((-1 : ℤˣ) ^ (∑ c ∈ C, permutationCycleWeight σ (fun _ => 1) c)) = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm, pow_mul]
    simp
  rw [← mul_assoc, hs, one_mul]

theorem cycleUnion_restriction_sign_twist_complex {A : Type*} [Fintype A] (σ : Equiv.Perm A)
    (C : Finset (PermutationCycles σ)) :
    (-1 : ℂ) ^ (permutationCycleUnion σ C).card *
      ((Equiv.Perm.sign (σ.subtypePerm (permutationCycleUnion_invariant σ C)) : ℤ) : ℂ) =
        (-1 : ℂ) ^ C.card := by
  have h := congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ)) (cycleUnion_restriction_sign_twist σ C)
  simpa using h

end
end ModifiedCartan

