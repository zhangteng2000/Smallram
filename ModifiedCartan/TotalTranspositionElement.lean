import ModifiedCartan.PermutationStar

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

def totalTranspositionElement (A : Type*) [Fintype A] [DecidableEq A] : ℂ[Equiv.Perm A] :=
  (2 : ℂ)⁻¹ • ∑ i : A, ∑ j : A, if i = j then 0 else transpositionElement i j

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem totalTranspositionElement_conjugate (u : Equiv.Perm A) :
    permutationElement u * totalTranspositionElement A * permutationElement u⁻¹ =
      totalTranspositionElement A := by
  simp only [totalTranspositionElement, mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul,
    transpositionElement_conjugate]
  congr 1
  calc
    _ = ∑ i : A, ∑ j : A, if u i = u j then 0 else transpositionElement (u i) (u j) := by
      simp only [u.injective.eq_iff]
    _ = ∑ i : A, ∑ j : A, if u i = j then 0 else transpositionElement (u i) j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp u (fun j => if u i = j then 0 else transpositionElement (u i) j)
    _ = _ := Equiv.sum_comp u (fun i => ∑ j : A, if i = j then 0 else transpositionElement i j)

theorem totalTranspositionElement_commutes_permutation (u : Equiv.Perm A) :
    permutationElement u * totalTranspositionElement A =
      totalTranspositionElement A * permutationElement u :=
  permutationElement_conjugation_cancel u _ _ (totalTranspositionElement_conjugate u)

end
end ModifiedCartan


