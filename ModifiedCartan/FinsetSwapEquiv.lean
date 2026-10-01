import ModifiedCartan.FiniteSubsetSwaps

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [DecidableEq A]

theorem finset_image_swap_twice (I : Finset A) (i j : A) :
    (I.image (Equiv.swap i j)).image (Equiv.swap i j) = I := by
  ext x
  rw [mem_image_permutation_iff, mem_image_permutation_iff]
  change Equiv.swap i j (Equiv.swap i j x) ∈ I ↔ x ∈ I
  rw [Equiv.swap_apply_self]

def finsetSwapEquiv (i j : A) : Finset A ≃ Finset A where
  toFun I := I.image (Equiv.swap i j)
  invFun I := I.image (Equiv.swap i j)
  left_inv I := finset_image_swap_twice I i j
  right_inv I := finset_image_swap_twice I i j

theorem finsetSwapEquiv_involutive (i j : A) (I : Finset A) :
    finsetSwapEquiv i j (finsetSwapEquiv i j I) = I := finset_image_swap_twice I i j

theorem finsetSwapEquiv_cut (i j : A) (I : Finset A) :
    (i ∈ finsetSwapEquiv i j I ∧ j ∉ finsetSwapEquiv i j I) ↔ (j ∈ I ∧ i ∉ I) := by
  change (i ∈ I.image (Equiv.swap i j) ∧ j ∉ I.image (Equiv.swap i j)) ↔ _
  simp only [mem_image_permutation_iff]
  change (Equiv.swap i j i ∈ I ∧ Equiv.swap i j j ∉ I) ↔ _
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right]

end
end ModifiedCartan


