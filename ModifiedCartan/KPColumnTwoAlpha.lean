import ModifiedCartan.ColumnPartitions
import ModifiedCartan.TwoLetterPermutations

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem kpAlpha_column_two_pair {A : Type*} [Fintype A] [DecidableEq A]
    (i j : A) (hij : i ≠ j) :
    kpAlpha (columnPartition 2) {i, j} = 1 - transpositionElement i j := by
  let u : ({i, j} : Finset A) := ⟨i, by simp⟩
  let v : ({i, j} : Finset A) := ⟨j, by simp⟩
  have huv : u ≠ v := fun he => hij (congrArg Subtype.val he)
  have hc : Fintype.card ({i, j} : Finset A) = 2 := by
    rw [Fintype.card_coe]
    simp [hij]
  have hn : (1 : Equiv.Perm ({i, j} : Finset A)) ≠ Equiv.swap u v := by
    intro he
    apply huv
    have he' := congrArg (fun p : Equiv.Perm ({i, j} : Finset A) => p u) he
    simpa only [Equiv.Perm.one_apply, Equiv.swap_apply_left] using he'
  rw [kpAlpha_of_card_eq _ _ (by simp [partitionSize_columnPartition, hij])]
  simp_rw [spechtCharacterOn_columnPartition]
  rw [permutation_univ_of_card_two hc u v huv, Finset.sum_pair hn]
  rw [supportedPermutation_extension_swap]
  simp [u, v, transpositionElement, permutationElement, Equiv.Perm.sign_swap huv,
    sub_eq_add_neg]
  rfl

end
end ModifiedCartan


