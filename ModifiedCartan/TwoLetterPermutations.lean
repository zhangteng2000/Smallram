import ModifiedCartan.TotalTranspositionDeletion

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem permutation_univ_of_card_two {A : Type*} [Fintype A] [DecidableEq A]
    (h : Fintype.card A = 2) (a b : A) (hab : a ≠ b) :
    (Finset.univ : Finset (Equiv.Perm A)) = {1, Equiv.swap a b} := by
  have hn : (1 : Equiv.Perm A) ≠ Equiv.swap a b := by
    intro he
    have hx := congrArg (fun p : Equiv.Perm A => p a) he
    exact hab (by simpa only [Equiv.Perm.one_apply, Equiv.swap_apply_left] using hx)
  apply (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
  simp only [Finset.card_univ, Fintype.card_perm, h]
  simp [hn]

end
end ModifiedCartan


