import ModifiedCartan.SymmetricPairDeletion

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem half_sum_symmetric_erase_module {X M : Type*} [DecidableEq X]
    [AddCommGroup M] [Module ℂ M] (s : Finset X) (f : X → X → M)
    (hsym : ∀ x y, f x y = f y x) (a : X) (ha : a ∈ s) (hself : f a a = 0) :
    (2 : ℂ)⁻¹ • (∑ x ∈ s, ∑ y ∈ s, f x y) =
      (2 : ℂ)⁻¹ • (∑ x ∈ s.erase a, ∑ y ∈ s.erase a, f x y) + ∑ y ∈ s, f a y := by
  have hr : (∑ x ∈ s.erase a, f x a) = ∑ y ∈ s, f a y := by
    simp_rw [hsym _ a]
    simpa only [hself, add_zero] using Finset.sum_erase_add s (f a) ha
  have ht : (∑ x ∈ s, ∑ y ∈ s, f x y) =
      (∑ x ∈ s.erase a, ∑ y ∈ s.erase a, f x y) +
        (∑ y ∈ s, f a y) + ∑ y ∈ s, f a y := by
    calc
      _ = (∑ x ∈ s.erase a, ∑ y ∈ s, f x y) + ∑ y ∈ s, f a y :=
        (Finset.sum_erase_add s (fun x => ∑ y ∈ s, f x y) ha).symm
      _ = (∑ x ∈ s.erase a, ((∑ y ∈ s.erase a, f x y) + f x a)) + ∑ y ∈ s, f a y := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        exact (Finset.sum_erase_add s (f x) ha).symm
      _ = _ := by rw [Finset.sum_add_distrib, hr]
  rw [ht, smul_add, smul_add, add_assoc, ← add_smul]
  norm_num

end
end ModifiedCartan


