import ModifiedCartan.FixedPointPermutationSums

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem sum_subtype_ne_add {X M : Type*} [Fintype X] [DecidableEq X] [AddCommMonoid M]
    (a : X) (f : X → M) :
    (∑ x : {x : X // x ≠ a}, f x.val) + f a = ∑ x : X, f x := by
  classical
  have he := Finset.sum_subtype (p := fun x : X => x ≠ a) (F := inferInstance)
    (Finset.univ.erase a) (by intro x; simp) f
  rw [← he]
  exact Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)

theorem half_sum_symmetric_delete {X : Type*} [Fintype X] [DecidableEq X] (f : X → X → ℂ)
    (hsym : ∀ x y, f x y = f y x) (a : X) (hself : f a a = 0) :
    (2 : ℂ)⁻¹ * (∑ x : X, ∑ y : X, f x y) =
      (2 : ℂ)⁻¹ * (∑ x : {x : X // x ≠ a}, ∑ y : {x : X // x ≠ a}, f x.val y.val) +
        ∑ y : X, f a y := by
  have hr : (∑ x : {x : X // x ≠ a}, f x.val a) = ∑ y : X, f a y := by
    simp_rw [hsym _ a]
    have he := sum_subtype_ne_add a (f a)
    simpa only [hself, add_zero] using he
  have ht : (∑ x : X, ∑ y : X, f x y) =
      (∑ x : {x : X // x ≠ a}, ∑ y : {x : X // x ≠ a}, f x.val y.val) +
        2 * ∑ y : X, f a y := by
    calc
      _ = (∑ x : {x : X // x ≠ a}, ∑ y : X, f x.val y) + ∑ y : X, f a y :=
        (sum_subtype_ne_add a (fun x => ∑ y : X, f x y)).symm
      _ = (∑ x : {x : X // x ≠ a},
          ((∑ y : {x : X // x ≠ a}, f x.val y.val) + f x.val a)) + ∑ y : X, f a y := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        exact (sum_subtype_ne_add a (f x.val)).symm
      _ = _ := by rw [Finset.sum_add_distrib, hr]; ring
  rw [ht]
  ring

end
end ModifiedCartan


