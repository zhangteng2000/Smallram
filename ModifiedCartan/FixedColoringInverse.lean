import ModifiedCartan.FixedColoringProduct
import ModifiedCartan.FiniteCyclePolynomials

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem fixedColoring_inverse_iff {A B : Type*} (σ : Equiv.Perm A) (f : A → B) :
    (∀ a, f (σ⁻¹ a) = f a) ↔ ∀ a, f (σ a) = f a := by
  constructor
  · intro h a
    exact (h (σ a)).symm.trans (congrArg f (σ.symm_apply_apply a))
  · intro h a
    exact (h (σ⁻¹ a)).symm.trans (congrArg f (σ.apply_symm_apply a))

theorem permutationFixedColoringSum_inv {A B R : Type*}
    [Fintype A] [Fintype B] [CommSemiring R] (σ : Equiv.Perm A) (x : B → R) :
    permutationFixedColoringSum σ⁻¹ x = permutationFixedColoringSum σ x := by
  unfold permutationFixedColoringSum
  exact Equiv.sum_comp (Equiv.subtypeEquivRight (fixedColoring_inverse_iff σ))
    (fun f => ∏ a : A, x (f.val a))

theorem finiteCyclePolynomial_inv {A B : Type*} [Fintype A] [Fintype B]
    (σ : Equiv.Perm A) : finiteCyclePolynomial B σ⁻¹ = finiteCyclePolynomial B σ :=
  permutationFixedColoringSum_inv σ _

theorem finiteCyclePolynomial_rename {A B C : Type*} [Fintype A] [Fintype B]
    (f : B → C) (σ : Equiv.Perm A) :
    MvPolynomial.rename f (finiteCyclePolynomial B σ) =
      permutationFixedColoringSum σ (fun b : B => (MvPolynomial.X (f b) : MvPolynomial C ℂ)) := by
  calc
    _ = permutationFixedColoringSum σ
        (fun b : B => MvPolynomial.rename f (MvPolynomial.X b)) :=
      permutationFixedColoringSum_map (MvPolynomial.rename f).toRingHom σ _
    _ = _ := by
      apply congrArg (permutationFixedColoringSum σ)
      funext b
      exact MvPolynomial.rename_X f b

end
end ModifiedCartan


