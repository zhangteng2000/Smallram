import ModifiedCartan.FixedColoringTransport

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem permutationFixedColoringSum_map {A B R S : Type*} [Fintype A] [Fintype B]
    [CommSemiring R] [CommSemiring S] (φ : R →+* S) (σ : Equiv.Perm A) (x : B → R) :
    φ (permutationFixedColoringSum σ x) = permutationFixedColoringSum σ (φ ∘ x) := by
  simp only [permutationFixedColoringSum, map_sum, map_prod, Function.comp_apply]

def fixedColoringProductEquiv {A B C : Type*} (σ : Equiv.Perm A) :
    {f : A → B × C // ∀ a, f (σ a) = f a} ≃
      ({f : A → B // ∀ a, f (σ a) = f a} × {f : A → C // ∀ a, f (σ a) = f a}) where
  toFun f := (⟨fun a => (f.val a).1, fun a => congrArg Prod.fst (f.property a)⟩,
    ⟨fun a => (f.val a).2, fun a => congrArg Prod.snd (f.property a)⟩)
  invFun p := ⟨fun a => (p.1.val a, p.2.val a), fun a => Prod.ext (p.1.property a) (p.2.property a)⟩
  left_inv f := rfl
  right_inv p := rfl

theorem permutationFixedColoringSum_product {A B C R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [CommSemiring R]
    (σ : Equiv.Perm A) (x : B → R) (y : C → R) :
    permutationFixedColoringSum σ (fun p : B × C => x p.1 * y p.2) =
      permutationFixedColoringSum σ x * permutationFixedColoringSum σ y := by
  letI : DecidableEq (B × C) := Classical.decEq _
  unfold permutationFixedColoringSum
  calc
    _ = ∑ p : {f : A → B // ∀ a, f (σ a) = f a} ×
        {f : A → C // ∀ a, f (σ a) = f a}, (∏ a, x (p.1.val a)) * ∏ a, y (p.2.val a) := by
      apply Fintype.sum_equiv (fixedColoringProductEquiv σ)
      intro f
      exact Finset.prod_mul_distrib
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

end
end ModifiedCartan


