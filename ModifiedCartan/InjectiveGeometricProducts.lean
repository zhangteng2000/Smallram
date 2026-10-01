import ModifiedCartan.FiniteCompositionSums

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem product_split_embedding {A B R : Type*} [Fintype A] [Fintype B]
    [CommMonoid R] (f : A ↪ B) (h : B → R) :
    (∏ b : B, h b) = (∏ a : A, h (f a)) *
      ∏ b ∈ Finset.univ \ Finset.univ.image f, h b := by
  have hs : Finset.univ.image f ⊆ (Finset.univ : Finset B) := Finset.subset_univ _
  rw [← Finset.prod_sdiff hs, Finset.prod_image f.injective.injOn, mul_comm]

/-- The finite geometric identity replaces the cancellation involution in the
proof of KP source Lemma 2.25. -/
theorem elementary_product_mul_injective_geometric {A B R : Type*}
    [Fintype A] [Fintype B] [CommRing R] (f : A ↪ B) (ℓ : A → ℕ) (x : B → R) :
    (∏ b : B, (1 - x b)) * (∏ a : A, positiveGeometricSum (ℓ a) (x (f a))) =
      (∏ a : A, (x (f a) - x (f a) ^ (ℓ a + 1))) *
        ∏ b ∈ Finset.univ \ Finset.univ.image f, (1 - x b) := by
  rw [product_split_embedding f (fun b => 1 - x b), mul_right_comm,
    ← Finset.prod_mul_distrib]
  simp only [one_sub_mul_positiveGeometricSum]

theorem elementary_product_mul_composition_sum {A B R : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [CommRing R] (ℓ : A → ℕ) (x : B → R) :
    (∏ b : B, (1 - x b)) * finiteCompositionMonomialSum ℓ x =
      ∑ f : A ↪ B, (∏ a : A, (x (f a) - x (f a) ^ (ℓ a + 1))) *
        ∏ b ∈ Finset.univ \ Finset.univ.image f, (1 - x b) := by
  rw [finiteCompositionMonomialSum_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun f hf => elementary_product_mul_injective_geometric f ℓ x)

end
end ModifiedCartan


