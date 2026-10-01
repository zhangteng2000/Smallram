import ModifiedCartan.FixedColoringTransport
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def fixedColoringSumEquiv {A C B : Type*} (σ : Equiv.Perm A) (τ : Equiv.Perm C) :
    ({f : A → B // ∀ a, f (σ a) = f a} × {g : C → B // ∀ c, g (τ c) = g c}) ≃
      {h : A ⊕ C → B // ∀ p, h (Equiv.sumCongr σ τ p) = h p} where
  toFun fg := ⟨Sum.elim fg.1.val fg.2.val, by
    rintro (a | c)
    · exact fg.1.property a
    · exact fg.2.property c⟩
  invFun h := ⟨⟨fun a => h.val (Sum.inl a), fun a => h.property (Sum.inl a)⟩,
    ⟨fun c => h.val (Sum.inr c), fun c => h.property (Sum.inr c)⟩⟩
  left_inv fg := by apply Prod.ext <;> exact Subtype.ext rfl
  right_inv h := by
    apply Subtype.ext
    funext p
    cases p <;> rfl

theorem permutationFixedColoringSum_sumCongr {A C B R : Type*}
    [Fintype A] [Fintype C] [Fintype B] [CommSemiring R]
    (σ : Equiv.Perm A) (τ : Equiv.Perm C) (x : B → R) :
    permutationFixedColoringSum (Equiv.sumCongr σ τ) x =
      permutationFixedColoringSum σ x * permutationFixedColoringSum τ x := by
  letI : DecidableEq (A ⊕ C) := Classical.decEq _
  unfold permutationFixedColoringSum
  rw [← Equiv.sum_comp (fixedColoringSumEquiv σ τ) (fun h => ∏ p, x (h.val p))]
  simp only [Fintype.prod_sum_type]
  change (∑ fg : ({f : A → B // ∀ a, f (σ a) = f a} ×
      {g : C → B // ∀ c, g (τ c) = g c}),
    (∏ a, x (fg.1.val a)) * (∏ c, x (fg.2.val c))) = _
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

end
end ModifiedCartan

