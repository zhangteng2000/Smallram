import ModifiedCartan.InjectiveColorSums

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem sum_embedding_products_equiv {A B C R : Type*} [Fintype A] [Fintype B] [Fintype C]
    [CommSemiring R] (e : A ≃ C) (w : C → B → R) :
    (∑ f : A ↪ B, ∏ a : A, w (e a) (f a)) = ∑ g : C ↪ B, ∏ c : C, w c (g c) := by
  rw [← Equiv.sum_comp (Equiv.embeddingCongr e (Equiv.refl B))
    (fun g => ∏ c : C, w c (g c))]
  apply Finset.sum_congr rfl
  intro f hf
  simpa using (Equiv.prod_comp e (fun c => w c (f (e.symm c))))

def eraseFinsetSubtypeEquiv {A : Type*} (s : Finset A) (a : s) :
    {i : s // i ≠ a} ≃ s.erase a.val where
  toFun i := ⟨i.val.val, Finset.mem_erase.mpr
    ⟨fun h => i.property (Subtype.ext h), i.val.property⟩⟩
  invFun i := ⟨⟨i.val, (Finset.mem_erase.mp i.property).2⟩,
    fun h => (Finset.mem_erase.mp i.property).1 (congrArg Subtype.val h)⟩
  left_inv i := by rfl
  right_inv i := by rfl

theorem sum_embedding_products_erase {A B R : Type*} [Fintype B] [CommSemiring R]
    (s : Finset A) (a : s) (w : A → B → R) :
    (∑ f : {i : s // i ≠ a} ↪ B, ∏ i : {i : s // i ≠ a}, w i.val.val (f i)) =
      ∑ g : s.erase a.val ↪ B, ∏ i : s.erase a.val, w i.val (g i) :=
  sum_embedding_products_equiv (eraseFinsetSubtypeEquiv s a) (fun i b => w i.val b)

end
end ModifiedCartan

