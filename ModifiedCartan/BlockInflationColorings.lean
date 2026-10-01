import ModifiedCartan.BlockInflation
import ModifiedCartan.CycleColorings

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem blockInflation_fixed_coloring_iff {A B : Type*} [Fintype A] (κ : A → ℕ)
    (σ : Equiv.Perm A) (f : (Σ a, Fin (κ a + 1)) → B) :
    (∀ p, f (blockInflation κ σ p) = f p) ↔
      (∀ (a : A) (i : Fin (κ a + 1)), f ⟨a, i⟩ = f ⟨a, 0⟩) ∧
      ∀ a, f ⟨σ a, 0⟩ = f ⟨a, 0⟩ := by
  constructor
  · intro hf
    constructor
    · intro a i
      have h := coloring_pow_eq (blockInflation κ σ) f hf i.val ⟨a, 0⟩
      rw [blockInflation_pow_head κ σ a i.val (by have := i.isLt; omega)] at h
      exact h
    · intro a
      have h := coloring_pow_eq (blockInflation κ σ) f hf (κ a + 1) ⟨a, 0⟩
      rw [blockInflation_block_step] at h
      exact h
  · rintro ⟨hi, ha⟩ ⟨a, i⟩
    by_cases hlt : i.val < κ a
    · rw [blockInflation_internal κ σ a i.val hlt]
      exact (hi a ⟨i.val + 1, by omega⟩).trans (hi a i).symm
    · have he : i = Fin.last (κ a) := Fin.ext (by change i.val = κ a; have := i.isLt; omega)
      rw [he, blockInflation_last, ha]
      exact (hi a (Fin.last (κ a))).symm

/-- Invariant colorings of the inflated permutation are exactly invariant
colorings of the original permutation, constant along each block. -/
def blockInflationColoringEquiv {A B : Type*} [Fintype A] (κ : A → ℕ) (σ : Equiv.Perm A) :
    {g : A → B // ∀ a, g (σ a) = g a} ≃
      {f : (Σ a, Fin (κ a + 1)) → B // ∀ p, f (blockInflation κ σ p) = f p} where
  toFun g := ⟨fun p => g.val p.1,
    (blockInflation_fixed_coloring_iff κ σ (fun p => g.val p.1)).mpr
      ⟨fun _ _ => rfl, g.property⟩⟩
  invFun f := ⟨fun a => f.val ⟨a, 0⟩, ((blockInflation_fixed_coloring_iff κ σ f.val).mp f.property).2⟩
  left_inv g := Subtype.ext rfl
  right_inv f := by
    apply Subtype.ext
    funext p
    exact (((blockInflation_fixed_coloring_iff κ σ f.val).mp f.property).1 p.1 p.2).symm

theorem blockConstant_coloring_product {A B R : Type*} [Fintype A] [CommMonoid R]
    (κ : A → ℕ) (x : B → R) (g : A → B) :
    (∏ p : (Σ a, Fin (κ a + 1)), x (g p.1)) = ∏ a : A, x (g a) ^ (κ a + 1) := by
  rw [Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end
end ModifiedCartan

