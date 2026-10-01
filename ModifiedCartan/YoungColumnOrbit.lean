import ModifiedCartan.YoungColumnMinimum
import ModifiedCartan.YoungTabloidRows

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- A column permutation realizing a column-injective assignment of rows. -/
def youngColumnAssignmentEquiv (μ : YoungDiagram) (f : YoungBoxes μ → ℕ)
    (hf : ∀ a b, a.val.2 = b.val.2 → f a = f b → a = b)
    (hs : (∑ b : YoungBoxes μ, f b) = ∑ b : YoungBoxes μ, b.val.1) :
    Equiv.Perm (YoungBoxes μ) := by
  let F : YoungBoxes μ → YoungBoxes μ :=
    fun b => ⟨(f b, b.val.2), youngColumn_assignment_mem μ f hf hs b⟩
  have hi : Function.Injective F := by
    intro a b hab
    apply hf a b
    · simpa only [F] using congrArg (fun c : YoungBoxes μ => c.val.2) hab
    · simpa only [F] using congrArg (fun c : YoungBoxes μ => c.val.1) hab
  exact Equiv.ofBijective F ⟨hi, Finite.surjective_of_injective hi⟩

@[simp] theorem youngColumnAssignmentEquiv_apply (μ : YoungDiagram) (f : YoungBoxes μ → ℕ)
    (hf : ∀ a b, a.val.2 = b.val.2 → f a = f b → a = b)
    (hs : (∑ b : YoungBoxes μ, f b) = ∑ b : YoungBoxes μ, b.val.1) (b : YoungBoxes μ) :
    (youngColumnAssignmentEquiv μ f hf hs b).val = (f b, b.val.2) := rfl

theorem youngColumnAssignmentEquiv_mem (μ : YoungDiagram) (f : YoungBoxes μ → ℕ)
    (hf : ∀ a b, a.val.2 = b.val.2 → f a = f b → a = b)
    (hs : (∑ b : YoungBoxes μ, f b) = ∑ b : YoungBoxes μ, b.val.1) :
    youngColumnAssignmentEquiv μ f hf hs ∈ youngColumnSubgroup μ := by
  intro b
  rfl

/-- The elementary column-orbit alternative used in the Specht submodule theorem. -/
theorem youngTabloid_eq_column_of_injective (μ : YoungDiagram) (t : YoungTabloid μ)
    (ht : ∀ a b : YoungBoxes μ, a.val.2 = b.val.2 →
      youngTabloidRows μ t a = youngTabloidRows μ t b → a = b) :
    ∃ c : youngColumnSubgroup μ, t = youngTabloid μ c.val := by
  let e := youngColumnAssignmentEquiv μ (youngTabloidRows μ t) ht (youngTabloidRows_sum μ t)
  have he : e ∈ youngColumnSubgroup μ := youngColumnAssignmentEquiv_mem μ _ ht _
  refine ⟨⟨e⁻¹, (youngColumnSubgroup μ).inv_mem he⟩, ?_⟩
  apply youngTabloidRows_injective μ
  funext b
  rw [youngTabloidRows_mk, inv_inv]
  rfl

end
end ModifiedCartan


