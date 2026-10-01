import ModifiedCartan.WeightColoringRepresentation
import ModifiedCartan.YoungColumnMinimum
import ModifiedCartan.YoungColumnOrbit

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def partitionRowWeight (μ : YoungDiagram) : ℕ := ∑ b : YoungBoxes μ, b.val.1

def finiteColorWeight {m : ℕ} (d : Fin m →₀ ℕ) : ℕ := ∑ b : Fin m, b.val * d b

theorem youngColumn_total_min (μ : YoungDiagram) (f : YoungBoxes μ → ℕ)
    (hf : ∀ a b, a.val.2 = b.val.2 → f a = f b → a = b) :
    partitionRowWeight μ ≤ ∑ b : YoungBoxes μ, f b := by
  rw [partitionRowWeight, ← young_sum_columns μ (fun b => b.val.1), ← young_sum_columns μ f]
  exact Finset.sum_le_sum (fun j _ => youngColumn_sum_min μ f hf j)

theorem weightColoring_finite_weight {m : ℕ} (μ : YoungDiagram) (d : Fin m →₀ ℕ)
    (f : WeightColoring (YoungBoxes μ) d) :
    (∑ b : YoungBoxes μ, (f.val b).val) = finiteColorWeight d := by
  rw [← coloringDegree_weight f.val Fin.val, f.property]
  rfl

/-- Below the minimum row weight, every actual coloring repeats a color in
some column. This supplies the triangular vanishing condition, not an assumption. -/
theorem weightColoring_column_collision {m : ℕ} (μ : YoungDiagram) (d : Fin m →₀ ℕ)
    (hd : finiteColorWeight d < partitionRowWeight μ)
    (f : WeightColoring (YoungBoxes μ) d) :
    ∃ a b : YoungBoxes μ, a ≠ b ∧ a.val.2 = b.val.2 ∧ f.val a = f.val b := by
  by_cases hi : ∀ a b : YoungBoxes μ, a.val.2 = b.val.2 → f.val a = f.val b → a = b
  · have hmin := youngColumn_total_min μ (fun b => (f.val b).val)
      (fun a b hc hv => hi a b hc (Fin.ext hv))
    rw [weightColoring_finite_weight μ d f] at hmin
    exact (Nat.not_le_of_lt hd hmin).elim
  · push_neg at hi
    obtain ⟨a, b, hc, hf, hne⟩ := hi
    exact ⟨a, b, hne, hc, hf⟩

theorem youngColumn_minimum_coloringDegree (μ : YoungDiagram) (f : YoungBoxes μ → ℕ)
    (hf : ∀ a b, a.val.2 = b.val.2 → f a = f b → a = b)
    (hs : (∑ b : YoungBoxes μ, f b) = partitionRowWeight μ) :
    coloringDegree f = coloringDegree (fun b : YoungBoxes μ => b.val.1) := by
  let e := youngColumnAssignmentEquiv μ f hf hs
  exact coloringDegree_comp_equiv (fun b : YoungBoxes μ => b.val.1) e

end
end ModifiedCartan


