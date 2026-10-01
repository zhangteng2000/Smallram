import ModifiedCartan.YoungColoringMinimum

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def youngFirstColumnBox (μ : YoungDiagram) (i : Fin (μ.colLen 0)) : YoungBoxes μ :=
  ⟨(i.val, 0), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩

/-- Too few colors force a repeated color in the first column.
    Auxiliary to paper `lem:KP-correspondence`. -/
theorem youngFirstColumn_color_collision {m : ℕ} (μ : YoungDiagram)
    (hm : m < μ.colLen 0) (f : YoungBoxes μ → Fin m) :
    ∃ a b : YoungBoxes μ, a ≠ b ∧ a.val.2 = b.val.2 ∧ f a = f b := by
  by_contra hs
  push_neg at hs
  have hf : Function.Injective (fun i : Fin (μ.colLen 0) => f (youngFirstColumnBox μ i)) := by
    intro i j hij
    have hb : youngFirstColumnBox μ i = youngFirstColumnBox μ j := by
      by_contra hne
      exact hs _ _ hne rfl hij
    apply Fin.ext
    exact congrArg (fun b : YoungBoxes μ => b.val.1) hb
  have hc := Fintype.card_le_of_injective _ hf
  simp only [Fintype.card_fin] at hc
  omega

end
end ModifiedCartan

#print axioms ModifiedCartan.youngFirstColumn_color_collision
