import ModifiedCartan.YoungPermutationSubgroups

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The row occupied by each letter in a tabloid. Letters are the boxes of the diagram. -/
def youngTabloidRows (μ : YoungDiagram) (t : YoungTabloid μ) : YoungBoxes μ → ℕ :=
  Quotient.lift (fun g b => (g⁻¹ b).val.1) (by
    intro g h hgh
    funext b
    have hr : g⁻¹ * h ∈ youngRowSubgroup μ := QuotientGroup.leftRel_apply.mp hgh
    simpa using hr (h⁻¹ b)) t

@[simp] theorem youngTabloidRows_mk (μ : YoungDiagram)
    (g : Equiv.Perm (YoungBoxes μ)) (b : YoungBoxes μ) :
    youngTabloidRows μ (youngTabloid μ g) b = (g⁻¹ b).val.1 := rfl

theorem youngTabloidRows_injective (μ : YoungDiagram) :
    Function.Injective (youngTabloidRows μ) := by
  intro t u htu
  induction t using Quotient.inductionOn with | h g =>
    induction u using Quotient.inductionOn with | h h =>
      apply (young_tabloid_eq_iff μ g h).mpr
      intro b
      have hh : (g⁻¹ (h b)).val.1 = (h⁻¹ (h b)).val.1 := congrFun htu (h b)
      simpa using hh

theorem young_tabloid_rows_eq_iff (μ : YoungDiagram) (t u : YoungTabloid μ) :
    youngTabloidRows μ t = youngTabloidRows μ u ↔ t = u :=
  (youngTabloidRows_injective μ).eq_iff

theorem youngTabloidRows_sum (μ : YoungDiagram) (t : YoungTabloid μ) :
    ∑ b : YoungBoxes μ, youngTabloidRows μ t b = ∑ b : YoungBoxes μ, b.val.1 := by
  induction t using Quotient.inductionOn with | h g =>
    change (∑ b : YoungBoxes μ, (g⁻¹ b).val.1) = ∑ b : YoungBoxes μ, b.val.1
    exact g.symm.sum_comp (fun b => b.val.1)

theorem youngTabloidRows_smul (μ : YoungDiagram) (g : Equiv.Perm (YoungBoxes μ))
    (t : YoungTabloid μ) (b : YoungBoxes μ) :
    youngTabloidRows μ (g • t) b = youngTabloidRows μ t (g⁻¹ b) := by
  induction t using Quotient.inductionOn with | h h =>
    change ((g * h)⁻¹ b).val.1 = (h⁻¹ (g⁻¹ b)).val.1
    rw [mul_inv_rev]
    rfl

end
end ModifiedCartan


