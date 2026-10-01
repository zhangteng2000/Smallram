import ModifiedCartan.FiniteCycleIndex
import ModifiedCartan.FiniteFrobeniusPolynomials
import ModifiedCartan.RowColumnFiniteCharacters

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The finite Frobenius transform for a single row is the complete homogeneous
polynomial. A proved special case of KP equation (2.15). -/
theorem finiteFrobeniusPolynomial_single_row {B : Type*} [Fintype B]
    (μ : YoungDiagram) (hr : ∀ a : YoungBoxes μ, a.val.1 = 0) :
    finiteFrobeniusPolynomial B μ = MvPolynomial.hsymm B ℂ (partitionSize μ) := by
  unfold finiteFrobeniusPolynomial finiteFrobeniusPolynomialOn
  simp_rw [spechtCharacterOn_single_row μ _ hr, map_one, one_mul]
  simpa only [Fintype.card_fin] using
    (finiteCyclePolynomial_average (A := Fin (partitionSize μ)) (B := B))

end
end ModifiedCartan


