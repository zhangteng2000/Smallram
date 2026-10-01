import ModifiedCartan.NormalizedMinorTranslation
import ModifiedCartan.PolynomialMinorBasisChange

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem normalizedPartitionMinor_basis_independent {n : ℕ}
    {V : Submodule ℂ (Polynomial ℂ)} (b c : Module.Basis (Fin (n + 1)) ℂ V)
    (ω μ : YoungDiagram) (a : ℂ) :
    normalizedPartitionMinor ω (fun j => (c j).val) μ a =
      normalizedPartitionMinor ω (fun j => (b j).val) μ a := by
  unfold normalizedPartitionMinor
  rw [partitionPolynomialMinor_basis_change b c μ,
    partitionPolynomialMinor_basis_change b c ω]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [← mul_assoc, mul_div_mul_right _ _ (polynomialBasis_toMatrix_det_ne_zero b c)]

/-- A basis with exactly the degree profile defining the manuscript's Schubert cell. -/
structure PolynomialSchubertFrame (n : ℕ) (ω : YoungDiagram)
    (V : Submodule ℂ (Polynomial ℂ)) where
  basis : Module.Basis (Fin (n + 1)) ℂ V
  degree_eq : ∀ j, (basis j).val.natDegree = partitionMinorOrders n ω j

def PolynomialSchubertFrame.polynomials {n : ℕ} {ω : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (F : PolynomialSchubertFrame n ω V) :
    Fin (n + 1) → Polynomial ℂ := fun j => (F.basis j).val

theorem PolynomialSchubertFrame.polynomials_ne_zero {n : ℕ} {ω : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (F : PolynomialSchubertFrame n ω V)
    (j : Fin (n + 1)) : F.polynomials j ≠ 0 := by
  intro h
  exact F.basis.ne_zero j (Subtype.ext h)

theorem PolynomialSchubertFrame.finrank {n : ℕ} {ω : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (F : PolynomialSchubertFrame n ω V) :
    Module.finrank ℂ V = n + 1 := by
  rw [Module.finrank_eq_card_basis F.basis, Fintype.card_fin]

/-- LaTeX Schubert cell `X^omega` in `C_{m-1}[z]`, specified by an actual basis. -/
def polynomialSchubertCell (n m : ℕ) (ω : YoungDiagram) :
    Set (Submodule ℂ (Polynomial ℂ)) :=
  {V | PartitionFits n ω ∧ n + 1 + ω.rowLen 0 ≤ m ∧
    Nonempty (PolynomialSchubertFrame n ω V)}

def schubertFrame {n m : ℕ} {ω : YoungDiagram} {V : Submodule ℂ (Polynomial ℂ)}
    (hV : V ∈ polynomialSchubertCell n m ω) : PolynomialSchubertFrame n ω V :=
  Classical.choice hV.2.2

/-- Basis-independent coordinates with the normalization `eq:normalized-Plucker-coordinates`. -/
def normalizedSchubertCoordinate {n m : ℕ} {ω : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n m ω)
    (μ : YoungDiagram) (a : ℂ) : ℂ :=
  normalizedPartitionMinor ω (schubertFrame hV).polynomials μ a

theorem normalizedSchubertCoordinate_eq_basis {n m : ℕ} {ω : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n m ω)
    (b : Module.Basis (Fin (n + 1)) ℂ V) (μ : YoungDiagram) (a : ℂ) :
    normalizedSchubertCoordinate hV μ a =
      normalizedPartitionMinor ω (fun j => (b j).val) μ a :=
  normalizedPartitionMinor_basis_independent b (schubertFrame hV).basis ω μ a

theorem normalizedSchubertCoordinate_top {n m : ℕ} {ω : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n m ω) (a : ℂ) :
    normalizedSchubertCoordinate hV ω a =
      (partitionSize ω).factorial / (standardSkewTableauCount ω ⊥ : ℂ) :=
  normalizedPartitionMinor_top (schubertFrame hV).polynomials hV.1
    (schubertFrame hV).polynomials_ne_zero (schubertFrame hV).degree_eq a

end
end ModifiedCartan


