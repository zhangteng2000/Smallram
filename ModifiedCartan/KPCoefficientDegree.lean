import ModifiedCartan.KPPolynomialCoefficients
import Mathlib.Algebra.Polynomial.BigOperators

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem kpWeightPolynomial_natDegree_le (z : A → ℂ) (I : Finset A) :
    (kpWeightPolynomial z I).natDegree ≤ (Finset.univ \ I).card := by
  have h := Polynomial.natDegree_prod_le (Finset.univ \ I)
    (fun l => Polynomial.X + Polynomial.C (z l))
  simpa [kpWeightPolynomial, Polynomial.natDegree_X_add_C] using h

theorem kpBetaCoefficientPolynomial_natDegree_le (μ : YoungDiagram) (z : A → ℂ) (g : Equiv.Perm A) :
    (kpBetaCoefficientPolynomial μ z g).natDegree ≤ Fintype.card A := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro I _
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (kpWeightPolynomial_natDegree_le z I.val).trans
  exact (Finset.card_le_card (Finset.sdiff_subset)).trans_eq (Finset.card_univ)

end
end ModifiedCartan


