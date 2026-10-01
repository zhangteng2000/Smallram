import ModifiedCartan.SizedSubsetInsertion
import ModifiedCartan.KPSubsetInduction
import Mathlib.Algebra.Polynomial.Derivative

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def kpWeightPolynomial (z : A → ℂ) (I : Finset A) : Polynomial ℂ :=
  ∏ l ∈ Finset.univ \ I, (Polynomial.X + Polynomial.C (z l))

theorem kpWeightPolynomial_eval (z : A → ℂ) (I : Finset A) (a : ℂ) :
    (kpWeightPolynomial z I).eval a = ∏ l ∈ Finset.univ \ I, (a + z l) := by
  simp [kpWeightPolynomial, Polynomial.eval_prod]

theorem kpWeightPolynomial_derivative (z : A → ℂ) (I : Finset A) :
    (kpWeightPolynomial z I).derivative = ∑ l ∈ Finset.univ \ I, kpWeightPolynomial z (insert l I) := by
  simp only [kpWeightPolynomial, Polynomial.derivative_prod_finset,
    Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C, add_zero, mul_one,
    complement_erase_eq_complement_insert]

def kpBetaCoefficientPolynomial (μ : YoungDiagram) (z : A → ℂ) (g : Equiv.Perm A) : Polynomial ℂ :=
  ∑ I : SizedLetterSubset A (partitionSize μ), Polynomial.C ((kpAlpha μ I.val).coeff g) * kpWeightPolynomial z I.val

theorem kpBetaCoefficientPolynomial_eval (μ : YoungDiagram) (z : A → ℂ) (g : Equiv.Perm A) (a : ℂ) :
    (kpBetaCoefficientPolynomial μ z g).eval a = (kpBeta μ z a).coeff g := by
  simp only [kpBetaCoefficientPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, kpWeightPolynomial_eval, kpBeta, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  rw [sum_sizedLetterSubset]
  apply Finset.sum_congr rfl
  intro I _
  exact mul_comm _ _

theorem kpBetaCoefficientPolynomial_of_size_gt (μ : YoungDiagram) (z : A → ℂ) (g : Equiv.Perm A)
    (h : Fintype.card A < partitionSize μ) : kpBetaCoefficientPolynomial μ z g = 0 := by
  apply Polynomial.funext
  intro a
  rw [kpBetaCoefficientPolynomial_eval, kpBeta_of_size_gt μ z a h]
  simp

end
end ModifiedCartan


