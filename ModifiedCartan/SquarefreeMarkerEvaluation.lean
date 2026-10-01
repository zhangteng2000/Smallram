import ModifiedCartan.MarkerAssignmentDegree
import Mathlib.Algebra.MvPolynomial.Eval

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem markerSquarefreeMonomial_eq_prod {A R : Type*} [CommSemiring R] (s : Finset A) :
    MvPolynomial.monomial (markerSquarefreeDegree s) (1 : R) =
      ∏ a ∈ s, (MvPolynomial.X a : MvPolynomial A R) := by
  simpa only [markerSquarefreeDegree, pow_one] using
    (MvPolynomial.prod_X_pow (R := R) (fun _ : A => 1) s).symm

theorem markerSquarefreeMonomial_eval₂ {A R S : Type*} [CommSemiring R] [CommSemiring S]
    (s : Finset A) (c : R) (f : R →+* S) (x : A → S) :
    MvPolynomial.eval₂Hom f x (MvPolynomial.monomial (markerSquarefreeDegree s) c) =
      f c * ∏ a ∈ s, x a := by
  have hm : MvPolynomial.monomial (markerSquarefreeDegree s) c =
      MvPolynomial.C c * ∏ a ∈ s, (MvPolynomial.X a : MvPolynomial A R) := by
    rw [← markerSquarefreeMonomial_eq_prod, MvPolynomial.C_mul_monomial, mul_one]
  rw [hm, map_mul, MvPolynomial.eval₂Hom_C, map_prod]
  simp only [MvPolynomial.eval₂Hom_X']

end
end ModifiedCartan

