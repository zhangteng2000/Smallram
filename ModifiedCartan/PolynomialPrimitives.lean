import ModifiedCartan.DividedPowerPolynomials
import Mathlib.Algebra.Polynomial.Basis

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The polynomial primitive with zero constant term, defined algebraically.
    Auxiliary to the dimension transfer in manuscript `lem:KP-correspondence`. -/
def complexPolynomialPrimitive : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ :=
  (Polynomial.basisMonomials ℂ).constr ℂ
    (fun n => Polynomial.monomial (n + 1) ((n + 1 : ℂ)⁻¹))

theorem complexPolynomialPrimitive_monomial_one (n : ℕ) :
    complexPolynomialPrimitive (Polynomial.monomial n 1) =
      Polynomial.monomial (n + 1) ((n + 1 : ℂ)⁻¹) :=
  (Polynomial.basisMonomials ℂ).constr_basis ℂ _ n

theorem complexPolynomialPrimitive_derivative (p : Polynomial ℂ) :
    (complexPolynomialPrimitive p).derivative = p := by
  have h : Polynomial.derivative.comp complexPolynomialPrimitive = LinearMap.id := by
    apply (Polynomial.basisMonomials ℂ).ext
    intro n
    change (complexPolynomialPrimitive (Polynomial.monomial n 1)).derivative =
      Polynomial.monomial n 1
    rw [complexPolynomialPrimitive_monomial_one, Polynomial.derivative_monomial_succ]
    congr 1
    apply inv_mul_cancel₀
    exact_mod_cast Nat.succ_ne_zero n
  exact LinearMap.congr_fun h p

theorem complexPolynomialPrimitive_coeff_zero (p : Polynomial ℂ) :
    (complexPolynomialPrimitive p).coeff 0 = 0 := by
  have h : (Polynomial.lcoeff ℂ 0).comp complexPolynomialPrimitive = 0 := by
    apply (Polynomial.basisMonomials ℂ).ext
    intro n
    change (complexPolynomialPrimitive (Polynomial.monomial n 1)).coeff 0 = 0
    rw [complexPolynomialPrimitive_monomial_one]
    simp
  exact LinearMap.congr_fun h p

theorem complexPolynomialPrimitive_iterate_derivative (p : Polynomial ℂ) (k : ℕ) :
    Polynomial.derivative^[k + 1] (complexPolynomialPrimitive p) =
      Polynomial.derivative^[k] p := by
  rw [Function.iterate_succ_apply, complexPolynomialPrimitive_derivative]

theorem complexPolynomialPrimitive_natDegree (p : Polynomial ℂ) (hp : p ≠ 0) :
    (complexPolynomialPrimitive p).natDegree = p.natDegree + 1 := by
  have h := Polynomial.natDegree_derivative (complexPolynomialPrimitive p)
  rw [complexPolynomialPrimitive_derivative] at h
  have hn : (complexPolynomialPrimitive p).natDegree ≠ 0 := by
    intro hz
    have he := Polynomial.derivative_of_natDegree_zero hz
    rw [complexPolynomialPrimitive_derivative] at he
    exact hp he
  omega

end
end ModifiedCartan

#print axioms ModifiedCartan.complexPolynomialPrimitive_derivative