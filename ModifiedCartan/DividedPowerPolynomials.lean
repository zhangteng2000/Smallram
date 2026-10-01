import FewInflection.PolynomialJets

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The normalized polynomial basis used in KP (4.7), indexed from zero. -/
def complexDividedPowerPolynomial (n : ℕ) : Polynomial ℂ :=
  Polynomial.monomial n ((n.factorial : ℂ)⁻¹)

theorem complexDividedPowerPolynomial_zero : complexDividedPowerPolynomial 0 = 1 := by
  simp [complexDividedPowerPolynomial]

theorem complexDividedPowerPolynomial_natDegree (n : ℕ) :
    (complexDividedPowerPolynomial n).natDegree = n := by
  apply Polynomial.natDegree_monomial_eq
  exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n)

theorem complexDividedPowerPolynomial_derivative_succ (n : ℕ) :
    (complexDividedPowerPolynomial (n + 1)).derivative = complexDividedPowerPolynomial n := by
  rw [complexDividedPowerPolynomial, Polynomial.derivative_monomial_succ,
    complexDividedPowerPolynomial]
  apply congrArg (Polynomial.monomial n)
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem complexDividedPowerPolynomial_iterate_derivative (k n : ℕ) :
    Polynomial.derivative^[k] (complexDividedPowerPolynomial n) =
      if k ≤ n then complexDividedPowerPolynomial (n - k) else 0 := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => simp [complexDividedPowerPolynomial_zero]
    | succ n =>
      rw [Function.iterate_succ_apply, complexDividedPowerPolynomial_derivative_succ, ih]
      simp

/-- The divided-power basis has Kronecker derivative jets at zero.
    Auxiliary to the translation argument in manuscript `lem:KP-correspondence`. -/
theorem complexDividedPowerPolynomial_jet_zero (k n : ℕ) :
    (Polynomial.derivative^[k] (complexDividedPowerPolynomial n)).eval 0 =
      if k = n then 1 else 0 := by
  rw [← FewInflection.iteratedDeriv_polynomial_eval,
    FewInflection.iteratedDeriv_polynomial_eval_zero, complexDividedPowerPolynomial]
  by_cases h : k = n
  · subst k
    simp [Nat.factorial_ne_zero]
  · simp only [Polynomial.coeff_monomial, h, Ne.symm h, ite_false, mul_zero]

end
end ModifiedCartan

#print axioms ModifiedCartan.complexDividedPowerPolynomial_jet_zero
