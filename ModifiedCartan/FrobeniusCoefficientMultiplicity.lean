import ModifiedCartan.CyclePolynomialCoefficients
import ModifiedCartan.FiniteFrobeniusPolynomials

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- Every coefficient is an actual finite-dimensional intertwiner multiplicity. -/
theorem finiteFrobeniusPolynomialOn_coeff_finrank {A B : Type*} [Fintype A] [Fintype B]
    (μ : YoungDiagram) (hA : Fintype.card A = partitionSize μ) (d : B →₀ ℕ) :
    MvPolynomial.coeff d (finiteFrobeniusPolynomialOn B μ hA) =
      (Module.finrank ℂ (Representation.IntertwiningMap
        (spechtRepresentationOn μ hA) (weightColoringRepresentation A d)) : ℂ) := by
  have hG : (Nat.card (Equiv.Perm A) : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero (α := Equiv.Perm A)
  letI : Invertible (Nat.card (Equiv.Perm A) : ℂ) := invertibleOfNonzero hG
  simp only [finiteFrobeniusPolynomialOn, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sum,
    finiteCyclePolynomial_coeff_character]
  simp_rw [mul_comm (spechtCharacterOn μ hA _)]
  exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (spechtRepresentationOn μ hA) (weightColoringRepresentation A d)

theorem finiteFrobeniusPolynomial_coeff_nat {B : Type*} [Fintype B]
    (μ : YoungDiagram) (d : B →₀ ℕ) :
    ∃ k : ℕ, MvPolynomial.coeff d (finiteFrobeniusPolynomial B μ) = (k : ℂ) := by
  exact ⟨_, finiteFrobeniusPolynomialOn_coeff_finrank μ (Fintype.card_fin _) d⟩

end
end ModifiedCartan


