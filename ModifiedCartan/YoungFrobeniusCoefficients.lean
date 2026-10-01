import ModifiedCartan.FrobeniusCoefficientMultiplicity

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finiteFrobeniusPolynomial_young_sum {B : Type*} [Fintype B] (μ : YoungDiagram) :
    finiteFrobeniusPolynomial B μ =
      MvPolynomial.C ((Nat.card (Equiv.Perm (YoungBoxes μ)) : ℂ)⁻¹) *
        ∑ g : Equiv.Perm (YoungBoxes μ),
          MvPolynomial.C ((youngSpechtRepresentation μ).character g⁻¹) * finiteCyclePolynomial B g := by
  have hA : Fintype.card (YoungBoxes μ) = partitionSize μ := Fintype.card_coe μ.cells
  rw [← finiteFrobeniusPolynomialOn_eq (A := YoungBoxes μ) μ hA]
  unfold finiteFrobeniusPolynomialOn
  apply congrArg (fun P : MvPolynomial B ℂ =>
    MvPolynomial.C ((Nat.card (Equiv.Perm (YoungBoxes μ)) : ℂ)⁻¹) * P)
  apply Finset.sum_congr (by ext; simp)
  intro g hg
  rw [spechtCharacterOn_eq_young μ hA (Equiv.refl _)]
  rfl

theorem finiteFrobeniusPolynomial_coeff_finrank_young {B : Type*} [Fintype B]
    (μ : YoungDiagram) (d : B →₀ ℕ) :
    MvPolynomial.coeff d (finiteFrobeniusPolynomial B μ) =
      (Module.finrank ℂ (Representation.IntertwiningMap
        (youngSpechtRepresentation μ) (weightColoringRepresentation (YoungBoxes μ) d)) : ℂ) := by
  have hG : (Nat.card (Equiv.Perm (YoungBoxes μ)) : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero (α := Equiv.Perm (YoungBoxes μ))
  letI : Invertible (Nat.card (Equiv.Perm (YoungBoxes μ)) : ℂ) := invertibleOfNonzero hG
  rw [finiteFrobeniusPolynomial_young_sum]
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sum, finiteCyclePolynomial_coeff_character]
  simp_rw [mul_comm ((youngSpechtRepresentation μ).character _)]
  exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (youngSpechtRepresentation μ) (weightColoringRepresentation (YoungBoxes μ) d)

end
end ModifiedCartan


