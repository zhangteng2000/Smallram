import ModifiedCartan.WeightColoringRepresentation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finiteCyclePolynomial_coeff {A B : Type*} [Fintype A] [Fintype B]
    (σ : Equiv.Perm A) (d : B →₀ ℕ) :
    MvPolynomial.coeff d (finiteCyclePolynomial B σ) =
      ∑ f : {f : A → B // ∀ a, f (σ a) = f a},
        if coloringDegree f.val = d then (1 : ℂ) else 0 := by
  simp only [finiteCyclePolynomial, permutationFixedColoringSum, MvPolynomial.coeff_sum,
    ← coloringDegree_monomial, MvPolynomial.coeff_monomial]

/-- A cycle-polynomial coefficient is the character of the actual permutation
representation on colorings with the specified multiplicities. -/
theorem finiteCyclePolynomial_coeff_character {A B : Type*} [Fintype A] [Fintype B]
    (σ : Equiv.Perm A) (d : B →₀ ℕ) :
    MvPolynomial.coeff d (finiteCyclePolynomial B σ) =
      (weightColoringRepresentation A d).character σ := by
  rw [finiteCyclePolynomial_coeff, weightColoringRepresentation_character]
  calc
    _ = ∑ f : A → B, if ∀ a, f (σ a) = f a then
        (if coloringDegree f = d then (1 : ℂ) else 0) else 0 :=
      (sum_dite_eq_sum_subtype (fun f : A → B => ∀ a, f (σ a) = f a)
        (fun f _ => if coloringDegree f = d then (1 : ℂ) else 0)).symm
    _ = ∑ f : A → B, if coloringDegree f = d then
        (if ∀ a, f (σ a) = f a then (1 : ℂ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      split_ifs <;> rfl
    _ = _ := sum_dite_eq_sum_subtype (fun f : A → B => coloringDegree f = d)
      (fun f _ => if ∀ a, f (σ a) = f a then (1 : ℂ) else 0)

end
end ModifiedCartan


