import ModifiedCartan.BernsteinCompositionSeries
import ModifiedCartan.BernsteinFactorResidue

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

/-- Auxiliary for LaTeX `lem:KP-correspondence`: the exact finite-alphabet
residue needed after the permutation-factorization expansion in KP source
Section 4.1. All power-sum factors are removed by proved ring identities. -/
theorem finiteBernstein_factored_composition_residue {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] (ℓ : A → ℕ) (s : Finset I) (j : I → ℕ) :
    (finiteBernsteinLaurent B ((∏ i ∈ s, (1 - LaurentPolynomial.T (j i : ℤ) *
      LaurentPolynomial.C (finitePowerSumPolynomial (Option B) (j i)))) *
        (LaurentPolynomial.T (-(∑ i ∈ s, (j i : ℤ))) * finiteCompositionSeries (Option B) ℓ))).coeff (-1) = 0 := by
  apply finiteBernsteinLaurent_strip_factors_residue
  rw [← mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, one_mul]
  exact finiteCompositionSeries_Bernstein_residue ℓ

end
end ModifiedCartan

